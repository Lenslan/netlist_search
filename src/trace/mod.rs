//! Backward tracing of one net bit through the netlist.
//!
//! Tracing works in *instance contexts*: a node is a net bit inside one module
//! instance. Crossing a module boundary moves to the context of the child or
//! parent instance, so there is never any doubt which instance a net is in.

#[cfg(test)]
mod tests;

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::rc::Rc;

use anyhow::Result;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::liberty::{BoolExpr, CellDef, CellKind, Dir, PinDef};
use crate::logic::bus::{reg_signal_name, split_index};
use crate::netlist::design::{Builtin, CellRef, Design, InstPath, PinInfo};
use crate::netlist::parser::{AssignKind, BitId, BitRef, Module};

pub type NodeId = u32;
pub type EndpointId = u32;

#[derive(Debug, Clone, Copy)]
pub struct TraceOpts {
    /// Stop creating nodes beyond this many; the rest become TRUNCATED.
    pub max_nodes: usize,
    /// How many module boundaries may be crossed, counted from the target instance.
    pub max_hier_depth: u32,
    /// Follow drivers across module boundaries at all.
    pub cross: bool,
}

impl Default for TraceOpts {
    fn default() -> Self {
        TraceOpts {
            max_nodes: 200_000,
            max_hier_depth: 8,
            cross: true,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EndpointKind {
    Reg,
    Latch,
    /// Cell neither in the library nor a module of the netlist.
    Unknown,
    /// Library cell whose output has no boolean function (macro, statetable cell).
    BlackBox,
    /// Input port (of the top module, or where cross-module tracing stopped).
    PortIn,
    /// inout port or three-state output.
    Inout,
    ConstX,
    Undriven,
    MultiDriver,
    Loop,
    Truncated,
    /// Output of a child module, when cross-module tracing stopped there.
    SubmoduleOut,
    /// `assign` whose right-hand side is not a plain alias.
    ComplexAssign,
}

impl EndpointKind {
    pub fn label(self) -> &'static str {
        match self {
            EndpointKind::Reg => "REG",
            EndpointKind::Latch => "LATCH",
            EndpointKind::Unknown => "UNKNOWN",
            EndpointKind::BlackBox => "BLACKBOX",
            EndpointKind::PortIn => "PORT-IN",
            EndpointKind::Inout => "INOUT",
            EndpointKind::ConstX => "CONSTX",
            EndpointKind::Undriven => "UNDRIVEN",
            EndpointKind::MultiDriver => "MULTI-DRIVER",
            EndpointKind::Loop => "LOOP",
            EndpointKind::Truncated => "TRUNCATED",
            EndpointKind::SubmoduleOut => "SUBMOD-OUT",
            EndpointKind::ComplexAssign => "ASSIGN-EXPR",
        }
    }
}

#[derive(Debug, Clone)]
pub struct Endpoint {
    pub kind: EndpointKind,
    /// Display name, used as the variable name in expressions.
    pub name: String,
    pub detail: String,
    /// Instance the endpoint belongs to (register, latch, black box).
    pub inst: Option<String>,
    pub cell: Option<String>,
}

#[derive(Debug)]
pub enum NodeKind {
    /// Output of a combinational cell.
    Gate {
        cell: String,
        inst: String,
        out_pin: String,
        func: Rc<BoolExpr>,
        /// `(pin name used in func, node driving that pin)`
        inputs: Vec<(String, NodeId)>,
    },
    /// The same signal as `src` (possibly inverted): assign or module boundary.
    Alias {
        src: NodeId,
        inv: bool,
        via: &'static str,
    },
    Endpoint {
        ep: EndpointId,
        inv: bool,
    },
    Const(bool),
}

#[derive(Debug)]
pub struct Node {
    pub name: String,
    /// Inside the instance the user asked about.
    pub in_target: bool,
    /// Number of gates between this node and the target.
    pub depth: u32,
    pub kind: NodeKind,
}

pub struct Cone {
    pub target: NodeId,
    pub nodes: Vec<Node>,
    pub endpoints: Vec<Endpoint>,
    /// Exploration order: the target first, then its fan-in by depth.
    pub order: Vec<NodeId>,
    /// Every node, each after all the nodes it depends on.
    pub topo: Vec<NodeId>,
    /// Names of bits that exist in the netlist, below the bits of an endpoint
    /// bus, but are not part of the cone (e.g. `cnt[0]` when only `cnt[3:1]`
    /// is read).
    pub siblings: Vec<String>,
    pub notes: Vec<String>,
    pub truncated: bool,
}

impl Cone {
    pub fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id as usize]
    }

    /// Nodes this node reads.
    pub fn inputs(&self, id: NodeId) -> Vec<NodeId> {
        match &self.nodes[id as usize].kind {
            NodeKind::Gate { inputs, .. } => inputs.iter().map(|(_, n)| *n).collect(),
            NodeKind::Alias { src, .. } => vec![*src],
            _ => Vec::new(),
        }
    }

    /// Plain-text rendering, one node per line, in exploration order.
    pub fn dump(&self) -> String {
        let mut s = String::new();
        let inv = |v: bool| if v { "!" } else { "" };
        for &id in &self.order {
            let n = self.node(id);
            let rhs = match &n.kind {
                NodeKind::Gate {
                    cell, inst, inputs, ..
                } => {
                    let pins: Vec<String> = inputs
                        .iter()
                        .map(|(p, i)| format!("{p}={}", self.node(*i).name))
                        .collect();
                    format!("{cell} {inst} ({})", pins.join(", "))
                }
                NodeKind::Alias { src, inv: i, via } => {
                    format!("{}{} ({via})", inv(*i), self.node(*src).name)
                }
                NodeKind::Endpoint { ep, inv: i } => {
                    let e = &self.endpoints[*ep as usize];
                    format!("{}[{}] {}", inv(*i), e.kind.label(), e.name)
                }
                NodeKind::Const(v) => format!("const {}", *v as u8),
            };
            s.push_str(&format!("d{} {} = {rhs}\n", n.depth, n.name));
        }
        s
    }
}

struct Ctx {
    module: u32,
    /// `(parent context, instance index in the parent module)`
    parent: Option<(u32, u32)>,
    /// Instance path from the top, without a leading slash.
    path: String,
    /// Module boundaries between this context and the target instance.
    hier: u32,
}

#[derive(Hash, PartialEq, Eq)]
enum EpKey {
    /// A flop or latch: one endpoint however many of its outputs are used.
    Cell(u32, u32),
    /// One bit of one pin of an instance.
    Pin(u32, u32, u32, u32),
    /// A named input pin left floating.
    Floating(u32, u32, String),
    /// An endpoint that belongs to exactly one node.
    Node(NodeId),
    ConstX,
}

enum Driver<'d> {
    Assign(BitRef, bool),
    AssignExpr,
    Builtin { inst: u32, gate: Builtin },
    LibOut { inst: u32, conn: u32, pos: u32, cell: &'d CellDef, pin: &'d PinDef },
    ChildOut { inst: u32, conn: u32, pos: u32, module: u32, port: u32 },
    PortIn { port: u32, off: u32 },
}

/// Where an endpoint's name came from, to look for the other bits of its bus.
#[derive(Clone, Copy)]
enum NameSrc {
    /// The name of a register instance: `(context, instance)`.
    RegInst(u32, u32),
    /// The name of a net bit: `(context, bit)`.
    Net(u32, BitId),
}

struct Tracer<'d, 'a> {
    design: &'d Design<'a>,
    opts: TraceOpts,
    ctxs: Vec<Ctx>,
    ctx_of_child: FxHashMap<(u32, u32), u32>,
    target_ctx: u32,
    nodes: Vec<Node>,
    /// `(context, bit)` of each node that stands for a net bit.
    keys: Vec<Option<(u32, BitId)>>,
    node_of: FxHashMap<(u32, BitId), NodeId>,
    expanded: Vec<bool>,
    endpoints: Vec<Endpoint>,
    ep_of: FxHashMap<EpKey, EndpointId>,
    name_src: Vec<(EndpointId, NameSrc)>,
    const_nodes: [Option<NodeId>; 3],
    func_cache: FxHashMap<(usize, usize), Rc<BoolExpr>>,
    heap: BinaryHeap<(Reverse<u32>, NodeId)>,
    order: Vec<NodeId>,
    notes: Vec<String>,
    /// Nets with a known driver that also touch pins of unknown cells.
    assumed_loads: Vec<String>,
    truncated: bool,
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

/// Trace `bit`, a net bit inside the module instance `path`, back to its drivers.
pub fn trace(design: &Design, path: &InstPath, bit: BitId, opts: &TraceOpts) -> Result<Cone> {
    let mut t = Tracer {
        design,
        opts: *opts,
        ctxs: Vec::new(),
        ctx_of_child: FxHashMap::default(),
        target_ctx: 0,
        nodes: Vec::new(),
        keys: Vec::new(),
        node_of: FxHashMap::default(),
        expanded: Vec::new(),
        endpoints: Vec::new(),
        ep_of: FxHashMap::default(),
        name_src: Vec::new(),
        const_nodes: [None; 3],
        func_cache: FxHashMap::default(),
        heap: BinaryHeap::new(),
        order: Vec::new(),
        notes: Vec::new(),
        assumed_loads: Vec::new(),
        truncated: false,
    };
    // Contexts from the top module down to the target instance.
    let depth = path.steps.len() as u32;
    t.ctxs.push(Ctx {
        module: path.top,
        parent: None,
        path: String::new(),
        hier: depth,
    });
    for (i, step) in path.steps.iter().enumerate() {
        let parent = i as u32;
        let p = t.child_path(parent, step.inst)?;
        t.ctxs.push(Ctx {
            module: step.module,
            parent: Some((parent, step.inst)),
            path: p,
            hier: depth - 1 - i as u32,
        });
        t.ctx_of_child.insert((parent, step.inst), parent + 1);
    }
    t.target_ctx = depth;

    let target = t.net_node(t.target_ctx, bit, 0)?;
    while let Some((_, id)) = t.heap.pop() {
        if std::mem::replace(&mut t.expanded[id as usize], true) {
            continue;
        }
        t.order.push(id);
        if t.keys[id as usize].is_some() && !t.is_endpoint(id) {
            t.expand(id)?;
        }
    }
    if t.truncated {
        t.note(format!(
            "the cone is larger than --max-nodes ({}); nets far from the target were not traced (TRUNCATED)",
            t.opts.max_nodes
        ));
    }
    if !t.assumed_loads.is_empty() {
        let n = t.assumed_loads.len();
        let mut shown: Vec<String> = t.assumed_loads.iter().take(8).cloned().collect();
        if n > 8 {
            shown.push(format!("... and {} more", n - 8));
        }
        t.note(format!(
            "{n} net(s) with a known driver also connect to pins of unknown cells; those pins are              assumed to be loads: {}",
            shown.join("; ")
        ));
    }
    let topo = t.topo_sort(target);
    let siblings = t.siblings()?;
    Ok(Cone {
        target,
        nodes: t.nodes,
        endpoints: t.endpoints,
        order: t.order,
        topo,
        siblings,
        notes: t.notes,
        truncated: t.truncated,
    })
}

impl<'d, 'a> Tracer<'d, 'a> {
    fn module(&self, ctx: u32) -> Result<&'d Module<'a>> {
        self.design.module(self.ctxs[ctx as usize].module)
    }

    fn child_path(&self, ctx: u32, inst: u32) -> Result<String> {
        let name = text(self.module(ctx)?.inst_name(inst));
        let base = &self.ctxs[ctx as usize].path;
        Ok(if base.is_empty() {
            name
        } else {
            format!("{base}/{name}")
        })
    }

    /// Prefix for names in `ctx`: nothing inside the target instance, an
    /// absolute `/path/` everywhere else.
    fn prefix(&self, ctx: u32) -> String {
        if ctx == self.target_ctx {
            return String::new();
        }
        let p = &self.ctxs[ctx as usize].path;
        if p.is_empty() {
            "/".into()
        } else {
            format!("/{p}/")
        }
    }

    fn note(&mut self, s: String) {
        if !self.notes.contains(&s) {
            self.notes.push(s);
        }
    }

    fn is_endpoint(&self, id: NodeId) -> bool {
        matches!(self.nodes[id as usize].kind, NodeKind::Endpoint { .. })
    }

    fn push_node(&mut self, name: String, ctx: u32, depth: u32, kind: NodeKind) -> NodeId {
        let id = self.nodes.len() as u32;
        self.nodes.push(Node {
            name,
            in_target: ctx == self.target_ctx,
            depth,
            kind,
        });
        self.keys.push(None);
        self.expanded.push(false);
        self.heap.push((Reverse(depth), id));
        id
    }

    fn endpoint(&mut self, key: EpKey, e: Endpoint) -> EndpointId {
        if let Some(&id) = self.ep_of.get(&key) {
            return id;
        }
        let id = self.endpoints.len() as u32;
        self.endpoints.push(e);
        self.ep_of.insert(key, id);
        id
    }

    fn plain_endpoint(&mut self, key: EpKey, kind: EndpointKind, name: String, detail: String) -> EndpointId {
        self.endpoint(
            key,
            Endpoint {
                kind,
                name,
                detail,
                inst: None,
                cell: None,
            },
        )
    }

    /// Turn node `id` into an endpoint of its own.
    fn set_endpoint(&mut self, id: NodeId, kind: EndpointKind, detail: String) {
        let name = self.nodes[id as usize].name.clone();
        let ep = self.plain_endpoint(EpKey::Node(id), kind, name, detail);
        if let Some((ctx, bit)) = self.keys[id as usize] {
            self.name_src.push((ep, NameSrc::Net(ctx, bit)));
        }
        self.nodes[id as usize].kind = NodeKind::Endpoint { ep, inv: false };
    }

    /// Bits that exist in the netlist below the bits of each endpoint bus but
    /// are not in the cone. Knowing they exist lets the report say
    /// `cnt[3:0] < 10` for a wire that only reads `cnt[3:1]`.
    fn siblings(&self) -> Result<Vec<String>> {
        let have: FxHashSet<&str> = self.endpoints.iter().map(|e| e.name.as_str()).collect();
        // Highest index seen per bus, with the source of one of its bits.
        let mut buses: Vec<(String, i64, NameSrc)> = Vec::new();
        let mut slot: FxHashMap<String, usize> = FxHashMap::default();
        for &(ep, src) in &self.name_src {
            let (base, Some(idx)) = split_index(&self.endpoints[ep as usize].name) else {
                continue;
            };
            match slot.get(&base) {
                Some(&i) => {
                    if idx > buses[i].1 {
                        buses[i].1 = idx;
                        buses[i].2 = src;
                    }
                }
                None => {
                    slot.insert(base.clone(), buses.len());
                    buses.push((base, idx, src));
                }
            }
        }
        let mut out = Vec::new();
        for (base, top, src) in buses {
            if !(1..=4096).contains(&top) {
                continue;
            }
            for i in 0..top {
                let name = format!("{base}[{i}]");
                if !have.contains(name.as_str()) && self.bit_exists(src, i)? {
                    out.push(name);
                }
            }
        }
        Ok(out)
    }

    /// Does bit `index` of the bus that `src` belongs to exist in the netlist?
    fn bit_exists(&self, src: NameSrc, index: i64) -> Result<bool> {
        match src {
            NameSrc::Net(ctx, bit) => {
                let m = self.module(ctx)?;
                let (net, _) = m.net_of_bit(bit);
                Ok(m.nets[net as usize].is_vec && m.bit_of(net, index as i32).is_some())
            }
            NameSrc::RegInst(ctx, inst) => {
                let m = self.module(ctx)?;
                let name = text(m.inst_name(inst));
                let (base, Some(_)) = split_index(&name) else {
                    return Ok(false);
                };
                // Same spelling as the bit we know: `x_reg[3]` or `x_reg_3_`.
                let other = if name.ends_with(']') {
                    format!("{base}[{index}]")
                } else {
                    format!("{base}_{index}_")
                };
                Ok(match m.find_inst(other.as_bytes()) {
                    Some(i) => matches!(
                        self.design.cell_ref(m.inst_cell(i)),
                        CellRef::Lib(c) if c.is_sequential()
                    ),
                    None => false,
                })
            }
        }
    }

    /// The node for net bit `(ctx, bit)`, created on first use.
    fn net_node(&mut self, ctx: u32, bit: BitId, depth: u32) -> Result<NodeId> {
        if let Some(&n) = self.node_of.get(&(ctx, bit)) {
            // A shorter route to a node not yet expanded lowers its depth.
            if depth < self.nodes[n as usize].depth && !self.expanded[n as usize] {
                self.nodes[n as usize].depth = depth;
                self.heap.push((Reverse(depth), n));
            }
            return Ok(n);
        }
        let name = format!("{}{}", self.prefix(ctx), self.module(ctx)?.bit_name(bit));
        let id = self.push_node(name, ctx, depth, NodeKind::Const(false));
        self.keys[id as usize] = Some((ctx, bit));
        self.node_of.insert((ctx, bit), id);
        if self.nodes.len() > self.opts.max_nodes {
            self.truncated = true;
            self.set_endpoint(
                id,
                EndpointKind::Truncated,
                "not traced: the cone exceeds --max-nodes".into(),
            );
        }
        Ok(id)
    }

    /// Shared node for a constant: 0, 1 or x.
    fn const_node(&mut self, r: BitRef, depth: u32) -> NodeId {
        let slot = match r {
            BitRef::CONST0 => 0,
            BitRef::CONST1 => 1,
            _ => 2,
        };
        if let Some(n) = self.const_nodes[slot] {
            return n;
        }
        let n = match slot {
            0 => self.push_node("1'b0".into(), u32::MAX, depth, NodeKind::Const(false)),
            1 => self.push_node("1'b1".into(), u32::MAX, depth, NodeKind::Const(true)),
            _ => {
                let ep = self.plain_endpoint(
                    EpKey::ConstX,
                    EndpointKind::ConstX,
                    "1'bx".into(),
                    "x or z constant in the netlist".into(),
                );
                self.push_node(
                    "1'bx".into(),
                    u32::MAX,
                    depth,
                    NodeKind::Endpoint { ep, inv: false },
                )
            }
        };
        self.const_nodes[slot] = Some(n);
        n
    }

    /// Make node `id` equal to `src` (a bit reference in context `ctx`).
    fn set_from_ref(&mut self, id: NodeId, ctx: u32, src: BitRef, inv: bool, via: &'static str) -> Result<()> {
        let depth = self.nodes[id as usize].depth;
        match src {
            BitRef::CONST0 => self.nodes[id as usize].kind = NodeKind::Const(inv),
            BitRef::CONST1 => self.nodes[id as usize].kind = NodeKind::Const(!inv),
            BitRef::CONSTX => {
                let ep = self.plain_endpoint(
                    EpKey::ConstX,
                    EndpointKind::ConstX,
                    "1'bx".into(),
                    "x or z constant in the netlist".into(),
                );
                self.nodes[id as usize].kind = NodeKind::Endpoint { ep, inv: false };
            }
            BitRef::OPEN => self.set_endpoint(id, EndpointKind::Undriven, format!("left unconnected ({via})")),
            _ => {
                let src = self.net_node(ctx, src.as_net().unwrap(), depth)?;
                self.nodes[id as usize].kind = NodeKind::Alias { src, inv, via };
            }
        }
        Ok(())
    }

    /// `inst.pin` or `inst.pin[i]` for bit `pos` of a connection.
    fn pin_name(&self, m: &Module, inst: u32, conn: u32, pos: u32) -> String {
        let pin = match m.conn_pin(conn) {
            Some(p) => text(p),
            None => format!("#{}", conn - m.inst_conns(inst).start),
        };
        let width = m.conn_bits(conn).len() as u32;
        let inst = text(m.inst_name(inst));
        if width > 1 {
            format!("{inst}.{pin}[{}]", width - 1 - pos)
        } else {
            format!("{inst}.{pin}")
        }
    }

    // ---- expansion ---------------------------------------------------------

    fn expand(&mut self, id: NodeId) -> Result<()> {
        let (ctx, bit) = self.keys[id as usize].unwrap();
        let m = self.module(ctx)?;
        let name = self.nodes[id as usize].name.clone();
        let prefix = self.prefix(ctx);

        let mut drivers: Vec<Driver<'d>> = Vec::new();
        let mut tristate: Vec<String> = Vec::new();
        let mut unknown: Vec<(u32, u32, u32)> = Vec::new();

        if let Some((src, kind)) = m.assign_driver(bit) {
            drivers.push(match kind {
                AssignKind::Complex => Driver::AssignExpr,
                k => Driver::Assign(src, k == AssignKind::Invert),
            });
            if m.multi_assigned(bit) {
                self.note(format!("net {name} is the target of several assigns; only the last is followed"));
            }
        }
        for p in m.pins_on(bit) {
            match self.design.pin_info(m, p.inst, p.conn) {
                PinInfo::LibPin { cell, pin } => match pin.dir {
                    Dir::Output | Dir::Internal if pin.three_state => {
                        tristate.push(self.pin_name(m, p.inst, p.conn, p.pos))
                    }
                    Dir::Output | Dir::Internal => drivers.push(Driver::LibOut {
                        inst: p.inst,
                        conn: p.conn,
                        pos: p.pos,
                        cell,
                        pin,
                    }),
                    Dir::Inout => tristate.push(self.pin_name(m, p.inst, p.conn, p.pos)),
                    Dir::Input => {}
                },
                PinInfo::ModulePort { module, port, dir } => match dir {
                    Dir::Output => drivers.push(Driver::ChildOut {
                        inst: p.inst,
                        conn: p.conn,
                        pos: p.pos,
                        module,
                        port,
                    }),
                    Dir::Inout => tristate.push(self.pin_name(m, p.inst, p.conn, p.pos)),
                    _ => {}
                },
                PinInfo::BuiltinPin { gate, index } => {
                    if index == 0 {
                        drivers.push(Driver::Builtin { inst: p.inst, gate });
                    }
                }
                PinInfo::Unknown => unknown.push((p.inst, p.conn, p.pos)),
            }
        }
        if let Some((port, off)) = m.port_of_bit(bit) {
            match m.ports[port as usize].dir {
                Dir::Input => drivers.push(Driver::PortIn { port, off }),
                Dir::Inout => tristate.push(format!("inout port {}", text(m.ports[port as usize].name))),
                _ => {}
            }
        }

        let unknown_desc: Vec<String> = unknown
            .iter()
            .map(|&(i, c, p)| format!("{} ({})", self.pin_name(m, i, c, p), text(m.inst_cell(i))))
            .collect();

        if !tristate.is_empty() {
            self.set_endpoint(
                id,
                EndpointKind::Inout,
                format!("driven through three-state or inout pins: {}", tristate.join(", ")),
            );
            return Ok(());
        }
        if drivers.is_empty() {
            match unknown.as_slice() {
                [] => self.set_endpoint(id, EndpointKind::Undriven, "no driver found".into()),
                [(inst, conn, pos)] => {
                    // The only candidate driver: name the endpoint after the pin.
                    let cell = text(m.inst_cell(*inst));
                    let e = Endpoint {
                        kind: EndpointKind::Unknown,
                        name: format!("{prefix}{}", self.pin_name(m, *inst, *conn, *pos)),
                        detail: format!(
                            "cell {cell} is neither in the library nor a module of the netlist; \
                             its pin is the only possible driver of {name}"
                        ),
                        inst: Some(format!("{prefix}{}", text(m.inst_name(*inst)))),
                        cell: Some(cell),
                    };
                    let ep = self.endpoint(EpKey::Pin(ctx, *inst, *conn, *pos), e);
                    self.nodes[id as usize].kind = NodeKind::Endpoint { ep, inv: false };
                }
                _ => self.set_endpoint(
                    id,
                    EndpointKind::Unknown,
                    format!(
                        "no known driver; connected to pins of cells that are neither in the library \
                         nor modules of the netlist: {}",
                        unknown_desc.join(", ")
                    ),
                ),
            }
            return Ok(());
        }
        if !unknown.is_empty() {
            let pins: Vec<String> = unknown_desc.iter().map(|d| format!("{prefix}{d}")).collect();
            self.assumed_loads.push(format!("{name} <- {}", pins.join(", ")));
        }
        if drivers.len() > 1 {
            let list: Vec<String> = drivers
                .iter()
                .map(|d| match d {
                    Driver::Assign(..) | Driver::AssignExpr => "an assign".to_string(),
                    Driver::Builtin { inst, gate } => {
                        format!("{} {}", gate.name(), text(m.inst_name(*inst)))
                    }
                    Driver::LibOut { inst, cell, .. } => {
                        format!("{} ({})", text(m.inst_name(*inst)), cell.name)
                    }
                    Driver::ChildOut { inst, .. } => {
                        format!("{} ({})", text(m.inst_name(*inst)), text(m.inst_cell(*inst)))
                    }
                    Driver::PortIn { port, .. } => {
                        format!("input port {}", text(m.ports[*port as usize].name))
                    }
                })
                .collect();
            self.set_endpoint(
                id,
                EndpointKind::MultiDriver,
                format!("{} drivers: {}", list.len(), list.join(", ")),
            );
            return Ok(());
        }

        match drivers.pop().unwrap() {
            Driver::Assign(src, inv) => self.set_from_ref(id, ctx, src, inv, "assign")?,
            Driver::AssignExpr => self.set_endpoint(
                id,
                EndpointKind::ComplexAssign,
                "driven by an assign whose right-hand side is an expression; not interpreted".into(),
            ),
            Driver::Builtin { inst, gate } => {
                let n = m.inst_conns(inst).len();
                let func = Rc::new(builtin_func(gate, n));
                self.set_gate(id, ctx, inst, "Y".into(), func, None)?;
            }
            Driver::LibOut {
                inst,
                conn,
                pos,
                cell,
                pin,
            } => self.lib_output(id, ctx, inst, conn, pos, cell, pin)?,
            Driver::ChildOut {
                inst,
                conn,
                pos,
                module,
                port,
            } => {
                let inst_name = text(m.inst_name(inst));
                if !self.opts.cross || self.ctxs[ctx as usize].hier + 1 > self.opts.max_hier_depth {
                    self.boundary_note();
                    self.set_endpoint(
                        id,
                        EndpointKind::SubmoduleOut,
                        format!(
                            "output of instance {prefix}{inst_name} (module {}); not traced into it",
                            text(m.inst_cell(inst))
                        ),
                    );
                    return Ok(());
                }
                let child = match self.ctx_of_child.get(&(ctx, inst)) {
                    Some(&c) => c,
                    None => {
                        let c = self.ctxs.len() as u32;
                        self.ctxs.push(Ctx {
                            module,
                            parent: Some((ctx, inst)),
                            path: self.child_path(ctx, inst)?,
                            hier: self.ctxs[ctx as usize].hier + 1,
                        });
                        self.ctx_of_child.insert((ctx, inst), c);
                        c
                    }
                };
                let off = m.conn_bits(conn).len() as u32 - 1 - pos;
                match self.module(child)?.port_bit(port, off) {
                    Some(b) => self.set_from_ref(id, child, BitRef::net(b), false, "submodule output")?,
                    None => self.set_endpoint(
                        id,
                        EndpointKind::Undriven,
                        format!("instance {prefix}{inst_name}: the port is narrower than its connection"),
                    ),
                }
            }
            Driver::PortIn { port, off } => {
                let port_name = text(m.ports[port as usize].name);
                let Some((parent, inst)) = self.ctxs[ctx as usize].parent else {
                    self.set_endpoint(id, EndpointKind::PortIn, "input port of the top module".into());
                    return Ok(());
                };
                if !self.opts.cross || self.ctxs[parent as usize].hier > self.opts.max_hier_depth {
                    self.boundary_note();
                    self.set_endpoint(
                        id,
                        EndpointKind::PortIn,
                        format!("input port {port_name} of the instance; not traced into the parent"),
                    );
                    return Ok(());
                }
                let pm = self.module(parent)?;
                let first = pm.inst_conns(inst).start;
                let conn = pm.inst_conns(inst).find(|&c| match pm.conn_pin(c) {
                    Some(p) => p == m.ports[port as usize].name,
                    None => c - first == port,
                });
                let bits = conn.map(|c| pm.conn_bits(c)).unwrap_or(&[]);
                match bits.len().checked_sub(1 + off as usize) {
                    Some(i) => self.set_from_ref(id, parent, bits[i], false, "input port")?,
                    None => self.set_endpoint(
                        id,
                        EndpointKind::Undriven,
                        format!("input port {port_name} is not connected in the parent module"),
                    ),
                }
            }
        }
        Ok(())
    }

    fn boundary_note(&mut self) {
        self.note(
            "tracing stopped at a module boundary (cross-module tracing is limited by --no-cross / --max-hier-depth)"
                .into(),
        );
    }

    /// Node `id` is driven by output `pin` of library cell instance `inst`.
    #[allow(clippy::too_many_arguments)]
    fn lib_output(
        &mut self,
        id: NodeId,
        ctx: u32,
        inst: u32,
        conn: u32,
        pos: u32,
        cell: &'d CellDef,
        pin: &'d PinDef,
    ) -> Result<()> {
        let m = self.module(ctx)?;
        let prefix = self.prefix(ctx);
        let inst_name = text(m.inst_name(inst));

        // Sequential cell: an output that depends on the state is where tracing stops.
        if let Some((iq, iqn)) = &cell.state_vars {
            let mut vars = Vec::new();
            if let Some(f) = &pin.function {
                f.vars(&mut vars);
            }
            if pin.function.is_none() || vars.iter().any(|v| v == iq || v == iqn) {
                let kind = if cell.kind == CellKind::Latch {
                    EndpointKind::Latch
                } else {
                    EndpointKind::Reg
                };
                let polarity = match &pin.function {
                    Some(BoolExpr::Var(v)) => Some(v == iqn),
                    Some(BoolExpr::Not(x)) => match &**x {
                        BoolExpr::Var(v) => Some(v == iq),
                        _ => None,
                    },
                    _ => None,
                };
                let (key, name, inv) = match polarity {
                    Some(inv) => {
                        let (name, src) = self.reg_name(ctx, inst, cell, iq)?;
                        let key = EpKey::Cell(ctx, inst);
                        if !self.ep_of.contains_key(&key)
                            && let Some(src) = src
                        {
                            self.name_src.push((self.endpoints.len() as u32, src));
                        }
                        (key, name, inv)
                    }
                    // Function mixes the state with other pins: this pin is its own endpoint.
                    None => (
                        EpKey::Pin(ctx, inst, conn, pos),
                        format!("{prefix}{}", self.pin_name(m, inst, conn, pos)),
                        false,
                    ),
                };
                let ep = self.endpoint(
                    key,
                    Endpoint {
                        kind,
                        name,
                        detail: String::new(),
                        inst: Some(format!("{prefix}{inst_name}")),
                        cell: Some(cell.name.clone()),
                    },
                );
                self.nodes[id as usize].kind = NodeKind::Endpoint { ep, inv };
                return Ok(());
            }
        }
        match &pin.function {
            None => {
                let e = Endpoint {
                    kind: EndpointKind::BlackBox,
                    name: format!("{prefix}{}", self.pin_name(m, inst, conn, pos)),
                    detail: format!(
                        "library cell {} gives no boolean function for pin {} (macro or state-table cell)",
                        cell.name, pin.name
                    ),
                    inst: Some(format!("{prefix}{inst_name}")),
                    cell: Some(cell.name.clone()),
                };
                let ep = self.endpoint(EpKey::Pin(ctx, inst, conn, pos), e);
                self.nodes[id as usize].kind = NodeKind::Endpoint { ep, inv: false };
            }
            Some(BoolExpr::Const(v)) => self.nodes[id as usize].kind = NodeKind::Const(*v),
            Some(f) => {
                let key = (cell as *const CellDef as usize, pin as *const PinDef as usize);
                let func = self
                    .func_cache
                    .entry(key)
                    .or_insert_with(|| Rc::new(f.clone()))
                    .clone();
                self.set_gate(id, ctx, inst, pin.name.clone(), func, Some(cell))?;
            }
        }
        Ok(())
    }

    /// Display name of a register: the RTL signal if the instance is named
    /// `<signal>_reg...`, else the net on its Q pin. Also says where the name
    /// came from.
    fn reg_name(
        &self,
        ctx: u32,
        inst: u32,
        cell: &CellDef,
        iq: &str,
    ) -> Result<(String, Option<NameSrc>)> {
        let m = self.module(ctx)?;
        let prefix = self.prefix(ctx);
        let inst_name = text(m.inst_name(inst));
        if let Some(sig) = reg_signal_name(&inst_name) {
            return Ok((format!("{prefix}{sig}"), Some(NameSrc::RegInst(ctx, inst))));
        }
        let q = cell
            .pins
            .iter()
            .position(|p| matches!(&p.function, Some(BoolExpr::Var(v)) if v == iq));
        if let Some(q) = q
            && let Some(conn) = find_conn(m, inst, cell.pins[q].name.as_bytes(), Some(q))
            && let [bit] = m.conn_bits(conn)
            && let Some(b) = bit.as_net()
        {
            return Ok((
                format!("{prefix}{}", m.bit_name(b)),
                Some(NameSrc::Net(ctx, b)),
            ));
        }
        Ok((format!("{prefix}{inst_name}"), None))
    }

    /// Node `id` is a combinational function of the pins of `inst`.
    fn set_gate(
        &mut self,
        id: NodeId,
        ctx: u32,
        inst: u32,
        out_pin: String,
        func: Rc<BoolExpr>,
        cell: Option<&CellDef>,
    ) -> Result<()> {
        let m = self.module(ctx)?;
        let prefix = self.prefix(ctx);
        let inst_name = text(m.inst_name(inst));
        let depth = self.nodes[id as usize].depth + 1;
        let mut vars = Vec::new();
        func.vars(&mut vars);
        let mut inputs = Vec::with_capacity(vars.len());
        for var in vars {
            // Library pins connect by name (or by pin order when positional);
            // gate primitive inputs are `I<k>` = terminal k.
            let conn = match cell {
                Some(c) => {
                    let pos = c.pins.iter().position(|p| p.name == var);
                    find_conn(m, inst, var.as_bytes(), pos)
                }
                None => var[1..]
                    .parse::<u32>()
                    .ok()
                    .map(|k| m.inst_conns(inst).start + k)
                    .filter(|c| m.inst_conns(inst).contains(c)),
            };
            let bits = conn.map(|c| m.conn_bits(c)).unwrap_or(&[]);
            let node = match bits.last() {
                Some(&r) => {
                    if bits.len() > 1 {
                        self.note(format!(
                            "{prefix}{inst_name}: pin {var} is connected to {} bits; the last one is used",
                            bits.len()
                        ));
                    }
                    match r.as_net() {
                        Some(b) => self.net_node(ctx, b, depth)?,
                        None if r == BitRef::OPEN => self.floating(ctx, inst, &inst_name, &var, depth),
                        None => self.const_node(r, depth),
                    }
                }
                None => self.floating(ctx, inst, &inst_name, &var, depth),
            };
            inputs.push((var, node));
        }
        self.nodes[id as usize].kind = NodeKind::Gate {
            cell: text(m.inst_cell(inst)),
            inst: if inst_name.is_empty() {
                "<unnamed>".into()
            } else {
                format!("{prefix}{inst_name}")
            },
            out_pin,
            func,
            inputs,
        };
        Ok(())
    }

    /// Endpoint node for an input pin that is not connected to anything.
    fn floating(&mut self, ctx: u32, inst: u32, inst_name: &str, pin: &str, depth: u32) -> NodeId {
        let name = format!("{}{inst_name}.{pin}", self.prefix(ctx));
        let ep = self.plain_endpoint(
            EpKey::Floating(ctx, inst, pin.to_string()),
            EndpointKind::Undriven,
            name.clone(),
            "input pin is not connected".into(),
        );
        self.push_node(name, ctx, depth, NodeKind::Endpoint { ep, inv: false })
    }

    // ---- ordering ----------------------------------------------------------

    /// Order nodes so each comes after the nodes it reads. An edge that closes
    /// a combinational loop is cut and replaced by a LOOP endpoint.
    fn topo_sort(&mut self, target: NodeId) -> Vec<NodeId> {
        #[derive(Clone, Copy, PartialEq)]
        enum Mark {
            New,
            Open,
            Done,
        }
        let mut mark = vec![Mark::New; self.nodes.len()];
        let mut topo = Vec::with_capacity(self.nodes.len());
        // (node, index of the next input to visit)
        let mut stack: Vec<(NodeId, usize)> = vec![(target, 0)];
        mark[target as usize] = Mark::Open;
        while let Some(&mut (n, ref mut next)) = stack.last_mut() {
            let input = match &self.nodes[n as usize].kind {
                NodeKind::Gate { inputs, .. } => inputs.get(*next).map(|(_, i)| *i),
                NodeKind::Alias { src, .. } => (*next == 0).then_some(*src),
                _ => None,
            };
            let slot = *next;
            *next += 1;
            let Some(child) = input else {
                mark[n as usize] = Mark::Done;
                topo.push(n);
                stack.pop();
                continue;
            };
            match mark[child as usize] {
                Mark::Done => {}
                Mark::New => {
                    mark[child as usize] = Mark::Open;
                    stack.push((child, 0));
                }
                Mark::Open => {
                    // `child` is on the current path: n -> child closes a loop.
                    let name = self.nodes[child as usize].name.clone();
                    let depth = self.nodes[n as usize].depth + 1;
                    self.note(format!(
                        "combinational loop through {name}; it is cut there and treated as an endpoint (LOOP)"
                    ));
                    let ep = self.plain_endpoint(
                        EpKey::Node(child),
                        EndpointKind::Loop,
                        name.clone(),
                        "combinational loop: this net depends on itself".into(),
                    );
                    let cut = self.push_node(name, u32::MAX, depth, NodeKind::Endpoint { ep, inv: false });
                    self.nodes[cut as usize].in_target = self.nodes[child as usize].in_target;
                    self.order.push(cut);
                    mark.push(Mark::Done);
                    topo.push(cut);
                    match &mut self.nodes[n as usize].kind {
                        NodeKind::Gate { inputs, .. } => inputs[slot].1 = cut,
                        NodeKind::Alias { src, .. } => *src = cut,
                        _ => unreachable!(),
                    }
                }
            }
        }
        topo
    }
}

/// Connection of `inst` to the pin called `name`; for positional connections,
/// the one at index `pos`.
fn find_conn(m: &Module, inst: u32, name: &[u8], pos: Option<usize>) -> Option<u32> {
    let conns = m.inst_conns(inst);
    conns
        .clone()
        .find(|&c| m.conn_pin(c) == Some(name))
        .or_else(|| {
            let c = conns.start + pos? as u32;
            (conns.contains(&c) && m.conn_pin(c).is_none()).then_some(c)
        })
}

/// Function of a gate primitive with `terminals` terminals; inputs are `I1..`.
fn builtin_func(gate: Builtin, terminals: usize) -> BoolExpr {
    let ins: Vec<BoolExpr> = (1..terminals.max(2))
        .map(|k| BoolExpr::Var(format!("I{k}")))
        .collect();
    let xor = |v: Vec<BoolExpr>| {
        v.into_iter()
            .reduce(|a, b| BoolExpr::Xor(Box::new(a), Box::new(b)))
            .unwrap()
    };
    let not = |e: BoolExpr| BoolExpr::Not(Box::new(e));
    let first = || BoolExpr::Var("I1".into());
    match gate {
        Builtin::And => BoolExpr::And(ins),
        Builtin::Or => BoolExpr::Or(ins),
        Builtin::Nand => not(BoolExpr::And(ins)),
        Builtin::Nor => not(BoolExpr::Or(ins)),
        Builtin::Xor => xor(ins),
        Builtin::Xnor => not(xor(ins)),
        Builtin::Not => not(first()),
        Builtin::Buf => first(),
    }
}
