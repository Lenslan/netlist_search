# netlist_search Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** 一个 Rust 命令行工具：给定门级 Verilog 网表、Liberty 库、例化路径和 wire，反向追溯其扇入锥到寄存器/黑盒/端口，并把每根中间 wire 的门逻辑还原成可读的 RTL 风格表达式。

**Architecture:** mmap + 模块索引 + 按需解析模块体；在实例上下文中做位级反向追溯得到锥图；对锥内每个 net 位构建 ROBDD（关于端点变量），再用"分解 + 假设—验证识别器"还原成字级表达式，每条表达式反算 BDD 自检。

**Tech Stack:** Rust 1.89，`clap`（derive）、`memmap2`、`rustc-hash`、`memchr`、`anyhow`、`rayon`。BDD、Liberty/Verilog 解析均自实现。

**Spec:** `docs/superpowers/specs/2026-11-12-netlist-trace-design.md`

**说明：** 本计划由同一会话直接执行，因此每个任务给出文件、接口签名、测试用例与验收命令，不重复抄写完整实现代码。所有任务遵循 TDD：先写测试、看它失败、再实现、看它通过、提交。

---

## 文件结构

| 文件 | 职责 |
|---|---|
| `Cargo.toml` | 依赖与 release profile（`opt-level=3`、`lto="thin"`、`codegen-units=1`、`debug=1`） |
| `src/lib.rs` | 模块声明 |
| `src/main.rs` | CLI：参数解析、加载、调用 trace/logic/report |
| `src/liberty/func.rs` | Liberty `function` 表达式 → `BoolExpr` |
| `src/liberty/parser.rs` | Liberty 流式解析（跳过 timing/power 等无关 group） |
| `src/liberty/mod.rs` | `CellLib` / `CellDef` / `PinDef` / `CellKind` |
| `src/netlist/lexer.rs` | 字节级 Verilog 词法分析 |
| `src/netlist/index.rs` | 第一遍：模块字节范围 + 被例化类型名集合 |
| `src/netlist/parser.rs` | 模块体解析 → `Module`（端口、net、实例、连接、assign、反向索引） |
| `src/netlist/design.rs` | `Design`：惰性模块存储、cell 类型判定、顶层判定、例化路径解析、wire 查找 |
| `src/trace/mod.rs` | 实例上下文中的锥遍历、端点分类、预算、环检测 |
| `src/logic/bdd.rs` | ROBDD |
| `src/logic/bus.rs` | 名字 → (基名, 位索引)；寄存器名推导；变量排序 |
| `src/logic/expr.rs` | 输出表达式 AST：渲染 + 反算 BDD |
| `src/logic/isop.rs` | Minato–Morreale ISOP |
| `src/logic/lift.rs` | 分解 + 识别器 |
| `src/logic/words.rs` | 字级 BDD 向量运算（加、减、乘、比较、移位） |
| `src/logic/sim.rs` | 锥的位并行仿真 + 宽乘法匹配 |
| `src/logic/mod.rs` | `analyze(cone) -> Analysis`：建 BDD、切点、调 lift、自检、别名 |
| `src/report.rs` | 文本报告 |
| `src/synth.rs` | 测试/生成器用的门级构造器（字级运算 → 门 → Verilog 文本） |
| `src/bin/gen_netlist.rs` | 大规模合成网表 + lib 生成器 |
| `tests/fixtures/*.lib`, `*.v` | 手写夹具 |
| `tests/*.rs` | 集成测试 |

---

## M1：加载

### Task 1: 工程骨架
**Files:** Create `Cargo.toml`, `src/lib.rs`, `src/main.rs`, `.gitignore`
- [ ] `cargo init --name netlist_search`（保留已有文件），加依赖与 release profile，`.gitignore` 含 `/target`、`/bench_data`
- [ ] `cargo build` 通过；提交

### Task 2: Liberty function 表达式
**Files:** Create `src/liberty/func.rs`
接口：
```rust
pub enum BoolExpr { Const(bool), Var(String), Not(Box<BoolExpr>), And(Vec<BoolExpr>), Or(Vec<BoolExpr>), Xor(Box<BoolExpr>, Box<BoolExpr>) }
pub fn parse_function(s: &str) -> Result<BoolExpr, String>;
impl BoolExpr { pub fn vars(&self, out: &mut Vec<String>); pub fn eval(&self, f: &dyn Fn(&str) -> bool) -> bool; }
```
优先级（Liberty）：`!`/后缀 `'` > `^` > `&`/`*`/并置 > `|`/`+`。
- [ ] 测试：`"A&B"`、`"(A B)'"`（并置与后缀取反）、`"A+B*C"`、`"!A^B&C"` 为 `((!A)^B)&C`、`"A1 A2 + B1'"`、`"0"`/`"1"`、`"IQ"`、非法输入报错；用 `eval` 穷举真值表比对
- [ ] 实现、通过、提交

### Task 3: Liberty 解析
**Files:** Create `src/liberty/parser.rs`, `src/liberty/mod.rs`, `tests/fixtures/basic.lib`
接口：
```rust
pub enum Dir { Input, Output, Inout, Internal }
pub enum CellKind { Comb, Ff, Latch, Other }          // Other: 有 statetable 或输出无 function
pub struct PinDef { pub name: String, pub dir: Dir, pub function: Option<BoolExpr>, pub three_state: bool, pub is_bus: bool }
pub struct CellDef { pub name: String, pub pins: Vec<PinDef>, pub kind: CellKind, pub state_vars: Option<(String, String)> }
pub struct CellLib { /* name -> CellDef */ }
impl CellLib { pub fn new() -> Self; pub fn load_file(&mut self, path: &Path) -> anyhow::Result<()>; pub fn load_str(&mut self, text: &str) -> anyhow::Result<()>; pub fn get(&self, name: &[u8]) -> Option<&CellDef>; pub fn len(&self) -> usize; }
impl CellDef { pub fn pin(&self, name: &[u8]) -> Option<&PinDef>; }
```
- [ ] 夹具 `basic.lib`：INVX1、BUFX2、AND2X1、OR2X1、NAND2X1、NOR2X1、NOR4X1、XOR2X1、XNOR2X1、MUX2X1、AOI22X1、OAI21X1、TIEHI、TIELO、DFFRX1（Q/QN，`ff(IQ,IQN)`）、SDFFX1（扫描）、LATX1（`latch`）、TBUFX1（`three_state`）、带 `bus` 的 RAM16X4（无 function）、带 `timing(){}` 嵌套表、`/* */` 注释、`\` 续行
- [ ] 测试：cell 数、各 pin 方向、function 真值、`kind`、`state_vars`、bus pin、未知 cell 返回 `None`；截断文件报错含行号
- [ ] 实现（流式：无关 group 用括号计数跳过）、通过、提交

### Task 4: 网表词法
**Files:** Create `src/netlist/lexer.rs`
接口：
```rust
pub enum Tok<'a> { Ident(&'a [u8]), Number(&'a [u8]), Punct(u8), Eof }   // 转义标识符去掉前导 '\'
pub struct Lexer<'a> { pub src: &'a [u8], pub pos: usize }
impl<'a> Lexer<'a> { pub fn new(src: &'a [u8]) -> Self; pub fn next(&mut self) -> Tok<'a>; pub fn peek(&mut self) -> Tok<'a>; }
pub fn line_of(src: &[u8], pos: usize) -> usize;
```
- [ ] 测试：`\cnt_reg[3] ` → `Ident(b"cnt_reg[3]")`；`//`、`/* */`、`(* attr *)`、`` `timescale `` 行被跳过；`1'b0`、`4'hF`、`12` 为 `Number`；字符串跳过；标点序列
- [ ] 实现、通过、提交

### Task 5: 模块索引
**Files:** Create `src/netlist/index.rs`
接口：
```rust
pub struct ModuleEntry<'a> { pub name: &'a [u8], pub src: &'a [u8], pub start: usize, pub end: usize }   // [start,end) 为 `module` 关键字之后到 `endmodule` 之前
pub struct ModuleIndex<'a> { pub modules: Vec<ModuleEntry<'a>>, /* by_name, instantiated */ }
impl<'a> ModuleIndex<'a> { pub fn build(sources: &[&'a [u8]]) -> anyhow::Result<Self>; pub fn find(&self, name: &[u8]) -> Option<u32>; pub fn is_instantiated(&self, name: &[u8]) -> bool; pub fn top_candidates(&self) -> Vec<u32>; }
```
- [ ] 测试：多模块、多文件、注释里的 `module` 不算、转义名、`top_candidates`（未被例化者）、重复模块名取第一个
- [ ] 实现、通过、提交

### Task 6: 模块体解析
**Files:** Create `src/netlist/parser.rs`, `tests/fixtures/small.v`
接口：
```rust
pub type BitId = u32;
pub enum BitRef { Net(BitId), Const0, Const1, ConstX, Open }
pub struct Port<'a> { pub name: &'a [u8], pub dir: Dir, pub net: u32 }
pub struct Net<'a> { pub name: &'a [u8], pub msb: i32, pub lsb: i32, pub is_vec: bool, pub base: BitId }
pub struct Inst<'a> { pub cell: &'a [u8], pub name: &'a [u8], pub conn_start: u32, pub conn_len: u32 }
pub struct Conn<'a> { pub pin: Option<&'a [u8]>, pub bit_start: u32, pub bit_len: u32 }   // None = 位置连接；位序 MSB 在前
pub enum AssignKind { Alias, Invert, Complex }
pub struct Module<'a> { pub name, pub ports, pub nets, pub insts, pub conns, pub conn_bits: Vec<BitRef>, pub assigns: Vec<(BitRef, BitRef, AssignKind)>, pub nbits: u32, /* net_by_name, bit->pins CSR, bit->assign */ }
impl<'a> Module<'a> {
  pub fn parse(entry: &ModuleEntry<'a>) -> anyhow::Result<Self>;
  pub fn parse_header(entry: &ModuleEntry<'a>) -> anyhow::Result<Vec<(&'a [u8], Dir, i32, i32, bool)>>;
  pub fn find_net(&self, name: &[u8]) -> Option<u32>;
  pub fn bit_of(&self, net: u32, index: i32) -> Option<BitId>;
  pub fn bit_name(&self, bit: BitId) -> String;                       // "n12" / "cnt[3]"
  pub fn pins_on(&self, bit: BitId) -> &[(u32 /*inst*/, u32 /*conn*/, u32 /*pos in conn*/)];
  pub fn assign_driver(&self, bit: BitId) -> Option<(BitRef, AssignKind)>;
  pub fn port_of_bit(&self, bit: BitId) -> Option<(u32 /*port*/, u32 /*pos from msb*/)>;
  pub fn find_inst(&self, name: &[u8]) -> Option<u32>;
}
```
- [ ] 测试：ANSI 与非 ANSI 端口、`wire [7:0] a`、升序范围 `[0:7]`、位选/部分选/拼接/重复 `{2{a}}`/常量、`.pin()` 空连接、位置连接、一条语句多实例、`assign a = b` / `= ~b` / `= 1'b0` / 复杂表达式、`supply0/1`、隐式 net、门原语 `and (y,a,b)`、`pins_on` 反向索引、语法错误带行号
- [ ] 实现、通过、提交

### Task 7: Design 与路径解析
**Files:** Create `src/netlist/design.rs`, `src/netlist/mod.rs`, `tests/fixtures/hier.v`
接口：
```rust
pub enum CellRef<'a> { Lib(&'a CellDef), Module(u32), Builtin(Builtin), Unknown }
pub struct Design<'a> { pub index: ModuleIndex<'a>, pub lib: &'a CellLib, /* lazily parsed modules + headers */ }
impl<'a> Design<'a> {
  pub fn new(index: ModuleIndex<'a>, lib: &'a CellLib) -> Self;
  pub fn module(&self, id: u32) -> anyhow::Result<&Module<'a>>;
  pub fn cell_ref(&self, cell: &[u8]) -> CellRef<'_>;
  pub fn pin_dir(&self, cell: &[u8], conn: &Conn, conn_idx_in_inst: usize) -> Option<Dir>;
  pub fn resolve_top(&self, top: Option<&str>, path: &str) -> anyhow::Result<(u32, String /*剩余路径*/)>;
  pub fn resolve_path(&self, top: u32, path: &str) -> anyhow::Result<Vec<(u32 /*module*/, u32 /*inst*/)>>;
  pub fn resolve_suffix(&self, top: u32, path: &str) -> anyhow::Result<Vec<String>>;   // 并行全解析后的唯一后缀匹配
}
```
- [ ] 测试：`top/u_a/u_b` 与 `u_a/u_b` 等价；`.` 分隔；展平名 `\u_a/u_b/U1 ` 的最长匹配；多顶层候选靠路径消歧；找不到时错误信息含相近候选；后缀匹配唯一/多个
- [ ] 实现、通过、提交

---

## M2：追溯与报告骨架

### Task 8: 锥遍历
**Files:** Create `src/trace/mod.rs`, `tests/trace.rs`, `tests/fixtures/endpoints.v`
接口：
```rust
pub struct TraceOpts { pub max_nodes: usize, pub max_hier_depth: u32, pub cross: bool }
pub enum EndpointKind { Reg, Latch, Unknown, PortIn, Inout, ConstX, Undriven, MultiDriver, Loop, Truncated, SubmoduleOut, ComplexAssign }
pub struct Endpoint { pub kind: EndpointKind, pub name: String /*显示名*/, pub detail: String }
pub enum NodeKind { Gate { cell: String, inst: String, out_pin: String, func: BoolExpr, inputs: Vec<(String /*pin*/, NodeId)> }, Alias { src: NodeId, inv: bool, via: &'static str }, Endpoint { ep: u32, inv: bool }, Const(bool) }
pub struct Node { pub name: String, pub in_target: bool, pub depth: u32, pub kind: NodeKind }
pub struct Cone { pub target: NodeId, pub nodes: Vec<Node>, pub endpoints: Vec<Endpoint>, pub notes: Vec<String>, pub topo: Vec<NodeId> /*输入先于输出*/ }
pub fn trace(design: &Design, path: &[(u32, u32)], top: u32, bit: BitId, opts: &TraceOpts) -> anyhow::Result<Cone>;
```
- [ ] 测试（每类端点一个用例）：REG（Q 与 QN 共用同一端点、QN 取反）、LATCH、未知 cell（无已知驱动 → UNKNOWN；有已知驱动 → 视作负载并写 note）、lib 中无 function 的宏、顶层 PORT-IN、三态、常量与 tie cell、UNDRIVEN、MULTI-DRIVER、组合环 → LOOP、`max_nodes` → TRUNCATED、`assign` 别名与取反、向下进子模块、向上经输入端口进父模块、`cross=false` 停在边界、`max_hier_depth`
- [ ] 实现（BFS 建图 → DFS 拓扑序并切环）、通过、提交

### Task 9: 报告骨架 + CLI
**Files:** Create `src/report.rs`, modify `src/main.rs`, create `tests/cli.rs`
- [ ] 测试：对 `small.v` 运行库 API，报告含 `=== Cone of`、`Endpoints`、每根 wire 的 `local:` 行、`Notes`；`--wire` 为整根总线时逐位输出；错误路径的退出码非零
- [ ] 实现 `render_report(cone, analysis: Option<&Analysis>, opts) -> String`、`main`（大栈线程中运行）、通过、提交

---

## M3：BDD 与基础还原

### Task 10: ROBDD
**Files:** Create `src/logic/bdd.rs`
接口：
```rust
pub type Bd = u32;  pub const FALSE: Bd = 0;  pub const TRUE: Bd = 1;
pub struct Blowup;
pub struct Bdd { /* nodes, unique, caches, limit */ }
impl Bdd {
  pub fn new(node_limit: usize) -> Self;  pub fn new_var(&mut self) -> u32;  pub fn var(&mut self, v: u32) -> Bd;
  pub fn not(&mut self, a: Bd) -> Result<Bd, Blowup>;  pub fn and/or/xor(&mut self, a: Bd, b: Bd) -> Result<Bd, Blowup>;  pub fn ite(&mut self, c: Bd, t: Bd, e: Bd) -> Result<Bd, Blowup>;
  pub fn restrict(&mut self, f: Bd, v: u32, val: bool) -> Result<Bd, Blowup>;
  pub fn exists(&mut self, f: Bd, vars: &[u32]) -> Result<Bd, Blowup>;  pub fn forall(...) -> Result<Bd, Blowup>;
  pub fn support(&self, f: Bd) -> Vec<u32>;  pub fn size(&self, f: Bd) -> usize;  pub fn node_count(&self) -> usize;
  pub fn eval(&self, f: Bd, assign: &dyn Fn(u32) -> bool) -> bool;
  pub fn top_var(&self, f: Bd) -> Option<u32>;  pub fn cofactors(&self, f: Bd, v: u32) -> (Bd, Bd);
  pub fn sat_count(&self, f: Bd, vars: &[u32]) -> u128;      // f 的支撑须 ⊆ vars
  pub fn min_max(&self, f: Bd, vars_msb_first: &[u32]) -> Option<(u128, u128)>;
  pub fn set_budget(&mut self, extra_nodes: usize);          // 单次求值的新增节点上限
}
```
- [ ] 测试：规范性（`a&b == b&a` 同一节点）、德摩根、`ite`、`restrict`、`exists`、`support`、`sat_count`、`min_max`、随机表达式与真值表比对、节点上限触发 `Blowup`
- [ ] 实现、通过、提交

### Task 11: 总线命名与变量排序
**Files:** Create `src/logic/bus.rs`
接口：
```rust
pub fn split_index(name: &str) -> (String, Option<i64>);      // "cnt[3]"→("cnt",3)；"cnt_3_"→("cnt",3)；"n12"→("n12",None)
pub fn reg_signal_name(inst: &str) -> Option<String>;         // "cnt_reg[3]"→"cnt[3]"；"cnt_reg_3_"→"cnt[3]"；"cnt_reg"→"cnt"；不含 _reg → None
pub struct VarInfo { pub name: String, pub bus: u32, pub index: Option<i64> }
pub fn order_vars(names: &[String]) -> (Vec<VarInfo>, Vec<usize> /*排序后的原下标*/);   // 标量在前；总线按位宽升序；等宽按位索引降序交错
```
- [ ] 测试：以上各例、层次前缀 `u_a/cnt[3]`、二维 `mem[3][2]`、排序结果（`sel` 在 `idx[1:0]` 前，`idx` 在 `a[3:0]`/`b[3:0]` 前，`a[3],b[3],a[2],b[2]…`）
- [ ] 实现、通过、提交

### Task 12: 输出表达式 AST
**Files:** Create `src/logic/expr.rs`, `src/logic/words.rs`
接口：
```rust
pub enum BitSrc { Var(u32), Const(bool) }
pub struct Word { pub bits: Vec<BitSrc> /*LSB 在前*/, pub signed: bool }
pub enum CmpOp { Eq, Ne, Lt, Le, Gt, Ge }
pub enum SelKind { Index, Shr, Ashr, Shl }
pub enum Arith { Add, Sub, Mul }
pub enum Expr {
  Const(bool), Var(u32), Not(Rc<Expr>), And(Vec<Rc<Expr>>), Or(Vec<Rc<Expr>>), Xor(Vec<Rc<Expr>>),
  Mux(Rc<Expr>, Rc<Expr>, Rc<Expr>),
  Cmp { op: CmpOp, a: Word, b: Word },
  Inside { a: Word, vals: Vec<u128> },
  ArithBit { op: Arith, a: Word, b: Word, cin: Option<u32>, bit: u32 },
  Select { kind: SelKind, data: Word, sel: Word, off: i64 },
}
impl Expr { pub fn size(&self) -> usize; pub fn to_bdd(&self, bdd: &mut Bdd) -> Result<Bd, Blowup>; pub fn render(&self, vars: &[VarInfo], radix: Radix) -> String; }
// words.rs
pub fn word_bdds(bdd, w: &Word, width: usize) -> Vec<Bd>;   // 按 signed 做零/符号扩展
pub fn add(bdd, a: &[Bd], b: &[Bd], cin: Bd) -> Result<Vec<Bd>, Blowup>;  pub fn sub(...);  pub fn mul(...);
pub fn ult(bdd, a: &[Bd], b: &[Bd]) -> Result<Bd, Blowup>;  pub fn eq(...);  pub fn slt(...);
```
- [ ] 测试：渲染 `cnt[3:0] == 5`、`sel ? a : b`、`!a & b | c`（括号按优先级最少化）、`{a[5], a[3:2]}`、`a[3:0] inside {5, 9}`、`(cnt[3:0] + 1)[3]`、`bitmap[idx[3:0]]`、`(d[7:0] >> s[2:0])[2]`、`--radix hex/bin`；`to_bdd` 与手工构造的 BDD 相等；`words` 各运算对随机数穷举比对
- [ ] 实现、通过、提交

### Task 13: ISOP + 基础 lift
**Files:** Create `src/logic/isop.rs`, `src/logic/lift.rs`
接口：
```rust
pub fn isop(bdd: &mut Bdd, f: Bd, max_cubes: usize) -> Result<Option<Vec<Vec<(u32, bool)>>>, Blowup>;
pub struct Lifter<'a> { /* bdd, vars, memo, limits */ }
impl<'a> Lifter<'a> { pub fn new(bdd: &'a mut Bdd, vars: &'a [VarInfo]) -> Self; pub fn lift(&mut self, f: Bd) -> Option<Rc<Expr>>; }   // None = 超预算
```
本任务实现：常量/字面量、立方体内的总线分组（`==`）、单总线 `==`/`!=`、不相交支撑 AND/OR/XOR 分解、标量变量上的 mux/Shannon（含 `s & g`、`s | g`、`s ^ g` 特例）、SOP 回退、按 `size` 取最小、memo。
- [ ] 测试：**`grammar.example` 两条逐字还原**——`cnt[0] & !cnt[1] & cnt[2] & !cnt[3]` → `cnt[3:0] == 5`；`sel & a | !sel & b` → `sel ? a : b`；另有 `mode & (state==5 | state==9)`、`a ^ b ^ c`、`!(cnt==3)` → `cnt[1:0] != 3`、随机 6 变量函数：`lift` 结果 `to_bdd` 必须等于原函数
- [ ] 实现、通过、提交

### Task 14: 分析集成（端点式、自检、别名、过滤）
**Files:** Create `src/logic/mod.rs`, modify `src/report.rs`, `src/main.rs`, create `tests/fixtures/fsm.v`, `tests/e2e.rs`
接口：
```rust
pub struct AnalyzeOpts { pub radix: Radix, pub expand: bool, pub strict: bool, pub node_limit: usize }
pub struct WireInfo { pub endpoint_form: Option<String>, pub support: usize, pub cut: bool, pub unproven: bool, pub aliases: Vec<String>, pub mismatch: bool }
pub struct Analysis { pub wires: Vec<Option<WireInfo>> /*按 NodeId*/, pub notes: Vec<String> }
pub fn analyze(cone: &Cone, opts: &AnalyzeOpts) -> Analysis;
```
- [ ] 测试（端到端，`fsm.v` 为手写门级 FSM）：目标 wire 的端点式为预期字符串；`n*` 中间线出现 `state[3:0] == 5`；别名行；`--filter state`；端点式超预算时省略并显示依赖数，`--expand` 时打印；人为注入错误表达式时自检退回并写 `INTERNAL` note（用测试专用钩子）
- [ ] 实现（按 topo 求 BDD；Blowup → 切点变量）、通过、提交

---

## M4：字级识别器

### Task 15: 门级构造器
**Files:** Create `src/synth.rs`
接口：
```rust
pub struct Synth { /* 实例与 net 列表 */ }
impl Synth {
  pub fn new(module: &str) -> Self;  pub fn input(&mut self, name: &str, width: usize) -> Vec<Sig>;  pub fn reg(&mut self, name: &str, width: usize) -> Vec<Sig>;   // 生成 DFF，返回 Q
  pub fn not/and/or/xor/mux(&mut self, ...) -> Sig;
  pub fn add(&mut self, a: &[Sig], b: &[Sig]) -> Vec<Sig>;  pub fn sub(...);  pub fn mul(...);  pub fn ult(...) -> Sig;  pub fn eq_const(...) -> Sig;
  pub fn shr(&mut self, a: &[Sig], s: &[Sig]) -> Vec<Sig>;  pub fn shl(...);  pub fn index(&mut self, a: &[Sig], idx: &[Sig]) -> Sig;
  pub fn name_net(&mut self, s: Sig, name: &str);  pub fn output(&mut self, name: &str, s: &[Sig]);
  pub fn emit(&self) -> String;     // Verilog 文本，使用 basic.lib 的 cell
}
```
随机化选门（如 AND 用 NAND+INV 或 NOR+INV 实现）以保证识别不依赖结构。
- [ ] 测试：生成的网表可被解析；用 `trace`+BDD 求值与字级参考模型在随机向量上一致
- [ ] 实现、通过、提交

### Task 16: 比较识别器
**Files:** Modify `src/logic/lift.rs`
- [ ] 测试（经 `Synth` 生成门级再端到端还原）：`cnt[3:0] < 10`、`cnt[3:0] >= 6`、`cnt[7:0] >= 16 & cnt[7:0] < 200`（区间）、`cnt[3:0] inside {1, 4, 7}`、`a[3:0] < b[3:0]`、`a[3:0] >= b[3:0]`、`a[3:0] == b[3:0]`、有符号 `$signed(a[3:0]) < $signed(b[3:0])`、带使能 `en & (cnt[3:0] < 10)`
- [ ] 实现单总线谓词（`sat_count` + `min_max` 区间检测、离散集合）、双总线假设—验证；通过、提交

### Task 17: 索引与变量移位
**Files:** Modify `src/logic/lift.rs`
- [ ] 测试：`bitmap[idx[3:0]]`（16 位）、`bitmap[idx[2:0]]` 配 6 位数据（越界为 0）、`(d[7:0] >> s[2:0])[2]`、`(d[7:0] << s[2:0])[5]`、算术右移 `>>>`、数据为零散标量时的 `mux(s[1:0]){0: a, 1: b, 2: c, 3: d}`、select 位宽 11 时不识别而回退
- [ ] 实现选择位枚举（cofactor → 字面量/常量 → 映射分类）；通过、提交

### Task 18: 加减
**Files:** Modify `src/logic/lift.rs`
- [ ] 测试：`(cnt[3:0] + 1)[3]`、`(cnt[3:0] - 1)[2]`、`(cnt[7:0] + 37)[6]`（常量反解）、`(a[3:0] + b[3:0])[3]`、进位 `(a[3:0] + b[3:0])[4]`、`(a[3:0] - b[3:0])[3]`、`(a[3:0] + b[3:0] + cin)[2]`、错位 `(a[7:4] + b[3:0])[2]`（按切片对齐可识别）、计数器 D 端 `rst ? 1'b0 : (en ? (cnt[3:0] + 1)[3] : cnt[3])`
- [ ] 实现；通过、提交

### Task 19: 乘法与仿真匹配
**Files:** Modify `src/logic/lift.rs`, create `src/logic/sim.rs`, modify `src/logic/mod.rs`
接口：
```rust
pub struct Sim { /* 每节点 64 个 u64 */ }
impl Sim { pub fn run(cone: &Cone, var_of_endpoint: &[u32], rounds: usize, seed: u64) -> Sim; pub fn sig(&self, n: NodeId) -> &[u64]; pub fn var_sig(&self, v: u32) -> &[u64]; }
pub fn match_wide_mul(sim: &Sim, node: NodeId, vars: &[VarInfo], support: &[u32]) -> Option<Expr>;
```
- [ ] 测试：`(a[3:0] * b[3:0])[5]` BDD 精确命中；`(a[3:0] * 5)[4]` 常量乘；16×16 乘法某一位 → 命中且标注 `[simulation-matched, unproven]`；`--strict` 下同一 wire 只给局部式；非乘法的随机逻辑不被仿真误报
- [ ] 实现；通过、提交

---

## M5：规模与性能

### Task 20: 合成网表生成器与实测
**Files:** Create `src/bin/gen_netlist.rs`, `README.md`
- [ ] `gen_netlist --lines 10000000 --out bench_data/` 生成约 620M 的层次化网表 + lib + `queries.txt`（若干例化路径与 wire），内容含 FSM、计数器、比较器、桶形移位器、SRAM 黑盒、多例化模块、转义标识符、展平层次名
- [ ] 小规模（`--lines 20000`）生成结果纳入集成测试：全部 query 运行成功且自检无 `INTERNAL` note
- [ ] release 构建后在 620M 网表上实测索引时间、查询时间、峰值内存；与目标（10 s / 15 s / 2 GB）比较；不达标则优化（并行索引等）并复测
- [ ] README：用法、报告说明、识别器清单与限制、实测数字；提交

---

## 自查记录

- 规格覆盖：§2 输入 → T7/T9；§3 报告 → T9/T14；§4 加载 → T4–T7、T20；§5 追溯 → T8；§6 化简 → T10–T19；§7 自检 → T14；§8 错误处理 → T3/T6/T7/T9；§9 测试 → 各任务 + T15/T20。
- 与规格的两处有意差异已回写规格：局部式保留真实连接的 net 名（不穿透 BUF/INV）；端点按位逐行列出。
