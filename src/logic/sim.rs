//! Bit-parallel simulation of a cone, used for the one kind of result that is
//! reported without a proof: a bit of a wide product.
//!
//! The BDD of a multiplier grows exponentially with its width whatever the
//! variable order, so a wide `a * b` cannot be recognised by comparing BDDs.
//! Instead the gates are simulated on random input vectors and compared with
//! the arithmetic product. A match is strong evidence, not a proof, and the
//! report marks it as such.

use crate::trace::{Cone, NodeId, NodeKind};

use super::bus::VarInfo;

/// Number of input vectors every match is checked on.
pub const VECTORS: usize = 4096;
const ROUNDS: usize = VECTORS / 64;

/// Wire `node` behaves like bit `bit` of `a * b` on every simulated vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProductMatch {
    pub node: NodeId,
    /// Variable levels of the operands, least significant bit first.
    pub a: Vec<u32>,
    pub b: Vec<u32>,
    pub signed: bool,
    pub bit: u32,
}

struct Candidate {
    node: NodeId,
    a: Vec<u32>,
    b: Vec<u32>,
    /// `alive[signed][k]`: bit `k` of the product has matched so far.
    alive: [Vec<bool>; 2],
}

/// The two operand buses a wire depends on, as endpoint ids, LSB first.
fn operands(
    cone: &Cone,
    node: NodeId,
    vars: &[VarInfo],
    level_of_ep: &[u32],
    stamp: &mut [u32],
    mark: u32,
) -> Option<(Vec<u32>, Vec<u32>)> {
    let mut eps: Vec<u32> = Vec::new();
    let mut stack = vec![node];
    while let Some(n) = stack.pop() {
        if std::mem::replace(&mut stamp[n as usize], mark) == mark {
            continue;
        }
        match &cone.node(n).kind {
            NodeKind::Endpoint { ep, .. } => {
                eps.push(*ep);
                if eps.len() > 128 {
                    return None;
                }
            }
            _ => stack.extend(cone.inputs(n)),
        }
    }
    eps.sort_unstable();
    eps.dedup();
    // Exactly two buses, each a contiguous run of at least two bits.
    let mut groups: Vec<(u32, Vec<(i64, u32)>)> = Vec::new();
    for ep in eps {
        let v = &vars[level_of_ep[ep as usize] as usize];
        let index = v.index?;
        match groups.iter_mut().find(|(bus, _)| *bus == v.bus) {
            Some((_, bits)) => bits.push((index, ep)),
            None => groups.push((v.bus, vec![(index, ep)])),
        }
    }
    if groups.len() != 2 {
        return None;
    }
    let mut out = Vec::new();
    for (_, mut bits) in groups {
        bits.sort_unstable();
        if !(2..=63).contains(&bits.len()) || bits.windows(2).any(|w| w[1].0 != w[0].0 + 1) {
            return None;
        }
        out.push(bits.into_iter().map(|(_, ep)| ep).collect::<Vec<u32>>());
    }
    let b = out.pop()?;
    let a = out.pop()?;
    Some((a, b))
}

/// One simulation round: 64 input vectors, one bit position each.
fn simulate(cone: &Cone, ep_values: &[u64], out: &mut [u64]) {
    for &id in &cone.topo {
        let flip = |inv: bool| if inv { !0u64 } else { 0 };
        out[id as usize] = match &cone.node(id).kind {
            NodeKind::Const(c) => flip(*c),
            NodeKind::Endpoint { ep, inv } => ep_values[*ep as usize] ^ flip(*inv),
            NodeKind::Alias { src, inv, .. } => out[*src as usize] ^ flip(*inv),
            NodeKind::Gate { func, inputs, .. } => func.eval64(&|pin| {
                inputs
                    .iter()
                    .find(|(p, _)| p == pin)
                    .map_or(0, |(_, n)| out[*n as usize])
            }),
        };
    }
}

fn sign_extend(x: u64, width: usize) -> i128 {
    let x = x as i128;
    if x >> (width - 1) & 1 == 1 { x - (1i128 << width) } else { x }
}

/// Find the wires among `wires` that behave like one bit of the product of
/// the two buses they depend on, on `VECTORS` random input vectors (which
/// include all-zeros and all-ones, and sparse and dense patterns).
pub fn match_products(
    cone: &Cone,
    wires: &[NodeId],
    vars: &[VarInfo],
    level_of_ep: &[u32],
) -> Vec<ProductMatch> {
    let mut stamp = vec![0u32; cone.nodes.len()];
    let mut cands: Vec<Candidate> = Vec::new();
    for (i, &node) in wires.iter().enumerate() {
        if let Some((a, b)) = operands(cone, node, vars, level_of_ep, &mut stamp, i as u32 + 1) {
            let w = a.len() + b.len();
            cands.push(Candidate {
                node,
                a,
                b,
                alive: [vec![true; w], vec![true; w]],
            });
        }
    }
    if cands.is_empty() {
        return Vec::new();
    }

    let mut rng = 0x243f_6a88_85a3_08d3u64;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    let mut ep_values = vec![0u64; cone.endpoints.len()];
    let mut out = vec![0u64; cone.nodes.len()];
    for round in 0..ROUNDS {
        for v in ep_values.iter_mut() {
            *v = match round % 4 {
                1 => next() & next(), // sparse: long runs of zeros
                3 => next() | next(), // dense: long carry chains
                _ => next(),
            };
            if round == 0 {
                // Vector 0 is all zeros, vector 1 all ones.
                *v = (*v & !1) | 2;
            }
        }
        simulate(cone, &ep_values, &mut out);
        for c in cands.iter_mut() {
            if !c.alive.iter().flatten().any(|&x| x) {
                continue;
            }
            let got = out[c.node as usize];
            let (wa, wb) = (c.a.len(), c.b.len());
            for j in 0..64 {
                let value = |eps: &[u32]| {
                    eps.iter().enumerate().fold(0u64, |acc, (i, &ep)| {
                        acc | (ep_values[ep as usize] >> j & 1) << i
                    })
                };
                let (x, y) = (value(&c.a), value(&c.b));
                let products = [
                    x as u128 * y as u128,
                    (sign_extend(x, wa) * sign_extend(y, wb)) as u128,
                ];
                let bit = u128::from(got >> j & 1);
                for (alive, p) in c.alive.iter_mut().zip(products) {
                    for (k, a) in alive.iter_mut().enumerate() {
                        *a &= p >> k & 1 == bit;
                    }
                }
            }
        }
    }

    let mut found = Vec::new();
    for c in cands {
        let only = |alive: &[bool]| {
            let mut hits = alive.iter().enumerate().filter(|(_, a)| **a).map(|(k, _)| k);
            match (hits.next(), hits.next()) {
                (Some(k), None) => Some(k as u32),
                _ => None,
            }
        };
        // The low bits of the signed and unsigned products agree; say unsigned.
        let (signed, bit) = match (only(&c.alive[0]), only(&c.alive[1])) {
            (Some(k), _) => (false, k),
            (None, Some(k)) => (true, k),
            (None, None) => continue,
        };
        let levels = |eps: &[u32]| eps.iter().map(|&e| level_of_ep[e as usize]).collect();
        found.push(ProductMatch {
            node: c.node,
            a: levels(&c.a),
            b: levels(&c.b),
            signed,
            bit,
        });
    }
    found
}
