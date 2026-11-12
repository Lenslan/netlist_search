//! Boolean analysis of a traced cone: naming, BDDs and expression lifting.

pub mod bdd;
pub mod expr;
pub mod isop;
pub mod lift;
pub mod bus;
pub mod words;

#[cfg(test)]
mod tests_lift;

/// What the analysis found out about one wire of the cone.
#[derive(Debug, Clone, Default)]
pub struct WireInfo {
    /// The wire as an expression of the cone's endpoints, if small enough.
    pub endpoint_form: Option<String>,
    /// Number of endpoints the wire depends on.
    pub support: usize,
    /// The function was too large to compute; only the local form is exact.
    pub cut: bool,
    /// Other wires of the cone with the same (or the inverted) function.
    pub aliases: Vec<String>,
}

/// Result of analysing a cone, indexed by node id.
#[derive(Debug, Default)]
pub struct Analysis {
    pub wires: Vec<Option<WireInfo>>,
    pub notes: Vec<String>,
}
