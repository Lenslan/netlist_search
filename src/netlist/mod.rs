//! Gate-level Verilog netlist: lexing, module index, per-module parsing.

pub mod design;
pub mod index;
pub mod lexer;
pub mod parser;

#[cfg(test)]
mod tests_design;
#[cfg(test)]
mod tests_index;
#[cfg(test)]
mod tests_lexer;
#[cfg(test)]
mod tests_parser;
