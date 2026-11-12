use super::lexer::*;

fn toks(s: &str) -> Vec<String> {
    let mut lx = Lexer::new(s.as_bytes());
    let mut out = Vec::new();
    loop {
        let t = lx.next();
        let text = |b: &[u8]| String::from_utf8_lossy(b).into_owned();
        out.push(match t {
            Tok::Ident(b) => format!("I:{}", text(b)),
            Tok::Escaped(b) => format!("E:{}", text(b)),
            Tok::Number(b) => format!("N:{}", text(b)),
            Tok::Str(b) => format!("S:{}", text(b)),
            Tok::Punct(c) => format!("P:{}", c as char),
            Tok::Eof => break,
        });
    }
    out
}

#[test]
fn simple_module_header() {
    assert_eq!(
        toks("module top (a, b);"),
        ["I:module", "I:top", "P:(", "I:a", "P:,", "I:b", "P:)", "P:;"]
    );
}

#[test]
fn escaped_identifier_runs_to_whitespace_and_drops_backslash() {
    assert_eq!(toks("\\cnt_reg[3] ("), ["E:cnt_reg[3]", "P:("]);
    assert_eq!(toks("\\a/b;c\t,"), ["E:a/b;c", "P:,"]);
}

#[test]
fn escaped_keyword_is_not_a_keyword() {
    assert_eq!(toks("\\module x"), ["E:module", "I:x"]);
}

#[test]
fn comments_attributes_and_directives_are_skipped() {
    assert_eq!(toks("a // x ; y\n b /* y\n z */ c"), ["I:a", "I:b", "I:c"]);
    assert_eq!(toks("(* keep = 1 *) wire"), ["I:wire"]);
    assert_eq!(toks("`timescale 1ns/1ps\nmodule"), ["I:module"]);
}

#[test]
fn numbers_and_sized_literals() {
    assert_eq!(
        toks("1'b0 4'hF 12 8'sd3 'b1 2'bx0"),
        ["N:1'b0", "N:4'hF", "N:12", "N:8'sd3", "N:'b1", "N:2'bx0"]
    );
}

#[test]
fn strings_are_one_token() {
    assert_eq!(toks("\"a;b\" x"), ["S:a;b", "I:x"]);
}

#[test]
fn connection_punctuation() {
    assert_eq!(
        toks(".A(n1[3:0]),"),
        ["P:.", "I:A", "P:(", "I:n1", "P:[", "N:3", "P::", "N:0", "P:]", "P:)", "P:,"]
    );
}

#[test]
fn identifiers_may_contain_dollar_and_digits() {
    assert_eq!(toks("a$b_1 _x9"), ["I:a$b_1", "I:_x9"]);
}

#[test]
fn skip_to_semicolon_ignores_semicolons_in_names_comments_and_strings() {
    let src = b"U1 (.A(\\x;y ), /* ; */ .B(\"s;\") // ;\n ); next";
    let mut lx = Lexer::new(src);
    assert!(lx.skip_past_semicolon());
    assert_eq!(lx.next(), Tok::Ident(b"next"));
    assert!(!lx.skip_past_semicolon(), "no further semicolon");
}

#[test]
fn peek_does_not_consume() {
    let mut lx = Lexer::new(b"a b");
    assert_eq!(lx.peek(), Tok::Ident(b"a"));
    assert_eq!(lx.next(), Tok::Ident(b"a"));
    assert_eq!(lx.next(), Tok::Ident(b"b"));
    assert_eq!(lx.next(), Tok::Eof);
    assert_eq!(lx.next(), Tok::Eof);
}

#[test]
fn line_numbers_are_one_based() {
    let src = b"a\nb\n\nc";
    assert_eq!(line_of(src, 0), 1);
    assert_eq!(line_of(src, 2), 2);
    assert_eq!(line_of(src, 5), 4);
}
