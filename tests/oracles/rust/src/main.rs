//! The Rust oracle for tests/run_tests.py: the `asn1` crate (rust-asn1,
//! a DER-only reader), at the version Cargo.lock pins with its checksum.
//!
//! Each line of standard input is one request in the form `der serve`
//! reads (octets in lower-case hex, `-` for none; integers in decimal),
//! and each answer is in the form it writes: `OK ...` or `FAIL`. A request
//! the crate cannot answer is answered `n/a`, and a line this program
//! cannot read `error`. A line may end in LF or CR LF.
//!
//!     decode HEX     the element at the start of the octets, and the rest
//!     all HEX        the element that is the whole input
//!     readint HEX    the integer that contents octets encode
//!     writeint INT   the contents octets of an integer
//!     encode TREE    n/a
//!     valid TREE     n/a
//!
//! `strip_tlv` reads each element as a `Tlv` and gives the octets after
//! it; a constructed element's contents are read the same way, element by
//! element, to their end. An element of the universal class with number
//! 1, 2 or 5 must also parse, with `parse_single`, as a `bool`, a `BigInt`
//! or a `Null`. The walk keeps its own stack, so deep nesting does not
//! use the machine stack.
//!
//! readint frames the contents octets as an INTEGER element (the length
//! octets are written here) and parses it as a `BigInt`: FAIL when that
//! fails, else the value from parsing it as an `i64`, or n/a when the
//! contents are longer than 8 octets. writeint writes an `i64` with
//! `write_single`, and prints the contents octets of what it writes; an
//! integer outside the `i64` range is n/a.

use std::fmt::Write as _;
use std::io::{self, BufRead, BufWriter, Write};

fn field(f: &str) -> Option<Vec<u8>> {
    if f == "-" {
        return Some(Vec::new());
    }
    if f.is_empty() || f.len() % 2 != 0 {
        return None;
    }
    let digit = |c: u8| match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        _ => None,
    };
    f.as_bytes()
        .chunks(2)
        .map(|p| Some(digit(p[0])? * 16 + digit(p[1])?))
        .collect()
}

fn to_field(b: &[u8]) -> String {
    if b.is_empty() {
        return "-".to_string();
    }
    let mut s = String::with_capacity(2 * b.len());
    for x in b {
        write!(s, "{x:02x}").unwrap();
    }
    s
}

/// Reads one element with `strip_tlv`, checks its contents if it is a
/// universal BOOLEAN, INTEGER or NULL, and writes the start of its tree.
/// Gives its contents when it is constructed, and the rest.
fn one<'a>(data: &'a [u8], out: &mut String) -> Option<(Option<&'a [u8]>, &'a [u8])> {
    let (tlv, rest) = asn1::strip_tlv(data).ok()?;
    let tag = tlv.tag();
    // The class as the crate numbers it: universal 0, application 1,
    // context-specific 2, private 3, as in Table 1 of X.690.
    let cls = tag.class() as u8;
    if cls == 0 {
        let ok = match tag.value() {
            1 => asn1::parse_single::<bool>(tlv.full_data()).is_ok(),
            2 => asn1::parse_single::<asn1::BigInt<'_>>(tlv.full_data()).is_ok(),
            5 => asn1::parse_single::<asn1::Null>(tlv.full_data()).is_ok(),
            _ => true,
        };
        if !ok {
            return None;
        }
    }
    if tag.is_constructed() {
        write!(out, "c{}.{}(", cls, tag.value()).unwrap();
        Some((Some(tlv.data()), rest))
    } else {
        write!(out, "p{}.{}.{}", cls, tag.value(), to_field(tlv.data())).unwrap();
        Some((None, rest))
    }
}

/// The element at the start of `data`, as a tree, and the rest.
fn element(data: &[u8]) -> Option<(String, &[u8])> {
    let mut out = String::new();
    let (body, rest) = one(data, &mut out)?;
    // The unread contents of each open constructed element, and whether
    // its next element is its first.
    let mut stack: Vec<(&[u8], bool)> = Vec::new();
    if let Some(b) = body {
        stack.push((b, true));
    }
    while let Some(top) = stack.last_mut() {
        if top.0.is_empty() {
            stack.pop();
            out.push(')');
            continue;
        }
        if !top.1 {
            out.push(',');
        }
        top.1 = false;
        let (body, after) = one(top.0, &mut out)?;
        top.0 = after;
        if let Some(b) = body {
            stack.push((b, true));
        }
    }
    Some((out, rest))
}

fn der_length(n: usize) -> Vec<u8> {
    if n < 128 {
        return vec![n as u8];
    }
    let digits: Vec<u8> = n.to_be_bytes().iter().copied().skip_while(|&d| d == 0).collect();
    let mut out = vec![0x80 | digits.len() as u8];
    out.extend(digits);
    out
}

fn readint(c: &[u8]) -> String {
    let mut framed = vec![0x02];
    framed.extend(der_length(c.len()));
    framed.extend_from_slice(c);
    if asn1::parse_single::<asn1::BigInt<'_>>(&framed).is_err() {
        return "FAIL".to_string();
    }
    if c.len() > 8 {
        return "n/a".to_string();
    }
    match asn1::parse_single::<i64>(&framed) {
        Ok(v) => format!("OK {v}"),
        Err(_) => "unreadable".to_string(),
    }
}

fn writeint(f: &str) -> String {
    let digits = f.strip_prefix('-').unwrap_or(f);
    if digits.is_empty() || !digits.bytes().all(|c| c.is_ascii_digit()) {
        return "error".to_string();
    }
    let v: i64 = match f.parse::<i64>() {
        Ok(v) => v,
        Err(_) => return "n/a".to_string(),
    };
    let framed = match asn1::write_single(&v) {
        Ok(b) => b,
        Err(_) => return "FAIL".to_string(),
    };
    match asn1::strip_tlv(&framed) {
        Ok((tlv, rest)) if rest.is_empty() => format!("OK {}", to_field(tlv.data())),
        _ => "unreadable".to_string(),
    }
}

fn answer(line: &str) -> String {
    let parts: Vec<&str> = line.split(' ').collect();
    if parts.len() != 2 {
        return "error".to_string();
    }
    let (op, f) = (parts[0], parts[1]);
    match op {
        "decode" | "all" | "readint" => {
            let b = match field(f) {
                Some(b) => b,
                None => return "error".to_string(),
            };
            if op == "readint" {
                return readint(&b);
            }
            match element(&b) {
                Some((tree, rest)) if op == "decode" => format!("OK {} {}", tree, to_field(rest)),
                Some((tree, rest)) if rest.is_empty() => format!("OK {tree}"),
                _ => "FAIL".to_string(),
            }
        }
        "writeint" => writeint(f),
        "encode" | "valid" => "n/a".to_string(),
        _ => "error".to_string(),
    }
}

fn main() {
    let stdin = io::stdin();
    let mut input = stdin.lock();
    let mut out = BufWriter::with_capacity(1 << 20, io::stdout().lock());
    let mut line = String::new();
    loop {
        line.clear();
        if input.read_line(&mut line).expect("reading standard input") == 0 {
            break;
        }
        let l = line.strip_suffix('\n').unwrap_or(&line);
        let l = l.strip_suffix('\r').unwrap_or(l);
        writeln!(out, "{}", answer(l)).unwrap();
    }
    out.flush().unwrap();
}
