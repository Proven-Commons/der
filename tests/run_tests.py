#!/usr/bin/env python3
"""Differential tests: the Lean DER reader and writer against a model of
X.690 and four implementations.

The tool answers `decode`, `all`, `encode`, `valid`, `readint` and
`writeint` requests (see the header of Main.lean). Its answers are
checked two ways.

1. Against the model, a Python transcription of Rec. ITU-T X.690
   (02/2021), with Table 1 of X.680 (02/2021) for the universal tags,
   that shares nothing with the Lean code. `read` reads one element as
   clause 8 lays it out, with the restrictions of clauses 10 and 11 and
   of this slice:
   - identifier octets as 8.1.2: numbers 0 to 30 in one octet, 31 and up
     in the high form, whose first subsequent octet does not have bits 7
     to 1 zero, and no number below 31 in the high form;
   - length octets in the definite form and in the fewest octets (8.1.3,
     10.1), never the initial octet 0xFF (8.1.3.5 c);
   - no universal tag 0; the universal types X.690 encodes as
     constructed (8, 11, 16, 17, 29) only constructed; the numbers Table
     1 reserves (15, and 37 on) in either form; every other universal
     type only primitive;
   - a BOOLEAN of one octet, 00 or FF (8.2.1, 11.1), an INTEGER of one
     or more octets in the fewest (8.3.1, 8.3.2), an ENUMERATED the
     same, as it is encoded as its integer (8.4), a NULL with none
     (8.8.2);
   - the contents of a constructed element are elements, one after
     another, which end exactly where it ends.
   `encode` writes a tree (8.1.2, 8.1.3, 10.1), and `read_int` and
   `write_int` the two's complement integers of 8.3. X.690 has four
   classes; for a class number of 4 or more, `encode` writes it as
   `Spec.der` does, the class times 64 taken as an octet, so modulo 4.
   `valid` says whether the slice accepts a tree: every element of a
   class from 0 to 3, the universal tags and contents as `read` checks
   them, and every length within the long form. The model also checks
   that `valid` holds exactly when `read` reads the tree's encoding back
   as the tree. No other content rule (bit strings, object identifiers,
   strings, times, the order of a SET) is checked in this slice. The
   model is checked against the examples X.690 gives. Every answer must
   agree.

2. Against four oracles, on every request each can answer:

   - Go cryptobyte: golang.org/x/crypto/cryptobyte, at the version
     tests/oracles/go/go.mod pins (go.sum holds its hash);
   - Go encoding/asn1: the standard library's package of the installed
     Go, which builds both Go oracles. It is not pinned; the record
     gives the Go version;
   - rust-asn1: the `asn1` crate, at the version and checksum
     tests/oracles/rust/Cargo.lock pins, built with `cargo --locked`;
   - OpenSSL: libcrypto, the version OPENSSL_PINNED, through
     tests/oracles/openssl/wrapper.c built with `cc`.

   Each reads elements with the package's own reader and walks a
   constructed element's contents element by element, checks a
   universal BOOLEAN and INTEGER with the package's own readers for
   them, and prints the tree in the syntax of `der serve` (the program
   in each oracle's folder says how). The programs for encoding/asn1,
   rust-asn1 and OpenSSL also check a NULL; cryptobyte has no reader
   for NULL. Only the OpenSSL program checks ENUMERATED contents, with
   d2i_ASN1_ENUMERATED. Each answers `decode`, `all`, `readint` and
   `writeint` (rust-asn1 gives a value only within 64 bits), and no
   `encode` or `valid`. An oracle that cannot be built or started
   is left out, and the record says so on its `- Oracles left out:`
   line.

   A disagreement is allowed only for a named reason that the model
   confirms: `read`, with the rules the oracle reads by (ORACLE_RULES),
   gives the oracle's answer. The reason names each rule where the two
   part on the way, and each disagreement is counted under its reason.
   Any other disagreement is a failure. The rules:
   - cryptobyte reads no tag number of 31 or more and no length of more
     than 4 octets, checks the form only of BOOLEAN and INTEGER, and has
     no reader for NULL;
   - encoding/asn1 reads tag numbers and lengths up to 2^31 - 1, and
     checks the form only of BOOLEAN, INTEGER and NULL;
   - rust-asn1 reads tag numbers and lengths up to 2^32 - 1, and checks
     the form only of BOOLEAN, INTEGER and NULL;
   - OpenSSL reads what BER allows and DER does not: the indefinite
     length for a constructed element, to end-of-contents octets 00 00;
     lengths not in the fewest octets, of at most 8 significant octets
     and when one more octet follows them; and any single octet as a
     BOOLEAN. Beyond BER, it also reads encodings that BER forbids as
     well: the initial length octet 0xFF (8.1.3.5 c), its length read
     as above, and tag numbers below 31 in the high form (8.1.2.2) or
     with a first subsequent octet 0x80 (8.1.2.4.2 c). It reads tag
     numbers up to 2^31 - 1. It checks the form only of BOOLEAN,
     INTEGER, ENUMERATED and NULL, so it reads the other universal types
     in either form, though BER allows the constructed form only for
     the string types and the types encoded as strings (8.6, 8.7, 8.23,
     and ObjectDescriptor, UTCTime and GeneralizedTime, 8.25).
   The Go and Rust programs check no ENUMERATED contents. None of the
   oracles refuses universal tag 0. Beyond that, for every element
   an oracle reads (`decode` and `all`), `read` with its rules must give
   its answer, whether or not it agrees with the tool; any element on
   which it does not is a failure.

Inputs come from a recorded seed, after fixed sets:

- the examples of X.690: BOOLEAN TRUE (8.2.2), the lengths 38 and 201
  (8.1.3.4, 8.1.3.5), NULL (8.8.2), and the three encodings of "Jones"
  (8.23.5), of which DER allows the primitive one (10.1, 10.2);
- every input of 0, 1 and 2 octets, read with `decode` and `all`;
- every identifier first octet, with subsequent tag octets when it
  takes them, and short contents;
- every initial length octet 0x80 to 0xFF, with several subsequent
  octets and contents; and lengths of 5 to 126 octets that a reader
  skipping leading zero octets, or keeping the length modulo 2^32 or
  2^64, would fit to the contents after them;
- lengths 0 to 100,000 around 127, 128, 255, 256, 65535 and 65536:
  whole, cut short, with the length one more and one less, not in the
  fewest octets (up to 126 length octets), and inside a SEQUENCE;
- tag numbers around 31, 127, 128, 16383, 16384, 2^21, 2^28, 2^31,
  2^32, 2^63 and 2^64, and one of 1,000 subsequent octets, in each
  class and form, cut short and with a first subsequent octet 0x80;
- every universal tag 0 to 40 in both forms, encoded, read and asked
  `valid`, and the high form for each below 31;
- BOOLEAN and NULL contents, and every INTEGER of 0, 1 and 2 octets
  with some longer ones, read as an element and with `readint`, and
  the same contents read as an ENUMERATED;
- chains nested 10,000 and 100,000 deep: whole, with octets after, with
  mixed classes and tags, with a bad BOOLEAN inside, with one element
  running past the one around it, and cut short; the 10,000 deep ones
  are also encoded. Chains 1,000 deep, one the slice accepts and one
  with a bad BOOLEAN inside, are asked `valid`. Each of these requests
  goes to a `der serve` of its own, which must answer within
  DEEP_BUDGET seconds;
- every signature of the Wycheproof vectors in
  tests/wycheproof/ecdsa_secp256r1_sha256_test.json, whose SHA-256 is
  checked first, read with `all`. The record says how many of those
  flagged BerEncodedSignature, InvalidEncoding and MissingZero the tool
  refuses;
- random trees the slice accepts, of every class, with tags in both
  forms, up to 6 levels and 8 elements in a constructed one, encoded by
  the model and read whole, with octets after, and mutated: an
  element's length one more or one less, not in the fewest octets (in
  the long form below 128, or with 1 to 125 leading zero octets) or
  indefinite, its tag in the high form below 31 or with a first
  subsequent octet 0x80, its constructed bit flipped, its length too
  short for the elements in it, so that the last runs past it, its
  BOOLEAN, INTEGER, ENUMERATED or NULL contents changed; and the whole
  encoding with a bit flipped or cut short.
  Each tree is also encoded, and the model reads the tool's encoding
  back as the tree. Each is asked `valid`, and so is a copy with one
  element the slice does not accept: of a class from 4 to 7, universal
  tag 0, a universal type in the wrong form (never a reserved number,
  which may take either), or BOOLEAN, INTEGER, ENUMERATED or NULL
  contents DER forbids. The model checks that it does not accept that
  copy, which is also encoded;
- random octet strings; `readint` on random contents; `writeint` on
  integers from -300 to 300, around plus and minus 2^k for k up to
  1,000, and random ones of up to 4,096 bits;
- malformed requests, which the tool must answer with `error`, and odd
  but well-formed ones;
- the command-line mode `der decode`, on input that decodes, input that
  does not, malformed hex, and wrong arguments: what each run prints on
  standard output and its exit status.

Every seventh request ends in CR LF.

    python3 tests/run_tests.py [--seed N] [--count N] [--no-oracles]

`--count` is the number of random trees; half as many random octet
strings are read, and a quarter as many random integer contents and
integers. `--no-oracles` leaves every oracle out and compares the tool
with the model alone, as tests/plant_bugs.py does. The script builds the
executable and the oracles first, writes tests/TEST-RESULTS.md, and
exits non-zero if any check fails.
"""

import argparse
import hashlib
import json
import os
import random
import re
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "der"
TESTS = ROOT / "tests"
WYCHEPROOF = TESTS / "wycheproof" / "ecdsa_secp256r1_sha256_test.json"
# https://raw.githubusercontent.com/C2SP/wycheproof/main/testvectors_v1/ecdsa_secp256r1_sha256_test.json
WYCHEPROOF_SHA256 = "182db4f3e230f6f9fa9f800d2a614dede30284b8e8438bbfe1171905402e9332"
ORACLES = TESTS / "oracles"
GO_SRC = ORACLES / "go"
GO_EXE = ROOT / ".lake" / "oracle-go" / "der-oracle"
RUST_SRC = ORACLES / "rust"
RUST_TARGET = ROOT / ".lake" / "oracle-rust"
RUST_EXE = RUST_TARGET / "release" / "der-oracle"
OPENSSL_SRC = ORACLES / "openssl"
OPENSSL_EXE = ROOT / ".lake" / "oracle-openssl" / "openssl-oracle"
OPENSSL_PINNED = "3.0.13"
RESULTS = TESTS / "TEST-RESULTS.md"
TIMEOUT = 3600
BUILD_TIMEOUT = 3600
# A request nested 1,000, 10,000 or 100,000 deep goes to a `der serve`
# of its own, which must answer it within this many seconds.
DEEP_BUDGET = 60
# The other requests are split among this many `der serve` processes.
JOBS = max(1, min(4, os.cpu_count() or 1))

# ---------------------------------------------------------------------
# The model: X.690.
#
# A tree is ("p", class, number, contents) for a primitive element and
# ("c", class, number, [elements]) for a constructed one, the elements
# `der serve` prints. Classes are numbered as Table 1 of X.690 encodes
# them in bits 8 and 7: universal 0, application 1, context-specific 2,
# private 3.

# The universal types X.690 encodes as constructed: 8, external and
# instance-of (8.18.1, 8.16.1); 11, embedded-pdv (8.17.1); 16, sequence
# and sequence-of (8.9.1, 8.10.1); 17, set and set-of (8.11.1, 8.12.1);
# 29, the unrestricted character string (8.24.1).
CONSTRUCTED_UNIVERSAL = {8, 11, 16, 17, 29}


def reserved_universal(n):
    """X.680 Table 1: 15 is "Reserved for future editions", and 37 on
    "Reserved for addenda". This slice reads them in either form."""
    return n == 15 or n >= 37


# Why the model refuses an input. Each is also the name of a rule on
# which an oracle may part from DER (see `Rules`).
WHY_IDENT_ENDS = "the input ends in the identifier octets"
WHY_LENGTH_ENDS = "the input ends in the length octets"
WHY_CONTENTS_END = "the contents run past the end of the input"
WHY_PAST_PARENT = "an element runs past the end of the one it is in"
WHY_HIGH_LOW = "a tag number below 31 in the high form (8.1.2.2)"
WHY_TAG_80 = "a first subsequent tag octet with bits 7 to 1 zero (8.1.2.4.2 c)"
WHY_INDEFINITE = "the indefinite length (10.1)"
WHY_LEN_FF = "the initial length octet 0xFF (8.1.3.5 c)"
WHY_LEN_ZERO = "a long-form length with a leading zero octet (10.1)"
WHY_LEN_SHORT = "a long-form length below 128 (10.1)"
WHY_UNIVERSAL_0 = "universal tag 0 (X.680 Table 1, 8.1.5)"
WHY_CONS_PRIM = "universal 8, 11, 16, 17 or 29 in the primitive form"
WHY_PRIM_CONS = "a primitive universal type in the constructed form"
WHY_BOOL_SIZE = "a BOOLEAN without exactly one contents octet (8.2.1)"
WHY_BOOL_VALUE = "a BOOLEAN contents octet other than 00 and FF (11.1)"
WHY_INT_EMPTY = "an INTEGER with no contents octets (8.3.1)"
WHY_INT_PAD = "an INTEGER with a redundant leading octet (8.3.2)"
WHY_NULL = "a NULL with contents octets (8.8.2)"
WHY_ENUM_EMPTY = "an ENUMERATED with no contents octets (8.4, 8.3.1)"
WHY_ENUM_PAD = "an ENUMERATED with a redundant leading octet (8.4, 8.3.2)"
WHY_AFTER = "octets after the element"
# Reasons only an oracle's rules give.
WHY_HIGH_FORM = "a tag number of 31 or more"
WHY_TAG_LIMIT = "a tag number past the oracle's limit"
WHY_LEN_LIMIT = "a length past the oracle's limit"
WHY_NO_EOC = "no end-of-contents octets before the end"


@dataclass(frozen=True)
class Rules:
    """The rules a reader reads by. The defaults are DER's, as this
    slice reads it."""
    high_form: bool = True             # reads tag numbers of 31 and more
    lenient_tags: bool = False         # reads any high form, even below 31 or from 0x80
    max_tag: int = None                # the largest tag number read
    ber_lengths: bool = False          # OpenSSL's lengths: BER's, and after the octet 0xFF
    max_length: int = None             # the largest length read
    checked_forms: frozenset = None    # universal numbers whose form is checked; None: all
    universal_0: bool = False          # reads universal tag 0
    ber_boolean: bool = False          # reads any single octet as a BOOLEAN (8.2.2)
    null_checked: bool = True          # refuses a NULL with contents
    enum_checked: bool = True          # checks the contents of an ENUMERATED


DER = Rules()


class Refused(Exception):
    def __init__(self, why):
        super().__init__(why)
        self.why = why


def settle(der_why, why, parted):
    """Applies one rule: `der_why` is DER's reason to refuse, or None,
    and `why` that of the rules in use. Where the two part, the reason
    goes in `parted`. Raises Refused when the rules in use refuse."""
    if (der_why is None) != (why is None):
        parted.add(why if why is not None else der_why)
    if why is not None:
        raise Refused(why)


def read_identifier(data, pos, end, inner, rules, parted):
    """8.1.2: the class, whether the element is constructed, the tag
    number, and the position after the identifier octets, which must end
    by `end`."""
    ends = WHY_PAST_PARENT if inner else WHY_IDENT_ENDS
    if pos >= end:
        raise Refused(ends)
    b = data[pos]
    pos += 1
    # Bits 8 and 7, the class (8.1.2.2 a, Table 1); bit 6 one for a
    # constructed encoding (8.1.2.5).
    cls, constructed = b >> 6, bool(b & 0x20)
    if b & 0x1f != 0x1f:
        # 8.1.2.2 c: bits 5 to 1 give a number from 0 to 30.
        return cls, constructed, b & 0x1f, pos
    # 8.1.2.4: bits 5 to 1 all ones, then subsequent octets, each with
    # bit 8 one but the last (8.1.2.4.2 a), whose bits 7 to 1 are the
    # number, most significant first (8.1.2.4.2 b).
    digits = []
    while True:
        if pos >= end:
            raise Refused(ends)
        o = data[pos]
        pos += 1
        digits.append(o & 0x7f)
        if not o & 0x80:
            break
    number = 0
    for d in digits:
        number = number * 128 + d
    if digits[0] == 0:
        der_why = WHY_TAG_80
    elif number < 31:
        der_why = WHY_HIGH_LOW  # 8.1.2.2: 0 to 30 take a single octet
    else:
        der_why = None
    if not rules.high_form:
        why = WHY_HIGH_FORM
    else:
        why = None if rules.lenient_tags else der_why
        if why is None and rules.max_tag is not None and number > rules.max_tag:
            why = WHY_TAG_LIMIT
    settle(der_why, why, parted)
    return cls, constructed, number, pos


def read_length(data, pos, end, inner, constructed, rules, parted):
    """8.1.3 and 10.1: the number of contents octets, or None for the
    indefinite form where the rules read it, and the position after the
    length octets, which must end by `end`."""
    ends = WHY_PAST_PARENT if inner else WHY_LENGTH_ENDS
    if pos >= end:
        raise Refused(ends)
    b = data[pos]
    pos += 1
    if b < 0x80:
        return b, pos  # 8.1.3.4, the short form
    if b == 0x80:
        # 8.1.3.6, the indefinite form, which 10.1 rules out. OpenSSL
        # reads it for a constructed element.
        settle(WHY_INDEFINITE, None if rules.ber_lengths and constructed else WHY_INDEFINITE,
               parted)
        return None, pos
    k = b & 0x7f  # 8.1.3.5 b: the number of subsequent octets
    if not rules.ber_lengths:
        if b == 0xff:
            raise Refused(WHY_LEN_FF)  # 8.1.3.5 c
        if end - pos < k:
            raise Refused(ends)
        octets = data[pos:pos + k]
        n = int.from_bytes(octets, "big")
        # 10.1: "encoded in the minimum number of octets".
        if octets[0] == 0:
            raise Refused(WHY_LEN_ZERO)
        if n < 128:
            raise Refused(WHY_LEN_SHORT)
        if rules.max_length is not None and n > rules.max_length:
            settle(None, WHY_LEN_LIMIT, parted)
        return n, pos + k
    # OpenSSL's asn1_get_length: one more octet must follow the
    # subsequent octets; leading zero octets are skipped; at most 8
    # significant octets, and a value up to 2^63 - 1.
    if end - pos < k + 1:
        raise Refused(ends)
    octets = data[pos:pos + k]
    significant = octets.lstrip(b"\0")
    n = int.from_bytes(significant, "big")
    if len(significant) > 8 or n > 2 ** 63 - 1:
        raise Refused(WHY_LEN_LIMIT)
    der_why = (WHY_LEN_FF if b == 0xff else WHY_LEN_ZERO if octets[0] == 0
               else WHY_LEN_SHORT if n < 128 else None)
    settle(der_why, None, parted)
    return n, pos + k


def check_tag(cls, constructed, number, rules, parted):
    """Universal tag 0 and the form of each universal type: X.680 Table
    1, and the clause of X.690 for each type."""
    if cls != 0:
        return
    if number == 0:
        der_why = WHY_UNIVERSAL_0
    elif constructed and not (number in CONSTRUCTED_UNIVERSAL or reserved_universal(number)):
        der_why = WHY_PRIM_CONS
    elif not constructed and number in CONSTRUCTED_UNIVERSAL:
        der_why = WHY_CONS_PRIM
    else:
        der_why = None
    if number == 0:
        why = None if rules.universal_0 else der_why
    elif rules.checked_forms is None or number in rules.checked_forms:
        why = der_why
    else:
        why = None
    settle(der_why, why, parted)


def check_contents(cls, number, c, rules, parted):
    """The contents of a universal BOOLEAN (8.2.1, 11.1), INTEGER (8.3.1,
    8.3.2), ENUMERATED (8.4: encoded as its integer) and NULL (8.8.2)."""
    if cls != 0 or number not in (1, 2, 5, 10):
        return
    if number == 1:
        der_why = (WHY_BOOL_SIZE if len(c) != 1 else
                   WHY_BOOL_VALUE if c[0] not in (0x00, 0xff) else None)
        why = None if rules.ber_boolean and der_why == WHY_BOOL_VALUE else der_why
    elif number == 2:
        der_why = why = read_int(c)[1]
    elif number == 10:
        der_why = {None: None, WHY_INT_EMPTY: WHY_ENUM_EMPTY,
                   WHY_INT_PAD: WHY_ENUM_PAD}[read_int(c)[1]]
        why = der_why if rules.enum_checked else None
    else:
        der_why = WHY_NULL if c else None
        why = der_why if rules.null_checked else None
    settle(der_why, why, parted)


def read(data, rules=DER):
    """The element at the start of `data`: ((tree, the octets after it),
    None) or (None, why); and the reasons on which `rules` part from DER
    on the way. A constructed element's contents are read element by
    element to the end of its length (8.1.1.1, 8.9.2), or for the
    indefinite form to the end-of-contents octets 00 00 (8.1.5). The
    reader keeps its own stack, so deep nesting takes no recursion."""
    parted = set()
    # The open constructed elements: class, number, the elements read so
    # far, where the contents end (None for the indefinite form), and
    # where the element around it ends.
    stack = []
    pos = 0
    try:
        while True:
            if stack:
                end = stack[-1][3] if stack[-1][3] is not None else stack[-1][4]
            else:
                end = len(data)
            inner = bool(stack)
            cls, constructed, number, pos = read_identifier(data, pos, end, inner, rules, parted)
            length, pos = read_length(data, pos, end, inner, constructed, rules, parted)
            if length is not None and length > end - pos:
                raise Refused(WHY_PAST_PARENT if inner else WHY_CONTENTS_END)
            check_tag(cls, constructed, number, rules, parted)
            node = None
            if constructed:
                stack.append((cls, number, [], None if length is None else pos + length, end))
            else:
                c = data[pos:pos + length]
                check_contents(cls, number, c, rules, parted)
                pos += length
                node = ("p", cls, number, c)
            # Put the element in the one around it, and close each one
            # that ends here.
            while True:
                if node is not None:
                    if not stack:
                        return ((node, data[pos:]), None), parted
                    stack[-1][2].append(node)
                    node = None
                f_cls, f_number, children, stop, outer = stack[-1]
                if stop is None:
                    if outer - pos >= 2 and data[pos] == 0 and data[pos + 1] == 0:
                        pos += 2
                    elif pos >= outer:
                        raise Refused(WHY_NO_EOC)
                    else:
                        break
                elif pos != stop:
                    break
                stack.pop()
                node = ("c", f_cls, f_number, children)
    except Refused as e:
        return (None, e.why), parted


def read_all(data, rules=DER):
    """The element that is the whole input."""
    (r, why), parted = read(data, rules)
    if r is not None and r[1]:
        return (None, WHY_AFTER), parted
    return (r, why), parted


def identifier_octets(cls, constructed, number):
    """8.1.2: one octet for a number up to 30; else the leading octet
    with bits 5 to 1 all ones, then the number in base 128, most
    significant first, bit 8 one in every octet but the last. X.690
    has four classes; a class number of 4 or more is written as
    `Spec.der` writes it, the class times 64 taken as an octet, which is
    the class modulo 4. No such tree is valid."""
    lead = (cls % 4) << 6 | (0x20 if constructed else 0)
    if number <= 30:
        return bytes([lead | number])
    digits = []
    while number:
        digits.append(number % 128)
        number //= 128
    digits.reverse()
    return bytes([lead | 0x1f] + [d | 0x80 for d in digits[:-1]] + [digits[-1]])


def length_octets(n):
    """8.1.3 and 10.1: the short form up to 127, else the long form in
    the fewest octets."""
    if n <= 127:
        return bytes([n])
    octets = n.to_bytes((n.bit_length() + 7) // 8, "big")
    if len(octets) > 126:
        raise ValueError("a length past the long form")
    return bytes([0x80 | len(octets)]) + octets


def encode(tree):
    """8.1.1: the identifier, length and contents octets; the contents of
    a constructed element are the encodings of its elements. Two passes
    over a stack of its own: the size of each element's contents, then
    the octets."""
    size = {}
    stack = [(tree, False)]
    while stack:
        t, done = stack.pop()
        if t[0] == "p":
            size[id(t)] = len(t[3])
        elif done:
            size[id(t)] = sum(len(identifier_octets(c[1], c[0] == "c", c[2]))
                              + len(length_octets(size[id(c)])) + size[id(c)] for c in t[3])
        else:
            stack.append((t, True))
            stack.extend((c, False) for c in t[3])
    out = bytearray()
    stack = [tree]
    while stack:
        t = stack.pop()
        out += identifier_octets(t[1], t[0] == "c", t[2]) + length_octets(size[id(t)])
        if t[0] == "p":
            out += t[3]
        else:
            stack.extend(reversed(t[3]))
    return bytes(out)


def valid(tree):
    """Whether this slice accepts a tree (`Spec.Valid`): every element
    of a class from 0 to 3, its universal tag and contents as `read`
    checks them, and every length within the long form, which `encode`
    checks."""
    for t in nodes(tree):
        if t[1] > 3:
            return False
        if t[1] == 0:
            try:
                check_tag(0, t[0] == "c", t[2], DER, set())
                if t[0] == "p":
                    check_contents(0, t[2], t[3], DER, set())
            except Refused:
                return False
    try:
        encode(tree)
    except ValueError:
        return False
    return True


def read_int(c):
    """8.3: the integer contents octets encode, (value, None), or (None,
    why). One or more octets (8.3.1), not starting with nine bits all
    ones or all zero (8.3.2); the value as the note to 8.3.3 sums it:
    every bit but bit 8 of the first octet, less that one's value when it
    is set."""
    if not c:
        return None, WHY_INT_EMPTY
    if len(c) > 1 and ((c[0] == 0xff and c[1] & 0x80) or (c[0] == 0x00 and not c[1] & 0x80)):
        return None, WHY_INT_PAD
    value = int.from_bytes(c, "big")
    if c[0] & 0x80:
        value -= 2 ** (8 * len(c))
    return value, None


def write_int(z):
    """The contents octets of z: the two's complement number of 8.3.3, in
    the fewest octets, which 8.3.2 requires."""
    n = max(1, abs(z).bit_length() // 8)
    while not -2 ** (8 * n - 1) <= z < 2 ** (8 * n - 1):
        n += 1
    return (z % 2 ** (8 * n)).to_bytes(n, "big")


def hx(data):
    return bytes(data).hex() or "-"


def show(tree):
    """A tree as `der serve` prints it, built with a stack of its own."""
    out, stack = [], [tree]
    while stack:
        t = stack.pop()
        if isinstance(t, str):
            out.append(t)
        elif t[0] == "p":
            out.append(f"p{t[1]}.{t[2]}.{hx(t[3])}")
        else:
            out.append(f"c{t[1]}.{t[2]}(")
            stack.append(")")
            for i, c in enumerate(reversed(t[3])):
                if i:
                    stack.append(",")
                stack.append(c)
    return "".join(out)


# ---------------------------------------------------------------------
# Requests and answers, in the form of `der serve`.

def request(op, args):
    if op in ("encode", "valid"):
        return f"{op} {show(args[0])}"
    if op == "writeint":
        return f"writeint {args[0]}"
    return f"{op} {hx(args[0])}"


def model(op, args, rules=DER):
    """The answer to a request as `der serve` writes it, why the model
    refuses or None, and the rules on which `rules` part from DER on the
    way."""
    if op in ("decode", "all"):
        (r, why), parted = (read if op == "decode" else read_all)(args[0], rules)
        if r is None:
            return "FAIL", why, parted
        if op == "decode":
            return f"OK {show(r[0])} {hx(r[1])}", None, parted
        return f"OK {show(r[0])}", None, parted
    if op == "encode":
        return f"OK {hx(encode(args[0]))}", None, set()
    if op == "valid":
        return ("OK" if valid(args[0]) else "FAIL"), None, set()
    if op == "readint":
        z, why = read_int(args[0])
        return ("FAIL" if z is None else f"OK {z}"), why, set()
    return f"OK {hx(write_int(args[0]))}", None, set()


def octets_field(f):
    """A field of octets: `-`, or lower-case hex digits in pairs."""
    if f == "-":
        return b""
    if f == "" or len(f) % 2 or any(c not in "0123456789abcdef" for c in f):
        raise ValueError
    return bytes.fromhex(f)


def decimal_field(f):
    if f == "" or any(c not in "0123456789" for c in f):
        raise ValueError
    return int(f)


def integer_field(f):
    """A decimal integer, with `-` in front when it is negative."""
    return -decimal_field(f[1:]) if f.startswith("-") else decimal_field(f)


def tree_field(f):
    """The tree a field writes, in the syntax Main.lean's header gives,
    or ValueError. It keeps a stack of its own."""
    pos = 0

    def number():
        nonlocal pos
        start = pos
        while pos < len(f) and f[pos] in "0123456789":
            pos += 1
        if pos == start:
            raise ValueError
        return int(f[start:pos])

    def expect(ch):
        nonlocal pos
        if pos >= len(f) or f[pos] != ch:
            raise ValueError
        pos += 1

    stack = []
    while True:
        if pos >= len(f) or f[pos] not in "pc":
            raise ValueError
        kind = f[pos]
        pos += 1
        cls = number()
        expect(".")
        num = number()
        if kind == "p":
            expect(".")
            start = pos
            while pos < len(f) and f[pos] not in ",)":
                pos += 1
            node = ("p", cls, num, octets_field(f[start:pos]))
        else:
            expect("(")
            if pos < len(f) and f[pos] == ")":
                pos += 1
                node = ("c", cls, num, [])
            else:
                stack.append(("c", cls, num, []))
                continue
        while True:
            if not stack:
                if pos != len(f):
                    raise ValueError
                return node
            stack[-1][3].append(node)
            if pos < len(f) and f[pos] == ",":
                pos += 1
                break
            expect(")")
            node = stack.pop()


def model_line(raw):
    """The answer to a request line, as sent with its line ending, as
    Main.lean's header describes the protocol: the line ends in LF or
    CR LF; `error` for a malformed request, else the model's answer."""
    line = raw
    if line.endswith("\n"):
        line = line[:-1]
        if line.endswith("\r"):
            line = line[:-1]
    parts = line.split(" ")
    if len(parts) != 2:
        return "error"
    op, f = parts
    read_field = {"decode": octets_field, "all": octets_field, "readint": octets_field,
                  "writeint": integer_field, "encode": tree_field,
                  "valid": tree_field}.get(op)
    if read_field is None:
        return "error"
    try:
        arg = read_field(f)
    except ValueError:
        return "error"
    return model(op, (arg,))[0]


# ---------------------------------------------------------------------
# Running a program over request lines.

def run_lines(cmd, lines, timeout=TIMEOUT, cwd=None, env=None):
    """Send `lines` to `cmd` and return its answer lines and a note on
    how the run failed, or None."""
    raw = "".join(lines).encode("utf-8")
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, cwd=cwd, env=env)
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf):
        while chunk := stream.read1(1 << 16):
            buf += chunk

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out)),
               threading.Thread(target=drain, args=(proc.stderr, err))]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    return answers, problem


def run_parallel(cmd, lines, jobs):
    """`run_lines` over `jobs` processes, each given a run of the lines
    in order; the answers in order, and the problems."""
    size = -(-len(lines) // jobs) if lines else 0
    chunks = [lines[k:k + size] for k in range(0, len(lines), size)] if size else [[]]
    results = [None] * len(chunks)

    def one(k):
        results[k] = run_lines(cmd, chunks[k])

    threads = [threading.Thread(target=one, args=(k,)) for k in range(len(chunks))]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    answers, problems = [], []
    for chunk, (got, problem) in zip(chunks, results):
        if problem:
            problems.append(problem)
        if len(got) != len(chunk):
            problems.append(f"{len(got)} answers for {len(chunk)} requests")
            got = (got + [""] * len(chunk))[:len(chunk)]
        answers += got
    return answers, problems


# ---------------------------------------------------------------------
# The oracles. Each setup returns a list of objects with `name`,
# `version` and `answers(lines)`, or raises OracleUnavailable.

class OracleUnavailable(Exception):
    pass


class ProcessOracle:
    def __init__(self, name, version, cmd):
        self.name, self.version, self.cmd = name, version, cmd

    def answers(self, lines):
        got, problem = run_lines(self.cmd, lines)
        if problem or len(got) != len(lines):
            raise RuntimeError(f"{self.name} oracle: "
                               f"{problem or f'{len(got)} answers for {len(lines)} requests'}")
        return got


def first_line(cmd, cwd=None):
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=300, cwd=cwd)
        return (out.stdout or out.stderr).strip().splitlines()[0]
    except (OSError, subprocess.SubprocessError, IndexError):
        return "unknown"


def setup_go():
    """Both Go oracles: one program, two modes, built by the installed Go.
    cryptobyte is at the version go.mod pins; encoding/asn1 is that Go's
    own, not pinned, and its version is recorded."""
    GO_EXE.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, GOFLAGS="-mod=readonly", CGO_ENABLED="0", GOTOOLCHAIN="local")
    try:
        subprocess.run(["go", "build", "-o", str(GO_EXE), "."], cwd=GO_SRC, check=True, env=env,
                       capture_output=True, timeout=BUILD_TIMEOUT)
    except (OSError, subprocess.SubprocessError) as e:
        raise OracleUnavailable(f"`go build` did not build it: {e}")
    mod = re.search(r"^require golang.org/x/crypto (\S+)",
                    (GO_SRC / "go.mod").read_text(encoding="utf-8"), re.M)
    sums = re.search(r"^golang.org/x/crypto \S+ (h1:\S+)",
                     (GO_SRC / "go.sum").read_text(encoding="utf-8"), re.M)
    go = first_line(["go", "version"])
    return [ProcessOracle("Go cryptobyte", f"golang.org/x/crypto/cryptobyte "
                          f"{mod.group(1) if mod else '?'} ({sums.group(1) if sums else '?'}), "
                          f"built with {go}", [str(GO_EXE), "cryptobyte"]),
            ProcessOracle("Go encoding/asn1", f"encoding/asn1 of the standard library of the "
                          f"installed {go} (not pinned)",
                          [str(GO_EXE), "asn1"])]


def setup_rust():
    RUST_TARGET.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, CARGO_TARGET_DIR=str(RUST_TARGET))
    try:
        subprocess.run(["cargo", "build", "--release", "--locked", "--quiet"], cwd=RUST_SRC,
                       check=True, env=env, capture_output=True, timeout=BUILD_TIMEOUT)
    except (OSError, subprocess.SubprocessError) as e:
        raise OracleUnavailable(f"`cargo build --locked` did not build it: {e}")
    lock = (RUST_SRC / "Cargo.lock").read_text(encoding="utf-8")
    m = re.search(r'name = "asn1"\nversion = "(\S+)"\nsource = "[^"]*"\nchecksum = "([0-9a-f]+)"',
                  lock)
    if not m:
        raise OracleUnavailable("tests/oracles/rust/Cargo.lock pins no asn1 crate")
    return [ProcessOracle("rust-asn1", f"the asn1 crate {m.group(1)} (checksum {m.group(2)}), "
                          f"built with {first_line(['rustc', '--version'])}", [str(RUST_EXE)])]


def setup_openssl():
    OPENSSL_EXE.parent.mkdir(parents=True, exist_ok=True)
    try:
        subprocess.run(["cc", "-O2", "-o", str(OPENSSL_EXE), str(OPENSSL_SRC / "wrapper.c"),
                        "-lcrypto"], check=True, capture_output=True, timeout=BUILD_TIMEOUT)
    except (OSError, subprocess.SubprocessError) as e:
        raise OracleUnavailable(f"`cc` did not build the wrapper against libcrypto (is "
                                f"libssl-dev installed?): {e}")
    got, problem = run_lines([str(OPENSSL_EXE)], ["version\n"], timeout=60)
    version = got[0][3:] if got and got[0].startswith("OK ") and not problem else "unknown"
    if version.split(" ")[:2] != ["OpenSSL", OPENSSL_PINNED]:
        raise OracleUnavailable(f"{version} is installed, not OpenSSL {OPENSSL_PINNED}")
    package = first_line(["dpkg-query", "-W", "-f", "${Package} ${Version}\n", "libssl3t64"])
    return [ProcessOracle("OpenSSL", f"libcrypto of {version}"
                          + (f" (Debian package {package})" if package != "unknown" else "")
                          + f", through `tests/oracles/openssl/wrapper.c` compiled with "
                          f"{first_line(['cc', '--version'])}", [str(OPENSSL_EXE)])]


ORACLE_SETUPS = [(("Go cryptobyte", "Go encoding/asn1"), setup_go), (("rust-asn1",), setup_rust),
                 (("OpenSSL",), setup_openssl)]

# The rules each oracle reads by (see the top of this file).
ORACLE_RULES = {
    "Go cryptobyte": Rules(high_form=False, max_length=2 ** 32 - 1,
                           checked_forms=frozenset({1, 2}), universal_0=True, null_checked=False,
                           enum_checked=False),
    "Go encoding/asn1": Rules(max_tag=2 ** 31 - 1, max_length=2 ** 31 - 1,
                              checked_forms=frozenset({1, 2, 5}), universal_0=True, enum_checked=False),
    "rust-asn1": Rules(max_tag=2 ** 32 - 1, max_length=2 ** 32 - 1,
                       checked_forms=frozenset({1, 2, 5}), universal_0=True, enum_checked=False),
    "OpenSSL": Rules(lenient_tags=True, max_tag=2 ** 31 - 1, ber_lengths=True,
                     checked_forms=frozenset({1, 2, 5, 10}), universal_0=True, ber_boolean=True),
}

# The Go and Rust oracle programs check no ENUMERATED contents.
ENUM_NOT_CHECKED = "the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED "

# What each oracle does on each rule where it parts from DER.
PARTS = {
    "Go cryptobyte": {
        WHY_HIGH_FORM: "ReadAnyASN1Element refuses every tag number of 31 or more (the high form)",
        WHY_LEN_LIMIT: "readASN1 refuses a length of more than 4 octets",
        WHY_UNIVERSAL_0: "ReadAnyASN1Element reads universal tag 0",
        WHY_CONS_PRIM: "ReadAnyASN1Element reads universal 8, 11, 16, 17 or 29 in the primitive "
                       "form",
        WHY_PRIM_CONS: "ReadAnyASN1Element reads a universal type other than BOOLEAN and INTEGER "
                       "in the constructed form",
        WHY_NULL: "cryptobyte has no reader for NULL, so a NULL with contents is read",
        WHY_ENUM_EMPTY: ENUM_NOT_CHECKED + "with no contents octets",
        WHY_ENUM_PAD: ENUM_NOT_CHECKED + "with a redundant leading octet",
    },
    "Go encoding/asn1": {
        WHY_TAG_LIMIT: "parseBase128Int refuses a tag number above 2^31 - 1",
        WHY_LEN_LIMIT: "parseTagAndLength refuses a length above 2^31 - 1",
        WHY_UNIVERSAL_0: "Unmarshal into a RawValue reads universal tag 0",
        WHY_CONS_PRIM: "Unmarshal into a RawValue reads universal 8, 11, 16, 17 or 29 in the "
                       "primitive form",
        WHY_PRIM_CONS: "Unmarshal into a RawValue reads a universal type other than BOOLEAN, "
                       "INTEGER and NULL in the constructed form",
        WHY_ENUM_EMPTY: ENUM_NOT_CHECKED + "with no contents octets",
        WHY_ENUM_PAD: ENUM_NOT_CHECKED + "with a redundant leading octet",
    },
    "rust-asn1": {
        WHY_TAG_LIMIT: "Tag::from_bytes refuses a tag number above 2^32 - 1",
        WHY_LEN_LIMIT: "read_length refuses a length of more than 4 octets",
        WHY_UNIVERSAL_0: "strip_tlv reads universal tag 0",
        WHY_CONS_PRIM: "strip_tlv reads universal 8, 11, 16, 17 or 29 in the primitive form",
        WHY_PRIM_CONS: "strip_tlv reads a universal type other than BOOLEAN, INTEGER and NULL in "
                       "the constructed form",
        WHY_ENUM_EMPTY: ENUM_NOT_CHECKED + "with no contents octets",
        WHY_ENUM_PAD: ENUM_NOT_CHECKED + "with a redundant leading octet",
    },
    "OpenSSL": {
        WHY_HIGH_LOW: "ASN1_get_object reads a tag number below 31 in the high form, which BER "
                      "forbids as well (8.1.2.2)",
        WHY_TAG_80: "ASN1_get_object reads a first subsequent tag octet 0x80, which BER forbids "
                    "as well (8.1.2.4.2 c)",
        WHY_TAG_LIMIT: "ASN1_get_object refuses a tag number above 2^31 - 1",
        WHY_INDEFINITE: "ASN1_get_object reads the indefinite length of a constructed element "
                        "(BER), to end-of-contents octets 00 00",
        WHY_LEN_FF: "asn1_get_length reads the initial length octet 0xFF, which BER forbids as "
                    "well (8.1.3.5 c), skipping leading zero octets",
        WHY_LEN_ZERO: "asn1_get_length reads a long-form length with leading zero octets (BER)",
        WHY_LEN_SHORT: "asn1_get_length reads the long form for a length below 128 (BER)",
        WHY_UNIVERSAL_0: "ASN1_get_object reads universal tag 0 where no end-of-contents octets "
                         "are due",
        WHY_CONS_PRIM: "ASN1_get_object reads universal 8, 11, 16, 17 or 29 in the primitive form",
        WHY_PRIM_CONS: "ASN1_get_object reads a universal type other than BOOLEAN, INTEGER, "
                       "ENUMERATED and NULL in the constructed form, which BER allows only for "
                       "the string types and the types encoded as strings (8.6, 8.7, 8.23, and "
                       "ObjectDescriptor, UTCTime and GeneralizedTime, 8.25)",
        WHY_BOOL_VALUE: "d2i_ASN1_TYPE reads any single contents octet as a BOOLEAN (BER, 8.2.2)",
    },
}


def difference_reason(oracle, op, theirs, theirs_by_model, parted):
    """The named reason the oracle's answer differs from the tool's,
    confirmed by the model, or None. `theirs_by_model` is the answer of
    `read` with the rules the oracle reads by, and `parted` the rules on
    which those part from DER on the way. It must be the oracle's answer,
    and the reason names each rule in `parted`."""
    if op not in ("decode", "all") or theirs_by_model != theirs or not parted:
        return None
    return "; ".join(PARTS[oracle].get(p, f"{p} (no description)") for p in sorted(parted))


# ---------------------------------------------------------------------
# The fixed sets.

def x690_examples():
    """X.690's own examples: (op, args, the answer the standard gives)."""
    l38, l201, jones = bytes(range(38)), bytes(range(201)), b"Jones"
    return [
        # 8.2.2 and 11.1: TRUE, 01 01 FF.
        ("decode", (bytes.fromhex("0101ff"),), "OK p0.1.ff -"),
        ("all", (bytes.fromhex("0101ff"),), "OK p0.1.ff"),
        ("encode", (("p", 0, 1, b"\xff"),), "OK 0101ff"),
        # 8.1.3.4: L = 38 in the short form, 00100110.
        ("encode", (("p", 0, 4, l38),), "OK 0426" + l38.hex()),
        ("all", (b"\x04\x26" + l38,), f"OK p0.4.{l38.hex()}"),
        # 8.1.3.5: L = 201 in the long form, 10000001 11001001.
        ("encode", (("p", 0, 4, l201),), "OK 0481c9" + l201.hex()),
        ("all", (b"\x04\x81\xc9" + l201,), f"OK p0.4.{l201.hex()}"),
        # 8.8.2: NULL, 05 00.
        ("all", (bytes.fromhex("0500"),), "OK p0.5.-"),
        ("encode", (("p", 0, 5, b""),), "OK 0500"),
        # 8.23.5: "Jones" as a VisibleString, in the primitive form, which
        # DER uses.
        ("decode", (bytes.fromhex("1a054a6f6e6573"),), "OK p0.26.4a6f6e6573 -"),
        ("encode", (("p", 0, 26, jones),), "OK 1a054a6f6e6573"),
        # 8.23.5: the constructed forms, definite and indefinite, which DER
        # rules out (10.2, 10.1).
        ("decode", (bytes.fromhex("3a0904034a6f6e04026573"),), "FAIL"),
        ("decode", (bytes.fromhex("3a8004034a6f6e040265730000"),), "FAIL"),
        # 8.1.5: the end-of-contents octets go with the indefinite form
        # only, so they are no element in DER.
        ("decode", (bytes.fromhex("0000"),), "FAIL"),
    ]


def short_sets():
    """Every input of 0, 1 and 2 octets."""
    label = "0 to 2 octets"
    for op in ("decode", "all"):
        yield (label, op, (b"",))
        for a in range(256):
            yield (label, op, (bytes([a]),))
            for b in range(256):
                yield (label, op, (bytes([a, b]),))


def identifier_sets():
    """Every identifier first octet with short contents; after a first
    octet with bits 5 to 1 all ones, a few runs of subsequent octets."""
    bodies = [b"", b"\x00", b"\xff", b"\x01", b"\x05\x00", b"\x02\x01\x00",
              b"\x01\x01\xff\x05\x00", b"\x00\x00"]
    for b in range(256):
        tails = [b""] if b & 0x1f != 0x1f else [b"\x1e", b"\x1f", b"\x7f", b"\x80\x1f",
                                                 b"\x81\x00", b"\xff\x7f", b"\x81"]
        for t in tails:
            for body in bodies:
                yield ("identifier first octets", "decode",
                       (bytes([b]) + t + length_octets(len(body)) + body,))


def length_sets():
    """Every initial length octet from 0x80 to 0xFF, after the
    identifiers of an OCTET STRING and a SEQUENCE, with several runs of
    subsequent octets: all zero, ending in 01, starting with 01, all
    ones, and one octet short. Contents follow when the length is at
    most 300; else three octets. Then lengths of 5 to 126 octets that a
    reader would fit to the contents after them if it skipped leading
    zero octets or kept the length modulo 2^32 or 2^64."""
    for b in range(0x80, 0x100):
        k = b & 0x7f
        if k == 0:
            runs = [b""]
        else:
            runs = [bytes(k), bytes(k - 1) + b"\x01", b"\x01" + bytes(k - 1), b"\xff" * k,
                    bytes(k - 1)]
        for run in runs:
            n = int.from_bytes(run, "big") if len(run) == k else 0
            for ident in (b"\x04", b"\x30"):
                if b == 0x80:
                    for body in (b"", b"\x00\x00", b"\x05\x00\x00\x00", b"\x05\x00"):
                        yield ("initial length octets", "decode", (ident + bytes([b]) + body,))
                    continue
                body = (b"\x05\x00" * 150)[:n] if n <= 300 else b"\x05\x00\x01"
                yield ("initial length octets", "decode", (ident + bytes([b]) + run + body,))
                yield ("initial length octets", "decode",
                       (ident + bytes([b]) + run + body + b"\x01",))
    # Long-form lengths of 5 to 126 octets that a wrong reader would take
    # for a length the contents fit: 128 and 256 with leading zero octets,
    # and 2^(8(k - 1)) + 128, which is 128 modulo 2^32 from 5 octets on
    # and modulo 2^64 from 9 on. Each is followed by as many contents
    # octets as the wrong reading gives.
    label = "lengths of 5 to 126 octets that a wrong reading fits"
    for k in range(5, 127):
        for run, fit in ((bytes(k - 1) + b"\x80", 128), (bytes(k - 2) + b"\x01\x00", 256),
                         (b"\x01" + bytes(k - 2) + b"\x80", 128)):
            for ident in (b"\x04", b"\x30"):
                e = ident + bytes([0x80 | k]) + run + (b"\x05\x00" * 128)[:fit]
                yield (label, "all", (e,))
                yield (label, "decode", (e + b"\x01",))


def size_sets():
    """Contents of 0 to 100,000 octets, at the lengths where the length
    octets change: whole, with an octet after, cut short, with the
    length one more and one less, not in the fewest octets (in the long
    form below 128, and with leading zero octets: in one subsequent
    length octet more than it needs, and in 5, 9 and 126), and inside a
    SEQUENCE."""
    rng = random.Random(3)
    label = "lengths 0 to 100,000"
    for n in (0, 1, 2, 126, 127, 128, 129, 254, 255, 256, 257, 65535, 65536, 65537, 100000):
        c = rng.randbytes(n)
        e = b"\x04" + length_octets(n) + c
        yield (label, "all", (e,))
        yield (label, "decode", (e + b"\x01",))
        if n:
            yield (label + ", cut short", "all", (e[:-1],))
            yield (label + ", length one less", "decode", (b"\x04" + length_octets(n - 1) + c,))
        yield (label + ", length one more", "decode", (b"\x04" + length_octets(n + 1) + c,))
        minimal = n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")
        for total in sorted({len(minimal) + 1, 5, 9, 126}):
            yield (label + ", not in the fewest octets", "all",
                   (b"\x04" + bytes([0x80 + total]) + bytes(total - len(minimal)) + minimal + c,))
        if n < 128:
            yield (label + ", not in the fewest octets", "all", (b"\x04\x81" + bytes([n]) + c,))
        yield (label, "encode", (("p", 0, 4, c),))
        yield (label, "all", (b"\x30" + length_octets(len(e)) + e,))
        yield (label, "encode", (("c", 0, 16, [("p", 0, 4, c), ("p", 0, 5, b"")]),))


def high_tag_sets():
    """Tag numbers around each of 31, 127, 128, 16383, 16384, 2^21,
    2^28, 2^31, 2^32, 2^63 and 2^64, and one of 1,000 subsequent octets,
    in each class and form: read, encoded, cut in the identifier octets,
    and with a first subsequent octet 0x80 put in."""
    rng = random.Random(4)
    tags = set()
    for t in (31, 127, 128, 16383, 16384, 2 ** 21, 2 ** 28, 2 ** 31, 2 ** 32, 2 ** 63, 2 ** 64):
        tags.update((t - 1, t, t + 1))
    tags.add(rng.randrange(128 ** 999, 128 ** 1000))
    label = "high tag numbers"
    for number in sorted(tags):
        for cls in range(4):
            for constructed in (False, True):
                tree = (("c", cls, number, [("p", 0, 5, b"")]) if constructed
                        else ("p", cls, number, b"\x01\x02"))
                enc = encode(tree)
                ident = identifier_octets(cls, constructed, number)
                yield (label, "all", (enc,))
                yield (label, "decode", (enc + b"\x00",))
                yield (label, "encode", (tree,))
                if number >= 31:
                    yield (label + ", cut short", "decode", (ident[:-1],))
                    yield (label + ", first subsequent octet 0x80", "all",
                           (ident[:1] + b"\x80" + enc[1:],))


def universal_sets():
    """Every universal tag from 0 to 40 in both forms, with a few
    contents, read and encoded; and the high form for those below 31."""
    label = "universal tags 0 to 40"
    contents = [b"", b"\x00", b"\xff", b"\x01", b"\x00\x80", b"\x80", b"\x05\x00"]
    elements = [[], [("p", 0, 5, b"")], [("p", 0, 2, b"\x01"), ("p", 0, 1, b"\xff")]]
    for number in range(41):
        trees = [("p", 0, number, c) for c in contents] + [("c", 0, number, e) for e in elements]
        for tree in trees:
            yield (label, "decode", (encode(tree),))
            yield (label, "encode", (tree,))
            yield (label, "valid", (tree,))
        if number < 31:
            for lead in (0x1f, 0x3f):
                yield (label + ", high form", "all", (bytes([lead, number, 0]),))


def contents_sets():
    """BOOLEAN and NULL contents; every INTEGER of 0, 1 and 2 octets and
    some longer, as elements and with `readint`."""
    for c in ([b""] + [bytes([x]) for x in range(256)]
              + [b"\x00\x00", b"\xff\xff", b"\xff\x00", b"\x00\xff", b"\x01\x01"]):
        yield ("BOOLEAN contents", "decode", (b"\x01" + length_octets(len(c)) + c,))
    for c in (b"", b"\x00", b"\x05", b"\x00\x00", bytes(200)):
        yield ("NULL contents", "decode", (b"\x05" + length_octets(len(c)) + c,))
    for e in ("2103010100", "2500", "25020500", "2203020100"):
        yield ("constructed BOOLEAN, INTEGER and NULL", "decode", (bytes.fromhex(e),))
    ints = [b""] + [bytes([x]) for x in range(256)]
    ints += [bytes([x, y]) for x in range(256) for y in range(256)]
    for k in (3, 8, 9, 16, 17, 32, 33, 100, 129):
        for first in (0x00, 0x01, 0x7f, 0x80, 0xff):
            for second in (0x00, 0x7f, 0x80, 0xff):
                ints.append(bytes([first, second]) + bytes(k - 2))
                ints.append(bytes([first, second]) + b"\xff" * (k - 2))
    for c in ints:
        yield ("INTEGER contents", "decode", (b"\x02" + length_octets(len(c)) + c,))
        yield ("INTEGER contents", "readint", (c,))
        yield ("ENUMERATED contents", "decode", (b"\x0a" + length_octets(len(c)) + c,))


def chain(depth, leaf, heads):
    """A chain of `depth` constructed elements around `leaf`, whose
    classes and numbers go round `heads`, from the inside out."""
    t = leaf
    for i in range(depth):
        cls, number = heads[i % len(heads)]
        t = ("c", cls, number, [t])
    return t


def chain_octets(depth, leaf, ident, longer_at=None):
    """The encoding of a chain of `depth` constructed elements with
    identifier octets `ident` around the octets `leaf`, where the one at
    `longer_at` from the inside claims one octet more than it holds."""
    size, heads = len(leaf), []
    for i in range(depth):
        h = ident + length_octets(size + (1 if i == longer_at else 0))
        heads.append(h)
        size += len(h)
    heads.reverse()
    return b"".join(heads) + leaf


def deep_sets():
    """Chains 1,000, 10,000 and 100,000 deep."""
    mixed = ((0, 16), (2, 0), (0, 17), (1, 31), (3, 1000), (0, 8))
    # Only chains 1,000 deep are asked `valid`: its time grows about with
    # the cube of the depth.
    label = "nested 1,000 deep"
    yield (label, "valid", (chain(1000, ("p", 2, 3, b"\x01"), mixed),))
    yield (label, "valid", (chain(1000, ("p", 0, 1, b"\x01"), ((0, 16),)),))
    for d in (10_000, 100_000):
        label = f"nested {d:,} deep"
        null = chain(d, ("p", 0, 5, b""), ((0, 16),))
        enc = encode(null)
        yield (label, "all", (enc,))
        yield (label, "decode", (enc + b"\x01\x01\xff",))
        yield (label, "all", (enc[:-1],))
        many = chain(d, ("p", 2, 3, b"\x01"), mixed)
        yield (label, "all", (encode(many),))
        yield (label, "all", (chain_octets(d, b"\x01\x01\x01", b"\x30"),))
        yield (label, "all", (chain_octets(d, b"\x05\x00", b"\x30", longer_at=d // 2),))
        # Only the 10,000 deep chains are encoded: `encode` takes time
        # that grows with the square of the depth.
        if d == 10_000:
            yield (label, "encode", (null,))
            yield (label, "encode", (many,))


def read_wycheproof():
    """The Wycheproof test vectors, after their SHA-256 is checked: each
    test's signature octets and flags."""
    raw = WYCHEPROOF.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != WYCHEPROOF_SHA256:
        raise ValueError(f"{WYCHEPROOF.name} has SHA-256 {digest}, not {WYCHEPROOF_SHA256}")
    doc = json.loads(raw)
    vectors = [(bytes.fromhex(t["sig"]), tuple(t["flags"]))
               for g in doc["testGroups"] for t in g["tests"]]
    if len(vectors) != doc["numberOfTests"]:
        raise ValueError(f"{len(vectors)} tests read, not {doc['numberOfTests']}")
    return vectors


# Wycheproof flags that mark an encoding that is not DER, or broken.
ENCODING_FLAGS = ("BerEncodedSignature", "InvalidEncoding", "MissingZero")


# ---------------------------------------------------------------------
# The random part.

PRIMITIVE_UNIVERSAL = [n for n in range(1, 37) if n not in CONSTRUCTED_UNIVERSAL]


def random_number(rng):
    """A tag number: mostly below 31, then in the high form of one,
    two, three and more subsequent octets."""
    r = rng.random()
    if r < 0.55:
        return rng.randrange(31)
    if r < 0.8:
        return rng.randrange(31, 128)
    if r < 0.93:
        return rng.randrange(128, 2 ** 14)
    return rng.randrange(2 ** 14, 2 ** rng.choice((21, 28, 32, 40, 64)))


def random_int(rng):
    r = rng.random()
    if r < 0.3:
        return rng.randint(-300, 300)
    if r < 0.6:
        return rng.choice((-1, 1)) * 2 ** rng.randrange(80) + rng.randint(-2, 2)
    return rng.choice((-1, 1)) * rng.getrandbits(rng.choice((8, 16, 64, 128, 300)))


def random_contents(rng):
    r = rng.random()
    n = rng.randint(0, 4) if r < 0.4 else rng.randint(5, 40) if r < 0.85 else rng.randint(41, 300)
    return rng.randbytes(n)


def random_tree(rng, depth, budget):
    """A random tree this slice accepts, with at most `depth` levels
    below it; budget[0] is how many more elements it may hold."""
    budget[0] -= 1
    cls = rng.choice((0, 0, 0, 1, 2, 3))
    constructed = depth > 0 and budget[0] > 0 and rng.random() < 0.45
    if cls == 0 and constructed:
        number = rng.choice((16, 16, 16, 17, 17, 8, 11, 29, 15, 37, rng.randrange(37, 2 ** 20)))
    elif cls == 0:
        number = rng.choice((1, 1, 2, 2, 2, 5, 5, 15, 37, rng.randrange(37, 2 ** 20))
                            + tuple(PRIMITIVE_UNIVERSAL))
    else:
        number = random_number(rng)
    if constructed:
        k = rng.choice((0, 1, 1, 2, 2, 3, 4, 5, 8))
        return ("c", cls, number, [random_tree(rng, depth - 1, budget) for _ in range(k)])
    if cls == 0 and number == 1:
        c = bytes([rng.choice((0x00, 0xff))])
    elif cls == 0 and number in (2, 10):
        c = write_int(random_int(rng))
    elif cls == 0 and number == 5:
        c = b""
    else:
        c = random_contents(rng)
    return ("p", cls, number, c)


def nodes(tree):
    """The elements of a tree in the order they are written."""
    out, stack = [], [tree]
    while stack:
        t = stack.pop()
        out.append(t)
        if t[0] == "c":
            stack.extend(reversed(t[3]))
    return out


DEFECTS = ["length one more", "length one less", "length not in the fewest octets",
           "indefinite length", "high form for a tag below 31", "first subsequent tag octet 0x80",
           "constructed bit flipped", "an element running past the one it is in",
           "BOOLEAN, INTEGER, ENUMERATED or NULL contents changed"]


def applies(defect, t):
    cons = t[0] == "c"
    if defect == "length one less":
        return len(encode(t)) > len(identifier_octets(t[1], cons, t[2])) + 1
    if defect == "high form for a tag below 31":
        return t[2] < 31
    if defect == "an element running past the one it is in":
        return cons and bool(t[3])
    if defect == "BOOLEAN, INTEGER, ENUMERATED or NULL contents changed":
        return t[0] == "p" and t[1] == 0 and t[2] in (1, 2, 5, 10)
    return True


def encode_with(tree, target, defect, rng):
    """The encoding of the tree, with the element `target` (an object of
    the tree) written with `defect`; the elements around it get the
    lengths of what they hold."""

    def enc(t):
        cons = t[0] == "c"
        body = b"".join(enc(c) for c in t[3]) if cons else t[3]
        ident = identifier_octets(t[1], cons, t[2])
        length = length_octets(len(body))
        tail = b""
        if t is target:
            n = len(body)
            if defect == "length one more":
                length = length_octets(n + 1)
            elif defect == "length one less":
                length = length_octets(n - 1)
            elif defect == "length not in the fewest octets":
                # The long form below 128, or leading zero octets: half
                # the time one, else from one up to as many as keep the
                # length within 126 octets.
                minimal = n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")
                pad = rng.choice((1, rng.randint(1, 126 - len(minimal))))
                length = (bytes([0x81, n]) if n < 128 and rng.random() < 0.5
                          else bytes([0x80 + pad + len(minimal)]) + bytes(pad) + minimal)
            elif defect == "indefinite length":
                length, tail = b"\x80", b"\x00\x00"
            elif defect == "high form for a tag below 31":
                ident = bytes([ident[0] | 0x1f, t[2]])
            elif defect == "first subsequent tag octet 0x80":
                ident = (ident[:1] + b"\x80" + ident[1:] if t[2] >= 31
                         else bytes([ident[0] | 0x1f, 0x80, t[2]]))
            elif defect == "constructed bit flipped":
                ident = bytes([ident[0] ^ 0x20]) + ident[1:]
            elif defect == "an element running past the one it is in":
                length = length_octets(n - rng.randint(1, min(3, n)))
            elif t[2] == 1:
                body = bytes([rng.randrange(1, 255)])
            elif t[2] in (2, 10):
                body = rng.choice((b"\x00", b"\xff", b"")) + (body if rng.random() < 0.8 else b"")
            else:
                body = bytes([rng.randrange(256)])
        return ident + length + body + tail

    return enc(tree)


INTERESTING = (0x00, 0x01, 0x02, 0x04, 0x05, 0x1f, 0x20, 0x30, 0x31, 0x3f, 0x7f, 0x80, 0x81, 0x82,
               0xa0, 0xff)


def replace(tree, target, new):
    """A copy of the tree with the element `target` (an object of the
    tree) replaced by `new`."""
    if tree is target:
        return new
    if tree[0] == "p":
        return tree
    return ("c", tree[1], tree[2], [replace(c, target, new) for c in tree[3]])


def spoil(tree, rng):
    """A copy of the tree with one element the slice does not accept."""
    target = rng.choice(nodes(tree))
    kind = rng.randrange(5)
    if kind == 0:
        new = (target[0], rng.randint(4, 7)) + target[2:]
    elif kind == 1:
        new = (target[0], 0, 0, target[3])
    elif kind == 2:
        new = ("p", 0, rng.choice(sorted(CONSTRUCTED_UNIVERSAL)), random_contents(rng))
    elif kind == 3:
        # Not a reserved number, which this slice reads in either form.
        new = ("c", 0, rng.choice([n for n in PRIMITIVE_UNIVERSAL if not reserved_universal(n)]),
               target[3] if target[0] == "c" else [])
    else:
        new = ("p", 0) + rng.choice(((1, b""), (1, b"\x01"), (1, b"\x00\x00"), (2, b""),
                                     (2, b"\x00\x05"), (2, b"\xff\x80"), (10, b""),
                                     (10, b"\x00\x00"), (10, b"\xff\xff"), (5, b"\x00")))
    bad = replace(tree, target, new)
    if valid(bad):
        raise AssertionError(f"a spoiled tree the slice accepts: {show(bad)}")
    return bad


def random_octets(rng):
    n = rng.choice((rng.randint(0, 4), rng.randint(5, 16), rng.randint(17, 60)))
    return bytes(rng.choice(INTERESTING) if rng.random() < 0.6 else rng.randrange(256)
                 for _ in range(n))


def random_int_contents(rng):
    n = rng.choice((rng.randint(0, 4), rng.randint(5, 24), rng.randint(25, 300)))
    c = bytearray(rng.randbytes(n))
    if n and rng.random() < 0.6:
        c[0] = rng.choice((0x00, 0xff, 0x7f, 0x80))
    if n > 1 and rng.random() < 0.6:
        c[1] = rng.choice((0x00, 0xff, 0x7f, 0x80))
    return bytes(c)


def writeint_sets():
    label = "integers around 0 and 2^k"
    for z in range(-300, 301):
        yield (label, "writeint", (z,))
    for k in range(1001):
        for d in (-2, -1, 0, 1, 2):
            yield (label, "writeint", (2 ** k + d,))
            yield (label, "writeint", (-2 ** k + d,))


def random_sets(seed, count):
    rng = random.Random(seed)
    for _ in range(count):
        tree = random_tree(rng, rng.randint(0, 6), [rng.randint(1, 40)])
        enc = encode(tree)
        yield ("random tree", "all", (enc,))
        yield ("random tree, octets after", rng.choice(("decode", "decode", "all")),
               (enc + rng.randbytes(rng.randint(1, 3)),))
        yield ("random tree", "encode", (tree,))
        yield ("random tree", "valid", (tree,))
        bad = spoil(tree, rng)
        yield ("random tree, one element not accepted", "valid", (bad,))
        yield ("random tree, one element not accepted", "encode", (bad,))
        ts = nodes(tree)
        for _ in range(rng.randint(3, 6)):
            defect = rng.choice(DEFECTS)
            fits = [t for t in ts if applies(defect, t)]
            if not fits:
                continue
            m = encode_with(tree, rng.choice(fits), defect, rng)
            if rng.random() < 0.5:
                yield (f"random tree, {defect}", "all", (m,))
            else:
                yield (f"random tree, {defect}", "decode", (m + rng.randbytes(rng.randint(0, 2)),))
        flipped = bytearray(enc)
        k = rng.randrange(8 * len(enc))
        flipped[k // 8] ^= 0x80 >> (k % 8)
        yield ("random tree, a bit flipped", "decode", (bytes(flipped),))
        yield ("random tree, cut short", "decode", (enc[:rng.randrange(len(enc))],))
    for _ in range(count // 2):
        yield ("random octets", "decode", (random_octets(rng),))
    for _ in range(count // 4):
        yield ("random integer contents", "readint", (random_int_contents(rng),))
        yield ("random integers", "writeint",
               (rng.choice((-1, 1)) * rng.getrandbits(rng.choice((8, 64, 512, 4096))),))


def inputs(seed, count, vectors):
    """(label, op, args) for every request."""
    yield from [("X.690 examples", op, a) for op, a, _ in x690_examples()]
    yield from short_sets()
    yield from identifier_sets()
    yield from length_sets()
    yield from size_sets()
    yield from high_tag_sets()
    yield from universal_sets()
    yield from contents_sets()
    yield from deep_sets()
    for sig, _ in vectors:
        yield ("Wycheproof ECDSA signatures", "all", (sig,))
    yield from writeint_sets()
    yield from random_sets(seed, count)


# Request lines, each sent with LF after it, that the tool must answer
# `error`. One ending in CR is sent ending in CR LF.
MALFORMED = ["", " ", "\r", "decode", "decode 0101ff 00", "DECODE 0101ff", "Decode 0101ff",
             "decode 0101FF", "decode 0", "decode 010", "decode 0g", "decode --", "decode -0101",
             "decode  0101ff", "decode 0101ff ", " decode 0101ff", "decode\t0101ff",
             "decode 0101ff\t", "decode ", "decode 0101ff\r\r", "decode\r 0101ff", "decode 0x01",
             "decode é", "decode 0101ff\x00", "all", "all 0101FF", "all 0101ff 0101ff",
             "all  0101ff", "readint", "readint 0G", "readint 1", "readint 00 00", "readint +01",
             "writeint", "writeint +1", "writeint 1.0", "writeint 1e3", "writeint --1",
             "writeint -", "writeint 0x10", "writeint - 1", "writeint 1 2", "writeint ١",
             "writeint  1", "writeint 1 ", "encode", "encode p0.2", "encode p0.2.", "encode p0.2.0",
             "encode p0.2.0G", "encode P0.2.00", "encode p0..00", "encode p.2.00",
             "encode p-1.2.00", "encode p0.-2.00", "encode p0.2.00)", "encode p0.2.00,",
             "encode c0.16(", "encode c0.16", "encode c0.16)", "encode c0.16(p0.5.-",
             "encode c0.16(,)", "encode c0.16(p0.5.-,)", "encode c0.16(p0.5.-))",
             "encode c0.16(p0.5.-)x", "encode c0.16.(p0.5.-)", "encode c0.16 (p0.5.-)",
             "encode x", "encode -", "encode p0.2.00 p0.2.00", "encode p0x1.2.00",
             "encode p0.2.-0", "encode p0.2.00(", "encode c0.16((p0.5.-))", "encode p0.2.0A",
             "encode p0.١.00", "encode c0.16(p0.5.-p0.5.-)", "encode ()", "nop", "DECODE",
             "decode 0101ff\x0b", "readint -00", "writeint 1-", "valid", "valid p0.2",
             "valid p0.5.- p0.5.-", "VALID p0.5.-", "Valid p0.5.-", "valid 0500", "valid  p0.5.-",
             "valid p0.5.- "]

# Well-formed but odd: leading zeros, large numbers, `-` fields, CR LF.
ODD = ["decode -", "all -", "readint -", "writeint 0", "writeint -0", "writeint 007",
       "writeint -007", "writeint 340282366920938463463374607431768211456",
       "writeint -340282366920938463463374607431768211457", "encode p0.5.-", "encode c0.16()",
       "encode p00.002.00", "encode c3.000099999999999999999999()", "encode p2.31.-",
       "encode c1.30(c2.31(p3.0.-),p0.1.00)", "decode 0101ff\r", "all 0500\r", "readint 0080\r",
       "writeint -129\r", "encode c0.16(p0.5.-)\r", "decode 1f8100", "encode p4.2.00",
       "encode c5.16(p0.5.-)", "encode c7.40(p6.300.00)", "valid p4.2.00", "valid p3.2.0080",
       "valid c0.16()", "valid p0.0.-", "valid c0.10()", "valid p0.10.0001", "valid p0.10.ff",
       "valid c1.2(p0.10.-)", "valid c0.16(p0.5.-)\r"]

# Last lines sent alone, as they are sent, and the answer due: with no
# LF, with CR LF, and with a lone CR, which is not a line ending.
AT_EOF = [("decode 0101ff", "OK p0.1.ff -"), ("decode 0101ff\r\n", "OK p0.1.ff -"),
          ("all 0500\r\n", "OK p0.5.-"), ("decode 0101ff\r", "error")]


def cli_cases():
    """Runs of `der decode HEX` and wrong arguments: (arguments, what the
    run must print on standard output, without the last LF, and its exit
    status), from the model. A run that does not decode, malformed HEX
    and wrong arguments print nothing on standard output, and exit with
    1, 2 and 2."""
    cases = []
    hexes = ("0101ff", "0101ff00", "30060201010500", "0101", "1a054a6f6e6573",
             "3a8004034a6f6e040265730000", "0500ff", "1f2a00", "1f05", "0481c9")
    inputs_ = [bytes.fromhex(h) for h in hexes]
    inputs_ += [b"", encode(chain(100, ("p", 0, 5, b""), ((0, 16), (2, 3))))]
    for data in inputs_:
        (r, _), _ = read(data)
        cases.append((["decode", hx(data)], f"{show(r[0])} {hx(r[1])}" if r else "",
                      0 if r else 1))
    for bad in ["", "0101FF", "1", "0x01", "01 01", "--", "-0101", "zz", "0101ff\r"]:
        cases.append((["decode", bad], "", 2))
    for args in [[], ["decode"], ["decode", "0101ff", "00"], ["bogus"], ["serve", "x"],
                 ["all", "0101ff"], ["DECODE", "0101ff"], ["decode", "-", "-"]]:
        cases.append((args, "", 2))
    return cases


def run_cli(cases):
    """How many runs print and exit as `cli_cases` says, and a failure
    for each other."""
    right, failures = 0, []
    for args, out, status in cases:
        try:
            p = subprocess.run([str(EXE)] + args, capture_output=True, timeout=60,
                               stdin=subprocess.DEVNULL)
            got, code_ = p.stdout.decode("utf-8", "backslashreplace"), p.returncode
            if got.endswith("\n"):
                got = got[:-1]
        except (OSError, subprocess.SubprocessError) as e:
            got, code_ = str(e), None
        if (got, code_) == (out, status):
            right += 1
        else:
            failures.append((f"der {' '.join(repr(a) for a in args)}",
                             f"{short(out, 160)!r}, exit {status}",
                             f"{short(got, 160)!r}, exit {code_}"))
    return right, failures

# ---------------------------------------------------------------------


def lean_version():
    try:
        out = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, errors="backslashreplace",
                             timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count_arg(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def code(text):
    """`text` as Markdown inline code, whatever backticks it holds."""
    return f"`` {text} ``" if "`" in text else f"`{text}`"


def short(text, n=200):
    return text if len(text) <= n else text[:n] + f"... ({len(text)} characters)"


def main():
    sys.set_int_max_str_digits(0)
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261027)
    ap.add_argument("--count", type=count_arg, default=100000)
    ap.add_argument("--no-oracles", action="store_true",
                    help="compare with the model only, as tests/plant_bugs.py does")
    args = ap.parse_args()
    os.environ["PATH"] = f"{Path.home() / '.elan' / 'bin'}{os.pathsep}{os.environ.get('PATH', '')}"

    def give_up(why):
        write(["# Test results", "", "- Oracle: none ran", f"- Seed: {args.seed}", "- Inputs: 0",
               f"- Failures: 1 ({why})", ""])
        sys.exit(why)

    try:
        vectors = read_wycheproof()
    except (OSError, ValueError, KeyError, TypeError) as e:
        give_up(f"the Wycheproof vectors could not be read: {e}")

    try:
        build = subprocess.run(["lake", "build", "der"], cwd=ROOT, capture_output=True,
                               text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
        if build.returncode != 0:
            print(build.stdout + build.stderr)
            give_up("`lake build der` failed")
    except (OSError, subprocess.SubprocessError) as e:
        give_up(f"`lake build der` failed: {e}")

    failures = []
    examples = x690_examples()
    examples_right = 0
    for op, a, due in examples:
        got = model(op, a)[0]
        if got == due:
            examples_right += 1
        else:
            failures.append((f"the model on {short(request(op, a))}", short(due), short(got)))

    cli = cli_cases()
    cli_right, cli_failures = run_cli(cli)
    failures += cli_failures

    oracles, left_out = [], []
    for names, setup in ORACLE_SETUPS:
        if args.no_oracles:
            left_out += [(name, "--no-oracles") for name in names]
            continue
        try:
            oracles += setup()
        except Exception as e:  # any oracle that cannot start is left out, and recorded
            why = str(e).splitlines()[0][:300] if str(e) else type(e).__name__
            left_out += [(name, why) for name in names]
    for name, why in left_out:
        print(f"oracle left out: {name}: {why}")

    items = list(inputs(args.seed, args.count, vectors))
    requests = [request(op, a) for _, op, a in items]
    lines = [r + ("\r\n" if i % 7 == 6 else "\n") for i, r in enumerate(requests)]
    deep = [i for i, (label, _, _) in enumerate(items) if label.startswith("nested")]
    deep_set = set(deep)
    rest = [i for i in range(len(items)) if i not in deep_set]

    # The tool: the deep requests one to a process, under DEEP_BUDGET;
    # the others, then the malformed and odd ones, over JOBS processes.
    tool = [None] * len(items)
    deep_in_time = 0
    for i in deep:
        started = time.monotonic()
        got, problem = run_lines([str(EXE), "serve"], [lines[i]], timeout=DEEP_BUDGET)
        took = time.monotonic() - started
        print(f"{items[i][0]} {items[i][1]}: {took:.1f} s")
        if problem or len(got) != 1:
            failures.append((short(requests[i], 120), f"an answer within {DEEP_BUDGET} seconds",
                             problem or f"{len(got)} answers"))
            got = [""]
        else:
            deep_in_time += 1
        tool[i] = got[0]
    odd = MALFORMED + ODD
    out, problems = run_parallel([str(EXE), "serve"],
                                 [lines[i] for i in rest] + [m + "\n" for m in odd], JOBS)
    for problem in problems:
        failures.append(("(whole run)", "a clean run", problem))
    for i, a in zip(rest, out):
        tool[i] = a
    odd_out = out[len(rest):]
    malformed_right = sum(1 for m, a in zip(MALFORMED, odd_out) if a == "error")
    for m in MALFORMED:
        if model_line(m + "\n") != "error":
            failures.append((f"the model on {m!r}", "error", model_line(m + "\n")))
    odd_right = 0
    for m, a in zip(odd, odd_out):
        want = model_line(m + "\n")
        if a == want:
            odd_right += m in ODD
        else:
            failures.append((f"request {m!r}", want, a))
    eof_right = 0
    for req, want in AT_EOF:
        if model_line(req) != want:
            failures.append((f"the model on {req!r} at end of input", want, model_line(req)))
        got, problem = run_lines([str(EXE), "serve"], [req], timeout=60)
        if got == [want] and not problem:
            eof_right += 1
        else:
            failures.append((req + " (at end of input)", want, f"{got} {problem or ''}".strip()))

    # Against the model.
    wants, whys = [], []
    differ_model = 0
    refused = {}
    for (label, op, a), got in zip(items, tool):
        want, why, _ = model(op, a)
        wants.append(want)
        whys.append(why)
        if why is not None:
            kind = "integer" if op == "readint" else "element"
            refused[(kind, why)] = refused.get((kind, why), 0) + 1
        if got != want:
            differ_model += 1
            failures.append((short(request(op, a)), short(want, 160), short(got, 160)))

    # What the tool encodes, read back by the model.
    encodes = [(i, a) for i, (_, op, a) in enumerate(items) if op == "encode"]
    read_back = 0
    for i, a in encodes:
        got = tool[i]
        try:
            (r, _), _ = read(octets_field(got[3:])) if got.startswith("OK ") else ((None, None), 0)
        except ValueError:
            r = None
        ok = valid(a[0])
        if not ok or (r is not None and not r[1] and show(r[0]) == show(a[0])):
            read_back += ok
        else:
            failures.append((f"the model reading back {short(request('encode', a), 120)}",
                             short(show(a[0]), 120), short(got, 120)))
    n_valid_encodes = sum(1 for _, a in encodes if valid(a[0]))

    # `valid` holds exactly when the model reads the encoding back as the tree.
    valids = [a for _, op, a in items if op == "valid"]
    valid_back = 0
    for a in valids:
        (r, _), _ = read_all(encode(a[0]))
        if (r is not None and show(r[0]) == show(a[0])) == valid(a[0]):
            valid_back += 1
        else:
            failures.append((f"the model on {short(request('valid', a), 120)}",
                             "`valid` exactly when the encoding reads back as the tree",
                             f"valid {valid(a[0])}"))
    n_valid_ok = sum(1 for a in valids if valid(a[0]))

    # The Wycheproof signatures.
    first_sig = next(i for i, it in enumerate(items) if it[0] == "Wycheproof ECDSA signatures")
    sig_answers = tool[first_sig:first_sig + len(vectors)]
    flagged = {f: [0, 0] for f in ENCODING_FLAGS}
    sig_differ = 0
    for (sig, flags), got, want in zip(vectors, sig_answers,
                                       wants[first_sig:first_sig + len(vectors)]):
        sig_differ += got != want
        for f in ENCODING_FLAGS:
            if f in flags:
                flagged[f][0] += 1
                flagged[f][1] += got == "FAIL"
    sig_refused = sum(1 for got in sig_answers if got == "FAIL")

    # Against the oracles.
    oracle_out = {}

    def ask(o):
        try:
            oracle_out[o.name] = o.answers(lines)
        except (RuntimeError, OSError) as e:
            oracle_out[o.name] = e

    threads = [threading.Thread(target=ask, args=(o,)) for o in oracles]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    for o in list(oracles):
        if isinstance(oracle_out[o.name], Exception):
            failures.append((f"({o.name} oracle run)", "a clean run", str(oracle_out[o.name])[:300]))
            oracles.remove(o)
    names = [o.name for o in oracles]
    # Elements each oracle reads, and how many of its answers the model
    # gives with the rules the oracle reads by.
    by_rules = {o: [0, 0] for o in names}
    asked = {o: 0 for o in names}
    agree = {o: 0 for o in names}
    by_op = {o: {} for o in names}
    named = {o: {} for o in names}
    for i, (label, op, a) in enumerate(items):
        got = tool[i]
        for o in names:
            theirs = oracle_out[o][i]
            if theirs == "n/a":
                continue
            asked[o] += 1
            by_op[o][op] = by_op[o].get(op, 0) + 1
            theirs_by_model, parted = None, set()
            if op in ("decode", "all"):
                # The model, with the rules the oracle reads by, must give
                # its answer, whether or not it agrees with the tool.
                theirs_by_model, _, parted = model(op, a, ORACLE_RULES[o])
                by_rules[o][0] += 1
                if theirs_by_model == theirs:
                    by_rules[o][1] += 1
                else:
                    failures.append((f"{o}, as the model reads with its rules: "
                                     f"{short(request(op, a))}", short(theirs_by_model, 160),
                                     short(theirs, 160)))
            if theirs == got:
                agree[o] += 1
                continue
            if theirs_by_model is not None and theirs_by_model != theirs:
                continue  # already a failure
            reason = difference_reason(o, op, theirs, theirs_by_model, parted)
            if reason is None:
                failures.append((f"{o}: {short(request(op, a))}", short(got, 160),
                                 short(theirs, 160)))
            else:
                n, example = named[o].get(reason, (0, None))
                named[o][reason] = (n + 1, example or request(op, a))

    by_label = {}
    for label, op, _ in items:
        key = f"{label} {op}"
        by_label[key] = by_label.get(key, 0) + 1

    def refusals(kind):
        return ", ".join(f"{why} {n}" for (k, why), n in
                         sorted(refused.items(), key=lambda kv: -kv[1]) if k == kind)

    n_elements = sum(1 for _, op, _ in items if op in ("decode", "all"))
    ok_elements = sum(1 for (_, op, _), y in zip(items, whys) if op in ("decode", "all") and y is None)
    n_readint = sum(1 for _, op, _ in items if op == "readint")
    ok_readint = sum(1 for (_, op, _), y in zip(items, whys) if op == "readint" and y is None)
    n_writeint = sum(1 for _, op, _ in items if op == "writeint")

    lines_out = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Lean: {lean_version()}",
        "- Oracle: the model of X.690 (02/2021) in `tests/run_tests.py`"
        + "".join(f"; {o.name}, {o.version}" for o in oracles),
    ]
    lines_out += [f"- {o.name}: {o.version}" for o in oracles]
    lines_out += [
        "- Oracles left out: " + ("; ".join(f"{n} ({why})" for n, why in left_out)
                                  if left_out else "none"),
        f"- Seed: {args.seed}",
        f"- Inputs: {len(items)}",
        "- By kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())),
        f"- Answers that differ from the model: {differ_model}",
        f"- X.690's examples, answered by the model as the standard gives them: {examples_right} "
        f"of {len(examples)}",
        f"- Elements read (`decode` and `all`): {n_elements}, of which {ok_elements} are accepted; "
        f"why the model refuses the others: {refusals('element')}",
        f"- Integer contents read (`readint`): {n_readint}, of which {ok_readint} give a value; why "
        f"the model refuses the others: {refusals('integer')}",
        f"- Encodings asked for: trees {len(encodes)}, of which the model reads the tool's "
        f"encoding back as the tree for {read_back} of the {n_valid_encodes} the slice accepts; "
        f"integers {n_writeint}",
        f"- `valid` asked of {len(valids)} trees, of which the slice accepts {n_valid_ok}; the "
        f"model's answer holds exactly when it reads the tree's encoding back as the tree, for "
        f"{valid_back} of {len(valids)}",
        f"- Wycheproof: `tests/wycheproof/{WYCHEPROOF.name}`, SHA-256 {WYCHEPROOF_SHA256}: "
        f"{len(vectors)} signatures read with `all`, of which the tool refuses {sig_refused}, "
        f"every answer as the model's but {sig_differ}. Flagged as an encoding that is not DER "
        f"or is broken: "
        + ", ".join(f"{f} {n}, of which the tool refuses {r}" for f, (n, r) in flagged.items())
        + ". Each flagged one it accepts is an element this slice accepts, with what is wrong "
        "in something it does not check: a negative INTEGER where a positive one belongs, a BIT "
        "STRING where an INTEGER belongs, or a SEQUENCE given the reserved universal tag 15",
        f"- Requests nested 1,000 (`valid`), 10,000 and 100,000 deep, each sent to a `der serve` "
        f"of its own: {len(deep)}, answered within {DEEP_BUDGET} seconds: {deep_in_time}",
        "- Agreement with each oracle over the requests it answers: "
        + ", ".join(f"{o} {agree[o]} of {asked[o]}" for o in names),
        "- Elements each oracle reads (`decode` and `all`) whose answer the model gives with the "
        "rules that oracle reads by, whether or not it agrees with the tool (any other is a "
        "failure): "
        + ", ".join(f"{o} {by_rules[o][1]} of {by_rules[o][0]}" for o in names),
        "- Requests each oracle answers, by operation: "
        + "; ".join(f"{o}: " + ", ".join(f"{op} {n}" for op, n in sorted(by_op[o].items()))
                    for o in names),
        f"- Malformed requests answered `error`: {malformed_right} of {len(MALFORMED)}; odd but "
        f"well-formed requests answered as the model says: {odd_right} of {len(ODD)}",
        f"- Requests ending in CR LF: every seventh, {len(requests) // 7}",
        f"- Last lines sent alone, with no LF, with CR LF, or with a lone CR, answered right: "
        f"{eof_right} of {len(AT_EOF)}",
        f"- Command-line mode `der decode` and wrong arguments, printing and exiting as the model "
        f"says: {cli_right} of {len(cli)}",
        f"- Failures: {len(failures)}",
        "",
        "## Where the oracles differ",
        "",
        "Each disagreement is counted under the reason the model confirms: the model, with the "
        "rules the oracle reads by, gives the oracle's answer. The reason names each rule on which "
        "those part from DER for the input, with the first input that showed it.",
        "",
    ]
    for o in names:
        lines_out.append(f"### {o}")
        lines_out.append("")
        if not named[o]:
            lines_out.append("No disagreement.")
        for reason, (n, example) in sorted(named[o].items(), key=lambda kv: -kv[1][0]):
            lines_out.append(f"- {reason}: {n}; for example {code(short(example, 240))}")
        lines_out.append("")
    if failures:
        lines_out += ["## Failures", ""]
        lines_out += [f"- {code(req)}: expected {code(want)}, got {code(got)}"
                      for req, want, got in failures[:50]]
        lines_out.append("")
    write(lines_out)
    print(f"{len(items)} inputs, {len(oracles)} oracles, {len(failures)} failures; results in "
          f"{RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
