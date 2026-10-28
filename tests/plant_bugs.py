#!/usr/bin/env python3
"""Check that the differential tests catch planted bugs.

Each bug is a one-line change to Der/Basic.lean, or to Main.lean where
its description says so. The script copies the project to a temporary
folder, plants one bug at a time, runs tests/run_tests.py there with a
small count and without the oracles, and records how many failures the
tests report. So every failure counted is the tool disagreeing with the
model of X.690; an oracle that crashes or times out cannot pass for a
catch. Every planted bug must give at least one failure. The unchanged
copy must give none. A bug that stops the executable from building is
not a catch: the tests then give up, and the bug counts as missed. So is
any run that gives up (its record shows `- Failures: 1 (why)`), a run
that dies without writing its record, and one whose exit status does
not match the failures it records. The tests build only the executable
(`lake build der`), so a bug that breaks a proof still runs.

    python3 tests/plant_bugs.py [--count N]

The script writes tests/PLANTED-BUGS.md and exits non-zero if any bug
goes uncaught.
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "tests" / "PLANTED-BUGS.md"
CODE = "Der/Basic.lean"

# (what the bug does, the line as written, the line with the bug[, file])
BUGS = [
    ("the long form is read for a length below 128",
     "    if n < 128 then none else some (n, k + 1, bs.drop k)",
     "    if n < 0 then none else some (n, k + 1, bs.drop k)"),
    ("the long form is refused for a length below 256",
     "    if n < 128 then none else some (n, k + 1, bs.drop k)",
     "    if n < 256 then none else some (n, k + 1, bs.drop k)"),
    ("a leading zero length octet is read",
     "  if ds.length < k ∨ ds.head? = some 0 then none",
     "  if ds.length < k then none"),
    ("the indefinite length octet 0x80 is read as length 0",
     "    if b.toNat < 128 then some (b.toNat, 1, bs)",
     "    if b.toNat ≤ 128 then some (b.toNat % 128, 1, bs)"),
    ("a tag number below 31 is read in the high form",
     "          if tag < 31 then none else some (cls, constructed, tag, ds.length + 2, rest)",
     "          if tag < 0 then none else some (cls, constructed, tag, ds.length + 2, rest)"),
    ("a first subsequent tag octet 0x80 is read",
     "        if d = 0 then none",
     "        if d = 128 then none"),
    ("the continuation bit of a tag octet is tested as 0x40",
     "    if b.toNat < 128 then some ((b.toNat :: acc).reverse, bs)",
     "    if b.toNat < 64 then some ((b.toNat :: acc).reverse, bs)"),
    ("the constructed bit is read from bit 7",
     "    let constructed := b.toNat / 32 % 2 == 1",
     "    let constructed := b.toNat / 64 % 2 == 1"),
    ("a BOOLEAN 01 is read",
     "  | 1 => c == [0] || c == [255]",
     "  | 1 => c.length == 1"),
    ("an INTEGER with a redundant leading zero octet is read",
     "  | a :: b :: _ => !(a.toNat == 255 && 128 ≤ b.toNat) && !(a.toNat == 0 && b.toNat < 128)",
     "  | a :: b :: _ => !(a.toNat == 255 && 128 ≤ b.toNat)"),
    ("a NULL with one contents octet is read",
     "  | 5 => c.isEmpty",
     "  | 5 => c.length ≤ 1"),
    ("universal tag 0 is read",
     "  cls != 0 || (tag != 0 && !constructedUniversal tag && contentsOk tag c)",
     "  cls != 0 || (!constructedUniversal tag && contentsOk tag c)"),
    ("a primitive SEQUENCE is read",
     "  cls != 0 || (tag != 0 && !constructedUniversal tag && contentsOk tag c)",
     "  cls != 0 || (tag != 0 && !(constructedUniversal tag && tag != 16) && contentsOk tag c)"),
    ("a constructed INTEGER is read",
     "  cls != 0 || constructedUniversal tag || reservedUniversal tag",
     "  cls != 0 || constructedUniversal tag || reservedUniversal tag || tag == 2"),
    ("universal 29 is taken for a primitive type",
     "  tag == 8 || tag == 11 || tag == 16 || tag == 17 || tag == 29",
     "  tag == 8 || tag == 11 || tag == 16 || tag == 17"),
    ("the reserved universal numbers start at 38, not 37",
     "def reservedUniversal (tag : Nat) : Bool := tag == 15 || 37 ≤ tag",
     "def reservedUniversal (tag : Nat) : Bool := tag == 15 || 38 ≤ tag"),
    ("an element may run one octet past the one it is in",
     "        if lim < n1 + n2 + len then none",
     "        if lim + 1 < n1 + n2 + len then none"),
    ("the elements of a constructed element must take one octet more than it holds",
     "      match readElements fuel (lim - n) b' with",
     "      match readElements fuel (lim - n + 1) b' with"),
    ("the reader's fuel is half the length of the input",
     "  match readElement b.length b.length b with",
     "  match readElement (b.length / 2) b.length b with"),
    ("decodeAll allows octets after the element",
     "  | some (e, []) => some e",
     "  | some (e, _) => some e"),
    ("long numbers: the first half is shifted by the length of the first half, not the second",
     "        (go fuel (ds.take h) <<< (w * (ds.length - h))) + go fuel (ds.drop h)",
     "        (go fuel (ds.take h) <<< (w * h)) + go fuel (ds.drop h)"),
    ("readInt takes a first octet 0x80 for a positive integer",
     "    | a :: _ => some (if a.toNat < 128 then (u : Int) else (u : Int) - 2 ^ (8 * c.length))",
     "    | a :: _ => some (if a.toNat ≤ 128 then (u : Int) else (u : Int) - 2 ^ (8 * c.length))"),
    ("writeInt writes 128 with no zero octet in front",
     "    | d :: _ => if 128 ≤ d.toNat then 0 :: ds else ds",
     "    | d :: _ => if 128 < d.toNat then 0 :: ds else ds"),
    ("the writer gives no subsequent tag octet but the last its bit 8",
     "    (lead + 31).toUInt8 :: (ds.dropLast.map fun d => (d + 128).toUInt8) ++ "
     "[(ds.getLastD 0).toUInt8]",
     "    (lead + 31).toUInt8 :: (ds.dropLast.map fun d => d.toUInt8) ++ "
     "[(ds.getLastD 0).toUInt8]"),
    ("the writer writes length 128 in the short form",
     "  if n < 128 then [n.toUInt8]",
     "  if n ≤ 128 then [n.toUInt8]"),
    ("the writer writes tag number 31 in one octet",
     "  if tag < 31 then [(lead + tag).toUInt8]",
     "  if tag ≤ 31 then [(lead + tag).toUInt8]"),
    ("Main.lean: `all` allows octets after the element",
     "    pure (match decodeAll b with",
     "    pure (match (decode b).map (·.1) with",
     "Main.lean"),
    ("Main.lean: `der decode` exits with 0 when the input is not an element",
     '      | none => IO.eprintln "not a DER element"; return 1',
     '      | none => IO.eprintln "not a DER element"; return 0',
     "Main.lean"),
    ("Main.lean: the CR of a CR LF line ending is kept",
     "    String.ofList (if cs.getLast? = some '\\r' then cs.dropLast else cs)",
     "    String.ofList cs",
     "Main.lean"),
    ("Main.lean: a primitive element is printed with its number before its class",
     '  | .prim cls tag c => s ++ s!"p{cls}.{tag}." ++ toHex c',
     '  | .prim cls tag c => s ++ s!"p{tag}.{cls}." ++ toHex c',
     "Main.lean"),
    ("Main.lean: upper-case hex digits are read",
     "  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)",
     "  else if 'a' ≤ c.toLower ∧ c.toLower ≤ 'f' then some (c.toLower.toNat - 'a'.toNat + 10)",
     "Main.lean"),
    ("an ENUMERATED is not checked",
     "  | 10 => intOk c",
     "  | 10 => true"),
    ("valid takes a primitive element of class 4",
     "  | .prim cls tag c => cls < 4 && primOk cls tag c && c.length < 256 ^ 126",
     "  | .prim cls tag c => cls < 5 && primOk cls tag c && c.length < 256 ^ 126"),
    ("valid does not look inside a constructed element",
     "    cls < 4 && consOk cls tag && validList cs && (encodeList cs).length < 256 ^ 126",
     "    cls < 4 && consOk cls tag && (encodeList cs).length < 256 ^ 126"),
    ("Main.lean: `valid` answers OK for every tree",
     '    pure (if valid e then "OK" else "FAIL")',
     '    pure "OK"',
     "Main.lean"),
]


def failures(copy, count):
    """The failures a run of the tests reports, or None, with the run's
    output, when it reports none: the code did not build, or the run did
    not finish. A run that dies writes no record, so the old one is
    removed first rather than read again."""
    record = copy / "tests" / "TEST-RESULTS.md"
    record.unlink(missing_ok=True)
    run = subprocess.run([sys.executable, "tests/run_tests.py", "--count", str(count),
                          "--no-oracles"],
                         cwd=copy, capture_output=True, text=True)
    out = run.stdout + run.stderr
    if not record.exists():
        return None, f"no record written, exit status {run.returncode}\n{out}"
    m = re.search(r"^- Failures: (\d+)(.*)$", record.read_text(encoding="utf-8"), re.M)
    if m is None or m.group(2).strip():
        return None, out  # the run gave up, for example the bug did not build: not a catch
    n = int(m.group(1))
    if run.returncode != (1 if n else 0):
        return None, f"{n} failures but exit status {run.returncode}\n{out}"
    return n, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=5000)
    args = ap.parse_args()
    rows, missed = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "der"
        shutil.copytree(ROOT, copy, symlinks=True,
                        ignore=shutil.ignore_patterns("PLANTED-BUGS.md", "__pycache__",
                                                      "oracle-go", "oracle-rust",
                                                      "oracle-openssl"))
        n, err = failures(copy, args.count)
        rows.append(("none", n))
        if n != 0:
            missed += 1
        print(f"none: {n} failures" + (" (did not build or did not finish)" if err else ""),
              flush=True)
        if err:
            print(err[-2000:], flush=True)
        for what, line, bug, *where in BUGS:
            name = where[0] if where else CODE
            code = copy / name
            original = code.read_text(encoding="utf-8")
            if original.count(line) != 1:
                sys.exit(f"{name} no longer holds, once, the line for {what!r}: {line}")
            code.write_text(original.replace(line, bug), encoding="utf-8")
            n, err = failures(copy, args.count)
            code.write_text(original, encoding="utf-8")
            rows.append((what, n))
            if not n:
                missed += 1
            print(f"{what}: {n} failures" + (" (did not build or did not finish)" if err else ""),
                  flush=True)
            if err:
                print(err[-2000:], flush=True)
    n_main = sum(1 for b in BUGS if b[3:] == ("Main.lean",))
    lines = ["# Planted bugs", "",
             f"Written by `tests/plant_bugs.py`. Each bug is a change of one line, to `{CODE}` "
             f"({len(BUGS) - n_main} bugs) or to `Main.lean` ({n_main}), tested with "
             f"`tests/run_tests.py --count {args.count} --no-oracles`, which builds only the "
             "executable and compares it with the model alone. Every bug must give failures, and "
             "the unchanged code none. A bug that does not build, or a run that gives up or "
             "dies, counts as missed.", "",
             "| Planted bug | Failures |", "|---|---|"]
    lines += [f"| {what} | {'did not build or did not finish' if n is None else n} |"
              for what, n in rows]
    lines += ["", f"Bugs caught: {sum(1 for what, n in rows[1:] if n)} of {len(BUGS)}", ""]
    RECORD.write_text("\n".join(lines), encoding="utf-8")
    return 1 if missed else 0


if __name__ == "__main__":
    sys.exit(main())
