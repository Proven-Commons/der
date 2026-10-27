/-
  Command line front end.

    der decode HEX

  prints the element at the start of some octets, as a tree, then the
  hex of the octets after it, or exits with 1 when they do not start
  with an element this library accepts. HEX is lower-case hex digits in
  pairs, or `-` for no octets; malformed HEX or wrong arguments exit
  with 2.

    der serve

  answers requests on standard input, one per line, for the
  differential tests. Octets are hex digits, two per octet, and an empty
  field is written `-`. Numbers are decimal, an integer with `-` in
  front when it is negative.

    decode HEX      prints  OK, the tree and the hex of the rest, or FAIL
                                                          (decode)
    all HEX         prints  OK and the tree, or FAIL      (decodeAll)
    encode TREE     prints  OK and the hex                (encode)
    readint HEX     prints  OK and the integer, or FAIL   (readInt)
    writeint INT    prints  OK and the hex                (writeInt)

  A tree is written with no spaces: a primitive element as `p`, its
  class, `.`, its tag number, `.` and the hex of its contents, such as
  `p0.2.0080`; a constructed one as `c`, its class, `.`, its tag number,
  then its elements between `(` and `)`, separated by `,`, such as
  `c0.16(p0.2.01,p0.5.-)`.

  A malformed request prints `error`: an unknown operation, the wrong
  number of fields, hex digits that are not in pairs or not lower case,
  a number that is not decimal, or a tree that does not parse. A
  request line may end in LF or CR LF.

  Every answer comes from the proved functions in `Der/`. The hex and
  tree coding and the request handling here are covered by the tests,
  not by a proof.
-/

import Der

open Der

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Octets from hex digits in pairs. Tail recursive, so that long
    inputs do not use the stack. -/
def hexBytes (cs : List Char) (acc : Array UInt8) : Option (Array UInt8) :=
  match cs with
  | [] => some acc
  | a :: b :: rest =>
    match hexValue a, hexValue b with
    | some hi, some lo => hexBytes rest (acc.push (hi * 16 + lo).toUInt8)
    | _, _ => none
  | [_] => none

/-- The octets a field gives: `-` for none, else hex digits in pairs. -/
def fromHex (f : String) : Option (List UInt8) :=
  if f = "-" then some [] else if f.isEmpty then none else (hexBytes f.toList #[]).map (·.toList)

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- A field for a list of octets: `-` when it is empty. -/
def toHex (bs : List UInt8) : String :=
  if bs.isEmpty then "-"
  else String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- A decimal number, without sign or leading `+`. -/
def decimal (s : String) : Option Nat :=
  if !s.isEmpty && s.all Char.isDigit then s.toNat? else none

/-- A decimal integer, with `-` in front when it is negative. -/
def integer (s : String) : Option Int :=
  if s.startsWith "-" then (decimal (String.ofList (s.toList.drop 1))).map fun n => -(n : Int)
  else (decimal s).map fun n => (n : Int)

mutual
/-- A tree as text, after `s`. Each piece is added to the end of one
    string, so a deep tree takes time linear in its size. -/
partial def showTreeInto (s : String) : Element → String
  | .prim cls tag c => s ++ s!"p{cls}.{tag}." ++ toHex c
  | .cons cls tag cs => showTreesInto (s ++ s!"c{cls}.{tag}(") cs ++ ")"

/-- Trees separated by `,`, after `s`. -/
partial def showTreesInto (s : String) : List Element → String
  | [] => s
  | [e] => showTreeInto s e
  | e :: es => showTreesInto (showTreeInto s e ++ ",") es
end

/-- A tree as text. -/
def showTree (e : Element) : String := showTreeInto "" e

/-- Digits at the start of the input, as a number, and what follows. -/
def readNumber (cs : List Char) : Option (Nat × List Char) :=
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty then none else some ((String.ofList ds).toNat!, cs.drop ds.length)

mutual
/-- A tree at the start of the input, and what follows. -/
partial def parseTree (cs : List Char) : Option (Element × List Char) := do
  match cs with
  | 'p' :: rest =>
    let (cls, rest) ← readNumber rest
    let '.' :: rest := rest | none
    let (tag, rest) ← readNumber rest
    let '.' :: rest := rest | none
    let field := rest.takeWhile fun c => c != ',' && c != ')'
    let c ← fromHex (String.ofList field)
    pure (.prim cls tag c, rest.drop field.length)
  | 'c' :: rest =>
    let (cls, rest) ← readNumber rest
    let '.' :: rest := rest | none
    let (tag, rest) ← readNumber rest
    let '(' :: rest := rest | none
    match rest with
    | ')' :: rest => pure (.cons cls tag [], rest)
    | _ =>
      let (es, rest) ← parseTrees rest
      pure (.cons cls tag es, rest)
  | _ => none

/-- Trees separated by `,`, up to and with the closing `)`. -/
partial def parseTrees (cs : List Char) : Option (List Element × List Char) := do
  let (e, rest) ← parseTree cs
  match rest with
  | ',' :: rest =>
    let (es, rest) ← parseTrees rest
    pure (e :: es, rest)
  | ')' :: rest => pure ([e], rest)
  | _ => none
end

/-- A whole field as a tree. -/
def treeField (f : String) : Option Element :=
  match parseTree f.toList with
  | some (e, []) => some e
  | _ => none

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["decode", h] => do
    let b ← fromHex h
    pure (match decode b with
      | some (e, rest) => s!"OK {showTree e} {toHex rest}"
      | none => "FAIL")
  | ["all", h] => do
    let b ← fromHex h
    pure (match decodeAll b with
      | some e => s!"OK {showTree e}"
      | none => "FAIL")
  | ["encode", t] => do
    let e ← treeField t
    pure s!"OK {toHex (encode e)}"
  | ["readint", h] => do
    let c ← fromHex h
    pure (match readInt c with
      | some z => s!"OK {z}"
      | none => "FAIL")
  | ["writeint", z] => do
    let z ← integer z
    pure s!"OK {toHex (writeInt z)}"
  | _ => none

/-- A request line without its line ending, LF or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn ((request (chomp line)).getD "error")
    stdout.flush

def usage : String := "usage: der decode HEX\n       der serve"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["decode", h] =>
    match fromHex h with
    | none => IO.eprintln "not lower-case hex digits in pairs"; return 2
    | some b =>
      match decode b with
      | some (e, rest) => IO.println s!"{showTree e} {toHex rest}"; return 0
      | none => IO.eprintln "not a DER element"; return 1
  | ["serve"] => serve; return 0
  | _ => IO.eprintln usage; return 2
