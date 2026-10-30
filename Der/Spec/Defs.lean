/-
  The definitions the statements in `Der/Spec.lean` use, written from
  Rec. ITU-T X.690 (02/2021), the Basic and Distinguished Encoding Rules
  of ASN.1, https://www.itu.int/rec/T-REC-X.690, and from Table 1 of
  Rec. ITU-T X.680 (02/2021), the universal class tag assignments.
  Section numbers below are those of X.690 unless they name X.680.

  This file is part of the specification: a reviewer approves it with
  `Der/Spec.lean` and `Der/Spec/Element.lean`. It shares nothing with the code in
  `Der/` but the type `Der.Element`.
-/

import Der.Spec.Element

namespace Der.Spec

open Der

/-! ## Numbers written as digits -/

/-- The digits of `n` in base `b`, most significant first, with no
    leading zero: `[0]` for zero. -/
def digits (b n : Nat) : List Nat :=
  if _h : n < b ∨ b < 2 then [n] else digits b (n / b) ++ [n % b]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-! ## Identifier octets (8.1.2) -/

/-- Bits 8 to 6 of the first identifier octet: the class in bits 8 and 7,
    as Table 1 of X.690 gives it (8.1.2.2 a, 8.1.2.4.1 a), and bit 6 one
    for a constructed encoding, zero for a primitive one (8.1.2.5). -/
def classAndForm (cls : Nat) (constructed : Bool) : Nat :=
  cls * 64 + if constructed then 32 else 0

/-- The identifier octets for a tag of class `cls` and number `tag`.

    A number from 0 to 30 takes a single octet, the number in bits 5 to 1
    (8.1.2.2). A number of 31 or more takes a leading octet with bits 5
    to 1 all ones (8.1.2.4.1 c), then subsequent octets: the number in
    base 128, most significant first, seven bits to an octet, with bit 8
    one in every octet but the last (8.1.2.4.2 a and b). The first
    subsequent octet does not have bits 7 to 1 all zero (8.1.2.4.2 c), so
    the digits have no leading zero. -/
def identifier (cls : Nat) (constructed : Bool) (tag : Nat) : List UInt8 :=
  if tag ≤ 30 then [(classAndForm cls constructed + tag).toUInt8]
  else
    let ds := digits 128 tag
    (classAndForm cls constructed + 31).toUInt8 ::
      ds.mapIdx fun i d => (if i + 1 < ds.length then d + 128 else d).toUInt8

/-! ## Length octets (8.1.3, 10.1) -/

/-- The length octets for `n` contents octets, as DER writes them: "The
    definite form of length encoding shall be used, encoded in the
    minimum number of octets" (10.1).

    Up to 127, the short form: one octet, bit 8 zero, the length in bits
    7 to 1 (8.1.3.4). Above 127, the long form (8.1.3.5): an initial
    octet with bit 8 one and the number of subsequent octets in bits 7
    to 1, then the length in base 256, most significant first, in as few
    octets as it takes. -/
def lengthOctets (n : Nat) : List UInt8 :=
  if n ≤ 127 then [n.toUInt8]
  else
    let ds := digits 256 n
    (128 + ds.length).toUInt8 :: ds.map Nat.toUInt8

/-! ## Encodings (8.1.1) -/

mutual
/-- The encoding of an element: identifier octets, length octets and
    contents octets (8.1.1.1). For an element this slice accepts, it is
    the DER encoding, apart from the contents of the types this slice
    does not check. With the definite form there are no
    end-of-contents octets (8.1.5). The contents octets of a constructed
    element are the encodings of its elements, one after another
    (8.1.1.1 c, 3.2, 8.9.2, 8.10.2). -/
def der : Element → List UInt8
  | .prim cls tag c => identifier cls false tag ++ lengthOctets c.length ++ c
  | .cons cls tag cs => identifier cls true tag ++ lengthOctets (derList cs).length ++ derList cs

/-- The encodings of elements, one after another. -/
def derList : List Element → List UInt8
  | [] => []
  | e :: es => der e ++ derList es
end

/-! ## Integers (8.3) -/

/-- Contents octets X.690 allows for an integer: one or more octets
    (8.3.1), and when there are two or more, the bits of the first octet
    and bit 8 of the second are not all ones and not all zero (8.3.2). -/
def IntegerContents (c : List UInt8) : Prop :=
  c ≠ [] ∧
    ∀ a b rest, c = a :: b :: rest →
      ¬ (a.toNat = 255 ∧ 128 ≤ b.toNat) ∧ ¬ (a.toNat = 0 ∧ b.toNat < 128)

/-- The integer that contents octets encode, a two's complement binary
    number (8.3.3 and its note): the octets read as one unsigned number,
    most significant first, less 2 to the power of 8 times the number of
    octets when bit 8 of the first octet is one. -/
def integerValue (c : List UInt8) : Int :=
  let u : Nat := c.foldl (fun n o => n * 256 + o.toNat) 0
  match c with
  | a :: _ => if 128 ≤ a.toNat then (u : Int) - 2 ^ (8 * c.length) else u
  | [] => 0

/-! ## What DER allows (8, 10, 11) -/

/-- The universal tags of types that X.690 encodes as constructed: 8,
    external and instance-of (8.18.1, 8.16.1); 11, embedded-pdv (8.17.1);
    16, sequence and sequence-of (8.9.1, 8.10.1); 17, set and set-of
    (8.11.1, 8.12.1); and 29, the unrestricted character string (8.24.1).
    X.680 gives these numbers in 37.2, 36.2, Table 1 and 44.2. -/
def ConstructedUniversal (tag : Nat) : Prop :=
  tag = 8 ∨ tag = 11 ∨ tag = 16 ∨ tag = 17 ∨ tag = 29

/-- The universal tags that X.680's Table 1 assigns to no type: 15,
    "Reserved for future editions", and 37 on, "Reserved for addenda".
    This slice accepts both forms for them. -/
def ReservedUniversal (tag : Nat) : Prop := tag = 15 ∨ 37 ≤ tag

/-- What this slice requires of a primitive element of class `cls`,
    number `tag` and contents `c`. Outside the universal class, nothing.
    In it:
    - number 0 is "Reserved for use by the encoding rules" (X.680 Table
      1); DER uses it for nothing, since end-of-contents octets go with
      the indefinite form only (8.1.5, 10.1);
    - the five numbers of `ConstructedUniversal` are not primitive;
    - a boolean has one contents octet (8.2.1), 0 for false (8.2.2) and
      all ones for true (11.1);
    - an integer has the contents `IntegerContents` describes (8.3), and
      so has an enumerated value, which is encoded as its integer (8.4);
    - a null has no contents octets (8.8.2).

    Every other universal type is primitive in DER: by 8.2.1, 8.3.1,
    8.4, 8.5.1, 8.8.1, 8.19.1, 8.20.1, 8.21.1, 8.22.1 and 8.26, and for
    bit strings, octet strings and the restricted character strings,
    with the useful types defined from them (8.25), by 10.2. This slice
    checks the contents of no other type: not those of 8.5 and 11.3
    (REAL), 8.6.2 and 11.2.1 (BIT STRING), 8.19.2 (OBJECT IDENTIFIER),
    8.20.2 (RELATIVE-OID), 8.21.2 and 8.22.2 (the IRI types), 8.23.7,
    8.23.8, 8.23.10 and 11.4 (strings), 11.7 and 11.8 (the useful time
    types), or 8.26 and 11.9 (TIME and its subtypes). -/
def PrimitiveOk (cls tag : Nat) (c : List UInt8) : Prop :=
  cls = 0 →
    tag ≠ 0 ∧ ¬ ConstructedUniversal tag ∧
      (tag = 1 → c = [0] ∨ c = [255]) ∧
      (tag = 2 ∨ tag = 10 → IntegerContents c) ∧
      (tag = 5 → c = [])

/-- What this slice requires of the tag of a constructed element: in the
    universal class, one of the five numbers of `ConstructedUniversal`,
    or a reserved number. Every other universal type is primitive in DER
    (see `PrimitiveOk`). The elements inside are not checked against the
    type: not the components of 8.16 to 8.18 and 8.24 for tags 8, 11
    and 29, nor the order of a set's components (10.3, 11.6), which
    depends on whether it is a SET or a SET OF. -/
def ConstructedOk (cls tag : Nat) : Prop :=
  cls = 0 → ConstructedUniversal tag ∨ ReservedUniversal tag

mutual
/-- An element DER can encode and this slice accepts. Its class is one of
    the four of Table 1. Its length fits the long form, whose initial
    octet may not be all ones (8.1.3.5 c), so at most 126 subsequent
    octets. And its tag and contents are as `PrimitiveOk` and
    `ConstructedOk` say. -/
def Valid : Element → Prop
  | .prim cls tag c => cls < 4 ∧ PrimitiveOk cls tag c ∧ c.length < 256 ^ 126
  | .cons cls tag cs =>
    cls < 4 ∧ ConstructedOk cls tag ∧ ValidList cs ∧ (derList cs).length < 256 ^ 126

/-- Each element of a list is `Valid`. -/
def ValidList : List Element → Prop
  | [] => True
  | e :: es => Valid e ∧ ValidList es
end

end Der.Spec
