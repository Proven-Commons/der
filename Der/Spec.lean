/-
  The statements this library is proved to meet, for a reviewer to
  approve. Each `sorry` is proved in `Der/Proofs/` under the same name, and
  `lake comparator` checks that each proof proves exactly the statement
  here.

  The definitions they use are in `Der/Spec/Defs.lean`, written from X.690,
  and the tree type is in `Der/Spec/Element.lean`. The functions they are
  about are in `Der/Basic.lean`.
-/

import Der.Spec.Defs
import Der

namespace Der.Spec

open Der

/-! ## Elements -/

/-- The writer writes `der v` for every tree. When this slice accepts
    `v`, the reader reads it back (see `decode_iff`), and it is the DER
    encoding of `v`, apart from the contents of the types this slice does
    not check. -/
theorem encode_eq (v : Element) : Der.encode v = der v := sorry

/-- `Der.valid` says whether this slice accepts an element. -/
theorem valid_iff (v : Element) : Der.valid v = true ↔ Valid v := sorry

/-- The reader accepts exactly a DER encoding of an element this slice
    accepts, followed by anything, and gives back the element and what
    follows. So it never reads past the end of the input, every element
    it gives is inside the contents of its parent, and writing back what
    it read gives the same octets. -/
theorem decode_iff (b : List UInt8) (v : Element) (rest : List UInt8) :
    Der.decode b = some (v, rest) ↔ Valid v ∧ b = der v ++ rest := sorry

/-- An input starts with the encoding of at most one element: two
    accepted elements whose encodings, as the writer writes them, start
    the same input are the same, and so is what follows them. The
    writer's encoding is `der` (`encode_eq`). With `decode_iff`, the
    reader gives one element for each input, and accepts one encoding of
    each element. -/
theorem encoding_unique (v w : Element) (r s : List UInt8) (hv : Valid v) (hw : Valid w)
    (h : Der.encode v ++ r = Der.encode w ++ s) : v = w ∧ r = s := sorry

/-- Reading what the writer wrote gives back the element and what
    follows. -/
theorem decode_encode (v : Element) (rest : List UInt8) (h : Valid v) :
    Der.decode (Der.encode v ++ rest) = some (v, rest) := sorry

/-- The whole input is one element exactly when it is a DER encoding of
    an element this slice accepts. -/
theorem decodeAll_iff (b : List UInt8) (v : Element) :
    Der.decodeAll b = some v ↔ Valid v ∧ b = der v := sorry

/-! ## Integers (8.3) -/

/-- `readInt` accepts exactly the contents octets X.690 allows for an
    integer, and gives the integer they encode. -/
theorem readInt_iff (c : List UInt8) (z : Int) :
    Der.readInt c = some z ↔ IntegerContents c ∧ integerValue c = z := sorry

/-- `writeInt` writes contents octets X.690 allows, which encode the
    integer. -/
theorem writeInt_spec (z : Int) :
    IntegerContents (Der.writeInt z) ∧ integerValue (Der.writeInt z) = z := sorry

/-- Each integer has one encoding: allowed contents octets are what
    `writeInt` writes for the integer they encode. -/
theorem writeInt_unique (c : List UInt8) (h : IntegerContents c) :
    Der.writeInt (integerValue c) = c := sorry

/-! ## Examples -/

/-- The examples of X.690: a length of 38 in the short form (8.1.3.4)
    and of 201 in the long form (8.1.3.5), the boolean TRUE as DER
    writes it (8.2.2, 11.1), and the primitive form of the VisibleString
    "Jones" (8.23.5), which DER uses. Then a tag number of 201 in the
    high form (8.1.2.4), worked by hand: the leading octet 0x5F for an
    application class primitive, then 201 = 1 × 128 + 73 as 0x81 0x49. -/
theorem x690_examples :
    Der.Spec.lengthOctets 38 = [0x26] ∧ Der.Spec.lengthOctets 201 = [0x81, 0xC9] ∧
    Der.Spec.identifier 1 false 201 = [0x5F, 0x81, 0x49] ∧
    Der.decode [0x5F, 0x81, 0x49, 0x00] = some (.prim 1 201 [], []) ∧
    Der.decode [0x01, 0x01, 0xFF] = some (.prim 0 1 [0xFF], []) ∧
    Der.decode [0x1A, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73] =
      some (.prim 0 26 [0x4A, 0x6F, 0x6E, 0x65, 0x73], []) := sorry

/-- Inputs the reader refuses, each for a rule:
    - the two constructed forms of "Jones" in 8.23.5, which DER forbids
      (10.2), the second also with the indefinite length (10.1);
    - a length in the long form below 128, and a length of 128 in the
      long form with a leading zero octet (10.1); the initial length
      octet all ones (8.1.3.5 c);
    - a tag number below 31 in the high form (8.1.2.2), and a first
      subsequent octet with bits 7 to 1 zero (8.1.2.4.2 c);
    - a boolean TRUE that is not all ones (11.1), and of two octets
      (8.2.1);
    - integers with a redundant leading octet (8.3.2) and with none
      (8.3.1), and the same for enumerated values (8.4);
    - a null with contents (8.8.2), a constructed integer (8.3.1), a
      primitive sequence (8.9.1), and the end-of-contents octets
      (8.1.5);
    - contents that run past the end of the input. -/
theorem x690_rejects :
    Der.decode [0x3A, 0x09, 0x04, 0x03, 0x4A, 0x6F, 0x6E, 0x04, 0x02, 0x65, 0x73] = none ∧
    Der.decode [0x3A, 0x80, 0x04, 0x03, 0x4A, 0x6F, 0x6E, 0x04, 0x02, 0x65, 0x73, 0x00, 0x00] =
      none ∧
    Der.decode [0x04, 0x81, 0x01, 0x00] = none ∧
    Der.decode ([0x04, 0x82, 0x00, 0x80] ++ List.replicate 128 0) = none ∧
    Der.decode [0x04, 0xFF, 0x00] = none ∧
    Der.decode [0x1F, 0x05, 0x00] = none ∧
    Der.decode [0x1F, 0x80, 0x1F, 0x00] = none ∧
    Der.decode [0x01, 0x01, 0x01] = none ∧
    Der.decode [0x01, 0x02, 0xFF, 0xFF] = none ∧
    Der.decode [0x02, 0x02, 0x00, 0x7F] = none ∧
    Der.decode [0x02, 0x02, 0xFF, 0x80] = none ∧
    Der.decode [0x02, 0x00] = none ∧
    Der.decode [0x0A, 0x02, 0x00, 0x01] = none ∧
    Der.decode [0x0A, 0x00] = none ∧
    Der.decode [0x05, 0x01, 0x00] = none ∧
    Der.decode [0x22, 0x03, 0x02, 0x01, 0x00] = none ∧
    Der.decode [0x10, 0x00] = none ∧
    Der.decode [0x00, 0x00] = none ∧
    Der.decode [0x04, 0x05, 0x00] = none := sorry

end Der.Spec
