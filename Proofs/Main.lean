/-
  The statements of `Spec.lean`, each proved from the lemmas in the
  other files of `Proofs/`. `lake comparator` checks that each theorem
  here is exactly the one in `Spec.lean`.
-/

import Proofs.Element
import Proofs.Int

namespace Spec

open Der

theorem encode_eq (v : Element) : Der.encode v = der v :=
  DerProofs.encode_eq' v

theorem valid_iff (v : Element) : Der.valid v = true ↔ Valid v :=
  DerProofs.valid_iff' v

theorem decode_iff (b : List UInt8) (v : Element) (rest : List UInt8) :
    Der.decode b = some (v, rest) ↔ Valid v ∧ b = der v ++ rest :=
  DerProofs.decode_iff' b v rest

theorem encoding_unique (v w : Element) (r s : List UInt8) (hv : Valid v) (hw : Valid w)
    (h : Der.encode v ++ r = Der.encode w ++ s) : v = w ∧ r = s := by
  rw [DerProofs.encode_eq' v, DerProofs.encode_eq' w] at h
  exact DerProofs.encoding_unique' v w r s hv hw h

theorem decode_encode (v : Element) (rest : List UInt8) (h : Valid v) :
    Der.decode (Der.encode v ++ rest) = some (v, rest) :=
  DerProofs.decode_encode' v rest h

theorem decodeAll_iff (b : List UInt8) (v : Element) :
    Der.decodeAll b = some v ↔ Valid v ∧ b = der v :=
  DerProofs.decodeAll_iff' b v

theorem readInt_iff (c : List UInt8) (z : Int) :
    Der.readInt c = some z ↔ IntegerContents c ∧ integerValue c = z :=
  DerProofs.readInt_iff' c z

theorem writeInt_spec (z : Int) :
    IntegerContents (Der.writeInt z) ∧ integerValue (Der.writeInt z) = z :=
  DerProofs.writeInt_spec' z

theorem writeInt_unique (c : List UInt8) (h : IntegerContents c) :
    Der.writeInt (integerValue c) = c :=
  DerProofs.writeInt_unique' c h

theorem x690_examples :
    Spec.lengthOctets 38 = [0x26] ∧ Spec.lengthOctets 201 = [0x81, 0xC9] ∧
    Spec.identifier 1 false 201 = [0x5F, 0x81, 0x49] ∧
    Der.decode [0x5F, 0x81, 0x49, 0x00] = some (.prim 1 201 [], []) ∧
    Der.decode [0x01, 0x01, 0xFF] = some (.prim 0 1 [0xFF], []) ∧
    Der.decode [0x1A, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73] =
      some (.prim 0 26 [0x4A, 0x6F, 0x6E, 0x65, 0x73], []) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [DerProofs.lengthOctets_short 38 (by omega)]
    rfl
  · rw [DerProofs.lengthOctets_long 201 (by omega), DerProofs.digits_of_lt (by omega)]
    rfl
  · rw [DerProofs.identifier_high 1 false 201 (by omega),
      DerProofs.digits_of_ge (by omega) (by omega), DerProofs.digits_of_lt (by omega)]
    rfl

set_option maxRecDepth 100000 in
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
    Der.decode [0x04, 0x05, 0x00] = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

end Spec
