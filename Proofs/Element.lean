/-
  Elements: the writer writes `Spec.der`, and the reader accepts exactly
  an encoding of an element this slice accepts, followed by anything.
-/

import Proofs.Header

namespace DerProofs

open Der

theorem identifier_ne_nil (cls : Nat) (c : Bool) (tag : Nat) :
    1 ≤ (Spec.identifier cls c tag).length := by
  by_cases h : tag ≤ 30
  · rw [identifier_low _ _ _ h]; simp
  · rw [identifier_high _ _ _ (by omega)]; simp

theorem lengthOctets_ne_nil (n : Nat) : 1 ≤ (Spec.lengthOctets n).length := by
  by_cases h : n ≤ 127
  · rw [lengthOctets_short _ h]; simp
  · rw [lengthOctets_long _ h]; simp

theorem der_prim (cls tag : Nat) (c : List UInt8) :
    Spec.der (.prim cls tag c) = Spec.identifier cls false tag ++ Spec.lengthOctets c.length ++ c := by
  simp [Spec.der]

theorem der_cons (cls tag : Nat) (cs : List Element) :
    Spec.der (.cons cls tag cs) =
      Spec.identifier cls true tag ++ Spec.lengthOctets (Spec.derList cs).length ++ Spec.derList cs := by
  simp [Spec.der]

theorem derList_nil : Spec.derList [] = [] := by simp [Spec.derList]

theorem derList_cons (v : Element) (vs : List Element) :
    Spec.derList (v :: vs) = Spec.der v ++ Spec.derList vs := by
  simp [Spec.derList]

theorem valid_prim (cls tag : Nat) (c : List UInt8) :
    Spec.Valid (.prim cls tag c) ↔ cls < 4 ∧ Spec.PrimitiveOk cls tag c ∧ c.length < 256 ^ 126 := by
  simp only [Spec.Valid]

theorem valid_cons (cls tag : Nat) (cs : List Element) :
    Spec.Valid (.cons cls tag cs) ↔
      cls < 4 ∧ Spec.ConstructedOk cls tag ∧ Spec.ValidList cs ∧ (Spec.derList cs).length < 256 ^ 126 := by
  simp only [Spec.Valid]

theorem validList_cons (v : Element) (vs : List Element) :
    Spec.ValidList (v :: vs) ↔ Spec.Valid v ∧ Spec.ValidList vs := by
  simp only [Spec.ValidList]

theorem der_length_ge (v : Element) : 2 ≤ (Spec.der v).length := by
  cases v with
  | prim cls tag c =>
    rw [der_prim]
    have := identifier_ne_nil cls false tag
    have := lengthOctets_ne_nil c.length
    simp only [List.length_append]
    omega
  | cons cls tag cs =>
    rw [der_cons]
    have := identifier_ne_nil cls true tag
    have := lengthOctets_ne_nil (Spec.derList cs).length
    simp only [List.length_append]
    omega

mutual
theorem encode_eq' : ∀ v : Element, Spec.Valid v → encode v = Spec.der v
  | .prim cls tag c, h => by
    rw [valid_prim] at h
    rw [der_prim]
    simp only [encode, identOctets_eq _ _ _ h.1, lengthOctets_eq]
  | .cons cls tag cs, h => by
    rw [valid_cons] at h
    rw [der_cons]
    simp only [encode, identOctets_eq _ _ _ h.1, lengthOctets_eq, encodeList_eq cs h.2.2.1]
theorem encodeList_eq : ∀ vs : List Element, Spec.ValidList vs → encodeList vs = Spec.derList vs
  | [], _ => by simp [encodeList, derList_nil]
  | v :: vs, h => by
    rw [validList_cons] at h
    rw [derList_cons]
    simp only [encodeList, encode_eq' v h.1, encodeList_eq vs h.2]
end

theorem readElements_zero (f : Nat) (b : List UInt8) : readElements f 0 b = some ([], b) := by
  cases f <;> simp [readElements]

mutual
theorem readElement_der : ∀ (v : Element) (f lim : Nat) (rest : List UInt8), Spec.Valid v →
    (Spec.der v).length ≤ f + 1 → (Spec.der v).length ≤ lim →
    readElement f lim (Spec.der v ++ rest) = some (v, (Spec.der v).length, rest)
  | .prim cls tag c, f, lim, rest, hv, hf, hl => by
    rw [valid_prim] at hv
    obtain ⟨hcls, hok, hlen⟩ := hv
    have h1 := identifier_ne_nil cls false tag
    have h2 := lengthOctets_ne_nil c.length
    rw [der_prim] at hf hl ⊢
    simp only [List.length_append] at hf hl ⊢
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [List.append_assoc, List.append_assoc]
    unfold readElement
    rw [readIdentifier_identifier _ _ _ _ hcls]
    dsimp only
    rw [readLength_lengthOctets _ _ hlen]
    dsimp only
    have ht : (c ++ rest).take c.length = c := List.take_left' rfl
    have hd : (c ++ rest).drop c.length = rest := List.drop_left' rfl
    rw [ht, hd, ite_eq_right (show ¬ lim < _ by omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, (primOk_iff cls tag c).mpr hok, and_self]
  | .cons cls tag cs, f, lim, rest, hv, hf, hl => by
    rw [valid_cons] at hv
    obtain ⟨hcls, hok, hcs, hlen⟩ := hv
    have h1 := identifier_ne_nil cls true tag
    have h2 := lengthOctets_ne_nil (Spec.derList cs).length
    rw [der_cons] at hf hl ⊢
    simp only [List.length_append] at hf hl ⊢
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [List.append_assoc, List.append_assoc]
    unfold readElement
    rw [readIdentifier_identifier _ _ _ _ hcls]
    dsimp only
    rw [readLength_lengthOctets _ _ hlen]
    dsimp only
    rw [ite_eq_right (show ¬ lim < _ by omega)]
    rw [readElements_der cs f' rest hcs (by omega)]
    simp only [↓reduceIte, (consOk_iff cls tag).mpr hok]
theorem readElements_der : ∀ (vs : List Element) (f : Nat) (rest : List UInt8), Spec.ValidList vs →
    (Spec.derList vs).length ≤ f →
    readElements f (Spec.derList vs).length (Spec.derList vs ++ rest) = some (vs, rest)
  | [], f, rest, _, _ => by
    rw [derList_nil]
    exact readElements_zero f rest
  | v :: vs, f, rest, hv, hf => by
    rw [validList_cons] at hv
    have hd := der_length_ge v
    rw [derList_cons] at hf ⊢
    simp only [List.length_append] at hf ⊢
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨L, hL⟩ : ∃ L, (Spec.der v).length + (Spec.derList vs).length = L + 1 :=
      ⟨(Spec.der v).length + (Spec.derList vs).length - 1, by omega⟩
    rw [hL, List.append_assoc]
    unfold readElements
    rw [readElement_der v f' (L + 1) _ hv.1 (by omega) (by omega)]
    dsimp only
    rw [show L + 1 - (Spec.der v).length = (Spec.derList vs).length by omega,
      readElements_der vs f' rest hv.2 (by omega)]
end

theorem read_sound (f : Nat) :
    (∀ lim b v n rest, readElement f lim b = some (v, n, rest) →
      Spec.Valid v ∧ b = Spec.der v ++ rest ∧ n = (Spec.der v).length ∧ n ≤ lim) ∧
    (∀ lim b vs rest, readElements f lim b = some (vs, rest) →
      Spec.ValidList vs ∧ b = Spec.derList vs ++ rest ∧ (Spec.derList vs).length = lim) := by
  induction f with
  | zero =>
    refine ⟨fun lim b v n rest h => by simp [readElement] at h, ?_⟩
    intro lim b vs rest h
    cases lim with
    | zero =>
      rw [readElements_zero] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp [Spec.ValidList], by rw [derList_nil]; rfl, by rw [derList_nil]; rfl⟩
    | succ l => simp [readElements] at h
  | succ f ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · intro lim b v n rest h
      unfold readElement at h
      cases hid : readIdentifier b with
      | none => rw [hid] at h; exact absurd h (Option.some_ne_none _).symm
      | some p =>
        obtain ⟨cls, cons, tag, n1, b1⟩ := p
        rw [hid] at h
        dsimp only at h
        obtain ⟨hcls, hb, hn1⟩ := readIdentifier_sound hid
        cases hlr : readLength b1 with
        | none => rw [hlr] at h; exact absurd h (Option.some_ne_none _).symm
        | some q =>
          obtain ⟨len, n2, b2⟩ := q
          rw [hlr] at h
          dsimp only at h
          obtain ⟨hlen, hb1, hn2⟩ := readLength_sound hlr
          by_cases hlim : lim < n1 + n2 + len
          · rw [ite_eq_left hlim] at h; exact absurd h (Option.some_ne_none _).symm
          · rw [ite_eq_right hlim] at h
            cases cons with
            | true =>
              simp only [↓reduceIte] at h
              by_cases hok : consOk cls tag = true
              · rw [ite_eq_left hok] at h
                cases hrs : readElements f len b2 with
                | none => rw [hrs] at h; exact absurd h (Option.some_ne_none _).symm
                | some r =>
                  obtain ⟨cs, b3⟩ := r
                  rw [hrs] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  obtain ⟨hcs, hb2, hl⟩ := ih2 _ _ _ _ hrs
                  subst hl
                  refine ⟨?_, ?_, ?_, by omega⟩
                  · rw [valid_cons]
                    exact ⟨hcls, (consOk_iff cls tag).mp hok, hcs, hlen⟩
                  · rw [der_cons, hb, hb1, hb2]
                    simp only [List.append_assoc]
                  · rw [der_cons, hn1, hn2]
                    simp only [List.length_append]
              · rw [ite_eq_right hok] at h; exact absurd h (Option.some_ne_none _).symm
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h
              by_cases hc : (b2.take len).length = len ∧ primOk cls tag (b2.take len) = true
              · rw [ite_eq_left hc] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                refine ⟨?_, ?_, ?_, by omega⟩
                · rw [valid_prim]
                  refine ⟨hcls, (primOk_iff _ _ _).mp hc.2, ?_⟩
                  rw [hc.1]; exact hlen
                · rw [der_prim, hb, hb1, hc.1]
                  simp only [List.append_assoc, List.take_append_drop]
                · rw [der_prim, hn1, hn2]
                  simp only [List.length_append]
                  rw [hc.1]
              · rw [ite_eq_right hc] at h; exact absurd h (Option.some_ne_none _).symm
    · intro lim b vs rest h
      cases lim with
      | zero =>
        rw [readElements_zero] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp [Spec.ValidList], by rw [derList_nil]; rfl, by rw [derList_nil]; rfl⟩
      | succ l =>
        unfold readElements at h
        cases he : readElement f (l + 1) b with
        | none => rw [he] at h; exact absurd h (Option.some_ne_none _).symm
        | some p =>
          obtain ⟨e, n, b'⟩ := p
          rw [he] at h
          dsimp only at h
          cases hrs : readElements f (l + 1 - n) b' with
          | none => rw [hrs] at h; exact absurd h (Option.some_ne_none _).symm
          | some r =>
            obtain ⟨es, b''⟩ := r
            rw [hrs] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hve, hb, hn, hnl⟩ := ih1 _ _ _ _ _ he
            obtain ⟨hves, hb', hl⟩ := ih2 _ _ _ _ hrs
            refine ⟨(validList_cons _ _).mpr ⟨hve, hves⟩, ?_, ?_⟩
            · rw [derList_cons, hb, hb', List.append_assoc]
            · rw [derList_cons, List.length_append, hl]
              omega

theorem decode_iff' (b : List UInt8) (v : Element) (rest : List UInt8) :
    decode b = some (v, rest) ↔ Spec.Valid v ∧ b = Spec.der v ++ rest := by
  constructor
  · intro h
    unfold decode at h
    cases he : readElement b.length b.length b with
    | none => rw [he] at h; exact absurd h (Option.some_ne_none _).symm
    | some p =>
      obtain ⟨e, n, r⟩ := p
      rw [he] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hv, hb, -, -⟩ := (read_sound _).1 _ _ _ _ _ he
      exact ⟨hv, hb⟩
  · rintro ⟨hv, rfl⟩
    unfold decode
    rw [readElement_der v _ _ rest hv (by simp; omega) (by simp)]

theorem encoding_unique' (v w : Element) (r s : List UInt8) (hv : Spec.Valid v) (hw : Spec.Valid w)
    (h : Spec.der v ++ r = Spec.der w ++ s) : v = w ∧ r = s := by
  have h1 := (decode_iff' (Spec.der v ++ r) v r).mpr ⟨hv, rfl⟩
  have h2 := (decode_iff' (Spec.der v ++ r) w s).mpr ⟨hw, h⟩
  rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2

theorem decode_encode' (v : Element) (rest : List UInt8) (h : Spec.Valid v) :
    decode (encode v ++ rest) = some (v, rest) := by
  rw [encode_eq' v h]
  exact (decode_iff' _ _ _).mpr ⟨h, rfl⟩

theorem decodeAll_iff' (b : List UInt8) (v : Element) :
    decodeAll b = some v ↔ Spec.Valid v ∧ b = Spec.der v := by
  unfold decodeAll
  constructor
  · intro h
    split at h
    · rename_i e he
      simp only [Option.some.injEq] at h
      subst h
      have := (decode_iff' b e []).mp he
      simpa using this
    · exact absurd h (Option.some_ne_none _).symm
  · rintro ⟨hv, rfl⟩
    have := (decode_iff' (Spec.der v ++ []) v []).mpr ⟨hv, rfl⟩
    rw [List.append_nil] at this
    rw [this]

end DerProofs
