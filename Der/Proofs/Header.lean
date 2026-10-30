/-
  Identifier octets and length octets: the writer gives what X.690 says,
  and the reader accepts exactly that. Then what each node may be: the
  code's checks against the specification's.
-/

import Der.Proofs.Digits

namespace DerProofs

open Der

theorem toNat_toUInt8 {x : Nat} (h : x < 256) : x.toUInt8.toNat = x := by
  simp; omega

def sub (ds : List Nat) : List UInt8 :=
  ds.dropLast.map (fun d => (d + 128).toUInt8) ++ [(ds.getLastD 0).toUInt8]

theorem sub_cons (d : Nat) (ds : List Nat) (h : ds ≠ []) :
    sub (d :: ds) = (d + 128).toUInt8 :: sub ds := by
  unfold sub
  rw [List.dropLast_cons_of_ne_nil h]
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [List.getLastD_eq_getLast?, List.getLast?_cons]

theorem splitTag_cons (b : UInt8) (bs : List UInt8) (acc : List Nat) :
    splitTag (b :: bs) acc =
      if b.toNat < 128 then some ((b.toNat :: acc).reverse, bs)
      else splitTag bs ((b.toNat - 128) :: acc) := rfl

theorem splitTag_sub (ds : List Nat) (hne : ds ≠ []) (hlt : ∀ d ∈ ds, d < 128)
    (rest : List UInt8) (acc : List Nat) :
    splitTag (sub ds ++ rest) acc = some (acc.reverse ++ ds, rest) := by
  induction ds generalizing acc with
  | nil => exact absurd rfl hne
  | cons d ds ih =>
    have hd : d < 128 := hlt d (by simp)
    by_cases hds : ds = []
    · subst hds
      have : sub [d] = [d.toUInt8] := rfl
      rw [this, List.singleton_append, splitTag_cons, toNat_toUInt8 (show d < 256 by omega)]
      simp only [hd, ↓reduceIte, List.reverse_cons]
    · rw [sub_cons d ds hds, List.cons_append, splitTag_cons,
        toNat_toUInt8 (show d + 128 < 256 by omega)]
      simp only [show ¬ (d + 128 < 128) by omega, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih hds (fun x hx => hlt x (by simp [hx]))]
      simp

theorem two_pow_seven : (2 : Nat) ^ 7 = 128 := rfl

theorem sub_length (ds : List Nat) (h : ds ≠ []) : (sub ds).length = ds.length := by
  unfold sub
  simp only [List.length_append, List.length_map, List.length_dropLast, List.length_singleton]
  have := List.length_pos_iff.mpr h
  omega

theorem mapIdx_eq_sub (ds : List Nat) (h : ds ≠ []) :
    ds.mapIdx (fun i d => (if i + 1 < ds.length then d + 128 else d).toUInt8) = sub ds := by
  rw [← List.dropLast_concat_getLast h]
  generalize ds.dropLast = init
  generalize ds.getLast h = last
  rw [List.mapIdx_append]
  simp only [List.length_append, List.length_singleton, List.mapIdx_singleton, Nat.zero_add,
    Nat.lt_irrefl, ↓reduceIte, sub, List.dropLast_concat, List.getLastD_concat]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_mapIdx, List.getElem_map]
  have : i + 1 < init.length + 1 := by simp at h1; omega
  simp only [this, ↓reduceIte]

theorem identifier_high (cls : Nat) (c : Bool) (tag : Nat) (h : 31 ≤ tag) :
    Der.Spec.identifier cls c tag =
      (Der.Spec.classAndForm cls c + 31).toUInt8 :: sub (Der.Spec.digits 128 tag) := by
  unfold Der.Spec.identifier
  simp only [show ¬ tag ≤ 30 by omega, ↓reduceIte]
  rw [mapIdx_eq_sub _ (digits_ne_nil _ _)]

theorem identifier_low (cls : Nat) (c : Bool) (tag : Nat) (h : tag ≤ 30) :
    Der.Spec.identifier cls c tag = [(Der.Spec.classAndForm cls c + tag).toUInt8] := by
  unfold Der.Spec.identifier
  simp only [h, ↓reduceIte]

theorem classAndForm_eq (cls : Nat) (c : Bool) :
    Der.Spec.classAndForm cls c = cls * 64 + if c then 32 else 0 := rfl

theorem readIdentifier_cons (b : UInt8) (bs : List UInt8) :
    readIdentifier (b :: bs) =
      if b.toNat % 32 < 31 then some (b.toNat / 64, b.toNat / 32 % 2 == 1, b.toNat % 32, 1, bs)
      else
        match splitTag bs [] with
        | some (d :: ds, rest) =>
          if d = 0 then none
          else
            if ofDigits 7 (d :: ds) < 31 then none
            else some (b.toNat / 64, b.toNat / 32 % 2 == 1, ofDigits 7 (d :: ds), ds.length + 2, rest)
        | _ => none := rfl

theorem lead_parts (cls : Nat) (c : Bool) (t : Nat) (hcls : cls < 4) (ht : t ≤ 31) :
    (Der.Spec.classAndForm cls c + t) % 32 = t ∧ (Der.Spec.classAndForm cls c + t) / 64 = cls ∧
    ((Der.Spec.classAndForm cls c + t) / 32 % 2 == 1) = c ∧ Der.Spec.classAndForm cls c + t < 256 := by
  rw [classAndForm_eq]
  cases c <;> simp <;> omega

theorem readIdentifier_identifier (cls : Nat) (c : Bool) (tag : Nat) (rest : List UInt8)
    (hcls : cls < 4) :
    readIdentifier (Der.Spec.identifier cls c tag ++ rest) =
      some (cls, c, tag, (Der.Spec.identifier cls c tag).length, rest) := by
  by_cases ht : tag ≤ 30
  · obtain ⟨h1, h2, h3, h4⟩ := lead_parts cls c tag hcls (by omega)
    rw [identifier_low cls c tag ht, List.singleton_append, readIdentifier_cons,
      toNat_toUInt8 h4, h1, h2, h3]
    simp only [show tag < 31 by omega, ↓reduceIte, List.length_singleton]
  · obtain ⟨h1, h2, h3, h4⟩ := lead_parts cls c 31 hcls (by omega)
    rw [identifier_high cls c tag (by omega), List.cons_append, readIdentifier_cons,
      toNat_toUInt8 h4, h1, h2, h3]
    have hne := digits_ne_nil 128 tag
    have hlt := digits_lt (by omega : 2 ≤ 128) tag
    obtain ⟨d, ds, he, hd⟩ := digits_head (by omega : 2 ≤ 128) (show tag ≠ 0 by omega)
    rw [splitTag_sub _ hne hlt rest [], he]
    have hv : ofDigits 7 (d :: ds) = tag := by
      rw [ofDigits_eq, ← he, ← two_pow_seven, digitsVal_digits 7 (by omega)]
    simp only [Nat.lt_irrefl, ↓reduceIte, List.reverse_nil, List.nil_append, hd, hv,
      show ¬ tag < 31 by omega, List.length_cons]
    rw [sub_length _ (by simp)]
    simp

theorem splitTag_sound (bs : List UInt8) (acc out : List Nat) (rest : List UInt8)
    (h : splitTag bs acc = some (out, rest)) :
    ∃ ds, ds ≠ [] ∧ (∀ d ∈ ds, d < 128) ∧ bs = sub ds ++ rest ∧ out = acc.reverse ++ ds := by
  induction bs generalizing acc with
  | nil => simp [splitTag] at h
  | cons b bs ih =>
    have hb := UInt8.toNat_lt b
    rw [splitTag_cons] at h
    by_cases hlt : b.toNat < 128
    · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[b.toNat], by simp, by simpa using hlt, ?_, by simp⟩
      show b :: bs = [b.toNat.toUInt8] ++ bs
      simp
    · simp only [hlt, ↓reduceIte] at h
      obtain ⟨ds, hne, hlt', rfl, rfl⟩ := ih _ h
      refine ⟨(b.toNat - 128) :: ds, by simp, ?_, ?_, by simp⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · rw [hx]; omega
        · exact hlt' x hx
      · have e : (b.toNat - 128 + 128).toUInt8 = b := by
          apply UInt8.toNat_inj.mp
          rw [toNat_toUInt8 (by omega)]
          omega
        rw [sub_cons _ _ hne, List.cons_append, e]

theorem first_octet (b : UInt8) (t : Nat) (ht : t = b.toNat % 32) :
    (Der.Spec.classAndForm (b.toNat / 64) (b.toNat / 32 % 2 == 1) + t).toUInt8 = b := by
  subst ht
  apply UInt8.toNat_inj.mp
  have hb := UInt8.toNat_lt b
  rw [classAndForm_eq, toNat_toUInt8]
  · by_cases h : b.toNat / 32 % 2 = 1 <;> simp [h] <;> omega
  · by_cases h : b.toNat / 32 % 2 = 1 <;> simp [h] <;> omega

theorem readIdentifier_sound {b : List UInt8} {cls : Nat} {c : Bool} {tag n : Nat}
    {rest : List UInt8} (h : readIdentifier b = some (cls, c, tag, n, rest)) :
    cls < 4 ∧ b = Der.Spec.identifier cls c tag ++ rest ∧ n = (Der.Spec.identifier cls c tag).length := by
  cases b with
  | nil => simp [readIdentifier] at h
  | cons x bs =>
    have hx := UInt8.toNat_lt x
    rw [readIdentifier_cons] at h
    by_cases hlow : x.toNat % 32 < 31
    · simp only [hlow, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      rw [identifier_low _ _ _ (by omega), first_octet x _ rfl]
      exact ⟨by omega, rfl, rfl⟩
    · simp only [hlow, ↓reduceIte] at h
      split at h
      · rename_i d ds rest' hs
        by_cases hd : d = 0
        · simp [hd] at h
        · by_cases ht : ofDigits 7 (d :: ds) < 31
          · simp [hd, ht] at h
          · simp only [hd, ht, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
            obtain ⟨ds0, hne, hlt, hbs, hout⟩ := splitTag_sound bs [] _ _ hs
            simp only [List.reverse_nil, List.nil_append] at hout
            subst hout
            have hdig : Der.Spec.digits 128 (ofDigits 7 (d :: ds)) = d :: ds := by
              rw [ofDigits_eq, ← two_pow_seven]
              exact digits_digitsVal 7 (by omega) _ (by simp) (by rwa [two_pow_seven])
                (Or.inl (by simpa using hd))
            refine ⟨by omega, ?_, ?_⟩
            · rw [identifier_high _ _ _ (by omega), hdig, hbs, List.cons_append,
                first_octet x 31 (by omega)]
            · rw [identifier_high _ _ _ (by omega), hdig, List.length_cons,
                sub_length _ (by simp)]
              simp
      · simp at h

theorem two_pow_eight : (2 : Nat) ^ 8 = 256 := rfl

set_option exponentiation.threshold 1024 in
theorem bound_eq : (2 : Nat) ^ (8 * 126) = 256 ^ 126 := by
  rw [Nat.pow_mul]

theorem digits256_length_le (n : Nat) : (Der.Spec.digits 256 n).length ≤ 126 ↔ n < 256 ^ 126 := by
  rw [← two_pow_eight, digits_length_le 8 (by omega) n 126 (by omega), two_pow_eight, bound_eq]

theorem le_bound : 256 ≤ (256 : Nat) ^ 126 := by
  have := Nat.pow_le_pow_right (show 0 < 256 by omega) (show 1 ≤ 126 by omega)
  rwa [Nat.pow_one] at this

theorem lengthOctets_eq (n : Nat) : lengthOctets n = Der.Spec.lengthOctets n := by
  unfold lengthOctets Der.Spec.lengthOctets
  by_cases h : n < 128
  · simp only [h, ↓reduceIte, show n ≤ 127 by omega]
  · simp only [h, ↓reduceIte, show ¬ n ≤ 127 by omega]
    rw [toDigits_eq 8 (by omega), two_pow_eight]

theorem lengthOctets_short (n : Nat) (h : n ≤ 127) : Der.Spec.lengthOctets n = [n.toUInt8] := by
  unfold Der.Spec.lengthOctets
  simp only [h, ↓reduceIte]

theorem lengthOctets_long (n : Nat) (h : ¬ n ≤ 127) :
    Der.Spec.lengthOctets n =
      (128 + (Der.Spec.digits 256 n).length).toUInt8 :: (Der.Spec.digits 256 n).map Nat.toUInt8 := by
  unfold Der.Spec.lengthOctets
  simp only [h, ↓reduceIte]

theorem readLength_cons (b : UInt8) (bs : List UInt8) :
    readLength (b :: bs) =
      if b.toNat < 128 then some (b.toNat, 1, bs)
      else if b.toNat - 128 = 0 ∨ b.toNat - 128 = 127 then none
      else readLong (b.toNat - 128) bs := rfl

theorem readLong_eq (k : Nat) (bs : List UInt8) :
    readLong k bs =
      if (bs.take k).length < k ∨ (bs.take k).head? = some 0 then none
      else
        if ofDigits 8 ((bs.take k).map UInt8.toNat) < 128 then none
        else some (ofDigits 8 ((bs.take k).map UInt8.toNat), k + 1, bs.drop k) := rfl

theorem map_toNat_toUInt8 (ds : List Nat) (h : ∀ d ∈ ds, d < 256) :
    (ds.map Nat.toUInt8).map UInt8.toNat = ds := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id ds]
  apply List.map_congr_left
  intro x hx
  exact toNat_toUInt8 (h x hx)

theorem readLength_lengthOctets (n : Nat) (rest : List UInt8) (h : n < 256 ^ 126) :
    readLength (Der.Spec.lengthOctets n ++ rest) = some (n, (Der.Spec.lengthOctets n).length, rest) := by
  by_cases hs : n ≤ 127
  · rw [lengthOctets_short n hs, List.singleton_append, readLength_cons,
      toNat_toUInt8 (show n < 256 by omega)]
    simp only [show n < 128 by omega, ↓reduceIte, List.length_singleton]
  · rw [lengthOctets_long n hs, List.cons_append, readLength_cons]
    have hk := (digits256_length_le n).mpr h
    have hne := digits_ne_nil 256 n
    have hk0 := List.length_pos_iff.mpr hne
    have hlt := digits_lt (by omega : 2 ≤ 256) n
    obtain ⟨d, ds', he, hd⟩ := digits_head (by omega : 2 ≤ 256) (show n ≠ 0 by omega)
    have hv : ofDigits 8 (((Der.Spec.digits 256 n).map Nat.toUInt8).map UInt8.toNat) = n := by
      rw [map_toNat_toUInt8 _ hlt, ofDigits_eq, ← two_pow_eight, digitsVal_digits 8 (by omega)]
    generalize hds : Der.Spec.digits 256 n = ds at hk hne hk0 hlt he hv
    subst he
    rw [toNat_toUInt8 (show 128 + (d :: ds').length < 256 by omega)]
    have htake : ((d :: ds').map Nat.toUInt8 ++ rest).take (d :: ds').length =
        (d :: ds').map Nat.toUInt8 := List.take_left' (by simp)
    have hdrop : ((d :: ds').map Nat.toUInt8 ++ rest).drop (d :: ds').length = rest :=
      List.drop_left' (by simp)
    have hd' : d.toUInt8 ≠ 0 := by
      intro h0
      have := congrArg UInt8.toNat h0
      rw [toNat_toUInt8 (hlt d (by simp))] at this
      exact hd (by simpa using this)
    have hcond : ¬ ((((d :: ds').map Nat.toUInt8).length < (d :: ds').length) ∨
        ((d :: ds').map Nat.toUInt8).head? = some 0) := by
      simp [hd']
    clear h
    rw [ite_eq_right (show ¬ (128 + (d :: ds').length < 128) by omega), Nat.add_sub_cancel_left,
      ite_eq_right (show ¬ ((d :: ds').length = 0 ∨ (d :: ds').length = 127) by omega),
      readLong_eq, htake, hdrop, ite_eq_right hcond, hv, ite_eq_right (show ¬ n < 128 by omega)]
    simp

theorem toUInt8_toNat (b : UInt8) : b.toNat.toUInt8 = b := by simp

theorem readLength_sound {b : List UInt8} {n m : Nat} {rest : List UInt8}
    (h : readLength b = some (n, m, rest)) :
    n < 256 ^ 126 ∧ b = Der.Spec.lengthOctets n ++ rest ∧ m = (Der.Spec.lengthOctets n).length := by
  cases b with
  | nil => simp [readLength] at h
  | cons x bs =>
    have hx := UInt8.toNat_lt x
    rw [readLength_cons] at h
    by_cases hs : x.toNat < 128
    · rw [ite_eq_left hs, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨Nat.lt_of_lt_of_le (by omega) le_bound, ?_, ?_⟩
      · rw [lengthOctets_short _ (by omega), toUInt8_toNat]
        rfl
      · rw [lengthOctets_short _ (by omega)]
        rfl
    · rw [ite_eq_right hs] at h
      by_cases hk : x.toNat - 128 = 0 ∨ x.toNat - 128 = 127
      · rw [ite_eq_left hk] at h
        exact absurd h (Option.some_ne_none _).symm
      · rw [ite_eq_right hk, readLong_eq] at h
        generalize hkk : x.toNat - 128 = k at h hk
        by_cases hbad : (bs.take k).length < k ∨ (bs.take k).head? = some 0
        · rw [ite_eq_left hbad] at h
          exact absurd h (Option.some_ne_none _).symm
        · rw [ite_eq_right hbad] at h
          by_cases hn : ofDigits 8 ((bs.take k).map UInt8.toNat) < 128
          · rw [ite_eq_left hn] at h
            exact absurd h (Option.some_ne_none _).symm
          · rw [ite_eq_right hn, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hk' : (bs.take k).length = k := by
              have := List.length_take_le k bs
              omega
            have hall : ∀ y ∈ (bs.take k).map UInt8.toNat, y < 2 ^ 8 := by
              intro y hy
              obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
              exact UInt8.toNat_lt z
            have hne' : bs.take k ≠ [] := by
              intro h0
              rw [h0] at hk'
              simp at hk'
              omega
            have hne : (bs.take k).map UInt8.toNat ≠ [] := by
              intro h0
              exact hne' (List.map_eq_nil_iff.mp h0)
            have hhead : ((bs.take k).map UInt8.toNat).head hne ≠ 0 := by
              obtain ⟨z, zs, hz⟩ := List.exists_cons_of_ne_nil hne'
              simp only [hz, List.map_cons, List.head_cons]
              intro h0
              apply hbad
              right
              rw [hz]
              simp only [List.head?_cons, Option.some.injEq]
              exact UInt8.toNat_inj.mp (by simpa using h0)
            have hdig : Der.Spec.digits 256 (ofDigits 8 ((bs.take k).map UInt8.toNat)) =
                (bs.take k).map UInt8.toNat := by
              rw [ofDigits_eq, ← two_pow_eight]
              exact digits_digitsVal 8 (by omega) _ hne hall (Or.inl hhead)
            have hlen : (Der.Spec.digits 256 (ofDigits 8 ((bs.take k).map UInt8.toNat))).length ≤ 126 := by
              rw [hdig, List.length_map]
              omega
            refine ⟨(digits256_length_le _).mp hlen, ?_, ?_⟩
            · rw [lengthOctets_long _ (by omega), hdig, List.length_map, hk', List.cons_append]
              have e1 : (128 + k).toUInt8 = x := by
                apply UInt8.toNat_inj.mp
                rw [toNat_toUInt8 (by omega)]
                omega
              have e2 : ((bs.take k).map UInt8.toNat).map Nat.toUInt8 = bs.take k := by
                rw [List.map_map]
                conv => rhs; rw [← List.map_id (bs.take k)]
                apply List.map_congr_left
                intro y _
                simp
              rw [e1, e2, List.take_append_drop]
            · rw [lengthOctets_long _ (by omega), hdig]
              simp only [List.length_cons, List.length_map, hk']

/-- Only the class modulo 4 reaches the octet, so the code's `cls % 4`
    and the specification's `cls` give the same octet. -/
theorem lead_octet (cls : Nat) (c : Bool) (k : Nat) :
    (cls % 4 * 64 + (if c then 32 else 0) + k).toUInt8 = (Der.Spec.classAndForm cls c + k).toUInt8 := by
  apply UInt8.toNat_inj.mp
  rw [classAndForm_eq]
  simp only [Nat.toUInt8]
  cases c <;> simp <;> omega

theorem identOctets_eq (cls : Nat) (c : Bool) (tag : Nat) :
    identOctets cls c tag = Der.Spec.identifier cls c tag := by
  unfold identOctets
  by_cases ht : tag < 31
  · rw [identifier_low cls c tag (by omega)]
    simp only [ht, ↓reduceIte, lead_octet]
  · rw [identifier_high cls c tag (by omega)]
    simp only [ht, ↓reduceIte, lead_octet]
    rw [toDigits_eq 7 (by omega), two_pow_seven]
    rfl

theorem intOk_iff (c : List UInt8) : intOk c = true ↔ Der.Spec.IntegerContents c := by
  unfold Der.Spec.IntegerContents
  match c with
  | [] => simp [intOk]
  | [a] => simp [intOk]
  | a :: b :: rest =>
    have e : intOk (a :: b :: rest) =
        (!(a.toNat == 255 && 128 ≤ b.toNat) && !(a.toNat == 0 && b.toNat < 128)) := rfl
    rw [e]
    constructor
    · intro h
      refine ⟨by simp, ?_⟩
      rintro a' b' rest' he
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_iff,
        beq_eq_false_iff_ne, decide_eq_false_iff_not] at h
      omega
    · rintro ⟨-, h⟩
      obtain ⟨h1, h2⟩ := h a b rest rfl
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_iff,
        beq_eq_false_iff_ne, decide_eq_false_iff_not]
      omega

theorem constructedUniversal_iff (tag : Nat) :
    constructedUniversal tag = true ↔ Der.Spec.ConstructedUniversal tag := by
  unfold constructedUniversal Der.Spec.ConstructedUniversal
  simp [Bool.or_eq_true, beq_iff_eq, or_assoc]

theorem reservedUniversal_iff (tag : Nat) :
    reservedUniversal tag = true ↔ Der.Spec.ReservedUniversal tag := by
  unfold reservedUniversal Der.Spec.ReservedUniversal
  simp

theorem contentsOk_iff (tag : Nat) (c : List UInt8) :
    contentsOk tag c = true ↔
      (tag = 1 → c = [0] ∨ c = [255]) ∧ (tag = 2 ∨ tag = 10 → Der.Spec.IntegerContents c) ∧
        (tag = 5 → c = []) := by
  unfold contentsOk
  split
  · simp
  · simp [intOk_iff]
  · simp [List.isEmpty_iff]
  · simp [intOk_iff]
  · rename_i h1 h2 h5 h10
    simp only [true_iff]
    exact ⟨fun h => absurd h h1, fun h => h.elim (absurd · h2) (absurd · h10),
      fun h => absurd h h5⟩

theorem primOk_iff (cls tag : Nat) (c : List UInt8) :
    primOk cls tag c = true ↔ Der.Spec.PrimitiveOk cls tag c := by
  unfold primOk Der.Spec.PrimitiveOk
  by_cases hc : cls = 0
  · subst hc
    simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq,
      Bool.not_eq_eq_eq_not, Bool.not_true, forall_const, contentsOk_iff]
    rw [← Bool.not_eq_true, constructedUniversal_iff]
    simp only [and_assoc]
  · simp [hc]

theorem consOk_iff (cls tag : Nat) : consOk cls tag = true ↔ Der.Spec.ConstructedOk cls tag := by
  unfold consOk Der.Spec.ConstructedOk
  by_cases hc : cls = 0
  · subst hc
    simp [constructedUniversal_iff, reservedUniversal_iff]
  · simp [hc]

end DerProofs
