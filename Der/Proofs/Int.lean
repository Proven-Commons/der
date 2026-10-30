/-
  Integers (X.690 8.3): `readInt` reads exactly the contents octets X.690
  allows, `writeInt` writes them, and each integer has one encoding.
-/

import Der.Proofs.Header

namespace DerProofs

open Der

/-- The octets as one unsigned number. -/
def uval (c : List UInt8) : Nat := c.foldl (fun n o => n * 256 + o.toNat) 0

theorem uval_eq (c : List UInt8) : uval c = digitsVal 8 (c.map UInt8.toNat) := by
  unfold uval digitsVal
  rw [List.foldl_map]

theorem integerValue_cons (a : UInt8) (t : List UInt8) :
    Der.Spec.integerValue (a :: t) =
      if 128 ≤ a.toNat then (uval (a :: t) : Int) - 2 ^ (8 * (t.length + 1)) else uval (a :: t) := by
  simp [Der.Spec.integerValue, uval]

theorem readInt_iff' (c : List UInt8) (z : Int) :
    readInt c = some z ↔ Der.Spec.IntegerContents c ∧ Der.Spec.integerValue c = z := by
  rw [← intOk_iff]
  unfold readInt
  cases c with
  | nil => simp [intOk]
  | cons a t =>
    rw [integerValue_cons]
    have hu : ofDigits 8 ((a :: t).map UInt8.toNat) = uval (a :: t) := by
      rw [ofDigits_eq, uval_eq]
    by_cases hok : intOk (a :: t) = true
    · simp only [hok, ↓reduceIte, true_and, hu, List.length_cons]
      by_cases ha : a.toNat < 128
      · simp [ha, show ¬ 128 ≤ a.toNat by omega]
      · simp [ha, show 128 ≤ a.toNat by omega]
    · simp [hok]

theorem toNat_comp (a : UInt8) : (255 - a).toNat = 255 - a.toNat := by
  rw [UInt8.toNat_sub]
  have := UInt8.toNat_lt a
  simp
  omega

theorem comp_comp (a : UInt8) : 255 - (255 - a) = a := by
  apply UInt8.toNat_inj.mp
  rw [toNat_comp, toNat_comp]
  have := UInt8.toNat_lt a
  omega

/-- Every bit flipped. -/
def comp (c : List UInt8) : List UInt8 := c.map (255 - ·)

theorem comp_comp_list (c : List UInt8) : comp (comp c) = c := by
  unfold comp
  rw [List.map_map]
  conv => rhs; rw [← List.map_id c]
  apply List.map_congr_left
  intro a _
  exact comp_comp a

theorem uval_cons (a : UInt8) (t : List UInt8) :
    uval (a :: t) = a.toNat * 2 ^ (8 * t.length) + uval t := by
  rw [uval_eq, uval_eq, List.map_cons, digitsVal_cons, List.length_map]

theorem uval_lt (c : List UInt8) : uval c < 2 ^ (8 * c.length) := by
  rw [uval_eq]
  have := digitsVal_lt 8 (c.map UInt8.toNat) (by
    intro y hy
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
    exact UInt8.toNat_lt z)
  rwa [List.length_map] at this

theorem uval_comp (c : List UInt8) : uval (comp c) + uval c + 1 = 2 ^ (8 * c.length) := by
  induction c with
  | nil => simp [comp, uval]
  | cons a t ih =>
    have ha := UInt8.toNat_lt a
    have e : comp (a :: t) = (255 - a) :: comp t := rfl
    rw [e, uval_cons, uval_cons, toNat_comp, show (comp t).length = t.length by simp [comp],
      List.length_cons, Nat.mul_succ, Nat.pow_add]
    have : (255 - a.toNat) * 2 ^ (8 * t.length) + a.toNat * 2 ^ (8 * t.length) =
        255 * 2 ^ (8 * t.length) := by
      rw [← Nat.add_mul]; congr 1; omega
    have h256 : (2 : Nat) ^ 8 = 256 := rfl
    rw [h256]
    omega

theorem integerContents_comp (c : List UInt8) :
    Der.Spec.IntegerContents (comp c) ↔ Der.Spec.IntegerContents c := by
  unfold Der.Spec.IntegerContents comp
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨fun h0 => hne (by simp [h0]), ?_⟩
    rintro a b rest rfl
    obtain ⟨h1, h2⟩ := h (255 - a) (255 - b) (rest.map (255 - ·)) rfl
    rw [toNat_comp, toNat_comp] at h1 h2
    have := UInt8.toNat_lt a
    have := UInt8.toNat_lt b
    constructor <;> omega
  · rintro ⟨hne, h⟩
    refine ⟨fun h0 => hne (List.map_eq_nil_iff.mp h0), ?_⟩
    intro a' b' rest' he
    cases c with
    | nil => exact absurd rfl hne
    | cons a t =>
      cases t with
      | nil => simp at he
      | cons b rest =>
        simp only [List.map_cons, List.cons.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        obtain ⟨h1, h2⟩ := h a b rest rfl
        rw [toNat_comp, toNat_comp]
        have := UInt8.toNat_lt a
        have := UInt8.toNat_lt b
        constructor <;> omega

/-- What `writeInt` writes for `m ≥ 0`, before any bits are flipped. -/
def pos (m : Nat) : List UInt8 :=
  match (toDigits 8 m).map Nat.toUInt8 with
  | d :: ds => if 128 ≤ d.toNat then 0 :: d :: ds else d :: ds
  | [] => [0]

theorem writeInt_nonneg (z : Int) (h : 0 ≤ z) : writeInt z = pos z.toNat := by
  unfold writeInt pos
  simp only [h, ↓reduceIte]
  split <;> simp_all

theorem writeInt_neg (z : Int) (h : ¬ 0 ≤ z) : writeInt z = comp (pos (-z - 1).toNat) := by
  unfold writeInt pos comp
  simp only [h, ↓reduceIte]
  split <;> simp_all

theorem map_digits_toUInt8 (m : Nat) :
    ((Der.Spec.digits 256 m).map Nat.toUInt8).map UInt8.toNat = Der.Spec.digits 256 m :=
  map_toNat_toUInt8 _ (digits_lt (by omega) m)

theorem uval_digits (m : Nat) : uval ((Der.Spec.digits 256 m).map Nat.toUInt8) = m := by
  rw [uval_eq, map_digits_toUInt8, ← two_pow_eight, digitsVal_digits 8 (by omega)]

theorem pos_spec (m : Nat) :
    ∃ a t, pos m = a :: t ∧ a.toNat < 128 ∧ uval (pos m) = m ∧ Der.Spec.IntegerContents (pos m) := by
  unfold pos
  rw [toDigits_eq 8 (by omega), two_pow_eight]
  have hu := uval_digits m
  have hlt := digits_lt (by omega : 2 ≤ 256) m
  obtain ⟨d, ds, he⟩ := List.exists_cons_of_ne_nil (digits_ne_nil 256 m)
  rw [he] at hu hlt ⊢
  have hd : d < 256 := hlt d (by simp)
  simp only [List.map_cons, toNat_toUInt8 hd]
  by_cases h128 : 128 ≤ d
  · simp only [h128, ↓reduceIte]
    refine ⟨0, _, rfl, by simp, ?_, ?_⟩
    · rw [uval_cons]; simp only [UInt8.toNat_zero, Nat.zero_mul, Nat.zero_add]
      simpa using hu
    · refine ⟨by simp, ?_⟩
      intro a b rest hab
      simp only [List.cons.injEq] at hab
      obtain ⟨rfl, rfl, -⟩ := hab
      rw [toNat_toUInt8 hd]
      simp only [UInt8.toNat_zero]
      omega
  · simp only [h128, ↓reduceIte]
    refine ⟨d.toUInt8, _, rfl, by rw [toNat_toUInt8 hd]; omega, by simpa using hu, ?_⟩
    refine ⟨by simp, ?_⟩
    intro a b rest hab
    simp only [List.cons.injEq] at hab
    obtain ⟨rfl, hb⟩ := hab
    rw [toNat_toUInt8 hd]
    have hds : ds ≠ [] := by
      intro h0
      rw [h0] at hb
      simp at hb
    have hd0 : d ≠ 0 := by
      intro h0
      have hm : m ≠ 0 := by
        intro hm0
        subst hm0
        rw [digits_of_lt (by omega)] at he
        simp only [List.cons.injEq] at he
        exact hds he.2.symm
      obtain ⟨d', ds', he', hd'⟩ := digits_head (by omega : 2 ≤ 256) hm
      rw [he] at he'
      simp only [List.cons.injEq] at he'
      omega
    omega

theorem pos_unique (c : List UInt8) (h : Der.Spec.IntegerContents c) (a : UInt8) (t : List UInt8)
    (hc : c = a :: t) (ha : a.toNat < 128) : pos (uval c) = c := by
  subst hc
  obtain ⟨-, hic⟩ := h
  have hall : ∀ y ∈ List.map UInt8.toNat (a :: t), y < 2 ^ 8 := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
    exact UInt8.toNat_lt z
  have back : ∀ l : List UInt8, (l.map UInt8.toNat).map Nat.toUInt8 = l := by
    intro l
    rw [List.map_map]
    conv => rhs; rw [← List.map_id l]
    apply List.map_congr_left
    intro y _
    simp
  by_cases ha0 : a.toNat = 0
  · cases t with
    | nil =>
      have : a = 0 := UInt8.toNat_inj.mp (by simpa using ha0)
      subst this
      decide
    | cons b t' =>
      have hb := (hic a b t' rfl).2
      have hb128 : 128 ≤ b.toNat := by omega
      have hu : uval (a :: b :: t') = uval (b :: t') := by
        rw [uval_cons, ha0, Nat.zero_mul, Nat.zero_add]
      rw [hu]
      unfold pos
      rw [toDigits_eq 8 (by omega), uval_eq, digits_digitsVal 8 (by omega) _ (by simp)
        (fun y hy => hall y (List.mem_cons_of_mem _ hy))
        (Or.inl (by simp; omega)), back]
      simp only [hb128, ↓reduceIte, List.cons.injEq, and_true]
      exact UInt8.toNat_inj.mp (by simpa using ha0.symm)
  · unfold pos
    rw [toDigits_eq 8 (by omega), uval_eq, digits_digitsVal 8 (by omega) _ (by simp) hall
      (Or.inl (by simpa using ha0)), back]
    simp only [show ¬ 128 ≤ a.toNat by omega, ↓reduceIte]

theorem integerValue_low (a : UInt8) (t : List UInt8) (ha : a.toNat < 128) :
    Der.Spec.integerValue (a :: t) = uval (a :: t) := by
  rw [integerValue_cons]
  simp [show ¬ 128 ≤ a.toNat by omega]

theorem integerValue_high (a : UInt8) (t : List UInt8) (ha : 128 ≤ a.toNat) :
    Der.Spec.integerValue (a :: t) = (uval (a :: t) : Int) - ((2 ^ (8 * (t.length + 1)) : Nat) : Int) := by
  rw [integerValue_cons]
  simp [ha]

theorem writeInt_spec' (z : Int) :
    Der.Spec.IntegerContents (writeInt z) ∧ Der.Spec.integerValue (writeInt z) = z := by
  by_cases hz : 0 ≤ z
  · rw [writeInt_nonneg z hz]
    obtain ⟨a, t, he, ha, hu, hic⟩ := pos_spec z.toNat
    refine ⟨hic, ?_⟩
    rw [he, integerValue_low a t ha, ← he, hu]
    omega
  · rw [writeInt_neg z hz]
    obtain ⟨a, t, he, ha, hu, hic⟩ := pos_spec (-z - 1).toNat
    refine ⟨(integerContents_comp _).mpr hic, ?_⟩
    have hcomp := uval_comp (pos (-z - 1).toNat)
    rw [hu] at hcomp
    have e : comp (pos (-z - 1).toNat) = (255 - a) :: comp t := by rw [he]; rfl
    have hl : (comp t).length = t.length := by simp [comp]
    rw [e, integerValue_high _ _ (by rw [toNat_comp]; omega), ← e, hl]
    have hlen : (pos (-z - 1).toNat).length = t.length + 1 := by rw [he]; rfl
    rw [hlen] at hcomp
    omega

theorem writeInt_unique' (c : List UInt8) (h : Der.Spec.IntegerContents c) :
    writeInt (Der.Spec.integerValue c) = c := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h.1
  by_cases ha : a.toNat < 128
  · rw [integerValue_low a t ha, writeInt_nonneg _ (by omega)]
    simp only [Int.toNat_natCast]
    exact pos_unique _ h a t rfl ha
  · rw [integerValue_high a t (by omega)]
    have hlt := uval_lt (a :: t)
    have hcomp := uval_comp (a :: t)
    rw [writeInt_neg _ (by simp only [List.length_cons] at hlt; omega)]
    have hm : (-((uval (a :: t) : Int) - ((2 ^ (8 * (t.length + 1)) : Nat) : Int)) - 1).toNat =
        uval (comp (a :: t)) := by
      simp only [List.length_cons] at hcomp
      omega
    rw [hm]
    have hic : Der.Spec.IntegerContents (comp (a :: t)) := (integerContents_comp _).mpr h
    rw [pos_unique (comp (a :: t)) hic (255 - a) (comp t) rfl (by rw [toNat_comp]; omega),
      comp_comp_list]

end DerProofs
