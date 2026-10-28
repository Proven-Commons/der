/-
  Numbers written as digits in base `2 ^ w`: the code's `ofDigits` and
  `toDigits`, and the specification's `digits`.
-/

import Spec.Defs
import Der

namespace DerProofs

open Der

/-- Induction from the end of a list. -/
theorem snoc_induction {α : Type} {P : List α → Prop} (nil : P [])
    (snoc : ∀ l a, P l → P (l ++ [a])) (l : List α) : P l := by
  have : ∀ r : List α, P r.reverse := by
    intro r
    induction r with
    | nil => exact nil
    | cons a r ih => rw [List.reverse_cons]; exact snoc _ a ih
  simpa using this l.reverse

/-- The value of digits in base `2 ^ w`, most significant first, one
    digit at a time. -/
def digitsVal (w : Nat) (ds : List Nat) : Nat := ds.foldl (fun n d => n * 2 ^ w + d) 0

theorem foldl_digits (w : Nat) (ds : List Nat) (a : Nat) :
    ds.foldl (fun n d => n * 2 ^ w + d) a = a * 2 ^ (w * ds.length) + digitsVal w ds := by
  induction ds generalizing a with
  | nil => simp [digitsVal]
  | cons d ds ih =>
    simp only [List.foldl_cons, List.length_cons, digitsVal]
    rw [ih, ih (0 * 2 ^ w + d)]
    rw [Nat.mul_succ, Nat.pow_add, Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc,
      Nat.mul_comm (2 ^ w) (2 ^ (w * ds.length)), Nat.add_assoc]

theorem digitsVal_nil (w : Nat) : digitsVal w [] = 0 := rfl

theorem digitsVal_append (w : Nat) (l1 l2 : List Nat) :
    digitsVal w (l1 ++ l2) = digitsVal w l1 * 2 ^ (w * l2.length) + digitsVal w l2 := by
  unfold digitsVal
  rw [List.foldl_append, foldl_digits]
  rfl

theorem digitsVal_cons (w d : Nat) (ds : List Nat) :
    digitsVal w (d :: ds) = d * 2 ^ (w * ds.length) + digitsVal w ds := by
  have := digitsVal_append w [d] ds
  simp only [List.singleton_append] at this
  rw [this]
  simp [digitsVal]

theorem digitsVal_concat (w : Nat) (ds : List Nat) (d : Nat) :
    digitsVal w (ds ++ [d]) = digitsVal w ds * 2 ^ w + d := by
  rw [digitsVal_append]
  simp [digitsVal]

theorem ofDigits_go (w fuel : Nat) (ds : List Nat) (h : ds.length ≤ fuel) :
    ofDigits.go w fuel ds = digitsVal w ds := by
  induction fuel generalizing ds with
  | zero =>
    have : ds = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ fuel ih =>
    unfold ofDigits.go
    split
    · rfl
    · simp only [Nat.shiftLeft_eq]
      rw [ih _ (by simp; omega), ih _ (by simp; omega)]
      conv => rhs; rw [← List.take_append_drop (ds.length / 2) ds]
      rw [digitsVal_append, List.length_drop]

theorem ofDigits_eq (w : Nat) (ds : List Nat) : ofDigits w ds = digitsVal w ds :=
  ofDigits_go w _ ds (Nat.le_refl _)

/-- Digits below the base give a value below the base to the number of
    digits. -/
theorem digitsVal_lt (w : Nat) (ds : List Nat) (h : ∀ d ∈ ds, d < 2 ^ w) :
    digitsVal w ds < 2 ^ (w * ds.length) := by
  induction ds using snoc_induction with
  | nil => simp [digitsVal]
  | snoc ds d ih =>
    rw [digitsVal_concat, List.length_append, List.length_singleton, Nat.mul_succ, Nat.pow_add]
    have h1 := ih (fun x hx => h x (by simp [hx]))
    have h2 := h d (by simp)
    have : (digitsVal w ds + 1) * 2 ^ w ≤ 2 ^ (w * ds.length) * 2 ^ w :=
      Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

/-- A first digit that is not zero gives a value of at least the base to
    the number of digits after it. -/
theorem le_digitsVal (w d : Nat) (ds : List Nat) (hd : d ≠ 0) :
    2 ^ (w * ds.length) ≤ digitsVal w (d :: ds) := by
  rw [digitsVal_cons]
  have : 1 * 2 ^ (w * ds.length) ≤ d * 2 ^ (w * ds.length) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## The specification's digits -/

theorem digits_of_lt {b n : Nat} (h : n < b) : Spec.digits b n = [n] := by
  rw [Spec.digits]
  simp [h]

theorem digits_of_ge {b n : Nat} (hb : 2 ≤ b) (h : b ≤ n) :
    Spec.digits b n = Spec.digits b (n / b) ++ [n % b] := by
  rw [Spec.digits]
  simp only [show ¬ (n < b ∨ b < 2) by omega, ↓reduceDIte]

theorem digits_ne_nil (b n : Nat) : Spec.digits b n ≠ [] := by
  rw [Spec.digits]
  split <;> simp

theorem digits_lt {b : Nat} (hb : 2 ≤ b) (n : Nat) : ∀ d ∈ Spec.digits b n, d < b := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < b
    · rw [digits_of_lt h]
      simpa using h
    · rw [digits_of_ge hb (by omega)]
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact ih (n / b) (Nat.div_lt_self (by omega) (by omega)) d hd
      · simp at hd
        rw [hd]
        exact Nat.mod_lt _ (by omega)

/-- The digits of a number that is not zero start with a digit that is
    not zero. -/
theorem digits_head {b n : Nat} (hb : 2 ≤ b) (hn : n ≠ 0) :
    ∃ d ds, Spec.digits b n = d :: ds ∧ d ≠ 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < b
    · exact ⟨n, [], digits_of_lt h, hn⟩
    · rw [digits_of_ge hb (by omega)]
      obtain ⟨d, ds, he, hd⟩ :=
        ih (n / b) (Nat.div_lt_self (by omega) (by omega)) (by
          have := Nat.div_pos (show b ≤ n by omega) (by omega : 0 < b)
          omega)
      exact ⟨d, ds ++ [n % b], by rw [he]; rfl, hd⟩

theorem digitsVal_digits (w : Nat) (hw : 1 ≤ w) (n : Nat) :
    digitsVal w (Spec.digits (2 ^ w) n) = n := by
  have hb : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hw
    simpa using this
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 2 ^ w
    · rw [digits_of_lt h]
      simp [digitsVal]
    · rw [digits_of_ge hb (by omega), digitsVal_concat,
        ih (n / 2 ^ w) (Nat.div_lt_self (by omega) (by omega))]
      exact Nat.div_add_mod' n (2 ^ w)

/-- Digits below the base, with a first digit that is not zero (or the
    single digit zero), are the digits of their value. -/
theorem digits_digitsVal (w : Nat) (hw : 1 ≤ w) (ds : List Nat) (hne : ds ≠ [])
    (hlt : ∀ d ∈ ds, d < 2 ^ w) (hhead : ds.head hne ≠ 0 ∨ ds.length = 1) :
    Spec.digits (2 ^ w) (digitsVal w ds) = ds := by
  have hb : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hw
    simpa using this
  induction ds using snoc_induction with
  | nil => exact absurd rfl hne
  | snoc init d ih =>
    have hd : d < 2 ^ w := hlt d (by simp)
    by_cases hi : init = []
    · subst hi
      simp only [List.nil_append]
      rw [show digitsVal w [d] = d by simp [digitsVal], digits_of_lt hd]
    · have hlt' : ∀ x ∈ init, x < 2 ^ w := fun x hx => hlt x (by simp [hx])
      have hh : init.head hi ≠ 0 := by
        rcases hhead with hh | hh
        · obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hi
          simpa using hh
        · obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hi
          simp at hh
      have hpos : 0 < digitsVal w init := by
        obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hi
        have := le_digitsVal w a t (by simpa using hh)
        have := Nat.two_pow_pos (w * t.length)
        omega
      rw [digitsVal_concat]
      have hge : 2 ^ w ≤ digitsVal w init * 2 ^ w + d := by
        have : 1 * 2 ^ w ≤ digitsVal w init * 2 ^ w := Nat.mul_le_mul_right _ hpos
        omega
      rw [digits_of_ge hb hge]
      have e1 : (digitsVal w init * 2 ^ w + d) / 2 ^ w = digitsVal w init := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hd, Nat.zero_add]
      have e2 : (digitsVal w init * 2 ^ w + d) % 2 ^ w = d := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
      rw [e1, e2, ih hi hlt' (Or.inl hh)]

/-- The number of digits is at most `k` exactly when the number is below
    the base to the `k`. -/
theorem digits_length_le (w : Nat) (hw : 1 ≤ w) (n k : Nat) (hk : 1 ≤ k) :
    (Spec.digits (2 ^ w) n).length ≤ k ↔ n < 2 ^ (w * k) := by
  have hb : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hw
    simpa using this
  constructor
  · intro h
    have hv := digitsVal_lt w (Spec.digits (2 ^ w) n) (digits_lt hb n)
    rw [digitsVal_digits w hw] at hv
    exact Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ h))
  · intro h
    by_cases hn : n = 0
    · subst hn
      rw [digits_of_lt (by omega)]
      simpa using hk
    · obtain ⟨d, ds, he, hd⟩ := digits_head hb hn
      have hle := le_digitsVal w d ds hd
      rw [← he, digitsVal_digits w hw] at hle
      rw [he]
      simp only [List.length_cons]
      have : w * ds.length < w * k := by
        apply Nat.lt_of_not_le
        intro hc
        have := Nat.pow_le_pow_right (by omega : 0 < 2) hc
        omega
      have := Nat.lt_of_mul_lt_mul_left this
      omega

/-! ## The code's digits -/

theorem toDigitsAux_eq (w : Nat) (hw : 1 ≤ w) (fuel n : Nat) (acc : List Nat) (hn : 0 < n)
    (hf : n ≤ fuel) : toDigitsAux w fuel n acc = Spec.digits (2 ^ w) n ++ acc := by
  have hb : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hw
    simpa using this
  induction fuel generalizing n acc with
  | zero => omega
  | succ fuel ih =>
    rw [toDigitsAux]
    simp only [show ¬ n = 0 by omega, ↓reduceIte, Nat.shiftRight_eq_div_pow]
    by_cases h : n < 2 ^ w
    · rw [Nat.div_eq_of_lt h, digits_of_lt h, Nat.mod_eq_of_lt h]
      cases fuel <;> simp [toDigitsAux]
    · have hq : 0 < n / 2 ^ w := Nat.div_pos (by omega) (by omega)
      have hq' : n / 2 ^ w < n := Nat.div_lt_self (by omega) (by omega)
      rw [ih (n / 2 ^ w) _ hq (by omega), digits_of_ge (n := n) hb (by omega), List.append_assoc]
      rfl

theorem toDigits_eq (w : Nat) (hw : 1 ≤ w) (n : Nat) : toDigits w n = Spec.digits (2 ^ w) n := by
  unfold toDigits
  split
  · rename_i h
    subst h
    rw [digits_of_lt (Nat.two_pow_pos w)]
  · rw [toDigitsAux_eq w hw n n [] (by omega) (Nat.le_refl _), List.append_nil]

end DerProofs
