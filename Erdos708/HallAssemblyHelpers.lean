module

public import Erdos708.Intervals
public import Erdos708.RepeatedDivisor
public import Mathlib.Tactic

@[expose] public section

/-!
Shared-side infrastructure for assembling the four-label proper-divisor Hall
theorem. This module is part of the trusted SDR dependency graph.
-/

namespace Erdos708

/--
In an M-term integer interval containing zero, there is one common side
q in {+1,-1} such that q*d lies in the interval for every d with 2d<=M.

This extracts the side-selection argument already used internally by the
all-distinct SDR proof.
-/
theorem exists_common_sign_mem_of_two_mul_le_candidate
    {m M : ℕ} {L : ℤ}
    (hL : L ≤ 0)
    (hU : 0 ≤ L + (M : ℤ) - 1)
    (d : Fin m → ℕ)
    (hdSmall : ∀ i, 2 * d i ≤ M) :
    ∃ q : ℤ, (q = 1 ∨ q = -1) ∧
      ∀ i, q * (d i : ℤ) ∈ integerInterval L M := by
  let U : ℤ := L + (M : ℤ) - 1
  have hspan : -L + U = (M : ℤ) - 1 := by
    dsimp [U]
    omega
  have hside :
      2 * U ≥ (M : ℤ) - 1 ∨
      2 * (-L) ≥ (M : ℤ) - 1 := by
    omega
  rcases hside with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro i
    rw [mem_integerInterval]
    have hd : 2 * (d i : ℤ) ≤ (M : ℤ) := by
      exact_mod_cast hdSmall i
    have hUi : (d i : ℤ) ≤ U := by
      dsimp [U] at hpos ⊢
      omega
    constructor
    · have hnonneg : 0 ≤ (d i : ℤ) := by positivity
      omega
    · simpa [U] using hUi
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro i
    rw [mem_integerInterval]
    have hd : 2 * (d i : ℤ) ≤ (M : ℤ) := by
      exact_mod_cast hdSmall i
    have hLi : L ≤ -(d i : ℤ) := by
      omega
    constructor
    · simpa using hLi
    · have hnonneg : 0 ≤ (d i : ℤ) := by positivity
      omega

/-- Two distinct proper positive r-multiples bounded by M force 3r<=M. -/
theorem two_repeated_proper_force_three_candidate
    {M r a b : ℕ}
    (hr : 0 < r)
    (ha : 0 < a) (hb : 0 < b)
    (hra : r ∣ a) (hrb : r ∣ b)
    (haProper : a ≠ r) (hbProper : b ≠ r)
    (haM : a ≤ M) (hbM : b ≤ M)
    (hab : a ≠ b) :
    3 * r ≤ M := by
  let f : Fin 2 → ℕ := fun i => if i.val = 0 then a else b
  have hfPos : ∀ i, 0 < f i := by
    intro i
    fin_cases i <;> simp [f, ha, hb]
  have hfDiv : ∀ i, r ∣ f i := by
    intro i
    fin_cases i <;> simp [f, hra, hrb]
  have hfProper : ∀ i, f i ≠ r := by
    intro i
    fin_cases i <;> simp [f, haProper, hbProper]
  have hfM : ∀ i, f i ≤ M := by
    intro i
    fin_cases i <;> simp [f, haM, hbM]
  have hfInj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
    · exact (hab hij).elim
    · exact (hab hij.symm).elim
  simpa using
    (repeated_proper_moduli_force_bound
      (m := 2) (M := M) (d := r)
      (by decide) hr f hfPos hfDiv hfProper hfM hfInj)

/-- Three distinct proper positive r-multiples bounded by M force 4r<=M. -/
theorem three_repeated_proper_force_four_candidate
    {M r a b c : ℕ}
    (hr : 0 < r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hra : r ∣ a) (hrb : r ∣ b) (hrc : r ∣ c)
    (haProper : a ≠ r) (hbProper : b ≠ r) (hcProper : c ≠ r)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    4 * r ≤ M := by
  let f : Fin 3 → ℕ := fun i =>
    if i.val = 0 then a else if i.val = 1 then b else c
  have hfPos : ∀ i, 0 < f i := by
    intro i
    fin_cases i <;> simp [f, ha, hb, hc]
  have hfDiv : ∀ i, r ∣ f i := by
    intro i
    fin_cases i <;> simp [f, hra, hrb, hrc]
  have hfProper : ∀ i, f i ≠ r := by
    intro i
    fin_cases i <;> simp [f, haProper, hbProper, hcProper]
  have hfM : ∀ i, f i ≤ M := by
    intro i
    fin_cases i <;> simp [f, haM, hbM, hcM]
  have hfInj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
    all_goals aesop
  simpa using
    (repeated_proper_moduli_force_bound
      (m := 3) (M := M) (d := r)
      (by decide) hr f hfPos hfDiv hfProper hfM hfInj)

end Erdos708
