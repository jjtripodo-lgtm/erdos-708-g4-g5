module

public import Erdos708.Intervals
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

@[expose] public section

/-!
Base existence lemma for the four-modulus Erdős #708 interval-cover argument.

This module is part of the trusted one-defect dependency graph.  Its helper
name retains the historical `_candidate` suffix.
-/

namespace Erdos708

/--
Every interval of M consecutive integers contains a multiple of every positive
d <= M.

The chosen point is d * ceil(L/d), the first d-multiple at or above the
left endpoint.
-/
theorem exists_interval_multiple_of_le_candidate
    {L : ℤ} {M d : ℕ}
    (hd : 0 < d)
    (hdM : d ≤ M) :
    ∃ y ∈ integerInterval L M, (d : ℤ) ∣ y := by
  let q : ℤ := ⌈(L : ℚ) / (d : ℚ)⌉
  let y : ℤ := q * (d : ℤ)
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hdne : (d : ℚ) ≠ 0 := ne_of_gt hdq
  have hlowQ : (L : ℚ) ≤ (q : ℚ) * (d : ℚ) := by
    have hceil : (L : ℚ) / (d : ℚ) ≤ (q : ℚ) := by
      dsimp [q]
      exact Int.le_ceil _
    have hmul := mul_le_mul_of_nonneg_right hceil hdq.le
    calc
      (L : ℚ) = ((L : ℚ) / (d : ℚ)) * (d : ℚ) := by
        field_simp
      _ ≤ (q : ℚ) * (d : ℚ) := hmul
  have hhighQ : (q : ℚ) * (d : ℚ) < (L : ℚ) + (d : ℚ) := by
    have hceil : (q : ℚ) < (L : ℚ) / (d : ℚ) + 1 := by
      dsimp [q]
      exact Int.ceil_lt_add_one _
    have hmul := mul_lt_mul_of_pos_right hceil hdq
    calc
      (q : ℚ) * (d : ℚ)
          < ((L : ℚ) / (d : ℚ) + 1) * (d : ℚ) := hmul
      _ = (L : ℚ) + (d : ℚ) := by
        field_simp
  have hlow : L ≤ y := by
    dsimp [y]
    exact_mod_cast hlowQ
  have hhigh : y < L + (M : ℤ) := by
    have hdMint : (d : ℤ) ≤ (M : ℤ) := by exact_mod_cast hdM
    have hhighZ : y < L + (d : ℤ) := by
      dsimp [y]
      exact_mod_cast hhighQ
    omega
  have hyI : y ∈ integerInterval L M := by
    rw [mem_integerInterval]
    constructor
    · exact hlow
    · omega
  refine ⟨y, hyI, ?_⟩
  refine ⟨q, ?_⟩
  dsimp [y]
  ring

end Erdos708
