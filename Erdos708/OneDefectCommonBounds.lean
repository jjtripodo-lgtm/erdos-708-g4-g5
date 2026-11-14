module

public import Erdos708.OneDefectBounds
public import Mathlib.Tactic

@[expose] public section

/-!
Explicit common-divisor bounds for the finite one-defect proof.

This module is part of the trusted one-defect dependency graph.  Helper names
retain their historical `_candidate` suffix.
-/

namespace Erdos708

theorem two_distinct_common_multiples_bound_candidate
    {M g a d : ℕ}
    (hg : 0 < g)
    (ha : 0 < a) (hd : 0 < d)
    (hga : g ∣ a) (hgd : g ∣ d)
    (haM : a ≤ M) (hdM : d ≤ M)
    (had : a ≠ d) :
    2 * g ≤ M := by
  let v : Fin 2 → ℕ := fun i => if i.val = 0 then a else d
  have hvPos : ∀ i, 0 < v i := by
    intro i
    fin_cases i <;> simp [v, ha, hd]
  have hvDiv : ∀ i, g ∣ v i := by
    intro i
    fin_cases i <;> simp [v, hga, hgd]
  have hvM : ∀ i, v i ≤ M := by
    intro i
    fin_cases i <;> simp [v, haM, hdM]
  have hvInj : Function.Injective v := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [v] at h ⊢
    · exact (had h).elim
    · exact (had h.symm).elim
  simpa using
    (distinct_multiples_force_bound_candidate
      (m := 2) (M := M) (d := g)
      (by decide) hg v hvPos hvDiv hvM hvInj)

theorem three_distinct_common_multiples_bound_candidate
    {M g a d b : ℕ}
    (hg : 0 < g)
    (ha : 0 < a) (hd : 0 < d) (hb : 0 < b)
    (hga : g ∣ a) (hgd : g ∣ d) (hgb : g ∣ b)
    (haM : a ≤ M) (hdM : d ≤ M) (hbM : b ≤ M)
    (had : a ≠ d) (hab : a ≠ b) (hdb : d ≠ b) :
    3 * g ≤ M := by
  let v : Fin 3 → ℕ := fun i =>
    if i.val = 0 then a else if i.val = 1 then d else b
  have hvPos : ∀ i, 0 < v i := by
    intro i
    fin_cases i <;> simp [v, ha, hd, hb]
  have hvDiv : ∀ i, g ∣ v i := by
    intro i
    fin_cases i <;> simp [v, hga, hgd, hgb]
  have hvM : ∀ i, v i ≤ M := by
    intro i
    fin_cases i <;> simp [v, haM, hdM, hbM]
  have hvInj : Function.Injective v := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [v] at h ⊢
    all_goals aesop
  simpa using
    (distinct_multiples_force_bound_candidate
      (m := 3) (M := M) (d := g)
      (by decide) hg v hvPos hvDiv hvM hvInj)

theorem four_distinct_common_multiples_bound_candidate
    {M g a d b c : ℕ}
    (hg : 0 < g)
    (ha : 0 < a) (hd : 0 < d) (hb : 0 < b) (hc : 0 < c)
    (hga : g ∣ a) (hgd : g ∣ d) (hgb : g ∣ b) (hgc : g ∣ c)
    (haM : a ≤ M) (hdM : d ≤ M) (hbM : b ≤ M) (hcM : c ≤ M)
    (had : a ≠ d) (hab : a ≠ b) (hac : a ≠ c)
    (hdb : d ≠ b) (hdc : d ≠ c) (hbc : b ≠ c) :
    4 * g ≤ M := by
  let v : Fin 4 → ℕ := fun i =>
    if i.val = 0 then a else if i.val = 1 then d else if i.val = 2 then b else c
  have hvPos : ∀ i, 0 < v i := by
    intro i
    fin_cases i <;> simp [v, ha, hd, hb, hc]
  have hvDiv : ∀ i, g ∣ v i := by
    intro i
    fin_cases i <;> simp [v, hga, hgd, hgb, hgc]
  have hvM : ∀ i, v i ≤ M := by
    intro i
    fin_cases i <;> simp [v, haM, hdM, hbM, hcM]
  have hvInj : Function.Injective v := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [v] at h ⊢
    all_goals aesop
  simpa using
    (distinct_multiples_force_bound_candidate
      (m := 4) (M := M) (d := g)
      (by decide) hg v hvPos hvDiv hvM hvInj)

end Erdos708
