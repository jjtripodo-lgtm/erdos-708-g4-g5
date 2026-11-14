module

public import Erdos708.RepeatedDivisor
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

/-!
Proper-divisor assembly helpers make the Fin 4 Hall proof work with arbitrary
index subfamilies without rebuilding quotient-coefficient arguments. This
module is part of the trusted SDR dependency graph.
-/

namespace Erdos708

/-- A positive proper divisor is at most half of its positive multiple. -/
theorem two_mul_le_of_dvd_ne_candidate
    {d a : ℕ}
    (hd : 0 < d) (ha : 0 < a)
    (hdiv : d ∣ a) (hne : a ≠ d) :
    2 * d ≤ a := by
  rcases dvd_iff_exists_eq_mul_right.mp hdiv with ⟨k, hk⟩
  have hkPos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk, hk0] at ha
    simp at ha
  have hkNeOne : k ≠ 1 := by
    intro hk1
    apply hne
    rw [hk, hk1]
    simp
  have hkTwo : 2 ≤ k := by omega
  rw [hk]
  calc
    2 * d = d * 2 := by omega
    _ ≤ d * k := Nat.mul_le_mul_left d hkTwo

/-- Reindex any finite subfamily whose originals all have the same proper
divisor and reuse repeated_proper_moduli_force_bound.

For a subfamily S of distinct originals, this gives
  (|S|+1)d <= M.
-/
theorem repeated_proper_moduli_finset_force_bound_candidate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M d : ℕ}
    (S : Finset ι)
    (hS : S.Nonempty)
    (hd : 0 < d)
    (a : ι → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haDiv : ∀ i ∈ S, d ∣ a i)
    (haProper : ∀ i ∈ S, a i ≠ d)
    (haM : ∀ i, a i ≤ M)
    (haInj : Function.Injective a) :
    (S.card + 1) * d ≤ M := by
  classical
  let aS : Fin S.card → ℕ :=
    fun j => a ((S.equivFin).symm j)
  have hm : 0 < S.card := Finset.card_pos.mpr hS
  have haSPos : ∀ j, 0 < aS j := by
    intro j
    exact haPos _
  have haSDiv : ∀ j, d ∣ aS j := by
    intro j
    apply haDiv
    exact ((S.equivFin).symm j).property
  have haSProper : ∀ j, aS j ≠ d := by
    intro j
    apply haProper
    exact ((S.equivFin).symm j).property
  have haSM : ∀ j, aS j ≤ M := by
    intro j
    exact haM _
  have haSInj : Function.Injective aS := by
    intro i j hij
    have hsub :
        ((S.equivFin).symm i : ι) = ((S.equivFin).symm j : ι) := by
      apply haInj
      exact hij
    exact (S.equivFin).symm.injective (Subtype.ext hsub)
  exact repeated_proper_moduli_force_bound
    hm hd aS haSPos haSDiv haSProper haSM haSInj

end Erdos708
