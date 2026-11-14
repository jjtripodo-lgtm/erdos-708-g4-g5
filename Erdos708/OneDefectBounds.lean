module

public import Erdos708.OneDefect
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

/-!
Finite-subfamily counting helper for the four-modulus one-defect proof.

This module is part of the trusted one-defect dependency graph.  Its helper
name retains the historical `_candidate` suffix.
-/

namespace Erdos708

/--
Reindex a finite subfamily of distinct positive multiples and reuse
distinct_multiples_force_bound_candidate.

If every original indexed by S is a positive multiple of d, all originals are
distinct and at most M, then |S|*d <= M.
-/
theorem distinct_multiples_finset_force_bound_candidate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M d : ℕ}
    (S : Finset ι)
    (hS : S.Nonempty)
    (hd : 0 < d)
    (a : ι → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haDiv : ∀ i ∈ S, d ∣ a i)
    (haM : ∀ i, a i ≤ M)
    (haInj : Function.Injective a) :
    S.card * d ≤ M := by
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
  exact distinct_multiples_force_bound_candidate
    hm hd aS haSPos haSDiv haSM haSInj

end Erdos708
