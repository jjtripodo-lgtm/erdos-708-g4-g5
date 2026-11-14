module

public import Erdos708.PrimeUnitHall
public import Erdos708.PrimeUnitProduct
public import Erdos708.PrimeResiduals
public import Erdos708.ProperDivisorSDR
public import Erdos708.Intervals
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Tactic

@[expose] public section

/-!
End-to-end common-unique-anchor lemma for Erdős #708.

This module is imported by the trusted theorem graph.  The public theorem
`one_anchor_four_moduli` is registered in the banked axiom audit; helper names
retain their historical `_candidate` suffixes for source compatibility.
-/

namespace Erdos708

/--
Four distinct upper-half moduli sharing one unique nonzero interval anchor can
be covered by that anchor plus four distinct off-anchor interval entries.

The conclusion is deliberately product-divisibility based and does not yet
package the five entries as one Finset.
-/
theorem one_anchor_four_moduli
    {L x : ℤ} {M : ℕ}
    (a : Fin 4 → ℕ)
    (haTwo : ∀ i, 2 ≤ a i)
    (haM : ∀ i, a i ≤ M)
    (haInj : Function.Injective a)
    (hxI : x ∈ integerInterval L M)
    (hx0 : x ≠ 0)
    (hxDiv : ∀ i, (a i : ℤ) ∣ x)
    (hunique :
      ∀ i y, y ∈ integerInterval L M →
        (a i : ℤ) ∣ y → y = x) :
    ∃ y : Fin 4 → ℤ,
      Function.Injective y ∧
      (∀ i, y i ∈ integerInterval L M ∧ y i ≠ x) ∧
      (∏ i : Fin 4, (a i : ℤ)) ∣
        x * ∏ i : Fin 4, y i := by
  classical

  have haPos : ∀ i, 0 < a i := by
    intro i
    have hi := haTwo i
    omega

  have haHalf : ∀ i, M < 2 * a i := by
    intro i
    exact modulus_gt_half_of_unique_multiple
      (d := a i) (x := x) (L := L) (M := M)
      (haPos i) hxI (hxDiv i) (hunique i)

  obtain ⟨f, hfInj, hfMem⟩ :=
    exists_distinct_prime_units_upper_half_candidate
      a haTwo haM haHalf haInj

  let r : Fin 4 → ℕ := fun i => selectedResidual a f i

  have hrPos : ∀ i, 0 < r i := by
    intro i
    dsimp [r]
    exact selectedResidual_pos_candidate (haPos i) (hfMem i)

  have hrDiv : ∀ i, r i ∣ a i := by
    intro i
    dsimp [r]
    exact selectedResidual_dvd_candidate (hfMem i)

  have hrProper : ∀ i, a i ≠ r i := by
    intro i
    dsimp [r]
    exact selectedResidual_proper_candidate (haPos i) (hfMem i)

  have hrAnchor : ∀ i, (r i : ℤ) ∣ x := by
    intro i
    dsimp [r]
    exact selectedResidual_dvd_anchor_candidate
      (hfMem i) (hxDiv i)

  obtain ⟨y, hyInj, hyMem⟩ :=
    proper_divisor_sdr_fin_four
      (L := L) (x := x) (M := M)
      a r haPos haInj hrPos hrDiv hrProper haM
      hxI hrAnchor

  have hyBasic :
      ∀ i, y i ∈ integerInterval L M ∧ y i ≠ x := by
    intro i
    have hi := hyMem i
    rw [properDivisorCandidates] at hi
    exact ⟨(Finset.mem_filter.mp hi).1,
      (Finset.mem_filter.mp hi).2.1⟩

  have hyResidual :
      ∀ i, (r i : ℤ) ∣ y i := by
    intro i
    have hi := hyMem i
    rw [properDivisorCandidates] at hi
    exact (Finset.mem_filter.mp hi).2.2

  have hPrimeAbs :
      (∏ i : Fin 4, selectedPrime f i) ∣ x.natAbs := by
    exact selected_prime_product_dvd_anchor_natAbs_candidate
      haPos hx0 hxDiv f hfInj hfMem

  have hPrimeCast :
      ((∏ i : Fin 4, selectedPrime f i : ℕ) : ℤ) ∣
        (x.natAbs : ℤ) := by
    exact_mod_cast hPrimeAbs

  have hAbsAnchor : (x.natAbs : ℤ) ∣ x := by
    exact Int.natAbs_dvd.mpr dvd_rfl

  have hPrimeAnchor :
      ((∏ i : Fin 4, selectedPrime f i : ℕ) : ℤ) ∣ x :=
    hPrimeCast.trans hAbsAnchor

  have hResidualProduct :
      (∏ i : Fin 4, (r i : ℤ)) ∣
        ∏ i : Fin 4, y i := by
    exact Finset.prod_dvd_prod_of_dvd
      (fun i : Fin 4 => (r i : ℤ))
      (fun i : Fin 4 => y i)
      (fun i hi => hyResidual i)

  have hSplit :
      ((∏ i : Fin 4, selectedPrime f i : ℕ) : ℤ) *
          (∏ i : Fin 4, (r i : ℤ)) =
        ∏ i : Fin 4, (a i : ℤ) := by
    have hNat :=
      selectedPrime_prod_mul_residual_prod_candidate
        a f hfMem
    dsimp [r]
    exact_mod_cast hNat

  have hCombined :=
    mul_dvd_mul hPrimeAnchor hResidualProduct

  rw [hSplit] at hCombined

  exact ⟨y, hyInj, hyBasic, hCombined⟩

end Erdos708
