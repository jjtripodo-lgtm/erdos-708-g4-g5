module

public import Erdos708.ProperDivisorHallFinFour
public import Erdos708.HallAssemblyHelpers
public import Mathlib.Tactic

@[expose] public section

/-!
Full-union wrappers for the mixed four-label proper-divisor multiplicity
patterns. This module is part of the trusted SDR dependency graph.
-/

namespace Erdos708

def fullC
    (L : ℤ) (M : ℕ) (r : Fin 4 → ℕ) (i : Fin 4) : Finset ℤ :=
  properDivisorCandidates4 L M r i

theorem fullC_subset
    {L : ℤ} {M : ℕ} {r : Fin 4 → ℕ} (i : Fin 4) :
    fullC L M r i ⊆ Finset.univ.biUnion (fullC L M r) := by
  intro z hz
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩

theorem fullC_two_subset
    {L : ℤ} {M : ℕ} {r : Fin 4 → ℕ}
    (i j : Fin 4) :
    fullC L M r i ∪ fullC L M r j ⊆
      Finset.univ.biUnion (fullC L M r) := by
  intro z hz
  simp only [Finset.mem_union] at hz
  rcases hz with hi | hj
  · exact fullC_subset i hi
  · exact fullC_subset j hj

theorem fullC_three_subset
    {L : ℤ} {M : ℕ} {r : Fin 4 → ℕ}
    (i j k : Fin 4) :
    (fullC L M r i ∪ fullC L M r j) ∪ fullC L M r k ⊆
      Finset.univ.biUnion (fullC L M r) := by
  intro z hz
  simp only [Finset.mem_union] at hz
  rcases hz with (hi | hj) | hk
  · exact fullC_subset i hi
  · exact fullC_subset j hj
  · exact fullC_subset k hk

/-- Full union bound for multiplicity pattern 2+1+1. -/
theorem proper_divisor_full_union_rrst_candidate
    {L : ℤ} {M : ℕ}
    (a r : Fin 4 → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haInj : Function.Injective a)
    (hrPos : ∀ i, 0 < r i)
    (hrDiv : ∀ i, r i ∣ a i)
    (hrProper : ∀ i, a i ≠ r i)
    (haM : ∀ i, a i ≤ M)
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (q : ℤ) (hq : q = 1 ∨ q = -1)
    (hqmem : ∀ i, q * (r i : ℤ) ∈ integerInterval L M)
    (i j k l : Fin 4)
    (hij : i ≠ j)
    (hrij : r i = r j)
    (hrik : r i ≠ r k) (hril : r i ≠ r l) (hrkl : r k ≠ r l) :
    4 ≤ (Finset.univ.biUnion (fullC L M r)).card := by
  have hMrr : 3 * r i ≤ M := by
    apply two_repeated_proper_force_three_candidate
      (hrPos i) (haPos i) (haPos j)
      (hrDiv i)
      (by simpa [← hrij] using hrDiv j)
      (hrProper i)
      (by simpa [← hrij] using hrProper j)
      (haM i) (haM j)
    intro h
    exact hij (haInj h)
  have hMk : 2 * r k ≤ M :=
    (two_mul_le_of_dvd_ne_candidate
      (hrPos k) (haPos k) (hrDiv k) (hrProper k)).trans (haM k)
  have hMl : 2 * r l ≤ M :=
    (two_mul_le_of_dvd_ne_candidate
      (hrPos l) (haPos l) (hrDiv l) (hrProper l)).trans (haM l)
  by_contra hfull
  have hfull3 :
      (Finset.univ.biUnion (fullC L M r)).card ≤ 3 := by omega
  have hsub := fullC_three_subset (L := L) (M := M) (r := r) i k l
  have hraw3 :
      ((fullC L M r i ∪ fullC L M r k) ∪ fullC L M r l).card ≤ 3 :=
    (Finset.card_le_card hsub).trans hfull3
  have hraw :
      ((((integerInterval L M).filter
            (fun z => z ≠ 0 ∧ (r i : ℤ) ∣ z) ∪
          (integerInterval L M).filter
            (fun z => z ≠ 0 ∧ (r k : ℤ) ∣ z)) ∪
        (integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r l : ℤ) ∣ z)).card ≤ 3) := by
    simpa [fullC, properDivisorCandidates4, properDivisorCandidates] using hraw3
  exact mixed_rrst_candidate_union_not_three_unordered_candidate
    hL hU (hrPos i) (hrPos k) (hrPos l)
    hrik hril hrkl hMrr hMk hMl hq
    (hqmem i) (hqmem k) (hqmem l) hraw

/-- Full union bound for multiplicity pattern 2+2. -/
theorem proper_divisor_full_union_rrss_candidate
    {L : ℤ} {M : ℕ}
    (a r : Fin 4 → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haInj : Function.Injective a)
    (hrPos : ∀ i, 0 < r i)
    (hrDiv : ∀ i, r i ∣ a i)
    (hrProper : ∀ i, a i ≠ r i)
    (haM : ∀ i, a i ≤ M)
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (q : ℤ) (hq : q = 1 ∨ q = -1)
    (hqmem : ∀ i, q * (r i : ℤ) ∈ integerInterval L M)
    (i j k l : Fin 4)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hrij : r i = r j) (hrkl : r k = r l)
    (hrik : r i ≠ r k) :
    4 ≤ (Finset.univ.biUnion (fullC L M r)).card := by
  have hMri : 3 * r i ≤ M := by
    apply two_repeated_proper_force_three_candidate
      (hrPos i) (haPos i) (haPos j)
      (hrDiv i)
      (by simpa [← hrij] using hrDiv j)
      (hrProper i)
      (by simpa [← hrij] using hrProper j)
      (haM i) (haM j)
    intro h
    exact hij (haInj h)
  have hMrk : 3 * r k ≤ M := by
    apply two_repeated_proper_force_three_candidate
      (hrPos k) (haPos k) (haPos l)
      (hrDiv k)
      (by simpa [← hrkl] using hrDiv l)
      (hrProper k)
      (by simpa [← hrkl] using hrProper l)
      (haM k) (haM l)
    intro h
    exact hkl (haInj h)
  by_contra hfull
  have hfull3 :
      (Finset.univ.biUnion (fullC L M r)).card ≤ 3 := by omega
  have hsub := fullC_two_subset (L := L) (M := M) (r := r) i k
  have hraw2 :
      (fullC L M r i ∪ fullC L M r k).card ≤ 3 :=
    (Finset.card_le_card hsub).trans hfull3
  have hraw :
      ((integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r i : ℤ) ∣ z) ∪
        (integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r k : ℤ) ∣ z)).card ≤ 3 := by
    simpa [fullC, properDivisorCandidates4, properDivisorCandidates] using hraw2
  exact mixed_rrss_candidate_union_not_three_unordered_candidate
    hL hU (hrPos i) (hrPos k) hrik
    hMri hMrk hq (hqmem i) (hqmem k) hraw

end Erdos708
