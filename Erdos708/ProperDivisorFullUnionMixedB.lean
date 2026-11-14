module

public import Erdos708.ProperDivisorFullUnionMixedA
public import Mathlib.Tactic

@[expose] public section

/-!
Continuation of the four-family Hall union bound. This module is part of the
trusted SDR dependency graph.
-/

namespace Erdos708

/-- Full union bound for multiplicity pattern 3+1. -/
theorem proper_divisor_full_union_rrrs_candidate
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
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l)
    (hrij : r i = r j) (hrik : r i = r k)
    (hril : r i ≠ r l) :
    4 ≤ (Finset.univ.biUnion (fullC L M r)).card := by
  let ar : Fin 3 → ℕ := fun n =>
    if n.val = 0 then a i else if n.val = 1 then a j else a k
  have harPos : ∀ n, 0 < ar n := by
    intro n
    fin_cases n <;> simp [ar, haPos]
  have harDiv : ∀ n, r i ∣ ar n := by
    intro n
    fin_cases n
    · simpa [ar] using hrDiv i
    · simpa [ar, hrij] using hrDiv j
    · simpa [ar, hrik] using hrDiv k
  have harProper : ∀ n, ar n ≠ r i := by
    intro n
    fin_cases n
    · simpa [ar] using hrProper i
    · simpa [ar, hrij] using hrProper j
    · simpa [ar, hrik] using hrProper k
  have harM : ∀ n, ar n ≤ M := by
    intro n
    fin_cases n <;> simp [ar, haM]
  have harInj : Function.Injective ar := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp [ar] at huv ⊢
    all_goals
      try exact (hij (haInj huv)).elim
      try exact (hik (haInj huv)).elim
      try exact (hjk (haInj huv)).elim
      try exact (hij (haInj huv.symm)).elim
      try exact (hik (haInj huv.symm)).elim
      try exact (hjk (haInj huv.symm)).elim
  have hMrrr : 4 * r i ≤ M := by
    simpa using repeated_proper_moduli_force_bound
      (m := 3) (M := M) (d := r i)
      (by decide) (hrPos i) ar harPos harDiv harProper harM harInj
  have hMl : 2 * r l ≤ M :=
    (two_mul_le_of_dvd_ne_candidate
      (hrPos l) (haPos l) (hrDiv l) (hrProper l)).trans (haM l)
  have hbDistinct : ∀ n, a l ≠ ar n := by
    intro n h
    fin_cases n
    · exact hil (haInj (by simpa [ar] using h)).symm
    · exact hjl (haInj (by simpa [ar] using h)).symm
    · exact hkl (haInj (by simpa [ar] using h)).symm
  by_contra hfull
  have hfull3 :
      (Finset.univ.biUnion (fullC L M r)).card ≤ 3 := by omega
  have hsub := fullC_two_subset (L := L) (M := M) (r := r) i l
  have hraw2 :
      (fullC L M r i ∪ fullC L M r l).card ≤ 3 :=
    (Finset.card_le_card hsub).trans hfull3
  have hraw :
      ((integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r i : ℤ) ∣ z) ∪
        (integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r l : ℤ) ∣ z)).card ≤ 3 := by
    simpa [fullC, properDivisorCandidates4, properDivisorCandidates] using hraw2
  exact mixed_rrrs_candidate_union_not_three_unordered_candidate
    hL hU (hrPos i) (hrPos l) hril
    hMrrr hMl ar harPos harDiv harProper harM harInj
    (haPos l) (hrDiv l) (hrProper l) (haM l) hbDistinct
    hq (hqmem i) (hqmem l) hraw

/-- Full union bound when all four divisor labels are equal. -/
theorem proper_divisor_full_union_all_equal_candidate
    {L : ℤ} {M : ℕ}
    (a r : Fin 4 → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haInj : Function.Injective a)
    (hrPos : ∀ i, 0 < r i)
    (hrDiv : ∀ i, r i ∣ a i)
    (hrProper : ∀ i, a i ≠ r i)
    (haM : ∀ i, a i ≤ M)
    (h01 : r 0 = r 1) (h02 : r 0 = r 2) (h03 : r 0 = r 3)
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1) :
    4 ≤ (Finset.univ.biUnion (fullC L M r)).card := by
  have hdiv : ∀ i, r 0 ∣ a i := by
    intro i
    fin_cases i
    · exact hrDiv 0
    · simpa [← h01] using hrDiv 1
    · simpa [← h02] using hrDiv 2
    · simpa [← h03] using hrDiv 3
  have hproper : ∀ i, a i ≠ r 0 := by
    intro i
    fin_cases i
    · exact hrProper 0
    · simpa [← h01] using hrProper 1
    · simpa [← h02] using hrProper 2
    · simpa [← h03] using hrProper 3
  have hMfive : 5 * r 0 ≤ M := by
    simpa using repeated_proper_moduli_force_bound
      (m := 4) (M := M) (d := r 0)
      (by decide) (hrPos 0) a haPos hdiv hproper haM haInj
  have hC0 : 4 ≤ (fullC L M r 0).card := by
    have hc := card_nonzero_multiples_ge
      (L := L) (M := M) (d := r 0) (k := 4)
      hL hU (hrPos 0) hMfive
    simpa [fullC, properDivisorCandidates4, properDivisorCandidates] using hc
  exact hC0.trans
    (Finset.card_le_card (fullC_subset (L := L) (M := M) (r := r) 0))

/-- Full union bound when all four divisor labels are distinct. -/
theorem proper_divisor_full_union_all_distinct_candidate
    {L : ℤ} {M : ℕ}
    (r : Fin 4 → ℕ)
    (hrPos : ∀ i, 0 < r i)
    (q : ℤ) (hq : q = 1 ∨ q = -1)
    (hqmem : ∀ i, q * (r i : ℤ) ∈ integerInterval L M)
    (h01 : r 0 ≠ r 1) (h02 : r 0 ≠ r 2) (h03 : r 0 ≠ r 3)
    (h12 : r 1 ≠ r 2) (h13 : r 1 ≠ r 3) (h23 : r 2 ≠ r 3) :
    4 ≤ (Finset.univ.biUnion (fullC L M r)).card := by
  let z0 : ℤ := q * (r 0 : ℤ)
  let z1 : ℤ := q * (r 1 : ℤ)
  let z2 : ℤ := q * (r 2 : ℤ)
  let z3 : ℤ := q * (r 3 : ℤ)
  have hz (i : Fin 4) :
      q * (r i : ℤ) ∈ fullC L M r i := by
    have hqNZ : q ≠ 0 := by rcases hq with hq | hq <;> simp [hq]
    have hrNZ : (r i : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt (hrPos i))
    simp only [fullC, properDivisorCandidates4, properDivisorCandidates,
      Finset.mem_filter]
    exact ⟨hqmem i, mul_ne_zero hqNZ hrNZ,
      by rcases hq with hq | hq <;> rw [hq] <;> simp⟩
  have hne01 : z0 ≠ z1 := by
    dsimp [z0, z1]
    rcases hq with hq | hq
    · rw [hq]
      have hcast : (r 0 : ℤ) ≠ (r 1 : ℤ) := by exact_mod_cast h01
      simpa using hcast
    · rw [hq]
      intro h
      apply h01
      have hcast : (r 0 : ℤ) = (r 1 : ℤ) := by linarith
      exact_mod_cast hcast
  have hne02 : z0 ≠ z2 := by
    dsimp [z0, z2]
    rcases hq with hq | hq
    · rw [hq]
      have hcast : (r 0 : ℤ) ≠ (r 2 : ℤ) := by exact_mod_cast h02
      simpa using hcast
    · rw [hq]
      intro h
      apply h02
      have hcast : (r 0 : ℤ) = (r 2 : ℤ) := by linarith
      exact_mod_cast hcast
  have hne03 : z0 ≠ z3 := by
    dsimp [z0, z3]
    rcases hq with hq | hq
    · rw [hq]
      have hcast : (r 0 : ℤ) ≠ (r 3 : ℤ) := by exact_mod_cast h03
      simpa using hcast
    · rw [hq]
      intro h
      apply h03
      have hcast : (r 0 : ℤ) = (r 3 : ℤ) := by linarith
      exact_mod_cast hcast
  have hne12 : z1 ≠ z2 := by
    dsimp [z1, z2]
    rcases hq with hq | hq
    · rw [hq]
      have hcast : (r 1 : ℤ) ≠ (r 2 : ℤ) := by exact_mod_cast h12
      simpa using hcast
    · rw [hq]
      intro h
      apply h12
      have hcast : (r 1 : ℤ) = (r 2 : ℤ) := by linarith
      exact_mod_cast hcast
  have hne13 : z1 ≠ z3 := by
    dsimp [z1, z3]
    rcases hq with hq | hq
    · rw [hq]
      have hcast : (r 1 : ℤ) ≠ (r 3 : ℤ) := by exact_mod_cast h13
      simpa using hcast
    · rw [hq]
      intro h
      apply h13
      have hcast : (r 1 : ℤ) = (r 3 : ℤ) := by linarith
      exact_mod_cast hcast
  have hne23 : z2 ≠ z3 := by
    dsimp [z2, z3]
    rcases hq with hq | hq
    · rw [hq]
      have hcast : (r 2 : ℤ) ≠ (r 3 : ℤ) := by exact_mod_cast h23
      simpa using hcast
    · rw [hq]
      intro h
      apply h23
      have hcast : (r 2 : ℤ) = (r 3 : ℤ) := by linarith
      exact_mod_cast hcast
  let Z : Finset ℤ := {z0, z1, z2, z3}
  have hZcard : Z.card = 4 := by
    dsimp [Z]
    simp [hne01, hne02, hne03, hne12, hne13, hne23]
  have hZsub : Z ⊆ Finset.univ.biUnion (fullC L M r) := by
    intro z hzmem
    dsimp [Z] at hzmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
    rcases hzmem with rfl | rfl | rfl | rfl
    · exact fullC_subset 0 (hz 0)
    · exact fullC_subset 1 (hz 1)
    · exact fullC_subset 2 (hz 2)
    · exact fullC_subset 3 (hz 3)
  have hle := Finset.card_le_card hZsub
  rw [hZcard] at hle
  exact hle

end Erdos708
