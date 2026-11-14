module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic

@[expose] public section

/-!
Alternative prime-unit representation for Erdős #708.

Instead of a dependent sigma type tied to one ambient lcm, a unit is a raw
label (p,j): prime p and exponent slot j. Each integer has a finite set of
such labels. Hall can use these raw finite sets directly. Sperner can later
restrict to the subtype of the unit set of a subfamily lcm.

This module is part of the trusted one-anchor dependency graph.  Helper names
retain their historical `_candidate` suffix.
-/

namespace Erdos708

open scoped ArithmeticFunction.Omega

/-- Raw labeled prime-exponent unit. The first coordinate is the prime and the
second is the zero-based exponent slot. -/
abbrev RawPrimeUnit := ℕ × ℕ

/-- All labeled prime-exponent units occurring in n. -/
def rawPrimeUnits (n : ℕ) : Finset RawPrimeUnit :=
  n.primeFactors.biUnion fun p =>
    (Finset.range (n.factorization p)).image fun j => (p, j)

@[simp] theorem mem_rawPrimeUnits_candidate
    {n p j : ℕ} :
    (p,j) ∈ rawPrimeUnits n ↔
      p ∈ n.primeFactors ∧ j < n.factorization p := by
  classical
  simp [rawPrimeUnits]

/-- Different primes contribute disjoint labeled slots. -/
theorem rawPrimeUnits_fiber_disjoint_candidate
    {n p q : ℕ} (hpq : p ≠ q) :
    Disjoint
      ((Finset.range (n.factorization p)).image fun j => (p,j))
      ((Finset.range (n.factorization q)).image fun j => (q,j)) := by
  classical
  rw [Finset.disjoint_left]
  intro u hup huq
  simp only [Finset.mem_image, Finset.mem_range] at hup huq
  rcases hup with ⟨jp, hjp, rfl⟩
  rcases huq with ⟨jq, hjq, hpair⟩
  exact hpq (congrArg Prod.fst hpair).symm

/--
The number of raw labeled units is big-Omega(n).

This is the finite-set version of summing all factorization exponents.
-/
theorem card_rawPrimeUnits_candidate (n : ℕ) :
    (rawPrimeUnits n).card = ArithmeticFunction.cardFactors n := by
  classical
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
  unfold rawPrimeUnits
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.card_image_of_injective _ (by
      intro i j hij
      exact congrArg Prod.snd hij)]
    simp
  · intro p hp q hq hpq
    exact rawPrimeUnits_fiber_disjoint_candidate hpq

/-- Divisibility gives inclusion of raw unit sets. -/
theorem rawPrimeUnits_subset_of_dvd_candidate
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ∣ b) :
    rawPrimeUnits a ⊆ rawPrimeUnits b := by
  classical
  have hfac : a.factorization ≤ b.factorization :=
    (Nat.factorization_le_iff_dvd ha hb).2 hab
  intro u hu
  rcases u with ⟨p,j⟩
  rw [mem_rawPrimeUnits_candidate] at hu ⊢
  have hpa := Nat.mem_primeFactors.mp hu.1
  have hpb : p ∈ b.primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hpa.1, hpa.2.1.trans hab, hb⟩
  exact ⟨hpb, lt_of_lt_of_le hu.2 (hfac p)⟩

/-- For nonzero integers, inclusion of raw unit sets is equivalent to divisibility. -/
theorem rawPrimeUnits_subset_iff_dvd_candidate
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    rawPrimeUnits a ⊆ rawPrimeUnits b ↔ a ∣ b := by
  constructor
  · intro hsub
    apply (Nat.factorization_le_iff_dvd ha hb).1
    intro p
    by_cases hz : a.factorization p = 0
    · simp [hz]
    · have hpMem : p ∈ a.primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr hz
      let j : ℕ := a.factorization p - 1
      have hj : j < a.factorization p := by
        dsimp [j]
        omega
      have huA : (p,j) ∈ rawPrimeUnits a := by
        rw [mem_rawPrimeUnits_candidate]
        exact ⟨hpMem, hj⟩
      have huB := hsub huA
      rw [mem_rawPrimeUnits_candidate] at huB
      dsimp [j] at huB
      omega
  · exact rawPrimeUnits_subset_of_dvd_candidate ha hb

/-- An integer greater than one has at least one labeled prime unit. -/
theorem rawPrimeUnits_nonempty_candidate
    {a : ℕ} (ha : 1 < a) :
    (rawPrimeUnits a).Nonempty := by
  classical
  have hpf : a.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr ha
  rcases hpf with ⟨p,hp⟩
  have hpData := Nat.mem_primeFactors.mp hp
  have hfac :
      0 < a.factorization p :=
    hpData.1.factorization_pos_of_dvd (by omega) hpData.2.1
  refine ⟨(p,0), ?_⟩
  rw [mem_rawPrimeUnits_candidate]
  exact ⟨hp, hfac⟩

/-- Pairwise lcm corresponds to union of raw labeled-unit sets. -/
theorem rawPrimeUnits_lcm_candidate
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    rawPrimeUnits (Nat.lcm a b) =
      rawPrimeUnits a ∪ rawPrimeUnits b := by
  classical
  ext u
  rcases u with ⟨p,j⟩
  rw [mem_rawPrimeUnits_candidate]
  rw [Finset.mem_union]
  rw [mem_rawPrimeUnits_candidate, mem_rawPrimeUnits_candidate]
  rw [Nat.factorization_lcm ha hb]
  simp only [Finsupp.sup_apply]
  constructor
  · intro h
    have hj : j < max (a.factorization p) (b.factorization p) := h.2
    rcases lt_max_iff.mp hj with hja | hjb
    · left
      refine ⟨?_, hja⟩
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
    · right
      refine ⟨?_, hjb⟩
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
  · intro h
    rcases h with h | h
    · refine ⟨?_, lt_of_lt_of_le h.2 (le_max_left _ _)⟩
      rw [Nat.mem_primeFactors]
      have hpa := Nat.mem_primeFactors.mp h.1
      exact ⟨hpa.1, hpa.2.1.trans (Nat.dvd_lcm_left a b),
        Nat.lcm_ne_zero ha hb⟩
    · refine ⟨?_, lt_of_lt_of_le h.2 (le_max_right _ _)⟩
      rw [Nat.mem_primeFactors]
      have hpb := Nat.mem_primeFactors.mp h.1
      exact ⟨hpb.1, hpb.2.1.trans (Nat.dvd_lcm_right a b),
        Nat.lcm_ne_zero ha hb⟩

end Erdos708
