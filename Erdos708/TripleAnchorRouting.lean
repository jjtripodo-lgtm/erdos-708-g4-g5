module

public import Erdos708.MatchingToCover
public import Erdos708.OneAnchor
public import Erdos708.TripleAnchor
public import Mathlib.Tactic

@[expose] public section

set_option maxHeartbeats 1000000

/-!
routing for the "three moduli have one available point" branch
of the Erdős #708 exhaustion.

A generic finite-set lemma extracts the common singleton.  One generic
number-theoretic wrapper then handles the normalized case p,q,r unique at x:
if the fourth modulus is also unique at x, use the trusted one-anchor theorem;
otherwise choose an off-anchor multiple of the fourth modulus and use the
trusted triple-anchor theorem.

The four possible deficient triples are reduced to this normalized wrapper by
permuting the modulus order; FourModuliCover is invariant under that
permutation because only the product matters.

This file is intentionally outside the trusted import graph and is NOT Banked.
-/

namespace Erdos708

open scoped BigOperators

theorem common_singleton_of_three_union_card_le_one_candidate
    {α : Type*} [DecidableEq α]
    (A B C : Finset α)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hcard : ((A ∪ B) ∪ C).card ≤ 1) :
    ∃ x,
      x ∈ A ∧ x ∈ B ∧ x ∈ C ∧
      (∀ z ∈ A, z = x) ∧
      (∀ z ∈ B, z = x) ∧
      (∀ z ∈ C, z = x) := by
  classical
  let U := (A ∪ B) ∪ C
  rcases hA with ⟨x, hxA⟩
  have hxU : x ∈ U := by
    dsimp [U]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hxA)
  have huniq : ∀ p ∈ U, ∀ q ∈ U, p = q :=
    Finset.card_le_one.mp (by simpa [U] using hcard)
  rcases hB with ⟨y, hyB⟩
  have hyU : y ∈ U := by
    dsimp [U]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hyB)
  have hyx : y = x := huniq y hyU x hxU
  have hxB : x ∈ B := by simpa [hyx] using hyB
  rcases hC with ⟨w, hwC⟩
  have hwU : w ∈ U := by
    dsimp [U]
    exact Finset.mem_union_right _ hwC
  have hwx : w = x := huniq w hwU x hxU
  have hxC : x ∈ C := by simpa [hwx] using hwC
  refine ⟨x, hxA, hxB, hxC, ?_, ?_, ?_⟩
  · intro z hz
    have hzU : z ∈ U := by
      dsimp [U]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
    exact huniq z hzU x hxU
  · intro z hz
    have hzU : z ∈ U := by
      dsimp [U]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
    exact huniq z hzU x hxU
  · intro z hz
    have hzU : z ∈ U := by
      dsimp [U]
      exact Finset.mem_union_right _ hz
    exact huniq z hzU x hxU

/--
Normalized anchor dispatcher: p,q,r are unique at x and s is the fourth
modulus.  Either s is also unique at x or it has an off-anchor multiple.
-/
theorem fourModuliCover_of_first_three_unique_anchor_candidate
    {L x : ℤ} {M p q r s : ℕ}
    (hpTwo : 2 ≤ p) (hqTwo : 2 ≤ q) (hrTwo : 2 ≤ r) (hsTwo : 2 ≤ s)
    (hpM : p ≤ M) (hqM : q ≤ M) (hrM : r ≤ M) (hsM : s ≤ M)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hxI : x ∈ integerInterval L M)
    (hx0 : x ≠ 0)
    (hpX : (p : ℤ) ∣ x)
    (hqX : (q : ℤ) ∣ x)
    (hrX : (r : ℤ) ∣ x)
    (huniqueP :
      ∀ z, z ∈ integerInterval L M → (p : ℤ) ∣ z → z = x)
    (huniqueQ :
      ∀ z, z ∈ integerInterval L M → (q : ℤ) ∣ z → z = x)
    (huniqueR :
      ∀ z, z ∈ integerInterval L M → (r : ℤ) ∣ z → z = x) :
    FourModuliCover L M p q r s := by
  classical
  by_cases huniqueS :
      ∀ z, z ∈ integerInterval L M → (s : ℤ) ∣ z → z = x
  · obtain ⟨yS, hySI, hsYS⟩ :=
      exists_interval_multiple_of_le_candidate
        (L := L) (M := M) (d := s) (by omega) hsM
    have hsX : (s : ℤ) ∣ x := by
      simpa [huniqueS yS hySI hsYS] using hsYS
    let A : Fin 4 → ℕ := fourModulus p q r s
    have hATwo : ∀ i, 2 ≤ A i := by
      intro i
      fin_cases i <;> simp [A, fourModulus, hpTwo, hqTwo, hrTwo, hsTwo]
    have hAM : ∀ i, A i ≤ M := by
      intro i
      fin_cases i <;> simp [A, fourModulus, hpM, hqM, hrM, hsM]
    have hAInj : Function.Injective A := by
      intro i j hij
      exact fourModulus_injective_candidate hpq hpr hps hqr hqs hrs
        (by simpa [A] using hij)
    have hxDiv : ∀ i, (A i : ℤ) ∣ x := by
      intro i
      fin_cases i <;> simp [A, fourModulus, hpX, hqX, hrX, hsX]
    have huniq : ∀ i z, z ∈ integerInterval L M →
        (A i : ℤ) ∣ z → z = x := by
      intro i z hzI hzD
      fin_cases i
      · exact huniqueP z hzI (by simpa [A, fourModulus] using hzD)
      · exact huniqueQ z hzI (by simpa [A, fourModulus] using hzD)
      · exact huniqueR z hzI (by simpa [A, fourModulus] using hzD)
      · exact huniqueS z hzI (by simpa [A, fourModulus] using hzD)
    obtain ⟨y, hyInj, hyBasic, hpay⟩ :=
      one_anchor_four_moduli A hATwo hAM hAInj hxI hx0 hxDiv huniq
    have hpay' :
        (p : ℤ) * (q : ℤ) * (r : ℤ) * (s : ℤ) ∣
          x * ∏ i : Fin 4, y i := by
      have hprod : (∏ i : Fin 4, (A i : ℤ)) =
          (p : ℤ) * (q : ℤ) * (r : ℤ) * (s : ℤ) := by
        simp [Fin.prod_univ_succ, A, fourModulus, mul_assoc]
      rw [hprod] at hpay
      exact hpay
    exact fourModuliCover_of_anchor_plus_four_candidate
      hxI y hyInj hyBasic hpay'
  · push_neg at huniqueS
    rcases huniqueS with ⟨y, hyI, hsY, hyx⟩
    have hpPos : 0 < p := by omega
    have hqPos : 0 < q := by omega
    have hrPos : 0 < r := by omega
    have htriple :=
      triple_anchor_four_moduli
        hpPos hqPos hrPos
        hpM hqM hrM
        hpq hpr hqr
        hxI hyI (Ne.symm hyx)
        hpX hqX hrX hsY
        huniqueP huniqueQ huniqueR
    exact fourModuliCover_of_triple_anchor_candidate
      hxI hyI (Ne.symm hyx) htriple

/-- The concrete triple 0,1,2 is confined to one point. -/
theorem fourModuliCover_of_012_deficiency_candidate
    {L : ℤ} {M a b c d : ℕ}
    (haTwo : 2 ≤ a) (hbTwo : 2 ≤ b) (hcTwo : 2 ≤ c) (hdTwo : 2 ≤ d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hzero : (0 : ℤ) ∉ integerInterval L M)
    (hcard :
      ((fourMultipleCandidates L M a b c d 0 ∪
        fourMultipleCandidates L M a b c d 1) ∪
        fourMultipleCandidates L M a b c d 2).card ≤ 1) :
    FourModuliCover L M a b c d := by
  have hne :=
    fourMultipleCandidates_nonempty_candidate
      (L := L) (by omega) (by omega) (by omega) (by omega)
      haM hbM hcM hdM
  obtain ⟨x, hx0C, hx1C, hx2C, hu0, hu1, hu2⟩ :=
    common_singleton_of_three_union_card_le_one_candidate
      (fourMultipleCandidates L M a b c d 0)
      (fourMultipleCandidates L M a b c d 1)
      (fourMultipleCandidates L M a b c d 2)
      (hne 0) (hne 1) (hne 2) hcard
  have hx0 := mem_fourMultipleCandidates_candidate.mp hx0C
  have hx1 := mem_fourMultipleCandidates_candidate.mp hx1C
  have hx2 := mem_fourMultipleCandidates_candidate.mp hx2C
  have haX : (a : ℤ) ∣ x := by simpa [fourModulus] using hx0.2
  have hbX : (b : ℤ) ∣ x := by simpa [fourModulus] using hx1.2
  have hcX : (c : ℤ) ∣ x := by simpa [fourModulus] using hx2.2
  have hxNe0 : x ≠ 0 := by
    intro hx
    apply hzero
    simpa [hx] using hx0.1
  have hua :
      ∀ z, z ∈ integerInterval L M → (a : ℤ) ∣ z → z = x := by
    intro z hzI hzD
    apply hu0 z
    exact mem_fourMultipleCandidates_candidate.mpr
      ⟨hzI, by simpa [fourModulus] using hzD⟩
  have hub :
      ∀ z, z ∈ integerInterval L M → (b : ℤ) ∣ z → z = x := by
    intro z hzI hzD
    apply hu1 z
    exact mem_fourMultipleCandidates_candidate.mpr
      ⟨hzI, by simpa [fourModulus] using hzD⟩
  have huc :
      ∀ z, z ∈ integerInterval L M → (c : ℤ) ∣ z → z = x := by
    intro z hzI hzD
    apply hu2 z
    exact mem_fourMultipleCandidates_candidate.mpr
      ⟨hzI, by simpa [fourModulus] using hzD⟩
  exact fourModuliCover_of_first_three_unique_anchor_candidate
    haTwo hbTwo hcTwo hdTwo
    haM hbM hcM hdM
    hab hac had hbc hbd hcd
    hx0.1 hxNe0 haX hbX hcX hua hub huc

/-- Normalize an arbitrary deficient triple among Fin 4 to one of the four
unordered triples. -/
theorem normalize_triple_deficiency_fin_four_candidate
    (C : Fin 4 → Finset ℤ)
    (h :
      ∃ i j k : Fin 4,
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        ((C i ∪ C j) ∪ C k).card ≤ 1) :
    ((C 0 ∪ C 1) ∪ C 2).card ≤ 1 ∨
    ((C 0 ∪ C 1) ∪ C 3).card ≤ 1 ∨
    ((C 0 ∪ C 2) ∪ C 3).card ≤ 1 ∨
    ((C 1 ∪ C 2) ∪ C 3).card ≤ 1 := by
  rcases h with ⟨i, j, k, hij, hik, hjk, hcard⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals simp_all [Finset.union_assoc, Finset.union_comm,
    Finset.union_left_comm]
  all_goals
    first
    | apply Or.inl
      convert hcard using 1
      congr 1
      ext z
      simp only [Finset.mem_union]
      tauto
    | apply Or.inr
      apply Or.inl
      convert hcard using 1
      congr 1
      ext z
      simp only [Finset.mem_union]
      tauto
    | apply Or.inr
      apply Or.inr
      apply Or.inl
      convert hcard using 1
      congr 1
      ext z
      simp only [Finset.mem_union]
      tauto
    | apply Or.inr
      apply Or.inr
      apply Or.inr
      convert hcard using 1
      congr 1
      ext z
      simp only [Finset.mem_union]
      tauto

/-- Route any deficient triple to the normalized 0,1,2 theorem by permuting
the modulus order and then use product invariance to restore a,b,c,d. -/
theorem fourModuliCover_of_triple_deficiency_candidate
    {L : ℤ} {M a b c d : ℕ}
    (haTwo : 2 ≤ a) (hbTwo : 2 ≤ b) (hcTwo : 2 ≤ c) (hdTwo : 2 ≤ d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hzero : (0 : ℤ) ∉ integerInterval L M)
    (h :
      ∃ i j k : Fin 4,
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        ((fourMultipleCandidates L M a b c d i ∪
          fourMultipleCandidates L M a b c d j) ∪
          fourMultipleCandidates L M a b c d k).card ≤ 1) :
    FourModuliCover L M a b c d := by
  have hn :=
    normalize_triple_deficiency_fin_four_candidate
      (fourMultipleCandidates L M a b c d) h
  rcases hn with h012 | h013 | h023 | h123
  · exact fourModuliCover_of_012_deficiency_candidate
      haTwo hbTwo hcTwo hdTwo
      haM hbM hcM hdM
      hab hac had hbc hbd hcd hzero h012
  · have hp : FourModuliCover L M a b d c := by
      apply fourModuliCover_of_012_deficiency_candidate
        haTwo hbTwo hdTwo hcTwo
        haM hbM hdM hcM
        hab had hac hbd hbc (Ne.symm hcd) hzero
      simpa [fourMultipleCandidates, fourModulus,
        Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using h013
    apply fourModuliCover_of_same_product_candidate
      (a' := a) (b' := b) (c' := d) (d' := c) (by ring) hp
  · have hp : FourModuliCover L M a c d b := by
      apply fourModuliCover_of_012_deficiency_candidate
        haTwo hcTwo hdTwo hbTwo
        haM hcM hdM hbM
        hac had hab hcd (Ne.symm hbc) (Ne.symm hbd) hzero
      simpa [fourMultipleCandidates, fourModulus,
        Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using h023
    apply fourModuliCover_of_same_product_candidate
      (a' := a) (b' := c) (c' := d) (d' := b) (by ring) hp
  · have hp : FourModuliCover L M b c d a := by
      apply fourModuliCover_of_012_deficiency_candidate
        hbTwo hcTwo hdTwo haTwo
        hbM hcM hdM haM
        hbc hbd (Ne.symm hab) hcd (Ne.symm hac) (Ne.symm had) hzero
      simpa [fourMultipleCandidates, fourModulus,
        Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using h123
    apply fourModuliCover_of_same_product_candidate
      (a' := b) (b' := c) (c' := d) (d' := a) (by ring) hp

end Erdos708
