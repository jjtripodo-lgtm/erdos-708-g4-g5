module

public import Erdos708.HallFinFour
public import Erdos708.MixedHallOrder
public import Erdos708.ProperDivisorAssembly
public import Mathlib.Tactic

@[expose] public section

/-!
Fin-4 proper-divisor Hall bounds for the four-label SDR theorem.

This file stages the singleton, pair, and triple Hall inequalities for the
actual four-divisor family. The only remaining Hall inequality after these is
the full four-way union, which requires the five multiplicity patterns.

This module is part of the trusted SDR dependency graph.
-/

namespace Erdos708

def properDivisorCandidates4
    (L : ℤ) (M : ℕ) (r : Fin 4 → ℕ) (i : Fin 4) : Finset ℤ :=
  properDivisorCandidates L M 0 r i

theorem proper_divisor_small_candidate
    {M : ℕ}
    (a r : Fin 4 → ℕ)
    (haPos : ∀ i, 0 < a i)
    (hrPos : ∀ i, 0 < r i)
    (hrDiv : ∀ i, r i ∣ a i)
    (hrProper : ∀ i, a i ≠ r i)
    (haM : ∀ i, a i ≤ M) :
    ∀ i, 2 * r i ≤ M := by
  intro i
  exact (two_mul_le_of_dvd_ne_candidate
    (hrPos i) (haPos i) (hrDiv i) (hrProper i)).trans (haM i)

theorem proper_divisor_singleton_union_bound_candidate
    {L : ℤ} {M : ℕ}
    (r : Fin 4 → ℕ)
    (hrPos : ∀ i, 0 < r i)
    (hrSmall : ∀ i, 2 * r i ≤ M)
    (q : ℤ) (hq : q = 1 ∨ q = -1)
    (hqmem : ∀ i, q * (r i : ℤ) ∈ integerInterval L M) :
    ∀ i, 1 ≤ (properDivisorCandidates4 L M r i).card := by
  intro i
  have hqNZ : q ≠ 0 := by rcases hq with hq | hq <;> simp [hq]
  have hrNZ : (r i : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt (hrPos i))
  have hprodNZ : q * (r i : ℤ) ≠ 0 := mul_ne_zero hqNZ hrNZ
  apply Finset.one_le_card.mpr
  refine ⟨q * (r i : ℤ), ?_⟩
  simp only [properDivisorCandidates4, properDivisorCandidates,
    Finset.mem_filter]
  exact ⟨hqmem i, hprodNZ, by rcases hq with hq | hq <;> rw [hq] <;> simp⟩

theorem proper_divisor_pair_union_bound_candidate
    {L : ℤ} {M : ℕ}
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (a r : Fin 4 → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haInj : Function.Injective a)
    (hrPos : ∀ i, 0 < r i)
    (hrDiv : ∀ i, r i ∣ a i)
    (hrProper : ∀ i, a i ≠ r i)
    (haM : ∀ i, a i ≤ M)
    (q : ℤ) (hq : q = 1 ∨ q = -1)
    (hqmem : ∀ i, q * (r i : ℤ) ∈ integerInterval L M) :
    ∀ i j, i ≠ j →
      2 ≤ (properDivisorCandidates4 L M r i ∪
        properDivisorCandidates4 L M r j).card := by
  classical
  intro i j hij
  have hqNZ : q ≠ 0 := by rcases hq with hq | hq <;> simp [hq]
  have hrNZ (i : Fin 4) : (r i : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hrPos i))
  have hprodNZ (i : Fin 4) : q * (r i : ℤ) ≠ 0 := mul_ne_zero hqNZ (hrNZ i)
  by_cases hrij : r i = r j
  · let S : Finset (Fin 4) := {i, j}
    have hS : S.Nonempty := by
      exact ⟨i, by simp [S]⟩
    have hbound :=
      repeated_proper_moduli_finset_force_bound_candidate
        (M := M) (d := r i) S hS (hrPos i)
        a haPos
        (fun k hk => by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with hki | hkj
          · subst k; exact hrDiv i
          · subst k; simpa [← hrij] using hrDiv j)
        (fun k hk => by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with hki | hkj
          · subst k; exact hrProper i
          · subst k; simpa [← hrij] using hrProper j)
        haM haInj
    have hScard : S.card = 2 := by simp [S, hij]
    have hthree : 3 * r i ≤ M := by nlinarith [hbound, hScard]
    have hcardRi :
        2 ≤ ((integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r i : ℤ) ∣ z)).card := by
      exact card_nonzero_multiples_ge
        hL hU (hrPos i) hthree
    have hsub :
        properDivisorCandidates4 L M r i ⊆
          properDivisorCandidates4 L M r i ∪
            properDivisorCandidates4 L M r j :=
      Finset.subset_union_left
    have hle := Finset.card_le_card hsub
    have hCi :
        (properDivisorCandidates4 L M r i).card =
          ((integerInterval L M).filter
            (fun z => z ≠ 0 ∧ (r i : ℤ) ∣ z)).card := by
      rfl
    rw [hCi] at hle
    omega
  · let zi : ℤ := q * (r i : ℤ)
    let zj : ℤ := q * (r j : ℤ)
    have hzi :
        zi ∈ properDivisorCandidates4 L M r i := by
      simp only [properDivisorCandidates4, properDivisorCandidates,
        Finset.mem_filter, zi]
      exact ⟨hqmem i, hprodNZ i,
        by rcases hq with hq | hq <;> rw [hq] <;> simp⟩
    have hzj :
        zj ∈ properDivisorCandidates4 L M r j := by
      simp only [properDivisorCandidates4, properDivisorCandidates,
        Finset.mem_filter, zj]
      exact ⟨hqmem j, hprodNZ j,
        by rcases hq with hq | hq <;> rw [hq] <;> simp⟩
    have hne : zi ≠ zj := by
      dsimp [zi, zj]
      rcases hq with hq | hq
      · rw [hq]
        have hcast : (r i : ℤ) ≠ (r j : ℤ) := by exact_mod_cast hrij
        simpa using hcast
      · rw [hq]
        intro h
        apply hrij
        have hcast : (r i : ℤ) = (r j : ℤ) := by linarith
        exact_mod_cast hcast
    have hpair :
        ({zi, zj} : Finset ℤ) ⊆
          properDivisorCandidates4 L M r i ∪
            properDivisorCandidates4 L M r j := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_union_left _ hzi
      · exact Finset.mem_union_right _ hzj
    have hle := Finset.card_le_card hpair
    simpa [hne] using hle

theorem proper_divisor_triple_union_bound_candidate
    {L : ℤ} {M : ℕ}
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (a r : Fin 4 → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haInj : Function.Injective a)
    (hrPos : ∀ i, 0 < r i)
    (hrDiv : ∀ i, r i ∣ a i)
    (hrProper : ∀ i, a i ≠ r i)
    (haM : ∀ i, a i ≤ M)
    (q : ℤ) (hq : q = 1 ∨ q = -1)
    (hqmem : ∀ i, q * (r i : ℤ) ∈ integerInterval L M) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      3 ≤ ((properDivisorCandidates4 L M r i ∪
        properDivisorCandidates4 L M r j) ∪
        properDivisorCandidates4 L M r k).card := by
  classical
  intro i j k hij hik hjk
  have hqNZ : q ≠ 0 := by rcases hq with hq | hq <;> simp [hq]
  have hrNZ (i : Fin 4) : (r i : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hrPos i))
  have hprodNZ (i : Fin 4) : q * (r i : ℤ) ≠ 0 := mul_ne_zero hqNZ (hrNZ i)
  let Ci := properDivisorCandidates4 L M r i
  let Cj := properDivisorCandidates4 L M r j
  let Ck := properDivisorCandidates4 L M r k
  by_cases hijr : r i = r j
  · by_cases hikr : r i = r k
    · let S : Finset (Fin 4) := {i, j, k}
      have hS : S.Nonempty := ⟨i, by simp [S]⟩
      have hbound :=
        repeated_proper_moduli_finset_force_bound_candidate
          (M := M) (d := r i) S hS (hrPos i)
          a haPos
          (fun u hu => by
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with hui | huJ | huK
            · subst u; exact hrDiv i
            · subst u; simpa [← hijr] using hrDiv j
            · subst u; simpa [← hikr] using hrDiv k)
          (fun u hu => by
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with hui | huJ | huK
            · subst u; exact hrProper i
            · subst u; simpa [← hijr] using hrProper j
            · subst u; simpa [← hikr] using hrProper k)
          haM haInj
      have hScard : S.card = 3 := by simp [S, hij, hik, hjk]
      have hfour : 4 * r i ≤ M := by nlinarith [hbound, hScard]
      have hcard :
          3 ≤ ((integerInterval L M).filter
            (fun z => z ≠ 0 ∧ (r i : ℤ) ∣ z)).card :=
        card_nonzero_multiples_ge hL hU (hrPos i) hfour
      have hsub : Ci ⊆ (Ci ∪ Cj) ∪ Ck :=
        fun z hz => Finset.mem_union_left _
          (Finset.mem_union_left _ hz)
      have hle := Finset.card_le_card hsub
      have hCi :
          Ci.card = ((integerInterval L M).filter
            (fun z => z ≠ 0 ∧ (r i : ℤ) ∣ z)).card := by rfl
      rw [hCi] at hle
      exact hcard.trans hle
    · have hrik : r i ≠ r k := hikr
      have hrjk : r j ≠ r k := by
        intro h
        apply hikr
        exact hijr.trans h
      let S : Finset (Fin 4) := {i, j}
      have hS : S.Nonempty := ⟨i, by simp [S]⟩
      have hbound :=
        repeated_proper_moduli_finset_force_bound_candidate
          (M := M) (d := r i) S hS (hrPos i)
          a haPos
          (fun u hu => by
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with hui | huJ
            · subst u; exact hrDiv i
            · subst u; simpa [← hijr] using hrDiv j)
          (fun u hu => by
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with hui | huJ
            · subst u; exact hrProper i
            · subst u; simpa [← hijr] using hrProper j)
          haM haInj
      have hScard : S.card = 2 := by simp [S, hij]
      have hthree : 3 * r i ≤ M := by nlinarith [hbound, hScard]
      have hkSmall :=
        (two_mul_le_of_dvd_ne_candidate
          (hrPos k) (haPos k) (hrDiv k) (hrProper k)).trans (haM k)
      by_contra hgoal
      have hgoal' : ¬ 3 ≤ ((Ci ∪ Cj) ∪ Ck).card := by
        simpa [Ci, Cj, Ck] using hgoal
      have hle : ((Ci ∪ Cj) ∪ Ck).card ≤ 2 := by omega
      have hraw :
          (((integerInterval L M).filter
              (fun z => z ≠ 0 ∧ (r i : ℤ) ∣ z)) ∪
            (integerInterval L M).filter
              (fun z => z ≠ 0 ∧ (r k : ℤ) ∣ z)).card ≤ 2 := by
        have hCiCj : Ci = Cj := by
          ext z
          simp [Ci, Cj, properDivisorCandidates4, properDivisorCandidates, hijr]
        have hpair : (Ci ∪ Ck).card ≤ 2 := by
          simpa [Finset.union_assoc, hCiCj] using hle
        simpa [Ci, Ck, properDivisorCandidates4, properDivisorCandidates] using hpair
      exact mixed_rrs_candidate_union_not_two_unordered_candidate
        hL hU (hrPos i) (hrPos k) hrik
        hthree hkSmall hq (hqmem i) (hqmem k) hraw
  · by_cases hikr : r i = r k
    · have hrij : r i ≠ r j := hijr
      have hjkr : r j ≠ r k := by
        intro h
        apply hijr
        exact hikr.trans h.symm
      let S : Finset (Fin 4) := {i, k}
      have hS : S.Nonempty := ⟨i, by simp [S]⟩
      have hbound :=
        repeated_proper_moduli_finset_force_bound_candidate
          (M := M) (d := r i) S hS (hrPos i)
          a haPos
          (fun u hu => by
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with hui | huK
            · subst u; exact hrDiv i
            · subst u; simpa [← hikr] using hrDiv k)
          (fun u hu => by
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with hui | huK
            · subst u; exact hrProper i
            · subst u; simpa [← hikr] using hrProper k)
          haM haInj
      have hScard : S.card = 2 := by simp [S, hik]
      have hthree : 3 * r i ≤ M := by nlinarith [hbound, hScard]
      have hjSmall :=
        (two_mul_le_of_dvd_ne_candidate
          (hrPos j) (haPos j) (hrDiv j) (hrProper j)).trans (haM j)
      by_contra hgoal
      have hgoal' : ¬ 3 ≤ ((Ci ∪ Cj) ∪ Ck).card := by
        simpa [Ci, Cj, Ck] using hgoal
      have hle : ((Ci ∪ Cj) ∪ Ck).card ≤ 2 := by omega
      have hraw :
          (((integerInterval L M).filter
              (fun z => z ≠ 0 ∧ (r i : ℤ) ∣ z)) ∪
            (integerInterval L M).filter
              (fun z => z ≠ 0 ∧ (r j : ℤ) ∣ z)).card ≤ 2 := by
          have hCiCk : Ci = Ck := by
            ext z
            simp [Ci, Ck, properDivisorCandidates4, properDivisorCandidates, hikr]
          have hpair : (Ci ∪ Cj).card ≤ 2 := by
            simpa [Finset.union_assoc, Finset.union_left_comm,
              Finset.union_comm, hCiCk] using hle
          simpa [Ci, Cj, properDivisorCandidates4, properDivisorCandidates] using hpair
      exact mixed_rrs_candidate_union_not_two_unordered_candidate
        hL hU (hrPos i) (hrPos j) hrij
        hthree hjSmall hq (hqmem i) (hqmem j) hraw
    · by_cases hjkr : r j = r k
      · have hrji : r j ≠ r i := Ne.symm hijr
        let S : Finset (Fin 4) := {j, k}
        have hS : S.Nonempty := ⟨j, by simp [S]⟩
        have hbound :=
          repeated_proper_moduli_finset_force_bound_candidate
            (M := M) (d := r j) S hS (hrPos j)
            a haPos
            (fun u hu => by
              simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu
              rcases hu with huJ | huK
              · subst u; exact hrDiv j
              · subst u; simpa [← hjkr] using hrDiv k)
            (fun u hu => by
              simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu
              rcases hu with huJ | huK
              · subst u; exact hrProper j
              · subst u; simpa [← hjkr] using hrProper k)
            haM haInj
        have hScard : S.card = 2 := by simp [S, hjk]
        have hthree : 3 * r j ≤ M := by nlinarith [hbound, hScard]
        have hiSmall :=
          (two_mul_le_of_dvd_ne_candidate
            (hrPos i) (haPos i) (hrDiv i) (hrProper i)).trans (haM i)
        by_contra hgoal
        have hgoal' : ¬ 3 ≤ ((Ci ∪ Cj) ∪ Ck).card := by
          simpa [Ci, Cj, Ck] using hgoal
        have hle : ((Ci ∪ Cj) ∪ Ck).card ≤ 2 := by omega
        have hraw :
            (((integerInterval L M).filter
                (fun z => z ≠ 0 ∧ (r j : ℤ) ∣ z)) ∪
              (integerInterval L M).filter
                (fun z => z ≠ 0 ∧ (r i : ℤ) ∣ z)).card ≤ 2 := by
          have hCjCk : Cj = Ck := by
            ext z
            simp [Cj, Ck, properDivisorCandidates4, properDivisorCandidates, hjkr]
          have hpair : (Cj ∪ Ci).card ≤ 2 := by
            simpa [Finset.union_assoc, Finset.union_left_comm,
              Finset.union_comm, hCjCk] using hle
          simpa [Cj, Ci, properDivisorCandidates4, properDivisorCandidates] using hpair
        exact mixed_rrs_candidate_union_not_two_unordered_candidate
          hL hU (hrPos j) (hrPos i) hrji
          hthree hiSmall hq (hqmem j) (hqmem i) hraw
      · let zi : ℤ := q * (r i : ℤ)
        let zj : ℤ := q * (r j : ℤ)
        let zk : ℤ := q * (r k : ℤ)
        have hzi : zi ∈ Ci := by
          simp only [Ci, properDivisorCandidates4, properDivisorCandidates,
            Finset.mem_filter, zi]
          exact ⟨hqmem i, hprodNZ i,
            by rcases hq with hq | hq <;> rw [hq] <;> simp⟩
        have hzj : zj ∈ Cj := by
          simp only [Cj, properDivisorCandidates4, properDivisorCandidates,
            Finset.mem_filter, zj]
          exact ⟨hqmem j, hprodNZ j,
            by rcases hq with hq | hq <;> rw [hq] <;> simp⟩
        have hzk : zk ∈ Ck := by
          simp only [Ck, properDivisorCandidates4, properDivisorCandidates,
            Finset.mem_filter, zk]
          exact ⟨hqmem k, hprodNZ k,
            by rcases hq with hq | hq <;> rw [hq] <;> simp⟩
        have hzij : zi ≠ zj := by
          dsimp [zi, zj]
          rcases hq with hq | hq
          · rw [hq]
            have hcast : (r i : ℤ) ≠ (r j : ℤ) := by exact_mod_cast hijr
            simpa using hcast
          · rw [hq]
            intro h
            apply hijr
            have hcast : (r i : ℤ) = (r j : ℤ) := by linarith
            exact_mod_cast hcast
        have hizk : zi ≠ zk := by
          dsimp [zi, zk]
          rcases hq with hq | hq
          · rw [hq]
            have hcast : (r i : ℤ) ≠ (r k : ℤ) := by exact_mod_cast hikr
            simpa using hcast
          · rw [hq]
            intro h
            apply hikr
            have hcast : (r i : ℤ) = (r k : ℤ) := by linarith
            exact_mod_cast hcast
        have hjzk : zj ≠ zk := by
          dsimp [zj, zk]
          rcases hq with hq | hq
          · rw [hq]
            have hcast : (r j : ℤ) ≠ (r k : ℤ) := by exact_mod_cast hjkr
            simpa using hcast
          · rw [hq]
            intro h
            apply hjkr
            have hcast : (r j : ℤ) = (r k : ℤ) := by linarith
            exact_mod_cast hcast
        have hset :
            ({zi, zj, zk} : Finset ℤ) ⊆ (Ci ∪ Cj) ∪ Ck := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ hzi)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hzj)
          · exact Finset.mem_union_right _ hzk
        have hle := Finset.card_le_card hset
        simpa [hzij, hizk, hjzk] using hle

end Erdos708
