module

public import Erdos708.MixedHall
public import Mathlib.Tactic

@[expose] public section

/-!
Order-reduction wrappers for the mixed Hall cases.

The internal mixed Hall candidates use numerical ordering to simplify proofs.
Multiplicity patterns themselves do not carry that order. These wrappers are
remove ordering hypotheses before final Hall assembly. This module is part of
the trusted SDR dependency graph.
-/

namespace Erdos708

theorem mixed_rrs_candidate_union_not_two_unordered_candidate
    {L : ℤ} {M r s : ℕ} {q : ℤ}
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s)
    (hMrr : 3 * r ≤ M) (hMs : 2 * s ≤ M)
    (hq : q = 1 ∨ q = -1)
    (hqr : q * (r : ℤ) ∈ integerInterval L M)
    (hqs : q * (s : ℤ) ∈ integerInterval L M)
    (hcard :
      ((integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z) ∪
        (integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)).card ≤ 2) : False := by
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · exact mixed_rrs_candidate_union_not_two
      hL hU hr hrs hMrr hMs hq hqr hqs hcard
  · classical
    let Ar := (integerInterval L M).filter
      (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z)
    let As := (integerInterval L M).filter
      (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)
    have hqrNe : q * (r : ℤ) ≠ q * (s : ℤ) := by
      rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
    have hqrAr : q * (r : ℤ) ∈ Ar := by
      refine Finset.mem_filter.mpr ⟨hqr, ?_⟩
      constructor
      · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
      · rcases hq with hq | hq <;> rw [hq] <;> simp
    have hqsAs : q * (s : ℤ) ∈ As := by
      refine Finset.mem_filter.mpr ⟨hqs, ?_⟩
      constructor
      · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
      · rcases hq with hq | hq <;> rw [hq] <;> simp
    have hpairSub :
        ({q * (r : ℤ), q * (s : ℤ)} : Finset ℤ) ⊆ Ar ∪ As := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · subst z
        exact Finset.mem_union_left _ hqrAr
      · subst z
        exact Finset.mem_union_right _ hqsAs
    have hpairCard :
        ({q * (r : ℤ), q * (s : ℤ)} : Finset ℤ).card = 2 := by
      simp [hqrNe]
    have hEq :
        ({q * (r : ℤ), q * (s : ℤ)} : Finset ℤ) = Ar ∪ As :=
      Finset.eq_of_subset_of_card_le hpairSub (by
        calc
          (Ar ∪ As).card ≤ 2 := by simpa [Ar, As] using hcard
          _ = ({q * (r : ℤ), q * (s : ℤ)} : Finset ℤ).card :=
            hpairCard.symm)
    have hArTwo : 2 ≤ Ar.card := by
      have h := card_nonzero_multiples_ge
        (L := L) (M := M) (d := r) (k := 2)
        hL hU hr hMrr
      simpa [Ar] using h
    have hqsAr : q * (s : ℤ) ∈ Ar := by
      by_contra hnot
      have hArSub : Ar ⊆ {q * (r : ℤ)} := by
        intro z hz
        have hzUnion : z ∈ Ar ∪ As := Finset.mem_union_left _ hz
        rw [← hEq] at hzUnion
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzUnion
        rcases hzUnion with hzR | hzS
        · exact Finset.mem_singleton.mpr hzR
        · subst z
          exact False.elim (hnot hz)
      have hle := Finset.card_le_card hArSub
      simp at hle
      omega
    have hdivInt : (r : ℤ) ∣ q * (s : ℤ) :=
      (Finset.mem_filter.mp hqsAr).2.2
    have hdivInt' : (r : ℤ) ∣ (s : ℤ) := by
      rcases hq with hq | hq
      · simpa [hq] using hdivInt
      · simpa [hq] using hdivInt
    have hdiv : r ∣ s := by exact_mod_cast hdivInt'
    have hrsLe : r ≤ s := Nat.le_of_dvd hs hdiv
    omega

theorem mixed_rrst_smaller_singleton_impossible_candidate
    {L : ℤ} {M r u v : ℕ} {q : ℤ}
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (hr : 0 < r) (hu : 0 < u) (hv : 0 < v)
    (hur : u < r) (hrv : r ≠ v) (huv : u ≠ v)
    (hMrr : 3 * r ≤ M) (hMu : 2 * u ≤ M) (hMv : 2 * v ≤ M)
    (hq : q = 1 ∨ q = -1)
    (hqr : q * (r : ℤ) ∈ integerInterval L M)
    (hqu : q * (u : ℤ) ∈ integerInterval L M)
    (hqv : q * (v : ℤ) ∈ integerInterval L M)
    (hcard :
      ((((integerInterval L M).filter
            (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z) ∪
          (integerInterval L M).filter
            (fun z => z ≠ 0 ∧ (u : ℤ) ∣ z)) ∪
        (integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (v : ℤ) ∣ z)).card ≤ 3)) : False := by
  classical
  let Ar := (integerInterval L M).filter
    (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z)
  let Au := (integerInterval L M).filter
    (fun z => z ≠ 0 ∧ (u : ℤ) ∣ z)
  let Av := (integerInterval L M).filter
    (fun z => z ≠ 0 ∧ (v : ℤ) ∣ z)
  have hzero : (0 : ℤ) ∈ integerInterval L M := by
    rw [mem_integerInterval]
    constructor <;> omega
  have hqrAr : q * (r : ℤ) ∈ Ar := by
    refine Finset.mem_filter.mpr ⟨hqr, ?_⟩
    constructor
    · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
    · rcases hq with hq | hq <;> rw [hq] <;> simp
  have hquAu : q * (u : ℤ) ∈ Au := by
    refine Finset.mem_filter.mpr ⟨hqu, ?_⟩
    constructor
    · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
    · rcases hq with hq | hq <;> rw [hq] <;> simp
  have hqvAv : q * (v : ℤ) ∈ Av := by
    refine Finset.mem_filter.mpr ⟨hqv, ?_⟩
    constructor
    · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
    · rcases hq with hq | hq <;> rw [hq] <;> simp
  have hqrNeQu : q * (r : ℤ) ≠ q * (u : ℤ) := by
    rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
  have hqrNeQv : q * (r : ℤ) ≠ q * (v : ℤ) := by
    rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
  have hquNeQv : q * (u : ℤ) ≠ q * (v : ℤ) := by
    rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
  have htripleCard :
      ({q * (r : ℤ), q * (u : ℤ), q * (v : ℤ)} : Finset ℤ).card = 3 := by
    simp [hqrNeQu, hqrNeQv, hquNeQv]
  have htripleSub :
      ({q * (r : ℤ), q * (u : ℤ), q * (v : ℤ)} : Finset ℤ) ⊆
        (Ar ∪ Au) ∪ Av := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz
    · subst z
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hqrAr)
    · subst z
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hquAu)
    · subst z
      exact Finset.mem_union_right _ hqvAv
  have hEq :
      ({q * (r : ℤ), q * (u : ℤ), q * (v : ℤ)} : Finset ℤ) =
        (Ar ∪ Au) ∪ Av :=
    Finset.eq_of_subset_of_card_le htripleSub (by
      calc
        ((Ar ∪ Au) ∪ Av).card ≤ 3 := by simpa [Ar, Au, Av] using hcard
        _ = ({q * (r : ℤ), q * (u : ℤ), q * (v : ℤ)} : Finset ℤ).card :=
          htripleCard.symm)
  have hsmall :
      (Ar ∪ Au) ∪ Av ⊆
        ({q * (r : ℤ), q * (u : ℤ), q * (v : ℤ)} : Finset ℤ) := by
    rw [← hEq]
  have hArTwo : 2 ≤ Ar.card := by
    have h := card_nonzero_multiples_ge
      (L := L) (M := M) (d := r) (k := 2)
      hL hU hr hMrr
    simpa [Ar] using h
  have hqvAr : q * (v : ℤ) ∈ Ar := by
    by_contra hnotV
    have hArSub : Ar ⊆ {q * (r : ℤ)} := by
      intro z hz
      have hzUnion : z ∈ (Ar ∪ Au) ∪ Av :=
        Finset.mem_union_left _ (Finset.mem_union_left _ hz)
      have hzTriple := hsmall hzUnion
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzTriple
      rcases hzTriple with hzR | hzU | hzV
      · exact Finset.mem_singleton.mpr hzR
      · subst z
        have hdivInt : (r : ℤ) ∣ q * (u : ℤ) :=
          (Finset.mem_filter.mp hz).2.2
        have hdivU : r ∣ u := by
          have h' : (r : ℤ) ∣ (u : ℤ) := by
            rcases hq with hq | hq
            · simpa [hq] using hdivInt
            · simpa [hq] using hdivInt
          exact_mod_cast h'
        have hru : r ≤ u := Nat.le_of_dvd hu hdivU
        omega
      · subst z
        exact False.elim (hnotV hz)
    have hle := Finset.card_le_card hArSub
    simp at hle
    omega
  have hdivVInt : (r : ℤ) ∣ q * (v : ℤ) :=
    (Finset.mem_filter.mp hqvAr).2.2
  have hdivVInt' : (r : ℤ) ∣ (v : ℤ) := by
    rcases hq with hq | hq
    · simpa [hq] using hdivVInt
    · simpa [hq] using hdivVInt
  have hdivV : r ∣ v := by exact_mod_cast hdivVInt'
  have hrvLe : r ≤ v := Nat.le_of_dvd hv hdivV
  have hrvLt : r < v := lt_of_le_of_ne hrvLe hrv
  have htwo : 2 * r ≤ v := by
    rcases dvd_iff_exists_eq_mul_right.mp hdivV with ⟨k, hk⟩
    have hkTwo : 2 ≤ k := by
      by_contra h
      have hkle : k ≤ 1 := by omega
      interval_cases k <;> simp_all
    rw [hk]
    calc
      2 * r = r * 2 := by omega
      _ ≤ r * k := Nat.mul_le_mul_left r hkTwo
  have hdoubleMem :=
    integerInterval_mem_signed_double hzero hqv hq htwo
  have hdoubleAr : q * ((2 * r : ℕ) : ℤ) ∈ Ar := by
    refine Finset.mem_filter.mpr ⟨hdoubleMem, ?_⟩
    constructor
    · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
    · rcases hq with hq | hq
      · rw [hq]
        exact ⟨2, by push_cast; ring⟩
      · rw [hq]
        exact ⟨-2, by push_cast; ring⟩
  have hdoubleChoice :=
    hsmall (Finset.mem_union_left _ (Finset.mem_union_left _ hdoubleAr))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdoubleChoice
  have hvEq : v = 2 * r := by
    rcases hdoubleChoice with hR | hU | hV
    · rcases hq with hq | hq <;> rw [hq] at hR <;> push_cast at hR <;> omega
    · rcases hq with hq | hq <;> rw [hq] at hU <;> push_cast at hU <;> omega
    · rcases hq with hq | hq <;> rw [hq] at hV <;> push_cast at hV <;> omega
  have hMfour : 4 * r ≤ M := by
    rw [hvEq] at hMv
    nlinarith
  have hArThree : 3 ≤ Ar.card := by
    have h := card_nonzero_multiples_ge
      (L := L) (M := M) (d := r) (k := 3)
      hL hU hr hMfour
    simpa [Ar] using h
  have hArSub : Ar ⊆ {q * (r : ℤ), q * (v : ℤ)} := by
    intro z hz
    have hzUnion : z ∈ (Ar ∪ Au) ∪ Av :=
      Finset.mem_union_left _ (Finset.mem_union_left _ hz)
    have hzTriple := hsmall hzUnion
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzTriple
    rcases hzTriple with hzR | hzU | hzV
    · exact Finset.mem_insert.mpr (Or.inl hzR)
    · subst z
      have hdivInt : (r : ℤ) ∣ q * (u : ℤ) :=
        (Finset.mem_filter.mp hz).2.2
      have hdivU : r ∣ u := by
        have h' : (r : ℤ) ∣ (u : ℤ) := by
          rcases hq with hq | hq
          · simpa [hq] using hdivInt
          · simpa [hq] using hdivInt
        exact_mod_cast h'
      have hru : r ≤ u := Nat.le_of_dvd hu hdivU
      omega
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hzV))
  have hle := Finset.card_le_card hArSub
  have hpairLe : ({q * (r : ℤ), q * (v : ℤ)} : Finset ℤ).card ≤ 2 :=
    Finset.card_le_two
  omega

theorem mixed_rrst_candidate_union_not_three_unordered_candidate
    {L : ℤ} {M r s t : ℕ} {q : ℤ}
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hMrr : 3 * r ≤ M) (hMs : 2 * s ≤ M) (hMt : 2 * t ≤ M)
    (hq : q = 1 ∨ q = -1)
    (hqr : q * (r : ℤ) ∈ integerInterval L M)
    (hqs : q * (s : ℤ) ∈ integerInterval L M)
    (hqt : q * (t : ℤ) ∈ integerInterval L M)
    (hcard :
      ((((integerInterval L M).filter
            (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z) ∪
          (integerInterval L M).filter
            (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)) ∪
        (integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (t : ℤ) ∣ z)).card ≤ 3)) : False := by
  by_cases hsr : s < r
  · exact mixed_rrst_smaller_singleton_impossible_candidate
      hL hU hr hs ht hsr hrt hst hMrr hMs hMt hq hqr hqs hqt hcard
  · by_cases htr : t < r
    · have hcard' :
        ((((integerInterval L M).filter
              (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z) ∪
            (integerInterval L M).filter
              (fun z => z ≠ 0 ∧ (t : ℤ) ∣ z)) ∪
          (integerInterval L M).filter
            (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)).card ≤ 3) := by
        simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hcard
      exact mixed_rrst_smaller_singleton_impossible_candidate
        hL hU hr ht hs htr hrs (Ne.symm hst)
        hMrr hMt hMs hq hqr hqt hqs hcard'
    · have hrsLt : r < s := by omega
      have hrtLt : r < t := by omega
      rcases lt_or_gt_of_ne hst with hstLt | htsLt
      · exact mixed_rrst_candidate_union_not_three_candidate
          hL hU hr hrsLt hstLt hMrr hMs hMt hq hqr hqs hqt hcard
      · have hcard' :
          ((((integerInterval L M).filter
                (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z) ∪
              (integerInterval L M).filter
                (fun z => z ≠ 0 ∧ (t : ℤ) ∣ z)) ∪
            (integerInterval L M).filter
              (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)).card ≤ 3) := by
          simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hcard
        exact mixed_rrst_candidate_union_not_three_candidate
          hL hU hr hrtLt htsLt hMrr hMt hMs hq hqr hqt hqs hcard'

theorem mixed_rrss_candidate_union_not_three_unordered_candidate
    {L : ℤ} {M r s : ℕ} {q : ℤ}
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s)
    (hMrr : 3 * r ≤ M) (hMss : 3 * s ≤ M)
    (hq : q = 1 ∨ q = -1)
    (hqr : q * (r : ℤ) ∈ integerInterval L M)
    (hqs : q * (s : ℤ) ∈ integerInterval L M)
    (hcard :
      ((integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z) ∪
        (integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)).card ≤ 3) : False := by
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · exact mixed_rrss_candidate_union_not_three_candidate
      hL hU hr hrs hMrr hMss hq hqr hqs hcard
  · have hcard' :
      ((integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z) ∪
        (integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z)).card ≤ 3 := by
      simpa [Finset.union_comm] using hcard
    exact mixed_rrss_candidate_union_not_three_candidate
      hL hU hs hsr hMss hMrr hq hqs hqr hcard'

theorem mixed_rrrs_candidate_union_not_three_unordered_candidate
    {L : ℤ} {M r s b : ℕ} {q : ℤ}
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s)
    (hMrrr : 4 * r ≤ M) (hMs : 2 * s ≤ M)
    (a : Fin 3 → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haDiv : ∀ i, r ∣ a i)
    (haProper : ∀ i, a i ≠ r)
    (haM : ∀ i, a i ≤ M)
    (haInj : Function.Injective a)
    (hbPos : 0 < b)
    (hsb : s ∣ b)
    (hbProper : b ≠ s)
    (hbM : b ≤ M)
    (hbDistinct : ∀ i, b ≠ a i)
    (hq : q = 1 ∨ q = -1)
    (hqr : q * (r : ℤ) ∈ integerInterval L M)
    (hqs : q * (s : ℤ) ∈ integerInterval L M)
    (hcard :
      ((integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z) ∪
        (integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)).card ≤ 3) : False := by
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · exact mixed_rrrs_candidate_union_not_three_candidate
      hL hU hr hrs hMrrr hMs
      a haPos haDiv haProper haM haInj
      hbPos hsb hbProper hbM hbDistinct
      hq hqr hqs hcard
  · classical
    let Ar := (integerInterval L M).filter
      (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z)
    let As := (integerInterval L M).filter
      (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)
    have hqsAs : q * (s : ℤ) ∈ As := by
      refine Finset.mem_filter.mpr ⟨hqs, ?_⟩
      constructor
      · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
      · rcases hq with hq | hq <;> rw [hq] <;> simp
    have hArThree : 3 ≤ Ar.card := by
      have h := card_nonzero_multiples_ge
        (L := L) (M := M) (d := r) (k := 3)
        hL hU hr hMrrr
      simpa [Ar] using h
    have hqsAr : q * (s : ℤ) ∈ Ar := by
      by_contra hnot
      have hinsert :
          insert (q * (s : ℤ)) Ar ⊆ Ar ∪ As := by
        intro z hz
        simp only [Finset.mem_insert] at hz
        rcases hz with hz | hz
        · subst z
          exact Finset.mem_union_right _ hqsAs
        · exact Finset.mem_union_left _ hz
      have hle := Finset.card_le_card hinsert
      have hinsertCard :
          (insert (q * (s : ℤ)) Ar).card = Ar.card + 1 := by
        rw [Finset.card_insert_of_notMem hnot]
      rw [hinsertCard] at hle
      have hunion : (Ar ∪ As).card ≤ 3 := by
        simpa [Ar, As] using hcard
      omega
    have hdivInt : (r : ℤ) ∣ q * (s : ℤ) :=
      (Finset.mem_filter.mp hqsAr).2.2
    have hdivInt' : (r : ℤ) ∣ (s : ℤ) := by
      rcases hq with hq | hq
      · simpa [hq] using hdivInt
      · simpa [hq] using hdivInt
    have hdiv : r ∣ s := by exact_mod_cast hdivInt'
    have hrsLe : r ≤ s := Nat.le_of_dvd hs hdiv
    omega

end Erdos708
