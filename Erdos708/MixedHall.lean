module

public import Erdos708.RepeatedDivisor
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Tactic

@[expose] public section

/-!
Mixed proper-divisor Hall cases for the four-label SDR theorem.

This module is part of the trusted SDR dependency graph. Internal helper names
retain their historical `_candidate` suffix.
-/

namespace Erdos708

/-- General signed intermediate-multiple version of
\`integerInterval_mem_signed_double\`.

If zero and the signed endpoint q*s are in the interval, every signed k*d
between them is also in the interval. -/
theorem integerInterval_mem_signed_multiple_candidate
    {L : ℤ} {M d s k : ℕ} {q : ℤ}
    (hzero : (0 : ℤ) ∈ integerInterval L M)
    (hs : q * (s : ℤ) ∈ integerInterval L M)
    (hq : q = 1 ∨ q = -1)
    (hks : k * d ≤ s) :
    q * ((k * d : ℕ) : ℤ) ∈ integerInterval L M := by
  rcases hq with hq | hq
  · subst q
    have hs' : (s : ℤ) ∈ integerInterval L M := by simpa using hs
    have hbetween :
        min (0 : ℤ) (s : ℤ) ≤ ((k * d : ℕ) : ℤ) ∧
          ((k * d : ℕ) : ℤ) ≤ max (0 : ℤ) (s : ℤ) := by
      constructor <;> push_cast <;> omega
    have h := integerInterval_mem_of_between hzero hs' hbetween
    simpa using h
  · subst q
    have hs' : -(s : ℤ) ∈ integerInterval L M := by simpa using hs
    have hbetween :
        min (-(s : ℤ)) (0 : ℤ) ≤ -((k * d : ℕ) : ℤ) ∧
          -((k * d : ℕ) : ℤ) ≤ max (-(s : ℤ)) (0 : ℤ) := by
      constructor <;> push_cast <;> omega
    have h := integerInterval_mem_of_between hs' hzero hbetween
    simpa using h

/-- Candidate proof for the \`(r,r,s,t)\` Hall-deficient pattern.

Under the proper-divisor size bounds, the union of nonzero r-, s-, and
t-multiples cannot have only three points.

Mathematical spine:
1. the union is exactly the three signed first multiples;
2. two r-multiples force s itself to be an r-multiple;
3. interval convexity then forces s=2r;
4. the third r-multiple forces t=3r;
5. properness of t gives 6r<=M, producing at least five r-multiples.
-/
theorem mixed_rrst_candidate_union_not_three_candidate
    {L : ℤ} {M r s t : ℕ} {q : ℤ}
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (hr : 0 < r) (hrs : r < s) (hst : s < t)
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
  classical
  let Ar := (integerInterval L M).filter
    (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z)
  let As := (integerInterval L M).filter
    (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)
  let At := (integerInterval L M).filter
    (fun z => z ≠ 0 ∧ (t : ℤ) ∣ z)
  have hzero : (0 : ℤ) ∈ integerInterval L M := by
    rw [mem_integerInterval]
    constructor <;> omega
  have hqrNeQs : q * (r : ℤ) ≠ q * (s : ℤ) := by
    rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
  have hqrNeQt : q * (r : ℤ) ≠ q * (t : ℤ) := by
    rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
  have hqsNeQt : q * (s : ℤ) ≠ q * (t : ℤ) := by
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
  have hqtAt : q * (t : ℤ) ∈ At := by
    refine Finset.mem_filter.mpr ⟨hqt, ?_⟩
    constructor
    · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
    · rcases hq with hq | hq <;> rw [hq] <;> simp
  have htripleCard :
      ({q * (r : ℤ), q * (s : ℤ), q * (t : ℤ)} : Finset ℤ).card = 3 := by
    simp [hqrNeQs, hqrNeQt, hqsNeQt]
  have htripleSub :
      ({q * (r : ℤ), q * (s : ℤ), q * (t : ℤ)} : Finset ℤ) ⊆
        (Ar ∪ As) ∪ At := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz
    · subst z
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hqrAr)
    · subst z
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hqsAs)
    · subst z
      exact Finset.mem_union_right _ hqtAt
  have hEq :
      ({q * (r : ℤ), q * (s : ℤ), q * (t : ℤ)} : Finset ℤ) =
        (Ar ∪ As) ∪ At :=
    Finset.eq_of_subset_of_card_le htripleSub (by
      calc
        ((Ar ∪ As) ∪ At).card ≤ 3 := by simpa [Ar, As, At] using hcard
        _ = ({q * (r : ℤ), q * (s : ℤ), q * (t : ℤ)} : Finset ℤ).card :=
          htripleCard.symm)
  have hsmall :
      (Ar ∪ As) ∪ At ⊆
        ({q * (r : ℤ), q * (s : ℤ), q * (t : ℤ)} : Finset ℤ) := by
    rw [← hEq]
  have hArTwo : 2 ≤ Ar.card := by
    have h := card_nonzero_multiples_ge
      (L := L) (M := M) (d := r) (k := 2)
      hL hU hr hMrr
    simpa [Ar] using h

  have hqsAr : q * (s : ℤ) ∈ Ar := by
    by_contra hnotS
    have hqtAr : q * (t : ℤ) ∈ Ar := by
      by_contra hnotT
      have hArSub : Ar ⊆ {q * (r : ℤ)} := by
        intro z hz
        have hzUnion : z ∈ (Ar ∪ As) ∪ At :=
          Finset.mem_union_left _ (Finset.mem_union_left _ hz)
        have hzTriple := hsmall hzUnion
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzTriple
        rcases hzTriple with hzR | hzS | hzT
        · exact Finset.mem_singleton.mpr hzR
        · subst z
          exact False.elim (hnotS hz)
        · subst z
          exact False.elim (hnotT hz)
      have hle := Finset.card_le_card hArSub
      simp at hle
      omega
    have hdivInt : (r : ℤ) ∣ q * (t : ℤ) :=
      (Finset.mem_filter.mp hqtAr).2.2
    have hdivInt' : (r : ℤ) ∣ (t : ℤ) := by
      rcases hq with hq | hq
      · simpa [hq] using hdivInt
      · simpa [hq] using hdivInt
    have hdivT : r ∣ t := by exact_mod_cast hdivInt'
    have hdoubleLower : 2 * r ≤ t := by
      rcases (dvd_iff_exists_eq_mul_right.mp hdivT) with ⟨u, hu⟩
      have huLower : 2 ≤ u := by
        by_contra h
        have huLe : u ≤ 1 := by omega
        by_cases hu0 : u = 0
        · rw [hu0] at hu
          simp at hu
          omega
        · have hu1 : u = 1 := by omega
          rw [hu, hu1] at hst
          simp at hst
          omega
      rw [hu]
      calc
        2 * r = r * 2 := by omega
        _ ≤ r * u := Nat.mul_le_mul_left r huLower
    have hdoubleMem :=
      integerInterval_mem_signed_double hzero hqt hq hdoubleLower
    have hdoubleAr : q * ((2 * r : ℕ) : ℤ) ∈ Ar := by
      refine Finset.mem_filter.mpr ⟨hdoubleMem, ?_⟩
      constructor
      · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
      · rcases hq with hq | hq
        · rw [hq]
          exact ⟨2, by push_cast; ring⟩
        · rw [hq]
          exact ⟨-2, by push_cast; ring⟩
    have hdoubleTriple :=
      hsmall (Finset.mem_union_left _ (Finset.mem_union_left _ hdoubleAr))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdoubleTriple
    rcases hdoubleTriple with hR | hS | hT
    · rcases hq with hq | hq <;> rw [hq] at hR <;> push_cast at hR <;> omega
    · apply hnotS
      rw [← hS]
      exact hdoubleAr
    · have htEq : t = 2 * r := by
        rcases hq with hq | hq <;> rw [hq] at hT <;> push_cast at hT <;> omega
      have hMfour : 4 * r ≤ M := by
        rw [htEq] at hMt
        nlinarith
      have hArThree : 3 ≤ Ar.card := by
        have h := card_nonzero_multiples_ge
          (L := L) (M := M) (d := r) (k := 3)
          hL hU hr hMfour
        simpa [Ar] using h
      have hArSub : Ar ⊆ {q * (r : ℤ), q * (t : ℤ)} := by
        intro z hz
        have hzUnion : z ∈ (Ar ∪ As) ∪ At :=
          Finset.mem_union_left _ (Finset.mem_union_left _ hz)
        have hzTriple := hsmall hzUnion
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzTriple
        rcases hzTriple with hzR | hzS | hzT
        · exact Finset.mem_insert.mpr (Or.inl hzR)
        · subst z
          exact False.elim (hnotS hz)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hzT))
      have hle := Finset.card_le_card hArSub
      have hpairLe :
          ({q * (r : ℤ), q * (t : ℤ)} : Finset ℤ).card ≤ 2 :=
        Finset.card_le_two
      omega

  have hdivSInt : (r : ℤ) ∣ q * (s : ℤ) :=
    (Finset.mem_filter.mp hqsAr).2.2
  have hdivSInt' : (r : ℤ) ∣ (s : ℤ) := by
    rcases hq with hq | hq
    · simpa [hq] using hdivSInt
    · simpa [hq] using hdivSInt
  have hdivS : r ∣ s := by exact_mod_cast hdivSInt'
  have hdoubleLowerS : 2 * r ≤ s := by
    rcases (dvd_iff_exists_eq_mul_right.mp hdivS) with ⟨u, hu⟩
    have huLower : 2 ≤ u := by
      by_contra h
      have huLe : u ≤ 1 := by omega
      interval_cases u <;> simp_all
    rw [hu]
    calc
      2 * r = r * 2 := by omega
      _ ≤ r * u := Nat.mul_le_mul_left r huLower
  have hdoubleMemS :=
    integerInterval_mem_signed_double hzero hqs hq hdoubleLowerS
  have hsNotGeThree : ¬ 3 * r ≤ s := by
    intro hthree
    have hdoubleAr : q * ((2 * r : ℕ) : ℤ) ∈ Ar := by
      refine Finset.mem_filter.mpr ⟨hdoubleMemS, ?_⟩
      constructor
      · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
      · rcases hq with hq | hq
        · rw [hq]
          exact ⟨2, by push_cast; ring⟩
        · rw [hq]
          exact ⟨-2, by push_cast; ring⟩
    have hdoubleTriple :=
      hsmall (Finset.mem_union_left _ (Finset.mem_union_left _ hdoubleAr))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdoubleTriple
    rcases hdoubleTriple with hR | hS | hT
    · rcases hq with hq | hq <;> rw [hq] at hR <;> push_cast at hR <;> omega
    · rcases hq with hq | hq <;> rw [hq] at hS <;> push_cast at hS <;> omega
    · rcases hq with hq | hq <;> rw [hq] at hT <;> push_cast at hT <;> omega
  have hslt : s < 3 * r := by omega
  have hsEq : s = 2 * r := by
    rcases (dvd_iff_exists_eq_mul_right.mp hdivS) with ⟨u, hu⟩
    have huLower : 2 ≤ u := by
      by_contra h
      have huLe : u ≤ 1 := by omega
      interval_cases u <;> simp_all
    have huUpper : u < 3 := by
      rw [hu] at hslt
      nlinarith
    have huEq : u = 2 := by omega
    rw [hu, huEq]
    ring

  have hMfour : 4 * r ≤ M := by
    rw [hsEq] at hMs
    nlinarith
  have hArThree : 3 ≤ Ar.card := by
    have h := card_nonzero_multiples_ge
      (L := L) (M := M) (d := r) (k := 3)
      hL hU hr hMfour
    simpa [Ar] using h

  have hqtAr : q * (t : ℤ) ∈ Ar := by
    by_contra hnotT
    have hArSub : Ar ⊆ {q * (r : ℤ), q * (s : ℤ)} := by
      intro z hz
      have hzUnion : z ∈ (Ar ∪ As) ∪ At :=
        Finset.mem_union_left _ (Finset.mem_union_left _ hz)
      have hzTriple := hsmall hzUnion
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzTriple
      rcases hzTriple with hzR | hzS | hzT
      · exact Finset.mem_insert.mpr (Or.inl hzR)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hzS))
      · subst z
        exact False.elim (hnotT hz)
    have hle := Finset.card_le_card hArSub
    have hpairLe :
        ({q * (r : ℤ), q * (s : ℤ)} : Finset ℤ).card ≤ 2 :=
      Finset.card_le_two
    omega

  have hdivTInt : (r : ℤ) ∣ q * (t : ℤ) :=
    (Finset.mem_filter.mp hqtAr).2.2
  have hdivTInt' : (r : ℤ) ∣ (t : ℤ) := by
    rcases hq with hq | hq
    · simpa [hq] using hdivTInt
    · simpa [hq] using hdivTInt
  have hdivT : r ∣ t := by exact_mod_cast hdivTInt'
  rcases (dvd_iff_exists_eq_mul_right.mp hdivT) with ⟨u, hu⟩
  have huLower : 3 ≤ u := by
    by_contra h
    have huLe : u ≤ 2 := by omega
    have htLe : t ≤ 2 * r := by
      rw [hu]
      calc
        r * u ≤ r * 2 := Nat.mul_le_mul_left r huLe
        _ = 2 * r := by omega
    have htwoLt : 2 * r < t := by
      rw [← hsEq]
      exact hst
    omega
  have htripleLower : 3 * r ≤ t := by
    rw [hu]
    calc
      3 * r = r * 3 := by omega
      _ ≤ r * u := Nat.mul_le_mul_left r huLower
  have htripleMem :=
    integerInterval_mem_signed_multiple_candidate
      (L := L) (M := M) (d := r) (s := t) (k := 3) (q := q)
      hzero hqt hq htripleLower
  have htripleAr : q * ((3 * r : ℕ) : ℤ) ∈ Ar := by
    refine Finset.mem_filter.mpr ⟨htripleMem, ?_⟩
    constructor
    · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
    · rcases hq with hq | hq
      · rw [hq]
        exact ⟨3, by push_cast; ring⟩
      · rw [hq]
        exact ⟨-3, by push_cast; ring⟩
  have htripleChoice :=
    hsmall (Finset.mem_union_left _ (Finset.mem_union_left _ htripleAr))
  simp only [Finset.mem_insert, Finset.mem_singleton] at htripleChoice
  have htEq : t = 3 * r := by
    rcases htripleChoice with hR | hS | hT
    · rcases hq with hq | hq <;> rw [hq] at hR <;> push_cast at hR <;> omega
    · rw [hsEq] at hS
      rcases hq with hq | hq <;> rw [hq] at hS <;> push_cast at hS <;> omega
    · rcases hq with hq | hq <;> rw [hq] at hT <;> push_cast at hT <;> omega

  have hMsix : 6 * r ≤ M := by
    rw [htEq] at hMt
    nlinarith
  have hArFive : 5 ≤ Ar.card := by
    have h := card_nonzero_multiples_ge
      (L := L) (M := M) (d := r) (k := 5)
      hL hU hr hMsix
    simpa [Ar] using h
  have hArSub :
      Ar ⊆ ({q * (r : ℤ), q * (s : ℤ), q * (t : ℤ)} : Finset ℤ) := by
    intro z hz
    exact hsmall (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
  have hle := Finset.card_le_card hArSub
  rw [htripleCard] at hle
  omega

end Erdos708


namespace Erdos708

/-- Candidate interval diameter lemma used by the mixed rrss disjointness
argument. If zero and z lie in an M-point integer interval, then |z| < M. -/
theorem integerInterval_abs_lt_length_candidate
    {L z : ℤ} {M : ℕ}
    (hzero : (0 : ℤ) ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) :
    |z| < (M : ℤ) := by
  rw [mem_integerInterval] at hzero hz
  rcases hzero with ⟨hL0, h0U⟩
  rcases hz with ⟨hLz, hzU⟩
  by_cases hzn : 0 ≤ z
  · rw [abs_of_nonneg hzn]
    omega
  · have hznonpos : z ≤ 0 := by omega
    rw [abs_of_nonpos hznonpos]
    omega

/-- Candidate arithmetic kernel for the hard rrss branch. -/
theorem lcm_ge_four_mul_of_three_mul_lt_four_mul_candidate
    {r s : ℕ}
    (hr : 0 < r) (hrs : r < s)
    (hratio : 3 * s < 4 * r) :
    4 * r ≤ Nat.lcm r s := by
  by_contra h
  have hlcmLt : Nat.lcm r s < 4 * r := by omega
  have hrlcm : r ∣ Nat.lcm r s := Nat.dvd_lcm_left r s
  have hslcm : s ∣ Nat.lcm r s := Nat.dvd_lcm_right r s
  have hspos : 0 < s := lt_trans hr hrs
  have hlcmPos : 0 < Nat.lcm r s := by
    exact Nat.pos_of_ne_zero
      (Nat.lcm_ne_zero (Nat.ne_of_gt hr) (Nat.ne_of_gt hspos))
  rcases dvd_iff_exists_eq_mul_right.mp hrlcm with ⟨k, hk⟩
  have hsLe : s ≤ Nat.lcm r s := Nat.le_of_dvd hlcmPos hslcm
  have hkLower : 2 ≤ k := by
    have hmul : r * 1 < r * k := by
      calc
        r * 1 = r := by simp
        _ < s := hrs
        _ ≤ Nat.lcm r s := hsLe
        _ = r * k := hk
    have hkgt := Nat.lt_of_mul_lt_mul_left hmul
    omega
  have hkUpper : k < 4 := by
    have hmul : r * k < r * 4 := by
      calc
        r * k = Nat.lcm r s := hk.symm
        _ < 4 * r := hlcmLt
        _ = r * 4 := by omega
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hkCases : k = 2 ∨ k = 3 := by omega
  rcases hkCases with hk2 | hk3
  · have hlcmEq : Nat.lcm r s = 2 * r := by
      calc
        Nat.lcm r s = r * k := hk
        _ = 2 * r := by rw [hk2]; omega
    rcases dvd_iff_exists_eq_mul_right.mp hslcm with ⟨u, hu⟩
    have huPos : 0 < u := by
      by_contra h
      have hu0 : u = 0 := by omega
      rw [hu0] at hu
      simp at hu
      omega
    have huLt : u < 2 := by
      by_contra h
      have hu2 : 2 ≤ u := by omega
      have h2s : 2 * s ≤ s * u := by
        calc
          2 * s = s * 2 := by omega
          _ ≤ s * u := Nat.mul_le_mul_left s hu2
      rw [← hu, hlcmEq] at h2s
      omega
    have huEq : u = 1 := by omega
    have hsEq : s = 2 * r := by
      rw [hlcmEq, huEq] at hu
      simp at hu
      omega
    rw [hsEq] at hratio
    omega
  · have hlcmEq : Nat.lcm r s = 3 * r := by
      calc
        Nat.lcm r s = r * k := hk
        _ = 3 * r := by rw [hk3]; omega
    rcases dvd_iff_exists_eq_mul_right.mp hslcm with ⟨u, hu⟩
    have huPos : 0 < u := by
      by_contra h
      have hu0 : u = 0 := by omega
      rw [hu0] at hu
      simp at hu
      omega
    have huLt : u < 3 := by
      by_contra h
      have hu3 : 3 ≤ u := by omega
      have h3s : 3 * s ≤ s * u := by
        calc
          3 * s = s * 3 := by omega
          _ ≤ s * u := Nat.mul_le_mul_left s hu3
      rw [← hu, hlcmEq] at h3s
      omega
    have huCases : u = 1 ∨ u = 2 := by omega
    rcases huCases with hu1 | hu2
    · rw [hlcmEq, hu1] at hu
      omega
    · rw [hlcmEq, hu2] at hu
      omega

/-- Candidate proof for the mixed rrss Hall-deficient pattern. -/
theorem mixed_rrss_candidate_union_not_three_candidate
    {L : ℤ} {M r s : ℕ} {q : ℤ}
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (hr : 0 < r) (hrs : r < s)
    (hMrr : 3 * r ≤ M) (hMss : 3 * s ≤ M)
    (hq : q = 1 ∨ q = -1)
    (hqr : q * (r : ℤ) ∈ integerInterval L M)
    (hqs : q * (s : ℤ) ∈ integerInterval L M)
    (hcard :
      ((integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z) ∪
        (integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)).card ≤ 3) : False := by
  classical
  let Ar := (integerInterval L M).filter
    (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z)
  let As := (integerInterval L M).filter
    (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)
  have hzero : (0 : ℤ) ∈ integerInterval L M := by
    rw [mem_integerInterval]
    constructor <;> omega
  have hqsAs : q * (s : ℤ) ∈ As := by
    refine Finset.mem_filter.mpr ⟨hqs, ?_⟩
    constructor
    · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
    · rcases hq with hq | hq <;> rw [hq] <;> simp
  have hArTwo : 2 ≤ Ar.card := by
    have h := card_nonzero_multiples_ge
      (L := L) (M := M) (d := r) (k := 2)
      hL hU hr hMrr
    simpa [Ar] using h
  have hspos : 0 < s := lt_trans hr hrs
  have hAsTwo : 2 ≤ As.card := by
    have h := card_nonzero_multiples_ge
      (L := L) (M := M) (d := s) (k := 2)
      hL hU hspos hMss
    simpa [As] using h
  by_cases hMfour : 4 * r ≤ M
  · have hArThree : 3 ≤ Ar.card := by
      have h := card_nonzero_multiples_ge
        (L := L) (M := M) (d := r) (k := 3)
        hL hU hr hMfour
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
    have hdouble : 2 * r ≤ s := by
      rcases (dvd_iff_exists_eq_mul_right.mp hdiv) with ⟨u, hu⟩
      have huLower : 2 ≤ u := by
        by_contra h
        have huLe : u ≤ 1 := by omega
        interval_cases u <;> simp_all
      rw [hu]
      calc
        2 * r = r * 2 := by omega
        _ ≤ r * u := Nat.mul_le_mul_left r huLower
    have hMsix : 6 * r ≤ M := by
      nlinarith [hMss, hdouble]
    have hArFive : 5 ≤ Ar.card := by
      have h := card_nonzero_multiples_ge
        (L := L) (M := M) (d := r) (k := 5)
        hL hU hr hMsix
      simpa [Ar] using h
    have hsubset : Ar ⊆ Ar ∪ As := Finset.subset_union_left
    have hle := Finset.card_le_card hsubset
    have hunion : (Ar ∪ As).card ≤ 3 := by
      simpa [Ar, As] using hcard
    omega
  · have hMlt : M < 4 * r := by omega
    have hratio : 3 * s < 4 * r := lt_of_le_of_lt hMss hMlt
    have hlcm :
        4 * r ≤ Nat.lcm r s :=
      lcm_ge_four_mul_of_three_mul_lt_four_mul_candidate hr hrs hratio
    have hdisj : Disjoint Ar As := by
      refine Finset.disjoint_left.mpr ?_
      intro z hzR hzS
      have hzInterval : z ∈ integerInterval L M :=
        (Finset.mem_filter.mp hzR).1
      have hzNe : z ≠ 0 :=
        (Finset.mem_filter.mp hzR).2.1
      have hrz : (r : ℤ) ∣ z :=
        (Finset.mem_filter.mp hzR).2.2
      have hsz : (s : ℤ) ∣ z :=
        (Finset.mem_filter.mp hzS).2.2
      have hlcmdvd : (Nat.lcm r s : ℤ) ∣ z :=
        Int.coe_lcm_dvd hrz hsz
      have habsM :=
        integerInterval_abs_lt_length_candidate hzero hzInterval
      have hMltLcmNat : M < Nat.lcm r s :=
        lt_of_lt_of_le hMlt hlcm
      have hMltLcm : (M : ℤ) < (Nat.lcm r s : ℤ) := by
        exact_mod_cast hMltLcmNat
      have habsLcm : |z| < (Nat.lcm r s : ℤ) :=
        lt_trans habsM hMltLcm
      have hzZero :=
        Int.eq_zero_of_abs_lt_dvd hlcmdvd habsLcm
      exact hzNe hzZero
    have hcardEq :
        (Ar ∪ As).card = Ar.card + As.card :=
      Finset.card_union_of_disjoint hdisj
    have hunion : (Ar ∪ As).card ≤ 3 := by
      simpa [Ar, As] using hcard
    rw [hcardEq] at hunion
    omega

end Erdos708


namespace Erdos708

/-- Candidate coefficient pigeonhole used by the mixed rrrs Hall case.

Three distinct positive proper multiples of r, all below 5r, must use the
three available coefficients 2,3,4; in particular one is exactly 4r. -/
theorem three_proper_r_multiples_below_five_contain_four_candidate
    {r : ℕ}
    (hr : 0 < r)
    (a : Fin 3 → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haDiv : ∀ i, r ∣ a i)
    (haProper : ∀ i, a i ≠ r)
    (haLt : ∀ i, a i < 5 * r)
    (haInj : Function.Injective a) :
    ∃ i, a i = 4 * r := by
  classical
  let q : Fin 3 → ℕ := fun i =>
    Classical.choose (dvd_iff_exists_eq_mul_right.mp (haDiv i))
  have hqmul (i : Fin 3) : a i = r * q i :=
    Classical.choose_spec (dvd_iff_exists_eq_mul_right.mp (haDiv i))
  have hqPos (i : Fin 3) : 0 < q i := by
    have ha := haPos i
    rw [hqmul i] at ha
    by_contra h
    have hzero : q i = 0 := by omega
    simp [hzero] at ha
  have hqNeOne (i : Fin 3) : q i ≠ 1 := by
    intro h
    apply haProper i
    rw [hqmul i, h]
    simp
  have hqLower (i : Fin 3) : 2 ≤ q i := by
    have hp := hqPos i
    have hne := hqNeOne i
    omega
  have hqUpper (i : Fin 3) : q i ≤ 4 := by
    have hlt : r * q i < r * 5 := by
      calc
        r * q i = a i := (hqmul i).symm
        _ < 5 * r := haLt i
        _ = r * 5 := by omega
    have := Nat.lt_of_mul_lt_mul_left hlt
    omega
  have hqInj : Function.Injective q := by
    intro i j hij
    apply haInj
    calc
      a i = r * q i := hqmul i
      _ = r * q j := congrArg (fun n => r * n) hij
      _ = a j := (hqmul j).symm
  let image := Finset.univ.image q
  have hcardImage : image.card = 3 := by
    dsimp [image]
    simp [Finset.card_image_of_injective, hqInj]
  have himageSubset : image ⊆ Finset.Icc 2 4 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact Finset.mem_Icc.mpr ⟨hqLower i, hqUpper i⟩
  have hEq : image = Finset.Icc 2 4 := by
    apply Finset.eq_of_subset_of_card_le himageSubset
    simp [hcardImage]
  have hfour : 4 ∈ image := by
    rw [hEq]
    simp
  rcases Finset.mem_image.mp hfour with ⟨i, hi, hqi⟩
  refine ⟨i, ?_⟩
  rw [hqmul i, hqi]
  omega

/-- Candidate single-original coefficient lemma for the rrrs case.

A positive proper multiple of 2r that is still below 5r must be 4r. -/
theorem proper_two_r_multiple_below_five_eq_four_candidate
    {r b : ℕ}
    (hr : 0 < r)
    (hbPos : 0 < b)
    (hdiv : 2 * r ∣ b)
    (hproper : b ≠ 2 * r)
    (hlt : b < 5 * r) :
    b = 4 * r := by
  rcases dvd_iff_exists_eq_mul_right.mp hdiv with ⟨u, hu⟩
  have huPos : 0 < u := by
    have hb := hbPos
    rw [hu] at hb
    by_contra h
    have hu0 : u = 0 := by omega
    simp [hu0] at hb
  have huNeOne : u ≠ 1 := by
    intro hu1
    apply hproper
    rw [hu, hu1]
    simp
  have huLower : 2 ≤ u := by omega
  have huLtThree : u < 3 := by
    by_contra h
    have hu3 : 3 ≤ u := by omega
    have hlower : 6 * r ≤ b := by
      rw [hu]
      calc
        6 * r = (2 * r) * 3 := by ring
        _ ≤ (2 * r) * u := Nat.mul_le_mul_left (2 * r) hu3
    omega
  have huEq : u = 2 := by omega
  rw [hu, huEq]
  ring

/-- Candidate proof for the mixed rrrs Hall-deficient pattern.

The theorem deliberately carries the original moduli because the last
contradiction is not a statement about divisor labels alone: distinctness of
the four original moduli is essential. -/
theorem mixed_rrrs_candidate_union_not_three_candidate
    {L : ℤ} {M r s b : ℕ} {q : ℤ}
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (hr : 0 < r) (hrs : r < s)
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
  classical
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
  have hdouble : 2 * r ≤ s := by
    rcases (dvd_iff_exists_eq_mul_right.mp hdiv) with ⟨u, hu⟩
    have huLower : 2 ≤ u := by
      by_contra h
      have huLe : u ≤ 1 := by omega
      interval_cases u <;> simp_all
    rw [hu]
    calc
      2 * r = r * 2 := by omega
      _ ≤ r * u := Nat.mul_le_mul_left r huLower

  have hMltFive : M < 5 * r := by
    by_contra h
    have hMfive : 5 * r ≤ M := by omega
    have hArFour : 4 ≤ Ar.card := by
      have h' := card_nonzero_multiples_ge
        (L := L) (M := M) (d := r) (k := 4)
        hL hU hr hMfive
      simpa [Ar] using h'
    have hsubset : Ar ⊆ Ar ∪ As := Finset.subset_union_left
    have hle := Finset.card_le_card hsubset
    have hunion : (Ar ∪ As).card ≤ 3 := by
      simpa [Ar, As] using hcard
    omega

  have hsltThree : s < 3 * r := by
    by_contra h
    have hthree : 3 * r ≤ s := by omega
    have hsix : 6 * r ≤ M := by
      nlinarith [hMs, hthree]
    omega
  have hsEq : s = 2 * r := by
    rcases (dvd_iff_exists_eq_mul_right.mp hdiv) with ⟨u, hu⟩
    have huLower : 2 ≤ u := by
      by_contra h
      have huLe : u ≤ 1 := by omega
      interval_cases u <;> simp_all
    have huUpper : u < 3 := by
      rw [hu] at hsltThree
      nlinarith
    have huEq : u = 2 := by omega
    rw [hu, huEq]
    ring

  have haLt : ∀ i, a i < 5 * r := by
    intro i
    exact lt_of_le_of_lt (haM i) hMltFive
  obtain ⟨i, haiFour⟩ :=
    three_proper_r_multiples_below_five_contain_four_candidate
      hr a haPos haDiv haProper haLt haInj

  have htwoRDivB : 2 * r ∣ b := by
    rw [← hsEq]
    exact hsb
  have hbNotTwoR : b ≠ 2 * r := by
    rw [← hsEq]
    exact hbProper
  have hbLt : b < 5 * r :=
    lt_of_le_of_lt hbM hMltFive
  have hbFour :=
    proper_two_r_multiple_below_five_eq_four_candidate
      hr hbPos htwoRDivB hbNotTwoR hbLt
  apply hbDistinct i
  rw [hbFour, haiFour]

end Erdos708


namespace Erdos708

/-- Candidate common-side lemma for assembling the mixed Hall cases.

In an M-point integer interval containing zero, one of the two sides has enough
room to contain q*d for every positive d with 2*d<=M, using one common
q in {+1,-1}. -/
theorem exists_common_signed_first_multiple_candidate
    {L : ℤ} {M : ℕ}
    (hL : L ≤ 0)
    (hU : 0 ≤ L + (M : ℤ) - 1) :
    ∃ q : ℤ, (q = 1 ∨ q = -1) ∧
      ∀ d : ℕ, 0 < d → 2 * d ≤ M →
        q * (d : ℤ) ∈ integerInterval L M := by
  let U : ℤ := L + (M : ℤ) - 1
  have hspan : -L + U = (M : ℤ) - 1 := by
    dsimp [U]
    omega
  have hside : 2 * U ≥ (M : ℤ) - 1 ∨ 2 * (-L) ≥ (M : ℤ) - 1 := by
    omega
  by_cases hpos : 2 * U ≥ (M : ℤ) - 1
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro d hd hsmall
    have hdcast : 2 * (d : ℤ) ≤ (M : ℤ) := by exact_mod_cast hsmall
    have hdU : (d : ℤ) ≤ U := by omega
    rw [mem_integerInterval]
    constructor
    · have hdnonneg : 0 ≤ (d : ℤ) := by positivity
      simp
      omega
    · simpa [U] using hdU
  · have hneg : 2 * (-L) ≥ (M : ℤ) - 1 := by
      rcases hside with h | h <;> omega
    refine ⟨-1, Or.inr rfl, ?_⟩
    intro d hd hsmall
    have hdcast : 2 * (d : ℤ) ≤ (M : ℤ) := by exact_mod_cast hsmall
    have hdL : (d : ℤ) ≤ -L := by omega
    rw [mem_integerInterval]
    constructor
    · simp
      linarith
    · have hU0 : 0 ≤ U := by dsimp [U]; exact hU
      have hdpos : 0 < (d : ℤ) := by exact_mod_cast hd
      linarith

end Erdos708
