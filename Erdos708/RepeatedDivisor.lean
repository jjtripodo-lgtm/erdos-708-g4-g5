module

public import Erdos708.IntervalMultiples
public import Erdos708.ProperDivisorHall
public import Mathlib.Tactic

@[expose] public section

namespace Erdos708

/-- Distinct proper multiples of `d` force `(m+1)d` below their common
upper bound. -/
theorem repeated_proper_moduli_force_bound
    {m M d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (a : Fin m → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haDiv : ∀ i, d ∣ a i)
    (haProper : ∀ i, a i ≠ d)
    (haM : ∀ i, a i ≤ M)
    (haInj : Function.Injective a) :
    (m + 1) * d ≤ M := by
  classical
  by_contra hbound
  have hM : M < (m + 1) * d := by omega
  let q : Fin m → ℕ := fun i =>
    Classical.choose (dvd_iff_exists_eq_mul_right.mp (haDiv i))
  have hqmul (i : Fin m) : a i = d * q i :=
    Classical.choose_spec (dvd_iff_exists_eq_mul_right.mp (haDiv i))
  have hqPos (i : Fin m) : 0 < q i := by
    have ha := haPos i
    rw [hqmul i] at ha
    by_contra h
    have hzero : q i = 0 := by omega
    simp [hzero] at ha
  have hqNeOne (i : Fin m) : q i ≠ 1 := by
    intro h
    apply haProper i
    rw [hqmul i, h]
    simp
  have hqLower (i : Fin m) : 2 ≤ q i := by
    by_contra h
    have hqle : q i ≤ 1 := by omega
    by_cases hzero : q i = 0
    · have hpos := hqPos i
      omega
    · have hone : q i = 1 := by omega
      exact hqNeOne i hone
  have hqUpper (i : Fin m) : q i ≤ m := by
    have hmul : d * q i < d * (m + 1) := by
      calc
        d * q i = a i := (hqmul i).symm
        _ ≤ M := haM i
        _ < (m + 1) * d := hM
        _ = d * (m + 1) := Nat.mul_comm _ _
    have hq : q i < m + 1 := Nat.lt_of_mul_lt_mul_left hmul
    omega
  have hqInj : Function.Injective q := by
    intro i j hij
    apply haInj
    calc
      a i = d * q i := hqmul i
      _ = d * q j := congrArg (fun n => d * n) hij
      _ = a j := (hqmul j).symm
  let image := Finset.univ.image q
  have hcardImage : image.card = m := by
    dsimp [image]
    simp [Finset.card_image_of_injective, hqInj]
  have himageSubset : image ⊆ Finset.Icc 2 m := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact Finset.mem_Icc.mpr ⟨hqLower i, hqUpper i⟩
  have hcardIcc : (Finset.Icc 2 m).card < m := by
    simp
    omega
  have hle := Finset.card_le_card himageSubset
  omega

/-- The `(r,r,s)` Hall-deficient configuration is impossible.  The two
repeated `r` labels provide two nonzero `r`-multiples, while the `s` label
provides its signed first multiple.  If the union had only those two points,
then `s` would be an `r`-multiple; interval convexity forces `s=2r`, after
which properness gives a third `r`-multiple. -/
theorem mixed_rrs_candidate_union_not_two
    {L : ℤ} {M r s : ℕ} {q : ℤ}
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (hr : 0 < r) (hrs : r < s)
    (hMrr : 3 * r ≤ M) (hMs : 2 * s ≤ M)
    (hq : q = 1 ∨ q = -1)
    (hqr : q * (r : ℤ) ∈ integerInterval L M)
    (hqs : q * (s : ℤ) ∈ integerInterval L M)
    (hcard :
      ((integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z) ∪
        (integerInterval L M).filter
          (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)).card ≤ 2) : False := by
  classical
  let Ar := (integerInterval L M).filter
    (fun z => z ≠ 0 ∧ (r : ℤ) ∣ z)
  let As := (integerInterval L M).filter
    (fun z => z ≠ 0 ∧ (s : ℤ) ∣ z)
  have hzero : (0 : ℤ) ∈ integerInterval L M := by
    rw [mem_integerInterval]
    constructor <;> omega
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
  have hpairCard : ({q * (r : ℤ), q * (s : ℤ)} : Finset ℤ).card = 2 := by
    simp [hqrNe]
  have hpairSub : {q * (r : ℤ), q * (s : ℤ)} ⊆ Ar ∪ As := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · subst z
      exact Finset.mem_union_left _ hqrAr
    · subst z
      exact Finset.mem_union_right _ hqsAs
  have hEq : {q * (r : ℤ), q * (s : ℤ)} = Ar ∪ As :=
    Finset.eq_of_subset_of_card_le hpairSub (by
      calc
        (Ar ∪ As).card ≤ 2 := by simpa [Ar, As] using hcard
        _ = ({q * (r : ℤ), q * (s : ℤ)} : Finset ℤ).card := hpairCard.symm)
  have hsmall : Ar ∪ As ⊆ {q * (r : ℤ), q * (s : ℤ)} := by
    rw [← hEq]
  have hArTwo : 2 ≤ Ar.card := by
    have h := card_nonzero_multiples_ge hL hU (Nat.pos_of_ne_zero (by omega : r ≠ 0)) hMrr
    simpa [Ar] using h
  have hqsAr : q * (s : ℤ) ∈ Ar := by
    by_contra hnot
    have hArSub : Ar ⊆ {q * (r : ℤ)} := by
      intro z hz
      have hzUnion : z ∈ Ar ∪ As := Finset.mem_union_left _ hz
      have hzPair := hsmall hzUnion
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
      rcases hzPair with hzq | hzs
      · exact Finset.mem_singleton.mpr hzq
      · subst z
        exact False.elim (hnot hz)
    have hle := Finset.card_le_card hArSub
    simp at hle
    omega
  have hdivInt : (r : ℤ) ∣ q * (s : ℤ) := (Finset.mem_filter.mp hqsAr).2.2
  have hdivInt' : (r : ℤ) ∣ (s : ℤ) := by
    rcases hq with hq | hq
    · simpa [hq] using hdivInt
    · simpa [hq] using hdivInt
  have hdiv : r ∣ s := by exact_mod_cast hdivInt'
  have hdoubleLower : 2 * r ≤ s := by
    rcases (dvd_iff_exists_eq_mul_right.mp hdiv) with ⟨t, ht⟩
    have htLower : 2 ≤ t := by
      by_contra htLower
      have ht' : t ≤ 1 := by omega
      interval_cases t <;> simp_all
    rw [ht]
    nlinarith
  have hdoubleMem := integerInterval_mem_signed_double hzero hqs hq hdoubleLower
  have hsNotGeThree : ¬ 3 * r ≤ s := by
    intro hthree
    have hdoubleNeR : q * ((2 * r : ℕ) : ℤ) ≠ q * (r : ℤ) := by
      rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
    have hdoubleNeS : q * ((2 * r : ℕ) : ℤ) ≠ q * (s : ℤ) := by
      rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
    have hmemAr : q * ((2 * r : ℕ) : ℤ) ∈ Ar := by
      refine Finset.mem_filter.mpr ⟨hdoubleMem, ?_⟩
      constructor
      · rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
      · rcases hq with hq | hq
        · rw [hq]
          exact ⟨2, by push_cast; ring⟩
        · rw [hq]
          exact ⟨-2, by push_cast; ring⟩
    have hpair := hsmall (Finset.mem_union_left _ hmemAr)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    rcases hpair with h | h
    · exact hdoubleNeR h
    · exact hdoubleNeS h
  have hslt : s < 3 * r := by omega
  have hsEq : s = 2 * r := by
    rcases (dvd_iff_exists_eq_mul_right.mp hdiv) with ⟨t, ht⟩
    have htLower : 2 ≤ t := by
      by_contra htLower
      have ht' : t ≤ 1 := by omega
      interval_cases t <;> simp_all
    have htUpper : t < 3 := by
      rw [ht] at hslt
      nlinarith
    have htEq : t = 2 := by omega
    rw [ht, htEq]
    ring
  have hMfour : 4 * r ≤ M := by rw [hsEq] at hMs; nlinarith
  have hArThree : 3 ≤ Ar.card := by
    have h := card_nonzero_multiples_ge (L := L) (M := M) (d := r) (k := 3)
      hL hU (Nat.pos_of_ne_zero (by omega : r ≠ 0))
      (by nlinarith [hMfour])
    simpa [Ar] using h
  have hArSub : Ar ⊆ {q * (r : ℤ), q * (s : ℤ)} := by
    intro z hz
    exact hsmall (Finset.mem_union_left _ hz)
  have hle := Finset.card_le_card hArSub
  omega

/-- When all proper divisors in a family are equal, their candidate set has
Hall's condition and hence admits distinct non-anchor representatives. -/
theorem equal_proper_divisor_family_has_sdr
    {m M d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (L : ℤ) (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (a : Fin m → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haDiv : ∀ i, d ∣ a i)
    (haProper : ∀ i, a i ≠ d)
    (haM : ∀ i, a i ≤ M)
    (haInj : Function.Injective a) :
    ∃ f : Fin m → ℤ, Function.Injective f ∧
      ∀ i, f i ∈ properDivisorCandidates L M 0 (fun _ => d) i := by
  classical
  have hsize := repeated_proper_moduli_force_bound hm hd a haPos haDiv haProper haM haInj
  have hcard : m ≤ (properDivisorCandidates L M 0 (fun _ => d) (⟨0, hm⟩)).card := by
    simpa [properDivisorCandidates] using
      (card_nonzero_multiples_ge hL hU hd hsize)
  have hhall : ∀ s : Finset (Fin m),
      s.card ≤ (s.biUnion (properDivisorCandidates L M 0 (fun _ => d))).card := by
    intro s
    by_cases hs : s = ∅
    · simp [hs]
    · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
      obtain ⟨i, hi⟩ := hsne
      have hsub :
          properDivisorCandidates L M 0 (fun _ => d) (⟨0, hm⟩) ⊆
            s.biUnion (properDivisorCandidates L M 0 (fun _ => d)) := by
        intro z hz
        refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
        simpa [properDivisorCandidates] using hz
      have hle := Finset.card_le_card hsub
      have hscard : s.card ≤ m := by
        calc
          s.card ≤ Finset.univ.card := Finset.card_le_univ s
          _ = m := by simp
      omega
  exact exists_distinct_divisor_representatives_of_hall L M 0
    (fun _ => d) hhall

/-- Pairwise distinct divisors at most half the interval length have distinct
nonzero representatives, all on a side of the anchor with enough room. -/
theorem distinct_small_divisors_have_sdr
    {m M : ℕ} (L : ℤ) (hL : L ≤ 0)
    (hU : 0 ≤ L + (M : ℤ) - 1)
    (r : Fin m → ℕ)
    (hrPos : ∀ i, 0 < r i)
    (hrSmall : ∀ i, 2 * r i ≤ M)
    (hrInj : Function.Injective r) :
    ∃ f : Fin m → ℤ, Function.Injective f ∧
      ∀ i, f i ≠ 0 ∧ f i ∈ integerInterval L M ∧ (r i : ℤ) ∣ f i := by
  classical
  let U : ℤ := L + (M : ℤ) - 1
  have hspan : -L + U = (M : ℤ) - 1 := by
    dsimp [U]
    omega
  have hside : 2 * U ≥ (M : ℤ) - 1 ∨ 2 * (-L) ≥ (M : ℤ) - 1 := by
    omega
  by_cases hpos : 2 * U ≥ (M : ℤ) - 1
  · let f : Fin m → ℤ := fun i => (r i : ℤ)
    refine ⟨f, ?_, ?_⟩
    · intro i j hij
      change (r i : ℤ) = (r j : ℤ) at hij
      apply hrInj
      exact_mod_cast hij
    · intro i
      change (r i : ℤ) ≠ 0 ∧
        (r i : ℤ) ∈ integerInterval L M ∧ (r i : ℤ) ∣ (r i : ℤ)
      have hsmall : 2 * (r i : ℤ) ≤ (M : ℤ) := by exact_mod_cast hrSmall i
      have hUpos : 0 ≤ U := by dsimp [U]; omega
      have hroom : (r i : ℤ) ≤ U := by omega
      have hri : (r i : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hrPos i))
      refine ⟨hri, ?_, dvd_rfl⟩
      rw [mem_integerInterval]
      constructor
      · have hrnonneg : 0 ≤ (r i : ℤ) := by positivity
        omega
      · exact hroom
  · have hneg : 2 * (-L) ≥ (M : ℤ) - 1 := by rcases hside with h | h <;> omega
    let f : Fin m → ℤ := fun i => -(r i : ℤ)
    refine ⟨f, ?_, ?_⟩
    · intro i j hij
      change -(r i : ℤ) = -(r j : ℤ) at hij
      apply hrInj
      have h' : (r i : ℤ) = (r j : ℤ) := by
        simpa using congrArg (fun z : ℤ => -z) hij
      exact_mod_cast h'
    · intro i
      have hsmall : 2 * (r i : ℤ) ≤ (M : ℤ) := by exact_mod_cast hrSmall i
      have hroom : L ≤ -(r i : ℤ) := by omega
      have hUpos : 0 ≤ U := by dsimp [U]; omega
      have hri : (r i : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hrPos i))
      change -(r i : ℤ) ≠ 0 ∧
        -(r i : ℤ) ∈ integerInterval L M ∧ (r i : ℤ) ∣ -(r i : ℤ)
      refine ⟨?_, ?_, ?_⟩
      · intro hz
        apply hri
        omega
      · rw [mem_integerInterval]
        constructor
        · exact hroom
        · omega
      · refine ⟨-1, ?_⟩
        ring

/-- Proper-divisor candidate formulation of the all-distinct case. -/
theorem distinct_proper_divisor_family_has_sdr
    {m M : ℕ} (L : ℤ) (hL : L ≤ 0)
    (hU : 0 ≤ L + (M : ℤ) - 1)
    (r : Fin m → ℕ)
    (hrPos : ∀ i, 0 < r i)
    (hrSmall : ∀ i, 2 * r i ≤ M)
    (hrInj : Function.Injective r) :
    ∃ f : Fin m → ℤ, Function.Injective f ∧
      ∀ i, f i ∈ properDivisorCandidates L M 0 r i := by
  obtain ⟨f, hf, hmem⟩ :=
    distinct_small_divisors_have_sdr L hL hU r hrPos hrSmall hrInj
  refine ⟨f, hf, ?_⟩
  intro i
  rcases hmem i with ⟨hne, hi, hdiv⟩
  simpa [properDivisorCandidates] using And.intro hi (And.intro hne hdiv)

end Erdos708
