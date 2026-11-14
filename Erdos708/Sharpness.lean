module

public import Erdos708.SharpnessArithmetic
public import Erdos708.UniversalUpper
public import Mathlib.Tactic

@[expose] public section

set_option maxHeartbeats 0

/-!
Trusted sharpness proof for the Erdős #708 four-modulus theorem.

Witness:
  moduli {77,91,139,143}
  interval {5935,...,6077}.

The proof is the manuscript's factor argument, not a brute-force enumeration.

1. The three-modulus target 77*91*143 = 7^2*11^2*13^2 cannot be paid by
   three interval entries.
   * If 6006 is selected, each of 7,11,13 still needs a second occurrence.
     Every other interval point supports at most one of those primes, so three
     additional points are required.
   * If 6006 is omitted, 13^2 forces two distinct 13-multiples because no
     interval entry is a multiple of 169.  Those two cannot carry 7 or 11, so
     a third remaining point would have to carry both 7 and 11, forcing 6006.

2. Any full cover must contain the unique 139-multiple 5977.  Since
   5977=139*43 and gcd(43,77*91*143)=1, deleting 5977 leaves a cover of the
   three-modulus target.  Thus a four-point full cover would induce a
   three-point triple cover, impossible.

3. The displayed five points do cover the full product.

This module proves the exact four-modulus optimum.
-/

namespace Erdos708

open scoped BigOperators

/-- The classical three-modulus obstruction requires at least four entries in
this interval. -/
theorem sharp_triple_no_three_cover
    (B : Finset ℤ)
    (hBI : B ⊆ sharpInterval)
    (hBcard : B.card ≤ 3) :
    ¬ sharpTripleTarget ∣ ∏ z ∈ B, z := by
  classical
  intro hpay
  have h7prod : (7 : ℤ) ∣ ∏ z ∈ B, z :=
    (show (7 : ℤ) ∣ sharpTripleTarget by
      norm_num [sharpTripleTarget]).trans hpay
  have h11prod : (11 : ℤ) ∣ ∏ z ∈ B, z :=
    (show (11 : ℤ) ∣ sharpTripleTarget by
      norm_num [sharpTripleTarget]).trans hpay
  have h13prod : (13 : ℤ) ∣ ∏ z ∈ B, z :=
    (show (13 : ℤ) ∣ sharpTripleTarget by
      norm_num [sharpTripleTarget]).trans hpay
  have h49prod : (49 : ℤ) ∣ ∏ z ∈ B, z :=
    (show (49 : ℤ) ∣ sharpTripleTarget by
      norm_num [sharpTripleTarget]).trans hpay
  have h121prod : (121 : ℤ) ∣ ∏ z ∈ B, z :=
    (show (121 : ℤ) ∣ sharpTripleTarget by
      norm_num [sharpTripleTarget]).trans hpay
  have h169prod : (169 : ℤ) ∣ ∏ z ∈ B, z :=
    (show (169 : ℤ) ∣ sharpTripleTarget by
      norm_num [sharpTripleTarget]).trans hpay

  by_cases h6006 : (6006 : ℤ) ∈ B
  · let R : ℤ := ∏ z ∈ B.erase 6006, z
    have hprodEq :
        (6006 : ℤ) * R = ∏ z ∈ B, z := by
      simpa [R] using
        (Finset.mul_prod_erase B (fun z : ℤ => z) h6006)

    have h7R : (7 : ℤ) ∣ R := by
      apply prime_dvd_rest_of_square_dvd_mul
        (p := (7 : ℤ)) (a := 6006) (R := R)
        (by norm_num)
        (by norm_num)
        (by norm_num)
      rw [hprodEq]
      simpa using h49prod

    have h11R : (11 : ℤ) ∣ R := by
      apply prime_dvd_rest_of_square_dvd_mul
        (p := (11 : ℤ)) (a := 6006) (R := R)
        (by norm_num)
        (by norm_num)
        (by norm_num)
      rw [hprodEq]
      simpa using h121prod

    have h13R : (13 : ℤ) ∣ R := by
      apply prime_dvd_rest_of_square_dvd_mul
        (p := (13 : ℤ)) (a := 6006) (R := R)
        (by norm_num)
        (by norm_num)
        (by norm_num)
      rw [hprodEq]
      simpa using h169prod

    obtain ⟨z7, hz7B, h7z7⟩ :=
      prime_dvd_finset_prod_exists
        (p := (7 : ℤ)) (by norm_num) (B.erase 6006)
        (by simpa [R] using h7R)
    obtain ⟨z11, hz11B, h11z11⟩ :=
      prime_dvd_finset_prod_exists
        (p := (11 : ℤ)) (by norm_num) (B.erase 6006)
        (by simpa [R] using h11R)
    obtain ⟨z13, hz13B, h13z13⟩ :=
      prime_dvd_finset_prod_exists
        (p := (13 : ℤ)) (by norm_num) (B.erase 6006)
        (by simpa [R] using h13R)

    have hz7I : z7 ∈ sharpInterval :=
      hBI (Finset.mem_of_mem_erase hz7B)
    have hz11I : z11 ∈ sharpInterval :=
      hBI (Finset.mem_of_mem_erase hz11B)
    have hz13I : z13 ∈ sharpInterval :=
      hBI (Finset.mem_of_mem_erase hz13B)

    have hz7Ne : z7 ≠ (6006 : ℤ) :=
      Finset.ne_of_mem_erase hz7B
    have hz11Ne : z11 ≠ (6006 : ℤ) :=
      Finset.ne_of_mem_erase hz11B
    have hz13Ne : z13 ≠ (6006 : ℤ) :=
      Finset.ne_of_mem_erase hz13B

    have h7ne11 : z7 ≠ z11 := by
      intro h
      subst z11
      exact hz7Ne
        (sharp_pair_7_11_eq_6006
          hz7I h7z7 h11z11)
    have h7ne13 : z7 ≠ z13 := by
      intro h
      subst z13
      exact hz7Ne
        (sharp_pair_7_13_eq_6006
          hz7I h7z7 h13z13)
    have h11ne13 : z11 ≠ z13 := by
      intro h
      subst z13
      exact hz11Ne
        (sharp_pair_11_13_eq_6006
          hz11I h11z11 h13z13)

    let T : Finset ℤ := {z7, z11, z13}
    have hTsub : T ⊆ B.erase 6006 := by
      intro z hz
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hz7B
      · exact hz11B
      · exact hz13B
    have hTcard : T.card = 3 := by
      simp [T, h7ne11, h7ne13, h11ne13]
    have hRestGe : 3 ≤ (B.erase 6006).card := by
      rw [← hTcard]
      exact Finset.card_le_card hTsub
    have hRestLe : (B.erase 6006).card ≤ 2 := by
      rw [Finset.card_erase_of_mem h6006]
      omega
    omega

  · obtain ⟨z13a, hz13aB, h13a⟩ :=
      prime_dvd_finset_prod_exists
        (p := (13 : ℤ)) (by norm_num) B h13prod
    have hz13aI : z13a ∈ sharpInterval := hBI hz13aB
    have h169a : ¬(169 : ℤ) ∣ z13a :=
      sharp_no_multiple_169 hz13aI

    let R : ℤ := ∏ z ∈ B.erase z13a, z
    have hprodEq :
        z13a * R = ∏ z ∈ B, z := by
      simpa [R] using
        (Finset.mul_prod_erase B (fun z : ℤ => z) hz13aB)

    have h13R : (13 : ℤ) ∣ R := by
      apply prime_dvd_rest_of_square_dvd_mul
        (p := (13 : ℤ)) (a := z13a) (R := R)
        (by norm_num)
        h13a
        (by simpa using h169a)
      rw [hprodEq]
      simpa using h169prod

    obtain ⟨z13b, hz13bErase, h13b⟩ :=
      prime_dvd_finset_prod_exists
        (p := (13 : ℤ)) (by norm_num) (B.erase z13a)
        (by simpa [R] using h13R)
    have hz13bB : z13b ∈ B :=
      Finset.mem_of_mem_erase hz13bErase
    have hz13bI : z13b ∈ sharpInterval := hBI hz13bB
    have h13ab : z13a ≠ z13b := by
      exact (Finset.ne_of_mem_erase hz13bErase).symm

    obtain ⟨z7, hz7B, h7z7⟩ :=
      prime_dvd_finset_prod_exists
        (p := (7 : ℤ)) (by norm_num) B h7prod
    obtain ⟨z11, hz11B, h11z11⟩ :=
      prime_dvd_finset_prod_exists
        (p := (11 : ℤ)) (by norm_num) B h11prod
    have hz7I : z7 ∈ sharpInterval := hBI hz7B
    have hz11I : z11 ∈ sharpInterval := hBI hz11B

    have h7ne13a : z7 ≠ z13a := by
      intro h
      subst z13a
      have hz := sharp_pair_7_13_eq_6006
        hz7I h7z7 h13a
      apply h6006
      rw [← hz]
      exact hz7B
    have h7ne13b : z7 ≠ z13b := by
      intro h
      subst z13b
      have hz := sharp_pair_7_13_eq_6006
        hz7I h7z7 h13b
      apply h6006
      rw [← hz]
      exact hz7B
    have h11ne13a : z11 ≠ z13a := by
      intro h
      subst z13a
      have hz := sharp_pair_11_13_eq_6006
        hz11I h11z11 h13a
      apply h6006
      rw [← hz]
      exact hz11B
    have h11ne13b : z11 ≠ z13b := by
      intro h
      subst z13b
      have hz := sharp_pair_11_13_eq_6006
        hz11I h11z11 h13b
      apply h6006
      rw [← hz]
      exact hz11B

    by_cases h7eq11 : z7 = z11
    · subst z11
      have hz := sharp_pair_7_11_eq_6006
        hz7I h7z7 h11z11
      apply h6006
      rw [← hz]
      exact hz7B
    · let T : Finset ℤ := {z13a, z13b, z7, z11}
      have hTsub : T ⊆ B := by
        intro z hz
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact hz13aB
        · exact hz13bB
        · exact hz7B
        · exact hz11B
      have hTcard : T.card = 4 := by
        change (insert z13a (insert z13b (insert z7 ({z11} : Finset ℤ)))).card = 4
        have h7not : z7 ∉ ({z11} : Finset ℤ) := by
          simp [h7eq11]
        have h13bnot : z13b ∉ insert z7 ({z11} : Finset ℤ) := by
          simp [Ne.symm h7ne13b, Ne.symm h11ne13b]
        have h13anot : z13a ∉ insert z13b (insert z7 ({z11} : Finset ℤ)) := by
          simp [h13ab, Ne.symm h7ne13a, Ne.symm h11ne13a]
        rw [Finset.card_insert_of_notMem h13anot,
          Finset.card_insert_of_notMem h13bnot,
          Finset.card_insert_of_notMem h7not]
        norm_num
      have hfour : 4 ≤ B.card := by
        rw [← hTcard]
        exact Finset.card_le_card hTsub
      omega

/-- Any full cover by at most four entries would leave at most three entries
after deleting the forced 139-multiple 5977, contradicting the triple
obstruction. -/
theorem sharp_full_no_four_cover
    (B : Finset ℤ)
    (hBI : B ⊆ sharpInterval)
    (hBcard : B.card ≤ 4) :
    ¬ sharpFullTarget ∣ ∏ z ∈ B, z := by
  classical
  intro hpay
  have h139prod : (139 : ℤ) ∣ ∏ z ∈ B, z :=
    (show (139 : ℤ) ∣ sharpFullTarget by
      norm_num [sharpFullTarget]).trans hpay
  obtain ⟨z, hzB, h139z⟩ :=
    prime_dvd_finset_prod_exists
      (p := (139 : ℤ)) (by norm_num) B h139prod
  have hzI : z ∈ sharpInterval := hBI hzB
  have hzEq : z = 5977 :=
    sharp_unique_multiple_139 hzI h139z
  have h5977B : (5977 : ℤ) ∈ B := by
    simpa [hzEq] using hzB

  let R : ℤ := ∏ z ∈ B.erase 5977, z
  have hprodEq :
      (5977 : ℤ) * R = ∏ z ∈ B, z := by
    simpa [R] using
      (Finset.mul_prod_erase B (fun z : ℤ => z) h5977B)

  have hscaled :
      (139 : ℤ) * sharpTripleTarget ∣
        (139 : ℤ) * (43 * R) := by
    have hh := hpay
    rw [sharp_full_target_factor] at hh
    rw [← hprodEq] at hh
    convert hh using 1 <;>
      simp only [show (5977 : ℤ) = 139 * 43 by norm_num] <;>
      ring

  have hT43R : sharpTripleTarget ∣ 43 * R :=
    Int.dvd_of_mul_dvd_mul_left (by norm_num) hscaled

  have hTR : sharpTripleTarget ∣ R := by
    have hswap : sharpTripleTarget ∣ R * 43 := by
      simpa [mul_comm] using hT43R
    exact Int.dvd_of_dvd_mul_left_of_gcd_one
      hswap
      (by norm_num [sharpTripleTarget])

  have hEraseSub : B.erase 5977 ⊆ sharpInterval :=
    (Finset.erase_subset _ _).trans hBI
  have hEraseCard : (B.erase 5977).card ≤ 3 := by
    rw [Finset.card_erase_of_mem h5977B]
    omega
  exact sharp_triple_no_three_cover
    (B.erase 5977) hEraseSub hEraseCard
    (by simpa [R] using hTR)

def sharpFiveSet : Finset ℤ :=
  {5936, 5940, 5941, 5977, 6006}

/-- The manuscript's displayed five entries lie in the interval. -/
theorem sharpFiveSet_subset :
    sharpFiveSet ⊆ sharpInterval := by
  intro z hz
  simp only [sharpFiveSet, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl <;>
    simp [mem_sharpInterval]

theorem sharpFiveSet_card :
    sharpFiveSet.card = 5 := by
  norm_num [sharpFiveSet]

/-- The displayed five entries pay the full product. -/
theorem sharpFiveSet_pays :
    sharpFullTarget ∣ ∏ z ∈ sharpFiveSet, z := by
  norm_num [sharpFiveSet, sharpFullTarget]

/-- Exact minimum five for the explicit sharpness witness. -/
theorem sharp_example_exactly_five :
    (∃ B : Finset ℤ,
      B ⊆ sharpInterval ∧
      B.card = 5 ∧
      sharpFullTarget ∣ ∏ z ∈ B, z) ∧
    (∀ B : Finset ℤ,
      B ⊆ sharpInterval →
      sharpFullTarget ∣ ∏ z ∈ B, z →
      5 ≤ B.card) := by
  constructor
  · exact ⟨sharpFiveSet, sharpFiveSet_subset,
      sharpFiveSet_card, sharpFiveSet_pays⟩
  · intro B hBI hpay
    by_contra hnot
    have hle : B.card ≤ 4 := by omega
    exact sharp_full_no_four_cover B hBI hle hpay

/--
Four-modulus-specific uniform bound formulation.

This is the exact optimization problem solved by the upper theorem: k works if
every four pairwise-distinct moduli in [2,M] and every M-term integer interval
have a product cover using at most k entries.
-/
def FourModuliUniformBound (k : ℕ) : Prop :=
  ∀ (L : ℤ) (M a b c d : ℕ),
    2 ≤ a → 2 ≤ b → 2 ≤ c → 2 ≤ d →
    a ≤ M → b ≤ M → c ≤ M → d ≤ M →
    a ≠ b → a ≠ c → a ≠ d →
    b ≠ c → b ≠ d → c ≠ d →
    ∃ B : Finset ℤ,
      B ⊆ integerInterval L M ∧
      B.card ≤ k ∧
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
        ∏ z ∈ B, z

theorem four_moduli_uniform_bound_five :
    FourModuliUniformBound 5 := by
  intro L M a b c d
    haTwo hbTwo hcTwo hdTwo
    haM hbM hcM hdM
    hab hac had hbc hbd hcd
  exact four_moduli_five_cover
    haTwo hbTwo hcTwo hdTwo
    haM hbM hcM hdM
    hab hac had hbc hbd hcd

theorem four_moduli_uniform_bound_four_fails :
    ¬ FourModuliUniformBound 4 := by
  intro hfour
  obtain ⟨B, hBI, hBcard, hpay⟩ :=
    hfour 5935 143 77 91 139 143
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hBI' : B ⊆ sharpInterval := by
    simpa [sharpInterval] using hBI
  have hpay' : sharpFullTarget ∣ ∏ z ∈ B, z := by
    simpa [sharpFullTarget] using hpay
  exact sharp_full_no_four_cover B hBI' hBcard hpay'


theorem four_moduli_uniform_bound_mono
    {k l : ℕ}
    (hkl : k ≤ l)
    (hk : FourModuliUniformBound k) :
    FourModuliUniformBound l := by
  intro L M a b c d
    haTwo hbTwo hcTwo hdTwo
    haM hbM hcM hdM
    hab hac had hbc hbd hcd
  obtain ⟨B, hBI, hBcard, hpay⟩ :=
    hk L M a b c d
      haTwo hbTwo hcTwo hdTwo
      haM hbM hcM hdM
      hab hac had hbc hbd hcd
  exact ⟨B, hBI, hBcard.trans hkl, hpay⟩

/-- Exact characterization of the four-modulus uniform cover constant. -/
theorem four_moduli_uniform_bound_iff_five_le
    (k : ℕ) :
    FourModuliUniformBound k ↔ 5 ≤ k := by
  constructor
  · intro hk
    by_contra hnot
    have hk4 : k ≤ 4 := by omega
    have hfour : FourModuliUniformBound 4 :=
      four_moduli_uniform_bound_mono
        hk4 hk
    exact four_moduli_uniform_bound_four_fails hfour
  · intro h5
    exact four_moduli_uniform_bound_mono
      h5 four_moduli_uniform_bound_five

/-- Publication-facing exact-optimality content usually summarized as g(4)=5. -/
theorem four_moduli_uniform_bound_exactly_five :
    FourModuliUniformBound 5 ∧
    ¬ FourModuliUniformBound 4 ∧
    (∀ k, FourModuliUniformBound k ↔ 5 ≤ k) := by
  refine ⟨four_moduli_uniform_bound_five,
    four_moduli_uniform_bound_four_fails, ?_⟩
  intro k
  exact four_moduli_uniform_bound_iff_five_le k

end Erdos708
