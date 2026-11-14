module

public import Erdos708.Five.Defs

@[expose] public section

/-!
# Lower bound `g(5) ≥ 6`

Moduli `{5, 10, 12, 15, 20}` (maximum `20`) and the interval `{51, …, 70}`.
The target is `5 * 10 * 12 * 15 * 20 = 180000 = 2^5 * 3^2 * 5^4`.

Argument (not a brute-force enumeration):
1. The only multiples of `5` in the interval are `55, 60, 65, 70`, and none is a multiple
   of `25`. Since `5^4` divides the product, all four must be selected.
2. Their product `15015000` is not divisible by `180000`, and at most one further entry
   can be added. No single entry `w` of the interval completes the target, since this
   would need `12 ∣ w` with `w ≠ 60`.

The six entries `{55, 60, 63, 64, 65, 70}` do cover the target.

The lower bound is classical (Erdős–Surányi 1959; the explicit witness is Chen's).
It is formalized here only so that the exact value `g(5) = 6` can be stated in Lean.
-/

namespace Erdos708

open scoped BigOperators

/-- The four multiples of five in `{51, …, 70}`. -/
def sharp5Fives : Finset ℤ := {55, 60, 65, 70}

theorem sharp5_not_five_dvd {z : ℤ} (hz : z ∈ integerInterval 51 20)
    (hzF : z ∉ sharp5Fives) : ¬ (5 : ℤ) ∣ z := by
  rw [mem_integerInterval] at hz
  obtain ⟨h1, h2⟩ := hz
  simp only [sharp5Fives, Finset.mem_insert, Finset.mem_singleton, not_or] at hzF
  intro h5
  omega

theorem sharp5_coprime_625 {z : ℤ} (hz : z ∈ integerInterval 51 20)
    (hzF : z ∉ sharp5Fives) : IsCoprime (625 : ℤ) z := by
  have h5 : IsCoprime (5 : ℤ) z := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hprime : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
    have hnd := sharp5_not_five_dvd hz hzF
    have hg : Int.gcd 5 z ∣ 5 := by
      have := Int.gcd_dvd_left (a := 5) (b := z)
      exact_mod_cast Int.natAbs_dvd_natAbs.mpr this
    have hcases : Int.gcd 5 z = 1 ∨ Int.gcd 5 z = 5 :=
      (Nat.dvd_prime (by norm_num)).mp hg
    rcases hcases with h | h
    · exact h
    · exfalso
      apply hnd
      have := Int.gcd_dvd_right (a := 5) (b := z)
      rw [h] at this
      exact_mod_cast this
  have : (625 : ℤ) = 5 ^ 4 := by norm_num
  rw [this]
  exact h5.pow_left

/-- Any cover of `5^4` by interval entries must contain all four multiples of five. -/
theorem sharp5_fives_subset (B : Finset ℤ) (hB : B ⊆ integerInterval 51 20)
    (hdvd : (625 : ℤ) ∣ ∏ z ∈ B, z) : sharp5Fives ⊆ B := by
  classical
  have hsplit := Finset.prod_inter_mul_prod_diff B sharp5Fives (fun z => z)
  have hcop : IsCoprime (625 : ℤ) (∏ z ∈ B \ sharp5Fives, z) := by
    apply IsCoprime.prod_right
    intro z hz
    rw [Finset.mem_sdiff] at hz
    exact sharp5_coprime_625 (hB hz.1) hz.2
  have hinter : (625 : ℤ) ∣ ∏ z ∈ B ∩ sharp5Fives, z := by
    rw [← hsplit] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd
  intro x hx
  by_contra hxB
  have hsub : B ∩ sharp5Fives ⊆ sharp5Fives.erase x := by
    intro y hy
    rw [Finset.mem_inter] at hy
    rw [Finset.mem_erase]
    exact ⟨fun hyx => hxB (hyx ▸ hy.1), hy.2⟩
  have hdiv : (∏ z ∈ B ∩ sharp5Fives, z) ∣ ∏ z ∈ sharp5Fives.erase x, z :=
    Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have h625 := hinter.trans hdiv
  simp only [sharp5Fives, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> revert h625 <;> decide

/-- No five interval entries cover `5 * 10 * 12 * 15 * 20`. -/
theorem sharp5_no_five_cover : ¬ FiveModuliCover 51 20 5 10 12 15 20 5 := by
  classical
  rintro ⟨B, hB, hcard, hdvd⟩
  have htarget : ((5 : ℕ) : ℤ) * ((10 : ℕ) : ℤ) * ((12 : ℕ) : ℤ) * ((15 : ℕ) : ℤ) *
      ((20 : ℕ) : ℤ) = 180000 := by norm_num
  rw [htarget] at hdvd
  have h625 : (625 : ℤ) ∣ ∏ z ∈ B, z := (by norm_num : (625 : ℤ) ∣ 180000).trans hdvd
  have hF := sharp5_fives_subset B hB h625
  have hFcard : sharp5Fives.card = 4 := by decide
  have hrest : (B \ sharp5Fives).card ≤ 1 := by
    have := Finset.card_sdiff_add_card_eq_card hF
    omega
  have hsplit : ∏ z ∈ B, z = (∏ z ∈ sharp5Fives, z) * ∏ z ∈ B \ sharp5Fives, z := by
    rw [← Finset.prod_sdiff hF, mul_comm]
  have hFprod : ∏ z ∈ sharp5Fives, z = 15015000 := by decide
  rw [hsplit, hFprod] at hdvd
  rcases Finset.card_le_one_iff_subset_singleton.mp hrest with ⟨w, hw⟩
  rcases Finset.subset_singleton_iff.mp hw with h0 | h1
  · rw [h0, Finset.prod_empty, mul_one] at hdvd
    revert hdvd; decide
  · rw [h1, Finset.prod_singleton] at hdvd
    have hwmem := Finset.mem_sdiff.mp (h1 ▸ Finset.mem_singleton_self w)
    have hwB : w ∈ B := hwmem.1
    have hwF : w ∉ sharp5Fives := hwmem.2
    have hwI := hB hwB
    rw [mem_integerInterval] at hwI
    obtain ⟨hlo, hhi⟩ := hwI
    norm_num at hlo hhi
    interval_cases w <;> first | exact absurd (by decide) hwF | (revert hdvd; decide)

/-- The six entries `{55, 60, 63, 64, 65, 70}` cover `5 * 10 * 12 * 15 * 20`. -/
theorem sharp5_six_cover : FiveModuliCover 51 20 5 10 12 15 20 6 := by
  refine ⟨{55, 60, 63, 64, 65, 70}, ?_, by decide, ?_⟩
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [mem_integerInterval]
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · decide

end Erdos708
