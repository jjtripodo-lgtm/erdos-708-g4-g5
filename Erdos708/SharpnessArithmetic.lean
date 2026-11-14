module

public import Erdos708.Intervals
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Arithmetic kernel for the Erdős #708 sharpness witness

  A = {77,91,139,143}
  I = {5935,...,6077} = integerInterval 5935 143.

This file keeps the finite arithmetic transparent.  Interval uniqueness facts
are proved from explicit divisibility witnesses and linear bounds; no large
finite enumeration is used.

This module is part of the trusted sharpness proof.
-/

namespace Erdos708

open scoped BigOperators

def sharpInterval : Finset ℤ :=
  integerInterval 5935 143

def sharpTripleTarget : ℤ :=
  77 * 91 * 143

def sharpFullTarget : ℤ :=
  77 * 91 * 139 * 143

@[simp] theorem mem_sharpInterval {z : ℤ} :
    z ∈ sharpInterval ↔ 5935 ≤ z ∧ z ≤ 6077 := by
  simp [sharpInterval, mem_integerInterval]

theorem sharp_unique_multiple_77
    {z : ℤ} (hz : z ∈ sharpInterval) (hd : (77 : ℤ) ∣ z) :
    z = 6006 := by
  rw [mem_sharpInterval] at hz
  rcases hd with ⟨q, hq⟩
  omega

theorem sharp_unique_multiple_91
    {z : ℤ} (hz : z ∈ sharpInterval) (hd : (91 : ℤ) ∣ z) :
    z = 6006 := by
  rw [mem_sharpInterval] at hz
  rcases hd with ⟨q, hq⟩
  omega

theorem sharp_unique_multiple_143
    {z : ℤ} (hz : z ∈ sharpInterval) (hd : (143 : ℤ) ∣ z) :
    z = 6006 := by
  rw [mem_sharpInterval] at hz
  rcases hd with ⟨q, hq⟩
  omega

theorem sharp_unique_multiple_139
    {z : ℤ} (hz : z ∈ sharpInterval) (hd : (139 : ℤ) ∣ z) :
    z = 5977 := by
  rw [mem_sharpInterval] at hz
  rcases hd with ⟨q, hq⟩
  omega

theorem sharp_no_multiple_169
    {z : ℤ} (hz : z ∈ sharpInterval) :
    ¬(169 : ℤ) ∣ z := by
  intro hd
  rw [mem_sharpInterval] at hz
  rcases hd with ⟨q, hq⟩
  omega

/-- Any interval entry carrying both 7 and 11 is the common point 6006. -/
theorem sharp_pair_7_11_eq_6006
    {z : ℤ}
    (hz : z ∈ sharpInterval)
    (h7 : (7 : ℤ) ∣ z)
    (h11 : (11 : ℤ) ∣ z) :
    z = 6006 := by
  rw [mem_sharpInterval] at hz
  rcases h7 with ⟨u, hu⟩
  rcases h11 with ⟨v, hv⟩
  omega

/-- Any interval entry carrying both 7 and 13 is the common point 6006. -/
theorem sharp_pair_7_13_eq_6006
    {z : ℤ}
    (hz : z ∈ sharpInterval)
    (h7 : (7 : ℤ) ∣ z)
    (h13 : (13 : ℤ) ∣ z) :
    z = 6006 := by
  rw [mem_sharpInterval] at hz
  rcases h7 with ⟨u, hu⟩
  rcases h13 with ⟨v, hv⟩
  omega

/-- Any interval entry carrying both 11 and 13 is the common point 6006. -/
theorem sharp_pair_11_13_eq_6006
    {z : ℤ}
    (hz : z ∈ sharpInterval)
    (h11 : (11 : ℤ) ∣ z)
    (h13 : (13 : ℤ) ∣ z) :
    z = 6006 := by
  rw [mem_sharpInterval] at hz
  rcases h11 with ⟨u, hu⟩
  rcases h13 with ⟨v, hv⟩
  omega

/-- A prime dividing a finite product divides one selected factor. -/
theorem prime_dvd_finset_prod_exists
    {p : ℤ} (hp : Prime p) (B : Finset ℤ)
    (hprod : p ∣ ∏ z ∈ B, z) :
    ∃ z ∈ B, p ∣ z := by
  classical
  induction B using Finset.induction_on with
  | empty =>
      exfalso
      apply hp.not_dvd_one
      simpa using hprod
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha] at hprod
      rcases hp.dvd_mul.mp hprod with hpa | hps
      · exact ⟨a, by simp, hpa⟩
      · rcases ih hps with ⟨z, hzs, hpz⟩
        exact ⟨z, by simp [hzs], hpz⟩

/--
Prime-square cancellation.

If p^2 divides a*R, p divides a, but p^2 does not divide a, then the missing
copy of p must divide R.
-/
theorem prime_dvd_rest_of_square_dvd_mul
    {p a R : ℤ}
    (hp : Prime p)
    (hpa : p ∣ a)
    (hnotSquare : ¬ p * p ∣ a)
    (hsquare : p * p ∣ a * R) :
    p ∣ R := by
  rcases hpa with ⟨k, hak⟩
  have hcancel : p ∣ k * R := by
    apply Int.dvd_of_mul_dvd_mul_left hp.ne_zero
    simpa [hak, mul_assoc, mul_comm, mul_left_comm] using hsquare
  rcases hp.dvd_mul.mp hcancel with hpk | hpR
  · exfalso
    apply hnotSquare
    rw [hak]
    exact mul_dvd_mul_left p hpk
  · exact hpR

/-- 5977 contributes none of the three primes used by the classical
three-modulus obstruction. -/
theorem sharp_5977_no_small_primes :
    ¬(7 : ℤ) ∣ 5977 ∧
    ¬(11 : ℤ) ∣ 5977 ∧
    ¬(13 : ℤ) ∣ 5977 := by
  norm_num

/-- The target arithmetic factorizations used by the sharpness proof. -/
theorem sharp_triple_target_factor :
    sharpTripleTarget = 1002001 := by
  norm_num [sharpTripleTarget]

theorem sharp_full_target_factor :
    sharpFullTarget = 139 * sharpTripleTarget := by
  norm_num [sharpFullTarget, sharpTripleTarget]

end Erdos708
