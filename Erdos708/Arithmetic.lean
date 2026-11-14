module

public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-!
Reusable arithmetic kernels for the four-modulus Erdős #708 formalization.

This module deliberately contains only denominator-free identities.  The
universal interval-cover argument is developed in later modules.
-/

namespace Erdos708

/-- The common gcd of three natural numbers, with a fixed association. -/
def tripleGcd (a b c : ℕ) : ℕ := Nat.gcd (Nat.gcd a b) c

/-- The common lcm of three natural numbers, with a fixed association. -/
def tripleLcm (a b c : ℕ) : ℕ := Nat.lcm (Nat.lcm a b) c

/--
Denominator-free three-variable gcd/lcm product identity.  Prime by prime,
the exponent identity is the min/max identity for three natural numbers.
-/
theorem triple_gcd_lcm_product_identity {a b c : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * b * c * tripleGcd a b c =
      tripleLcm a b c * Nat.gcd a b * Nat.gcd a c * Nat.gcd b c := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have habG : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
  have habL : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hg : Nat.gcd (Nat.gcd a b) c ≠ 0 := Nat.gcd_ne_zero_left habG
  have hl : Nat.lcm (Nat.lcm a b) c ≠ 0 := Nat.lcm_ne_zero habL hc
  have hac : Nat.gcd a c ≠ 0 := Nat.gcd_ne_zero_left ha
  have hbc : Nat.gcd b c ≠ 0 := Nat.gcd_ne_zero_left hb
  have habc : a * b * c ≠ 0 := mul_ne_zero hab hc
  have hLgab : Nat.lcm (Nat.lcm a b) c * Nat.gcd a b ≠ 0 :=
    mul_ne_zero hl habG
  have hLgabac : Nat.lcm (Nat.lcm a b) c * Nat.gcd a b * Nat.gcd a c ≠ 0 :=
    mul_ne_zero hLgab hac
  have hleft : a * b * c * tripleGcd a b c ≠ 0 := by
    exact mul_ne_zero habc hg
  have hright : tripleLcm a b c * Nat.gcd a b * Nat.gcd a c * Nat.gcd b c ≠ 0 := by
    exact mul_ne_zero hLgabac hbc
  apply Nat.eq_of_factorization_eq hleft hright
  intro p
  dsimp [tripleGcd, tripleLcm]
  rw [Nat.factorization_mul habc hg]
  rw [Nat.factorization_mul hab hc]
  rw [Nat.factorization_mul ha hb]
  rw [Nat.factorization_mul hLgabac hbc]
  rw [Nat.factorization_mul hLgab hac]
  rw [Nat.factorization_mul hl habG]
  rw [Nat.factorization_lcm habL hc]
  rw [Nat.factorization_lcm ha hb]
  rw [Nat.factorization_gcd habG hc]
  rw [Nat.factorization_gcd ha hb]
  rw [Nat.factorization_gcd ha hc]
  rw [Nat.factorization_gcd hb hc]
  simp only [Finsupp.add_apply, Finsupp.sup_apply, Finsupp.inf_apply]
  omega

end Erdos708
