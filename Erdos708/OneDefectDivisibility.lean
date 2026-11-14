module

public import Erdos708.CollisionArithmetic
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Tactic

@[expose] public section

/-!
Divisibility consequences of the nested one-defect collision identities.

This module is part of the trusted one-defect dependency graph.  Helper names
retain their historical `_candidate` suffix.
-/

namespace Erdos708

/-- One collision: the collided point plus a residual multiple covers a*d. -/
theorem one_collision_product_dvd_candidate
    {a d : ℕ} {x z : ℤ}
    (ha : (a : ℤ) ∣ x)
    (hd : (d : ℤ) ∣ x)
    (hg : (Nat.gcd a d : ℤ) ∣ z) :
    (a : ℤ) * (d : ℤ) ∣ x * z := by
  have hl : (Nat.lcm a d : ℤ) ∣ x :=
    Int.coe_lcm_dvd ha hd
  have hmul :=
    mul_dvd_mul hl hg
  have hid :
      (Nat.lcm a d : ℤ) * (Nat.gcd a d : ℤ) =
        (a : ℤ) * (d : ℤ) := by
    exact_mod_cast lcm_mul_gcd_product_candidate a d
  rw [hid] at hmul
  exact hmul

/-- Two collisions: retained lcm factors plus residual cover a*d*b. -/
theorem two_collision_product_dvd_candidate
    {a d b : ℕ} {xa xb w : ℤ}
    (ha : (a : ℤ) ∣ xa)
    (hd : (d : ℤ) ∣ xa)
    (hg1 : (Nat.gcd a d : ℤ) ∣ xb)
    (hb : (b : ℤ) ∣ xb)
    (hg2 : (Nat.gcd (Nat.gcd a d) b : ℤ) ∣ w) :
    (a : ℤ) * (d : ℤ) * (b : ℤ) ∣ xa * xb * w := by
  have hl1 : (Nat.lcm a d : ℤ) ∣ xa :=
    Int.coe_lcm_dvd ha hd
  have hl2 : (Nat.lcm (Nat.gcd a d) b : ℤ) ∣ xb :=
    Int.coe_lcm_dvd hg1 hb
  have hmul :=
    mul_dvd_mul (mul_dvd_mul hl1 hl2) hg2
  have hid :
      (Nat.lcm a d : ℤ) *
          (Nat.lcm (Nat.gcd a d) b : ℤ) *
          (Nat.gcd (Nat.gcd a d) b : ℤ) =
        (a : ℤ) * (d : ℤ) * (b : ℤ) := by
    exact_mod_cast two_collision_product_identity_candidate a d b
  rw [hid] at hmul
  exact hmul

/-- Three collisions: the three occupied anchors plus final residual cover all four labels. -/
theorem three_collision_product_dvd_candidate
    {a d b c : ℕ} {xa xb xc u : ℤ}
    (ha : (a : ℤ) ∣ xa)
    (hd : (d : ℤ) ∣ xa)
    (hg1 : (Nat.gcd a d : ℤ) ∣ xb)
    (hb : (b : ℤ) ∣ xb)
    (hg2 : (Nat.gcd (Nat.gcd a d) b : ℤ) ∣ xc)
    (hc : (c : ℤ) ∣ xc)
    (hg3 : (Nat.gcd (Nat.gcd (Nat.gcd a d) b) c : ℤ) ∣ u) :
    (a : ℤ) * (d : ℤ) * (b : ℤ) * (c : ℤ) ∣
      xa * xb * xc * u := by
  have hl1 : (Nat.lcm a d : ℤ) ∣ xa :=
    Int.coe_lcm_dvd ha hd
  have hl2 : (Nat.lcm (Nat.gcd a d) b : ℤ) ∣ xb :=
    Int.coe_lcm_dvd hg1 hb
  have hl3 :
      (Nat.lcm (Nat.gcd (Nat.gcd a d) b) c : ℤ) ∣ xc :=
    Int.coe_lcm_dvd hg2 hc
  have hmul :=
    mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hl1 hl2) hl3) hg3
  have hid :
      (Nat.lcm a d : ℤ) *
          (Nat.lcm (Nat.gcd a d) b : ℤ) *
          (Nat.lcm (Nat.gcd (Nat.gcd a d) b) c : ℤ) *
          (Nat.gcd (Nat.gcd (Nat.gcd a d) b) c : ℤ) =
        (a : ℤ) * (d : ℤ) * (b : ℤ) * (c : ℤ) := by
    exact_mod_cast three_collision_product_identity_candidate a d b c
  rw [hid] at hmul
  exact hmul

end Erdos708
