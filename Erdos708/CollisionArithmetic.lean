module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Arithmetic identities for the finite four-modulus one-defect collision tree.

This module is part of the trusted one-defect dependency graph.  Helper names
retain their historical `_candidate` suffix.
-/

namespace Erdos708

/-- lcm*gcd product conservation in the factor order used by collision repair. -/
theorem lcm_mul_gcd_product_candidate (a b : ℕ) :
    Nat.lcm a b * Nat.gcd a b = a * b := by
  simpa [Nat.mul_comm] using Nat.gcd_mul_lcm a b

/--
After a first collision between a and d and a second collision of the residual
with b, the retained lcm factors plus the new residual multiply to a*d*b.
-/
theorem two_collision_product_identity_candidate (a d b : ℕ) :
    Nat.lcm a d *
        Nat.lcm (Nat.gcd a d) b *
        Nat.gcd (Nat.gcd a d) b =
      a * d * b := by
  calc
    Nat.lcm a d *
          Nat.lcm (Nat.gcd a d) b *
          Nat.gcd (Nat.gcd a d) b
        =
      Nat.lcm a d *
        (Nat.lcm (Nat.gcd a d) b *
          Nat.gcd (Nat.gcd a d) b) := by ring
    _ = Nat.lcm a d * (Nat.gcd a d * b) := by
      rw [lcm_mul_gcd_product_candidate]
    _ = (Nat.lcm a d * Nat.gcd a d) * b := by ring
    _ = (a * d) * b := by
      rw [lcm_mul_gcd_product_candidate]
    _ = a * d * b := by ring

/--
After three successive collisions, the three retained lcm factors and final
residual multiply to the product of all four original labels.
-/
theorem three_collision_product_identity_candidate (a d b c : ℕ) :
    Nat.lcm a d *
        Nat.lcm (Nat.gcd a d) b *
        Nat.lcm (Nat.gcd (Nat.gcd a d) b) c *
        Nat.gcd (Nat.gcd (Nat.gcd a d) b) c =
      a * d * b * c := by
  calc
    Nat.lcm a d *
          Nat.lcm (Nat.gcd a d) b *
          Nat.lcm (Nat.gcd (Nat.gcd a d) b) c *
          Nat.gcd (Nat.gcd (Nat.gcd a d) b) c
        =
      Nat.lcm a d *
        Nat.lcm (Nat.gcd a d) b *
        (Nat.lcm (Nat.gcd (Nat.gcd a d) b) c *
          Nat.gcd (Nat.gcd (Nat.gcd a d) b) c) := by ring
    _ =
      Nat.lcm a d *
        Nat.lcm (Nat.gcd a d) b *
        (Nat.gcd (Nat.gcd a d) b * c) := by
      rw [lcm_mul_gcd_product_candidate]
    _ =
      Nat.lcm a d *
        (Nat.lcm (Nat.gcd a d) b *
          Nat.gcd (Nat.gcd a d) b) * c := by ring
    _ = Nat.lcm a d * (Nat.gcd a d * b) * c := by
      rw [lcm_mul_gcd_product_candidate]
    _ = (Nat.lcm a d * Nat.gcd a d) * b * c := by ring
    _ = (a * d) * b * c := by
      rw [lcm_mul_gcd_product_candidate]
    _ = a * d * b * c := by ring

end Erdos708
