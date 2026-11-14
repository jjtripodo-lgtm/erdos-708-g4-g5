module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Subject-local arithmetic kernel for the exceptional two-anchor branch of the
four-modulus Erdős #708 proof.

This module duplicates the already-banked identity formerly imported from the
historical cross-project `Erdos488.FlagshipVerification` module.  Its purpose
is release hygiene: the future standalone #708 repository should not depend on
unrelated #488 source files.
-/

namespace Erdos708

/-- Prime-exponent identity behind the exceptional bridge payment. -/
theorem bridge_exponent_identity (x y z : ℕ) :
    max (max x y) z + min x y + max (min x z) (min y z) =
      x + y + z := by
  omega

/--
Residual-product identity in the exceptional two-anchor bridge case.

`lcm(a,b,D)` is paid by the two anchors; the second factor is exactly the
remaining gcd/lcm repair product.
-/
theorem bridge_residual_product_identity {a b D : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hD : D ≠ 0) :
    Nat.lcm (Nat.lcm a b) D *
        (Nat.gcd a b * Nat.lcm (Nat.gcd a D) (Nat.gcd b D))
      = a * b * D := by
  have habL : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hL : Nat.lcm (Nat.lcm a b) D ≠ 0 := Nat.lcm_ne_zero habL hD
  have hg : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
  have hr : Nat.gcd a D ≠ 0 := Nat.gcd_ne_zero_left ha
  have hs : Nat.gcd b D ≠ 0 := Nat.gcd_ne_zero_left hb
  have hrs : Nat.lcm (Nat.gcd a D) (Nat.gcd b D) ≠ 0 :=
    Nat.lcm_ne_zero hr hs
  have hGR : Nat.gcd a b * Nat.lcm (Nat.gcd a D) (Nat.gcd b D) ≠ 0 :=
    mul_ne_zero hg hrs
  have hleft :
      Nat.lcm (Nat.lcm a b) D *
          (Nat.gcd a b * Nat.lcm (Nat.gcd a D) (Nat.gcd b D)) ≠ 0 :=
    mul_ne_zero hL hGR
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hright : a * b * D ≠ 0 := mul_ne_zero hab hD
  apply Nat.eq_of_factorization_eq hleft hright
  intro p
  rw [Nat.factorization_mul hL hGR]
  rw [Nat.factorization_mul hg hrs]
  rw [Nat.factorization_mul hab hD]
  rw [Nat.factorization_mul ha hb]
  rw [Nat.factorization_lcm habL hD]
  rw [Nat.factorization_lcm ha hb]
  rw [Nat.factorization_gcd ha hb]
  rw [Nat.factorization_lcm hr hs]
  rw [Nat.factorization_gcd ha hD]
  rw [Nat.factorization_gcd hb hD]
  simp only [Finsupp.add_apply, Finsupp.sup_apply, Finsupp.inf_apply]
  simpa only [Nat.add_assoc] using
    bridge_exponent_identity (a.factorization p) (b.factorization p)
      (D.factorization p)

end Erdos708
