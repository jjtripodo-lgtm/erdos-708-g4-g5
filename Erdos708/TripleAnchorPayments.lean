module

public import Erdos708.TripleAnchorArithmetic
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Tactic

@[expose] public section

/-!
Divisibility payments for the Erdős #708 triple-anchor case.

This module is imported by the trusted Erdős 708 theorem map.

The arithmetic identities in `TripleAnchorArithmetic` are equalities
in `ℕ`.  The interval proof ultimately needs divisibility statements for
integer interval entries.  These lemmas are the bridge: a common anchor pays
the triple lcm, collided repair points pay lcms of pair gcds, and the remaining
repair point pays the residual gcd.

No interval-existence or collision-exhaustion theorem is claimed here.
-/

namespace Erdos708

/-- A common integer multiple of a,b,c is a multiple of their triple lcm. -/
theorem tripleLcm_dvd_common_int
    {a b c : ℕ} {x : ℤ}
    (ha : (a : ℤ) ∣ x)
    (hb : (b : ℤ) ∣ x)
    (hc : (c : ℤ) ∣ x) :
    (tripleLcm a b c : ℤ) ∣ x := by
  dsimp [tripleLcm]
  exact Int.coe_lcm_dvd (Int.coe_lcm_dvd ha hb) hc

/--
When the three pair-gcd repair points are distinct, the common anchor together
with those three points already pays a*b*c.  The banked three-variable identity
actually gives the stronger divisor a*b*c*tripleGcd.
-/
theorem triple_anchor_distinct_repairs_product_dvd
    {a b c : ℕ} {x zab zac zbc : ℤ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c)
    (ha : (a : ℤ) ∣ x)
    (hb : (b : ℤ) ∣ x)
    (hc : (c : ℤ) ∣ x)
    (hab : (Nat.gcd a b : ℤ) ∣ zab)
    (hac : (Nat.gcd a c : ℤ) ∣ zac)
    (hbc : (Nat.gcd b c : ℤ) ∣ zbc) :
    (a : ℤ) * (b : ℤ) * (c : ℤ) ∣ x * zab * zac * zbc := by
  have hL : (tripleLcm a b c : ℤ) ∣ x :=
    tripleLcm_dvd_common_int ha hb hc
  have hmul :=
    mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hL hab) hac) hbc
  have hid :
      (tripleLcm a b c : ℤ) *
          (Nat.gcd a b : ℤ) *
          (Nat.gcd a c : ℤ) *
          (Nat.gcd b c : ℤ) =
        (a : ℤ) * (b : ℤ) * (c : ℤ) *
          (tripleGcd a b c : ℤ) := by
    exact_mod_cast
      (triple_gcd_lcm_product_identity
        (a := a) (b := b) (c := c)
        (Nat.ne_of_gt haPos) (Nat.ne_of_gt hbPos) (Nat.ne_of_gt hcPos)).symm
  rw [hid] at hmul
  rcases hmul with ⟨k, hk⟩
  refine ⟨(tripleGcd a b c : ℤ) * k, ?_⟩
  rw [hk]
  ring

/--
If the gcd(a,b) and gcd(a,c) repairs collide, the collided point plus a
gcd(b,c)-multiple and the common anchor pay a*b*c.
-/
theorem triple_anchor_collision_ab_ac_product_dvd
    {a b c : ℕ} {x z w : ℤ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c)
    (ha : (a : ℤ) ∣ x)
    (hb : (b : ℤ) ∣ x)
    (hc : (c : ℤ) ∣ x)
    (hab : (Nat.gcd a b : ℤ) ∣ z)
    (hac : (Nat.gcd a c : ℤ) ∣ z)
    (hbc : (Nat.gcd b c : ℤ) ∣ w) :
    (a : ℤ) * (b : ℤ) * (c : ℤ) ∣ x * z * w := by
  have hL : (tripleLcm a b c : ℤ) ∣ x :=
    tripleLcm_dvd_common_int ha hb hc
  have hp :
      (Nat.lcm (Nat.gcd a b) (Nat.gcd a c) : ℤ) ∣ z :=
    Int.coe_lcm_dvd hab hac
  have hmul := mul_dvd_mul (mul_dvd_mul hL hp) hbc
  have hid :
      (tripleLcm a b c : ℤ) *
          (Nat.lcm (Nat.gcd a b) (Nat.gcd a c) : ℤ) *
          (Nat.gcd b c : ℤ) =
        (a : ℤ) * (b : ℤ) * (c : ℤ) := by
    exact_mod_cast
      triple_anchor_collision_ab_ac_identity
        (a := a) (b := b) (c := c)
        (Nat.ne_of_gt haPos) (Nat.ne_of_gt hbPos) (Nat.ne_of_gt hcPos)
  rw [hid] at hmul
  exact hmul

/--
If the gcd(a,b) and gcd(b,c) repairs collide, the collided point plus a
gcd(a,c)-multiple and the common anchor pay a*b*c.
-/
theorem triple_anchor_collision_ab_bc_product_dvd
    {a b c : ℕ} {x z w : ℤ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c)
    (ha : (a : ℤ) ∣ x)
    (hb : (b : ℤ) ∣ x)
    (hc : (c : ℤ) ∣ x)
    (hab : (Nat.gcd a b : ℤ) ∣ z)
    (hbc : (Nat.gcd b c : ℤ) ∣ z)
    (hac : (Nat.gcd a c : ℤ) ∣ w) :
    (a : ℤ) * (b : ℤ) * (c : ℤ) ∣ x * z * w := by
  have hL : (tripleLcm a b c : ℤ) ∣ x :=
    tripleLcm_dvd_common_int ha hb hc
  have hp :
      (Nat.lcm (Nat.gcd a b) (Nat.gcd b c) : ℤ) ∣ z :=
    Int.coe_lcm_dvd hab hbc
  have hmul := mul_dvd_mul (mul_dvd_mul hL hp) hac
  have hid :
      (tripleLcm a b c : ℤ) *
          (Nat.lcm (Nat.gcd a b) (Nat.gcd b c) : ℤ) *
          (Nat.gcd a c : ℤ) =
        (a : ℤ) * (b : ℤ) * (c : ℤ) := by
    exact_mod_cast
      triple_anchor_collision_ab_bc_identity
        (a := a) (b := b) (c := c)
        (Nat.ne_of_gt haPos) (Nat.ne_of_gt hbPos) (Nat.ne_of_gt hcPos)
  rw [hid] at hmul
  exact hmul

/--
If the gcd(a,c) and gcd(b,c) repairs collide, the collided point plus a
gcd(a,b)-multiple and the common anchor pay a*b*c.
-/
theorem triple_anchor_collision_ac_bc_product_dvd
    {a b c : ℕ} {x z w : ℤ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c)
    (ha : (a : ℤ) ∣ x)
    (hb : (b : ℤ) ∣ x)
    (hc : (c : ℤ) ∣ x)
    (hac : (Nat.gcd a c : ℤ) ∣ z)
    (hbc : (Nat.gcd b c : ℤ) ∣ z)
    (hab : (Nat.gcd a b : ℤ) ∣ w) :
    (a : ℤ) * (b : ℤ) * (c : ℤ) ∣ x * z * w := by
  have hL : (tripleLcm a b c : ℤ) ∣ x :=
    tripleLcm_dvd_common_int ha hb hc
  have hp :
      (Nat.lcm (Nat.gcd a c) (Nat.gcd b c) : ℤ) ∣ z :=
    Int.coe_lcm_dvd hac hbc
  have hmul := mul_dvd_mul (mul_dvd_mul hL hp) hab
  have hid :
      (tripleLcm a b c : ℤ) *
          (Nat.lcm (Nat.gcd a c) (Nat.gcd b c) : ℤ) *
          (Nat.gcd a b : ℤ) =
        (a : ℤ) * (b : ℤ) * (c : ℤ) := by
    exact_mod_cast
      triple_anchor_collision_ac_bc_identity
        (a := a) (b := b) (c := c)
        (Nat.ne_of_gt haPos) (Nat.ne_of_gt hbPos) (Nat.ne_of_gt hcPos)
  rw [hid] at hmul
  exact hmul

/--
If all three pair-gcd repairs collide at one point z, then z pays their lcm.
A second point carrying the triple gcd completes the residual exactly.
-/
theorem triple_anchor_all_collision_product_dvd
    {a b c : ℕ} {x z w : ℤ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c)
    (ha : (a : ℤ) ∣ x)
    (hb : (b : ℤ) ∣ x)
    (hc : (c : ℤ) ∣ x)
    (hab : (Nat.gcd a b : ℤ) ∣ z)
    (hac : (Nat.gcd a c : ℤ) ∣ z)
    (hbc : (Nat.gcd b c : ℤ) ∣ z)
    (hg : (tripleGcd a b c : ℤ) ∣ w) :
    (a : ℤ) * (b : ℤ) * (c : ℤ) ∣ x * z * w := by
  have hL : (tripleLcm a b c : ℤ) ∣ x :=
    tripleLcm_dvd_common_int ha hb hc
  have hp12 :
      (Nat.lcm (Nat.gcd a b) (Nat.gcd a c) : ℤ) ∣ z :=
    Int.coe_lcm_dvd hab hac
  have hp :
      (Nat.lcm
          (Nat.lcm (Nat.gcd a b) (Nat.gcd a c))
          (Nat.gcd b c) : ℤ) ∣ z :=
    Int.coe_lcm_dvd hp12 hbc
  have hmul := mul_dvd_mul (mul_dvd_mul hL hp) hg
  have hid :
      (tripleLcm a b c : ℤ) *
          (Nat.lcm
            (Nat.lcm (Nat.gcd a b) (Nat.gcd a c))
            (Nat.gcd b c) : ℤ) *
          (tripleGcd a b c : ℤ) =
        (a : ℤ) * (b : ℤ) * (c : ℤ) := by
    exact_mod_cast
      triple_anchor_all_collision_identity
        (a := a) (b := b) (c := c)
        (Nat.ne_of_gt haPos) (Nat.ne_of_gt hbPos) (Nat.ne_of_gt hcPos)
  rw [hid] at hmul
  exact hmul

/--
Generic final step for the triple-anchor lemma: once a product of repair
entries covers a*b*c, append any multiple of the fourth modulus d.
-/
theorem triple_anchor_append_fourth_payment
    {a b c d : ℕ} {u y : ℤ}
    (habc : (a : ℤ) * (b : ℤ) * (c : ℤ) ∣ u)
    (hd : (d : ℤ) ∣ y) :
    (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣ u * y := by
  exact mul_dvd_mul habc hd

end Erdos708
