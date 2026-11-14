module

public import Erdos708.Arithmetic
public import Mathlib.Tactic

@[expose] public section

/-!
Trusted arithmetic kernels for the Erdős #708 triple-anchor case.

This module is imported by the trusted Erdős 708 theorem map.

The manuscript writes the three pair gcds as g*u, g*v, g*w.  For Lean it is
cleaner to avoid those quotient variables entirely.  The identities below say
exactly what the anchor plus the repair points pay in each collision pattern.
-/

namespace Erdos708

private theorem max_middle_min_sum {α : Type*} [LinearOrder α]
    [AddCommMonoid α] (x y z : α) :
    max (max x y) z + max (max (min x y) (min x z)) (min y z) +
        min (min x y) z = x + y + z := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · have hxz := le_trans hxy hyz
      simp_all [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
        add_assoc, add_comm, add_left_comm]
    · rcases le_total x z with hxz | hzx
      · simp_all [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
          add_assoc, add_comm, add_left_comm]
      · simp_all [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
          add_assoc, add_comm, add_left_comm]
  · rcases le_total x z with hxz | hzx
    · rcases le_total y z with hyz | hzy
      · simp_all [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
          add_assoc, add_comm, add_left_comm]
      · have hxyEq : x = y := le_antisymm (le_trans hxz hzy) hyx
        have hyzEq : y = z := le_antisymm (le_trans hyx hxz) hzy
        subst y
        subst z
        simp
    · rcases le_total y z with hyz | hzy
      · simp_all [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
          add_assoc, add_comm, add_left_comm]
      · simp_all [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
          add_assoc, add_comm, add_left_comm]

/--
If the repair points for gcd(a,b) and gcd(a,c) collide, their common point pays
the lcm of those two gcds.  Together with gcd(b,c) and the common anchor lcm,
this reconstructs a*b*c exactly.
-/
theorem triple_anchor_collision_ab_ac_identity
    {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    tripleLcm a b c *
        Nat.lcm (Nat.gcd a b) (Nat.gcd a c) *
        Nat.gcd b c =
      a * b * c := by
  have habL : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hL : tripleLcm a b c ≠ 0 := by
    dsimp [tripleLcm]
    exact Nat.lcm_ne_zero habL hc
  have habG : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
  have hacG : Nat.gcd a c ≠ 0 := Nat.gcd_ne_zero_left ha
  have hbcG : Nat.gcd b c ≠ 0 := Nat.gcd_ne_zero_left hb
  have hp : Nat.lcm (Nat.gcd a b) (Nat.gcd a c) ≠ 0 :=
    Nat.lcm_ne_zero habG hacG
  have hLp :
      tripleLcm a b c *
          Nat.lcm (Nat.gcd a b) (Nat.gcd a c) ≠ 0 :=
    mul_ne_zero hL hp
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hleft :
      tripleLcm a b c *
          Nat.lcm (Nat.gcd a b) (Nat.gcd a c) *
          Nat.gcd b c ≠ 0 :=
    mul_ne_zero hLp hbcG
  have hright : a * b * c ≠ 0 := mul_ne_zero hab hc
  apply Nat.eq_of_factorization_eq hleft hright
  intro p
  rw [Nat.factorization_mul hLp hbcG]
  rw [Nat.factorization_mul hL hp]
  dsimp [tripleLcm]
  rw [Nat.factorization_mul hab hc]
  rw [Nat.factorization_mul ha hb]
  rw [Nat.factorization_lcm habL hc]
  rw [Nat.factorization_lcm ha hb]
  rw [Nat.factorization_lcm habG hacG]
  rw [Nat.factorization_gcd ha hb]
  rw [Nat.factorization_gcd ha hc]
  rw [Nat.factorization_gcd hb hc]
  simp only [Finsupp.add_apply, Finsupp.sup_apply, Finsupp.inf_apply]
  omega

/-- Symmetric collision identity when gcd(a,b) and gcd(b,c) share a point. -/
theorem triple_anchor_collision_ab_bc_identity
    {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    tripleLcm a b c *
        Nat.lcm (Nat.gcd a b) (Nat.gcd b c) *
        Nat.gcd a c =
      a * b * c := by
  have habL : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hL : tripleLcm a b c ≠ 0 := by
    dsimp [tripleLcm]
    exact Nat.lcm_ne_zero habL hc
  have habG : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
  have hbcG : Nat.gcd b c ≠ 0 := Nat.gcd_ne_zero_left hb
  have hacG : Nat.gcd a c ≠ 0 := Nat.gcd_ne_zero_left ha
  have hp : Nat.lcm (Nat.gcd a b) (Nat.gcd b c) ≠ 0 :=
    Nat.lcm_ne_zero habG hbcG
  have hLp :
      tripleLcm a b c *
          Nat.lcm (Nat.gcd a b) (Nat.gcd b c) ≠ 0 :=
    mul_ne_zero hL hp
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hleft :
      tripleLcm a b c *
          Nat.lcm (Nat.gcd a b) (Nat.gcd b c) *
          Nat.gcd a c ≠ 0 :=
    mul_ne_zero hLp hacG
  have hright : a * b * c ≠ 0 := mul_ne_zero hab hc
  apply Nat.eq_of_factorization_eq hleft hright
  intro p
  rw [Nat.factorization_mul hLp hacG]
  rw [Nat.factorization_mul hL hp]
  dsimp [tripleLcm]
  rw [Nat.factorization_mul hab hc]
  rw [Nat.factorization_mul ha hb]
  rw [Nat.factorization_lcm habL hc]
  rw [Nat.factorization_lcm ha hb]
  rw [Nat.factorization_lcm habG hbcG]
  rw [Nat.factorization_gcd ha hb]
  rw [Nat.factorization_gcd hb hc]
  rw [Nat.factorization_gcd ha hc]
  simp only [Finsupp.add_apply, Finsupp.sup_apply, Finsupp.inf_apply]
  omega

/-- Symmetric collision identity when gcd(a,c) and gcd(b,c) share a point. -/
theorem triple_anchor_collision_ac_bc_identity
    {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    tripleLcm a b c *
        Nat.lcm (Nat.gcd a c) (Nat.gcd b c) *
        Nat.gcd a b =
      a * b * c := by
  have habL : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hL : tripleLcm a b c ≠ 0 := by
    dsimp [tripleLcm]
    exact Nat.lcm_ne_zero habL hc
  have hacG : Nat.gcd a c ≠ 0 := Nat.gcd_ne_zero_left ha
  have hbcG : Nat.gcd b c ≠ 0 := Nat.gcd_ne_zero_left hb
  have habG : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
  have hp : Nat.lcm (Nat.gcd a c) (Nat.gcd b c) ≠ 0 :=
    Nat.lcm_ne_zero hacG hbcG
  have hLp :
      tripleLcm a b c *
          Nat.lcm (Nat.gcd a c) (Nat.gcd b c) ≠ 0 :=
    mul_ne_zero hL hp
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hleft :
      tripleLcm a b c *
          Nat.lcm (Nat.gcd a c) (Nat.gcd b c) *
          Nat.gcd a b ≠ 0 :=
    mul_ne_zero hLp habG
  have hright : a * b * c ≠ 0 := mul_ne_zero hab hc
  apply Nat.eq_of_factorization_eq hleft hright
  intro p
  rw [Nat.factorization_mul hLp habG]
  rw [Nat.factorization_mul hL hp]
  dsimp [tripleLcm]
  rw [Nat.factorization_mul hab hc]
  rw [Nat.factorization_mul ha hb]
  rw [Nat.factorization_lcm habL hc]
  rw [Nat.factorization_lcm ha hb]
  rw [Nat.factorization_lcm hacG hbcG]
  rw [Nat.factorization_gcd ha hc]
  rw [Nat.factorization_gcd hb hc]
  rw [Nat.factorization_gcd ha hb]
  simp only [Finsupp.add_apply, Finsupp.sup_apply, Finsupp.inf_apply]
  omega

/--
If all three pair-gcd repair choices collide at one point, that point pays the
lcm of all three pair gcds.  One additional triple-gcd multiple completes the
residual exactly.
-/
theorem triple_anchor_all_collision_identity
    {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    tripleLcm a b c *
        Nat.lcm
          (Nat.lcm (Nat.gcd a b) (Nat.gcd a c))
          (Nat.gcd b c) *
        tripleGcd a b c =
      a * b * c := by
  have habL : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hL : tripleLcm a b c ≠ 0 := by
    dsimp [tripleLcm]
    exact Nat.lcm_ne_zero habL hc
  have habG : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
  have hacG : Nat.gcd a c ≠ 0 := Nat.gcd_ne_zero_left ha
  have hbcG : Nat.gcd b c ≠ 0 := Nat.gcd_ne_zero_left hb
  have hp12 : Nat.lcm (Nat.gcd a b) (Nat.gcd a c) ≠ 0 :=
    Nat.lcm_ne_zero habG hacG
  have hp :
      Nat.lcm
        (Nat.lcm (Nat.gcd a b) (Nat.gcd a c))
        (Nat.gcd b c) ≠ 0 :=
    Nat.lcm_ne_zero hp12 hbcG
  have hg : tripleGcd a b c ≠ 0 := by
    dsimp [tripleGcd]
    exact Nat.gcd_ne_zero_left habG
  have hLp :
      tripleLcm a b c *
        Nat.lcm
          (Nat.lcm (Nat.gcd a b) (Nat.gcd a c))
          (Nat.gcd b c) ≠ 0 :=
    mul_ne_zero hL hp
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hleft :
      tripleLcm a b c *
          Nat.lcm
            (Nat.lcm (Nat.gcd a b) (Nat.gcd a c))
            (Nat.gcd b c) *
          tripleGcd a b c ≠ 0 :=
    mul_ne_zero hLp hg
  have hright : a * b * c ≠ 0 := mul_ne_zero hab hc
  apply Nat.eq_of_factorization_eq hleft hright
  intro p
  rw [Nat.factorization_mul hLp hg]
  rw [Nat.factorization_mul hL hp]
  dsimp [tripleLcm, tripleGcd]
  rw [Nat.factorization_mul hab hc]
  rw [Nat.factorization_mul ha hb]
  rw [Nat.factorization_lcm habL hc]
  rw [Nat.factorization_lcm ha hb]
  rw [Nat.factorization_lcm hp12 hbcG]
  rw [Nat.factorization_lcm habG hacG]
  rw [Nat.factorization_gcd ha hb]
  rw [Nat.factorization_gcd ha hc]
  rw [Nat.factorization_gcd hb hc]
  rw [Nat.factorization_gcd habG hc]
  rw [Nat.factorization_gcd ha hb]
  simp only [Finsupp.add_apply, Finsupp.sup_apply, Finsupp.inf_apply]
  exact_mod_cast
    (max_middle_min_sum (a.factorization p) (b.factorization p)
      (c.factorization p))

end Erdos708
