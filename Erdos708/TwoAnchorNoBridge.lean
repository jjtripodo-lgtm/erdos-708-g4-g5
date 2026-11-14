module

public import Erdos708.OneDefectDivisibility
public import Erdos708.OneDefectCommonBounds
public import Erdos708.TripleAnchorRepairs
public import Erdos708.Intervals
public import Mathlib.Tactic

@[expose] public section

/-!
No-bridge two-anchor theorem for Erdős #708.

This module is part of the trusted Erdős 708 theorem map.

It formalizes the first branch of the manuscript's two-anchor lemma: two
moduli are unique at x and two are unique at y, with no modulus using both
anchors.  Pair-gcd repairs are chosen off the anchors.  If those repairs
collide, a final gcd-of-gcds multiple repairs the collision.
-/

namespace Erdos708

/-- Distinct pair-gcd repairs together with the two anchors cover all four moduli. -/
theorem two_anchor_distinct_repairs_product_dvd
    {a b c d : ℕ} {x y zg zh : ℤ}
    (haX : (a : ℤ) ∣ x)
    (hbX : (b : ℤ) ∣ x)
    (hcY : (c : ℤ) ∣ y)
    (hdY : (d : ℤ) ∣ y)
    (hgZ : (Nat.gcd a b : ℤ) ∣ zg)
    (hhZ : (Nat.gcd c d : ℤ) ∣ zh) :
    (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
      x * y * zg * zh := by
  have habPay :=
    one_collision_product_dvd_candidate haX hbX hgZ
  have hcdPay :=
    one_collision_product_dvd_candidate hcY hdY hhZ
  have hmul := mul_dvd_mul habPay hcdPay
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/--
If the two pair-gcd repairs collide at z, then z pays the lcm of the two
residual gcds and a further gcd-of-gcds multiple w completes the product.
-/
theorem two_anchor_collision_product_dvd
    {a b c d : ℕ} {x y z w : ℤ}
    (haX : (a : ℤ) ∣ x)
    (hbX : (b : ℤ) ∣ x)
    (hcY : (c : ℤ) ∣ y)
    (hdY : (d : ℤ) ∣ y)
    (hgZ : (Nat.gcd a b : ℤ) ∣ z)
    (hhZ : (Nat.gcd c d : ℤ) ∣ z)
    (hkW :
      (Nat.gcd (Nat.gcd a b) (Nat.gcd c d) : ℤ) ∣ w) :
    (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
      x * y * z * w := by
  have hLab : (Nat.lcm a b : ℤ) ∣ x :=
    Int.coe_lcm_dvd haX hbX
  have hLcd : (Nat.lcm c d : ℤ) ∣ y :=
    Int.coe_lcm_dvd hcY hdY
  have hgh :
      (Nat.gcd a b : ℤ) * (Nat.gcd c d : ℤ) ∣ z * w :=
    one_collision_product_dvd_candidate hgZ hhZ hkW
  have hmul := mul_dvd_mul (mul_dvd_mul hLab hLcd) hgh
  have hidNat :
      Nat.lcm a b * Nat.lcm c d *
          (Nat.gcd a b * Nat.gcd c d) =
        a * b * c * d := by
    calc
      Nat.lcm a b * Nat.lcm c d *
            (Nat.gcd a b * Nat.gcd c d)
          =
        (Nat.lcm a b * Nat.gcd a b) *
          (Nat.lcm c d * Nat.gcd c d) := by ring
      _ = (a * b) * (c * d) := by
        rw [lcm_mul_gcd_product_candidate, lcm_mul_gcd_product_candidate]
      _ = a * b * c * d := by ring
  have hid :
      (Nat.lcm a b : ℤ) * (Nat.lcm c d : ℤ) *
          ((Nat.gcd a b : ℤ) * (Nat.gcd c d : ℤ)) =
        (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) := by
    exact_mod_cast hidNat
  rw [hid] at hmul
  simpa [mul_assoc] using hmul

/--
No-bridge branch of the two-anchor lemma.

The conclusion exposes the four distinct interval entries directly: the two
anchors and two off-anchor repairs.
-/
theorem two_anchor_no_bridge
    {L x y : ℤ} {M a b c d : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c) (hdPos : 0 < d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hxy : x ≠ y)
    (haX : (a : ℤ) ∣ x)
    (hbX : (b : ℤ) ∣ x)
    (hcY : (c : ℤ) ∣ y)
    (hdY : (d : ℤ) ∣ y)
    (huniqueA :
      ∀ z, z ∈ integerInterval L M → (a : ℤ) ∣ z → z = x)
    (huniqueB :
      ∀ z, z ∈ integerInterval L M → (b : ℤ) ∣ z → z = x)
    (huniqueC :
      ∀ z, z ∈ integerInterval L M → (c : ℤ) ∣ z → z = y)
    (huniqueD :
      ∀ z, z ∈ integerInterval L M → (d : ℤ) ∣ z → z = y) :
    ∃ u v : ℤ,
      u ∈ integerInterval L M ∧
      v ∈ integerInterval L M ∧
      u ≠ x ∧ u ≠ y ∧
      v ≠ x ∧ v ≠ y ∧
      u ≠ v ∧
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
        x * y * u * v := by
  have haHalf : M < 2 * a :=
    modulus_gt_half_of_unique_multiple
      haPos hxI haX huniqueA
  have hbHalf : M < 2 * b :=
    modulus_gt_half_of_unique_multiple
      hbPos hxI hbX huniqueB
  have hcHalf : M < 2 * c :=
    modulus_gt_half_of_unique_multiple
      hcPos hyI hcY huniqueC
  have hdHalf : M < 2 * d :=
    modulus_gt_half_of_unique_multiple
      hdPos hyI hdY huniqueD

  obtain ⟨zg, hzgI, hzgD, hzgX, hzgY⟩ :=
    exists_pair_gcd_repair_outside_two
      (L := L) (x := x) (y := y) (M := M)
      (a := a) (b := b)
      haPos hbPos haM hbM haHalf hbHalf hab
      hxI haX hbX

  obtain ⟨zh, hzhI, hzhD, hzhY, hzhX⟩ :=
    exists_pair_gcd_repair_outside_two
      (L := L) (x := y) (y := x) (M := M)
      (a := c) (b := d)
      hcPos hdPos hcM hdM hcHalf hdHalf hcd
      hyI hcY hdY

  by_cases hrep : zg = zh
  · let g := Nat.gcd a b
    let h := Nat.gcd c d
    let k := Nat.gcd g h
    have hgPos : 0 < g := by
      dsimp [g]
      exact Nat.gcd_pos_of_pos_left b haPos
    have hhPos : 0 < h := by
      dsimp [h]
      exact Nat.gcd_pos_of_pos_left d hcPos
    have hkPos : 0 < k := by
      dsimp [k]
      exact Nat.gcd_pos_of_pos_left h hgPos
    have hkg : k ∣ g := by
      dsimp [k]
      exact Nat.gcd_dvd_left _ _
    have hkh : k ∣ h := by
      dsimp [k]
      exact Nat.gcd_dvd_right _ _
    have hga : g ∣ a := by
      dsimp [g]
      exact Nat.gcd_dvd_left _ _
    have hgb : g ∣ b := by
      dsimp [g]
      exact Nat.gcd_dvd_right _ _
    have hhc : h ∣ c := by
      dsimp [h]
      exact Nat.gcd_dvd_left _ _
    have hhd : h ∣ d := by
      dsimp [h]
      exact Nat.gcd_dvd_right _ _
    have hka : k ∣ a := hkg.trans hga
    have hkb : k ∣ b := hkg.trans hgb
    have hkc : k ∣ c := hkh.trans hhc
    have hkd : k ∣ d := hkh.trans hhd
    have hMfour : 4 * k ≤ M :=
      four_distinct_common_multiples_bound_candidate
        (M := M) (g := k) (a := a) (d := b) (b := c) (c := d)
        hkPos haPos hbPos hcPos hdPos
        hka hkb hkc hkd
        haM hbM hcM hdM
        hab hac had hbc hbd hcd
    have hkGInt : (k : ℤ) ∣ (g : ℤ) := by
      exact_mod_cast hkg
    have hkZg : (k : ℤ) ∣ zg :=
      hkGInt.trans (by simpa [g] using hzgD)
    obtain ⟨w, hwI, hwD, hwF⟩ :=
      exists_interval_multiple_outside_finset_candidate
        (L := L) (x := zg) (M := M) (d := k) (k := 3)
        ({x, y, zg} : Finset ℤ)
        hkPos hzgI hkZg (by simpa using hMfour) Finset.card_le_three
    have hwX : w ≠ x := by
      intro hw
      apply hwF
      simp [hw]
    have hwY : w ≠ y := by
      intro hw
      apply hwF
      simp [hw]
    have hwZ : w ≠ zg := by
      intro hw
      apply hwF
      simp [hw]
    have hhAtZg : (Nat.gcd c d : ℤ) ∣ zg := by
      simpa [hrep] using hzhD
    have hpay :=
      two_anchor_collision_product_dvd
        haX hbX hcY hdY hzgD hhAtZg
        (by simpa [k, g, h] using hwD)
    exact
      ⟨zg, w, hzgI, hwI,
        hzgX, hzgY, hwX, hwY, Ne.symm hwZ, hpay⟩
  · have hpay :=
      two_anchor_distinct_repairs_product_dvd
        haX hbX hcY hdY hzgD hzhD
    exact
      ⟨zg, zh, hzgI, hzhI,
        hzgX, hzgY, hzhX, hzhY, hrep, hpay⟩

end Erdos708
