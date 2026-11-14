module

public import Erdos708.TwoAnchorNoBridge
public import Mathlib.Tactic

@[expose] public section

/-!
Regular bridge branch of the Erdős #708 two-anchor lemma.

This module is part of the trusted Erdős 708 theorem map.

Here D is the bridge modulus, a and b are unique at x, and c is assigned to y.
The residuals are g = gcd(a,b) and h = gcd(c,D).  This file handles the branch
where h already has an interval multiple off both anchors.  The only remaining
two-anchor branch after this candidate is the exceptional case in which the
only h-multiples are the two anchors, forcing h = D and then c = 2D.
-/

namespace Erdos708

theorem two_anchor_regular_bridge
    {L x y zh : ℤ} {M a b c D : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c) (hDPos : 0 < D)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hDM : D ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (haD : a ≠ D)
    (hbc : b ≠ c) (hbD : b ≠ D) (hcD : c ≠ D)
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hxy : x ≠ y)
    (haX : (a : ℤ) ∣ x)
    (hbX : (b : ℤ) ∣ x)
    (hcY : (c : ℤ) ∣ y)
    (hDY : (D : ℤ) ∣ y)
    (huniqueA :
      ∀ z, z ∈ integerInterval L M → (a : ℤ) ∣ z → z = x)
    (huniqueB :
      ∀ z, z ∈ integerInterval L M → (b : ℤ) ∣ z → z = x)
    (hzhI : zh ∈ integerInterval L M)
    (hzhDiv : (Nat.gcd c D : ℤ) ∣ zh)
    (hzhX : zh ≠ x)
    (hzhY : zh ≠ y) :
    ∃ u v : ℤ,
      u ∈ integerInterval L M ∧
      v ∈ integerInterval L M ∧
      u ≠ x ∧ u ≠ y ∧
      v ≠ x ∧ v ≠ y ∧
      u ≠ v ∧
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (D : ℤ) ∣
        x * y * u * v := by
  have haHalf : M < 2 * a :=
    modulus_gt_half_of_unique_multiple
      haPos hxI haX huniqueA
  have hbHalf : M < 2 * b :=
    modulus_gt_half_of_unique_multiple
      hbPos hxI hbX huniqueB

  obtain ⟨zg, hzgI, hzgDiv, hzgX, hzgY⟩ :=
    exists_pair_gcd_repair_outside_two
      (L := L) (x := x) (y := y) (M := M)
      (a := a) (b := b)
      haPos hbPos haM hbM haHalf hbHalf hab
      hxI haX hbX

  by_cases hrep : zg = zh
  · let g := Nat.gcd a b
    let h := Nat.gcd c D
    let k := Nat.gcd g h
    have hgPos : 0 < g := by
      dsimp [g]
      exact Nat.gcd_pos_of_pos_left b haPos
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
    have hhD : h ∣ D := by
      dsimp [h]
      exact Nat.gcd_dvd_right _ _
    have hka : k ∣ a := hkg.trans hga
    have hkb : k ∣ b := hkg.trans hgb
    have hkc : k ∣ c := hkh.trans hhc
    have hkD : k ∣ D := hkh.trans hhD
    have hMfour : 4 * k ≤ M :=
      four_distinct_common_multiples_bound_candidate
        (M := M) (g := k) (a := a) (d := b) (b := c) (c := D)
        hkPos haPos hbPos hcPos hDPos
        hka hkb hkc hkD
        haM hbM hcM hDM
        hab hac haD hbc hbD hcD
    have hkGInt : (k : ℤ) ∣ (g : ℤ) := by
      exact_mod_cast hkg
    have hkZg : (k : ℤ) ∣ zg :=
      hkGInt.trans (by simpa [g] using hzgDiv)
    obtain ⟨w, hwI, hwDiv, hwF⟩ :=
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
    have hhAtZg : (Nat.gcd c D : ℤ) ∣ zg := by
      simpa [hrep] using hzhDiv
    have hpay :=
      two_anchor_collision_product_dvd
        haX hbX hcY hDY hzgDiv hhAtZg
        (by simpa [k, g, h] using hwDiv)
    exact
      ⟨zg, w, hzgI, hwI,
        hzgX, hzgY, hwX, hwY, Ne.symm hwZ, hpay⟩
  · have hpay :=
      two_anchor_distinct_repairs_product_dvd
        haX hbX hcY hDY hzgDiv hzhDiv
    exact
      ⟨zg, zh, hzgI, hzhI,
        hzgX, hzgY, hzhX, hzhY, hrep, hpay⟩

end Erdos708
