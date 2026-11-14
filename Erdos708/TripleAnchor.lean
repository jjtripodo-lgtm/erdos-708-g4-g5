module

public import Erdos708.TripleAnchorPayments
public import Erdos708.TripleAnchorRepairs
public import Erdos708.Intervals
public import Mathlib.Tactic

@[expose] public section

/-!
End-to-end triple-anchor lemma for Erdős #708.

This module is imported by the trusted Erdős 708 theorem map.

It follows the manuscript's exact finite case split.  Three upper-half moduli
share one unique anchor x; a fourth modulus has a different interval multiple y.
We choose one off-anchor repair multiple for each pair gcd.  If the three repair
points are distinct, use all three.  If exactly two collide, the collision pays
the lcm of the corresponding pair gcds.  If all three collide, one additional
triple-gcd multiple outside the occupied points completes the payment.

The conclusion keeps the distinct-entry bookkeeping explicit: either five
distinct entries (two anchors plus three repairs) or four distinct entries (two
anchors plus two repairs) cover the four-modulus product.
-/

namespace Erdos708

theorem triple_anchor_four_moduli
    {L x y : ℤ} {M a b c d : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M)
    (habNe : a ≠ b) (hacNe : a ≠ c) (hbcNe : b ≠ c)
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hxy : x ≠ y)
    (haX : (a : ℤ) ∣ x)
    (hbX : (b : ℤ) ∣ x)
    (hcX : (c : ℤ) ∣ x)
    (hdY : (d : ℤ) ∣ y)
    (huniqueA :
      ∀ z, z ∈ integerInterval L M → (a : ℤ) ∣ z → z = x)
    (huniqueB :
      ∀ z, z ∈ integerInterval L M → (b : ℤ) ∣ z → z = x)
    (huniqueC :
      ∀ z, z ∈ integerInterval L M → (c : ℤ) ∣ z → z = x) :
    (∃ u v w : ℤ,
      u ∈ integerInterval L M ∧
      v ∈ integerInterval L M ∧
      w ∈ integerInterval L M ∧
      u ≠ x ∧ u ≠ y ∧
      v ≠ x ∧ v ≠ y ∧
      w ≠ x ∧ w ≠ y ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
        x * y * u * v * w) ∨
    (∃ u v : ℤ,
      u ∈ integerInterval L M ∧
      v ∈ integerInterval L M ∧
      u ≠ x ∧ u ≠ y ∧
      v ≠ x ∧ v ≠ y ∧
      u ≠ v ∧
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
        x * y * u * v) := by
  have haHalf : M < 2 * a :=
    modulus_gt_half_of_unique_multiple
      haPos hxI haX huniqueA
  have hbHalf : M < 2 * b :=
    modulus_gt_half_of_unique_multiple
      hbPos hxI hbX huniqueB
  have hcHalf : M < 2 * c :=
    modulus_gt_half_of_unique_multiple
      hcPos hxI hcX huniqueC

  obtain
      ⟨zab, zac, zbc,
        hzabI, hzacI, hzbcI,
        hzabD, hzacD, hzbcD,
        hzabX, hzabY, hzacX, hzacY, hzbcX, hzbcY⟩ :=
    exists_triple_anchor_pair_repairs
      (L := L) (x := x) (y := y) (M := M)
      (a := a) (b := b) (c := c)
      haPos hbPos hcPos
      haM hbM hcM
      haHalf hbHalf hcHalf
      habNe hacNe hbcNe
      hxI haX hbX hcX

  by_cases habac : zab = zac
  · have hacAtZab : (Nat.gcd a c : ℤ) ∣ zab := by
      simpa [habac] using hzacD
    by_cases hbcab : zbc = zab
    · have hbcAtZab : (Nat.gcd b c : ℤ) ∣ zab := by
        simpa [hbcab] using hzbcD
      obtain ⟨w, hwI, hwD, hwX, hwY, hwZ⟩ :=
        exists_triple_gcd_repair_outside_three
          (L := L) (x := x) (y := y) (z := zab) (M := M)
          (a := a) (b := b) (c := c)
          haPos hbPos hcPos
          haM hbM hcM
          haHalf hbHalf hcHalf
          habNe hacNe hbcNe
          hxI haX
      have habcPay :=
        triple_anchor_all_collision_product_dvd
          haPos hbPos hcPos
          haX hbX hcX
          hzabD hacAtZab hbcAtZab hwD
      have habcdPay :=
        triple_anchor_append_fourth_payment habcPay hdY
      right
      refine
        ⟨zab, w, hzabI, hwI,
          hzabX, hzabY, hwX, hwY, ?_, ?_⟩
      · exact Ne.symm hwZ
      · simpa [mul_assoc, mul_left_comm, mul_comm] using habcdPay
    · have habcPay :=
        triple_anchor_collision_ab_ac_product_dvd
          haPos hbPos hcPos
          haX hbX hcX
          hzabD hacAtZab hzbcD
      have habcdPay :=
        triple_anchor_append_fourth_payment habcPay hdY
      right
      refine
        ⟨zab, zbc, hzabI, hzbcI,
          hzabX, hzabY, hzbcX, hzbcY, ?_, ?_⟩
      · exact Ne.symm hbcab
      · simpa [mul_assoc, mul_left_comm, mul_comm] using habcdPay
  · by_cases habbc : zab = zbc
    · have hbcAtZab : (Nat.gcd b c : ℤ) ∣ zab := by
        simpa [habbc] using hzbcD
      have habcPay :=
        triple_anchor_collision_ab_bc_product_dvd
          haPos hbPos hcPos
          haX hbX hcX
          hzabD hbcAtZab hzacD
      have habcdPay :=
        triple_anchor_append_fourth_payment habcPay hdY
      right
      refine
        ⟨zab, zac, hzabI, hzacI,
          hzabX, hzabY, hzacX, hzacY, habac, ?_⟩
      simpa [mul_assoc, mul_left_comm, mul_comm] using habcdPay
    · by_cases hacbc : zac = zbc
      · have hbcAtZac : (Nat.gcd b c : ℤ) ∣ zac := by
          simpa [hacbc] using hzbcD
        have habcPay :=
          triple_anchor_collision_ac_bc_product_dvd
            haPos hbPos hcPos
            haX hbX hcX
            hzacD hbcAtZac hzabD
        have habcdPay :=
          triple_anchor_append_fourth_payment habcPay hdY
        right
        refine
          ⟨zac, zab, hzacI, hzabI,
            hzacX, hzacY, hzabX, hzabY, ?_, ?_⟩
        · exact Ne.symm habac
        · simpa [mul_assoc, mul_left_comm, mul_comm] using habcdPay
      · have habcPay :=
          triple_anchor_distinct_repairs_product_dvd
            haPos hbPos hcPos
            haX hbX hcX
            hzabD hzacD hzbcD
        have habcdPay :=
          triple_anchor_append_fourth_payment habcPay hdY
        left
        refine
          ⟨zab, zac, zbc,
            hzabI, hzacI, hzbcI,
            hzabX, hzabY,
            hzacX, hzacY,
            hzbcX, hzbcY,
            habac, habbc, hacbc, ?_⟩
        simpa [mul_assoc, mul_left_comm, mul_comm] using habcdPay

end Erdos708
