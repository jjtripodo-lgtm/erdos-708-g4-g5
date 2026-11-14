module

public import Erdos708.ResidualMultiples
public import Erdos708.UpperHalf
public import Mathlib.Tactic

@[expose] public section

/-!
Repair-point existence lemmas for the Erdős #708 triple-anchor
case.

This module is imported by the trusted Erdős 708 theorem map.
It converts the banked upper-half gcd bounds into the exact interval selections
used by the manuscript: one off-anchor repair for each pair gcd, and, in the
all-collision branch, a further triple-gcd multiple outside three occupied
points.
-/

namespace Erdos708

/--
Two distinct upper-half moduli sharing an anchor have a pair-gcd multiple in the
interval outside any two forbidden points.
-/
theorem exists_pair_gcd_repair_outside_two
    {L x y : ℤ} {M a b : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b)
    (haM : a ≤ M) (hbM : b ≤ M)
    (haHalf : M < 2 * a) (hbHalf : M < 2 * b)
    (habNe : a ≠ b)
    (hxI : x ∈ integerInterval L M)
    (haX : (a : ℤ) ∣ x)
    (hbX : (b : ℤ) ∣ x) :
    ∃ z ∈ integerInterval L M,
      (Nat.gcd a b : ℤ) ∣ z ∧ z ≠ x ∧ z ≠ y := by
  have hdPos : 0 < Nat.gcd a b :=
    Nat.gcd_pos_of_pos_left b haPos
  have hbound : 3 * Nat.gcd a b ≤ M :=
    pair_gcd_le_one_third
      haPos hbPos haM hbM haHalf hbHalf habNe
  have hdA : Nat.gcd a b ∣ a :=
    Nat.gcd_dvd_left a b
  have hdAInt : (Nat.gcd a b : ℤ) ∣ (a : ℤ) := by
    exact_mod_cast hdA
  have hdX : (Nat.gcd a b : ℤ) ∣ x :=
    dvd_trans hdAInt haX
  have hF : ({x, y} : Finset ℤ).card ≤ 2 := by
    by_cases hxy : x = y
    · subst y
      simp
    · simp [hxy]
  rcases
      exists_interval_multiple_outside_finset_candidate
        (F := ({x, y} : Finset ℤ))
        (L := L) (x := x) (M := M)
        (d := Nat.gcd a b) (k := 2)
        hdPos hxI hdX (by simpa using hbound) hF with
    ⟨z, hzI, hzd, hzF⟩
  have hzx : z ≠ x := by
    intro h
    apply hzF
    subst z
    simp
  have hzy : z ≠ y := by
    intro h
    apply hzF
    subst z
    simp
  exact ⟨z, hzI, hzd, hzx, hzy⟩

/--
Choose the three pair-gcd repairs used in the triple-anchor proof.  They are all
off the two anchors, but are deliberately not required to be mutually distinct;
their equality pattern drives the later collision case split.
-/
theorem exists_triple_anchor_pair_repairs
    {L x y : ℤ} {M a b c : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M)
    (haHalf : M < 2 * a) (hbHalf : M < 2 * b) (hcHalf : M < 2 * c)
    (habNe : a ≠ b) (hacNe : a ≠ c) (hbcNe : b ≠ c)
    (hxI : x ∈ integerInterval L M)
    (haX : (a : ℤ) ∣ x)
    (hbX : (b : ℤ) ∣ x)
    (hcX : (c : ℤ) ∣ x) :
    ∃ zab zac zbc : ℤ,
      zab ∈ integerInterval L M ∧
      zac ∈ integerInterval L M ∧
      zbc ∈ integerInterval L M ∧
      (Nat.gcd a b : ℤ) ∣ zab ∧
      (Nat.gcd a c : ℤ) ∣ zac ∧
      (Nat.gcd b c : ℤ) ∣ zbc ∧
      zab ≠ x ∧ zab ≠ y ∧
      zac ≠ x ∧ zac ≠ y ∧
      zbc ≠ x ∧ zbc ≠ y := by
  rcases
      exists_pair_gcd_repair_outside_two
        (L := L) (x := x) (y := y) (M := M)
        (a := a) (b := b)
        haPos hbPos haM hbM haHalf hbHalf habNe hxI haX hbX with
    ⟨zab, hzabI, hzabD, hzabX, hzabY⟩
  rcases
      exists_pair_gcd_repair_outside_two
        (L := L) (x := x) (y := y) (M := M)
        (a := a) (b := c)
        haPos hcPos haM hcM haHalf hcHalf hacNe hxI haX hcX with
    ⟨zac, hzacI, hzacD, hzacX, hzacY⟩
  rcases
      exists_pair_gcd_repair_outside_two
        (L := L) (x := x) (y := y) (M := M)
        (a := b) (b := c)
        hbPos hcPos hbM hcM hbHalf hcHalf hbcNe hxI hbX hcX with
    ⟨zbc, hzbcI, hzbcD, hzbcX, hzbcY⟩
  exact
    ⟨zab, zac, zbc,
      hzabI, hzacI, hzbcI,
      hzabD, hzacD, hzbcD,
      hzabX, hzabY, hzacX, hzacY, hzbcX, hzbcY⟩

/--
For three distinct upper-half moduli, an all-collision repair point can be
followed by a triple-gcd multiple outside the two anchors and the collision
point.
-/
theorem exists_triple_gcd_repair_outside_three
    {L x y z : ℤ} {M a b c : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M)
    (haHalf : M < 2 * a) (hbHalf : M < 2 * b) (hcHalf : M < 2 * c)
    (habNe : a ≠ b) (hacNe : a ≠ c) (hbcNe : b ≠ c)
    (hxI : x ∈ integerInterval L M)
    (haX : (a : ℤ) ∣ x) :
    ∃ w ∈ integerInterval L M,
      (tripleGcd a b c : ℤ) ∣ w ∧
      w ≠ x ∧ w ≠ y ∧ w ≠ z := by
  have hgPos : 0 < tripleGcd a b c := by
    dsimp [tripleGcd]
    exact Nat.gcd_pos_of_pos_left c (Nat.gcd_pos_of_pos_left b haPos)
  have hfive : 5 * tripleGcd a b c ≤ M :=
    triple_gcd_le_one_fifth
      haPos hbPos hcPos
      haM hbM hcM
      haHalf hbHalf hcHalf
      habNe hacNe hbcNe
  have hgA : tripleGcd a b c ∣ a := by
    dsimp [tripleGcd]
    exact dvd_trans
      (Nat.gcd_dvd_left (Nat.gcd a b) c)
      (Nat.gcd_dvd_left a b)
  have hgAInt : (tripleGcd a b c : ℤ) ∣ (a : ℤ) := by
    exact_mod_cast hgA
  have hgX : (tripleGcd a b c : ℤ) ∣ x :=
    dvd_trans hgAInt haX
  have hF : ({x, y, z} : Finset ℤ).card ≤ 3 := by
    exact Finset.card_le_three
  have hfour : (3 + 1) * tripleGcd a b c ≤ M := by
    omega
  rcases
      exists_interval_multiple_outside_finset_candidate
        (F := ({x, y, z} : Finset ℤ))
        (L := L) (x := x) (M := M)
        (d := tripleGcd a b c) (k := 3)
        hgPos hxI hgX hfour hF with
    ⟨w, hwI, hwD, hwF⟩
  have hwx : w ≠ x := by
    intro h
    apply hwF
    subst w
    simp
  have hwy : w ≠ y := by
    intro h
    apply hwF
    subst w
    simp
  have hwz : w ≠ z := by
    intro h
    apply hwF
    subst w
    simp
  exact ⟨w, hwI, hwD, hwx, hwy, hwz⟩

end Erdos708
