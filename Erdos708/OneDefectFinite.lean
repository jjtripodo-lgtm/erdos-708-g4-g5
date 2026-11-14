module

public import Erdos708.InitialMultiple
public import Erdos708.ResidualMultiples
public import Erdos708.OneDefectDivisibility
public import Erdos708.OneDefectCommonBounds
public import Mathlib.Tactic

@[expose] public section

/-!
Finite four-modulus one-defect theorem.

This trusted module replaces the manuscript's general recursive propagation
process with a bounded collision tree of depth at most three.  The public
theorem `one_defect_four_moduli` is registered in the banked axiom audit;
helper names retain their historical `_candidate` suffixes.
-/

namespace Erdos708

/--
Continue the one-defect repair after the first residual has collided with the
representative of b.

The first point xa already carries a and d. The second point xb carries b and
gcd(a,d). The theorem either finds a new second-residual multiple or handles
one final collision with xc.
-/
theorem one_defect_after_two_collisions_candidate
    {L : ℤ} {M a d b c : ℕ} {xa xb xc : ℤ}
    (ha : 0 < a) (hd : 0 < d) (hb : 0 < b) (hc : 0 < c)
    (haM : a ≤ M) (hdM : d ≤ M) (hbM : b ≤ M) (hcM : c ≤ M)
    (had : a ≠ d) (hab : a ≠ b) (hac : a ≠ c)
    (hdb : d ≠ b) (hdc : d ≠ c) (hbc : b ≠ c)
    (hxaI : xa ∈ integerInterval L M)
    (hxbI : xb ∈ integerInterval L M)
    (hxcI : xc ∈ integerInterval L M)
    (hxab : xa ≠ xb) (hxac : xa ≠ xc) (hxbc : xb ≠ xc)
    (haXa : (a : ℤ) ∣ xa)
    (hdXa : (d : ℤ) ∣ xa)
    (hg1Xb : (Nat.gcd a d : ℤ) ∣ xb)
    (hbXb : (b : ℤ) ∣ xb)
    (hcXc : (c : ℤ) ∣ xc) :
    ∃ u ∈ integerInterval L M,
      u ≠ xa ∧ u ≠ xb ∧ u ≠ xc ∧
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
        xa * xb * xc * u := by
  let g1 := Nat.gcd a d
  let g2 := Nat.gcd g1 b
  have hg1 : 0 < g1 := by
    dsimp [g1]
    exact Nat.gcd_pos_of_pos_left d ha
  have hg2 : 0 < g2 := by
    dsimp [g2]
    exact Nat.gcd_pos_of_pos_left b hg1
  have hg2g1 : g2 ∣ g1 := by
    dsimp [g2]
    exact Nat.gcd_dvd_left _ _
  have hg2b : g2 ∣ b := by
    dsimp [g2]
    exact Nat.gcd_dvd_right _ _
  have hg1a : g1 ∣ a := by
    dsimp [g1]
    exact Nat.gcd_dvd_left _ _
  have hg1d : g1 ∣ d := by
    dsimp [g1]
    exact Nat.gcd_dvd_right _ _
  have hg2a : g2 ∣ a := hg2g1.trans hg1a
  have hg2d : g2 ∣ d := hg2g1.trans hg1d

  have hMthree : 3 * g2 ≤ M :=
    three_distinct_common_multiples_bound_candidate
      hg2 ha hd hb hg2a hg2d hg2b
      haM hdM hbM had hab hdb

  have hg2Xb : (g2 : ℤ) ∣ xb := by
    have hcast : (g2 : ℤ) ∣ (Nat.gcd a d : ℤ) := by
      exact_mod_cast hg2g1
    exact hcast.trans hg1Xb

  obtain ⟨w, hwI, hwDiv, hwF⟩ :=
    exists_interval_multiple_outside_finset_candidate
      (L := L) (x := xb) (M := M) (d := g2) (k := 2)
      ({xa, xb} : Finset ℤ)
      hg2 hxbI hg2Xb (by simpa using hMthree) (by simp [hxab])
  have hwNeXa : w ≠ xa := by
    simpa using fun h => hwF (by simp [h])
  have hwNeXb : w ≠ xb := by
    simpa using fun h => hwF (by simp [h])

  by_cases hwc : w = xc
  · let g3 := Nat.gcd g2 c
    have hg3 : 0 < g3 := by
      dsimp [g3]
      exact Nat.gcd_pos_of_pos_left c hg2
    have hg3g2 : g3 ∣ g2 := by
      dsimp [g3]
      exact Nat.gcd_dvd_left _ _
    have hg3c : g3 ∣ c := by
      dsimp [g3]
      exact Nat.gcd_dvd_right _ _
    have hg3a : g3 ∣ a := hg3g2.trans hg2a
    have hg3d : g3 ∣ d := hg3g2.trans hg2d
    have hg3b : g3 ∣ b := hg3g2.trans hg2b
    have hMfour : 4 * g3 ≤ M :=
      four_distinct_common_multiples_bound_candidate
        hg3 ha hd hb hc
        hg3a hg3d hg3b hg3c
        haM hdM hbM hcM
        had hab hac hdb hdc hbc
    have hg3Xc : (g3 : ℤ) ∣ xc := by
      have hcast : (g3 : ℤ) ∣ (c : ℤ) := by
        exact_mod_cast hg3c
      exact hcast.trans hcXc
    obtain ⟨u, huI, huDiv, huF⟩ :=
      exists_interval_multiple_outside_finset_candidate
        (L := L) (x := xc) (M := M) (d := g3) (k := 3)
        ({xa, xb, xc} : Finset ℤ)
        hg3 hxcI hg3Xc (by simpa using hMfour) (by simp [hxab, hxac, hxbc])
    have huNeXa : u ≠ xa := by
      intro h
      apply huF
      simp [h]
    have huNeXb : u ≠ xb := by
      intro h
      apply huF
      simp [h]
    have huNeXc : u ≠ xc := by
      intro h
      apply huF
      simp [h]
    have hg2Xc : (g2 : ℤ) ∣ xc := by
      simpa [hwc] using hwDiv
    have hprod :=
      three_collision_product_dvd_candidate
        haXa hdXa hg1Xb hbXb hg2Xc hcXc huDiv
    refine ⟨u, huI, huNeXa, huNeXb, huNeXc, ?_⟩
    simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
  · have hprodADB :=
      two_collision_product_dvd_candidate
        haXa hdXa hg1Xb hbXb hwDiv
    have hprodAll := mul_dvd_mul hprodADB hcXc
    refine ⟨w, hwI, hwNeXa, hwNeXb, hwc, ?_⟩
    simpa [mul_assoc, mul_left_comm, mul_comm] using hprodAll

/--
Continue after the missing modulus d collides with the representative xa of a.
-/
theorem one_defect_after_first_collision_candidate
    {L : ℤ} {M a b c d : ℕ} {xa xb xc : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hxaI : xa ∈ integerInterval L M)
    (hxbI : xb ∈ integerInterval L M)
    (hxcI : xc ∈ integerInterval L M)
    (hxab : xa ≠ xb) (hxac : xa ≠ xc) (hxbc : xb ≠ xc)
    (haXa : (a : ℤ) ∣ xa)
    (hbXb : (b : ℤ) ∣ xb)
    (hcXc : (c : ℤ) ∣ xc)
    (hdXa : (d : ℤ) ∣ xa) :
    ∃ u ∈ integerInterval L M,
      u ≠ xa ∧ u ≠ xb ∧ u ≠ xc ∧
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
        xa * xb * xc * u := by
  let g1 := Nat.gcd a d
  have hg1 : 0 < g1 := by
    dsimp [g1]
    exact Nat.gcd_pos_of_pos_left d ha
  have hg1a : g1 ∣ a := by
    dsimp [g1]
    exact Nat.gcd_dvd_left _ _
  have hg1d : g1 ∣ d := by
    dsimp [g1]
    exact Nat.gcd_dvd_right _ _
  have hMtwo : 2 * g1 ≤ M :=
    two_distinct_common_multiples_bound_candidate
      hg1 ha hd hg1a hg1d haM hdM had
  have hg1Xa : (g1 : ℤ) ∣ xa := by
    have hcast : (g1 : ℤ) ∣ (a : ℤ) := by
      exact_mod_cast hg1a
    exact hcast.trans haXa

  obtain ⟨z, hzI, hzDiv, hzF⟩ :=
    exists_interval_multiple_outside_finset_candidate
      (L := L) (x := xa) (M := M) (d := g1) (k := 1)
      ({xa} : Finset ℤ)
      hg1 hxaI hg1Xa (by simpa using hMtwo) (by simp)
  have hzNeXa : z ≠ xa := by
    intro h
    apply hzF
    simp [h]

  by_cases hzb : z = xb
  · have hg1Xb : (g1 : ℤ) ∣ xb := by
      simpa [hzb] using hzDiv
    exact one_defect_after_two_collisions_candidate
      ha hd hb hc haM hdM hbM hcM
      had hab hac (Ne.symm hbd) (Ne.symm hcd) hbc
      hxaI hxbI hxcI hxab hxac hxbc
      haXa hdXa hg1Xb hbXb hcXc
  · by_cases hzc : z = xc
    · have hg1Xc : (g1 : ℤ) ∣ xc := by
        simpa [hzc] using hzDiv
      obtain ⟨u, huI, huNeXa, huNeXc, huNeXb, hprod⟩ :=
        one_defect_after_two_collisions_candidate
          ha hd hc hb haM hdM hcM hbM
          had hac hab (Ne.symm hcd) (Ne.symm hbd) (Ne.symm hbc)
          hxaI hxcI hxbI hxac hxab (Ne.symm hxbc)
          haXa hdXa hg1Xc hcXc hbXb
      refine ⟨u, huI, huNeXa, huNeXb, huNeXc, ?_⟩
      simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
    · have hprodAD :=
        one_collision_product_dvd_candidate haXa hdXa hzDiv
      have hprodBC := mul_dvd_mul hbXb hcXc
      have hprodAll := mul_dvd_mul hprodAD hprodBC
      refine ⟨z, hzI, hzNeXa, hzb, hzc, ?_⟩
      simpa [mul_assoc, mul_left_comm, mul_comm] using hprodAll

/--
Finite four-modulus one-defect theorem.

Three distinct representatives already cover a,b,c. A fourth modulus d can be
added without using more than one additional distinct interval entry.
-/
theorem one_defect_four_moduli
    {L : ℤ} {M a b c d : ℕ} {xa xb xc : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hxaI : xa ∈ integerInterval L M)
    (hxbI : xb ∈ integerInterval L M)
    (hxcI : xc ∈ integerInterval L M)
    (hxab : xa ≠ xb) (hxac : xa ≠ xc) (hxbc : xb ≠ xc)
    (haXa : (a : ℤ) ∣ xa)
    (hbXb : (b : ℤ) ∣ xb)
    (hcXc : (c : ℤ) ∣ xc) :
    ∃ u ∈ integerInterval L M,
      u ≠ xa ∧ u ≠ xb ∧ u ≠ xc ∧
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
        xa * xb * xc * u := by
  obtain ⟨y, hyI, hdY⟩ :=
    exists_interval_multiple_of_le_candidate
      (L := L) (M := M) (d := d) hd hdM
  by_cases hya : y = xa
  · exact one_defect_after_first_collision_candidate
      ha hb hc hd haM hbM hcM hdM
      hab hac had hbc hbd hcd
      hxaI hxbI hxcI hxab hxac hxbc
      haXa hbXb hcXc (by simpa [hya] using hdY)
  · by_cases hyb : y = xb
    · obtain ⟨u, huI, huNeXb, huNeXa, huNeXc, hprod⟩ :=
        one_defect_after_first_collision_candidate
          hb ha hc hd hbM haM hcM hdM
          (Ne.symm hab) hbc hbd hac had hcd
          hxbI hxaI hxcI (Ne.symm hxab) hxbc hxac
          hbXb haXa hcXc (by simpa [hyb] using hdY)
      refine ⟨u, huI, huNeXa, huNeXb, huNeXc, ?_⟩
      simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
    · by_cases hyc : y = xc
      · obtain ⟨u, huI, huNeXc, huNeXa, huNeXb, hprod⟩ :=
          one_defect_after_first_collision_candidate
            hc ha hb hd hcM haM hbM hdM
            (Ne.symm hac) (Ne.symm hbc) hcd hab had hbd
            hxcI hxaI hxbI (Ne.symm hxac) (Ne.symm hxbc) hxab
            hcXc haXa hbXb (by simpa [hyc] using hdY)
        refine ⟨u, huI, huNeXa, huNeXb, huNeXc, ?_⟩
        simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
      · have hprod :=
          mul_dvd_mul
            (mul_dvd_mul (mul_dvd_mul haXa hbXb) hcXc)
            hdY
        refine ⟨y, hyI, hya, hyb, hyc, ?_⟩
        simpa [mul_assoc] using hprod

end Erdos708
