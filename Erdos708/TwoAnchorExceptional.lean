module

public import Erdos708.TwoAnchorExceptionalCore
public import Erdos708.TwoAnchorBridgeRegular
public import Erdos708.BridgeProduct
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Exceptional two-anchor bridge theorem for Erdős #708.

Setup:
* a,b have unique anchor x;
* c has unique anchor y;
* bridge modulus D divides both anchors;
* h=gcd(c,D) has no interval multiple outside the two anchors.

The proof derives h=D, c=2D, and D∤a,b.  It then sets
  g=gcd(a,b), r=gcd(a,D), s=gcd(b,D)
and applies Hall to the off-two-anchor multiple families for g,r,s.

The full-union Hall contradiction uses the step-toward-the-other-anchor
rigidity lemma from CandidateTwoAnchorExceptionalCore rather than sorting two
four-point arithmetic progressions.
-/

namespace Erdos708

theorem hall_fin_three_of_union_bounds
    {α : Type*} [DecidableEq α]
    (C : Fin 3 → Finset α)
    (h1 : ∀ i, 1 ≤ (C i).card)
    (h2 : ∀ i j, i ≠ j → 2 ≤ (C i ∪ C j).card)
    (h3 : 3 ≤ ((C 0 ∪ C 1) ∪ C 2).card) :
    ∀ t : Finset (Fin 3), t.card ≤ (t.biUnion C).card := by
  classical
  intro t
  have htle : t.card ≤ 3 := by
    calc
      t.card ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_univ t
      _ = 3 := by simp
  interval_cases ht : t.card
  · have hzero : t = ∅ := Finset.card_eq_zero.mp ht
    simp [hzero]
  · rcases Finset.card_eq_one.mp ht with ⟨i, rfl⟩
    simpa using h1 i
  · rcases Finset.card_eq_two.mp ht with ⟨i, j, hij, rfl⟩
    simpa [hij] using h2 i j hij
  · have hUniv : t = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using ht
    subst t
    have hbi : (Finset.univ : Finset (Fin 3)).biUnion C =
        ((C 0 ∪ C 1) ∪ C 2) := by
      ext z
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_union]
      constructor
      · rintro ⟨i, hz⟩
        fin_cases i <;> simp_all
      · intro hz
        rcases hz with hz | hz
        · rcases hz with hz | hz
          · exact ⟨0, hz⟩
          · exact ⟨1, hz⟩
        · exact ⟨2, hz⟩
    rw [hbi]
    exact h3

theorem exists_distinct_representatives_fin_three_of_union_bounds
    {α : Type*} [DecidableEq α]
    (C : Fin 3 → Finset α)
    (h1 : ∀ i, 1 ≤ (C i).card)
    (h2 : ∀ i j, i ≠ j → 2 ≤ (C i ∪ C j).card)
    (h3 : 3 ≤ ((C 0 ∪ C 1) ∪ C 2).card) :
    ∃ f : Fin 3 → α, Function.Injective f ∧ ∀ i, f i ∈ C i := by
  classical
  exact (Finset.all_card_le_biUnion_card_iff_exists_injective C).mp
    (hall_fin_three_of_union_bounds C h1 h2 h3)

/-- Exceptional full-union Hall bound for g,r,s. -/
theorem exceptional_bridge_full_union_ge_three
    {L x y : ℤ} {M a b c D : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c) (hDPos : 0 < D)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hdir : y = x + (D : ℤ) ∨ x = y + (D : ℤ))
    (haX : (a : ℤ) ∣ x)
    (hbX : (b : ℤ) ∣ x)
    (hDX : (D : ℤ) ∣ x)
    (hcTwo : c = 2 * D)
    (hnotDa : ¬ D ∣ a)
    (hnotDb : ¬ D ∣ b)
    (haHalf : M < 2 * a)
    (hbHalf : M < 2 * b)
    (hcHalf : M < 2 * c) :
    let g := Nat.gcd a b
    let r := Nat.gcd a D
    let s := Nat.gcd b D
    let Cg := offTwoAnchorMultiples L M x y g
    let Cr := offTwoAnchorMultiples L M x y r
    let Cs := offTwoAnchorMultiples L M x y s
    3 ≤ ((Cg ∪ Cr) ∪ Cs).card := by
  classical
  dsimp
  let g := Nat.gcd a b
  let r := Nat.gcd a D
  let s := Nat.gcd b D
  let Cg := offTwoAnchorMultiples L M x y g
  let Cr := offTwoAnchorMultiples L M x y r
  let Cs := offTwoAnchorMultiples L M x y s

  have hrData :=
    gcd_proper_divisor_right haPos hDPos hnotDa
  have hsData :=
    gcd_proper_divisor_right hbPos hDPos hnotDb
  have hrPos : 0 < r := by simpa [r] using hrData.1
  have hsPos : 0 < s := by simpa [s] using hsData.1
  have hrD : r ∣ D := by simpa [r] using hrData.2.1
  have hsD : s ∣ D := by simpa [s] using hsData.2.1
  have hrNeD : r ≠ D := by simpa [r] using hrData.2.2
  have hsNeD : s ≠ D := by simpa [s] using hsData.2.2
  have hrLtD : r < D := by
    have hle := Nat.le_of_dvd hDPos hrD
    omega
  have hsLtD : s < D := by
    have hle := Nat.le_of_dvd hDPos hsD
    omega
  have htwoR : 2 * r ≤ D :=
    two_mul_le_of_dvd_ne_candidate
      hrPos hDPos hrD (Ne.symm hrNeD)
  have htwoS : 2 * s ≤ D :=
    two_mul_le_of_dvd_ne_candidate
      hsPos hDPos hsD (Ne.symm hsNeD)
  have htwoD : 2 * D ≤ M := by
    rw [← hcTwo]
    exact hcM
  have hfourR : 4 * r ≤ M := by omega
  have hfourS : 4 * s ≤ M := by omega

  have hrX : (r : ℤ) ∣ x := by
    have hNat : r ∣ a := by
      dsimp [r]
      exact Nat.gcd_dvd_left a D
    have hCast : (r : ℤ) ∣ (a : ℤ) := by exact_mod_cast hNat
    exact hCast.trans haX
  have hsX : (s : ℤ) ∣ x := by
    have hNat : s ∣ b := by
      dsimp [s]
      exact Nat.gcd_dvd_left b D
    have hCast : (s : ℤ) ∣ (b : ℤ) := by exact_mod_cast hNat
    exact hCast.trans hbX

  have hCr2 : 2 ≤ Cr.card := by
    simpa [Cr, r] using
      (off_two_anchor_card_ge_two_of_four_mul_le
        (L := L) (x := x) (y := y) (M := M) (d := r)
        hrPos hxI hrX hfourR)
  have hCs2 : 2 ≤ Cs.card := by
    simpa [Cs, s] using
      (off_two_anchor_card_ge_two_of_four_mul_le
        (L := L) (x := x) (y := y) (M := M) (d := s)
        hsPos hxI hsX hfourS)

  by_contra hbad
  have hU2 : ((Cg ∪ Cr) ∪ Cs).card ≤ 2 := by
    by_contra hnot
    have hge : 3 ≤ ((Cg ∪ Cr) ∪ Cs).card := by omega
    exact hbad hge
  have hCrSub : Cr ⊆ (Cg ∪ Cr) ∪ Cs := by
    intro z hz
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ hz)
  have hCsSub : Cs ⊆ (Cg ∪ Cr) ∪ Cs :=
    Finset.subset_union_right
  have hEqRS : Cr = Cs :=
    equal_of_two_large_subsets_of_card_le_two
      hCrSub hCsSub hCr2 hCs2 hU2

  have hrs : r = s := by
    apply eq_of_equal_off_two_anchor_multiples
      (L := L) (x := x) (y := y) (M := M) (D := D)
      hxI hyI hdir hrPos hsPos hrLtD hsLtD hrX hsX
    simpa [Cr, Cs] using hEqRS

  have hrA : r ∣ a := by
    dsimp [r]
    exact Nat.gcd_dvd_left a D
  have hrB : r ∣ b := by
    rw [hrs]
    dsimp [s]
    exact Nat.gcd_dvd_left b D
  have hDc : D ∣ c := by
    rw [hcTwo]
    refine ⟨2, ?_⟩
    omega
  have hrC : r ∣ c := hrD.trans hDc

  have hfiveR : 5 * r ≤ M :=
    three_distinct_upper_half_multiples
      hrPos hrA hrB hrC
      haM hbM hcM
      haHalf hbHalf hcHalf
      hab hac hbc

  let U : Finset ℤ := (Cg ∪ Cr) ∪ Cs
  let F : Finset ℤ := ({x, y} : Finset ℤ) ∪ U
  have hFcard : F.card ≤ 4 := by
    have hpair : ({x, y} : Finset ℤ).card ≤ 2 := by
      exact Finset.card_le_two
    change U.card ≤ 2 at hU2
    change (({x, y} : Finset ℤ) ∪ U).card ≤ 4
    calc
      (({x, y} : Finset ℤ) ∪ U).card ≤
          ({x, y} : Finset ℤ).card + U.card := Finset.card_union_le _ _
      _ ≤ 2 + 2 := Nat.add_le_add hpair hU2
      _ = 4 := by norm_num

  obtain ⟨z, hzI, hrZ, hzF⟩ :=
    exists_interval_multiple_outside_finset_candidate
      (F := F)
      (L := L) (x := x) (M := M) (d := r) (k := 4)
      hrPos hxI hrX (by simpa using hfiveR) hFcard

  have hzX : z ≠ x := by
    intro h
    apply hzF
    subst z
    simp [F]
  have hzY : z ≠ y := by
    intro h
    apply hzF
    subst z
    simp [F]
  have hzCr : z ∈ Cr := by
    simp [Cr, offTwoAnchorMultiples, hzI, hzX, hzY, hrZ]
  have hzU : z ∈ U := by
    dsimp [U]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ hzCr)
  apply hzF
  simp [F, hzU]

/-- End-to-end exceptional bridge candidate. -/
theorem two_anchor_exceptional_bridge
    {L x y : ℤ} {M a b c D : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c) (hDPos : 0 < D)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hDM : D ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (haD : a ≠ D)
    (hbc : b ≠ c) (hbD : b ≠ D) (hcD : c ≠ D)
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hdir : y = x + (D : ℤ) ∨ x = y + (D : ℤ))
    (haX : (a : ℤ) ∣ x)
    (hbX : (b : ℤ) ∣ x)
    (hDX : (D : ℤ) ∣ x)
    (hDY : (D : ℤ) ∣ y)
    (hcY : (c : ℤ) ∣ y)
    (huniqueA :
      ∀ z, z ∈ integerInterval L M → (a : ℤ) ∣ z → z = x)
    (huniqueB :
      ∀ z, z ∈ integerInterval L M → (b : ℤ) ∣ z → z = x)
    (huniqueC :
      ∀ z, z ∈ integerInterval L M → (c : ℤ) ∣ z → z = y)
    (honlyH :
      ∀ z, z ∈ integerInterval L M →
        (Nat.gcd c D : ℤ) ∣ z → z = x ∨ z = y) :
    ∃ f : Fin 3 → ℤ,
      Function.Injective f ∧
      (∀ i, f i ∈ integerInterval L M ∧ f i ≠ x ∧ f i ≠ y) ∧
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (D : ℤ) ∣
        x * y * (f 0 * f 1 * f 2) := by
  classical
  let h := Nat.gcd c D
  have hhPos : 0 < h := by
    dsimp [h]
    exact Nat.gcd_pos_of_pos_left D hcPos
  have hhD : h ∣ D := by
    dsimp [h]
    exact Nat.gcd_dvd_right c D
  have hhX : (h : ℤ) ∣ x := by
    have hCast : (h : ℤ) ∣ (D : ℤ) := by exact_mod_cast hhD
    exact hCast.trans hDX
  have hhEq : h = D :=
    modulus_eq_anchor_distance_of_only_anchor_multiples
      hDPos hhPos hhD hxI hyI hdir hhX
      (by simpa [h] using honlyH)

  have hDc : D ∣ c := by
    have hhc : h ∣ c := by
      dsimp [h]
      exact Nat.gcd_dvd_left c D
    simpa [hhEq] using hhc

  have hM3 : M < 3 * D := by
    by_contra hnot
    have hthree : 3 * D ≤ M := by omega
    obtain ⟨z, hzI, hDz, hzF⟩ :=
      exists_interval_multiple_outside_finset_candidate
        (F := ({x, y} : Finset ℤ))
        (L := L) (x := x) (M := M) (d := D) (k := 2)
        hDPos hxI hDX hthree Finset.card_le_two
    have hOnlyD : z = x ∨ z = y := by
      apply honlyH z hzI
      simpa [h, hhEq] using hDz
    rcases hOnlyD with hzx | hzy
    · apply hzF
      simp [hzx]
    · apply hzF
      simp [hzy]

  have hcTwo : c = 2 * D :=
    eq_two_mul_of_dvd_ne_of_lt_three_mul
      hDPos hcPos hDc hcD hcM hM3

  have hnotDa : ¬ D ∣ a :=
    not_dvd_of_bounded_below_three_mul_and_distinct
      hDPos haPos haM hM3 hcTwo haD hac
  have hnotDb : ¬ D ∣ b :=
    not_dvd_of_bounded_below_three_mul_and_distinct
      hDPos hbPos hbM hM3 hcTwo hbD hbc

  have haHalf : M < 2 * a :=
    modulus_gt_half_of_unique_multiple
      haPos hxI haX huniqueA
  have hbHalf : M < 2 * b :=
    modulus_gt_half_of_unique_multiple
      hbPos hxI hbX huniqueB
  have hcHalf : M < 2 * c :=
    modulus_gt_half_of_unique_multiple
      hcPos hyI hcY huniqueC

  let g := Nat.gcd a b
  let r := Nat.gcd a D
  let s := Nat.gcd b D
  let Cg := offTwoAnchorMultiples L M x y g
  let Cr := offTwoAnchorMultiples L M x y r
  let Cs := offTwoAnchorMultiples L M x y s
  let C : Fin 3 → Finset ℤ := fun i =>
    if i.val = 0 then Cg else if i.val = 1 then Cr else Cs

  have hgPos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left b haPos
  have hgX : (g : ℤ) ∣ x := by
    have hga : g ∣ a := by
      dsimp [g]
      exact Nat.gcd_dvd_left a b
    have hcast : (g : ℤ) ∣ (a : ℤ) := by exact_mod_cast hga
    exact hcast.trans haX

  obtain ⟨zg, hzgI, hzgDiv, hzgX, hzgY⟩ :=
    exists_pair_gcd_repair_outside_two
      (L := L) (x := x) (y := y) (M := M)
      (a := a) (b := b)
      haPos hbPos haM hbM haHalf hbHalf hab
      hxI haX hbX
  have hzgCg : zg ∈ Cg := by
    have hzgG : (g : ℤ) ∣ zg := by simpa [g] using hzgDiv
    simp [Cg, offTwoAnchorMultiples,
      hzgI, hzgX, hzgY, hzgG]
  have hCg1 : 1 ≤ Cg.card :=
    Finset.one_le_card.mpr ⟨zg, hzgCg⟩

  have hrData :=
    gcd_proper_divisor_right haPos hDPos hnotDa
  have hsData :=
    gcd_proper_divisor_right hbPos hDPos hnotDb
  have hrPos : 0 < r := by simpa [r] using hrData.1
  have hsPos : 0 < s := by simpa [s] using hsData.1
  have hrD : r ∣ D := by simpa [r] using hrData.2.1
  have hsD : s ∣ D := by simpa [s] using hsData.2.1
  have hrNeD : r ≠ D := by simpa [r] using hrData.2.2
  have hsNeD : s ≠ D := by simpa [s] using hsData.2.2
  have htwoR : 2 * r ≤ D :=
    two_mul_le_of_dvd_ne_candidate
      hrPos hDPos hrD (Ne.symm hrNeD)
  have htwoS : 2 * s ≤ D :=
    two_mul_le_of_dvd_ne_candidate
      hsPos hDPos hsD (Ne.symm hsNeD)
  have htwoD : 2 * D ≤ M := by
    rw [← hcTwo]
    exact hcM
  have hfourR : 4 * r ≤ M := by omega
  have hfourS : 4 * s ≤ M := by omega
  have hrX : (r : ℤ) ∣ x := by
    have hra : r ∣ a := by
      dsimp [r]
      exact Nat.gcd_dvd_left a D
    have hcast : (r : ℤ) ∣ (a : ℤ) := by exact_mod_cast hra
    exact hcast.trans haX
  have hsX : (s : ℤ) ∣ x := by
    have hsb : s ∣ b := by
      dsimp [s]
      exact Nat.gcd_dvd_left b D
    have hcast : (s : ℤ) ∣ (b : ℤ) := by exact_mod_cast hsb
    exact hcast.trans hbX
  have hCr2 : 2 ≤ Cr.card := by
    simpa [Cr] using
      (off_two_anchor_card_ge_two_of_four_mul_le
        (L := L) (x := x) (y := y) (M := M) (d := r)
        hrPos hxI hrX hfourR)
  have hCs2 : 2 ≤ Cs.card := by
    simpa [Cs] using
      (off_two_anchor_card_ge_two_of_four_mul_le
        (L := L) (x := x) (y := y) (M := M) (d := s)
        hsPos hxI hsX hfourS)

  have h1 : ∀ i, 1 ≤ (C i).card := by
    intro i
    fin_cases i
    · simpa [C] using hCg1
    · simpa [C] using (show 1 ≤ Cr.card by omega)
    · simpa [C] using (show 1 ≤ Cs.card by omega)

  have h2 : ∀ i j, i ≠ j → 2 ≤ (C i ∪ C j).card := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · exact (hij rfl).elim
      · simpa [C] using
          hCr2.trans (Finset.card_le_card Finset.subset_union_right)
      · simpa [C] using
          hCs2.trans (Finset.card_le_card Finset.subset_union_right)
    · fin_cases j
      · simpa [C] using
          hCr2.trans (Finset.card_le_card Finset.subset_union_left)
      · exact (hij rfl).elim
      · simpa [C] using
          hCr2.trans (Finset.card_le_card Finset.subset_union_left)
    · fin_cases j
      · simpa [C] using
          hCs2.trans (Finset.card_le_card Finset.subset_union_left)
      · simpa [C] using
          hCs2.trans (Finset.card_le_card Finset.subset_union_left)
      · exact (hij rfl).elim

  have h3 : 3 ≤ ((C 0 ∪ C 1) ∪ C 2).card := by
    have hfull :=
      exceptional_bridge_full_union_ge_three
        (L := L) (x := x) (y := y) (M := M)
        (a := a) (b := b) (c := c) (D := D)
        haPos hbPos hcPos hDPos
        haM hbM hcM hab hac hbc
        hxI hyI hdir haX hbX hDX
        hcTwo hnotDa hnotDb haHalf hbHalf hcHalf
    simpa [C, Cg, Cr, Cs, g, r, s] using hfull

  obtain ⟨f, hfInj, hfMem⟩ :=
    exists_distinct_representatives_fin_three_of_union_bounds
      C h1 h2 h3

  have hfBasic :
      ∀ i, f i ∈ integerInterval L M ∧ f i ≠ x ∧ f i ≠ y := by
    intro i
    have hi := hfMem i
    fin_cases i
    · have hi' : f 0 ∈ offTwoAnchorMultiples L M x y g := by
        simpa [C, Cg] using hi
      rcases Finset.mem_filter.mp hi' with ⟨hiI, hrest⟩
      exact ⟨hiI, hrest.1, hrest.2.1⟩
    · have hi' : f 1 ∈ offTwoAnchorMultiples L M x y r := by
        simpa [C, Cr] using hi
      rcases Finset.mem_filter.mp hi' with ⟨hiI, hrest⟩
      exact ⟨hiI, hrest.1, hrest.2.1⟩
    · have hi' : f 2 ∈ offTwoAnchorMultiples L M x y s := by
        simpa [C, Cs] using hi
      rcases Finset.mem_filter.mp hi' with ⟨hiI, hrest⟩
      exact ⟨hiI, hrest.1, hrest.2.1⟩

  have hf0 : f 0 ∈ Cg := by simpa [C] using hfMem 0
  have hf1 : f 1 ∈ Cr := by simpa [C] using hfMem 1
  have hf2 : f 2 ∈ Cs := by simpa [C] using hfMem 2
  have hgRep : (g : ℤ) ∣ f 0 := by
    have hm : f 0 ∈ offTwoAnchorMultiples L M x y g := by
      simpa [Cg] using hf0
    exact (Finset.mem_filter.mp hm).2.2.2
  have hrRep : (r : ℤ) ∣ f 1 := by
    have hm : f 1 ∈ offTwoAnchorMultiples L M x y r := by
      simpa [Cr] using hf1
    exact (Finset.mem_filter.mp hm).2.2.2
  have hsRep : (s : ℤ) ∣ f 2 := by
    have hm : f 2 ∈ offTwoAnchorMultiples L M x y s := by
      simpa [Cs] using hf2
    exact (Finset.mem_filter.mp hm).2.2.2

  have hLx :
      (Nat.lcm (Nat.lcm a b) D : ℤ) ∣ x :=
    Int.coe_lcm_dvd (Int.coe_lcm_dvd haX hbX) hDX
  have hrProd : (r : ℤ) ∣ f 1 * f 2 := by
    rcases hrRep with ⟨u, hu⟩
    refine ⟨u * f 2, ?_⟩
    rw [hu]
    ring
  have hsProd : (s : ℤ) ∣ f 1 * f 2 := by
    rcases hsRep with ⟨v, hv⟩
    refine ⟨f 1 * v, ?_⟩
    rw [hv]
    ring
  have hLrs :
      (Nat.lcm r s : ℤ) ∣ f 1 * f 2 :=
    Int.coe_lcm_dvd hrProd hsProd
  have hRepair :
      (g : ℤ) * (Nat.lcm r s : ℤ) ∣
        f 0 * (f 1 * f 2) :=
    mul_dvd_mul hgRep hLrs
  have hAnchors :
      (Nat.lcm (Nat.lcm a b) D : ℤ) * (c : ℤ) ∣
        x * y :=
    mul_dvd_mul hLx hcY
  have hAll := mul_dvd_mul hAnchors hRepair

  have hBridgeNat :=
    Erdos708.bridge_residual_product_identity
      (a := a) (b := b) (D := D)
      (Nat.ne_of_gt haPos) (Nat.ne_of_gt hbPos) (Nat.ne_of_gt hDPos)
  have hBridgeInt :
      (Nat.lcm (Nat.lcm a b) D : ℤ) *
          ((g : ℤ) * (Nat.lcm r s : ℤ)) =
        (a : ℤ) * (b : ℤ) * (D : ℤ) := by
    dsimp [g, r, s]
    exact_mod_cast hBridgeNat
  have hLeft :
      (Nat.lcm (Nat.lcm a b) D : ℤ) * (c : ℤ) *
          ((g : ℤ) * (Nat.lcm r s : ℤ)) =
        (a : ℤ) * (b : ℤ) * (c : ℤ) * (D : ℤ) := by
    calc
      (Nat.lcm (Nat.lcm a b) D : ℤ) * (c : ℤ) *
            ((g : ℤ) * (Nat.lcm r s : ℤ))
          =
        ((Nat.lcm (Nat.lcm a b) D : ℤ) *
            ((g : ℤ) * (Nat.lcm r s : ℤ))) * (c : ℤ) := by ring
      _ = ((a : ℤ) * (b : ℤ) * (D : ℤ)) * (c : ℤ) := by
        rw [hBridgeInt]
      _ = (a : ℤ) * (b : ℤ) * (c : ℤ) * (D : ℤ) := by ring

  rw [hLeft] at hAll
  refine ⟨f, hfInj, hfBasic, ?_⟩
  simpa [mul_assoc] using hAll

end Erdos708
