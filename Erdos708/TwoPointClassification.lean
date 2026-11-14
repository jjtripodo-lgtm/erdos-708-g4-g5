module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

/-!
Classification of four nonempty families living on two points.

Assume:
* every family is a nonempty subset of {x,y};
* x != y;
* every triple union has at least two points;
* at most one family equals the full pair {x,y}.

Then, possibly swapping x and y, the four families can be ordered as

  {x}, {x}, {y}, ({y} or {x,y}).

This is the exact set-theoretic normal form consumed by the combined
two-anchor theorem.

This module is part of the trusted theorem graph.
-/

namespace Erdos708

theorem nonempty_subset_pair_classification_candidate
    {α : Type*} [DecidableEq α]
    {A : Finset α} {x y : α}
    (hxy : x ≠ y)
    (hA : A.Nonempty)
    (hsub : A ⊆ {x, y}) :
    A = {x} ∨ A = {y} ∨ A = {x, y} := by
  classical
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ A
    · right
      right
      apply Finset.Subset.antisymm hsub
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    · left
      ext z
      constructor
      · intro hz
        have hzpair := hsub hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzpair
        rcases hzpair with hzx | hzy
        · simpa [hzx]
        · exact (hy (hzy ▸ hz)).elim
      · intro hz
        have hzx : z = x := by simpa using hz
        simpa [hzx] using hx
  · right
    left
    rcases hA with ⟨z, hz⟩
    have hzpair := hsub hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzpair
    have hzy : z = y := by
      rcases hzpair with hzx | hzy
      · subst z
        exact (hx hz).elim
      · exact hzy
    have hy : y ∈ A := by simpa [hzy] using hz
    ext w
    constructor
    · intro hw
      have hwpair := hsub hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwpair
      rcases hwpair with hwx | hwy
      · subst w
        exact (hx hw).elim
      · simpa [hwy]
    · intro hw
      have hwy : w = y := by simpa using hw
      simpa [hwy] using hy

def NormalizedTwoPointRoute
    {α : Type*} [DecidableEq α]
    (C : Fin 4 → Finset α) (x y : α) : Prop :=
  ∃ x' y' : α, ∃ p q r s : Fin 4,
    ({x', y'} : Finset α) = {x, y} ∧
    x' ≠ y' ∧
    p ≠ q ∧ p ≠ r ∧ p ≠ s ∧
    q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
    C p = {x'} ∧
    C q = {x'} ∧
    C r = {y'} ∧
    (C s = {y'} ∨ C s = {x', y'})

theorem normalized_two_point_route_candidate
    {α : Type*} [DecidableEq α]
    (C : Fin 4 → Finset α)
    {x y : α}
    (hxy : x ≠ y)
    (hnonempty : ∀ i, (C i).Nonempty)
    (hsub : ∀ i, C i ⊆ {x, y})
    (htriple :
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        2 ≤ ((C i ∪ C j) ∪ C k).card)
    (hbridgeUnique :
      ∀ i j, C i = {x, y} → C j = {x, y} → i = j) :
    NormalizedTwoPointRoute C x y := by
  classical
  let Br : Finset (Fin 4) :=
    Finset.univ.filter (fun i => C i = {x, y})
  let N : Finset (Fin 4) :=
    Finset.univ.filter (fun i => C i ≠ {x, y})
  let X : Finset (Fin 4) :=
    N.filter (fun i => C i = {x})
  let Y : Finset (Fin 4) :=
    N.filter (fun i => C i ≠ {x})

  have hclass (i : Fin 4) :
      C i = {x} ∨ C i = {y} ∨ C i = {x, y} :=
    nonempty_subset_pair_classification_candidate
      hxy (hnonempty i) (hsub i)

  have hXeq {i : Fin 4} (hi : i ∈ X) : C i = {x} := by
    exact (Finset.mem_filter.mp hi).2

  have hYeq {i : Fin 4} (hi : i ∈ Y) : C i = {y} := by
    have hiN := (Finset.mem_filter.mp hi).1
    have hixne := (Finset.mem_filter.mp hi).2
    have hibridge : C i ≠ {x, y} := (Finset.mem_filter.mp hiN).2
    rcases hclass i with hx | hy | hb
    · exact (hixne hx).elim
    · exact hy
    · exact (hibridge hb).elim

  have hBreq {i : Fin 4} (hi : i ∈ Br) : C i = {x, y} := by
    exact (Finset.mem_filter.mp hi).2

  have hBrLe : Br.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro i hi j hj
    exact hbridgeUnique i j (hBreq hi) (hBreq hj)

  have hXle : X.card ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ X.card := by omega
    obtain ⟨T, hTX, hTcard⟩ :=
      Finset.exists_subset_card_eq (s := X) hthree
    rcases Finset.card_eq_three.mp hTcard with
      ⟨i, j, k, hij, hik, hjk, hTeq⟩
    have hiX : i ∈ X := hTX (by rw [hTeq]; simp)
    have hjX : j ∈ X := hTX (by rw [hTeq]; simp)
    have hkX : k ∈ X := hTX (by rw [hTeq]; simp)
    have ht := htriple i j k hij hik hjk
    rw [hXeq hiX, hXeq hjX, hXeq hkX] at ht
    simp at ht

  have hYle : Y.card ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ Y.card := by omega
    obtain ⟨T, hTY, hTcard⟩ :=
      Finset.exists_subset_card_eq (s := Y) hthree
    rcases Finset.card_eq_three.mp hTcard with
      ⟨i, j, k, hij, hik, hjk, hTeq⟩
    have hiY : i ∈ Y := hTY (by rw [hTeq]; simp)
    have hjY : j ∈ Y := hTY (by rw [hTeq]; simp)
    have hkY : k ∈ Y := hTY (by rw [hTeq]; simp)
    have ht := htriple i j k hij hik hjk
    rw [hYeq hiY, hYeq hjY, hYeq hkY] at ht
    simp at ht

  have hBN : Br.card + N.card = 4 := by
    have hpart :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin 4)))
        (p := fun i => C i = {x, y})
    simpa [Br, N] using hpart

  have hXY : X.card + Y.card = N.card := by
    have hpart :=
      Finset.card_filter_add_card_filter_not
        (s := N)
        (p := fun i => C i = {x})
    simpa [X, Y] using hpart

  have hXYne :
      ∀ {i j : Fin 4}, i ∈ X → j ∈ Y → i ≠ j := by
    intro i j hi hj hij
    subst j
    have hs : ({x} : Finset α) = {y} :=
      (hXeq hi).symm.trans (hYeq hj)
    have hxmem : x ∈ ({y} : Finset α) := by
      rw [← hs]
      simp
    have hxy' : x = y := by simpa using hxmem
    exact hxy hxy'

  have hXBne :
      ∀ {i j : Fin 4}, i ∈ X → j ∈ Br → i ≠ j := by
    intro i j hi hj hij
    subst j
    have hs : ({x} : Finset α) = {x, y} :=
      (hXeq hi).symm.trans (hBreq hj)
    have hymem : y ∈ ({x} : Finset α) := by
      rw [hs]
      simp
    have hyx : y = x := by simpa using hymem
    exact hxy hyx.symm

  have hYBne :
      ∀ {i j : Fin 4}, i ∈ Y → j ∈ Br → i ≠ j := by
    intro i j hi hj hij
    subst j
    have hs : ({y} : Finset α) = {x, y} :=
      (hYeq hi).symm.trans (hBreq hj)
    have hxmem : x ∈ ({y} : Finset α) := by
      rw [hs]
      simp
    have hxy' : x = y := by simpa using hxmem
    exact hxy hxy'

  by_cases hBr0 : Br.card = 0
  · have hN4 : N.card = 4 := by omega
    have hX2 : X.card = 2 := by omega
    have hY2 : Y.card = 2 := by omega
    rcases Finset.card_eq_two.mp hX2 with ⟨p, q, hpq, hXset⟩
    rcases Finset.card_eq_two.mp hY2 with ⟨r, s, hrs, hYset⟩
    have hpX : p ∈ X := by rw [hXset]; simp
    have hqX : q ∈ X := by rw [hXset]; simp
    have hrY : r ∈ Y := by rw [hYset]; simp
    have hsY : s ∈ Y := by rw [hYset]; simp
    refine ⟨x, y, p, q, r, s, rfl, hxy,
      hpq, hXYne hpX hrY, hXYne hpX hsY,
      hXYne hqX hrY, hXYne hqX hsY, hrs,
      hXeq hpX, hXeq hqX, hYeq hrY, Or.inl (hYeq hsY)⟩
  · have hBr1 : Br.card = 1 := by omega
    have hN3 : N.card = 3 := by omega
    have hsum3 : X.card + Y.card = 3 := by omega
    by_cases hX2 : X.card = 2
    · have hY1 : Y.card = 1 := by omega
      rcases Finset.card_eq_two.mp hX2 with ⟨p, q, hpq, hXset⟩
      rcases Finset.card_eq_one.mp hY1 with ⟨r, hYset⟩
      rcases Finset.card_eq_one.mp hBr1 with ⟨s, hBset⟩
      have hpX : p ∈ X := by rw [hXset]; simp
      have hqX : q ∈ X := by rw [hXset]; simp
      have hrY : r ∈ Y := by rw [hYset]; simp
      have hsB : s ∈ Br := by rw [hBset]; simp
      refine ⟨x, y, p, q, r, s, rfl, hxy,
        hpq, hXYne hpX hrY, hXBne hpX hsB,
        hXYne hqX hrY, hXBne hqX hsB, hYBne hrY hsB,
        hXeq hpX, hXeq hqX, hYeq hrY, Or.inr (hBreq hsB)⟩
    · have hX1 : X.card = 1 := by omega
      have hY2 : Y.card = 2 := by omega
      rcases Finset.card_eq_two.mp hY2 with ⟨p, q, hpq, hYset⟩
      rcases Finset.card_eq_one.mp hX1 with ⟨r, hXset⟩
      rcases Finset.card_eq_one.mp hBr1 with ⟨s, hBset⟩
      have hpY : p ∈ Y := by rw [hYset]; simp
      have hqY : q ∈ Y := by rw [hYset]; simp
      have hrX : r ∈ X := by rw [hXset]; simp
      have hsB : s ∈ Br := by rw [hBset]; simp
      have hpairSwap : ({y, x} : Finset α) = {x, y} := by
        ext z
        simp [or_comm]
      refine ⟨y, x, p, q, r, s,
        hpairSwap, ?_,
        hpq, ?_, ?_, ?_, ?_, ?_,
        hYeq hpY, hYeq hqY, hXeq hrX, ?_⟩
      · exact hxy.symm
      · exact (hXYne hrX hpY).symm
      · exact hYBne hpY hsB
      · exact (hXYne hrX hqY).symm
      · exact hYBne hqY hsB
      · exact hXBne hrX hsB
      · right
        have hb := hBreq hsB
        ext z
        simpa [or_comm] using Finset.ext_iff.mp hb z

end Erdos708
