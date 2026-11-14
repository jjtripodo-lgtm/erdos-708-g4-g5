module

public import Erdos708.Five.Shapes

@[expose] public section

/-!
# The five-modulus upper bound, conditional on the (4,1) and single-anchor cases

Take a valid assignment maximizing the number of occupied sites and classify its fibre sizes:
`≥4` occupied sites (missing-one repair), three sites (3,1,1)/(2,2,1), two sites (4,1)/(3,2),
one site (5). The (4,1) and (5) cases enter as the hypotheses `Case41Statement` and
`Case5Statement`.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

section

variable {L : ℤ} {M : ℕ} {m : Fin 5 → ℕ} {f : Fin 5 → ℤ}

theorem fiber_mem {x : ℤ} {i : Fin 5} :
    i ∈ Finset.univ.filter (fun j => f j = x) ↔ f i = x := by simp

/-- Fibre-size bookkeeping for two occupied values. -/
theorem fibers_two {x y : ℤ} (hxy : x ≠ y) (hS : Finset.univ.image f = {x, y}) :
    (Finset.univ.filter (fun j => f j = x)).card +
      (Finset.univ.filter (fun j => f j = y)).card = 5 := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := {x, y})
    (fun i _ => by rw [← hS]; exact Finset.mem_image_of_mem f (Finset.mem_univ i))
  rw [Finset.sum_pair hxy] at h
  simpa using h.symm

/-- Fibre-size bookkeeping for three occupied values. -/
theorem fibers_three {x y z : ℤ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hS : Finset.univ.image f = {x, y, z}) :
    (Finset.univ.filter (fun j => f j = x)).card +
      (Finset.univ.filter (fun j => f j = y)).card +
        (Finset.univ.filter (fun j => f j = z)).card = 5 := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := {x, y, z})
    (fun i _ => by rw [← hS]; exact Finset.mem_image_of_mem f (Finset.mem_univ i))
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_pair hyz] at h
  simp at h
  omega

theorem fiber_pos {x : ℤ} (hx : x ∈ Finset.univ.image f) :
    1 ≤ (Finset.univ.filter (fun j => f j = x)).card := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

theorem ne_of_fibers {x y : ℤ} (hxy : x ≠ y) {i j : Fin 5} (hi : f i = x) (hj : f j = y) :
    i ≠ j := by
  rintro rfl; exact hxy (hi.symm.trans hj)

end

/-- Three occupied sites. -/
theorem upper_three {L : ℤ} {M : ℕ} {m : Fin 5 → ℕ} {f : Fin 5 → ℤ}
    (hinj : Function.Injective m) (hpos : ∀ i, 0 < m i) (hle : ∀ i, m i ≤ M)
    (hf : ValidAssign L M m f) {x y z : ℤ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hS : Finset.univ.image f = {x, y, z}) :
    ProdCover L M (∏ i, m i) 6 := by
  classical
  have hsum := fibers_three hxy hxz hyz hS
  have px := fiber_pos (f := f) (x := x) (by rw [hS]; simp)
  have py := fiber_pos (f := f) (x := y) (by rw [hS]; simp)
  have pz := fiber_pos (f := f) (x := z) (by rw [hS]; simp)
  set Fx := Finset.univ.filter (fun j => f j = x)
  set Fy := Finset.univ.filter (fun j => f j = y)
  set Fz := Finset.univ.filter (fun j => f j = z)
  -- generic (3,1,1) and (2,2,1) dispatch, with sites permuted
  have d311 : ∀ {p q r : ℤ}, p ≠ q → p ≠ r → q ≠ r →
      (Finset.univ.filter (fun j => f j = p)).card = 3 →
      (Finset.univ.filter (fun j => f j = q)).card = 1 →
      (Finset.univ.filter (fun j => f j = r)).card = 1 → ProdCover L M (∏ i, m i) 6 := by
    intro p q r hpq hpr hqr c3 c1 c1'
    obtain ⟨i₁, i₂, i₃, h12, h13, h23, hF⟩ := Finset.card_eq_three.mp c3
    obtain ⟨j, hFj⟩ := Finset.card_eq_one.mp c1
    obtain ⟨l, hFl⟩ := Finset.card_eq_one.mp c1'
    have f1 : f i₁ = p := fiber_mem.mp (by rw [hF]; simp)
    have f2 : f i₂ = p := fiber_mem.mp (by rw [hF]; simp)
    have f3 : f i₃ = p := fiber_mem.mp (by rw [hF]; simp)
    have fj : f j = q := fiber_mem.mp (by rw [hFj]; simp)
    have fl : f l = r := fiber_mem.mp (by rw [hFl]; simp)
    exact shape311 hinj hpos hle hf h12 h13 (ne_of_fibers hpq f1 fj) (ne_of_fibers hpr f1 fl)
      h23 (ne_of_fibers hpq f2 fj) (ne_of_fibers hpr f2 fl) (ne_of_fibers hpq f3 fj)
      (ne_of_fibers hpr f3 fl) (ne_of_fibers hqr fj fl) f1 f2 f3 fj fl hpq hpr hqr
  have d221 : ∀ {p q r : ℤ}, p ≠ q → p ≠ r → q ≠ r →
      (Finset.univ.filter (fun j => f j = p)).card = 2 →
      (Finset.univ.filter (fun j => f j = q)).card = 2 →
      (Finset.univ.filter (fun j => f j = r)).card = 1 → ProdCover L M (∏ i, m i) 6 := by
    intro p q r hpq hpr hqr c2 c2' c1
    obtain ⟨i₁, i₂, h12, hF⟩ := Finset.card_eq_two.mp c2
    obtain ⟨j₁, j₂, h34, hF'⟩ := Finset.card_eq_two.mp c2'
    obtain ⟨l, hFl⟩ := Finset.card_eq_one.mp c1
    have f1 : f i₁ = p := fiber_mem.mp (by rw [hF]; simp)
    have f2 : f i₂ = p := fiber_mem.mp (by rw [hF]; simp)
    have f3 : f j₁ = q := fiber_mem.mp (by rw [hF']; simp)
    have f4 : f j₂ = q := fiber_mem.mp (by rw [hF']; simp)
    have fl : f l = r := fiber_mem.mp (by rw [hFl]; simp)
    exact shape221 hinj hpos hle hf h12 (ne_of_fibers hpq f1 f3) (ne_of_fibers hpq f1 f4)
      (ne_of_fibers hpr f1 fl) (ne_of_fibers hpq f2 f3) (ne_of_fibers hpq f2 f4)
      (ne_of_fibers hpr f2 fl) h34 (ne_of_fibers hqr f3 fl) (ne_of_fibers hqr f4 fl)
      f1 f2 f3 f4 fl hpq hpr hqr
  have cases : (Fx.card = 3 ∧ Fy.card = 1 ∧ Fz.card = 1) ∨
      (Fx.card = 1 ∧ Fy.card = 3 ∧ Fz.card = 1) ∨ (Fx.card = 1 ∧ Fy.card = 1 ∧ Fz.card = 3) ∨
      (Fx.card = 2 ∧ Fy.card = 2 ∧ Fz.card = 1) ∨ (Fx.card = 2 ∧ Fy.card = 1 ∧ Fz.card = 2) ∨
      (Fx.card = 1 ∧ Fy.card = 2 ∧ Fz.card = 2) := by omega
  rcases cases with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact d311 hxy hxz hyz a b c
  · exact d311 (Ne.symm hxy) hyz hxz b a c
  · exact d311 (Ne.symm hxz) (Ne.symm hyz) hxy c a b
  · exact d221 hxy hxz hyz a b c
  · exact d221 hxz hxy (Ne.symm hyz) a c b
  · exact d221 hyz (Ne.symm hxy) (Ne.symm hxz) b c a

/-- Two occupied sites. -/
theorem upper_two (h41 : Case41Statement) {L : ℤ} {M : ℕ} {m : Fin 5 → ℕ} {f : Fin 5 → ℤ}
    (hinj : Function.Injective m) (hpos : ∀ i, 0 < m i) (hle : ∀ i, m i ≤ M)
    (hf : ValidAssign L M m f)
    (hmax : ∀ f', ValidAssign L M m f' →
      (Finset.univ.image f').card ≤ (Finset.univ.image f).card)
    {x y : ℤ} (hxy : x ≠ y) (hS : Finset.univ.image f = {x, y}) :
    ProdCover L M (∏ i, m i) 6 := by
  classical
  have hK : (Finset.univ.image f).card = 2 := by rw [hS, Finset.card_pair hxy]
  have hsum := fibers_two hxy hS
  have px := fiber_pos (f := f) (x := x) (by rw [hS]; simp)
  have py := fiber_pos (f := f) (x := y) (by rw [hS]; simp)
  have d41 : ∀ {p q : ℤ}, p ≠ q →
      (Finset.univ.filter (fun j => f j = p)).card = 4 →
      (Finset.univ.filter (fun j => f j = q)).card = 1 → ProdCover L M (∏ i, m i) 6 := by
    intro p q hpq c4 c1
    obtain ⟨i₁, i₂, i₃, i₄, h12, h13, h14, h23, h24, h34, hF⟩ := Finset.card_eq_four.mp c4
    obtain ⟨l, hFl⟩ := Finset.card_eq_one.mp c1
    have f1 : f i₁ = p := fiber_mem.mp (by rw [hF]; simp)
    have f2 : f i₂ = p := fiber_mem.mp (by rw [hF]; simp)
    have f3 : f i₃ = p := fiber_mem.mp (by rw [hF]; simp)
    have f4 : f i₄ = p := fiber_mem.mp (by rw [hF]; simp)
    have fl : f l = q := fiber_mem.mp (by rw [hFl]; simp)
    exact shape41 h41 hinj hpos hle hf hmax hK h12 h13 h14 (ne_of_fibers hpq f1 fl) h23 h24
      (ne_of_fibers hpq f2 fl) h34 (ne_of_fibers hpq f3 fl) (ne_of_fibers hpq f4 fl)
      f1 f2 f3 f4 fl hpq
  have d32 : ∀ {p q : ℤ}, p ≠ q →
      (Finset.univ.filter (fun j => f j = p)).card = 3 →
      (Finset.univ.filter (fun j => f j = q)).card = 2 → ProdCover L M (∏ i, m i) 6 := by
    intro p q hpq c3 c2
    obtain ⟨i₁, i₂, i₃, h12, h13, h23, hF⟩ := Finset.card_eq_three.mp c3
    obtain ⟨j₁, j₂, h45, hF'⟩ := Finset.card_eq_two.mp c2
    have f1 : f i₁ = p := fiber_mem.mp (by rw [hF]; simp)
    have f2 : f i₂ = p := fiber_mem.mp (by rw [hF]; simp)
    have f3 : f i₃ = p := fiber_mem.mp (by rw [hF]; simp)
    have f4 : f j₁ = q := fiber_mem.mp (by rw [hF']; simp)
    have f5 : f j₂ = q := fiber_mem.mp (by rw [hF']; simp)
    exact shape32 hinj hpos hle hf h12 h13 (ne_of_fibers hpq f1 f4) (ne_of_fibers hpq f1 f5)
      h23 (ne_of_fibers hpq f2 f4) (ne_of_fibers hpq f2 f5) (ne_of_fibers hpq f3 f4)
      (ne_of_fibers hpq f3 f5) h45 f1 f2 f3 f4 f5 hpq
  have cases : ((Finset.univ.filter (fun j => f j = x)).card = 4 ∧
        (Finset.univ.filter (fun j => f j = y)).card = 1) ∨
      ((Finset.univ.filter (fun j => f j = x)).card = 1 ∧
        (Finset.univ.filter (fun j => f j = y)).card = 4) ∨
      ((Finset.univ.filter (fun j => f j = x)).card = 3 ∧
        (Finset.univ.filter (fun j => f j = y)).card = 2) ∨
      ((Finset.univ.filter (fun j => f j = x)).card = 2 ∧
        (Finset.univ.filter (fun j => f j = y)).card = 3) := by omega
  rcases cases with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact d41 hxy a b
  · exact d41 (Ne.symm hxy) b a
  · exact d32 hxy a b
  · exact d32 (Ne.symm hxy) b a

/-- **Conditional five-modulus upper bound.** Assuming the (4,1) and single-anchor case
statements, every five distinct positive originals at most `M` have a six-entry cover in every
interval of `M` consecutive integers. -/
theorem upper_of_cases (h41 : Case41Statement) (h5 : Case5Statement) {L : ℤ} {M : ℕ}
    (m : Fin 5 → ℕ) (hinj : Function.Injective m) (hpos : ∀ i, 0 < m i)
    (hle : ∀ i, m i ≤ M) :
    ProdCover L M (∏ i, m i) 6 := by
  classical
  obtain ⟨f, hf, hmax⟩ := exists_max_validAssign (L := L) m hinj hpos hle
  set S := Finset.univ.image f with hSdef
  have hS0 : 0 < S.card := Finset.card_pos.mpr ⟨f 0, Finset.mem_image_of_mem f (by simp)⟩
  by_cases h4 : 4 ≤ S.card
  · exact shape_missing hinj hpos hle hf h4
  · have hcases : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
    rcases hcases with h1 | h2 | h3
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
      refine shape5 h5 hinj hpos hle hf hmax (x := x) (fun i => ?_)
      have : f i ∈ S := Finset.mem_image_of_mem f (Finset.mem_univ i)
      rw [hx] at this; simpa using this
    · obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.mp h2
      exact upper_two h41 hinj hpos hle hf hmax hxy hxy'
    · obtain ⟨x, y, z, hxy, hxz, hyz, hxyz⟩ := Finset.card_eq_three.mp h3
      exact upper_three hinj hpos hle hf hxy hxz hyz hxyz

end Erdos708.Five
