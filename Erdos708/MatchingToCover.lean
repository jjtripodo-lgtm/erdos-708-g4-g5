module

public import Erdos708.MatchingExhaustion
public import Erdos708.CoverPackaging
public import Erdos708.InitialMultiple
public import Mathlib.Tactic

@[expose] public section

/-!
Bridge from abstract matching output to FourModuliCover.

This module specializes the finite matching trichotomy to the four concrete
modulus candidate families.  A four-matching gives a four-point cover
immediately.  A matching on any three of the four left vertices is routed,
case-by-case on the omitted index, through the already-banked finite one-defect
theorem.

This file is intentionally outside the trusted import graph and is NOT Banked.
-/

namespace Erdos708

def fourModulus (a b c d : ℕ) (i : Fin 4) : ℕ :=
  if i.val = 0 then a
  else if i.val = 1 then b
  else if i.val = 2 then c
  else d

def fourMultipleCandidates
    (L : ℤ) (M : ℕ) (a b c d : ℕ) (i : Fin 4) : Finset ℤ :=
  (integerInterval L M).filter
    (fun z => (fourModulus a b c d i : ℤ) ∣ z)

theorem fourModulus_two_le_candidate
    {a b c d : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) :
    ∀ i, 2 ≤ fourModulus a b c d i := by
  intro i
  fin_cases i <;> simp [fourModulus, ha, hb, hc, hd]

theorem fourModulus_le_candidate
    {M a b c d : ℕ}
    (ha : a ≤ M) (hb : b ≤ M) (hc : c ≤ M) (hd : d ≤ M) :
    ∀ i, fourModulus a b c d i ≤ M := by
  intro i
  fin_cases i <;> simp [fourModulus, ha, hb, hc, hd]

theorem fourModulus_injective_candidate
    {a b c d : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (fourModulus a b c d) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [fourModulus] at h ⊢
  all_goals aesop

theorem fourModulus_product_of_distinct_indices_candidate
    {a b c d : ℕ} {p q r s : Fin 4}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    (fourModulus a b c d p : ℤ) *
        (fourModulus a b c d q : ℤ) *
        (fourModulus a b c d r : ℤ) *
        (fourModulus a b c d s : ℤ) =
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) := by
  fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases s <;>
    simp_all [fourModulus, mul_assoc, mul_comm, mul_left_comm]

@[simp] theorem mem_fourMultipleCandidates_candidate
    {L z : ℤ} {M a b c d : ℕ} {i : Fin 4} :
    z ∈ fourMultipleCandidates L M a b c d i ↔
      z ∈ integerInterval L M ∧
      (fourModulus a b c d i : ℤ) ∣ z := by
  simp [fourMultipleCandidates]

theorem fourMultipleCandidates_nonempty_candidate
    {L : ℤ} {M a b c d : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c) (hdPos : 0 < d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M) :
    ∀ i, (fourMultipleCandidates L M a b c d i).Nonempty := by
  intro i
  fin_cases i
  · obtain ⟨z, hzI, hzD⟩ :=
      exists_interval_multiple_of_le_candidate
        (L := L) (M := M) (d := a) haPos haM
    exact ⟨z, by simpa [fourMultipleCandidates, fourModulus] using
      (show z ∈ integerInterval L M ∧ (a : ℤ) ∣ z from ⟨hzI, hzD⟩)⟩
  · obtain ⟨z, hzI, hzD⟩ :=
      exists_interval_multiple_of_le_candidate
        (L := L) (M := M) (d := b) hbPos hbM
    exact ⟨z, by simpa [fourMultipleCandidates, fourModulus] using
      (show z ∈ integerInterval L M ∧ (b : ℤ) ∣ z from ⟨hzI, hzD⟩)⟩
  · obtain ⟨z, hzI, hzD⟩ :=
      exists_interval_multiple_of_le_candidate
        (L := L) (M := M) (d := c) hcPos hcM
    exact ⟨z, by simpa [fourMultipleCandidates, fourModulus] using
      (show z ∈ integerInterval L M ∧ (c : ℤ) ∣ z from ⟨hzI, hzD⟩)⟩
  · obtain ⟨z, hzI, hzD⟩ :=
      exists_interval_multiple_of_le_candidate
        (L := L) (M := M) (d := d) hdPos hdM
    exact ⟨z, by simpa [fourMultipleCandidates, fourModulus] using
      (show z ∈ integerInterval L M ∧ (d : ℤ) ∣ z from ⟨hzI, hzD⟩)⟩

/-- A full real matching gives a four-entry cover. -/
theorem fourModuliCover_of_full_matching_candidate
    {L : ℤ} {M a b c d : ℕ}
    (g : Fin 4 → ℤ)
    (hgInj : Function.Injective g)
    (hgMem : ∀ i, g i ∈ fourMultipleCandidates L M a b c d i) :
    FourModuliCover L M a b c d := by
  have h0 := (mem_fourMultipleCandidates_candidate.mp (hgMem 0))
  have h1 := (mem_fourMultipleCandidates_candidate.mp (hgMem 1))
  have h2 := (mem_fourMultipleCandidates_candidate.mp (hgMem 2))
  have h3 := (mem_fourMultipleCandidates_candidate.mp (hgMem 3))
  have h01 : g 0 ≠ g 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (hgInj h)
  have h02 : g 0 ≠ g 2 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 2) (hgInj h)
  have h03 : g 0 ≠ g 3 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 3) (hgInj h)
  have h12 : g 1 ≠ g 2 := by
    intro h
    exact (by decide : (1 : Fin 4) ≠ 2) (hgInj h)
  have h13 : g 1 ≠ g 3 := by
    intro h
    exact (by decide : (1 : Fin 4) ≠ 3) (hgInj h)
  have h23 : g 2 ≠ g 3 := by
    intro h
    exact (by decide : (2 : Fin 4) ≠ 3) (hgInj h)
  have haD : (a : ℤ) ∣ g 0 := by
    simpa [fourModulus] using h0.2
  have hbD : (b : ℤ) ∣ g 1 := by
    simpa [fourModulus] using h1.2
  have hcD : (c : ℤ) ∣ g 2 := by
    simpa [fourModulus] using h2.2
  have hdD : (d : ℤ) ∣ g 3 := by
    simpa [fourModulus] using h3.2
  have hpay :=
    mul_dvd_mul (mul_dvd_mul (mul_dvd_mul haD hbD) hcD) hdD
  exact fourModuliCover_of_four_points_candidate
    h0.1 h1.1 h2.1 h3.1
    h01 h02 h03 h12 h13 h23
    (by simpa [mul_assoc] using hpay)

/-- Package a three-of-four matching through one-defect, irrespective of which
index is omitted. -/
theorem fourModuliCover_of_three_matching_candidate
    {L : ℤ} {M a b c d : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c) (hdPos : 0 < d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (m : Fin 4)
    (g : {i : Fin 4 // i ≠ m} → ℤ)
    (hgInj : Function.Injective g)
    (hgMem : ∀ i, g i ∈ fourMultipleCandidates L M a b c d i.1) :
    FourModuliCover L M a b c d := by
  fin_cases m
  · let i1 : {i : Fin 4 // i ≠ (0 : Fin 4)} := ⟨1, by decide⟩
    let i2 : {i : Fin 4 // i ≠ (0 : Fin 4)} := ⟨2, by decide⟩
    let i3 : {i : Fin 4 // i ≠ (0 : Fin 4)} := ⟨3, by decide⟩
    let x1 := g i1
    let x2 := g i2
    let x3 := g i3
    have h1 := mem_fourMultipleCandidates_candidate.mp (hgMem i1)
    have h2 := mem_fourMultipleCandidates_candidate.mp (hgMem i2)
    have h3 := mem_fourMultipleCandidates_candidate.mp (hgMem i3)
    have hx12 : x1 ≠ x2 := by
      intro h
      exact (by decide : i1 ≠ i2) (hgInj h)
    have hx13 : x1 ≠ x3 := by
      intro h
      exact (by decide : i1 ≠ i3) (hgInj h)
    have hx23 : x2 ≠ x3 := by
      intro h
      exact (by decide : i2 ≠ i3) (hgInj h)
    have hbX1 : (b : ℤ) ∣ x1 := by
      simpa [i1, x1, fourModulus] using h1.2
    have hcX2 : (c : ℤ) ∣ x2 := by
      simpa [i2, x2, fourModulus] using h2.2
    have hdX3 : (d : ℤ) ∣ x3 := by
      simpa [i3, x3, fourModulus] using h3.2
    obtain ⟨u, huI, hu1, hu2, hu3, hpay⟩ :=
      one_defect_four_moduli
        hbPos hcPos hdPos haPos
        hbM hcM hdM haM
        hbc hbd (Ne.symm hab)
        hcd (Ne.symm hac) (Ne.symm had)
        h1.1 h2.1 h3.1 hx12 hx13 hx23
        hbX1 hcX2 hdX3
    have hpay' :
        (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
          x1 * x2 * x3 * u := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hpay
    exact fourModuliCover_of_four_points_candidate
      h1.1 h2.1 h3.1 huI
      hx12 hx13 (Ne.symm hu1) hx23 (Ne.symm hu2) (Ne.symm hu3)
      hpay'
  · let i0 : {i : Fin 4 // i ≠ (1 : Fin 4)} := ⟨0, by decide⟩
    let i2 : {i : Fin 4 // i ≠ (1 : Fin 4)} := ⟨2, by decide⟩
    let i3 : {i : Fin 4 // i ≠ (1 : Fin 4)} := ⟨3, by decide⟩
    let x0 := g i0
    let x2 := g i2
    let x3 := g i3
    have h0 := mem_fourMultipleCandidates_candidate.mp (hgMem i0)
    have h2 := mem_fourMultipleCandidates_candidate.mp (hgMem i2)
    have h3 := mem_fourMultipleCandidates_candidate.mp (hgMem i3)
    have hx02 : x0 ≠ x2 := by
      intro h
      exact (by decide : i0 ≠ i2) (hgInj h)
    have hx03 : x0 ≠ x3 := by
      intro h
      exact (by decide : i0 ≠ i3) (hgInj h)
    have hx23 : x2 ≠ x3 := by
      intro h
      exact (by decide : i2 ≠ i3) (hgInj h)
    have haX0 : (a : ℤ) ∣ x0 := by
      simpa [i0, x0, fourModulus] using h0.2
    have hcX2 : (c : ℤ) ∣ x2 := by
      simpa [i2, x2, fourModulus] using h2.2
    have hdX3 : (d : ℤ) ∣ x3 := by
      simpa [i3, x3, fourModulus] using h3.2
    obtain ⟨u, huI, hu0, hu2, hu3, hpay⟩ :=
      one_defect_four_moduli
        haPos hcPos hdPos hbPos
        haM hcM hdM hbM
        hac had hab
        hcd (Ne.symm hbc) (Ne.symm hbd)
        h0.1 h2.1 h3.1 hx02 hx03 hx23
        haX0 hcX2 hdX3
    have hpay' :
        (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
          x0 * x2 * x3 * u := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hpay
    exact fourModuliCover_of_four_points_candidate
      h0.1 h2.1 h3.1 huI
      hx02 hx03 (Ne.symm hu0) hx23 (Ne.symm hu2) (Ne.symm hu3)
      hpay'
  · let i0 : {i : Fin 4 // i ≠ (2 : Fin 4)} := ⟨0, by decide⟩
    let i1 : {i : Fin 4 // i ≠ (2 : Fin 4)} := ⟨1, by decide⟩
    let i3 : {i : Fin 4 // i ≠ (2 : Fin 4)} := ⟨3, by decide⟩
    let x0 := g i0
    let x1 := g i1
    let x3 := g i3
    have h0 := mem_fourMultipleCandidates_candidate.mp (hgMem i0)
    have h1 := mem_fourMultipleCandidates_candidate.mp (hgMem i1)
    have h3 := mem_fourMultipleCandidates_candidate.mp (hgMem i3)
    have hx01 : x0 ≠ x1 := by
      intro h
      exact (by decide : i0 ≠ i1) (hgInj h)
    have hx03 : x0 ≠ x3 := by
      intro h
      exact (by decide : i0 ≠ i3) (hgInj h)
    have hx13 : x1 ≠ x3 := by
      intro h
      exact (by decide : i1 ≠ i3) (hgInj h)
    have haX0 : (a : ℤ) ∣ x0 := by
      simpa [i0, x0, fourModulus] using h0.2
    have hbX1 : (b : ℤ) ∣ x1 := by
      simpa [i1, x1, fourModulus] using h1.2
    have hdX3 : (d : ℤ) ∣ x3 := by
      simpa [i3, x3, fourModulus] using h3.2
    obtain ⟨u, huI, hu0, hu1, hu3, hpay⟩ :=
      one_defect_four_moduli
        haPos hbPos hdPos hcPos
        haM hbM hdM hcM
        hab had hac
        hbd hbc (Ne.symm hcd)
        h0.1 h1.1 h3.1 hx01 hx03 hx13
        haX0 hbX1 hdX3
    have hpay' :
        (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
          x0 * x1 * x3 * u := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hpay
    exact fourModuliCover_of_four_points_candidate
      h0.1 h1.1 h3.1 huI
      hx01 hx03 (Ne.symm hu0) hx13 (Ne.symm hu1) (Ne.symm hu3)
      hpay'
  · let i0 : {i : Fin 4 // i ≠ (3 : Fin 4)} := ⟨0, by decide⟩
    let i1 : {i : Fin 4 // i ≠ (3 : Fin 4)} := ⟨1, by decide⟩
    let i2 : {i : Fin 4 // i ≠ (3 : Fin 4)} := ⟨2, by decide⟩
    let x0 := g i0
    let x1 := g i1
    let x2 := g i2
    have h0 := mem_fourMultipleCandidates_candidate.mp (hgMem i0)
    have h1 := mem_fourMultipleCandidates_candidate.mp (hgMem i1)
    have h2 := mem_fourMultipleCandidates_candidate.mp (hgMem i2)
    have hx01 : x0 ≠ x1 := by
      intro h
      exact (by decide : i0 ≠ i1) (hgInj h)
    have hx02 : x0 ≠ x2 := by
      intro h
      exact (by decide : i0 ≠ i2) (hgInj h)
    have hx12 : x1 ≠ x2 := by
      intro h
      exact (by decide : i1 ≠ i2) (hgInj h)
    have haX0 : (a : ℤ) ∣ x0 := by
      simpa [i0, x0, fourModulus] using h0.2
    have hbX1 : (b : ℤ) ∣ x1 := by
      simpa [i1, x1, fourModulus] using h1.2
    have hcX2 : (c : ℤ) ∣ x2 := by
      simpa [i2, x2, fourModulus] using h2.2
    obtain ⟨u, huI, hu0, hu1, hu2, hpay⟩ :=
      one_defect_four_moduli
        haPos hbPos hcPos hdPos
        haM hbM hcM hdM
        hab hac had
        hbc hbd hcd
        h0.1 h1.1 h2.1 hx01 hx02 hx12
        haX0 hbX1 hcX2
    exact fourModuliCover_of_four_points_candidate
      h0.1 h1.1 h2.1 huI
      hx01 hx02 (Ne.symm hu0) hx12 (Ne.symm hu1) (Ne.symm hu2)
      hpay

theorem fourModuliCover_of_matching_output_candidate
    {L : ℤ} {M a b c d : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c) (hdPos : 0 < d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h :
      (∃ g : Fin 4 → ℤ,
          Function.Injective g ∧
          ∀ i, g i ∈ fourMultipleCandidates L M a b c d i) ∨
      (∃ m : Fin 4,
        ∃ g : {i : Fin 4 // i ≠ m} → ℤ,
          Function.Injective g ∧
          ∀ i, g i ∈ fourMultipleCandidates L M a b c d i.1)) :
    FourModuliCover L M a b c d := by
  rcases h with h4 | h3
  · rcases h4 with ⟨g, hgInj, hgMem⟩
    exact fourModuliCover_of_full_matching_candidate g hgInj hgMem
  · rcases h3 with ⟨m, g, hgInj, hgMem⟩
    exact fourModuliCover_of_three_matching_candidate
      haPos hbPos hcPos hdPos
      haM hbM hcM hdM
      hab hac had hbc hbd hcd
      m g hgInj hgMem

end Erdos708
