module

public import Erdos708.Five.Case311

@[expose] public section

/-!
# Partition (3,2)

A pairwise incomparable triple `a, b, c` shares anchor `x`; an incomparable pair `d, e`
shares anchor `y ≠ x`. Then six interval entries cover `abcde`. This is Section 4 of
`G5_COMPLETE_CANDIDATE.md`.

The pair residual `h = gcd d e` is paid at a third site `z`. The site is chosen so that every
triple pair-label still has a multiple outside `{x, y, z}`. Then the (3,1,1) free-label
assembly applies with payments `lcm d e` at `y` and `h` at `z`.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

section

variable {L x y : ℤ} {M : ℕ}

/-- Two labels whose interval multiples are each confined to three sites, and which both divide
two distinct anchors, are equal. -/
theorem eq_of_two_confined_labels {R S : ℕ} (hR0 : 0 < R) (hS0 : 0 < S)
    (h3R : 3 * R ≤ M) (h4R : M < 4 * R) (h3S : 3 * S ≤ M) (h4S : M < 4 * S)
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M) (hxy : x ≠ y)
    (hRx : (R : ℤ) ∣ x) (hRy : (R : ℤ) ∣ y) (hSx : (S : ℤ) ∣ x) (hSy : (S : ℤ) ∣ y) :
    R = S := by
  have hLx : ((Nat.lcm R S : ℕ) : ℤ) ∣ x := int_lcm_dvd hRx hSx
  have hLy : ((Nat.lcm R S : ℕ) : ℤ) ∣ y := int_lcm_dvd hRy hSy
  have hLd : ((Nat.lcm R S : ℕ) : ℤ) ∣ x - y := dvd_sub hLx hLy
  have hL0 : 0 < Nat.lcm R S := Nat.lcm_pos hR0 hS0
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hle : ((Nat.lcm R S : ℕ) : ℤ) ≤ |x - y| := Int.le_of_dvd (abs_pos.mpr hxy')
    ((dvd_abs _ _).mpr hLd)
  rw [mem_integerInterval] at hx hy
  have habs : |x - y| ≤ (M : ℤ) - 1 := by rw [abs_le]; constructor <;> omega
  have hLM : Nat.lcm R S < M := by omega
  obtain ⟨i, hi⟩ := Nat.dvd_lcm_left R S
  obtain ⟨j, hj⟩ := Nat.dvd_lcm_right R S
  have hi4 : i < 4 := by by_contra h; push Not at h; nlinarith
  have hj4 : j < 4 := by by_contra h; push Not at h; nlinarith
  have hi0 : i ≠ 0 := by rintro rfl; omega
  have hj0 : j ≠ 0 := by rintro rfl; omega
  interval_cases i <;> interval_cases j <;> omega

end

section

variable {L x y : ℤ} {M a b c d e : ℕ}

/-- A label confined to `{x, y, z₀}` cannot equal the second pair's gcd, so the pair residual has
a further free site. -/
theorem case32_switch {z₀ : ℤ} {P Q : ℕ}
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz₀ : z₀ ∈ integerInterval L M) (hxy : x ≠ y) (hx0 : x ≠ z₀) (hy0 : y ≠ z₀)
    (hP : (P : ℤ) ∣ x) (hQ : (Q : ℤ) ∣ x) (hd : (d : ℤ) ∣ y) (he : (e : ℤ) ∣ y)
    (hP0 : 0 < P) (hQ0 : 0 < Q) (hd0 : 0 < d) (he0 : 0 < e)
    (hPM : P ≤ M) (hQM : Q ≤ M) (hdM : d ≤ M) (heM : e ≤ M)
    (hdP : d ≠ P) (hdQ : d ≠ Q)
    (hPQ : ¬ P ∣ Q) (hQP : ¬ Q ∣ P) (hde' : ¬ d ∣ e) (hed' : ¬ e ∣ d)
    (hconf : ∀ w ∈ integerInterval L M, ((Nat.gcd P Q : ℕ) : ℤ) ∣ w →
      w = x ∨ w = y ∨ w = z₀) :
    ∃ z₁ ∈ integerInterval L M, ((Nat.gcd d e : ℕ) : ℤ) ∣ z₁ ∧ z₁ ≠ x ∧ z₁ ≠ y ∧ z₁ ≠ z₀ := by
  classical
  by_contra hno
  have hconfh : ∀ w ∈ integerInterval L M, ((Nat.gcd d e : ℕ) : ℤ) ∣ w →
      w = x ∨ w = y ∨ w = z₀ := by
    intro w hw hhw
    by_contra hne
    push Not at hne
    exact hno ⟨w, hw, hhw, hne.1, hne.2.1, hne.2.2⟩
  set R := Nat.gcd P Q
  set h := Nat.gcd d e
  have hR0 : 0 < R := Nat.gcd_pos_of_pos_left Q hP0
  have hh0 : 0 < h := Nat.gcd_pos_of_pos_left e hd0
  have hRx : (R : ℤ) ∣ x := int_dvd_trans_nat (Nat.gcd_dvd_left P Q) hP
  have hhy : (h : ℤ) ∣ y := int_dvd_trans_nat (Nat.gcd_dvd_left d e) hd
  have h3R : 3 * R ≤ M := three_mul_le_of_incomparable hR0 (Nat.gcd_dvd_left P Q)
    (Nat.gcd_dvd_right P Q) hP0 hQ0 hPM hQM hPQ hQP
  have h3h : 3 * h ≤ M := three_mul_le_of_incomparable hh0 (Nat.gcd_dvd_left d e)
    (Nat.gcd_dvd_right d e) hd0 he0 hdM heM hde' hed'
  have h4R := lt_four_mul_of_confined {x, y, z₀} hR0 hx hRx Finset.card_le_three
    (fun w hw hRw => by rcases hconf w hw hRw with rfl | rfl | rfl <;> simp)
  have h4h := lt_four_mul_of_confined {x, y, z₀} hh0 hy hhy Finset.card_le_three
    (fun w hw hhw => by rcases hconfh w hw hhw with rfl | rfl | rfl <;> simp)
  obtain ⟨-, hRy, -⟩ := dvd_all_of_confined_three hR0 hx hRx hxy hx0 hy0 h3R hconf
  obtain ⟨hhx, -, -⟩ := dvd_all_of_confined_three hh0 hy hhy hxy hx0 hy0 h3h hconfh
  have hRh : R = h := eq_of_two_confined_labels hR0 hh0 h3R h4R h3h h4h hx hy hxy hRx hRy hhx hhy
  have hPQ23 := eq_two_three_of_incomparable (Nat.gcd_dvd_left P Q) (Nat.gcd_dvd_right P Q)
    hP0 hQ0 hPM hQM h4R hPQ hQP
  have hde23 := eq_two_three_of_incomparable (Nat.gcd_dvd_left d e) (Nat.gcd_dvd_right d e)
    hd0 he0 hdM heM h4h hde' hed'
  have : R = Nat.gcd P Q := rfl
  rw [← this, hRh] at hPQ23
  rcases hPQ23 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hde23 with ⟨h3, -⟩ | ⟨h3, -⟩ <;> omega

/-- After switching, every label has a free site outside `{x, y, z₁}`. -/
theorem case32_good_after_switch {z₀ z₁ : ℤ} {R S : ℕ}
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hxy : x ≠ y) (hx0 : x ≠ z₀) (hy0 : y ≠ z₀) (hx1 : x ≠ z₁) (hy1 : y ≠ z₁) (h01 : z₀ ≠ z₁)
    (hR0 : 0 < R) (hS0 : 0 < S) (h3R : 3 * R ≤ M) (h3S : 3 * S ≤ M)
    (hRx : (R : ℤ) ∣ x) (hSx : (S : ℤ) ∣ x)
    (hconfR : ∀ w ∈ integerInterval L M, (R : ℤ) ∣ w → w = x ∨ w = y ∨ w = z₀) :
    ∃ s ∈ integerInterval L M, (S : ℤ) ∣ s ∧ s ≠ x ∧ s ≠ y ∧ s ≠ z₁ := by
  classical
  by_contra hno
  have hconfS : ∀ w ∈ integerInterval L M, (S : ℤ) ∣ w → w = x ∨ w = y ∨ w = z₁ := by
    intro w hw hSw
    by_contra hne
    push Not at hne
    exact hno ⟨w, hw, hSw, hne.1, hne.2.1, hne.2.2⟩
  by_cases hRS : R = S
  · subst hRS
    obtain ⟨w, hw, hRw, hwF⟩ := exists_multiple_outside {x, y} hR0 hx hRx (k := 2)
      (by omega) (Finset.card_le_two)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwF
    rcases hconfR w hw hRw with h | h | h
    · exact hwF.1 h
    · exact hwF.2 h
    · rcases hconfS w hw hRw with h' | h' | h'
      · exact hwF.1 h'
      · exact hwF.2 h'
      · exact h01 (h.symm.trans h')
  · have h4R := lt_four_mul_of_confined {x, y, z₀} hR0 hx hRx Finset.card_le_three
      (fun w hw hRw => by rcases hconfR w hw hRw with rfl | rfl | rfl <;> simp)
    have h4S := lt_four_mul_of_confined {x, y, z₁} hS0 hx hSx Finset.card_le_three
      (fun w hw hSw => by rcases hconfS w hw hSw with rfl | rfl | rfl <;> simp)
    obtain ⟨-, hRy, -⟩ := dvd_all_of_confined_three hR0 hx hRx hxy hx0 hy0 h3R hconfR
    obtain ⟨-, hSy, -⟩ := dvd_all_of_confined_three hS0 hx hSx hxy hx1 hy1 h3S hconfS
    exact hRS (eq_of_two_confined_labels hR0 hS0 h3R h4R h3S h4S hx hy hxy hRx hRy hSx hSy)

end


/-- **Partition (3,2).** A pairwise incomparable triple at `x` and an incomparable pair at
`y ≠ x` admit a six-entry cover. -/
theorem case32 {L x y : ℤ} {M a b c d e : ℕ}
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M) (hxy : x ≠ y)
    (ha : (a : ℤ) ∣ x) (hb : (b : ℤ) ∣ x) (hc : (c : ℤ) ∣ x) (hd : (d : ℤ) ∣ y)
    (he : (e : ℤ) ∣ y)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d) (he0 : 0 < e)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M) (heM : e ≤ M)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hab' : ¬ a ∣ b) (hba' : ¬ b ∣ a) (hac' : ¬ a ∣ c) (hca' : ¬ c ∣ a)
    (hbc' : ¬ b ∣ c) (hcb' : ¬ c ∣ b) (hde' : ¬ d ∣ e) (hed' : ¬ e ∣ d) :
    FiveModuliCover L M a b c d e 6 := by
  classical
  set h := Nat.gcd d e with hhdef
  have hh0 : 0 < h := Nat.gcd_pos_of_pos_left e hd0
  have hhy : (h : ℤ) ∣ y := int_dvd_trans_nat (Nat.gcd_dvd_left d e) hd
  have h3h : 3 * h ≤ M := three_mul_le_of_incomparable hh0 (Nat.gcd_dvd_left d e)
    (Nat.gcd_dvd_right d e) hd0 he0 hdM heM hde' hed'
  -- facts about the three labels
  have lab : ∀ {P Q : ℕ}, (P : ℤ) ∣ x → (Q : ℤ) ∣ x → 0 < P → 0 < Q → P ≤ M → Q ≤ M →
      ¬ P ∣ Q → ¬ Q ∣ P →
      0 < Nat.gcd P Q ∧ 3 * Nat.gcd P Q ≤ M ∧ ((Nat.gcd P Q : ℕ) : ℤ) ∣ x := by
    intro P Q hP hQ hP0 hQ0 hPM hQM hPQ hQP
    have h0 := Nat.gcd_pos_of_pos_left Q hP0
    exact ⟨h0, three_mul_le_of_incomparable h0 (Nat.gcd_dvd_left P Q) (Nat.gcd_dvd_right P Q)
      hP0 hQ0 hPM hQM hPQ hQP, int_dvd_trans_nat (Nat.gcd_dvd_left P Q) hP⟩
  obtain ⟨hA0, h3A, hAx⟩ := lab ha hb ha0 hb0 haM hbM hab' hba'
  obtain ⟨hB0, h3B, hBx⟩ := lab ha hc ha0 hc0 haM hcM hac' hca'
  obtain ⟨hC0, h3C, hCx⟩ := lab hb hc hb0 hc0 hbM hcM hbc' hcb'
  -- the finishing step with any good third site
  have finish : ∀ z ∈ integerInterval L M, (h : ℤ) ∣ z → z ≠ x → z ≠ y →
      (∃ s ∈ integerInterval L M, ((Nat.gcd a b : ℕ) : ℤ) ∣ s ∧ s ≠ x ∧ s ≠ y ∧ s ≠ z) →
      (∃ s ∈ integerInterval L M, ((Nat.gcd a c : ℕ) : ℤ) ∣ s ∧ s ≠ x ∧ s ≠ y ∧ s ≠ z) →
      (∃ s ∈ integerInterval L M, ((Nat.gcd b c : ℕ) : ℤ) ∣ s ∧ s ≠ x ∧ s ≠ y ∧ s ≠ z) →
      FiveModuliCover L M a b c d e 6 := by
    intro z hz hhz hzx hzy gA gB gC
    obtain ⟨sA, hsA, dA, hAx', hAy', hAz'⟩ := gA
    obtain ⟨sB, hsB, dB, hBx', hBy', hBz'⟩ := gB
    obtain ⟨sC, hsC, dC, hCx', hCy', hCz'⟩ := gC
    have := case311_free (d := Nat.lcm d e) (e := h) hx hy hz hxy (Ne.symm hzx) (Ne.symm hzy)
      ha hb hc (int_lcm_dvd hd he) hhz ha0 hb0 hc0 haM hbM hcM hab' hba' hac' hca' hbc' hcb'
      hsA hsB hsC hAx' hAy' hAz' hBx' hBy' hBz' hCx' hCy' hCz' dA dB dC
    refine FiveModuliCover.of_prod_eq this ?_
    have := Nat.gcd_mul_lcm d e
    rw [← hhdef] at this
    calc a * b * c * Nat.lcm d e * h = a * b * c * (h * Nat.lcm d e) := by ring
      _ = a * b * c * d * e := by rw [this]; ring
  obtain ⟨z₀, hz₀, hhz₀, hz₀F⟩ := exists_multiple_outside {x, y} hh0 hy hhy (k := 2)
    (by omega) Finset.card_le_two
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz₀F
  obtain ⟨hz₀x, hz₀y⟩ := hz₀F
  have conf_of : ∀ {q : ℕ}, ¬ (∃ s ∈ integerInterval L M, (q : ℤ) ∣ s ∧ s ≠ x ∧ s ≠ y ∧ s ≠ z₀) →
      ∀ w ∈ integerInterval L M, (q : ℤ) ∣ w → w = x ∨ w = y ∨ w = z₀ := by
    intro q hno w hw hqw
    by_contra hne
    push Not at hne
    exact hno ⟨w, hw, hqw, hne.1, hne.2.1, hne.2.2⟩
  -- switch to a second site when one label is confined
  have switch : ∀ {R : ℕ}, 0 < R → 3 * R ≤ M → (R : ℤ) ∣ x →
      (∀ w ∈ integerInterval L M, (R : ℤ) ∣ w → w = x ∨ w = y ∨ w = z₀) →
      (∃ z₁ ∈ integerInterval L M, (h : ℤ) ∣ z₁ ∧ z₁ ≠ x ∧ z₁ ≠ y ∧ z₁ ≠ z₀) →
      FiveModuliCover L M a b c d e 6 := by
    intro R hR0 h3R hRx hconfR hz₁
    obtain ⟨z₁, hz₁, hhz₁, h1x, h1y, h10⟩ := hz₁
    exact finish z₁ hz₁ hhz₁ h1x h1y
      (case32_good_after_switch hx hy hxy (Ne.symm hz₀x) (Ne.symm hz₀y) (Ne.symm h1x)
        (Ne.symm h1y) (Ne.symm h10) hR0 hA0 h3R h3A hRx hAx hconfR)
      (case32_good_after_switch hx hy hxy (Ne.symm hz₀x) (Ne.symm hz₀y) (Ne.symm h1x)
        (Ne.symm h1y) (Ne.symm h10) hR0 hB0 h3R h3B hRx hBx hconfR)
      (case32_good_after_switch hx hy hxy (Ne.symm hz₀x) (Ne.symm hz₀y) (Ne.symm h1x)
        (Ne.symm h1y) (Ne.symm h10) hR0 hC0 h3R h3C hRx hCx hconfR)
  by_cases gA : ∃ s ∈ integerInterval L M, ((Nat.gcd a b : ℕ) : ℤ) ∣ s ∧ s ≠ x ∧ s ≠ y ∧ s ≠ z₀
  · by_cases gB : ∃ s ∈ integerInterval L M, ((Nat.gcd a c : ℕ) : ℤ) ∣ s ∧ s ≠ x ∧ s ≠ y ∧
        s ≠ z₀
    · by_cases gC : ∃ s ∈ integerInterval L M, ((Nat.gcd b c : ℕ) : ℤ) ∣ s ∧ s ≠ x ∧ s ≠ y ∧
          s ≠ z₀
      · exact finish z₀ hz₀ hhz₀ hz₀x hz₀y gA gB gC
      · exact switch hC0 h3C hCx (conf_of gC)
          (case32_switch hx hy hz₀ hxy (Ne.symm hz₀x) (Ne.symm hz₀y) hb hc hd he hb0 hc0 hd0
            he0 hbM hcM hdM heM hbd.symm hcd.symm hbc' hcb' hde' hed' (conf_of gC))
    · exact switch hB0 h3B hBx (conf_of gB)
        (case32_switch hx hy hz₀ hxy (Ne.symm hz₀x) (Ne.symm hz₀y) ha hc hd he ha0 hc0 hd0
          he0 haM hcM hdM heM had.symm hcd.symm hac' hca' hde' hed' (conf_of gB))
  · exact switch hA0 h3A hAx (conf_of gA)
      (case32_switch hx hy hz₀ hxy (Ne.symm hz₀x) (Ne.symm hz₀y) ha hb hd he ha0 hb0 hd0
        he0 haM hbM hdM heM had.symm hbd.symm hab' hba' hde' hed' (conf_of gA))

end Erdos708.Five
