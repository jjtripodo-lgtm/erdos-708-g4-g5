module

public import Erdos708.Five.SiteArith

@[expose] public section

/-!
# Partition (2,2,1)

Moduli `a, b` share anchor `x`, `c, d` share anchor `y`, `e` has anchor `z`, with the
three anchors distinct and each pair incomparable. Then six interval entries cover
`abcde`. This is Section 6 of `G5_COMPLETE_CANDIDATE.md`.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

section

variable {L x y z : ℤ} {M a b c d e : ℕ}

/-- Payment identity used when the second pair contains `g` itself. -/
theorem case221_small_product (hcg : c = Nat.gcd a b) :
    a * b * c * d * e ∣
      Nat.lcm a b * Nat.lcm c d * Nat.lcm e (Nat.gcd a b) *
        Nat.gcd (Nat.gcd a b) d * Nat.gcd (Nat.gcd a b) e := by
  set g := Nat.gcd a b with hg
  subst hcg
  have h1 : Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
  have h2 : Nat.gcd g d * Nat.lcm g d = g * d := Nat.gcd_mul_lcm g d
  have h3 : Nat.gcd e g * Nat.lcm e g = e * g := Nat.gcd_mul_lcm e g
  have h4 : Nat.gcd g e = Nat.gcd e g := Nat.gcd_comm g e
  apply dvd_of_eq
  rw [h4]
  calc a * b * g * d * e = (Nat.gcd a b * Nat.lcm a b) * g * d * e := by rw [h1]
    _ = Nat.lcm a b * (Nat.gcd g d * Nat.lcm g d) * (Nat.gcd e g * Nat.lcm e g) := by
        rw [h2, h3, ← hg]; ring
    _ = _ := by ring

/-- Payment identity when neither member of the second pair is a multiple of `g`. -/
theorem case221_spread_product :
    a * b * c * d * e ∣
      Nat.lcm a b * Nat.lcm (Nat.lcm c d) (Nat.gcd a b) * e * Nat.gcd c d *
        Nat.gcd (Nat.gcd a b) c * Nat.gcd (Nat.gcd a b) d := by
  set g := Nat.gcd a b with hg
  set Lc := Nat.lcm c d with hLc
  have h1 : Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
  have h2 : Nat.gcd c d * Nat.lcm c d = c * d := Nat.gcd_mul_lcm c d
  have h3 : Nat.gcd Lc g * Nat.lcm Lc g = Lc * g := Nat.gcd_mul_lcm Lc g
  have h4 : Nat.gcd Lc g ∣ Nat.gcd g c * Nat.gcd g d := by
    rw [Nat.gcd_comm]
    exact (Nat.gcd_dvd_gcd_of_dvd_right g (Nat.lcm_dvd_mul c d)).trans
      (Nat.gcd_mul_right_dvd_mul_gcd g c d)
  have hlhs : a * b * c * d * e =
      Nat.lcm a b * Nat.gcd c d * e * (Nat.gcd Lc g * Nat.lcm Lc g) := by
    rw [h3]
    calc a * b * c * d * e = (Nat.gcd a b * Nat.lcm a b) * (Nat.gcd c d * Nat.lcm c d) * e := by
          rw [h1, h2]; ring
      _ = _ := by rw [← hg, ← hLc]; ring
  rw [hlhs]
  have := Nat.mul_dvd_mul_left (Nat.lcm a b * Nat.gcd c d * e * Nat.lcm Lc g) h4
  calc Nat.lcm a b * Nat.gcd c d * e * (Nat.gcd Lc g * Nat.lcm Lc g)
      = Nat.lcm a b * Nat.gcd c d * e * Nat.lcm Lc g * Nat.gcd Lc g := by ring
    _ ∣ Nat.lcm a b * Nat.gcd c d * e * Nat.lcm Lc g * (Nat.gcd g c * Nat.gcd g d) := this
    _ = _ := by ring

/-- Payment identity when both pair residuals share one free site. -/
theorem case221_shared_product :
    a * b * c * d * e ∣
      Nat.lcm a b * Nat.lcm c d * e * Nat.lcm (Nat.gcd a b) (Nat.gcd c d) *
        Nat.gcd (Nat.gcd a b) (Nat.gcd c d) := by
  have h1 : Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
  have h2 : Nat.gcd c d * Nat.lcm c d = c * d := Nat.gcd_mul_lcm c d
  have h3 := Nat.gcd_mul_lcm (Nat.gcd a b) (Nat.gcd c d)
  apply dvd_of_eq
  calc a * b * c * d * e = (Nat.gcd a b * Nat.lcm a b) * (Nat.gcd c d * Nat.lcm c d) * e := by
        rw [h1, h2]; ring
    _ = Nat.lcm a b * Nat.lcm c d * e *
          (Nat.gcd (Nat.gcd a b) (Nat.gcd c d) * Nat.lcm (Nat.gcd a b) (Nat.gcd c d)) := by
        rw [h3]; ring
    _ = _ := by ring

/-- Payment identity when both pair residuals use different free sites. -/
theorem case221_separate_product :
    a * b * c * d * e ∣ Nat.lcm a b * Nat.lcm c d * e * Nat.gcd a b * Nat.gcd c d := by
  have h1 : Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
  have h2 : Nat.gcd c d * Nat.lcm c d = c * d := Nat.gcd_mul_lcm c d
  apply dvd_of_eq
  calc a * b * c * d * e = (Nat.gcd a b * Nat.lcm a b) * (Nat.gcd c d * Nat.lcm c d) * e := by
        rw [h1, h2]; ring
    _ = _ := by ring

end


section Cases

variable {L x y z : ℤ} {M a b c d e : ℕ}

/-- Branch: the second pair contains `g = gcd a b` itself. -/
theorem case221_small
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : (a : ℤ) ∣ x) (hb : (b : ℤ) ∣ x) (hc : (c : ℤ) ∣ y) (hd : (d : ℤ) ∣ y)
    (he : (e : ℤ) ∣ z) (ha0 : 0 < a)
    (h3g : 3 * Nat.gcd a b ≤ M) (hgz : ((Nat.gcd a b : ℕ) : ℤ) ∣ z)
    (hcg : c = Nat.gcd a b) (hdg : ¬ Nat.gcd a b ∣ d) (heg : ¬ Nat.gcd a b ∣ e) :
    FiveModuliCover L M a b c d e 6 := by
  classical
  have hg0 : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha0
  have hgx : ((Nat.gcd a b : ℕ) : ℤ) ∣ x := int_dvd_trans_nat (Nat.gcd_dvd_left a b) ha
  have hkd2 := two_mul_gcd_le_of_not_dvd hg0 hdg
  have hke2 := two_mul_gcd_le_of_not_dvd hg0 heg
  have hkd0 : 0 < Nat.gcd (Nat.gcd a b) d := Nat.gcd_pos_of_pos_left d hg0
  have hke0 : 0 < Nat.gcd (Nat.gcd a b) e := Nat.gcd_pos_of_pos_left e hg0
  obtain ⟨u₁, hu₁, hu₁d, hu₁F⟩ := exists_multiple_outside {x, y, z} hkd0 hx
    (int_dvd_trans_nat (Nat.gcd_dvd_left _ d) hgx) (k := 3) (by omega) Finset.card_le_three
  obtain ⟨u₂, hu₂, hu₂d, hu₂F⟩ := exists_multiple_outside {x, y, z, u₁} hke0 hx
    (int_dvd_trans_nat (Nat.gcd_dvd_left _ e) hgx) (k := 4) (by omega) Finset.card_le_four
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu₁F hu₂F
  obtain ⟨h1x, h1y, h1z⟩ := hu₁F
  obtain ⟨h2x, h2y, h2z, h21⟩ := hu₂F
  exact cover_five hxy hxz (Ne.symm h1x) (Ne.symm h2x) hyz (Ne.symm h1y) (Ne.symm h2y)
    (Ne.symm h1z) (Ne.symm h2z) (Ne.symm h21) hx hy hz hu₁ hu₂
    (int_lcm_dvd ha hb) (int_lcm_dvd hc hd) (int_lcm_dvd he hgz) hu₁d hu₂d
    (case221_small_product hcg)

/-- Branch: neither member of the second pair is a multiple of `g`. -/
theorem case221_spread {w : ℤ}
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hw : w ∈ integerInterval L M)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (ha : (a : ℤ) ∣ x) (hb : (b : ℤ) ∣ x) (hc : (c : ℤ) ∣ y) (hd : (d : ℤ) ∣ y)
    (he : (e : ℤ) ∣ z) (ha0 : 0 < a)
    (h3g : 3 * Nat.gcd a b ≤ M) (hgy : ((Nat.gcd a b : ℕ) : ℤ) ∣ y)
    (hwh : ((Nat.gcd c d : ℕ) : ℤ) ∣ w)
    (hcg : ¬ Nat.gcd a b ∣ c) (hdg : ¬ Nat.gcd a b ∣ d) :
    FiveModuliCover L M a b c d e 6 := by
  classical
  have hg0 : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha0
  have hgx : ((Nat.gcd a b : ℕ) : ℤ) ∣ x := int_dvd_trans_nat (Nat.gcd_dvd_left a b) ha
  have hkc2 := two_mul_gcd_le_of_not_dvd hg0 hcg
  have hkd2 := two_mul_gcd_le_of_not_dvd hg0 hdg
  have hkc0 : 0 < Nat.gcd (Nat.gcd a b) c := Nat.gcd_pos_of_pos_left c hg0
  have hkd0 : 0 < Nat.gcd (Nat.gcd a b) d := Nat.gcd_pos_of_pos_left d hg0
  obtain ⟨u₁, hu₁, hu₁d, hu₁F⟩ := exists_multiple_outside {x, y, z, w} hkc0 hx
    (int_dvd_trans_nat (Nat.gcd_dvd_left _ c) hgx) (k := 4) (by omega) Finset.card_le_four
  obtain ⟨u₂, hu₂, hu₂d, hu₂F⟩ := exists_multiple_outside {x, y, z, w, u₁} hkd0 hx
    (int_dvd_trans_nat (Nat.gcd_dvd_left _ d) hgx) (k := 5) (by omega) Finset.card_le_five
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu₁F hu₂F
  obtain ⟨h1x, h1y, h1z, h1w⟩ := hu₁F
  obtain ⟨h2x, h2y, h2z, h2w, h21⟩ := hu₂F
  exact cover_six hxy hxz (Ne.symm hwx) (Ne.symm h1x) (Ne.symm h2x) hyz (Ne.symm hwy)
    (Ne.symm h1y) (Ne.symm h2y) (Ne.symm hwz) (Ne.symm h1z) (Ne.symm h2z)
    (Ne.symm h1w) (Ne.symm h2w) (Ne.symm h21) hx hy hz hw hu₁ hu₂
    (int_lcm_dvd ha hb) (int_lcm_dvd (int_lcm_dvd hc hd) hgy) he hwh hu₁d hu₂d
    case221_spread_product

/-- Branch: both pair residuals have free sites outside the anchors. -/
theorem case221_both {w₁ w₂ : ℤ}
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hw₁ : w₁ ∈ integerInterval L M)
    (hw₂ : w₂ ∈ integerInterval L M)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1x : w₁ ≠ x) (h1y : w₁ ≠ y) (h1z : w₁ ≠ z)
    (h2x : w₂ ≠ x) (h2y : w₂ ≠ y) (h2z : w₂ ≠ z)
    (ha : (a : ℤ) ∣ x) (hb : (b : ℤ) ∣ x) (hc : (c : ℤ) ∣ y) (hd : (d : ℤ) ∣ y)
    (he : (e : ℤ) ∣ z)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hab' : ¬ a ∣ b) (hba' : ¬ b ∣ a) (hcd' : ¬ c ∣ d) (hdc' : ¬ d ∣ c)
    (hw₁g : ((Nat.gcd a b : ℕ) : ℤ) ∣ w₁) (hw₂h : ((Nat.gcd c d : ℕ) : ℤ) ∣ w₂) :
    FiveModuliCover L M a b c d e 6 := by
  classical
  by_cases h12 : w₁ = w₂
  · subst h12
    set q := Nat.gcd (Nat.gcd a b) (Nat.gcd c d) with hqdef
    have hg0 : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha0
    have hq0 : 0 < q := Nat.gcd_pos_of_pos_left _ hg0
    have hqg : q ∣ Nat.gcd a b := Nat.gcd_dvd_left _ _
    have hqh : q ∣ Nat.gcd c d := Nat.gcd_dvd_right _ _
    have hqa : q ∣ a := hqg.trans (Nat.gcd_dvd_left a b)
    have hqb : q ∣ b := hqg.trans (Nat.gcd_dvd_right a b)
    have hqc : q ∣ c := hqh.trans (Nat.gcd_dvd_left c d)
    have hqd : q ∣ d := hqh.trans (Nat.gcd_dvd_right c d)
    have hlt : ∀ {m n : ℕ}, 0 < m → q ∣ m → q ∣ n → ¬ m ∣ n → q < m := by
      intro m n hm hqm hqn hmn
      rcases (Nat.le_of_dvd hm hqm).lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hqn) hmn
    have h5q : 5 * q ≤ M := five_mul_le_of_four hqa hqb hqc hqd
      (hlt ha0 hqa hqb hab') (hlt hb0 hqb hqa hba') (hlt hc0 hqc hqd hcd')
      (hlt hd0 hqd hqc hdc') haM hbM hcM hdM hab hac had hbc hbd hcd
    have hqx : (q : ℤ) ∣ x := int_dvd_trans_nat (hqa) ha
    obtain ⟨u, hu, huq, huF⟩ := exists_multiple_outside {x, y, z, w₁} hq0 hx hqx
      (k := 4) (by omega) Finset.card_le_four
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at huF
    obtain ⟨hux, huy, huz, huw⟩ := huF
    exact cover_five hxy hxz (Ne.symm h1x) (Ne.symm hux) hyz (Ne.symm h1y) (Ne.symm huy)
      (Ne.symm h1z) (Ne.symm huz) (Ne.symm huw) hx hy hz hw₁ hu
      (int_lcm_dvd ha hb) (int_lcm_dvd hc hd) he (int_lcm_dvd hw₁g hw₂h) huq
      case221_shared_product
  · exact cover_five hxy hxz (Ne.symm h1x) (Ne.symm h2x) hyz (Ne.symm h1y) (Ne.symm h2y)
      (Ne.symm h1z) (Ne.symm h2z) h12 hx hy hz hw₁ hw₂
      (int_lcm_dvd ha hb) (int_lcm_dvd hc hd) he hw₁g hw₂h
      case221_separate_product

end Cases


section Blocked

variable {L x y z : ℤ} {M a b c d e : ℕ}

theorem eq_one_two_three_mul {g m M : ℕ} (hgm : g ∣ m) (hm0 : 0 < m) (hmM : m ≤ M)
    (hM : M < 4 * g) : m = g ∨ m = 2 * g ∨ m = 3 * g := by
  obtain ⟨s, rfl⟩ := hgm
  have hs : s < 4 := by by_contra h; push Not at h; nlinarith
  have hs0 : 0 < s := Nat.pos_of_mul_pos_left hm0
  interval_cases s <;> simp [Nat.mul_comm]

/-- The blocked branch: `g = gcd a b` has no multiple outside the three anchors. -/
theorem case221_blocked
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : (a : ℤ) ∣ x) (hb : (b : ℤ) ∣ x) (hc : (c : ℤ) ∣ y) (hd : (d : ℤ) ∣ y)
    (he : (e : ℤ) ∣ z)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d) (he0 : 0 < e)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M) (heM : e ≤ M)
    (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hce : c ≠ e) (hde : d ≠ e)
    (hab' : ¬ a ∣ b) (hba' : ¬ b ∣ a) (hcd' : ¬ c ∣ d) (hdc' : ¬ d ∣ c)
    (hconf : ∀ w ∈ integerInterval L M, ((Nat.gcd a b : ℕ) : ℤ) ∣ w →
      w = x ∨ w = y ∨ w = z) :
    FiveModuliCover L M a b c d e 6 := by
  classical
  set g := Nat.gcd a b with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left b ha0
  have hgx : (g : ℤ) ∣ x := int_dvd_trans_nat (Nat.gcd_dvd_left a b) ha
  have h3g : 3 * g ≤ M := three_mul_le_of_incomparable hg0 (Nat.gcd_dvd_left a b)
    (Nat.gcd_dvd_right a b) ha0 hb0 haM hbM hab' hba'
  have hM4 : M < 4 * g := lt_four_mul_of_confined {x, y, z} hg0 hx hgx Finset.card_le_three
    (fun w hw hgw => by rcases hconf w hw hgw with rfl | rfl | rfl <;> simp)
  have hab23 := eq_two_three_of_incomparable (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
    ha0 hb0 haM hbM hM4 hab' hba'
  rw [← hgdef] at hab23
  obtain ⟨-, hgy, hgz⟩ := dvd_all_of_confined_three hg0 hx hgx hxy hxz hyz h3g hconf
  -- a multiple of `m` in `{g, 2g, 3g}` other than `a, b` must be `g`
  have hone : ∀ {m : ℕ}, g ∣ m → 0 < m → m ≤ M → m ≠ a → m ≠ b → m = g := by
    intro m hgm hm0 hmM hma hmb
    rcases eq_one_two_three_mul hgm hm0 hmM hM4 with h | h | h
    · exact h
    · exfalso; rcases hab23 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · exfalso; rcases hab23 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  set h := Nat.gcd c d with hhdef
  have hh0 : 0 < h := Nat.gcd_pos_of_pos_left d hc0
  have hhy : (h : ℤ) ∣ y := int_dvd_trans_nat (Nat.gcd_dvd_left c d) hc
  -- `h` has a free site outside the anchors
  have hfree : ∃ w ∈ integerInterval L M, (h : ℤ) ∣ w ∧ w ≠ x ∧ w ≠ y ∧ w ≠ z := by
    by_contra hno
    have hconfh : ∀ w ∈ integerInterval L M, (h : ℤ) ∣ w → w = x ∨ w = y ∨ w = z := by
      intro w hw hhw
      by_contra hne
      push Not at hne
      exact hno ⟨w, hw, hhw, hne.1, hne.2.1, hne.2.2⟩
    have h3h : 3 * h ≤ M := three_mul_le_of_incomparable hh0 (Nat.gcd_dvd_left c d)
      (Nat.gcd_dvd_right c d) hc0 hd0 hcM hdM hcd' hdc'
    obtain ⟨hhx, -, hhz⟩ := dvd_all_of_confined_three hh0 hy hhy hxy hxz hyz h3h hconfh
    set ℓ := Nat.lcm g h with hℓ
    have hℓx : (ℓ : ℤ) ∣ x := int_lcm_dvd hgx hhx
    have hℓy : (ℓ : ℤ) ∣ y := int_lcm_dvd hgy hhy
    have hℓz : (ℓ : ℤ) ∣ z := int_lcm_dvd hgz hhz
    have h2ℓ := two_mul_lt_of_three_multiples hx hy hz hℓx hℓy hℓz hxy hxz hyz
    have hgℓ : g ∣ ℓ := Nat.dvd_lcm_left g h
    have hhℓ : h ∣ ℓ := Nat.dvd_lcm_right g h
    have hℓ0 : 0 < ℓ := Nat.lcm_pos hg0 hh0
    have hℓg : ℓ = g := by
      obtain ⟨t, ht⟩ := hgℓ
      have ht1 : t < 2 := by
        by_contra hc'; push Not at hc'; nlinarith
      have ht0 : t ≠ 0 := by rintro rfl; omega
      have : t = 1 := by omega
      rw [ht, this, mul_one]
    have hM4h : M < 4 * h := lt_four_mul_of_confined {x, y, z} hh0 hy hhy Finset.card_le_three
      (fun w hw hhw => by rcases hconfh w hw hhw with rfl | rfl | rfl <;> simp)
    have hℓh : ℓ = h := by
      obtain ⟨t, ht⟩ := hhℓ
      have ht1 : t < 2 := by
        by_contra hc'; push Not at hc'; nlinarith
      have ht0 : t ≠ 0 := by rintro rfl; omega
      have : t = 1 := by omega
      rw [ht, this, mul_one]
    have hgh : g = h := hℓg.symm.trans hℓh
    have hgc : g ∣ c := hgh ▸ Nat.gcd_dvd_left c d
    have hgd : g ∣ d := hgh ▸ Nat.gcd_dvd_right c d
    have hcd23 := eq_two_three_of_incomparable hgc hgd hc0 hd0 hcM hdM hM4 hcd' hdc'
    rcases hcd23 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rcases hab23 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  obtain ⟨w, hw, hwh, hwx, hwy, hwz⟩ := hfree
  by_cases hcg : g ∣ c
  · have hc_eq : c = g := hone hcg hc0 hcM hac.symm hbc.symm
    have hdg : ¬ g ∣ d := by
      intro hgd
      have : d = g := hone hgd hd0 hdM had.symm hbd.symm
      exact hcd' (by rw [hc_eq, this])
    have heg : ¬ g ∣ e := by
      intro hge
      have : e = g := hone hge he0 heM hae.symm hbe.symm
      exact hce (hc_eq.trans this.symm)
    exact case221_small hx hy hz hxy hxz hyz ha hb hc hd he ha0 h3g hgz hc_eq hdg heg
  · by_cases hdg : g ∣ d
    · have hd_eq : d = g := hone hdg hd0 hdM had.symm hbd.symm
      have heg : ¬ g ∣ e := by
        intro hge
        have : e = g := hone hge he0 heM hae.symm hbe.symm
        exact hde (hd_eq.trans this.symm)
      exact FiveModuliCover.swap34
        (case221_small hx hy hz hxy hxz hyz ha hb hd hc he ha0 h3g hgz hd_eq hcg heg)
    · exact case221_spread hx hy hz hw hxy hxz hyz hwx hwy hwz ha hb hc hd he ha0 h3g hgy
        hwh hcg hdg

end Blocked


/-- **Partition (2,2,1).** Two incomparable pairs and a singleton at three distinct anchors
admit a six-entry cover. -/
theorem case221 {L x y z : ℤ} {M a b c d e : ℕ}
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : (a : ℤ) ∣ x) (hb : (b : ℤ) ∣ x) (hc : (c : ℤ) ∣ y) (hd : (d : ℤ) ∣ y)
    (he : (e : ℤ) ∣ z)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d) (he0 : 0 < e)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M) (heM : e ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hab' : ¬ a ∣ b) (hba' : ¬ b ∣ a) (hcd' : ¬ c ∣ d) (hdc' : ¬ d ∣ c) :
    FiveModuliCover L M a b c d e 6 := by
  classical
  by_cases hg : ∃ w ∈ integerInterval L M, ((Nat.gcd a b : ℕ) : ℤ) ∣ w ∧
      w ≠ x ∧ w ≠ y ∧ w ≠ z
  · by_cases hh : ∃ w ∈ integerInterval L M, ((Nat.gcd c d : ℕ) : ℤ) ∣ w ∧
        w ≠ x ∧ w ≠ y ∧ w ≠ z
    · obtain ⟨w₁, hw₁, hg₁, h1x, h1y, h1z⟩ := hg
      obtain ⟨w₂, hw₂, hh₂, h2x, h2y, h2z⟩ := hh
      exact case221_both hx hy hz hw₁ hw₂ hxy hxz hyz h1x h1y h1z h2x h2y h2z
        ha hb hc hd he ha0 hb0 hc0 hd0 haM hbM hcM hdM hab hac had hbc hbd hcd
        hab' hba' hcd' hdc' hg₁ hh₂
    · have hconf : ∀ w ∈ integerInterval L M, ((Nat.gcd c d : ℕ) : ℤ) ∣ w →
          w = y ∨ w = x ∨ w = z := by
        intro w hw hhw
        by_contra hne
        push Not at hne
        exact hh ⟨w, hw, hhw, hne.2.1, hne.1, hne.2.2⟩
      exact FiveModuliCover.swap_pairs
        (case221_blocked hy hx hz hxy.symm hyz hxz hc hd ha hb he hc0 hd0 ha0 hb0 he0
          hcM hdM haM hbM heM hac.symm hbc.symm hce had.symm hbd.symm hde hae hbe
          hcd' hdc' hab' hba' hconf)
  · have hconf : ∀ w ∈ integerInterval L M, ((Nat.gcd a b : ℕ) : ℤ) ∣ w →
        w = x ∨ w = y ∨ w = z := by
      intro w hw hgw
      by_contra hne
      push Not at hne
      exact hg ⟨w, hw, hgw, hne.1, hne.2.1, hne.2.2⟩
    exact case221_blocked hx hy hz hxy hxz hyz ha hb hc hd he ha0 hb0 hc0 hd0 he0
      haM hbM hcM hdM heM hac had hae hbc hbd hbe hce hde hab' hba' hcd' hdc' hconf

end Erdos708.Five
