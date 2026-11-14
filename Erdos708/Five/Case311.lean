module

public import Erdos708.Five.Case221

@[expose] public section

/-!
# Partition (3,1,1)

Pairwise incomparable moduli `a, b, c` share anchor `x`; `d` has anchor `y` and `e` has
anchor `z`, with the anchors distinct. Then six interval entries cover `abcde`. This is
Section 5 of `G5_COMPLETE_CANDIDATE.md`.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

/-- Prime-by-prime divisibility for gcd/lcm expressions. -/
macro "factor_omega" : tactic => `(tactic| (
  rw [← Nat.factorization_le_iff_dvd (by positivity) (by positivity)]
  intro p
  simp (disch := simp_all [Nat.lcm_eq_zero_iff, Nat.gcd_eq_zero_iff]) only
    [Nat.factorization_mul, Nat.factorization_lcm, Nat.factorization_gcd,
     Finsupp.coe_add, Pi.add_apply, Finsupp.sup_apply, Finsupp.inf_apply]
  omega))

section Identities

variable {a b c : ℕ}

theorem triple_sep (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * b * c ∣ Nat.lcm (Nat.lcm a b) c * Nat.gcd a b * Nat.gcd a c * Nat.gcd b c := by
  factor_omega

theorem triple_ab_ac (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * b * c ∣ Nat.lcm (Nat.lcm a b) c * Nat.lcm (Nat.gcd a b) (Nat.gcd a c) * Nat.gcd b c := by
  factor_omega

theorem triple_ab_bc (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * b * c ∣ Nat.lcm (Nat.lcm a b) c * Nat.lcm (Nat.gcd a b) (Nat.gcd b c) * Nat.gcd a c := by
  factor_omega

theorem triple_ac_bc (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * b * c ∣ Nat.lcm (Nat.lcm a b) c * Nat.lcm (Nat.gcd a c) (Nat.gcd b c) * Nat.gcd a b := by
  factor_omega

theorem triple_all (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * b * c ∣ Nat.lcm (Nat.lcm a b) c *
      Nat.lcm (Nat.lcm (Nat.gcd a b) (Nat.gcd a c)) (Nat.gcd b c) *
        Nat.gcd (Nat.gcd a b) c := by
  factor_omega

theorem lift_de₂ {d e P X Y : ℕ} (h : a * b * c ∣ P * X * Y) :
    a * b * c * d * e ∣ P * d * e * X * Y := by
  have := Nat.mul_dvd_mul h (dvd_refl (d * e))
  calc a * b * c * d * e = a * b * c * (d * e) := by ring
    _ ∣ P * X * Y * (d * e) := this
    _ = P * d * e * X * Y := by ring

theorem lift_de₃ {d e P X Y Z : ℕ} (h : a * b * c ∣ P * X * Y * Z) :
    a * b * c * d * e ∣ P * d * e * X * Y * Z := by
  have := Nat.mul_dvd_mul h (dvd_refl (d * e))
  calc a * b * c * d * e = a * b * c * (d * e) := by ring
    _ ∣ P * X * Y * Z * (d * e) := this
    _ = P * d * e * X * Y * Z := by ring

end Identities

section Free

variable {L x y z : ℤ} {M a b c d e : ℕ}

/-- Branch: all three triple pair-labels have free sites outside the anchors. -/
theorem case311_free {sA sB sC : ℤ}
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : (a : ℤ) ∣ x) (hb : (b : ℤ) ∣ x) (hc : (c : ℤ) ∣ x) (hd : (d : ℤ) ∣ y)
    (he : (e : ℤ) ∣ z)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M)
    (hab' : ¬ a ∣ b) (hba' : ¬ b ∣ a) (hac' : ¬ a ∣ c) (hca' : ¬ c ∣ a)
    (hbc' : ¬ b ∣ c) (hcb' : ¬ c ∣ b)
    (hsA : sA ∈ integerInterval L M) (hsB : sB ∈ integerInterval L M)
    (hsC : sC ∈ integerInterval L M)
    (hAx : sA ≠ x) (hAy : sA ≠ y) (hAz : sA ≠ z)
    (hBx : sB ≠ x) (hBy : sB ≠ y) (hBz : sB ≠ z)
    (hCx : sC ≠ x) (hCy : sC ≠ y) (hCz : sC ≠ z)
    (dA : ((Nat.gcd a b : ℕ) : ℤ) ∣ sA) (dB : ((Nat.gcd a c : ℕ) : ℤ) ∣ sB)
    (dC : ((Nat.gcd b c : ℕ) : ℤ) ∣ sC) :
    FiveModuliCover L M a b c d e 6 := by
  classical
  have ha' : a ≠ 0 := ha0.ne'
  have hb' : b ≠ 0 := hb0.ne'
  have hc' : c ≠ 0 := hc0.ne'
  have hL : ((Nat.lcm (Nat.lcm a b) c : ℕ) : ℤ) ∣ x := int_lcm_dvd (int_lcm_dvd ha hb) hc
  by_cases hAB : sA = sB
  · subst hAB
    by_cases hAC : sA = sC
    · subst hAC
      set G := Nat.gcd (Nat.gcd a b) c with hG
      have hG0 : 0 < G := Nat.gcd_pos_of_pos_right _ hc0
      have hGa : G ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left a b)
      have hGb : G ∣ b := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right a b)
      have hGc : G ∣ c := Nat.gcd_dvd_right _ _
      have h5G : 5 * G ≤ M := five_mul_le_of_incomparable_three hG0 hGa hGb hGc ha0 hb0 hc0
        haM hbM hcM hab' hba' hac' hca' hbc' hcb'
      obtain ⟨u, hu, huG, huF⟩ := exists_multiple_outside {x, y, z, sA} hG0 hx
        (int_dvd_trans_nat hGa ha) (k := 4) (by omega) Finset.card_le_four
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at huF
      obtain ⟨hux, huy, huz, hus⟩ := huF
      exact cover_five hxy hxz (Ne.symm hAx) (Ne.symm hux) hyz (Ne.symm hAy) (Ne.symm huy)
        (Ne.symm hAz) (Ne.symm huz) (Ne.symm hus) hx hy hz hsA hu hL hd he
        (int_lcm_dvd (int_lcm_dvd dA dB) dC) huG (lift_de₂ (triple_all ha' hb' hc'))
    · exact cover_five hxy hxz (Ne.symm hAx) (Ne.symm hCx) hyz (Ne.symm hAy) (Ne.symm hCy)
        (Ne.symm hAz) (Ne.symm hCz) hAC hx hy hz hsA hsC hL hd he
        (int_lcm_dvd dA dB) dC (lift_de₂ (triple_ab_ac ha' hb' hc'))
  · by_cases hAC : sA = sC
    · subst hAC
      exact cover_five hxy hxz (Ne.symm hAx) (Ne.symm hBx) hyz (Ne.symm hAy) (Ne.symm hBy)
        (Ne.symm hAz) (Ne.symm hBz) hAB hx hy hz hsA hsB hL hd he
        (int_lcm_dvd dA dC) dB (lift_de₂ (triple_ab_bc ha' hb' hc'))
    · by_cases hBC : sB = sC
      · subst hBC
        exact cover_five hxy hxz (Ne.symm hBx) (Ne.symm hAx) hyz (Ne.symm hBy) (Ne.symm hAy)
          (Ne.symm hBz) (Ne.symm hAz) (Ne.symm hAB) hx hy hz hsB hsA hL hd he
          (int_lcm_dvd dB dC) dA (lift_de₂ (triple_ac_bc ha' hb' hc'))
      · exact cover_six hxy hxz (Ne.symm hAx) (Ne.symm hBx) (Ne.symm hCx) hyz (Ne.symm hAy)
          (Ne.symm hBy) (Ne.symm hCy) (Ne.symm hAz) (Ne.symm hBz) (Ne.symm hCz) hAB hAC hBC
          hx hy hz hsA hsB hsC hL hd he dA dB dC (lift_de₃ (triple_sep ha' hb' hc'))

end Free


section Blocked

variable {L x y z : ℤ} {M a b c d e : ℕ}

theorem case311_blocked_product :
    a * b * c * d * e ∣
      Nat.lcm (Nat.lcm a b) c * Nat.lcm (Nat.gcd a b) d * e * Nat.gcd (Nat.lcm a b) c *
        Nat.gcd (Nat.gcd a b) d := by
  have h1 := Nat.gcd_mul_lcm a b
  have h2 := Nat.gcd_mul_lcm (Nat.lcm a b) c
  have h3 := Nat.gcd_mul_lcm (Nat.gcd a b) d
  apply dvd_of_eq
  calc a * b * c * d * e = (Nat.gcd a b * Nat.lcm a b) * c * d * e := by rw [h1]
    _ = (Nat.gcd (Nat.lcm a b) c * Nat.lcm (Nat.lcm a b) c) *
          (Nat.gcd (Nat.gcd a b) d * Nat.lcm (Nat.gcd a b) d) * e := by rw [h2, h3]; ring
    _ = _ := by ring

/-- Core blocked branch: `A = gcd a b` is confined to the anchors and `A ∤ d`. -/
theorem case311_blocked_core
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : (a : ℤ) ∣ x) (hb : (b : ℤ) ∣ x) (hc : (c : ℤ) ∣ x) (hd : (d : ℤ) ∣ y)
    (he : (e : ℤ) ∣ z)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M)
    (hca : c ≠ a) (hcb : c ≠ b)
    (hab' : ¬ a ∣ b) (hba' : ¬ b ∣ a) (hca' : ¬ c ∣ a)
    (hconf : ∀ w ∈ integerInterval L M, ((Nat.gcd a b : ℕ) : ℤ) ∣ w →
      w = x ∨ w = y ∨ w = z)
    (hdA : ¬ Nat.gcd a b ∣ d) :
    FiveModuliCover L M a b c d e 6 := by
  classical
  set A := Nat.gcd a b with hAdef
  have hA0 : 0 < A := Nat.gcd_pos_of_pos_left b ha0
  have hAx : (A : ℤ) ∣ x := int_dvd_trans_nat (Nat.gcd_dvd_left a b) ha
  have h3A : 3 * A ≤ M := three_mul_le_of_incomparable hA0 (Nat.gcd_dvd_left a b)
    (Nat.gcd_dvd_right a b) ha0 hb0 haM hbM hab' hba'
  have hM4 : M < 4 * A := lt_four_mul_of_confined {x, y, z} hA0 hx hAx Finset.card_le_three
    (fun w hw hAw => by rcases hconf w hw hAw with rfl | rfl | rfl <;> simp)
  have hab23 := eq_two_three_of_incomparable (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
    ha0 hb0 haM hbM hM4 hab' hba'
  rw [← hAdef] at hab23
  obtain ⟨-, hAy, hAz⟩ := dvd_all_of_confined_three hA0 hx hAx hxy hxz hyz h3A hconf
  have hdiff := diff_of_confined_three hA0 hx hy hz hAx hAy hAz hxy hxz hyz hconf
  set Lab := Nat.lcm a b with hLdef
  have hL6 : Lab = 6 * A := by
    rcases hab23 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hLdef, h1, h2, Nat.lcm_mul_right]; norm_num [Nat.lcm]
    · rw [hLdef, h1, h2, Nat.lcm_mul_right]; norm_num [Nat.lcm]
  have hcA : ¬ A ∣ c := by
    intro hAc
    rcases eq_one_two_three_mul hAc hc0 hcM hM4 with h | h | h
    · exact hca' (h ▸ Nat.gcd_dvd_left a b)
    · rcases hab23 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hab23 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  set t := Nat.gcd Lab c with htdef
  have ht0 : 0 < t := Nat.gcd_pos_of_pos_right _ hc0
  have htc : t ∣ c := Nat.gcd_dvd_right _ _
  have htL : t ∣ Lab := Nat.gcd_dvd_left _ _
  have hLx : (Lab : ℤ) ∣ x := int_lcm_dvd ha hb
  have htx : (t : ℤ) ∣ x := int_dvd_trans_nat htL hLx
  have htle : t ≤ c := Nat.le_of_dvd hc0 htc
  -- `t` is at most `M/2`
  have h2t : 2 * t ≤ M := by
    by_contra hbig
    push Not at hbig
    obtain ⟨j, hj⟩ : t ∣ 6 * A := hL6 ▸ htL
    have hj4 : j < 4 := by
      by_contra h; push Not at h; nlinarith
    have hj2 : 2 ≤ j := by
      by_contra h; push Not at h
      interval_cases j <;> omega
    have htv : t = 3 * A ∨ t = 2 * A := by interval_cases j <;> omega
    obtain ⟨m, hm⟩ := htc
    have hm1 : m = 1 := by
      have hm0 : m ≠ 0 := by rintro rfl; omega
      by_contra h
      have : 2 ≤ m := by omega
      nlinarith
    subst hm1
    rcases htv with h | h <;> rcases hab23 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  -- `t` has a free site outside the anchors
  have hfree : ∃ w ∈ integerInterval L M, (t : ℤ) ∣ w ∧ w ≠ x ∧ w ≠ y ∧ w ≠ z := by
    by_contra hno
    have hconft : ∀ w ∈ integerInterval L M, (t : ℤ) ∣ w → w = x ∨ w = y ∨ w = z := by
      intro w hw htw
      by_contra hne
      push Not at hne
      exact hno ⟨w, hw, htw, hne.1, hne.2.1, hne.2.2⟩
    have hcard := card_interval_multiples_ge_of_known_multiple_candidate (k := 1) ht0 hx htx
      (by omega)
    obtain ⟨r, hr, hrx⟩ := Finset.exists_mem_ne
      (s := (integerInterval L M).filter (fun w => (t : ℤ) ∣ w)) (by omega) x
    rw [Finset.mem_filter] at hr
    have hrS : r ∈ ({x, y, z} : Finset ℤ) := by
      rcases hconft r hr.1 hr.2 with h | h | h <;> simp [h]
    have hd2 := hdiff x (by simp) r hrS (Ne.symm hrx)
    have htdiff : (t : ℤ) ∣ x - r := dvd_sub htx hr.2
    have ht2A : t ∣ 2 * A := by
      have : (t : ℤ) ∣ 2 * (A : ℤ) := by
        rcases hd2 with h | h | h | h <;> rw [h] at htdiff
        · exact htdiff.mul_left 2
        · exact (dvd_neg.mp htdiff).mul_left 2
        · exact htdiff
        · exact dvd_neg.mp htdiff
      exact_mod_cast this
    have htA : t ≠ A := fun h => hcA (h ▸ htc)
    have ht2A' : t ≠ 2 * A := by
      intro h
      obtain ⟨m, hm⟩ := htc
      have hm1 : m = 1 := by
        have hm0 : m ≠ 0 := by rintro rfl; omega
        by_contra hne
        have : 2 ≤ m := by omega
        nlinarith
      subst hm1
      rcases hab23 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have h3t : 3 * t ≤ 2 * A := by
      obtain ⟨j, hj⟩ := ht2A
      have hj3 : 3 ≤ j := by
        by_contra h; push Not at h
        interval_cases j <;> omega
      nlinarith
    have hM4t := lt_four_mul_of_confined {x, y, z} ht0 hx htx Finset.card_le_three
      (fun w hw htw => by rcases hconft w hw htw with rfl | rfl | rfl <;> simp)
    omega
  obtain ⟨w, hw, htw, hwx, hwy, hwz⟩ := hfree
  have hk2 := two_mul_gcd_le_of_not_dvd hA0 hdA
  have hk0 : 0 < Nat.gcd A d := Nat.gcd_pos_of_pos_left d hA0
  obtain ⟨v, hv, hvk, hvF⟩ := exists_multiple_outside {x, y, z, w} hk0 hx
    (int_dvd_trans_nat (Nat.gcd_dvd_left A d) hAx) (k := 4) (by omega) Finset.card_le_four
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvF
  obtain ⟨hvx, hvy, hvz, hvw⟩ := hvF
  exact cover_five hxy hxz (Ne.symm hwx) (Ne.symm hvx) hyz (Ne.symm hwy) (Ne.symm hvy)
    (Ne.symm hwz) (Ne.symm hvz) (Ne.symm hvw) hx hy hz hw hv
    (int_lcm_dvd hLx hc) (int_lcm_dvd hAy hd) he htw hvk case311_blocked_product

/-- Blocked branch: `A = gcd a b` is confined to the anchors. -/
theorem case311_blocked
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : (a : ℤ) ∣ x) (hb : (b : ℤ) ∣ x) (hc : (c : ℤ) ∣ x) (hd : (d : ℤ) ∣ y)
    (he : (e : ℤ) ∣ z)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d) (he0 : 0 < e)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M) (heM : e ≤ M)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hea : e ≠ a) (heb : e ≠ b)
    (hde : d ≠ e)
    (hab' : ¬ a ∣ b) (hba' : ¬ b ∣ a) (hca' : ¬ c ∣ a)
    (hconf : ∀ w ∈ integerInterval L M, ((Nat.gcd a b : ℕ) : ℤ) ∣ w →
      w = x ∨ w = y ∨ w = z) :
    FiveModuliCover L M a b c d e 6 := by
  classical
  by_cases hdA : Nat.gcd a b ∣ d
  · -- then `e` is not a multiple of `A`; exchange the singletons
    have hA0 : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha0
    have hAx : ((Nat.gcd a b : ℕ) : ℤ) ∣ x := int_dvd_trans_nat (Nat.gcd_dvd_left a b) ha
    have hM4 := lt_four_mul_of_confined {x, y, z} hA0 hx hAx Finset.card_le_three
      (fun w hw hAw => by rcases hconf w hw hAw with rfl | rfl | rfl <;> simp)
    have hab23 := eq_two_three_of_incomparable (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
      ha0 hb0 haM hbM hM4 hab' hba'
    have heA : ¬ Nat.gcd a b ∣ e := by
      intro hAe
      rcases eq_one_two_three_mul hdA hd0 hdM hM4 with h | h | h <;>
        rcases eq_one_two_three_mul hAe he0 heM hM4 with h' | h' | h' <;>
        rcases hab23 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have := case311_blocked_core hx hz hy hxz hxy hyz.symm ha hb hc he hd ha0 hb0 hc0
      haM hbM hcM hca hcb hab' hba' hca'
      (fun w hw hAw => by rcases hconf w hw hAw with h | h | h <;> simp [h]) heA
    exact FiveModuliCover.of_prod_eq this (by ring)
  · exact case311_blocked_core hx hy hz hxy hxz hyz ha hb hc hd he ha0 hb0 hc0
      haM hbM hcM hca hcb hab' hba' hca' hconf hdA

end Blocked


/-- **Partition (3,1,1).** A pairwise incomparable triple at one anchor and two singletons at
two further distinct anchors admit a six-entry cover. -/
theorem case311 {L x y z : ℤ} {M a b c d e : ℕ}
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : (a : ℤ) ∣ x) (hb : (b : ℤ) ∣ x) (hc : (c : ℤ) ∣ x) (hd : (d : ℤ) ∣ y)
    (he : (e : ℤ) ∣ z)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d) (he0 : 0 < e)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M) (heM : e ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hab' : ¬ a ∣ b) (hba' : ¬ b ∣ a) (hac' : ¬ a ∣ c) (hca' : ¬ c ∣ a)
    (hbc' : ¬ b ∣ c) (hcb' : ¬ c ∣ b) :
    FiveModuliCover L M a b c d e 6 := by
  classical
  have conf_of : ∀ {q : ℕ}, ¬ (∃ w ∈ integerInterval L M, (q : ℤ) ∣ w ∧ w ≠ x ∧ w ≠ y ∧ w ≠ z) →
      ∀ w ∈ integerInterval L M, (q : ℤ) ∣ w → w = x ∨ w = y ∨ w = z := by
    intro q hno w hw hqw
    by_contra hne
    push Not at hne
    exact hno ⟨w, hw, hqw, hne.1, hne.2.1, hne.2.2⟩
  by_cases hA : ∃ w ∈ integerInterval L M, ((Nat.gcd a b : ℕ) : ℤ) ∣ w ∧ w ≠ x ∧ w ≠ y ∧ w ≠ z
  · by_cases hB : ∃ w ∈ integerInterval L M, ((Nat.gcd a c : ℕ) : ℤ) ∣ w ∧
        w ≠ x ∧ w ≠ y ∧ w ≠ z
    · by_cases hC : ∃ w ∈ integerInterval L M, ((Nat.gcd b c : ℕ) : ℤ) ∣ w ∧
          w ≠ x ∧ w ≠ y ∧ w ≠ z
      · obtain ⟨sA, hsA, dA, hAx, hAy, hAz⟩ := hA
        obtain ⟨sB, hsB, dB, hBx, hBy, hBz⟩ := hB
        obtain ⟨sC, hsC, dC, hCx, hCy, hCz⟩ := hC
        exact case311_free hx hy hz hxy hxz hyz ha hb hc hd he ha0 hb0 hc0 haM hbM hcM
          hab' hba' hac' hca' hbc' hcb' hsA hsB hsC hAx hAy hAz hBx hBy hBz hCx hCy hCz dA dB dC
      · have := case311_blocked hx hy hz hxy hxz hyz hb hc ha hd he hb0 hc0 ha0 hd0 he0
          hbM hcM haM hdM heM hab hac hbd.symm hcd.symm hbe.symm hce.symm hde
          hbc' hcb' hab' (conf_of hC)
        exact FiveModuliCover.of_prod_eq this (by ring)
    · have := case311_blocked hx hy hz hxy hxz hyz ha hc hb hd he ha0 hc0 hb0 hd0 he0
        haM hcM hbM hdM heM hab.symm hbc had.symm hcd.symm hae.symm hce.symm hde
        hac' hca' hba' (conf_of hB)
      exact FiveModuliCover.of_prod_eq this (by ring)
  · exact case311_blocked hx hy hz hxy hxz hyz ha hb hc hd he ha0 hb0 hc0 hd0 he0
      haM hbM hcM hdM heM hac.symm hbc.symm had.symm hbd.symm hae.symm hbe.symm hde
      hab' hba' hca' (conf_of hA)

end Erdos708.Five
