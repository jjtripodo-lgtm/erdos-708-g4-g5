module

public import Erdos708.Five.Sites

@[expose] public section

/-!
# Arithmetic of interval sites

Helpers shared by the five-modulus partition cases.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

theorem int_dvd_of_nat {m : ℕ} {x : ℤ} (h : (m : ℤ) ∣ x) : m ∣ x.natAbs :=
  Int.natCast_dvd.mp h

theorem int_lcm_dvd {a b : ℕ} {x : ℤ} (ha : (a : ℤ) ∣ x) (hb : (b : ℤ) ∣ x) :
    ((Nat.lcm a b : ℕ) : ℤ) ∣ x :=
  Int.natCast_dvd.mpr (Nat.lcm_dvd (Int.natCast_dvd.mp ha) (Int.natCast_dvd.mp hb))

theorem int_dvd_trans_nat {m n : ℕ} {x : ℤ} (hmn : m ∣ n) (hx : (n : ℤ) ∣ x) :
    (m : ℤ) ∣ x :=
  (Int.natCast_dvd_natCast.mpr hmn).trans hx

/-- Injectivity of a six-site vector from pairwise distinctness. -/
theorem injective_six {x y z w u v : ℤ}
    (h01 : x ≠ y) (h02 : x ≠ z) (h03 : x ≠ w) (h04 : x ≠ u) (h05 : x ≠ v)
    (h12 : y ≠ z) (h13 : y ≠ w) (h14 : y ≠ u) (h15 : y ≠ v)
    (h23 : z ≠ w) (h24 : z ≠ u) (h25 : z ≠ v)
    (h34 : w ≠ u) (h35 : w ≠ v) (h45 : u ≠ v) :
    Function.Injective ![x, y, z, w, u, v] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- Injectivity of a five-site vector from pairwise distinctness. -/
theorem injective_five {x y z w u : ℤ}
    (h01 : x ≠ y) (h02 : x ≠ z) (h03 : x ≠ w) (h04 : x ≠ u)
    (h12 : y ≠ z) (h13 : y ≠ w) (h14 : y ≠ u)
    (h23 : z ≠ w) (h24 : z ≠ u) (h34 : w ≠ u) :
    Function.Injective ![x, y, z, w, u] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- If all multiples of `q` in the interval lie among three distinct interval points, one of
them is a multiple, and `3q ≤ M`, then all three points are multiples of `q`. -/
theorem dvd_all_of_confined_three {L p x y z : ℤ} {M q : ℕ} (hq : 0 < q)
    (hp : p ∈ integerInterval L M) (hpq : (q : ℤ) ∣ p)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (h3 : 3 * q ≤ M)
    (hconf : ∀ w ∈ integerInterval L M, (q : ℤ) ∣ w → w = x ∨ w = y ∨ w = z) :
    (q : ℤ) ∣ x ∧ (q : ℤ) ∣ y ∧ (q : ℤ) ∣ z := by
  classical
  let F := (integerInterval L M).filter (fun w => (q : ℤ) ∣ w)
  have hcard : 2 + 1 ≤ F.card :=
    card_interval_multiples_ge_of_known_multiple_candidate (k := 2) hq hp hpq (by omega)
  have hsub : F ⊆ {x, y, z} := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rcases hconf w hw.1 hw.2 with h | h | h <;> simp [h]
  have hS : ({x, y, z} : Finset ℤ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]
  have heq : F = {x, y, z} := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hx : x ∈ F := by rw [heq]; simp
  have hy : y ∈ F := by rw [heq]; simp
  have hz : z ∈ F := by rw [heq]; simp
  exact ⟨(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2, (Finset.mem_filter.mp hz).2⟩

/-- Three distinct interval multiples of `ℓ > 0` force `2ℓ < M`. -/
theorem two_mul_lt_of_three_multiples {L x y z : ℤ} {M ℓ : ℕ}
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M)
    (hxl : (ℓ : ℤ) ∣ x) (hyl : (ℓ : ℤ) ∣ y) (hzl : (ℓ : ℤ) ∣ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    2 * ℓ < M := by
  rw [mem_integerInterval] at hx hy hz
  obtain ⟨i, rfl⟩ := hxl
  obtain ⟨j, rfl⟩ := hyl
  obtain ⟨k, rfl⟩ := hzl
  have hij : i ≠ j := fun h => hxy (by rw [h])
  have hik : i ≠ k := fun h => hxz (by rw [h])
  have hjk : j ≠ k := fun h => hyz (by rw [h])
  have hl : (0 : ℤ) ≤ ℓ := by positivity
  have hcases : 2 ≤ i - j ∨ 2 ≤ j - i ∨ 2 ≤ i - k ∨ 2 ≤ k - i ∨ 2 ≤ j - k ∨ 2 ≤ k - j := by
    omega
  have key : 2 * (ℓ : ℤ) < M := by
    rcases hcases with h | h | h | h | h | h <;> nlinarith
  exact_mod_cast key

/-- Four distinct positive multiples of `q`, none equal to `q`, that are at most `M` force
`5q ≤ M`. -/
theorem five_mul_le_of_four {q a b c d M : ℕ}
    (ha : q ∣ a) (hb : q ∣ b) (hc : q ∣ c) (hd : q ∣ d)
    (ha2 : q < a) (hb2 : q < b) (hc2 : q < c) (hd2 : q < d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    5 * q ≤ M := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  obtain ⟨u, rfl⟩ := hc
  obtain ⟨v, rfl⟩ := hd
  have hs : 2 ≤ s := by
    by_contra h; push Not at h; interval_cases s <;> simp_all
  have ht : 2 ≤ t := by
    by_contra h; push Not at h; interval_cases t <;> simp_all
  have hu : 2 ≤ u := by
    by_contra h; push Not at h; interval_cases u <;> simp_all
  have hv : 2 ≤ v := by
    by_contra h; push Not at h; interval_cases v <;> simp_all
  have hst : s ≠ t := fun h => hab (by rw [h])
  have hsu : s ≠ u := fun h => hac (by rw [h])
  have hsv : s ≠ v := fun h => had (by rw [h])
  have htu : t ≠ u := fun h => hbc (by rw [h])
  have htv : t ≠ v := fun h => hbd (by rw [h])
  have huv : u ≠ v := fun h => hcd (by rw [h])
  have hcases : 5 ≤ s ∨ 5 ≤ t ∨ 5 ≤ u ∨ 5 ≤ v := by omega
  rcases hcases with h | h | h | h <;> nlinarith

/-- A proper divisor of `g` obtained as `gcd g c` with `g ∤ c` is at most `g / 2`. -/
theorem two_mul_gcd_le_of_not_dvd {g c : ℕ} (hg : 0 < g) (hgc : ¬ g ∣ c) :
    2 * Nat.gcd g c ≤ g := by
  have hdvd : Nat.gcd g c ∣ g := Nat.gcd_dvd_left g c
  obtain ⟨t, ht⟩ := hdvd
  have hpos : 0 < Nat.gcd g c := Nat.gcd_pos_of_pos_left c hg
  have ht2 : t ≠ 1 := by
    rintro rfl
    apply hgc
    rw [mul_one] at ht
    rw [ht]
    exact Nat.gcd_dvd_right g c
  have ht0 : t ≠ 0 := by
    rintro rfl
    omega
  have : 2 ≤ t := by omega
  calc 2 * Nat.gcd g c ≤ t * Nat.gcd g c := Nat.mul_le_mul_right _ this
    _ = g := by rw [mul_comm]; exact ht.symm

/-- Reordering moduli: swap the two pairs. -/
theorem FiveModuliCover.swap_pairs {L : ℤ} {M a b c d e k : ℕ}
    (h : FiveModuliCover L M c d a b e k) : FiveModuliCover L M a b c d e k := by
  obtain ⟨B, hB, hcard, hdvd⟩ := h
  refine ⟨B, hB, hcard, ?_⟩
  have : (a : ℤ) * b * c * d * e = (c : ℤ) * d * a * b * e := by ring
  rw [this]
  exact hdvd

/-- Reordering moduli: swap the third and fourth. -/
theorem FiveModuliCover.swap34 {L : ℤ} {M a b c d e k : ℕ}
    (h : FiveModuliCover L M a b d c e k) : FiveModuliCover L M a b c d e k := by
  obtain ⟨B, hB, hcard, hdvd⟩ := h
  refine ⟨B, hB, hcard, ?_⟩
  have : (a : ℤ) * b * c * d * e = (a : ℤ) * b * d * c * e := by ring
  rw [this]
  exact hdvd


/-- Six distinct interval sites with natural payments. -/
theorem cover_six {L : ℤ} {M a b c d e : ℕ} {x y z w u v : ℤ} {p₀ p₁ p₂ p₃ p₄ p₅ : ℕ}
    (h01 : x ≠ y) (h02 : x ≠ z) (h03 : x ≠ w) (h04 : x ≠ u) (h05 : x ≠ v)
    (h12 : y ≠ z) (h13 : y ≠ w) (h14 : y ≠ u) (h15 : y ≠ v)
    (h23 : z ≠ w) (h24 : z ≠ u) (h25 : z ≠ v)
    (h34 : w ≠ u) (h35 : w ≠ v) (h45 : u ≠ v)
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hw : w ∈ integerInterval L M)
    (hu : u ∈ integerInterval L M) (hv : v ∈ integerInterval L M)
    (d₀ : (p₀ : ℤ) ∣ x) (d₁ : (p₁ : ℤ) ∣ y) (d₂ : (p₂ : ℤ) ∣ z) (d₃ : (p₃ : ℤ) ∣ w)
    (d₄ : (p₄ : ℤ) ∣ u) (d₅ : (p₅ : ℤ) ∣ v)
    (ht : a * b * c * d * e ∣ p₀ * p₁ * p₂ * p₃ * p₄ * p₅) :
    FiveModuliCover L M a b c d e 6 := by
  refine cover_of_sites ![x, y, z, w, u, v] ![(p₀ : ℤ), p₁, p₂, p₃, p₄, p₅]
    (injective_six h01 h02 h03 h04 h05 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45) ?_ ?_ ?_
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · have hprod : (∏ i, ![(p₀ : ℤ), p₁, p₂, p₃, p₄, p₅] i) =
        ((p₀ * p₁ * p₂ * p₃ * p₄ * p₅ : ℕ) : ℤ) := by
      rw [Fin.prod_univ_six]; push_cast; rfl
    rw [hprod]
    exact_mod_cast ht

/-- Five distinct interval sites with natural payments. -/
theorem cover_five {L : ℤ} {M a b c d e : ℕ} {x y z w u : ℤ} {p₀ p₁ p₂ p₃ p₄ : ℕ}
    (h01 : x ≠ y) (h02 : x ≠ z) (h03 : x ≠ w) (h04 : x ≠ u)
    (h12 : y ≠ z) (h13 : y ≠ w) (h14 : y ≠ u)
    (h23 : z ≠ w) (h24 : z ≠ u) (h34 : w ≠ u)
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hw : w ∈ integerInterval L M)
    (hu : u ∈ integerInterval L M)
    (d₀ : (p₀ : ℤ) ∣ x) (d₁ : (p₁ : ℤ) ∣ y) (d₂ : (p₂ : ℤ) ∣ z) (d₃ : (p₃ : ℤ) ∣ w)
    (d₄ : (p₄ : ℤ) ∣ u)
    (ht : a * b * c * d * e ∣ p₀ * p₁ * p₂ * p₃ * p₄) :
    FiveModuliCover L M a b c d e 6 := by
  refine FiveModuliCover.mono (k := 5) ?_ (by norm_num)
  refine cover_of_sites ![x, y, z, w, u] ![(p₀ : ℤ), p₁, p₂, p₃, p₄]
    (injective_five h01 h02 h03 h04 h12 h13 h14 h23 h24 h34) ?_ ?_ ?_
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · have hprod : (∏ i, ![(p₀ : ℤ), p₁, p₂, p₃, p₄] i) =
        ((p₀ * p₁ * p₂ * p₃ * p₄ : ℕ) : ℤ) := by
      rw [Fin.prod_univ_five]; push_cast; rfl
    rw [hprod]
    exact_mod_cast ht


/-- Reorder the moduli of a cover when their products agree. -/
theorem FiveModuliCover.of_prod_eq {L : ℤ} {M a b c d e a' b' c' d' e' k : ℕ}
    (h : FiveModuliCover L M a' b' c' d' e' k)
    (heq : a' * b' * c' * d' * e' = a * b * c * d * e) :
    FiveModuliCover L M a b c d e k := by
  obtain ⟨B, hB, hcard, hdvd⟩ := h
  refine ⟨B, hB, hcard, ?_⟩
  have hz : ((a' : ℤ) * b' * c' * d' * e') = (a : ℤ) * b * c * d * e := by exact_mod_cast heq
  rw [← hz]
  exact hdvd

/-- Three distinct interval points that contain every interval multiple of `q > 0`, and are
all multiples of `q`, differ pairwise by `±q` or `±2q`. -/
theorem diff_of_confined_three {L x y z : ℤ} {M q : ℕ} (hq : 0 < q)
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M)
    (hxq : (q : ℤ) ∣ x) (hyq : (q : ℤ) ∣ y) (hzq : (q : ℤ) ∣ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconf : ∀ w ∈ integerInterval L M, (q : ℤ) ∣ w → w = x ∨ w = y ∨ w = z) :
    ∀ p ∈ ({x, y, z} : Finset ℤ), ∀ r ∈ ({x, y, z} : Finset ℤ), p ≠ r →
      p - r = q ∨ p - r = -q ∨ p - r = 2 * q ∨ p - r = -(2 * q) := by
  obtain ⟨i, rfl⟩ := hxq
  obtain ⟨j, rfl⟩ := hyq
  obtain ⟨k, rfl⟩ := hzq
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hij : i ≠ j := fun h => hxy (by rw [h])
  have hik : i ≠ k := fun h => hxz (by rw [h])
  have hjk : j ≠ k := fun h => hyz (by rw [h])
  -- every index strictly between two anchor indices is an anchor index
  have hbetween : ∀ {s t : ℤ}, (q : ℤ) * s ∈ integerInterval L M →
      (q : ℤ) * t ∈ integerInterval L M → ∀ m : ℤ, s < m → m < t → m = i ∨ m = j ∨ m = k := by
    intro s t hs ht m hsm hmt
    have hmem : (q : ℤ) * m ∈ integerInterval L M := by
      apply integerInterval_mem_of_between hs ht
      constructor
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (by nlinarith : (q : ℤ) * m ≤ q * t).trans (le_max_right _ _)
    rcases hconf _ hmem (dvd_mul_right _ _) with h | h | h
    · left; exact mul_left_cancel₀ hq'.ne' h
    · right; left; exact mul_left_cancel₀ hq'.ne' h
    · right; right; exact mul_left_cancel₀ hq'.ne' h
  -- pairwise index gaps are at most two
  have hgap : ∀ {s t : ℤ}, (q : ℤ) * s ∈ integerInterval L M →
      (q : ℤ) * t ∈ integerInterval L M → s ∈ ({i, j, k} : Finset ℤ) →
      t ∈ ({i, j, k} : Finset ℤ) → s < t → t - s ≤ 2 := by
    intro s t hs ht hsS htS hst
    by_contra hbig
    push Not at hbig
    have h1 := hbetween hs ht (s + 1) (by omega) (by omega)
    have h2 := hbetween hs ht (s + 2) (by omega) (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsS htS
    omega
  have hiS : i ∈ ({i, j, k} : Finset ℤ) := by simp
  have hjS : j ∈ ({i, j, k} : Finset ℤ) := by simp
  have hkS : k ∈ ({i, j, k} : Finset ℤ) := by simp
  have gij : |i - j| ≤ 2 := by
    rcases lt_or_gt_of_ne hij with h | h
    · have := hgap hx hy hiS hjS h; rw [abs_le]; constructor <;> omega
    · have := hgap hy hx hjS hiS h; rw [abs_le]; constructor <;> omega
  have gik : |i - k| ≤ 2 := by
    rcases lt_or_gt_of_ne hik with h | h
    · have := hgap hx hz hiS hkS h; rw [abs_le]; constructor <;> omega
    · have := hgap hz hx hkS hiS h; rw [abs_le]; constructor <;> omega
  have gjk : |j - k| ≤ 2 := by
    rcases lt_or_gt_of_ne hjk with h | h
    · have := hgap hy hz hjS hkS h; rw [abs_le]; constructor <;> omega
    · have := hgap hz hy hkS hjS h; rw [abs_le]; constructor <;> omega
  rw [abs_le] at gij gik gjk
  have key : ∀ s t : ℤ, s ≠ t → -2 ≤ s - t → s - t ≤ 2 →
      (q : ℤ) * s - q * t = q ∨ (q : ℤ) * s - q * t = -q ∨
        (q : ℤ) * s - q * t = 2 * q ∨ (q : ℤ) * s - q * t = -(2 * q) := by
    intro s t hst h1 h2
    have : s - t = 1 ∨ s - t = -1 ∨ s - t = 2 ∨ s - t = -2 := by omega
    rcases this with h | h | h | h
    · left; rw [← mul_sub, h, mul_one]
    · right; left; rw [← mul_sub, h]; ring
    · right; right; left; rw [← mul_sub, h]; ring
    · right; right; right; rw [← mul_sub, h]; ring
  intro p hp r hr hpr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hr
  rcases hp with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl
  · exact absurd rfl hpr
  · exact key i j hij (by omega) (by omega)
  · exact key i k hik (by omega) (by omega)
  · exact key j i hij.symm (by omega) (by omega)
  · exact absurd rfl hpr
  · exact key j k hjk (by omega) (by omega)
  · exact key k i hik.symm (by omega) (by omega)
  · exact key k j hjk.symm (by omega) (by omega)
  · exact absurd rfl hpr

end Erdos708.Five
