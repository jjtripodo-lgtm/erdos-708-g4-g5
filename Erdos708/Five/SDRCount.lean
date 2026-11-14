module

public import Erdos708.Five.SiteArith
public import Erdos708.ProperDivisorHall

@[expose] public section

/-!
# Counting multiples for the five-label proper-divisor lemma

* The candidate set `C s`: interval multiples of `s` other than the anchor.
* `|C s| ≥ M/s - 1` when the anchor is a multiple, and `|C s| ≤ M/s`.
* The proper multiples of `s` in `[1, M]` number at most `M/s - 1`.
-/

namespace Erdos708.Five

open Erdos708

/-- Interval multiples of `s` other than the anchor `x`. -/
def cand (L : ℤ) (M : ℕ) (x : ℤ) (s : ℕ) : Finset ℤ :=
  (integerInterval L M).filter fun z => z ≠ x ∧ (s : ℤ) ∣ z

/-- Proper multiples of `s` in `[1, M]`. -/
def propMult (M s : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter fun n => s ∣ n ∧ n ≠ s

theorem mem_cand {L x z : ℤ} {M s : ℕ} :
    z ∈ cand L M x s ↔ z ∈ integerInterval L M ∧ z ≠ x ∧ (s : ℤ) ∣ z := by
  simp [cand, and_assoc]

theorem card_multiples_le {L : ℤ} {M l : ℕ} (hl : 0 < l) :
    ((integerInterval L M).filter (fun z => (l : ℤ) ∣ z)).card ≤ M / l + 1 := by
  classical
  have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
  let g : ℤ → ℕ := fun z => ((z - L) / l).toNat
  have hmaps : ∀ z ∈ (integerInterval L M).filter (fun z => (l : ℤ) ∣ z),
      g z ∈ Finset.range (M / l + 1) := by
    intro z hz
    rw [Finset.mem_filter, mem_integerInterval] at hz
    rw [Finset.mem_range]
    have h0 : 0 ≤ z - L := by omega
    have h1 : z - L ≤ (M : ℤ) - 1 := by omega
    have hq : (z - L) / l ≤ ((M : ℤ)) / l := Int.ediv_le_ediv (by exact_mod_cast hl) (by omega)
    have hq0 : 0 ≤ (z - L) / l := Int.ediv_nonneg h0 (by exact_mod_cast hl.le)
    have hM : ((M : ℤ)) / l = ((M / l : ℕ) : ℤ) := by push_cast; rfl
    simp only [g]
    omega
  have hinj : Set.InjOn g ((integerInterval L M).filter (fun z => (l : ℤ) ∣ z)) := by
    intro z hz z' hz' hzz
    rw [Finset.coe_filter, Set.mem_setOf_eq, mem_integerInterval] at hz hz'
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hz
    obtain ⟨⟨h1', h2'⟩, k', rfl⟩ := hz'
    simp only [g] at hzz
    have e1 : ((l : ℤ) * k - L) / l = (-L) / l + k := by
      rw [show (l : ℤ) * k - L = -L + l * k by ring, Int.add_mul_ediv_left _ _ hl']
    have e2 : ((l : ℤ) * k' - L) / l = (-L) / l + k' := by
      rw [show (l : ℤ) * k' - L = -L + l * k' by ring, Int.add_mul_ediv_left _ _ hl']
    have n1 : 0 ≤ ((l : ℤ) * k - L) / l := Int.ediv_nonneg (by omega) (by exact_mod_cast hl.le)
    have n2 : 0 ≤ ((l : ℤ) * k' - L) / l := Int.ediv_nonneg (by omega) (by exact_mod_cast hl.le)
    have : ((l : ℤ) * k - L) / l = ((l : ℤ) * k' - L) / l := by omega
    rw [e1, e2] at this
    have hkk : k = k' := by omega
    rw [hkk]
  calc _ = (((integerInterval L M).filter (fun z => (l : ℤ) ∣ z)).image g).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (M / l + 1)).card :=
        Finset.card_le_card (fun y hy => by
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
          exact hmaps z hz)
    _ = M / l + 1 := Finset.card_range _

theorem card_cand_le {L x : ℤ} {M l : ℕ} (hl : 0 < l) (hx : x ∈ integerInterval L M)
    (hlx : (l : ℤ) ∣ x) : (cand L M x l).card ≤ M / l := by
  classical
  have hsub : insert x (cand L M x l) ⊆ (integerInterval L M).filter (fun z => (l : ℤ) ∣ z) := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rw [Finset.mem_filter]
    rcases hz with rfl | hz
    · exact ⟨hx, hlx⟩
    · rw [mem_cand] at hz; exact ⟨hz.1, hz.2.2⟩
  have hnot : x ∉ cand L M x l := by rw [mem_cand]; tauto
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at this
  have := card_multiples_le (L := L) (M := M) hl
  omega

theorem card_cand_ge {L x : ℤ} {M s : ℕ} (hs : 0 < s) (hx : x ∈ integerInterval L M)
    (hsx : (s : ℤ) ∣ x) (hsM : s ≤ M) : M / s - 1 ≤ (cand L M x s).card := by
  classical
  have hk : (M / s - 1 + 1) * s ≤ M := by
    have h1 : 1 ≤ M / s := (Nat.le_div_iff_mul_le hs).mpr (by omega)
    rw [Nat.sub_add_cancel h1]
    exact Nat.div_mul_le_self M s
  have hcard := card_interval_multiples_ge_of_known_multiple_candidate hs hx hsx hk
  have hsub : (integerInterval L M).filter (fun z => (s : ℤ) ∣ z) ⊆ insert x (cand L M x s) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_insert, mem_cand]
    by_cases h : z = x
    · left; exact h
    · right; exact ⟨hz.1, h, hz.2⟩
  have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  omega

theorem card_propMult_le {M s : ℕ} (hs : 0 < s) (hsM : s ≤ M) :
    (propMult M s).card ≤ M / s - 1 := by
  classical
  have hmult : ((Finset.Icc 1 M).filter (fun n => s ∣ n)).card = M / s := by
    have : Finset.Icc 1 M = Finset.Ioc 0 M := by ext n; simp; omega
    rw [this]; exact Nat.Ioc_filter_dvd_card_eq_div M s
  have hsub : insert s (propMult M s) ⊆ (Finset.Icc 1 M).filter (fun n => s ∣ n) := by
    intro n hn
    rw [Finset.mem_insert] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    rcases hn with rfl | hn
    · exact ⟨⟨hs, hsM⟩, dvd_rfl⟩
    · simp only [propMult, Finset.mem_filter, Finset.mem_Icc] at hn
      exact ⟨hn.1, hn.2.1⟩
  have hnot : s ∉ propMult M s := by simp [propMult]
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hmult] at this
  omega


section Primitive

variable {L x : ℤ} {M : ℕ}

theorem exists_side (hx : x ∈ integerInterval L M) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ n : ℕ, 2 * n ≤ M → x + σ * n ∈ integerInterval L M := by
  rw [mem_integerInterval] at hx
  by_cases h : x - L ≤ L + (M : ℤ) - 1 - x
  · refine ⟨1, Or.inl rfl, fun n hn => ?_⟩
    rw [mem_integerInterval]; constructor <;> push_cast <;> omega
  · refine ⟨-1, Or.inr rfl, fun n hn => ?_⟩
    rw [mem_integerInterval]; constructor <;> push_cast <;> omega

theorem between_mem {σ d e z : ℤ} (hσ : σ = 1 ∨ σ = -1) (hx : x ∈ integerInterval L M)
    (hz : z ∈ integerInterval L M) (hzd : z = x + σ * d)
    (he : (0 < e ∧ e ≤ d) ∨ (d ≤ e ∧ e < 0)) : x + σ * e ∈ integerInterval L M := by
  rw [mem_integerInterval] at hx hz ⊢
  rcases hσ with rfl | rfl <;> constructor <;> rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- **Full-union bound.** Let `R0` be a primitive set of positive labels at most `M/2`, all
dividing the anchor. If five distinct positive originals at most `M` are each a proper multiple
of some label, then the labels' off-anchor interval candidates have at least five points. -/
theorem five_le_card_union_of_primitive (hx : x ∈ integerInterval L M) (R0 : Finset ℕ)
    (hpos : ∀ s ∈ R0, 0 < s) (hhalf : ∀ s ∈ R0, 2 * s ≤ M)
    (hdiv : ∀ s ∈ R0, (s : ℤ) ∣ x) (hprim : ∀ s ∈ R0, ∀ t ∈ R0, s ∣ t → s = t)
    (A : Finset ℕ) (hA : A.card = 5) (hApos : ∀ a ∈ A, 0 < a)
    (hAcov : ∀ a ∈ A, a ≤ M ∧ ∃ s ∈ R0, s ∣ a ∧ a ≠ s) :
    5 ≤ (R0.biUnion (cand L M x)).card := by
  classical
  by_contra hU
  push Not at hU
  set U := R0.biUnion (cand L M x) with hUdef
  obtain ⟨σ, hσ, hside⟩ := exists_side hx
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hU_of : ∀ {s : ℕ} {z : ℤ}, s ∈ R0 → z ∈ cand L M x s → z ∈ U :=
    fun hs hz => Finset.mem_biUnion.mpr ⟨_, hs, hz⟩
  -- representatives on the long side
  let rep : ℤ → ℤ := fun n => x + σ * n
  have hrep_cand : ∀ {s : ℕ} {n : ℤ}, s ∈ R0 → n ≠ 0 → (s : ℤ) ∣ n →
      x + σ * n ∈ integerInterval L M → x + σ * n ∈ cand L M x s := by
    intro s n hs hn hsn hI
    rw [mem_cand]
    refine ⟨hI, fun h => ?_, dvd_add (hdiv s hs) (dvd_mul_of_dvd_right hsn _)⟩
    have : σ * n = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hσ0 h'
    · exact hn h'
  have hrepU : ∀ s ∈ R0, rep s ∈ U := by
    intro s hs
    have h0 := hpos s hs
    exact hU_of hs (hrep_cand hs (by exact_mod_cast h0.ne') dvd_rfl (hside s (hhalf s hs)))
  have hrep_inj : ∀ {m n : ℤ}, rep m = rep n → m = n := by
    intro m n h
    simp only [rep] at h
    exact mul_left_cancel₀ hσ0 (by linarith)
  set Rz := R0.image (fun s : ℕ => rep s) with hRz
  have hRU : Rz ⊆ U := fun z hz => by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz; exact hrepU s hs
  have hRcard : Rz.card = R0.card :=
    Finset.card_image_of_injOn (fun s _ t _ h => by exact_mod_cast hrep_inj h)
  have hR4 : R0.card ≤ 4 := by have := Finset.card_le_card hRU; omega
  have hoff : ∀ {s : ℕ} {z : ℤ}, s ∈ R0 → (s : ℤ) ∣ z → (s : ℤ) ∣ σ * (z - x) :=
    fun hs hz => dvd_mul_of_dvd_right (dvd_sub hz (hdiv _ hs)) _
  have hz_eq : ∀ z : ℤ, z = rep (σ * (z - x)) := by
    intro z; simp only [rep]; rw [← mul_assoc, hσσ]; ring
  have mem_Rz : ∀ {z : ℤ}, z ∈ Rz → ∃ w ∈ R0, σ * (z - x) = w := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    refine ⟨w, hw, ?_⟩
    simp only [rep]; rw [show x + σ * (w : ℤ) - x = σ * w by ring, ← mul_assoc, hσσ, one_mul]
  -- the originals are proper multiples
  have hApm : A ⊆ R0.biUnion (propMult M) := by
    intro a ha
    obtain ⟨haM, s, hs, hsa, hne⟩ := hAcov a ha
    refine Finset.mem_biUnion.mpr ⟨s, hs, ?_⟩
    simp only [propMult, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hApos a ha, haM⟩, hsa, hne⟩
  have hA5 : 5 ≤ (R0.biUnion (propMult M)).card := hA ▸ Finset.card_le_card hApm
  have hper : ∀ s ∈ R0, (propMult M s).card ≤ (cand L M x s).card := fun s hs =>
    (card_propMult_le (hpos s hs) (by have := hhalf s hs; have := hpos s hs; omega)).trans
      (card_cand_ge (hpos s hs) hx (hdiv s hs) (by have := hhalf s hs; omega))
  -- disjoint candidate families give the contradiction
  have disj : (↑R0 : Set ℕ).PairwiseDisjoint (cand L M x) → False := by
    intro hd
    have h1 := Finset.card_biUnion hd
    have h2 : (R0.biUnion (propMult M)).card ≤ ∑ s ∈ R0, (propMult M s).card :=
      Finset.card_biUnion_le
    have h3 : ∑ s ∈ R0, (propMult M s).card ≤ ∑ s ∈ R0, (cand L M x s).card :=
      Finset.sum_le_sum hper
    rw [← hUdef] at h1
    omega
  -- five points of `U` give a contradiction
  have five : ∀ p q : ℤ, p ∈ U → q ∈ U → p ∉ Rz → q ∉ Rz → p ≠ q → R0.card = 3 → False := by
    intro p q hp hq hpR hqR hpq h3
    have hsub : insert p (insert q Rz) ⊆ U := by
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact hp
      · exact hq
      · exact hRU hz
    have hcard : (insert p (insert q Rz)).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [hpq, hpR]), Finset.card_insert_of_notMem hqR,
        hRcard, h3]
    have := Finset.card_le_card hsub
    omega
  have hcases : R0.card ≤ 1 ∨ R0.card = 2 ∨ R0.card = 3 ∨ R0.card = 4 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · apply disj
    intro s hs t ht hst
    exact absurd (Finset.card_le_one.mp h1 s hs t ht) hst
  · -- two primitive labels: inclusion–exclusion
    obtain ⟨s, t, hst, hR⟩ := Finset.card_eq_two.mp h2
    have hs : s ∈ R0 := by rw [hR]; simp
    have ht : t ∈ R0 := by rw [hR]; simp
    have hs0 := hpos s hs
    have ht0 := hpos t ht
    set l := Nat.lcm s t with hl
    have hl0 : 0 < l := Nat.lcm_pos hs0 ht0
    have hls : s < l := by
      have hsl : s ∣ l := Nat.dvd_lcm_left s t
      rcases (Nat.le_of_dvd hl0 hsl).lt_or_eq with h | h
      · exact h
      · exfalso; exact hst (hprim t ht s hs (h ▸ Nat.dvd_lcm_right s t)).symm
    have hlt : t < l := by
      have htl : t ∣ l := Nat.dvd_lcm_right s t
      rcases (Nat.le_of_dvd hl0 htl).lt_or_eq with h | h
      · exact h
      · exfalso; exact hst (hprim s hs t ht (h ▸ Nat.dvd_lcm_left s t))
    have hUst : U = cand L M x s ∪ cand L M x t := by
      rw [hUdef, hR, Finset.biUnion_insert, Finset.singleton_biUnion]
    have hCi : cand L M x s ∩ cand L M x t = cand L M x l := by
      ext z
      simp only [Finset.mem_inter, mem_cand]
      have : ((l : ℕ) : ℤ) ∣ z ↔ (s : ℤ) ∣ z ∧ (t : ℤ) ∣ z := by
        simp [hl, Int.natCast_dvd, Nat.lcm_dvd_iff]
      rw [this]; tauto
    have hlx : (l : ℤ) ∣ x := int_lcm_dvd (hdiv s hs) (hdiv t ht)
    have hCl := card_cand_le (L := L) (M := M) hl0 hx hlx
    have hPi : (Finset.Icc 1 M).filter (fun n => l ∣ n) ⊆ propMult M s ∩ propMult M t := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnM⟩, hln⟩ := hn
      have hnl : l ≤ n := Nat.le_of_dvd (by omega) hln
      simp only [Finset.mem_inter, propMult, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hn1, hnM⟩, (Nat.dvd_lcm_left s t).trans hln, by omega⟩,
        ⟨⟨hn1, hnM⟩, (Nat.dvd_lcm_right s t).trans hln, by omega⟩⟩
    have hPl : ((Finset.Icc 1 M).filter (fun n => l ∣ n)).card = M / l := by
      have : Finset.Icc 1 M = Finset.Ioc 0 M := by ext n; simp; omega
      rw [this]; exact Nat.Ioc_filter_dvd_card_eq_div M l
    have hPi' := Finset.card_le_card hPi
    have hPU : R0.biUnion (propMult M) = propMult M s ∪ propMult M t := by
      rw [hR, Finset.biUnion_insert, Finset.singleton_biUnion]
    have e1 := Finset.card_union_add_card_inter (propMult M s) (propMult M t)
    have e2 := Finset.card_union_add_card_inter (cand L M x s) (cand L M x t)
    rw [hCi] at e2
    rw [hPU] at hA5
    have p1 := hper s hs
    have p2 := hper t ht
    rw [hUst] at hU
    omega
  · -- three primitive labels: candidate families are disjoint
    apply disj
    intro s hs t ht hst
    rw [Function.onFun, Finset.disjoint_left]
    intro z hzs hzt
    rw [Finset.mem_coe] at hs ht
    have hzs' := hzs
    rw [mem_cand] at hzs hzt
    obtain ⟨hzI, hzx, hsz⟩ := hzs
    obtain ⟨-, -, htz⟩ := hzt
    set d := σ * (z - x) with hd
    have hzd : z = x + σ * d := hz_eq z
    have hd0 : d ≠ 0 := by
      intro h; rw [h, mul_zero, add_zero] at hzd; exact hzx hzd
    have hsd := hoff hs hsz
    have htd := hoff ht htz
    have hs0 := hpos s hs
    have ht0 := hpos t ht
    have hs0' : (0 : ℤ) < s := by exact_mod_cast hs0
    have ht0' : (0 : ℤ) < t := by exact_mod_cast ht0
    rcases lt_or_gt_of_ne hd0 with hneg | hposd
    · -- negative side: `-s` and `-t` are two further candidates
      obtain ⟨α, hα⟩ := hsd
      obtain ⟨β, hβ⟩ := htd
      have hα' : α ≤ -1 := by by_contra h; push Not at h; nlinarith
      have hβ' : β ≤ -1 := by by_contra h; push Not at h; nlinarith
      have hp1 : x + σ * (-(s : ℤ)) ∈ U := hU_of hs (hrep_cand hs (by omega) (dvd_neg.mpr dvd_rfl)
        (between_mem hσ hx hzI hzd (Or.inr ⟨by nlinarith, by omega⟩)))
      have hp2 : x + σ * (-(t : ℤ)) ∈ U := hU_of ht (hrep_cand ht (by omega) (dvd_neg.mpr dvd_rfl)
        (between_mem hσ hx hzI hzd (Or.inr ⟨by nlinarith, by omega⟩)))
      have notR : ∀ {n : ℕ}, 0 < n → x + σ * (-(n : ℤ)) ∉ Rz := by
        intro n hn hmem
        obtain ⟨w, -, hw⟩ := mem_Rz hmem
        rw [show x + σ * (-(n : ℤ)) - x = σ * (-(n : ℤ)) by ring, ← mul_assoc, hσσ,
          one_mul] at hw
        have : (0 : ℤ) ≤ w := by positivity
        omega
      exact five _ _ hp1 hp2 (notR hs0) (notR ht0)
        (fun h => hst (by have := hrep_inj h; omega)) h3
    · -- positive side
      obtain ⟨α, hα⟩ := hsd
      obtain ⟨β, hβ⟩ := htd
      have hα1 : 1 ≤ α := by by_contra h; push Not at h; nlinarith
      have hβ1 : 1 ≤ β := by by_contra h; push Not at h; nlinarith
      have hα2 : 2 ≤ α := by
        by_contra h
        have : α = 1 := by omega
        subst this
        have htsI : (t : ℤ) ∣ s := ⟨β, by linarith⟩
        exact hst (hprim t ht s hs (by exact_mod_cast htsI)).symm
      have hβ2 : 2 ≤ β := by
        by_contra h
        have : β = 1 := by omega
        subst this
        have hstI : (s : ℤ) ∣ t := ⟨α, by linarith⟩
        exact hst (hprim s hs t ht (by exact_mod_cast hstI))
      have hzU : z ∈ U := hU_of hs hzs'
      -- a label with quotient at least three supplies its double
      have dbl : ∀ {u : ℕ} {γ : ℤ}, u ∈ R0 → 0 < u → d = u * γ → 3 ≤ γ → False := by
        intro u γ hu hu0 hγ h3γ
        have hu0' : (0 : ℤ) < u := by exact_mod_cast hu0
        have hq : x + σ * (2 * (u : ℤ)) ∈ U := hU_of hu (hrep_cand hu (by omega)
          (dvd_mul_left _ _) (between_mem hσ hx hzI hzd (Or.inl ⟨by omega, by nlinarith⟩)))
        have hqR : x + σ * (2 * (u : ℤ)) ∉ Rz := by
          intro hmem
          obtain ⟨w, hw, hw'⟩ := mem_Rz hmem
          rw [show x + σ * (2 * (u : ℤ)) - x = σ * (2 * u) by ring, ← mul_assoc, hσσ,
            one_mul] at hw'
          have huw : u ∣ w := by
            have : (u : ℤ) ∣ w := ⟨2, by linarith⟩
            exact_mod_cast this
          have := hprim u hu w hw huw
          omega
        have hzR : z ∉ Rz := by
          intro hmem
          obtain ⟨w, hw, hw'⟩ := mem_Rz hmem
          have huw : u ∣ w := by
            have : (u : ℤ) ∣ w := ⟨γ, by rw [← hw', ← hd, hγ]⟩
            exact_mod_cast this
          have := hprim u hu w hw huw
          have : (w : ℤ) = u := by exact_mod_cast this.symm
          nlinarith
        exact five _ _ hq hzU hqR hzR (fun h => by
          have := hrep_inj (h.trans (hz_eq z))
          nlinarith) h3
      by_cases h3α : 3 ≤ α
      · exact dbl hs hs0 hα h3α
      · have hα2' : α = 2 := by omega
        have h3β : 3 ≤ β := by
          by_contra h
          have : β = 2 := by omega
          subst this; subst hα2'
          exact hst (by have : (s : ℤ) = t := by linarith
                        exact_mod_cast this)
        exact dbl ht ht0 hβ h3β
  · -- four primitive labels: candidates are exactly the representatives
    have hEq : Rz = U := Finset.eq_of_subset_of_card_le hRU (by omega)
    apply disj
    intro s hs t ht hst
    rw [Function.onFun, Finset.disjoint_left]
    intro z hzs hzt
    rw [Finset.mem_coe] at hs ht
    have hzU : z ∈ U := hU_of hs hzs
    rw [← hEq] at hzU
    obtain ⟨w, hw, hw'⟩ := mem_Rz hzU
    rw [mem_cand] at hzs hzt
    have h1 : s ∣ w := by
      have := hoff hs hzs.2.2; rw [hw'] at this; exact_mod_cast this
    have h2 : t ∣ w := by
      have := hoff ht hzt.2.2; rw [hw'] at this; exact_mod_cast this
    exact hst ((hprim s hs w hw h1).trans (hprim t ht w hw h2).symm)

end Primitive

end Erdos708.Five
