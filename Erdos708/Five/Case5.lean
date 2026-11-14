module

public import Erdos708.Five.SDR5
public import Erdos708.Five.Shapes
public import Erdos708.PrimeUnitsRaw
public import Erdos708.PrimeUnitProduct
public import Erdos708.PrimeResiduals
public import Erdos708.SmallAntichainUnion

@[expose] public section

/-!
# Five pairwise incomparable originals at a common anchor

Source: `FIVE_COMMON_ANCHOR.md`. Assign distinct prime units by Hall's theorem. For subfamilies
of at most four this holds by the small-antichain union bound; for the full family it holds when
the units number at least five. The residuals then have five distinct off-anchor representatives
(`proper_divisor_sdr_fin_five`). The only failure, four units in all, is the exceptional
squarefree family; it is handled separately.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

section

variable {L x : ℤ} {M : ℕ}

/-- Units of each original lie among the units of the lcm. -/
theorem rawPrimeUnits_subset_lcm {m : Fin 5 → ℕ} (hm : ∀ i, m i ≠ 0) (i : Fin 5) :
    rawPrimeUnits (m i) ⊆ rawPrimeUnits (Finset.univ.lcm m) :=
  (rawPrimeUnits_subset_iff_dvd_candidate (hm i)
    (by rw [Ne, Finset.lcm_eq_zero_iff]; push Not; intro j _; exact hm j)).mpr
    (Finset.dvd_lcm (Finset.mem_univ i))

theorem lcm_dvd_anchor {m : Fin 5 → ℕ} (hdiv : ∀ i, (m i : ℤ) ∣ x) :
    ((Finset.univ.lcm m : ℕ) : ℤ) ∣ x :=
  Int.natCast_dvd.mpr (Finset.lcm_dvd (fun i _ => Int.natCast_dvd.mp (hdiv i)))

/-- The regular branch: at least five prime units in total. -/
theorem case5_regular (m : Fin 5 → ℕ) (hm2 : ∀ i, 2 ≤ m i) (hinj : Function.Injective m)
    (hle : ∀ i, m i ≤ M) (hx : x ∈ integerInterval L M) (hdiv : ∀ i, (m i : ℤ) ∣ x)
    (hinc : ∀ i j, i ≠ j → ¬ m i ∣ m j)
    (hU : 5 ≤ (Finset.univ.biUnion (fun i => rawPrimeUnits (m i))).card) :
    ProdCover L M (∏ i, m i) 6 := by
  classical
  have hm0 : ∀ i, m i ≠ 0 := fun i => by have := hm2 i; omega
  let C : Fin 5 → Finset RawPrimeUnit := fun i => rawPrimeUnits (m i)
  have hhall : ∀ S : Finset (Fin 5), S.card ≤ (S.biUnion C).card := by
    intro S
    by_cases hS : S.card ≤ 4
    · exact small_pairwise_incomparable_biUnion_card_candidate S C hS
        (fun i _ => rawPrimeUnits_nonempty_candidate (by have := hm2 i; omega))
        (fun i _ j _ hij hsub => hinc i j hij
          ((rawPrimeUnits_subset_iff_dvd_candidate (hm0 i) (hm0 j)).mp hsub))
    · have hSu : S = Finset.univ := Finset.eq_univ_of_card _
        (by have := Finset.card_le_univ S; simp at this ⊢; omega)
      subst hSu
      simpa using hU
  obtain ⟨u, hu, huC⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective C).mp hhall
  let p : Fin 5 → ℕ := selectedPrime u
  let r : Fin 5 → ℕ := selectedResidual m u
  obtain ⟨b, hb, hbC⟩ := proper_divisor_sdr_fin_five (L := L) (x := x) (M := M) m r
    (fun i => by have := hm2 i; omega) hinj
    (fun i => selectedResidual_pos_candidate (by have := hm2 i; omega) (huC i))
    (fun i => selectedResidual_dvd_candidate (huC i))
    (fun i => selectedResidual_proper_candidate (by have := hm2 i; omega) (huC i)) hle hx
    (fun i => selectedResidual_dvd_anchor_candidate (huC i) (hdiv i))
  -- the selected primes divide the lcm, hence the anchor
  have hpL : (∏ i, p i) ∣ Finset.univ.lcm m := by
    have hsub : Finset.univ.image u ⊆ rawPrimeUnits (Finset.univ.lcm m) := by
      intro w hw
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
      exact rawPrimeUnits_subset_lcm hm0 i (huC i)
    have h := prod_rawPrimeUnits_subset_dvd_candidate
      (by rw [Ne, Finset.lcm_eq_zero_iff]; push Not; intro j _; exact hm0 j) _ hsub
    rwa [Finset.prod_image (fun i _ j _ h => hu h)] at h
  have hpx : ((∏ i, p i : ℕ) : ℤ) ∣ x :=
    (Int.natCast_dvd_natCast.mpr hpL).trans (lcm_dvd_anchor hdiv)
  have hbx : ∀ i, b i ≠ x := fun i => by
    have := hbC i; rw [properDivisorCandidates_eq_cand, mem_cand] at this; exact this.2.1
  have hxB : x ∉ Finset.univ.image b := by
    intro h; obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h; exact hbx i hi
  refine ⟨insert x (Finset.univ.image b), ?_, ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact hx
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      have := hbC i; rw [properDivisorCandidates_eq_cand, mem_cand] at this; exact this.1
  · rw [Finset.card_insert_of_notMem hxB, Finset.card_image_of_injective _ hb]; simp
  · rw [Finset.prod_insert hxB, Finset.prod_image (fun i _ j _ h => hb h)]
    have hrb : ((∏ i, r i : ℕ) : ℤ) ∣ ∏ i, b i := by
      push_cast
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => by
        have := hbC i; rw [properDivisorCandidates_eq_cand, mem_cand] at this; exact this.2.2)
    have hprod : ∏ i, m i = (∏ i, p i) * ∏ i, r i :=
      (selectedPrime_prod_mul_residual_prod_candidate m u huC).symm
    rw [hprod]
    push_cast
    exact mul_dvd_mul (by exact_mod_cast hpx) (by exact_mod_cast hrb)

end


section Antichain

variable {α : Type*} [DecidableEq α]

/-- Five nonempty pairwise incomparable sets inside a ground set of at most four elements are
two-element sets, and the ground set has exactly four elements. -/
theorem antichain_five_in_four (C : Fin 5 → Finset α) (hne : ∀ i, (C i).Nonempty)
    (hinc : ∀ i j, i ≠ j → ¬ C i ⊆ C j) (hW : (Finset.univ.biUnion C).card ≤ 4) :
    (Finset.univ.biUnion C).card = 4 ∧ ∀ i, (C i).card = 2 := by
  classical
  set W := Finset.univ.biUnion C with hWdef
  have hCW : ∀ i, C i ⊆ W := fun i => Finset.subset_biUnion_of_mem C (Finset.mem_univ i)
  have hS4 : ∀ i : Fin 5, (Finset.univ.erase i).card = 4 := fun i => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
  -- no singleton
  have no1 : ∀ i, (C i).card ≠ 1 := by
    intro i h1
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
    have hsub : (Finset.univ.erase i).biUnion C ⊆ W.erase w := by
      intro y hy
      obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp hy
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [Finset.mem_erase]
      refine ⟨fun hyw => hinc i j (Ne.symm hji) ?_, hCW j hyj⟩
      rw [hw, Finset.singleton_subset_iff, ← hyw]; exact hyj
    have hcard := small_pairwise_incomparable_biUnion_card_candidate (Finset.univ.erase i) C
      (by rw [hS4]) (fun j _ => hne j) (fun j _ k _ hjk => hinc j k hjk)
    have := Finset.card_le_card hsub
    have hwW : w ∈ W := hCW i (by rw [hw]; simp)
    rw [Finset.card_erase_of_mem hwW] at this
    rw [hS4] at hcard
    omega
  -- no set of size at least three
  have no3 : ∀ i, (C i).card < 3 := by
    intro i
    by_contra hge
    push Not at hge
    have hdiff : (W \ C i).card ≤ 1 := by
      have := Finset.card_sdiff_add_card_eq_card (hCW i); omega
    have hout : ∀ j, j ≠ i → ∃ y ∈ C j, y ∉ C i := by
      intro j hji
      by_contra h; push Not at h
      exact hinc j i hji h
    obtain ⟨j₀, hj₀⟩ : ∃ j : Fin 5, j ≠ i := by
      by_cases h0 : i = 0
      · exact ⟨1, by rw [h0]; decide⟩
      · exact ⟨0, fun e => h0 e.symm⟩
    obtain ⟨w, hwj, hwi⟩ := hout j₀ hj₀
    have hWd : W \ C i = {w} := by
      have hwmem : w ∈ W \ C i := Finset.mem_sdiff.mpr ⟨hCW j₀ hwj, hwi⟩
      exact (Finset.eq_singleton_iff_unique_mem.mpr ⟨hwmem, fun y hy =>
        Finset.card_le_one.mp hdiff y hy w hwmem⟩)
    have hwall : ∀ j, j ≠ i → w ∈ C j := by
      intro j hji
      obtain ⟨y, hyj, hyi⟩ := hout j hji
      have : y ∈ W \ C i := Finset.mem_sdiff.mpr ⟨hCW j hyj, hyi⟩
      rw [hWd, Finset.mem_singleton] at this
      exact this ▸ hyj
    let D : Fin 5 → Finset α := fun j => (C j).erase w
    have hsub : (Finset.univ.erase i).biUnion D ⊆ W.erase w := by
      intro y hy
      obtain ⟨j, -, hyj⟩ := Finset.mem_biUnion.mp hy
      rw [Finset.mem_erase] at hyj ⊢
      exact ⟨hyj.1, hCW j hyj.2⟩
    have hDne : ∀ j ∈ Finset.univ.erase i, (D j).Nonempty := by
      intro j hj
      have hji := Finset.ne_of_mem_erase hj
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have : C j = {w} := by
        ext y; constructor
        · intro hy
          by_contra hyw
          rw [Finset.mem_singleton] at hyw
          have : y ∈ D j := Finset.mem_erase.mpr ⟨hyw, hy⟩
          rw [hemp] at this; simp at this
        · intro hy; rw [Finset.mem_singleton] at hy; rw [hy]; exact hwall j hji
      exact no1 j (by rw [this]; simp)
    have hDinc : ∀ j ∈ Finset.univ.erase i, ∀ k ∈ Finset.univ.erase i, j ≠ k →
        ¬ D j ⊆ D k := by
      intro j hj k hk hjk hsub'
      apply hinc j k hjk
      intro y hy
      by_cases hyw : y = w
      · rw [hyw]; exact hwall k (Finset.ne_of_mem_erase hk)
      · exact (Finset.mem_erase.mp (hsub' (Finset.mem_erase.mpr ⟨hyw, hy⟩))).2
    have hcard := small_pairwise_incomparable_biUnion_card_candidate (Finset.univ.erase i) D
      (by rw [hS4]) hDne hDinc
    have := Finset.card_le_card hsub
    have hwW : w ∈ W := hCW j₀ hwj
    rw [Finset.card_erase_of_mem hwW] at this
    rw [hS4] at hcard
    omega
  have h2 : ∀ i, (C i).card = 2 := by
    intro i
    have := (hne i).card_pos
    have := no1 i
    have := no3 i
    omega
  refine ⟨?_, h2⟩
  by_contra h4
  have hW3 : W.card ≤ 3 := by omega
  have hCinj : Function.Injective C := fun i j h => by
    by_contra hij; exact hinc i j hij (h ▸ subset_refl _)
  have hsub : Finset.univ.image C ⊆ W.powersetCard 2 := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_powersetCard.mpr ⟨hCW i, h2 i⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hCinj, Finset.card_powersetCard] at this
  simp at this
  interval_cases hw : W.card <;> simp_all <;> omega

/-- In a family of five distinct two-element subsets of a four-element set, every element lies
in at least two members. -/
theorem two_le_degree (C : Fin 5 → Finset α) (hCinj : Function.Injective C)
    (W : Finset α) (hW : W.card = 4) (hC : ∀ i, C i ⊆ W ∧ (C i).card = 2) {w : α}
    (hw : w ∈ W) : 2 ≤ (Finset.univ.filter (fun i => w ∈ C i)).card := by
  classical
  set F := Finset.univ.image C with hF
  have hFcard : F.card = 5 := by rw [hF, Finset.card_image_of_injective _ hCinj]; simp
  have hFsub : F ⊆ W.powersetCard 2 := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_powersetCard.mpr (hC i)
  have hP : (W.powersetCard 2).card = 6 := by rw [Finset.card_powersetCard, hW]; rfl
  set Pw := (W.erase w).image (fun v => ({w, v} : Finset α)) with hPw
  have hPwcard : Pw.card = 3 := by
    rw [hPw, Finset.card_image_of_injOn]
    · rw [Finset.card_erase_of_mem hw, hW]
    · intro v hv v' hv' h
      simp only at h
      have hv1 : v ≠ w := Finset.ne_of_mem_erase hv
      have : v ∈ ({w, v'} : Finset α) := h ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'
      · exact absurd h' hv1
      · exact h'
  have hPwsub : Pw ⊆ W.powersetCard 2 := by
    intro t ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hw
      · exact Finset.mem_of_mem_erase hv
    · rw [Finset.card_pair (Ne.symm (Finset.ne_of_mem_erase hv))]
  -- at most one pair is missing from `F`
  have hmiss : (Pw \ F).card ≤ 1 := by
    have h1 : Pw \ F ⊆ W.powersetCard 2 \ F := Finset.sdiff_subset_sdiff hPwsub (subset_refl F)
    have h2 := Finset.card_sdiff_add_card_eq_card hFsub
    have := Finset.card_le_card h1
    omega
  have hinter : 2 ≤ (Pw ∩ F).card := by
    have := Finset.card_sdiff_add_card_inter Pw F
    omega
  -- each pair of `Pw ∩ F` comes from an index whose set contains `w`
  have hle : (Pw ∩ F).card ≤ (Finset.univ.filter (fun i => w ∈ C i)).card := by
    have hsub : Pw ∩ F ⊆ (Finset.univ.filter (fun i => w ∈ C i)).image C := by
      intro t ht
      rw [Finset.mem_inter] at ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht.2
      obtain ⟨v, -, hv⟩ := Finset.mem_image.mp ht.1
      refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [← hv]; simp⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  omega

end Antichain


section Exceptional

set_option maxHeartbeats 400000 in
/-- With at most four prime units in total, the five originals are five of the six products of
two among four distinct primes. -/
theorem exceptional_structure (m : Fin 5 → ℕ) (hm2 : ∀ i, 2 ≤ m i)
    (hinc : ∀ i j, i ≠ j → ¬ m i ∣ m j)
    (hW : (Finset.univ.biUnion (fun i => rawPrimeUnits (m i))).card ≤ 4) :
    ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
      p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
      ∃ j₁ j₂ j₃ j₄ j₅ : Fin 5, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₁ ≠ j₄ ∧ j₁ ≠ j₅ ∧ j₂ ≠ j₃ ∧
        j₂ ≠ j₄ ∧ j₂ ≠ j₅ ∧ j₃ ≠ j₄ ∧ j₃ ≠ j₅ ∧ j₄ ≠ j₅ ∧
        m j₁ = p * q ∧ m j₂ = p * r ∧ m j₃ = p * s ∧ m j₄ = q * r ∧ m j₅ = q * s := by
  classical
  have hm0 : ∀ i, m i ≠ 0 := fun i => by have := hm2 i; omega
  set C : Fin 5 → Finset RawPrimeUnit := fun i => rawPrimeUnits (m i) with hCdef
  have hne : ∀ i, (C i).Nonempty := fun i => rawPrimeUnits_nonempty_candidate (by
    have := hm2 i; omega)
  have hincC : ∀ i j, i ≠ j → ¬ C i ⊆ C j := fun i j hij hsub =>
    hinc i j hij ((rawPrimeUnits_subset_iff_dvd_candidate (hm0 i) (hm0 j)).mp hsub)
  obtain ⟨hW4, hC2⟩ := antichain_five_in_four C hne hincC hW
  set W := Finset.univ.biUnion C with hWdef
  have hCW : ∀ i, C i ⊆ W := fun i => Finset.subset_biUnion_of_mem C (Finset.mem_univ i)
  have hCinj : Function.Injective C := fun i j h => by
    by_contra hij; exact hincC i j hij (h ▸ subset_refl _)
  -- every unit of `W` has slot zero
  have slot0 : ∀ u ∈ W, u.2 = 0 := by
    intro u hu
    by_contra hj
    have hdeg := two_le_degree C hCinj W hW4 (fun i => ⟨hCW i, hC2 i⟩) hu
    have hforce : ∀ i, u ∈ C i → C i = {(u.1, 0), u} := by
      intro i hui
      have h0 : (u.1, 0) ∈ C i := by
        have := hui
        simp only [hCdef] at this ⊢
        rw [show u = (u.1, u.2) from rfl, mem_rawPrimeUnits_candidate] at this
        rw [mem_rawPrimeUnits_candidate]
        exact ⟨this.1, by omega⟩
      have hne' : (u.1, 0) ≠ u := by intro h; rw [← h] at hj; exact hj rfl
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact h0
        · exact hui
      · rw [hC2 i, Finset.card_pair hne']
    obtain ⟨i, hi, i', hi', hii'⟩ := Finset.one_lt_card.mp (by omega : 1 <
      (Finset.univ.filter (fun i => u ∈ C i)).card)
    rw [Finset.mem_filter] at hi hi'
    exact hii' (hCinj ((hforce i hi.2).trans (hforce i' hi'.2).symm))
  -- each original is a product of two distinct primes from `W`
  have hpair : ∀ i, ∃ α β : ℕ, α.Prime ∧ β.Prime ∧ α ≠ β ∧ C i = {(α, 0), (β, 0)} ∧
      m i = α * β := by
    intro i
    obtain ⟨u, v, huv, hCi⟩ := Finset.card_eq_two.mp (hC2 i)
    have hu0 : u.2 = 0 := slot0 u (hCW i (by rw [hCi]; simp))
    have hv0 : v.2 = 0 := slot0 v (hCW i (by rw [hCi]; simp))
    have hu : u = (u.1, 0) := Prod.ext rfl hu0
    have hv : v = (v.1, 0) := Prod.ext rfl hv0
    have hup : u.1.Prime := by
      have := (show u ∈ rawPrimeUnits (m i) by rw [show rawPrimeUnits (m i) = C i from rfl, hCi]; simp)
      rw [hu, mem_rawPrimeUnits_candidate] at this
      exact (Nat.mem_primeFactors.mp this.1).1
    have hvp : v.1.Prime := by
      have := (show v ∈ rawPrimeUnits (m i) by rw [show rawPrimeUnits (m i) = C i from rfl, hCi]; simp)
      rw [hv, mem_rawPrimeUnits_candidate] at this
      exact (Nat.mem_primeFactors.mp this.1).1
    have hne1 : u.1 ≠ v.1 := by
      intro h; apply huv; rw [hu, hv, h]
    refine ⟨u.1, v.1, hup, hvp, hne1, by rw [hCi, ← hu, ← hv], ?_⟩
    have := prod_rawPrimeUnits_fst_candidate (hm0 i)
    rw [show rawPrimeUnits (m i) = C i from rfl, hCi, Finset.prod_pair huv] at this
    exact this.symm
  -- the missing pair
  set F := Finset.univ.image C with hF
  have hFcard : F.card = 5 := by rw [hF, Finset.card_image_of_injective _ hCinj]; simp
  have hFsub : F ⊆ W.powersetCard 2 := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_powersetCard.mpr ⟨hCW i, hC2 i⟩
  have hP6 : (W.powersetCard 2).card = 6 := by rw [Finset.card_powersetCard, hW4]; rfl
  obtain ⟨e₀, he₀⟩ : (W.powersetCard 2 \ F).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.card_sdiff_add_card_eq_card hFsub
    omega
  rw [Finset.mem_sdiff, Finset.mem_powersetCard] at he₀
  obtain ⟨⟨he₀W, he₀2⟩, he₀F⟩ := he₀
  have hrest : (W \ e₀).card = 2 := by
    have := Finset.card_sdiff_add_card_eq_card he₀W; omega
  obtain ⟨u₁, u₂, hu12, hre⟩ := Finset.card_eq_two.mp hrest
  obtain ⟨u₃, u₄, hu34, he₀'⟩ := Finset.card_eq_two.mp he₀2
  have hu1 : u₁ ∈ W ∧ u₁ ∉ e₀ := Finset.mem_sdiff.mp (by rw [hre]; simp)
  have hu2 : u₂ ∈ W ∧ u₂ ∉ e₀ := Finset.mem_sdiff.mp (by rw [hre]; simp)
  have hu3 : u₃ ∈ W := he₀W (by rw [he₀']; simp)
  have hu4 : u₄ ∈ W := he₀W (by rw [he₀']; simp)
  have h13 : u₁ ≠ u₃ := fun h => hu1.2 (by rw [h, he₀']; simp)
  have h14 : u₁ ≠ u₄ := fun h => hu1.2 (by rw [h, he₀']; simp)
  have h23 : u₂ ≠ u₃ := fun h => hu2.2 (by rw [h, he₀']; simp)
  have h24 : u₂ ≠ u₄ := fun h => hu2.2 (by rw [h, he₀']; simp)
  -- a pair other than the missing one is some `C j`
  have hit : ∀ {v w : RawPrimeUnit}, v ∈ W → w ∈ W → v ≠ w → v ∉ e₀ →
      ∃ j, C j = {v, w} := by
    intro v w hv hw hvw hve
    have hmem : ({v, w} : Finset RawPrimeUnit) ∈ W.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair hvw⟩
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> assumption
    have hne0 : ({v, w} : Finset RawPrimeUnit) ≠ e₀ := fun h => hve (by rw [← h]; simp)
    have hnotin : ({v, w} : Finset RawPrimeUnit) ∈ F := by
      by_contra hF'
      -- then two pairs would be missing
      have hsub2 : ({e₀, {v, w}} : Finset (Finset RawPrimeUnit)) ⊆ W.powersetCard 2 \ F := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨he₀W, he₀2⟩, he₀F⟩
        · exact Finset.mem_sdiff.mpr ⟨hmem, hF'⟩
      have := Finset.card_le_card hsub2
      rw [Finset.card_pair (Ne.symm hne0)] at this
      have := Finset.card_sdiff_add_card_eq_card hFsub
      omega
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hnotin
    exact ⟨j, hj⟩
  have hsym : ∀ {v w : RawPrimeUnit}, ({v, w} : Finset RawPrimeUnit) = {w, v} :=
    Finset.pair_comm _ _
  obtain ⟨j₁, hj₁⟩ := hit hu1.1 hu2.1 hu12 hu1.2
  obtain ⟨j₂, hj₂⟩ := hit hu1.1 hu3 h13 hu1.2
  obtain ⟨j₃, hj₃⟩ := hit hu1.1 hu4 h14 hu1.2
  obtain ⟨j₄, hj₄⟩ := hit hu2.1 hu3 h23 hu2.2
  obtain ⟨j₅, hj₅⟩ := hit hu2.1 hu4 h24 hu2.2
  -- the units are prime units with slot zero
  have prm : ∀ {u : RawPrimeUnit}, u ∈ W → u = (u.1, 0) ∧ u.1.Prime := by
    intro u hu
    refine ⟨Prod.ext rfl (slot0 u hu), ?_⟩
    obtain ⟨i, -, hui⟩ := Finset.mem_biUnion.mp hu
    have := hui
    simp only [hCdef] at this
    rw [show u = (u.1, u.2) from rfl, mem_rawPrimeUnits_candidate] at this
    exact (Nat.mem_primeFactors.mp this.1).1
  obtain ⟨e1, p1⟩ := prm hu1.1
  obtain ⟨e2, p2⟩ := prm hu2.1
  obtain ⟨e3, p3⟩ := prm hu3
  obtain ⟨e4, p4⟩ := prm hu4
  have nep : ∀ {v w : RawPrimeUnit}, v = (v.1, 0) → w = (w.1, 0) → v ≠ w → v.1 ≠ w.1 := by
    intro v w hv hw hvw h; apply hvw; rw [hv, hw, h]
  have val : ∀ {j : Fin 5} {v w : RawPrimeUnit}, C j = {v, w} → v ≠ w → m j = v.1 * w.1 := by
    intro j v w hj hvw
    have := prod_rawPrimeUnits_fst_candidate (hm0 j)
    rw [show rawPrimeUnits (m j) = C j from rfl, hj, Finset.prod_pair hvw] at this
    exact this.symm
  have jne : ∀ {j j' : Fin 5} {t t' : Finset RawPrimeUnit}, C j = t → C j' = t' → t ≠ t' →
      j ≠ j' := by
    intro j j' t t' h h' htt e; rw [e] at h; exact htt (h.symm.trans h')
  have pne : ∀ {a b c d : RawPrimeUnit}, a ≠ c → a ≠ d → ({a, b} : Finset RawPrimeUnit) ≠ {c, d} :=
    by intro a b c d hac had h; have : a ∈ ({c, d} : Finset RawPrimeUnit) := h ▸ (by simp)
       simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto
  refine ⟨u₁.1, u₂.1, u₃.1, u₄.1, p1, p2, p3, p4, nep e1 e2 hu12, nep e1 e3 h13, nep e1 e4 h14,
    nep e2 e3 h23, nep e2 e4 h24, nep e3 e4 hu34, j₁, j₂, j₃, j₄, j₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, val hj₁ hu12, val hj₂ h13, val hj₃ h14, val hj₄ h23, val hj₅ h24⟩
  · exact jne hj₁ hj₂ (fun h => by
      have : u₂ ∈ ({u₁, u₃} : Finset RawPrimeUnit) := h ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'; exact hu12 h'.symm; exact h23 h')
  · exact jne hj₁ hj₃ (fun h => by
      have : u₂ ∈ ({u₁, u₄} : Finset RawPrimeUnit) := h ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'; exact hu12 h'.symm; exact h24 h')
  · exact jne hj₁ hj₄ (pne hu12 h13)
  · exact jne hj₁ hj₅ (pne hu12 h14)
  · exact jne hj₂ hj₃ (fun h => by
      have : u₃ ∈ ({u₁, u₄} : Finset RawPrimeUnit) := h ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'; exact h13 h'.symm; exact hu34 h')
  · exact jne hj₂ hj₄ (pne (Ne.symm hu12 |> fun h => by exact fun e => hu12 e) h13)
  · exact jne hj₂ hj₅ (pne (fun e => hu12 e) h14)
  · exact jne hj₃ hj₄ (pne (fun e => hu12 e) h13)
  · exact jne hj₃ hj₅ (pne (fun e => hu12 e) h14)
  · exact jne hj₄ hj₅ (fun h => by
      have : u₃ ∈ ({u₂, u₄} : Finset RawPrimeUnit) := h ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'; exact h23 h'.symm; exact hu34 h')

end Exceptional


section Repair

variable {L x : ℤ} {M : ℕ}

theorem fiveCover_of_prodCover {a b c d e k T : ℕ} (h : ProdCover L M T k)
    (hT : T = a * b * c * d * e) : FiveModuliCover L M a b c d e k := by
  obtain ⟨B, hB, hcard, hdvd⟩ := h
  refine ⟨B, hB, hcard, ?_⟩
  rw [hT] at hdvd; push_cast at hdvd; exact hdvd

/-- Four labelled representatives, an anchor payment `X`, and one extra payment `π` coprime to
the labels: at most six sites, even if the extra site coincides with a representative. -/
theorem cover_extra {z : ℤ} {X π T : ℕ} (ℓ : Fin 4 → ℕ) (b : Fin 4 → ℤ)
    (hb : Function.Injective b) (hx : x ∈ integerInterval L M)
    (hbI : ∀ k, b k ∈ integerInterval L M) (hbx : ∀ k, b k ≠ x) (hℓ : ∀ k, (ℓ k : ℤ) ∣ b k)
    (hz : z ∈ integerInterval L M) (hzx : z ≠ x) (hπ : (π : ℤ) ∣ z)
    (hcop : ∀ k, Nat.Coprime π (ℓ k)) (hX : (X : ℤ) ∣ x)
    (hT : T ∣ X * (∏ k, ℓ k) * π) : ProdCover L M T 6 := by
  classical
  have hxB : x ∉ Finset.univ.image b := by
    intro h; obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h; exact hbx k hk
  have hbcard : (Finset.univ.image b).card = 4 := by
    rw [Finset.card_image_of_injective _ hb]; simp
  have hprodb : ∏ z ∈ Finset.univ.image b, z = ∏ k, b k :=
    Finset.prod_image (fun i _ j _ h => hb h)
  have hℓb : ((∏ k, ℓ k : ℕ) : ℤ) ∣ ∏ k, b k := by
    push_cast; exact Finset.prod_dvd_prod_of_dvd _ _ (fun k _ => hℓ k)
  have hT' : (T : ℤ) ∣ (X : ℤ) * ((∏ k, ℓ k : ℕ) : ℤ) * π := by exact_mod_cast hT
  by_cases hzb : ∃ k, b k = z
  · obtain ⟨k₀, hk₀⟩ := hzb
    refine ⟨insert x (Finset.univ.image b), ?_, ?_, ?_⟩
    · intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · exact hx
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hw; exact hbI k
    · rw [Finset.card_insert_of_notMem hxB, hbcard]
      norm_num
    · rw [Finset.prod_insert hxB, hprodb]
      refine hT'.trans ?_
      have hk0 : ((ℓ k₀ * π : ℕ) : ℤ) ∣ b k₀ := by
        push_cast
        have hc : IsCoprime (ℓ k₀ : ℤ) (π : ℤ) :=
          Nat.isCoprime_iff_coprime.mpr (hcop k₀).symm
        exact hc.mul_dvd (hℓ k₀) (hk₀ ▸ hπ)
      have hrest : ((∏ k ∈ Finset.univ.erase k₀, ℓ k : ℕ) : ℤ) ∣
          ∏ k ∈ Finset.univ.erase k₀, b k := by
        push_cast; exact Finset.prod_dvd_prod_of_dvd _ _ (fun k _ => hℓ k)
      rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ k₀),
        ← Finset.mul_prod_erase Finset.univ ℓ (Finset.mem_univ k₀)]
      have := mul_dvd_mul hX (mul_dvd_mul hk0 hrest)
      push_cast at this ⊢
      calc (X : ℤ) * ((ℓ k₀ : ℤ) * ∏ k ∈ Finset.univ.erase k₀, (ℓ k : ℤ)) * π
          = X * ((ℓ k₀ * π) * ∏ k ∈ Finset.univ.erase k₀, (ℓ k : ℤ)) := by ring
        _ ∣ x * (b k₀ * ∏ k ∈ Finset.univ.erase k₀, b k) := this
  · push Not at hzb
    have hzB : z ∉ Finset.univ.image b := by
      intro h; obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h; exact hzb k hk
    have hxzB : x ∉ insert z (Finset.univ.image b) := by
      rw [Finset.mem_insert, not_or]; exact ⟨Ne.symm hzx, hxB⟩
    refine ⟨insert x (insert z (Finset.univ.image b)), ?_, ?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | rfl | hw
      · exact hx
      · exact hz
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hw; exact hbI k
    · rw [Finset.card_insert_of_notMem hxzB, Finset.card_insert_of_notMem hzB, hbcard]
    · rw [Finset.prod_insert hxzB, Finset.prod_insert hzB, hprodb]
      refine hT'.trans ?_
      have := mul_dvd_mul (mul_dvd_mul hX hℓb) hπ
      calc (X : ℤ) * ((∏ k, ℓ k : ℕ) : ℤ) * π ∣ x * (∏ k, b k) * z := this
        _ = x * (z * ∏ k, b k) := by ring

/-- Prime-power bookkeeping: pairwise coprime divisors of `x` multiply to a divisor. -/
theorem coprime_mul_dvd {a b : ℕ} (hab : Nat.Coprime a b) (ha : (a : ℤ) ∣ x)
    (hb : (b : ℤ) ∣ x) : ((a * b : ℕ) : ℤ) ∣ x :=
  Int.natCast_dvd.mpr (hab.mul_dvd_of_dvd_of_dvd (Int.natCast_dvd.mp ha) (Int.natCast_dvd.mp hb))

/-- The exceptional family `{pq, pr, ps, qr, qs}` with `p < q`. -/
theorem exceptional_cover_lt {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : s.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s)
    (hrs : r ≠ s) (hlt : p < q) (hx : x ∈ integerInterval L M)
    (d1 : ((p * q : ℕ) : ℤ) ∣ x) (d2 : ((p * r : ℕ) : ℤ) ∣ x) (d3 : ((p * s : ℕ) : ℤ) ∣ x)
    (d4 : ((q * r : ℕ) : ℤ) ∣ x)
    (m1 : p * q ≤ M) (m2 : p * r ≤ M) (m3 : p * s ≤ M) (m4 : q * r ≤ M) :
    ProdCover L M ((p * q) * (p * r) * (p * s) * (q * r) * (q * s)) 6 := by
  classical
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have hs2 := hs.two_le
  have cop : ∀ {a b : ℕ}, a.Prime → b.Prime → a ≠ b → Nat.Coprime a b :=
    fun ha hb hab => (Nat.coprime_primes ha hb).mpr hab
  have dvdx : ∀ {a b : ℕ}, ((a * b : ℕ) : ℤ) ∣ x → (a : ℤ) ∣ x ∧ (b : ℤ) ∣ x := by
    intro a b h
    exact ⟨(Int.natCast_dvd_natCast.mpr (dvd_mul_right a b)).trans h,
      (Int.natCast_dvd_natCast.mpr (dvd_mul_left b a)).trans h⟩
  obtain ⟨hpx, hqx⟩ := dvdx d1
  obtain ⟨-, hrx⟩ := dvdx d2
  obtain ⟨-, hsx⟩ := dvdx d3
  -- four-label representatives
  let a' : Fin 4 → ℕ := ![p * q, q * r, p * r, p * s]
  let r' : Fin 4 → ℕ := ![q, q, r, s]
  have hmulne : ∀ {a b c d : ℕ}, a * b = c * d → a.Prime → b.Prime → c.Prime → d.Prime →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    intro a b c d h ha hb hc hd
    have hca : c ∣ a * b := ⟨d, h.symm ▸ rfl⟩
    rcases (Nat.Prime.dvd_mul hc).mp hca with h1 | h1
    · have : c = a := (Nat.prime_dvd_prime_iff_eq hc ha).mp h1
      subst this
      left; exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hc.pos h⟩
    · have : c = b := (Nat.prime_dvd_prime_iff_eq hc hb).mp h1
      subst this
      right; refine ⟨?_, rfl⟩
      have : c * a = c * d := by rw [← h]; ring
      exact Nat.eq_of_mul_eq_mul_left hc.pos this
  have hinj : Function.Injective a' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [a'] at hij ⊢ <;>
      first
      | omega
      | (rcases hmulne hij (by assumption) (by assumption) (by assumption) (by assumption) with
          ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
  obtain ⟨b, hb, hbC⟩ := proper_divisor_sdr_fin_four (L := L) (x := x) (M := M) a' r'
    (fun i => Nat.pos_of_ne_zero (by fin_cases i <;> simp [a'] <;> omega)) hinj
    (fun i => by fin_cases i <;> simp [r'] <;> omega)
    (fun i => by fin_cases i <;> simp [a', r'] <;> exact dvd_mul_left _ _ <;> exact dvd_mul_right _ _)
    (fun i => by
      fin_cases i <;> simp [a', r'] <;> intro h <;> nlinarith)
    (fun i => by fin_cases i <;> simp [a'] <;> assumption)
    hx (fun i => by fin_cases i <;> simp [r'] <;> assumption)
  have hbI : ∀ k, b k ∈ integerInterval L M := fun k => by
    have := hbC k; rw [properDivisorCandidates_eq_cand, mem_cand] at this; exact this.1
  have hbx : ∀ k, b k ≠ x := fun k => by
    have := hbC k; rw [properDivisorCandidates_eq_cand, mem_cand] at this; exact this.2.1
  have hbℓ : ∀ k, (r' k : ℤ) ∣ b k := fun k => by
    have := hbC k; rw [properDivisorCandidates_eq_cand, mem_cand] at this; exact this.2.2
  have hcopℓ : ∀ {π : ℕ}, (π = p * p ∨ π = p) → ∀ k, Nat.Coprime π (r' k) := by
    intro π hπ k
    have hpk : Nat.Coprime p (r' k) := by
      fin_cases k
      · exact cop hp hq hpq
      · exact cop hp hq hpq
      · exact cop hp hr hpr
      · exact cop hp hs hps
    rcases hπ with rfl | rfl
    · exact Nat.coprime_mul_iff_left.mpr ⟨hpk, hpk⟩
    · exact hpk
  have hℓprod : ∏ k, r' k = q * q * r * s := by
    simp [r', Fin.prod_univ_four]
  have hqrs : ((q * r * s : ℕ) : ℤ) ∣ x :=
    coprime_mul_dvd (Nat.coprime_mul_iff_left.mpr ⟨cop hq hs hqs, cop hr hs hrs⟩)
      (coprime_mul_dvd (cop hq hr hqr) hqx hrx) hsx
  have hpqrs : Nat.Coprime p (q * r * s) :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right (cop hp hq hpq) (cop hp hr hpr)) (cop hp hs hps)
  have hpp : p * p ≤ M := by nlinarith
  by_cases hA : ∃ z ∈ integerInterval L M, z ≠ x ∧ ((p * p : ℕ) : ℤ) ∣ z
  · obtain ⟨z, hz, hzx, hzp⟩ := hA
    have hX : ((p * (q * r * s) : ℕ) : ℤ) ∣ x := coprime_mul_dvd hpqrs hpx hqrs
    exact cover_extra r' b hb hx hbI hbx hbℓ hz hzx hzp (hcopℓ (Or.inl rfl)) hX
      (by rw [hℓprod]; apply dvd_of_eq; ring)
  · push Not at hA
    obtain ⟨w, hw, hwp⟩ := exists_interval_multiple_of_le_candidate (L := L)
      (by positivity : 0 < p * p) hpp
    have hwx : w = x := by by_contra h; exact hA w hw h hwp
    have hppx : ((p * p : ℕ) : ℤ) ∣ x := hwx ▸ hwp
    obtain ⟨z, hz, hzp, hzF⟩ := exists_multiple_outside {x} hp.pos hx hpx (k := 1)
      (by nlinarith) (by simp)
    have hzx : z ≠ x := by simpa using hzF
    have hX : ((p * p * (q * r * s) : ℕ) : ℤ) ∣ x :=
      coprime_mul_dvd (Nat.coprime_mul_iff_left.mpr ⟨hpqrs, hpqrs⟩) hppx hqrs
    exact cover_extra r' b hb hx hbI hbx hbℓ hz hzx hzp (hcopℓ (Or.inr rfl)) hX
      (by rw [hℓprod]; apply dvd_of_eq; ring)

end Repair


section Final

/-- The exceptional family in either order of the two triply occurring primes. -/
theorem exceptional_cover {L x : ℤ} {M : ℕ} {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) (hx : x ∈ integerInterval L M)
    (d1 : ((p * q : ℕ) : ℤ) ∣ x) (d2 : ((p * r : ℕ) : ℤ) ∣ x) (d3 : ((p * s : ℕ) : ℤ) ∣ x)
    (d4 : ((q * r : ℕ) : ℤ) ∣ x) (d5 : ((q * s : ℕ) : ℤ) ∣ x)
    (m1 : p * q ≤ M) (m2 : p * r ≤ M) (m3 : p * s ≤ M) (m4 : q * r ≤ M) (m5 : q * s ≤ M) :
    ProdCover L M ((p * q) * (p * r) * (p * s) * (q * r) * (q * s)) 6 := by
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact exceptional_cover_lt hp hq hr hs hpq hpr hps hqr hqs hrs hlt hx d1 d2 d3 d4 m1 m2 m3 m4
  · have h := exceptional_cover_lt hq hp hr hs (Ne.symm hpq) hqr hqs hpr hps hrs hgt hx
      (by rw [mul_comm]; exact d1) d4 d5 d2 (by rw [mul_comm]; exact m1) m4 m5 m2
    obtain ⟨B, hB, hcard, hdvd⟩ := h
    refine ⟨B, hB, hcard, ?_⟩
    have : ((q * p) * (q * r) * (q * s) * (p * r) * (p * s) : ℕ) =
        (p * q) * (p * r) * (p * s) * (q * r) * (q * s) := by ring
    rw [← this]; exact hdvd

/-- **The single-anchor case** (`FIVE_COMMON_ANCHOR.md`). -/
theorem case5_holds : Case5Statement := by
  intro L M x a b c d e hx ha hb hc hd he ha0 hb0 hc0 hd0 he0 haM hbM hcM hdM heM
    iab iba iac ica iad ida iae iea ibc icb ibd idb ibe ieb icd idc ice iec ide ied _
  classical
  let m : Fin 5 → ℕ := ![a, b, c, d, e]
  have hinc : ∀ i j, i ≠ j → ¬ m i ∣ m j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [m] at hij ⊢ <;> assumption
  have hm2 : ∀ i, 2 ≤ m i := by
    intro i
    by_contra h
    push Not at h
    have hpos : 0 < m i := by fin_cases i <;> simp [m] <;> assumption
    have h1 : m i = 1 := by omega
    obtain ⟨j, hj⟩ : ∃ j : Fin 5, j ≠ i := by
      by_cases h0 : i = 0
      · exact ⟨1, by rw [h0]; decide⟩
      · exact ⟨0, fun e => h0 e.symm⟩
    exact hinc i j (Ne.symm hj) (h1 ▸ one_dvd _)
  have hinj : Function.Injective m := by
    intro i j hij
    by_contra hne
    exact hinc i j hne (hij ▸ dvd_rfl)
  have hle : ∀ i, m i ≤ M := by intro i; fin_cases i <;> simp [m] <;> assumption
  have hdiv : ∀ i, (m i : ℤ) ∣ x := by intro i; fin_cases i <;> simp [m] <;> assumption
  have hprod : ∏ i, m i = a * b * c * d * e := by simp [m, Fin.prod_univ_five]
  by_cases hU : 5 ≤ (Finset.univ.biUnion (fun i => rawPrimeUnits (m i))).card
  · exact fiveCover_of_prodCover (case5_regular m hm2 hinj hle hx hdiv hinc hU) hprod
  · obtain ⟨p, q, r, s, hp, hq, hr, hs, hpq, hpr, hps, hqr, hqs, hrs, j₁, j₂, j₃, j₄, j₅,
      h12, h13, h14, h15, h23, h24, h25, h34, h35, h45, e1, e2, e3, e4, e5⟩ :=
      exceptional_structure m hm2 hinc (by omega)
    have hT : ∏ i, m i = (p * q) * (p * r) * (p * s) * (q * r) * (q * s) := by
      rw [prod_five h12 h13 h14 h15 h23 h24 h25 h34 h35 h45, e1, e2, e3, e4, e5]
    have cov := exceptional_cover hp hq hr hs hpq hpr hps hqr hqs hrs hx
      (e1 ▸ hdiv j₁) (e2 ▸ hdiv j₂) (e3 ▸ hdiv j₃) (e4 ▸ hdiv j₄) (e5 ▸ hdiv j₅)
      (e1 ▸ hle j₁) (e2 ▸ hle j₂) (e3 ▸ hle j₃) (e4 ▸ hle j₄) (e5 ▸ hle j₅)
    exact fiveCover_of_prodCover cov (by rw [← hT, hprod])

end Final

end Erdos708.Five
