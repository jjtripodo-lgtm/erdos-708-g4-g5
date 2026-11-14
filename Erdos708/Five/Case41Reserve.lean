module

public import Erdos708.Five.Case5

@[expose] public section

/-!
# The (4,1) case: the reserve-or-odd-unit choice

Source: `FOUR_UPPER_PLUS_ONE_CANDIDATE.md`, reserve-or-odd-unit lemma. Four pairwise
incomparable upper-half originals, one of them `A = 2e`. We find a split `a i = p i * r i` with
`2 ≤ p i`, `∏ p i ∣ lcm a`, and `p k ≠ 2` for the original `A = a k`. The three other originals
receive distinct prime units that avoid a chosen set `W` of units of `A`. `A` receives the
product of the units in `W`: one odd prime, or two factors `2`.

Hall's condition for the three others with `W` removed can fail only when their units form a
three-element set that contains the removed unit. Then the three others are `q p₁, q p₂, p₁ p₂`
for distinct primes. The case analysis below uses this structure to pick a different `W`.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

theorem fin3_third (i j : Fin 3) : ∃ l : Fin 3, l ≠ i ∧ l ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

/-- Three pairwise incomparable originals have distinct prime units. -/
theorem plain3 (o : Fin 3 → ℕ) (ho2 : ∀ j, 2 ≤ o j) (hinc : ∀ i j, i ≠ j → ¬ o i ∣ o j) :
    ∃ f : Fin 3 → RawPrimeUnit, Function.Injective f ∧ ∀ j, f j ∈ rawPrimeUnits (o j) := by
  classical
  have ho0 : ∀ j, o j ≠ 0 := fun j => by have := ho2 j; omega
  have hhall : ∀ S : Finset (Fin 3), S.card ≤ (S.biUnion (fun j => rawPrimeUnits (o j))).card :=
    fun S => small_pairwise_incomparable_biUnion_card_candidate S _
      (by simpa using (Finset.card_le_univ S).trans (by simp))
      (fun j _ => rawPrimeUnits_nonempty_candidate (by have := ho2 j; omega))
      (fun i _ j _ hij hs => hinc i j hij
        ((rawPrimeUnits_subset_iff_dvd_candidate (ho0 i) (ho0 j)).mp hs))
  exact (Finset.all_card_le_biUnion_card_iff_exists_injective _).mp hhall

/-- **Hall with removed units.** Three pairwise incomparable originals, none dividing `A`.
Remove a set `W` of units of `A` that meets the units of each original at most in `w₀`. Either
distinct units avoiding `W` exist, or the units of the three form a three-element set that
contains `w₀`. -/
theorem hall3_avoid (o : Fin 3 → ℕ) (A : ℕ) (ho2 : ∀ j, 2 ≤ o j) (hA0 : A ≠ 0)
    (hinc : ∀ i j, i ≠ j → ¬ o i ∣ o j) (hoA : ∀ j, ¬ o j ∣ A)
    (W : Finset RawPrimeUnit) (hW : W ⊆ rawPrimeUnits A) (w₀ : RawPrimeUnit)
    (hw₀ : ∀ j, rawPrimeUnits (o j) ∩ W ⊆ {w₀}) :
    (∃ f : Fin 3 → RawPrimeUnit, Function.Injective f ∧
        ∀ j, f j ∈ rawPrimeUnits (o j) ∧ f j ∉ W) ∨
      ((Finset.univ.biUnion (fun j => rawPrimeUnits (o j))).card = 3 ∧
        w₀ ∈ Finset.univ.biUnion (fun j => rawPrimeUnits (o j))) := by
  classical
  by_cases hbad : (Finset.univ.biUnion (fun j => rawPrimeUnits (o j))).card = 3 ∧
      w₀ ∈ Finset.univ.biUnion (fun j => rawPrimeUnits (o j))
  · exact Or.inr hbad
  left
  have ho0 : ∀ j, o j ≠ 0 := fun j => by have := ho2 j; omega
  set C : Fin 3 → Finset RawPrimeUnit := fun j => rawPrimeUnits (o j) with hCdef
  set D : Fin 3 → Finset RawPrimeUnit := fun j => C j \ W with hDdef
  have hincC : ∀ i j, i ≠ j → ¬ C i ⊆ C j := fun i j hij hs =>
    hinc i j hij ((rawPrimeUnits_subset_iff_dvd_candidate (ho0 i) (ho0 j)).mp hs)
  have hne : ∀ j, (C j).Nonempty := fun j =>
    rawPrimeUnits_nonempty_candidate (by have := ho2 j; omega)
  have hDne : ∀ j, (D j).Nonempty := by
    intro j
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, hDdef, Finset.sdiff_eq_empty_iff_subset] at h
    exact hoA j ((rawPrimeUnits_subset_iff_dvd_candidate (ho0 j) hA0).mp (h.trans hW))
  have hCD : ∀ j, C j ⊆ insert w₀ (D j) := by
    intro j u hu
    by_cases huW : u ∈ W
    · rw [Finset.mem_singleton.mp (hw₀ j (Finset.mem_inter.mpr ⟨hu, huW⟩))]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hu, huW⟩)
  have hunion : ∀ S : Finset (Fin 3), S.biUnion D = S.biUnion C \ W := by
    intro S; ext u
    simp only [hDdef, Finset.mem_biUnion, Finset.mem_sdiff]
    constructor
    · rintro ⟨j, hj, hu, huW⟩; exact ⟨⟨j, hj, hu⟩, huW⟩
    · rintro ⟨⟨j, hj, hu⟩, huW⟩; exact ⟨j, hj, hu, huW⟩
  have hinter : ∀ S : Finset (Fin 3), S.biUnion C ∩ W ⊆ {w₀} := by
    intro S u hu
    rw [Finset.mem_inter, Finset.mem_biUnion] at hu
    obtain ⟨⟨j, -, hj⟩, hW'⟩ := hu
    exact hw₀ j (Finset.mem_inter.mpr ⟨hj, hW'⟩)
  have hhall : ∀ S : Finset (Fin 3), S.card ≤ (S.biUnion D).card := by
    intro S
    have hS3 : S.card ≤ 3 := by simpa using Finset.card_le_univ S
    have hbase := small_pairwise_incomparable_biUnion_card_candidate S C (by omega)
      (fun j _ => hne j) (fun i _ j _ hij => hincC i j hij)
    have hsplit := Finset.card_sdiff_add_card_inter (S.biUnion C) W
    have hI1 : (S.biUnion C ∩ W).card ≤ 1 :=
      (Finset.card_le_card (hinter S)).trans (by simp)
    rw [hunion]
    by_cases hI0 : (S.biUnion C ∩ W).card = 0
    · omega
    by_cases hbig : S.card + 1 ≤ (S.biUnion C).card
    · omega
    exfalso
    have hw₀in : w₀ ∈ S.biUnion C ∩ W := by
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (S.biUnion C ∩ W).card)
      rwa [Finset.mem_singleton.mp (hinter S hu)] at hu
    have htight : (S.biUnion C).card = S.card := by omega
    have hdiff : (S.biUnion C \ W).card + 1 = S.card := by omega
    rcases Nat.lt_or_ge S.card 3 with h3 | h3
    · interval_cases hc : S.card
      · rw [Finset.card_eq_zero] at hc; subst hc; simp at hw₀in
      · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hc
        have : D j = ∅ := by
          rw [← Finset.card_eq_zero, ← Finset.singleton_biUnion (a := j) (t := D), hunion]
          omega
        exact (hDne j).ne_empty this
      · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hc
        have hX : (({i, j} : Finset (Fin 3)).biUnion C \ W).card = 1 := by omega
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hX
        have hDsub : ∀ l ∈ ({i, j} : Finset (Fin 3)), D l = {v} := by
          intro l hl
          have hsub : D l ⊆ {v} := by
            rw [← hv, ← hunion]
            exact Finset.subset_biUnion_of_mem D hl
          rcases Finset.subset_singleton_iff.mp hsub with h | h
          · exact absurd h (hDne l).ne_empty
          · exact h
        have hDi := hDsub i (by simp)
        have hDj := hDsub j (by simp)
        by_cases hwj : w₀ ∈ C j
        · apply hincC i j hij
          intro u hu
          have := hCD i hu
          rw [hDi, ← hDj] at this
          rw [Finset.mem_insert] at this
          rcases this with rfl | h
          · exact hwj
          · exact (Finset.mem_sdiff.mp h).1
        · apply hincC j i (Ne.symm hij)
          intro u hu
          have huW : u ∉ W := by
            intro huW
            have := hw₀ j (Finset.mem_inter.mpr ⟨hu, huW⟩)
            rw [Finset.mem_singleton] at this
            exact hwj (this ▸ hu)
          have hu' : u ∈ D j := Finset.mem_sdiff.mpr ⟨hu, huW⟩
          rw [hDj, ← hDi] at hu'
          exact (Finset.mem_sdiff.mp hu').1
    · have hSu : S = Finset.univ := Finset.eq_univ_of_card _ (by simp; omega)
      subst hSu
      exact hbad ⟨by omega, (Finset.mem_inter.mp hw₀in).1⟩
  obtain ⟨f, hf, hfD⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective D).mp hhall
  exact ⟨f, hf, fun j => Finset.mem_sdiff.mp (hfD j)⟩

/-- **Tight three-unit structure.** Three pairwise incomparable originals whose units form a
three-element set containing `(q, s)`, with no original having `(q, s)` as its only unit, are
`q p₁, q p₂, p₁ p₂` for distinct primes, and `s = 0`. -/
theorem struct3 (o : Fin 3 → ℕ) (ho2 : ∀ j, 2 ≤ o j) (hinc : ∀ i j, i ≠ j → ¬ o i ∣ o j)
    (hG : (Finset.univ.biUnion (fun j => rawPrimeUnits (o j))).card = 3)
    {q s : ℕ} (hw : (q, s) ∈ Finset.univ.biUnion (fun j => rawPrimeUnits (o j)))
    (hsing : ∀ j, rawPrimeUnits (o j) ≠ {(q, s)}) :
    s = 0 ∧ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ q.Prime ∧ p₁ ≠ p₂ ∧ q ≠ p₁ ∧ q ≠ p₂ ∧
      Finset.univ.biUnion (fun j => rawPrimeUnits (o j)) = {(q, 0), (p₁, 0), (p₂, 0)} ∧
      (∃ j, o j = q * p₁) ∧ (∃ j, o j = q * p₂) ∧ (∃ j, o j = p₁ * p₂) := by
  classical
  have ho0 : ∀ j, o j ≠ 0 := fun j => by have := ho2 j; omega
  set C : Fin 3 → Finset RawPrimeUnit := fun j => rawPrimeUnits (o j) with hCdef
  set G := Finset.univ.biUnion C with hGdef
  have hCG : ∀ j, C j ⊆ G := fun j => Finset.subset_biUnion_of_mem C (Finset.mem_univ j)
  have hincC : ∀ i j, i ≠ j → ¬ C i ⊆ C j := fun i j hij hs =>
    hinc i j hij ((rawPrimeUnits_subset_iff_dvd_candidate (ho0 i) (ho0 j)).mp hs)
  have hne : ∀ j, (C j).Nonempty := fun j =>
    rawPrimeUnits_nonempty_candidate (by have := ho2 j; omega)
  have hCinj : Function.Injective C := fun i j h => by
    by_contra hij; exact hincC i j hij (h ▸ subset_refl _)
  -- no member is all of `G`
  have hlt3 : ∀ j, (C j).card < 3 := by
    intro j
    by_contra h
    have hj : C j = G := Finset.eq_of_subset_of_card_le (hCG j) (by omega)
    obtain ⟨l, hl, -⟩ := fin3_third j j
    exact hincC l j hl (hj ▸ hCG l)
  -- no singleton member
  have hno1 : ∀ i, (C i).card ≠ 1 := by
    intro i h1
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
    have huG : u ∈ G := hCG i (by rw [hu]; simp)
    have hE : (G.erase u).card = 2 := by rw [Finset.card_erase_of_mem huG]; omega
    have hsubE : ∀ j, j ≠ i → C j ⊆ G.erase u := by
      intro j hji v hv
      refine Finset.mem_erase.mpr ⟨fun hvu => hincC i j (Ne.symm hji) ?_, hCG j hv⟩
      rw [hu, Finset.singleton_subset_iff, ← hvu]; exact hv
    -- every member is a singleton
    have hall1 : ∀ j, (C j).card = 1 := by
      intro j
      by_cases hji : j = i
      · rw [hji]; exact h1
      obtain ⟨l, hli, hlj⟩ := fin3_third i j
      have hle : (C j).card ≤ 1 := by
        by_contra h2
        have hj : C j = G.erase u :=
          Finset.eq_of_subset_of_card_le (hsubE j hji) (by
            have := Finset.card_le_card (hsubE j hji); omega)
        exact hincC l j hlj (hj ▸ hsubE l hli)
      have := (hne j).card_pos
      omega
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (hall1 j)
    rw [hv, Finset.mem_singleton] at hj
    exact hsing j (by rw [show rawPrimeUnits (o j) = C j from rfl, hv, hj])
  have hC2 : ∀ j, (C j).card = 2 := fun j => by
    have := (hne j).card_pos; have := hno1 j; have := hlt3 j; omega
  -- every two-element subset of `G` is a member
  have hit : ∀ P ∈ G.powersetCard 2, ∃ j, C j = P := by
    have hsub : Finset.univ.image C ⊆ G.powersetCard 2 := by
      intro t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_powersetCard.mpr ⟨hCG i, hC2 i⟩
    have heq : Finset.univ.image C = G.powersetCard 2 :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_image_of_injective _ hCinj, Finset.card_powersetCard, hG]; simp)
    intro P hP
    rw [← heq] at hP
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hP
    exact ⟨j, hj⟩
  have hpair : ∀ {u v : RawPrimeUnit}, u ∈ G → v ∈ G → u ≠ v → ∃ j, C j = {u, v} := by
    intro u v hu hv huv
    apply hit
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair huv⟩
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> assumption
  -- every unit of `G` has slot zero
  have slot0 : ∀ u ∈ G, u.2 = 0 := by
    intro u hu
    by_contra hj
    have hE : (G.erase u).card = 2 := by rw [Finset.card_erase_of_mem hu]; omega
    obtain ⟨t₁, t₂, ht, hEq⟩ := Finset.card_eq_two.mp hE
    have ht₁ : t₁ ∈ G.erase u := by rw [hEq]; simp
    have ht₂ : t₂ ∈ G.erase u := by rw [hEq]; simp
    have hdown : ∀ j, u ∈ C j → (u.1, 0) ∈ C j := by
      intro j huj
      simp only [hCdef] at huj ⊢
      rw [show u = (u.1, u.2) from rfl, mem_rawPrimeUnits_candidate] at huj
      rw [mem_rawPrimeUnits_candidate]
      exact ⟨huj.1, by omega⟩
    have hne0 : (u.1, 0) ≠ u := by intro h; rw [← h] at hj; exact hj rfl
    obtain ⟨j₁, hj₁⟩ := hpair hu (Finset.mem_of_mem_erase ht₁) (Finset.ne_of_mem_erase ht₁).symm
    obtain ⟨j₂, hj₂⟩ := hpair hu (Finset.mem_of_mem_erase ht₂) (Finset.ne_of_mem_erase ht₂).symm
    have h1 := hdown j₁ (by rw [hj₁]; simp)
    have h2 := hdown j₂ (by rw [hj₂]; simp)
    rw [hj₁, Finset.mem_insert, Finset.mem_singleton] at h1
    rw [hj₂, Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h1 with h1 | h1
    · exact hne0 h1
    rcases h2 with h2 | h2
    · exact hne0 h2
    exact ht (h1.symm.trans h2)
  have prm : ∀ {u : RawPrimeUnit}, u ∈ G → u.1.Prime := by
    intro u hu
    obtain ⟨i, -, hui⟩ := Finset.mem_biUnion.mp hu
    simp only [hCdef] at hui
    rw [show u = (u.1, u.2) from rfl, mem_rawPrimeUnits_candidate] at hui
    exact (Nat.mem_primeFactors.mp hui.1).1
  have hs0 : s = 0 := slot0 _ hw
  subst hs0
  have hE : (G.erase (q, 0)).card = 2 := by rw [Finset.card_erase_of_mem hw]; omega
  obtain ⟨v₁, v₂, hv, hEq⟩ := Finset.card_eq_two.mp hE
  have hv₁ : v₁ ∈ G.erase (q, 0) := by rw [hEq]; simp
  have hv₂ : v₂ ∈ G.erase (q, 0) := by rw [hEq]; simp
  have hv₁G := Finset.mem_of_mem_erase hv₁
  have hv₂G := Finset.mem_of_mem_erase hv₂
  have e₁ : v₁ = (v₁.1, 0) := Prod.ext rfl (slot0 _ hv₁G)
  have e₂ : v₂ = (v₂.1, 0) := Prod.ext rfl (slot0 _ hv₂G)
  have val : ∀ {j : Fin 3} {u v : RawPrimeUnit}, C j = {u, v} → u ≠ v → o j = u.1 * v.1 := by
    intro j u v hj huv
    have := prod_rawPrimeUnits_fst_candidate (ho0 j)
    rw [show rawPrimeUnits (o j) = C j from rfl, hj, Finset.prod_pair huv] at this
    exact this.symm
  have hq1 : ((q, 0) : RawPrimeUnit) ≠ v₁ := (Finset.ne_of_mem_erase hv₁).symm
  have hq2 : ((q, 0) : RawPrimeUnit) ≠ v₂ := (Finset.ne_of_mem_erase hv₂).symm
  obtain ⟨j₁, hj₁⟩ := hpair hw hv₁G hq1
  obtain ⟨j₂, hj₂⟩ := hpair hw hv₂G hq2
  obtain ⟨j₃, hj₃⟩ := hpair hv₁G hv₂G hv
  refine ⟨rfl, v₁.1, v₂.1, prm hv₁G, prm hv₂G, prm hw, fun h => hv (by rw [e₁, e₂, h]),
    fun h => hq1 (by rw [e₁, ← h]), fun h => hq2 (by rw [e₂, ← h]), ?_,
    ⟨j₁, val hj₁ hq1⟩, ⟨j₂, val hj₂ hq2⟩, ⟨j₃, val hj₃ hv⟩⟩
  rw [← e₁, ← e₂, ← hEq, Finset.insert_erase hw]

/-- Assemble the four-original split from three avoiding units and the units `W` of `a k`. -/
theorem reserve_of_avoid (a : Fin 4 → ℕ) (k : Fin 4) (ha0 : ∀ i, a i ≠ 0)
    (f : Fin 3 → RawPrimeUnit) (hf : Function.Injective f)
    (hfC : ∀ j, f j ∈ rawPrimeUnits (a (k.succAbove j)))
    (W : Finset RawPrimeUnit) (hW : W ⊆ rawPrimeUnits (a k)) (hWne : W.Nonempty)
    (hfW : ∀ j, f j ∉ W) (hW2 : ∏ w ∈ W, w.1 ≠ 2) :
    ∃ p : Fin 4 → ℕ, (∀ i, p i ∣ a i) ∧ (∀ i, 2 ≤ p i) ∧
      (∏ i, p i) ∣ Finset.univ.lcm a ∧ p k ≠ 2 := by
  classical
  let p : Fin 4 → ℕ := Fin.insertNth k (∏ w ∈ W, w.1) (fun j => (f j).1)
  have hpk : p k = ∏ w ∈ W, w.1 := Fin.insertNth_apply_same _ _ _
  have hpj : ∀ j, p (k.succAbove j) = (f j).1 := fun j => Fin.insertNth_apply_succAbove _ _ _ _
  have hfP : ∀ j, (f j).1.Prime ∧ (f j).1 ∣ a (k.succAbove j) := by
    intro j
    have := hfC j
    rw [show f j = ((f j).1, (f j).2) from rfl, mem_rawPrimeUnits_candidate] at this
    exact ⟨(Nat.mem_primeFactors.mp this.1).1, (Nat.mem_primeFactors.mp this.1).2.1⟩
  have hWP : ∀ w ∈ W, w.1.Prime := by
    intro w hw
    have := hW hw
    rw [show w = (w.1, w.2) from rfl, mem_rawPrimeUnits_candidate] at this
    exact (Nat.mem_primeFactors.mp this.1).1
  have hL0 : Finset.univ.lcm a ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]; push Not; intro j _; exact ha0 j
  have hsubL : ∀ i, rawPrimeUnits (a i) ⊆ rawPrimeUnits (Finset.univ.lcm a) := fun i =>
    (rawPrimeUnits_subset_iff_dvd_candidate (ha0 i) hL0).mpr
      (Finset.dvd_lcm (Finset.mem_univ i))
  refine ⟨p, ?_, ?_, ?_, by rw [hpk]; exact hW2⟩
  · intro i
    rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
    · rw [hpk]; exact prod_rawPrimeUnits_subset_dvd_candidate (ha0 _) W hW
    · rw [hpj]; exact (hfP j).2
  · intro i
    rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
    · rw [hpk]
      obtain ⟨w, hw⟩ := hWne
      have hdvd : w.1 ∣ ∏ w ∈ W, w.1 := Finset.dvd_prod_of_mem _ hw
      have hpos : 0 < ∏ w ∈ W, w.1 :=
        Finset.prod_pos (fun v hv => (hWP v hv).pos)
      exact (hWP w hw).two_le.trans (Nat.le_of_dvd hpos hdvd)
    · rw [hpj]; exact (hfP j).1.two_le
  · rw [Fin.prod_univ_succAbove p k, hpk]
    simp only [hpj]
    have hdisj : Disjoint W (Finset.univ.image f) := by
      rw [Finset.disjoint_left]
      intro w hw hwf
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hwf
      exact hfW j hw
    have hsub : W ∪ Finset.univ.image f ⊆ rawPrimeUnits (Finset.univ.lcm a) := by
      intro u hu
      rw [Finset.mem_union] at hu
      rcases hu with hu | hu
      · exact hsubL k (hW hu)
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hu
        exact hsubL _ (hfC j)
    have := prod_rawPrimeUnits_subset_dvd_candidate hL0 _ hsub
    rwa [Finset.prod_union hdisj, Finset.prod_image (fun i _ j _ h => hf h)] at this

theorem mem_units_of_pow_dvd {n p j : ℕ} (hn : n ≠ 0) (hp : p.Prime) (h : p ^ (j + 1) ∣ n) :
    (p, j) ∈ rawPrimeUnits n := by
  rw [mem_rawPrimeUnits_candidate]
  refine ⟨Nat.mem_primeFactors.mpr ⟨hp, (dvd_pow_self p (Nat.succ_ne_zero j)).trans h, hn⟩, ?_⟩
  have := (hp.pow_dvd_iff_le_factorization hn).mp h; omega

theorem pow_dvd_of_mem_units {n p j : ℕ} (hn : n ≠ 0) (h : (p, j) ∈ rawPrimeUnits n) :
    p ^ (j + 1) ∣ n := by
  rw [mem_rawPrimeUnits_candidate] at h
  have hp := (Nat.mem_primeFactors.mp h.1).1
  exact (hp.pow_dvd_iff_le_factorization hn).mpr (by omega)

/-- **Reserve-or-odd-unit lemma.** Four pairwise incomparable upper-half originals, one of them
`a k = 2e`, have a split with `p k ≠ 2`. -/
theorem reserve (a : Fin 4 → ℕ) (k : Fin 4) {M e : ℕ} (hA : a k = 2 * e)
    (ha2 : ∀ i, 2 ≤ a i) (hinc : ∀ i j, i ≠ j → ¬ a i ∣ a j)
    (haM : ∀ i, a i ≤ M) (hhalf : ∀ i, M < 2 * a i) :
    ∃ p : Fin 4 → ℕ, (∀ i, p i ∣ a i) ∧ (∀ i, 2 ≤ p i) ∧
      (∏ i, p i) ∣ Finset.univ.lcm a ∧ p k ≠ 2 := by
  classical
  have ha0 : ∀ i, a i ≠ 0 := fun i => by have := ha2 i; omega
  set o : Fin 3 → ℕ := fun j => a (k.succAbove j) with hodef
  have ho2 : ∀ j, 2 ≤ o j := fun j => ha2 _
  have ho0 : ∀ j, o j ≠ 0 := fun j => ha0 _
  have hoinc : ∀ i j, i ≠ j → ¬ o i ∣ o j := fun i j hij =>
    hinc _ _ (fun h => hij (Fin.succAbove_right_injective h))
  have hoA : ∀ j, ¬ o j ∣ a k := fun j => hinc _ _ (Fin.succAbove_ne k j)
  have hA0 : a k ≠ 0 := ha0 k
  have hoM : ∀ j, o j ≤ M := fun j => haM _
  have hAM : M < 2 * a k := hhalf k
  have he0 : e ≠ 0 := by intro h; rw [h] at hA; exact hA0 hA
  have hsing : ∀ (W : Finset RawPrimeUnit), W ⊆ rawPrimeUnits (a k) → ∀ u ∈ W, ∀ j,
      rawPrimeUnits (o j) ≠ {u} := by
    intro W hW u hu j h
    apply hoA j
    exact (rawPrimeUnits_subset_iff_dvd_candidate (ho0 j) hA0).mp (h ▸ (by
      rw [Finset.singleton_subset_iff]; exact hW hu))
  obtain ⟨f₀, hf₀, hf₀C⟩ := plain3 o ho2 hoinc
  have finish := reserve_of_avoid a k ha0
  -- a matching avoids every `W` that misses the units of the three others
  have finish₀ : ∀ W : Finset RawPrimeUnit, W ⊆ rawPrimeUnits (a k) → W.Nonempty →
      (∀ j, ∀ u ∈ rawPrimeUnits (o j), u ∉ W) → ∏ w ∈ W, w.1 ≠ 2 →
      ∃ p : Fin 4 → ℕ, (∀ i, p i ∣ a i) ∧ (∀ i, 2 ≤ p i) ∧
        (∏ i, p i) ∣ Finset.univ.lcm a ∧ p k ≠ 2 :=
    fun W hW hWne hWo hW2 => finish f₀ hf₀ hf₀C W hW hWne (fun j => hWo j _ (hf₀C j)) hW2
  have hfour : ∀ {p₁ q : ℕ}, p₁.Prime → p₁ ≠ 2 → q * p₁ ≤ M → M < 4 * q → p₁ = 3 := by
    intro p₁ q hp h2 hle hlt
    have hq : 0 < q := by omega
    have : p₁ < 4 := by
      by_contra h; push Not at h
      have : q * 4 ≤ q * p₁ := Nat.mul_le_mul_left q h
      omega
    have := hp.two_le
    omega
  by_cases hodd : ∃ q, q.Prime ∧ q ∣ e ∧ q ≠ 2
  · obtain ⟨q, hq, hqe, hq2⟩ := hodd
    have hqA : q ∣ a k := hA ▸ Dvd.dvd.mul_left hqe 2
    have hW : ({(q, 0)} : Finset RawPrimeUnit) ⊆ rawPrimeUnits (a k) := by
      rw [Finset.singleton_subset_iff]; exact mem_units_of_pow_dvd hA0 hq (by simpa using hqA)
    rcases hall3_avoid o (a k) ho2 hA0 hoinc hoA {(q, 0)} hW (q, 0)
        (fun j => Finset.inter_subset_right) with ⟨f, hf, hfC⟩ | ⟨hG, hwG⟩
    · exact finish f hf (fun j => (hfC j).1) _ hW (Finset.singleton_nonempty _)
        (fun j => (hfC j).2) (by rw [Finset.prod_singleton]; exact hq2)
    obtain ⟨-, p₁, p₂, hp₁, hp₂, -, h12, hq1, hq2', hGeq, ⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩, -⟩ :=
      struct3 o ho2 hoinc hG hwG (hsing _ hW _ (Finset.mem_singleton_self _))
    have hGmem : ∀ j, ∀ u ∈ rawPrimeUnits (o j), u = (q, 0) ∨ u = (p₁, 0) ∨ u = (p₂, 0) := by
      intro j u hu
      have : u ∈ Finset.univ.biUnion (fun j => rawPrimeUnits (o j)) :=
        Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hu⟩
      rw [hGeq] at this
      simpa using this
    have hp2 : ∀ {p : ℕ} {j : Fin 3}, o j = q * p → p ≠ 2 := by
      intro p j hj hp
      apply hoA j
      rw [hj, hp, hA, mul_comm]
      exact Nat.mul_dvd_mul_left 2 hqe
    have hpe : ∀ {p : ℕ} {j : Fin 3}, p.Prime → q ≠ p → o j = q * p → ¬ p ∣ e := by
      intro p j hp hqp hj hpe
      apply hoA j
      rw [hj, hA]
      exact (Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hq hp).mpr hqp) hqe hpe).trans
        (Dvd.intro_left 2 rfl)
    have hp₁2 := hp2 hj₁
    have hp₂2 := hp2 hj₂
    have hp₁e := hpe hp₁ hq1 hj₁
    have hp₂e := hpe hp₂ hq2' hj₂
    by_cases he2 : 2 ∣ e
    · -- two factors `2` of `a k` are free
      have h4 : 2 ^ (1 + 1) ∣ a k := by
        rw [hA]; obtain ⟨t, rfl⟩ := he2; exact ⟨t, by ring⟩
      have hW' : ({(2, 0), (2, 1)} : Finset RawPrimeUnit) ⊆ rawPrimeUnits (a k) := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact mem_units_of_pow_dvd hA0 Nat.prime_two ((pow_dvd_pow 2 (by omega)).trans h4)
        · exact mem_units_of_pow_dvd hA0 Nat.prime_two h4
      refine finish₀ _ hW' (by simp) ?_ (by rw [Finset.prod_pair (by decide)]; decide)
      intro j u hu huW
      simp only [Finset.mem_insert, Finset.mem_singleton] at huW
      rcases hGmem j u hu with rfl | rfl | rfl <;> rcases huW with h | h <;>
        simp only [Prod.mk.injEq] at h <;> omega
    by_cases hq' : ∃ q', q'.Prime ∧ q' ∣ e ∧ q' ≠ q
    · obtain ⟨q', hq'p, hq'e, hq'q⟩ := hq'
      have hq'A : q' ∣ a k := hA ▸ Dvd.dvd.mul_left hq'e 2
      have hW' : ({(q', 0)} : Finset RawPrimeUnit) ⊆ rawPrimeUnits (a k) := by
        rw [Finset.singleton_subset_iff]
        exact mem_units_of_pow_dvd hA0 hq'p (by simpa using hq'A)
      have hq'2 : q' ≠ 2 := fun h => he2 (h ▸ hq'e)
      refine finish₀ _ hW' (by simp) ?_ (by rw [Finset.prod_singleton]; exact hq'2)
      intro j u hu huW
      rw [Finset.mem_singleton] at huW
      subst huW
      rcases hGmem j _ hu with h | h | h <;> simp only [Prod.mk.injEq] at h
      · exact hq'q h.1
      · exact hp₁e (h.1 ▸ hq'e)
      · exact hp₂e (h.1 ▸ hq'e)
    push Not at hq'
    by_cases hv : q ^ 2 ∣ e
    · have hW' : ({(q, 1)} : Finset RawPrimeUnit) ⊆ rawPrimeUnits (a k) := by
        rw [Finset.singleton_subset_iff]
        exact mem_units_of_pow_dvd hA0 hq (hA ▸ Dvd.dvd.mul_left hv 2)
      refine finish₀ _ hW' (by simp) ?_ (by rw [Finset.prod_singleton]; exact hq2)
      intro j u hu huW
      rw [Finset.mem_singleton] at huW
      subst huW
      rcases hGmem j _ hu with h | h | h <;> simp at h
    -- `e = q`
    have heq : e = q := by
      obtain ⟨n, hn⟩ : ∃ n, e = q ^ n := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd he0
        (fun {d} hd hde => hq' d hd hde)⟩
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · interval_cases n
        · rw [hn, pow_zero] at hqe; exact absurd (Nat.le_of_dvd one_pos hqe) (by have := hq.two_le; omega)
        · rw [hn, pow_one]
      · exact absurd (hn ▸ pow_dvd_pow q h2) hv
    subst heq
    have h4q : M < 4 * e := by omega
    have e₁ := hfour hp₁ hp₁2 (hj₁ ▸ hoM j₁) h4q
    have e₂ := hfour hp₂ hp₂2 (hj₂ ▸ hoM j₂) h4q
    exact absurd (e₁.trans e₂.symm) h12
  · -- `e` is a power of two
    push Not at hodd
    obtain ⟨s, hpow⟩ : ∃ s, e = 2 ^ s := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd he0
      (fun {d} hd hde => by
        by_contra h2
        exact h2 (hodd d hd hde))⟩
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · -- `e = 1`: impossible in the upper half
      have he1 : e = 1 := by rw [hpow, hs0, pow_zero]
      have h3 : ∀ j, o j = 3 := by
        intro j
        have := ho2 j; have := hoM j
        have h2 : o j ≠ 2 := fun h => hoA j (by rw [h, hA, he1])
        omega
      exact (hoinc 0 1 (by decide) (by rw [h3 0, h3 1])).elim
    obtain ⟨t, hst⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have hAp : a k = 2 ^ (t + 2) := by rw [hA, hpow, hst]; ring
    have hW : ({(2, t), (2, t + 1)} : Finset RawPrimeUnit) ⊆ rawPrimeUnits (a k) := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact mem_units_of_pow_dvd hA0 Nat.prime_two (hAp ▸ pow_dvd_pow 2 (by omega))
      · exact mem_units_of_pow_dvd hA0 Nat.prime_two (hAp ▸ dvd_rfl)
    have hw₀ : ∀ j, rawPrimeUnits (o j) ∩ {(2, t), (2, t + 1)} ⊆ {(2, t)} := by
      intro j u hu
      rw [Finset.mem_inter] at hu
      obtain ⟨hu, huW⟩ := hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at huW
      rcases huW with rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact (hinc k (k.succAbove j) (Fin.succAbove_ne k j).symm
          (by rw [hAp]; exact pow_dvd_of_mem_units (ho0 j) hu)).elim
    have hW2 : ∏ w ∈ ({(2, t), (2, t + 1)} : Finset RawPrimeUnit), w.1 ≠ 2 := by
      rw [Finset.prod_pair (by simp)]; norm_num
    rcases hall3_avoid o (a k) ho2 hA0 hoinc hoA _ hW (2, t) hw₀ with ⟨f, hf, hfC⟩ | ⟨hG, hwG⟩
    · exact finish f hf (fun j => (hfC j).1) _ hW (by simp) (fun j => (hfC j).2) hW2
    obtain ⟨ht0, p₁, p₂, hp₁, hp₂, -, h12, hq1, hq2, -, ⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩, -⟩ :=
      struct3 o ho2 hoinc hG hwG (hsing _ hW _ (by simp))
    subst ht0
    have h8 : M < 4 * 2 := by rw [hAp] at hAM; norm_num at hAM; omega
    have e₁ := hfour hp₁ (Ne.symm hq1) (hj₁ ▸ hoM j₁) h8
    have e₂ := hfour hp₂ (Ne.symm hq2) (hj₂ ▸ hoM j₂) h8
    exact absurd (e₁.trans e₂.symm) h12

end Erdos708.Five
