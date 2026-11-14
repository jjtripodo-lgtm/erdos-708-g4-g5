module

public import Definitions
public import Erdos708.Sharpness
public import Erdos708.Five.Final

@[expose] public section

namespace Erdos708Finite
open scoped BigOperators

theorem four_upper : CoverBound 4 5 := by
  intro m hinj htwo L
  have hle (i : Fin 4) : m i ≤ Finset.univ.sup m := Finset.le_sup (Finset.mem_univ i)
  have hne {i j : Fin 4} (h : i ≠ j) : m i ≠ m j := fun e => h (hinj e)
  simpa [Erdos708.FourModuliCover, interval, Erdos708.integerInterval, Fin.prod_univ_four] using
    (Erdos708.four_moduli_five_cover (L := L)
      (htwo 0) (htwo 1) (htwo 2) (htwo 3)
      (hle 0) (hle 1) (hle 2) (hle 3)
      (hne (by decide : (0 : Fin 4) ≠ 1)) (hne (by decide : (0 : Fin 4) ≠ 2))
      (hne (by decide : (0 : Fin 4) ≠ 3)) (hne (by decide : (1 : Fin 4) ≠ 2))
      (hne (by decide : (1 : Fin 4) ≠ 3)) (hne (by decide : (2 : Fin 4) ≠ 3)))

theorem five_upper : CoverBound 5 6 := by
  intro m hinj htwo L
  have hpos (i : Fin 5) : 0 < m i := by have := htwo i; omega
  have hle (i : Fin 5) : m i ≤ Finset.univ.sup m := Finset.le_sup (Finset.mem_univ i)
  simpa [Erdos708.Five.ProdCover, interval, Erdos708.integerInterval, Nat.cast_prod] using
    (Erdos708.Five.upper_of_cases Erdos708.Five.case41_holds
      Erdos708.Five.case5_holds (L := L) m hinj hpos hle)

theorem four_lower : ¬ CoverBound 4 4 := by
  intro h
  let m : Fin 4 → ℕ := ![77, 91, 139, 143]
  have hi : Function.Injective m := by decide
  have ht : ∀ i, 2 ≤ m i := by decide
  obtain ⟨B, hB, hc, hd⟩ := h m hi ht 5935
  have hm : Finset.univ.sup m = 143 := by decide
  apply Erdos708.sharp_full_no_four_cover B _ hc _
  · simpa [interval, Erdos708.sharpInterval, Erdos708.integerInterval,
      hm] using hB
  · simpa [m, Fin.prod_univ_four, Erdos708.sharpFullTarget] using hd

theorem five_lower : ¬ CoverBound 5 5 := by
  intro h
  let m : Fin 5 → ℕ := ![5, 10, 12, 15, 20]
  have hi : Function.Injective m := by decide
  have ht : ∀ i, 2 ≤ m i := by decide
  obtain ⟨B, hB, hc, hd⟩ := h m hi ht 51
  have hm : Finset.univ.sup m = 20 := by decide
  apply Erdos708.sharp5_no_five_cover
  refine ⟨B, ?_, hc, ?_⟩
  · simpa [interval, Erdos708.integerInterval, hm] using hB
  · simpa [m, Fin.prod_univ_five] using hd

theorem cover_mono {n k l : ℕ} (h : k ≤ l) (hk : CoverBound n k) : CoverBound n l := by
  intro m hi ht L
  obtain ⟨B, hB, hc, hd⟩ := hk m hi ht L
  exact ⟨B, hB, hc.trans h, hd⟩

theorem four_least : IsLeast {k | CoverBound 4 k} 5 := by
  refine ⟨four_upper, ?_⟩
  intro k hk
  by_contra h
  exact four_lower (cover_mono (by omega) hk)

theorem five_least : IsLeast {k | CoverBound 5 k} 6 := by
  refine ⟨five_upper, ?_⟩
  intro k hk
  by_contra h
  exact five_lower (cover_mono (by omega) hk)

theorem interval_large {n : ℕ} (m : Fin n → ℕ) (hi : Function.Injective m)
    (ht : ∀ i, 2 ≤ m i) (hn : 0 < n) (L : ℤ) :
    n + 1 ≤ (interval L (Finset.univ.sup m)).card := by
  classical
  let M := Finset.univ.sup m
  have hM : 2 ≤ M := (ht ⟨0, hn⟩).trans (Finset.le_sup (Finset.mem_univ _))
  have hs : Finset.univ.image m ⊆ Finset.Icc 2 M := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_Icc.mpr ⟨ht i, Finset.le_sup (Finset.mem_univ _)⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hi] at hc
  simp only [Finset.card_univ, Fintype.card_fin, Nat.card_Icc] at hc
  have hlen : (interval L M).card = M := by
    simpa [interval, Erdos708.integerInterval] using
      (Erdos708.integerInterval_card (L := L) (by omega : 0 < M))
  change n + 1 ≤ (interval L M).card
  rw [hlen]
  omega

theorem exact_of_bound {n k : ℕ} (hn : 0 < n) (hk : k ≤ n + 1)
    (h : CoverBound n k) : ExactCoverBound n k := by
  intro m hi ht L
  obtain ⟨B, hB, hc, hd⟩ := h m hi ht L
  obtain ⟨C, hBC, hC, hcard⟩ := Finset.exists_subsuperset_card_eq hB hc
    (hk.trans (interval_large m hi ht hn L))
  exact ⟨C, hC, hcard, hd.trans (Finset.prod_dvd_prod_of_subset _ _ _ hBC)⟩

theorem four_exact : ExactCoverBound 4 5 := exact_of_bound (by decide) (by decide) four_upper

theorem five_exact : ExactCoverBound 5 6 := exact_of_bound (by decide) (by decide) five_upper

end Erdos708Finite

