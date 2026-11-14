module

public import Erdos708.Five.SDRCount
public import Erdos708.ProperDivisorSDR

@[expose] public section

/-!
# Five proper divisors have distinct off-anchor representatives

The source is `FIVE_PROPER_DIVISORS.md`. Subfamilies of at most four labels use the banked
four-label lemma `Erdos708.proper_divisor_sdr_fin_four`. The full family uses the primitive-set
union bound `five_le_card_union_of_primitive`. Hall's theorem then gives the representatives.
-/

namespace Erdos708.Five

open Erdos708

theorem properDivisorCandidates_eq_cand {k : ℕ} (L : ℤ) (M : ℕ) (x : ℤ) (r : Fin k → ℕ)
    (i : Fin k) : properDivisorCandidates L M x r i = cand L M x (r i) := by
  ext z; simp [properDivisorCandidates, cand]

/-- **Five-label proper-divisor SDR.** -/
theorem proper_divisor_sdr_fin_five {L x : ℤ} {M : ℕ} (a r : Fin 5 → ℕ)
    (haPos : ∀ i, 0 < a i) (haInj : Function.Injective a) (hrPos : ∀ i, 0 < r i)
    (hrDiv : ∀ i, r i ∣ a i) (hrProper : ∀ i, a i ≠ r i) (haM : ∀ i, a i ≤ M)
    (hx : x ∈ integerInterval L M) (hxDiv : ∀ i, (r i : ℤ) ∣ x) :
    ∃ f : Fin 5 → ℤ, Function.Injective f ∧
      ∀ i, f i ∈ properDivisorCandidates L M x r i := by
  classical
  apply exists_distinct_divisor_representatives_of_hall
  intro S
  by_cases hS : S.card ≤ 4
  · -- extend to four labels and use the banked four-label lemma
    obtain ⟨S', hSS', hS'⟩ := Finset.exists_superset_card_eq (n := 4) hS (by simp)
    let e : Fin 4 ≃ S' := (S'.equivFin.trans (finCongr hS')).symm
    obtain ⟨g, hg, hgC⟩ := proper_divisor_sdr_fin_four (L := L) (x := x) (M := M)
      (fun i => a (e i)) (fun i => r (e i)) (fun i => haPos _)
      (fun i j h => e.injective (Subtype.ext (haInj h))) (fun i => hrPos _) (fun i => hrDiv _)
      (fun i => hrProper _) (fun i => haM _) hx (fun i => hxDiv _)
    let h : Fin 5 → ℤ := fun j => if hj : j ∈ S' then g (e.symm ⟨j, hj⟩) else 0
    have hmem : ∀ j ∈ S', h j ∈ properDivisorCandidates L M x r j := by
      intro j hj
      have := hgC (e.symm ⟨j, hj⟩)
      simp only [h, hj, dite_true]
      rw [properDivisorCandidates_eq_cand] at this ⊢
      simpa using this
    have hinj : Set.InjOn h S := by
      intro j hj k hk hjk
      have hj' := hSS' hj
      have hk' := hSS' hk
      simp only [h, hj', hk', dite_true] at hjk
      have := e.symm.injective (hg hjk)
      exact congrArg Subtype.val this
    calc S.card = (S.image h).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (S.biUnion (properDivisorCandidates L M x r)).card :=
          Finset.card_le_card (fun z hz => by
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
            exact Finset.mem_biUnion.mpr ⟨j, hj, hmem j (hSS' hj)⟩)
  · -- the full family
    have hSu : S = Finset.univ := Finset.eq_univ_of_card _
      (by have := Finset.card_le_univ S; simp at this ⊢; omega)
    subst hSu
    set R := Finset.univ.image r with hR
    set R0 := R.filter (fun s => ∀ t ∈ R, t ∣ s → t = s) with hR0
    have hmin : ∀ i, ∃ s ∈ R0, s ∣ r i := by
      intro i
      let T := R.filter (fun t => t ∣ r i)
      have hT : T.Nonempty := ⟨r i, by simp [T, R]⟩
      refine ⟨T.min' hT, ?_, (Finset.mem_filter.mp (T.min'_mem hT)).2⟩
      have hm := Finset.mem_filter.mp (T.min'_mem hT)
      rw [Finset.mem_filter]
      refine ⟨hm.1, fun t ht htm => ?_⟩
      have htT : t ∈ T := Finset.mem_filter.mpr ⟨ht, htm.trans hm.2⟩
      have h1 := T.min'_le t htT
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hm.1
      have hpos' : 0 < T.min' hT := hj ▸ hrPos j
      have h2 := Nat.le_of_dvd hpos' htm
      omega
    have hR0mem : ∀ s ∈ R0, ∃ j, r j = s := by
      intro s hs
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
      exact ⟨j, hj⟩
    have hunion : Finset.univ.biUnion (properDivisorCandidates L M x r) =
        R0.biUnion (cand L M x) := by
      ext z
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, properDivisorCandidates_eq_cand]
      constructor
      · rintro ⟨i, hz⟩
        obtain ⟨s, hs, hsr⟩ := hmin i
        refine ⟨s, hs, ?_⟩
        rw [mem_cand] at hz ⊢
        exact ⟨hz.1, hz.2.1, (Int.natCast_dvd_natCast.mpr hsr).trans hz.2.2⟩
      · rintro ⟨s, hs, hz⟩
        obtain ⟨j, rfl⟩ := hR0mem s hs
        exact ⟨j, hz⟩
    rw [hunion]
    have h2r : ∀ i, 2 * r i ≤ a i := by
      intro i
      obtain ⟨c, hc⟩ := hrDiv i
      have hc0 : c ≠ 0 := by rintro rfl; have := haPos i; simp at hc; omega
      have hc1 : c ≠ 1 := by rintro rfl; exact hrProper i (by rw [hc, mul_one])
      have : 2 ≤ c := by omega
      calc 2 * r i ≤ c * r i := Nat.mul_le_mul_right _ this
        _ = a i := by rw [hc, mul_comm]
    have := five_le_card_union_of_primitive hx R0
      (fun s hs => by obtain ⟨j, rfl⟩ := hR0mem s hs; exact hrPos j)
      (fun s hs => by obtain ⟨j, rfl⟩ := hR0mem s hs; exact (h2r j).trans (haM j))
      (fun s hs => by obtain ⟨j, rfl⟩ := hR0mem s hs; exact hxDiv j)
      (fun s hs t ht hst => by
        have ht' := Finset.mem_filter.mp ht
        exact ht'.2 s (Finset.mem_filter.mp hs).1 hst)
      (Finset.univ.image a) (by rw [Finset.card_image_of_injective _ haInj]; simp)
      (fun b hb => by obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb; exact haPos j)
      (fun b hb => by
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨s, hs, hsr⟩ := hmin j
        refine ⟨haM j, s, hs, hsr.trans (hrDiv j), fun h => ?_⟩
        have h1 := Nat.le_of_dvd (hrPos j) hsr
        have h2 := h2r j
        have := hrPos j
        omega)
    simpa using this

end Erdos708.Five
