module

public import Erdos708.Five.Assign
public import Erdos708.Five.Case32

@[expose] public section

/-!
# From an assignment shape to a cover

For five originals `m : Fin 5 → ℕ` and a valid assignment `f`, each partition shape of the
occupied sites is reduced to the corresponding case theorem. The (4,1) and single-anchor
cases are taken as explicit hypotheses `Case41Statement` and `Case5Statement` here. Their
proofs are separate stages.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

/-- `T` is covered by at most `k` entries of the `M`-interval from `L`. -/
def ProdCover (L : ℤ) (M T k : ℕ) : Prop :=
  ∃ B : Finset ℤ, B ⊆ integerInterval L M ∧ B.card ≤ k ∧ (T : ℤ) ∣ ∏ z ∈ B, z

theorem prodCover_of_five {L : ℤ} {M a b c d e k T : ℕ} (h : FiveModuliCover L M a b c d e k)
    (hT : T = a * b * c * d * e) : ProdCover L M T k := by
  obtain ⟨B, hB, hcard, hdvd⟩ := h
  refine ⟨B, hB, hcard, ?_⟩
  rw [hT]; push_cast; exact hdvd

theorem prod_five {m : Fin 5 → ℕ} {i₁ i₂ i₃ i₄ i₅ : Fin 5}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄) (h15 : i₁ ≠ i₅)
    (h23 : i₂ ≠ i₃) (h24 : i₂ ≠ i₄) (h25 : i₂ ≠ i₅)
    (h34 : i₃ ≠ i₄) (h35 : i₃ ≠ i₅) (h45 : i₄ ≠ i₅) :
    ∏ i, m i = m i₁ * m i₂ * m i₃ * m i₄ * m i₅ := by
  classical
  have hS : ({i₁, i₂, i₃, i₄, i₅} : Finset (Fin 5)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14, h15]),
      Finset.card_insert_of_notMem (by simp [h23, h24, h25]),
      Finset.card_insert_of_notMem (by simp [h34, h35]), Finset.card_pair h45]
    simp
  rw [← hS, Finset.prod_insert (by simp [h12, h13, h14, h15]),
    Finset.prod_insert (by simp [h23, h24, h25]), Finset.prod_insert (by simp [h34, h35]),
    Finset.prod_pair h45]
  ring

theorem idx_five {i₁ i₂ i₃ i₄ i₅ : Fin 5}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄) (h15 : i₁ ≠ i₅)
    (h23 : i₂ ≠ i₃) (h24 : i₂ ≠ i₄) (h25 : i₂ ≠ i₅)
    (h34 : i₃ ≠ i₄) (h35 : i₃ ≠ i₅) (h45 : i₄ ≠ i₅) (j : Fin 5) :
    j = i₁ ∨ j = i₂ ∨ j = i₃ ∨ j = i₄ ∨ j = i₅ := by
  classical
  have hS : ({i₁, i₂, i₃, i₄, i₅} : Finset (Fin 5)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14, h15]),
      Finset.card_insert_of_notMem (by simp [h23, h24, h25]),
      Finset.card_insert_of_notMem (by simp [h34, h35]), Finset.card_pair h45]
    simp
  have : j ∈ ({i₁, i₂, i₃, i₄, i₅} : Finset (Fin 5)) := hS ▸ Finset.mem_univ j
  simpa using this

section

variable {L : ℤ} {M : ℕ} {m : Fin 5 → ℕ} {f : Fin 5 → ℤ}

theorem incomp_of_same (hf : ValidAssign L M m f) {i j : Fin 5} (hij : i ≠ j)
    (h : f i = f j) : ¬ m i ∣ m j := fun hd => hf.2.2 i j hij hd h

theorem dvd_site (hf : ValidAssign L M m f) {i : Fin 5} {x : ℤ} (h : f i = x) :
    (m i : ℤ) ∣ x := h ▸ hf.2.1 i

theorem site_mem (hf : ValidAssign L M m f) {i : Fin 5} {x : ℤ} (h : f i = x) :
    x ∈ integerInterval L M := h ▸ hf.1 i

/-- Shape (3,1,1). -/
theorem shape311 (hinj : Function.Injective m) (hpos : ∀ i, 0 < m i) (hle : ∀ i, m i ≤ M)
    (hf : ValidAssign L M m f) {i₁ i₂ i₃ j l : Fin 5} {x y z : ℤ}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h1j : i₁ ≠ j) (h1l : i₁ ≠ l) (h23 : i₂ ≠ i₃)
    (h2j : i₂ ≠ j) (h2l : i₂ ≠ l) (h3j : i₃ ≠ j) (h3l : i₃ ≠ l) (hjl : j ≠ l)
    (f1 : f i₁ = x) (f2 : f i₂ = x) (f3 : f i₃ = x) (fj : f j = y) (fl : f l = z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ProdCover L M (∏ i, m i) 6 := by
  have ne : ∀ {i j : Fin 5}, i ≠ j → m i ≠ m j := fun h e => h (hinj e)
  refine prodCover_of_five (case311 (site_mem hf f1) (site_mem hf fj) (site_mem hf fl) hxy hxz
    hyz (dvd_site hf f1) (dvd_site hf f2) (dvd_site hf f3) (dvd_site hf fj) (dvd_site hf fl)
    (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) (hle _) (hle _) (hle _) (hle _) (hle _)
    (ne h12) (ne h13) (ne h1j) (ne h1l) (ne h23) (ne h2j) (ne h2l) (ne h3j) (ne h3l) (ne hjl)
    (incomp_of_same hf h12 (f1.trans f2.symm)) (incomp_of_same hf h12.symm (f2.trans f1.symm))
    (incomp_of_same hf h13 (f1.trans f3.symm)) (incomp_of_same hf h13.symm (f3.trans f1.symm))
    (incomp_of_same hf h23 (f2.trans f3.symm)) (incomp_of_same hf h23.symm (f3.trans f2.symm)))
    (prod_five h12 h13 h1j h1l h23 h2j h2l h3j h3l hjl)

/-- Shape (2,2,1). -/
theorem shape221 (hinj : Function.Injective m) (hpos : ∀ i, 0 < m i) (hle : ∀ i, m i ≤ M)
    (hf : ValidAssign L M m f) {i₁ i₂ j₁ j₂ l : Fin 5} {x y z : ℤ}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ j₁) (h14 : i₁ ≠ j₂) (h15 : i₁ ≠ l) (h23 : i₂ ≠ j₁)
    (h24 : i₂ ≠ j₂) (h25 : i₂ ≠ l) (h34 : j₁ ≠ j₂) (h35 : j₁ ≠ l) (h45 : j₂ ≠ l)
    (f1 : f i₁ = x) (f2 : f i₂ = x) (f3 : f j₁ = y) (f4 : f j₂ = y) (fl : f l = z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ProdCover L M (∏ i, m i) 6 := by
  have ne : ∀ {i j : Fin 5}, i ≠ j → m i ≠ m j := fun h e => h (hinj e)
  refine prodCover_of_five (case221 (site_mem hf f1) (site_mem hf f3) (site_mem hf fl) hxy hxz
    hyz (dvd_site hf f1) (dvd_site hf f2) (dvd_site hf f3) (dvd_site hf f4) (dvd_site hf fl)
    (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) (hle _) (hle _) (hle _) (hle _) (hle _)
    (ne h12) (ne h13) (ne h14) (ne h15) (ne h23) (ne h24) (ne h25) (ne h34) (ne h35) (ne h45)
    (incomp_of_same hf h12 (f1.trans f2.symm)) (incomp_of_same hf h12.symm (f2.trans f1.symm))
    (incomp_of_same hf h34 (f3.trans f4.symm)) (incomp_of_same hf h34.symm (f4.trans f3.symm)))
    (prod_five h12 h13 h14 h15 h23 h24 h25 h34 h35 h45)

/-- Shape (3,2). -/
theorem shape32 (hinj : Function.Injective m) (hpos : ∀ i, 0 < m i) (hle : ∀ i, m i ≤ M)
    (hf : ValidAssign L M m f) {i₁ i₂ i₃ j₁ j₂ : Fin 5} {x y : ℤ}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ j₁) (h15 : i₁ ≠ j₂) (h23 : i₂ ≠ i₃)
    (h24 : i₂ ≠ j₁) (h25 : i₂ ≠ j₂) (h34 : i₃ ≠ j₁) (h35 : i₃ ≠ j₂) (h45 : j₁ ≠ j₂)
    (f1 : f i₁ = x) (f2 : f i₂ = x) (f3 : f i₃ = x) (f4 : f j₁ = y) (f5 : f j₂ = y)
    (hxy : x ≠ y) :
    ProdCover L M (∏ i, m i) 6 := by
  have ne : ∀ {i j : Fin 5}, i ≠ j → m i ≠ m j := fun h e => h (hinj e)
  refine prodCover_of_five (case32 (site_mem hf f1) (site_mem hf f4) hxy
    (dvd_site hf f1) (dvd_site hf f2) (dvd_site hf f3) (dvd_site hf f4) (dvd_site hf f5)
    (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) (hle _) (hle _) (hle _) (hle _) (hle _)
    (ne h14) (ne h24) (ne h34)
    (incomp_of_same hf h12 (f1.trans f2.symm)) (incomp_of_same hf h12.symm (f2.trans f1.symm))
    (incomp_of_same hf h13 (f1.trans f3.symm)) (incomp_of_same hf h13.symm (f3.trans f1.symm))
    (incomp_of_same hf h23 (f2.trans f3.symm)) (incomp_of_same hf h23.symm (f3.trans f2.symm))
    (incomp_of_same hf h45 (f4.trans f5.symm)) (incomp_of_same hf h45.symm (f5.trans f4.symm)))
    (prod_five h12 h13 h14 h15 h23 h24 h25 h34 h35 h45)

/-- Four or more occupied sites: the missing-one repair. -/
theorem shape_missing (hinj : Function.Injective m) (hpos : ∀ i, 0 < m i)
    (hle : ∀ i, m i ≤ M) (hf : ValidAssign L M m f)
    (hK : 4 ≤ (Finset.univ.image f).card) :
    ProdCover L M (∏ i, m i) 6 := by
  classical
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hK
  have hpre : ∀ t ∈ T, ∃ i, f i = t := by
    intro t ht
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (hTsub ht)
    exact ⟨i, hi⟩
  choose! σ hσ using hpre
  have hσinj : Set.InjOn σ T := by
    intro s hs t ht hst
    rw [← hσ s hs, ← hσ t ht, hst]
  have hσcard : (T.image σ).card = 4 := by rw [Finset.card_image_of_injOn hσinj, hTcard]
  obtain ⟨j, hj⟩ : ∃ j, j ∉ T.image σ := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset (Fin 5)) ⊆ T.image σ := fun i _ => h i
    have := Finset.card_le_card this
    simp at this
    omega
  have hlab : ∀ t ∈ T, (m (σ t) : ℤ) ∣ t := by
    intro t ht; have := hf.2.1 (σ t); rw [hσ t ht] at this; exact this
  obtain ⟨B, hB, hBcard, hBdvd⟩ := missing_one (L := L) (M := M) (m := m j) T (fun t => m (σ t))
    (fun t ht => hTsub ht |> fun h => by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h; rw [← hi]; exact hf.1 i)
    hlab
    (by intro s hs t ht hst; exact hσinj hs ht (hinj hst))
    (by
      intro t ht
      refine ⟨hpos _, hle _, fun h => hj ?_⟩
      have := hinj h
      rw [Finset.mem_image]; exact ⟨t, ht, this⟩)
    (hpos j) (hle j)
  refine ⟨B, hB, by omega, ?_⟩
  have hprod : ∏ i, m i = m j * ∏ t ∈ T, m (σ t) := by
    have hU : (Finset.univ : Finset (Fin 5)) = insert j (T.image σ) := by
      apply (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) _).symm
      rw [Finset.card_insert_of_notMem hj, hσcard]; simp
    rw [hU, Finset.prod_insert hj, Finset.prod_image (fun s hs t ht h => hσinj hs ht h)]
  rw [hprod]
  exact hBdvd

end


/-- The (4,1) case, with the two consequences of maximality used by the written proof:
every multiple of the four grouped originals lies at the two anchors, and if one of them also
divides `y` then `e` has no multiple outside the anchors. -/
def Case41Statement : Prop :=
  ∀ {L : ℤ} {M : ℕ} {x y : ℤ} {a b c d e : ℕ},
    x ∈ integerInterval L M → y ∈ integerInterval L M → x ≠ y →
    (a : ℤ) ∣ x → (b : ℤ) ∣ x → (c : ℤ) ∣ x → (d : ℤ) ∣ x → (e : ℤ) ∣ y →
    0 < a → 0 < b → 0 < c → 0 < d → 0 < e →
    a ≤ M → b ≤ M → c ≤ M → d ≤ M → e ≤ M →
    a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
    ¬ a ∣ b → ¬ b ∣ a → ¬ a ∣ c → ¬ c ∣ a → ¬ a ∣ d → ¬ d ∣ a →
    ¬ b ∣ c → ¬ c ∣ b → ¬ b ∣ d → ¬ d ∣ b → ¬ c ∣ d → ¬ d ∣ c →
    (∀ o ∈ ({a, b, c, d} : Finset ℕ), ∀ w ∈ integerInterval L M, (o : ℤ) ∣ w →
      w = x ∨ w = y) →
    (∀ o ∈ ({a, b, c, d} : Finset ℕ), (o : ℤ) ∣ y → ∀ w ∈ integerInterval L M,
      (e : ℤ) ∣ w → w = x ∨ w = y) →
    FiveModuliCover L M a b c d e 6

/-- The single-anchor case: five pairwise incomparable originals whose common interval
multiple `x` is the unique interval multiple of each (the consequence of maximality). -/
def Case5Statement : Prop :=
  ∀ {L : ℤ} {M : ℕ} {x : ℤ} {a b c d e : ℕ},
    x ∈ integerInterval L M →
    (a : ℤ) ∣ x → (b : ℤ) ∣ x → (c : ℤ) ∣ x → (d : ℤ) ∣ x → (e : ℤ) ∣ x →
    0 < a → 0 < b → 0 < c → 0 < d → 0 < e →
    a ≤ M → b ≤ M → c ≤ M → d ≤ M → e ≤ M →
    ¬ a ∣ b → ¬ b ∣ a → ¬ a ∣ c → ¬ c ∣ a → ¬ a ∣ d → ¬ d ∣ a → ¬ a ∣ e → ¬ e ∣ a →
    ¬ b ∣ c → ¬ c ∣ b → ¬ b ∣ d → ¬ d ∣ b → ¬ b ∣ e → ¬ e ∣ b →
    ¬ c ∣ d → ¬ d ∣ c → ¬ c ∣ e → ¬ e ∣ c → ¬ d ∣ e → ¬ e ∣ d →
    (∀ o ∈ ({a, b, c, d, e} : Finset ℕ), ∀ w ∈ integerInterval L M, (o : ℤ) ∣ w → w = x) →
    FiveModuliCover L M a b c d e 6

section Max

variable {L : ℤ} {M : ℕ} {m : Fin 5 → ℕ} {f : Fin 5 → ℤ}

theorem valid_update (hf : ValidAssign L M m f) {i : Fin 5} {w : ℤ}
    (hw : w ∈ integerInterval L M) (hmw : (m i : ℤ) ∣ w) (hfree : ∀ j, j ≠ i → f j ≠ w) :
    ValidAssign L M m (Function.update f i w) := by
  refine ⟨fun j => ?_, fun j => ?_, fun j k hjk hd => ?_⟩
  · by_cases h : j = i
    · subst h; simp [hw]
    · simp [Function.update, h, hf.1 j]
  · by_cases h : j = i
    · subst h; simp [hmw]
    · simp [Function.update, h, hf.2.1 j]
  · by_cases hj : j = i
    · subst hj
      have hk : k ≠ j := fun h => hjk h.symm
      simp only [Function.update, hk, dite_false, dite_true]
      exact fun h => hfree k hk h.symm
    · by_cases hk : k = i
      · subst hk
        simp only [Function.update, hj, dite_false, dite_true]
        exact hfree j hj
      · simp only [Function.update, hj, hk, dite_false]
        exact hf.2.2 j k hjk hd

/-- Shape (4,1) via maximality. -/
theorem shape41 (h41 : Case41Statement) (hinj : Function.Injective m) (hpos : ∀ i, 0 < m i)
    (hle : ∀ i, m i ≤ M) (hf : ValidAssign L M m f)
    (hmax : ∀ f', ValidAssign L M m f' →
      (Finset.univ.image f').card ≤ (Finset.univ.image f).card)
    (hK : (Finset.univ.image f).card = 2)
    {i₁ i₂ i₃ i₄ l : Fin 5} {x y : ℤ}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄) (h15 : i₁ ≠ l) (h23 : i₂ ≠ i₃)
    (h24 : i₂ ≠ i₄) (h25 : i₂ ≠ l) (h34 : i₃ ≠ i₄) (h35 : i₃ ≠ l) (h45 : i₄ ≠ l)
    (f1 : f i₁ = x) (f2 : f i₂ = x) (f3 : f i₃ = x) (f4 : f i₄ = x) (fl : f l = y)
    (hxy : x ≠ y) :
    ProdCover L M (∏ i, m i) 6 := by
  classical
  have ne : ∀ {i j : Fin 5}, i ≠ j → m i ≠ m j := fun h e => h (hinj e)
  have hall : ∀ j, f j = x ∨ f j = y := by
    intro j
    have hsub : Finset.univ.image f ⊆ {x, y} := by
      apply Finset.eq_of_subset_of_card_le (s := {x, y}) _ _ |>.symm.subset
      · intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact Finset.mem_image.mpr ⟨i₁, Finset.mem_univ _, f1⟩
        · exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, fl⟩
      · rw [hK, Finset.card_pair hxy]
    have := hsub (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    simpa using this
  -- three distinct occupied values contradict maximality
  have three : ∀ f', ValidAssign L M m f' → ∀ w, w ≠ x → w ≠ y →
      x ∈ Finset.univ.image f' → y ∈ Finset.univ.image f' → w ∈ Finset.univ.image f' → False := by
    intro f' hf' w hwx hwy hx hy hw
    have hsub : ({x, y, w} : Finset ℤ) ⊆ Finset.univ.image f' := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> assumption
    have hcard : ({x, y, w} : Finset ℤ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, Ne.symm hwx]), Finset.card_pair (Ne.symm hwy)]
    have := Finset.card_le_card hsub
    have := hmax f' hf'
    omega
  have img : ∀ (g : Fin 5 → ℤ) (j : Fin 5) (v : ℤ), g j = v → v ∈ Finset.univ.image g :=
    fun g j v h => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h⟩
  -- H1: grouped originals have no multiple outside `{x, y}`
  have H1 : ∀ i, f i = x → ∀ w ∈ integerInterval L M, (m i : ℤ) ∣ w → w = x ∨ w = y := by
    intro i hi w hw hmw
    by_contra hne
    push Not at hne
    obtain ⟨hwx, hwy⟩ := hne
    have hfree : ∀ j, j ≠ i → f j ≠ w := by
      intro j _ h
      rcases hall j with h' | h' <;> [exact hwx (h.symm.trans h'); exact hwy (h.symm.trans h')]
    have hv := valid_update hf hw hmw hfree
    -- another grouped index keeps `x`
    obtain ⟨k, hk, hkx⟩ : ∃ k, k ≠ i ∧ f k = x := by
      by_cases h : i = i₁
      · exact ⟨i₂, fun e => h12 (h ▸ e.symm), f2⟩
      · exact ⟨i₁, fun e => h (e ▸ rfl), f1⟩
    have hli : l ≠ i := by
      intro e; rw [e] at fl; exact hxy (hi.symm.trans fl)
    exact three _ hv w hwx hwy
      (img _ k x (by simp [Function.update, hk, hkx]))
      (img _ l y (by simp [Function.update, hli, fl]))
      (img _ i w (by simp))
  -- H2: a bridge forces `m l` to have no multiple outside `{x, y}`
  have H2 : ∀ i, f i = x → (m i : ℤ) ∣ y → ∀ w ∈ integerInterval L M, (m l : ℤ) ∣ w →
      w = x ∨ w = y := by
    intro i hi hiy w hw hmw
    by_contra hne
    push Not at hne
    obtain ⟨hwx, hwy⟩ := hne
    have hli : l ≠ i := by
      intro e; rw [e] at fl; exact hxy (hi.symm.trans fl)
    have hv₁ := valid_update hf hw hmw (fun j _ h => by
      rcases hall j with h' | h' <;> [exact hwx (h.symm.trans h'); exact hwy (h.symm.trans h')])
    have hv₂ := valid_update hv₁ (site_mem hf fl) hiy (fun j hj h => by
      by_cases hjl : j = l
      · subst hjl; simp at h; exact hwy h
      · simp only [Function.update, hjl, dite_false] at h
        rcases idx_five h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 j with
          rfl | rfl | rfl | rfl | rfl
        · exact hxy (f1.symm.trans h)
        · exact hxy (f2.symm.trans h)
        · exact hxy (f3.symm.trans h)
        · exact hxy (f4.symm.trans h)
        · exact hjl rfl)
    obtain ⟨k, hk, hkx⟩ : ∃ k, k ≠ i ∧ f k = x := by
      by_cases h : i = i₁
      · exact ⟨i₂, fun e => h12 (h ▸ e.symm), f2⟩
      · exact ⟨i₁, fun e => h (e ▸ rfl), f1⟩
    have hkl : k ≠ l := by intro e; rw [e] at hkx; exact hxy (hkx.symm.trans fl)
    exact three _ hv₂ w hwx hwy
      (img _ k x (by simp [Function.update, hk, hkl, hkx]))
      (img _ i y (by simp))
      (img _ l w (by simp [Function.update, hli.symm, hli]))
  refine prodCover_of_five (h41 (site_mem hf f1) (site_mem hf fl) hxy
    (dvd_site hf f1) (dvd_site hf f2) (dvd_site hf f3) (dvd_site hf f4) (dvd_site hf fl)
    (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) (hle _) (hle _) (hle _) (hle _) (hle _)
    (ne h12) (ne h13) (ne h14) (ne h15) (ne h23) (ne h24) (ne h25) (ne h34) (ne h35) (ne h45)
    (incomp_of_same hf h12 (f1.trans f2.symm)) (incomp_of_same hf h12.symm (f2.trans f1.symm))
    (incomp_of_same hf h13 (f1.trans f3.symm)) (incomp_of_same hf h13.symm (f3.trans f1.symm))
    (incomp_of_same hf h14 (f1.trans f4.symm)) (incomp_of_same hf h14.symm (f4.trans f1.symm))
    (incomp_of_same hf h23 (f2.trans f3.symm)) (incomp_of_same hf h23.symm (f3.trans f2.symm))
    (incomp_of_same hf h24 (f2.trans f4.symm)) (incomp_of_same hf h24.symm (f4.trans f2.symm))
    (incomp_of_same hf h34 (f3.trans f4.symm)) (incomp_of_same hf h34.symm (f4.trans f3.symm))
    ?_ ?_) (prod_five h12 h13 h14 h15 h23 h24 h25 h34 h35 h45)
  · intro o ho w hw how
    simp only [Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact H1 i₁ f1 w hw how
    · exact H1 i₂ f2 w hw how
    · exact H1 i₃ f3 w hw how
    · exact H1 i₄ f4 w hw how
  · intro o ho hoy w hw hew
    simp only [Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact H2 i₁ f1 hoy w hw hew
    · exact H2 i₂ f2 hoy w hw hew
    · exact H2 i₃ f3 hoy w hw hew
    · exact H2 i₄ f4 hoy w hw hew

/-- Shape (5): all five at one site; maximality makes `x` each original's unique multiple. -/
theorem shape5 (h5 : Case5Statement) (hinj : Function.Injective m) (hpos : ∀ i, 0 < m i)
    (hle : ∀ i, m i ≤ M) (hf : ValidAssign L M m f)
    (hmax : ∀ f', ValidAssign L M m f' →
      (Finset.univ.image f').card ≤ (Finset.univ.image f).card)
    {x : ℤ} (hall : ∀ i, f i = x) :
    ProdCover L M (∏ i, m i) 6 := by
  classical
  have inc : ∀ i j : Fin 5, i ≠ j → ¬ m i ∣ m j :=
    fun i j hij => incomp_of_same hf hij ((hall i).trans (hall j).symm)
  have hK : (Finset.univ.image f).card = 1 := by
    rw [Finset.card_eq_one]
    exact ⟨x, by ext t; simp [hall, eq_comm]⟩
  have uniq : ∀ i, ∀ w ∈ integerInterval L M, (m i : ℤ) ∣ w → w = x := by
    intro i w hw hmw
    by_contra hwx
    have hv := valid_update hf hw hmw (fun j _ h => hwx (h.symm.trans (hall j)))
    obtain ⟨k, hk⟩ : ∃ k : Fin 5, k ≠ i := by
      by_cases h0 : i = 0
      · exact ⟨1, by rw [h0]; decide⟩
      · exact ⟨0, fun e => h0 e.symm⟩
    have hsub : ({x, w} : Finset ℤ) ⊆ Finset.univ.image (Function.update f i w) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, by
          rw [Function.update_of_ne hk]; exact hall k⟩
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (Ne.symm hwx)] at this
    have := hmax _ hv
    omega
  refine prodCover_of_five (h5 (site_mem hf (hall 0)) (dvd_site hf (hall 0))
    (dvd_site hf (hall 1)) (dvd_site hf (hall 2)) (dvd_site hf (hall 3)) (dvd_site hf (hall 4))
    (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) (hle _) (hle _) (hle _) (hle _) (hle _)
    (inc 0 1 (by decide)) (inc 1 0 (by decide)) (inc 0 2 (by decide)) (inc 2 0 (by decide))
    (inc 0 3 (by decide)) (inc 3 0 (by decide)) (inc 0 4 (by decide)) (inc 4 0 (by decide))
    (inc 1 2 (by decide)) (inc 2 1 (by decide)) (inc 1 3 (by decide)) (inc 3 1 (by decide))
    (inc 1 4 (by decide)) (inc 4 1 (by decide)) (inc 2 3 (by decide)) (inc 3 2 (by decide))
    (inc 2 4 (by decide)) (inc 4 2 (by decide)) (inc 3 4 (by decide)) (inc 4 3 (by decide))
    ?_) (Fin.prod_univ_five m)
  intro o ho w hw how
  simp only [Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · exact uniq 0 w hw how
  · exact uniq 1 w hw how
  · exact uniq 2 w hw how
  · exact uniq 3 w hw how
  · exact uniq 4 w hw how

end Max

end Erdos708.Five
