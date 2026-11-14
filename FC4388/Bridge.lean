module

public import Erdos708Statement
public import Adapter

/-!
# g(4) = 5 and g(5) = 6 for the definitions of Formal Conjectures PR #4388

`HasCoveringSize` uses a `Finset ℕ` of moduli, natural products and windows
`Finset.Ico m (m + max A)` with `0 < m`. The owner development (`Erdos708Finite`) uses
an injective enumeration `Fin n → ℕ`, integer starts and integer products. The upper
bound transfers by enumerating `A` in increasing order and restricting to positive starts.
The lower bound uses the same explicit instances, which start at positive integers.
-/

@[expose] public section

namespace Erdos708

open scoped BigOperators

/-- Every at-most cover for all integer starts gives a `HasCoveringSize` cover. -/
theorem hasCoveringSize_of_coverBound {n k : ℕ} (h : Erdos708Finite.CoverBound n k) :
    HasCoveringSize n k := by
  classical
  intro A hA h2 m hm
  set e := A.orderEmbOfFin hA
  have himg : Finset.univ.image (fun i => e i) = A := A.image_orderEmbOfFin_univ hA
  have hinj : Function.Injective (fun i => e i) := e.injective
  have hmem (i : Fin n) : e i ∈ A := A.orderEmbOfFin_mem hA i
  obtain ⟨B, hB, hc, hd⟩ := h (fun i => e i) hinj (fun i => h2 _ (hmem i)) (m : ℤ)
  have hsup : Finset.univ.sup (fun i => e i) = A.sup id := by
    rw [← himg, Finset.sup_image]; rfl
  rw [hsup] at hB
  have hpos : ∀ z ∈ B, (m : ℤ) ≤ z := fun z hz => by
    have := hB hz
    simp only [Erdos708Finite.interval, Finset.mem_Icc] at this
    exact this.1
  refine ⟨B.image Int.toNat, ?_, (Finset.card_image_le).trans hc, ?_⟩
  · intro b hb
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
    have := hB hz
    simp only [Erdos708Finite.interval, Finset.mem_Icc] at this
    simp only [Finset.mem_Ico]
    omega
  · have hinjB : Set.InjOn Int.toNat (B : Set ℤ) := by
      intro x hx y hy hxy
      have := hpos x hx; have := hpos y hy
      omega
    rw [← Int.natCast_dvd_natCast]
    have hprodA : ((∏ a ∈ A, a : ℕ) : ℤ) = ∏ i, ((e i : ℕ) : ℤ) := by
      rw [← himg, Finset.prod_image (fun x _ y _ hxy => hinj hxy)]
      push_cast; rfl
    have hprodB : ((∏ b ∈ B.image Int.toNat, b : ℕ) : ℤ) = ∏ z ∈ B, z := by
      rw [Finset.prod_image hinjB]
      push_cast
      refine Finset.prod_congr rfl fun z hz => ?_
      have := hpos z hz
      omega
    rw [hprodA, hprodB]
    exact hd

theorem hasCoveringSize_mono {n k l : ℕ} (h : k ≤ l) (hk : HasCoveringSize n k) :
    HasCoveringSize n l := by
  intro A hA h2 m hm
  obtain ⟨B, hB, hc, hd⟩ := hk A hA h2 m hm
  exact ⟨B, hB, hc.trans h, hd⟩

/-- The four-modulus instance `{77, 91, 139, 143}` at the window starting at `5935`. -/
theorem not_hasCoveringSize_four_four : ¬ HasCoveringSize 4 4 := by
  classical
  intro h
  obtain ⟨B, hB, hc, hd⟩ := h {77, 91, 139, 143} (by decide) (by decide) 5935 (by decide)
  have hsup : ({77, 91, 139, 143} : Finset ℕ).sup id = 143 := by decide
  rw [hsup] at hB
  apply Erdos708.sharp_full_no_four_cover (B.image (fun b : ℕ => (b : ℤ)))
  · intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    have := hB hb
    simp only [Finset.mem_Ico] at this
    simp only [Erdos708.sharpInterval, Erdos708.mem_integerInterval]
    omega
  · exact Finset.card_image_le.trans hc
  · rw [Finset.prod_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
    have hd' := Int.natCast_dvd_natCast.mpr hd
    push_cast at hd'
    simpa [Erdos708.sharpFullTarget, Finset.prod_insert, mul_assoc] using hd'

/-- The five-modulus instance `{5, 10, 12, 15, 20}` at the window starting at `51`. -/
theorem not_hasCoveringSize_five_five : ¬ HasCoveringSize 5 5 := by
  classical
  intro h
  obtain ⟨B, hB, hc, hd⟩ := h {5, 10, 12, 15, 20} (by decide) (by decide) 51 (by decide)
  have hsup : ({5, 10, 12, 15, 20} : Finset ℕ).sup id = 20 := by decide
  rw [hsup] at hB
  apply Erdos708.sharp5_no_five_cover
  refine ⟨B.image (fun b : ℕ => (b : ℤ)), ?_, Finset.card_image_le.trans hc, ?_⟩
  · intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    have := hB hb
    simp only [Finset.mem_Ico] at this
    simp only [Erdos708.mem_integerInterval]
    omega
  · rw [Finset.prod_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
    have hd' := Int.natCast_dvd_natCast.mpr hd
    push_cast at hd'
    simpa [Finset.prod_insert, mul_assoc] using hd'

theorem isLeast_four : IsLeast {k | HasCoveringSize 4 k} 5 :=
  ⟨hasCoveringSize_of_coverBound Erdos708Finite.four_upper, fun _ hk => by
    by_contra hlt
    exact not_hasCoveringSize_four_four (hasCoveringSize_mono (by omega) hk)⟩

theorem isLeast_five : IsLeast {k | HasCoveringSize 5 k} 6 :=
  ⟨hasCoveringSize_of_coverBound Erdos708Finite.five_upper, fun _ hk => by
    by_contra hlt
    exact not_hasCoveringSize_five_five (hasCoveringSize_mono (by omega) hk)⟩

/-- $g(4) = 5$, in the form of PR #4388. -/
theorem erdos_708.variants.g_four (g : ℕ → ℕ) (hg : IsMinCoveringSize g) : g 4 = 5 :=
  (hg 4).unique isLeast_four

/-- $g(5) = 6$, in the form of PR #4388. -/
theorem erdos_708.variants.g_five (g : ℕ → ℕ) (hg : IsMinCoveringSize g) : g 5 = 6 :=
  (hg 5).unique isLeast_five

end Erdos708

#print axioms Erdos708.erdos_708.variants.g_four
#print axioms Erdos708.erdos_708.variants.g_five
