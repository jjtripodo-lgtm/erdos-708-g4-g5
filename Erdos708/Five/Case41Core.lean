module

public import Erdos708.Five.MissingOne
public import Erdos708.Five.SDR5
public import Erdos708.Five.Shapes

@[expose] public section

/-!
# The (4,1) case: propagation core

Sources: `G5_COMPLETE_CANDIDATE.md` §7 and `FOUR_UPPER_PLUS_ONE_CANDIDATE.md`.

Four distinct originals `a i` divide the anchor `x`. Each original is split as `p i * r i`
with `2 ≤ p i`, and `∏ p i` divides `x`. The four residuals `r i` sit at distinct sites off `x`
(the banked four-label proper-divisor SDR). The fifth original `e` divides a second site
`y ≠ x`. A collision of `e` with a residual site merges the two labels into their lcm and
carries their gcd. The propagation invariant `propagate_inv` keeps a separate witness (the
original) for each residual label. The only obstruction is a residual equal to `e` coming from
the original `2e`. Hypothesis `hC` excludes it.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

/-- A fresh site finishes the propagation. -/
theorem finish_fresh {L : ℤ} {M T g : ℕ} {V U : Finset ℤ} {pay lab : ℤ → ℕ} {w : ℤ}
    (hV : V ⊆ integerInterval L M) (hUI : U ⊆ integerInterval L M) (hdisj : Disjoint V U)
    (hpay : ∀ v ∈ V, (pay v : ℤ) ∣ v) (hlab : ∀ u ∈ U, (lab u : ℤ) ∣ u)
    (hw : w ∈ integerInterval L M) (hgw : (g : ℤ) ∣ w) (hwV : w ∉ V) (hwU : w ∉ U)
    (hT : T ∣ (∏ v ∈ V, pay v) * g * ∏ u ∈ U, lab u) :
    ∃ B : Finset ℤ, B ⊆ integerInterval L M ∧ B.card ≤ V.card + U.card + 1 ∧
      (T : ℤ) ∣ ∏ z ∈ B, z := by
  classical
  have hwVU : w ∉ V ∪ U := by rw [Finset.mem_union, not_or]; exact ⟨hwV, hwU⟩
  refine ⟨insert w (V ∪ U), ?_, ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_insert, Finset.mem_union] at hz
    rcases hz with rfl | hz | hz
    · exact hw
    · exact hV hz
    · exact hUI hz
  · rw [Finset.card_insert_of_notMem hwVU, Finset.card_union_of_disjoint hdisj]
  · rw [Finset.prod_insert hwVU, Finset.prod_union hdisj]
    have h1 : ((∏ v ∈ V, pay v : ℕ) : ℤ) ∣ ∏ v ∈ V, v := by
      push_cast; exact Finset.prod_dvd_prod_of_dvd _ _ (fun v hv => hpay v hv)
    have h2 : ((∏ u ∈ U, lab u : ℕ) : ℤ) ∣ ∏ u ∈ U, u := by
      push_cast; exact Finset.prod_dvd_prod_of_dvd _ _ (fun u hu => hlab u hu)
    have hT' : (T : ℤ) ∣ ((∏ v ∈ V, pay v : ℕ) : ℤ) * (g : ℤ) * ((∏ u ∈ U, lab u : ℕ) : ℤ) := by
      exact_mod_cast hT
    refine hT'.trans ?_
    calc ((∏ v ∈ V, pay v : ℕ) : ℤ) * (g : ℤ) * ((∏ u ∈ U, lab u : ℕ) : ℤ)
        ∣ (∏ v ∈ V, v) * w * ∏ u ∈ U, u := mul_dvd_mul (mul_dvd_mul h1 hgw) h2
      _ = w * ((∏ v ∈ V, v) * ∏ u ∈ U, u) := by ring

/-- **Propagation with witnesses.** Occupied sites `U` pay labels `lab u`. Each has a witness
`wit u` (in use: the original whose residual is `lab u`). An invariant `Inv` on the set `S` of
involved witnesses and the carried debt `g` supplies, after each merge, enough multiples of the
new debt to avoid every involved site. -/
theorem propagate_inv {L : ℤ} {M : ℕ} (T : ℕ) (Inv : Finset ℕ → ℕ → Prop)
    (lab wit : ℤ → ℕ) (U₀ : Finset ℤ)
    (hpos : ∀ S g, Inv S g → 0 < g)
    (hstep : ∀ S g u, Inv S g → u ∈ U₀ → wit u ∉ S →
      Inv (insert (wit u) S) (Nat.gcd g (lab u)) ∧
        (S.card + 2) * Nat.gcd g (lab u) ≤ M) :
    ∀ (r : ℕ) (V U : Finset ℤ) (pay : ℤ → ℕ) (S : Finset ℕ) (g : ℕ),
      U.card = r → U ⊆ U₀ →
      V ⊆ integerInterval L M → U ⊆ integerInterval L M → Disjoint V U →
      (∀ v ∈ V, (pay v : ℤ) ∣ v) → (∀ u ∈ U, (lab u : ℤ) ∣ u) →
      Set.InjOn wit U → (∀ u ∈ U, wit u ∉ S) →
      Inv S g → S.card = V.card →
      (∃ w ∈ integerInterval L M, (g : ℤ) ∣ w ∧ w ∉ V) →
      T ∣ (∏ v ∈ V, pay v) * g * ∏ u ∈ U, lab u →
      ∃ B : Finset ℤ, B ⊆ integerInterval L M ∧ B.card ≤ V.card + U.card + 1 ∧
        (T : ℤ) ∣ ∏ z ∈ B, z := by
  classical
  intro r
  induction r with
  | zero =>
    intro V U pay S g hU _ hV hUI hdisj hpay hlab _ _ _ _ hfresh hT
    obtain ⟨w, hw, hgw, hwV⟩ := hfresh
    have hU0 : U = ∅ := Finset.card_eq_zero.mp hU
    exact finish_fresh hV hUI hdisj hpay hlab hw hgw hwV (by rw [hU0]; simp) hT
  | succ r ih =>
    intro V U pay S g hU hU₀ hV hUI hdisj hpay hlab hinj hwS hInv hSV hfresh hT
    obtain ⟨w, hw, hgw, hwV⟩ := hfresh
    by_cases hwU : w ∈ U
    · set b := lab w with hbdef
      have hbw : (b : ℤ) ∣ w := hlab w hwU
      obtain ⟨hInv', hcount⟩ := hstep S g w hInv (hU₀ hwU) (hwS w hwU)
      let pay' : ℤ → ℕ := Function.update pay w (Nat.lcm g b)
      have hpay'V : ∀ v ∈ V, pay' v = pay v := by
        intro v hv
        have : v ≠ w := fun h => hwV (h ▸ hv)
        simp [pay', this]
      have hpay'w : pay' w = Nat.lcm g b := by simp [pay']
      have hUe : (U.erase w).card = r := by rw [Finset.card_erase_of_mem hwU, hU]; rfl
      have hg' : 0 < Nat.gcd g b := hpos _ _ hInv'
      have hcardV : (insert w V).card + 1 = S.card + 2 := by
        rw [Finset.card_insert_of_notMem hwV, hSV]
      have hfresh' := exists_multiple_outside (L := L) (insert w V) hg' hw
        (int_dvd_trans_nat (Nat.gcd_dvd_left g b) hgw) (k := (insert w V).card)
        (by rw [hcardV]; exact hcount) le_rfl
      have key := ih (insert w V) (U.erase w) pay' (insert (wit w) S) (Nat.gcd g b) hUe
        ((Finset.erase_subset w U).trans hU₀)
        (by
          intro z hz
          rw [Finset.mem_insert] at hz
          rcases hz with rfl | hz
          · exact hw
          · exact hV hz)
        (fun z hz => hUI (Finset.mem_of_mem_erase hz))
        (by
          rw [Finset.disjoint_insert_left]
          refine ⟨Finset.notMem_erase w U, ?_⟩
          exact Finset.disjoint_of_subset_right (Finset.erase_subset w U) hdisj)
        (by
          intro v hv
          rw [Finset.mem_insert] at hv
          rcases hv with rfl | hv
          · rw [hpay'w]; exact int_lcm_dvd hgw hbw
          · rw [hpay'V v hv]; exact hpay v hv)
        (fun u hu => hlab u (Finset.mem_of_mem_erase hu))
        (hinj.mono (fun z hz => Finset.mem_of_mem_erase hz))
        (by
          intro u hu
          rw [Finset.mem_insert, not_or]
          refine ⟨fun h => ?_, hwS u (Finset.mem_of_mem_erase hu)⟩
          exact Finset.ne_of_mem_erase hu (hinj (Finset.mem_of_mem_erase hu) hwU h))
        hInv'
        (by rw [Finset.card_insert_of_notMem (hwS w hwU), Finset.card_insert_of_notMem hwV, hSV])
        hfresh'
        (by
          rw [Finset.prod_insert hwV, hpay'w, Finset.prod_congr rfl hpay'V]
          have hsplit : ∏ u ∈ U, lab u = b * ∏ u ∈ U.erase w, lab u :=
            (Finset.mul_prod_erase U lab hwU).symm
          rw [hsplit] at hT
          have hgl := Nat.gcd_mul_lcm g b
          calc T ∣ (∏ v ∈ V, pay v) * g * (b * ∏ u ∈ U.erase w, lab u) := hT
            _ = (∏ v ∈ V, pay v) * (g * b) * ∏ u ∈ U.erase w, lab u := by ring
            _ = (∏ v ∈ V, pay v) * (Nat.gcd g b * Nat.lcm g b) * ∏ u ∈ U.erase w, lab u := by
                rw [hgl]
            _ = Nat.lcm g b * (∏ v ∈ V, pay v) * Nat.gcd g b * ∏ u ∈ U.erase w, lab u := by
                ring)
      obtain ⟨B, hB, hBcard, hBdvd⟩ := key
      refine ⟨B, hB, ?_, hBdvd⟩
      rw [Finset.card_insert_of_notMem hwV, Finset.card_erase_of_mem hwU] at hBcard
      have : 0 < U.card := Finset.card_pos.mpr ⟨w, hwU⟩
      omega
    · exact finish_fresh hV hUI hdisj hpay hlab hw hgw hwV hwU hT

/-- **(4,1) core.** Four distinct originals at `x`, split as `p i * r i` with `2 ≤ p i` and
`∏ p i ∣ x`, and a fifth original `e` at `y ≠ x`. If no original `2e` has residual divisible by
`e`, six sites cover `e * ∏ a i`. -/
theorem case41_core {L x y : ℤ} {M e : ℕ} (a p : Fin 4 → ℕ)
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M) (hxy : x ≠ y)
    (haPos : ∀ i, 0 < a i) (haInj : Function.Injective a) (haM : ∀ i, a i ≤ M)
    (hax : ∀ i, (a i : ℤ) ∣ x)
    (hpa : ∀ i, p i ∣ a i) (hp2 : ∀ i, 2 ≤ p i) (hPx : ((∏ i, p i : ℕ) : ℤ) ∣ x)
    (he0 : 0 < e) (heM : e ≤ M) (hea : ∀ i, a i ≠ e) (hey : (e : ℤ) ∣ y)
    (hC : ∀ i, a i = 2 * e → ¬ e ∣ a i / p i) :
    ProdCover L M (e * ∏ i, a i) 6 := by
  classical
  set r : Fin 4 → ℕ := fun i => a i / p i with hrdef
  have hpr : ∀ i, p i * r i = a i := fun i => Nat.mul_div_cancel' (hpa i)
  have hrPos : ∀ i, 0 < r i := by
    intro i
    rcases Nat.eq_zero_or_pos (r i) with h | h
    · have := hpr i; rw [h, mul_zero] at this; have := haPos i; omega
    · exact h
  have h2r : ∀ i, 2 * r i ≤ a i := fun i => by
    rw [← hpr i]; exact Nat.mul_le_mul_right _ (hp2 i)
  have hrDiv : ∀ i, r i ∣ a i := fun i => ⟨p i, by rw [← hpr i, mul_comm]⟩
  have hrProper : ∀ i, a i ≠ r i := fun i h => by
    have := h2r i; have := hrPos i; omega
  obtain ⟨b, hb, hbC⟩ := proper_divisor_sdr_fin_four (L := L) (x := x) (M := M) a r haPos haInj
    hrPos hrDiv hrProper haM hx (fun i => int_dvd_trans_nat (hrDiv i) (hax i))
  have hbmem : ∀ i, b i ∈ integerInterval L M ∧ b i ≠ x ∧ (r i : ℤ) ∣ b i := fun i => by
    have := hbC i; rw [properDivisorCandidates_eq_cand, mem_cand] at this; exact this
  -- labels and witnesses on the residual sites
  let idx : ℤ → Fin 4 := fun z => if h : ∃ i, b i = z then h.choose else 0
  have hidx : ∀ i, idx (b i) = i := by
    intro i
    have h : ∃ j, b j = b i := ⟨i, rfl⟩
    simp only [idx, h, dite_true]
    exact hb h.choose_spec
  let lab : ℤ → ℕ := fun z => r (idx z)
  let wit : ℤ → ℕ := fun z => a (idx z)
  set U₀ : Finset ℤ := Finset.univ.image b with hU₀
  have hmemU : ∀ {u}, u ∈ U₀ → ∃ i, b i = u := by
    intro u hu; obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hu; exact ⟨i, hi⟩
  let Inv : Finset ℕ → ℕ → Prop := fun S g =>
    0 < g ∧ g ∣ e ∧ e ∈ S ∧ (∀ s ∈ S, g ∣ s ∧ 0 < s ∧ s ≤ M) ∧
      (∀ s ∈ S, s ≠ e → (∃ i, a i = s) ∧ 2 * g ≤ s) ∧ (g = e → 2 * e ∉ S)
  have hstep : ∀ S g u, Inv S g → u ∈ U₀ → wit u ∉ S →
      Inv (insert (wit u) S) (Nat.gcd g (lab u)) ∧ (S.card + 2) * Nat.gcd g (lab u) ≤ M := by
    intro S g u hInv hu hwS
    obtain ⟨i, rfl⟩ := hmemU hu
    simp only [wit, lab, hidx] at hwS ⊢
    obtain ⟨hg, hge, heS, hSb, hSa, hS2⟩ := hInv
    set g' := Nat.gcd g (r i) with hg'def
    have hg'0 : 0 < g' := Nat.gcd_pos_of_pos_left _ hg
    have hg'g : g' ∣ g := Nat.gcd_dvd_left _ _
    have hg'r : g' ∣ r i := Nat.gcd_dvd_right _ _
    have hg'le : g' ≤ g := Nat.le_of_dvd hg hg'g
    have hge' : g ≤ e := Nat.le_of_dvd he0 hge
    have hg're : g' ≤ r i := Nat.le_of_dvd (hrPos i) hg'r
    have hnot2 : g' = e → 2 * e ∉ insert (a i) S := by
      intro hge2 hmem
      have hgeq : g = e := by omega
      rw [Finset.mem_insert] at hmem
      rcases hmem with h | h
      · exact hC i h.symm (hge2 ▸ hg'r)
      · exact hS2 hgeq h
    have hInv' : Inv (insert (a i) S) g' := by
      refine ⟨hg'0, hg'g.trans hge, Finset.mem_insert_of_mem heS, ?_, ?_, hnot2⟩
      · intro s hs
        rw [Finset.mem_insert] at hs
        rcases hs with rfl | hs
        · exact ⟨hg'r.trans (hrDiv i), haPos i, haM i⟩
        · obtain ⟨h1, h2, h3⟩ := hSb s hs
          exact ⟨hg'g.trans h1, h2, h3⟩
      · intro s hs hse
        rw [Finset.mem_insert] at hs
        rcases hs with rfl | hs
        · exact ⟨⟨i, rfl⟩, by have := h2r i; omega⟩
        · obtain ⟨h1, h2⟩ := hSa s hs hse
          exact ⟨h1, by omega⟩
    refine ⟨hInv', ?_⟩
    -- count: the involved witnesses plus one extra multiple of `g'`
    have hS'b : ∀ s ∈ insert (a i) S, g' ∣ s ∧ 0 < s ∧ s ≤ M := hInv'.2.2.2.1
    have hcard' : (insert (a i) S).card = S.card + 1 := Finset.card_insert_of_notMem hwS
    by_cases hge2 : g' = e
    · have hnm := hnot2 hge2
      have h2eM : 2 * e ≤ M := by have := h2r i; have := haM i; omega
      have := card_mul_le_of_multiples hg'0 (S := insert (2 * e) (insert (a i) S)) (M := M)
        (by
          intro m hm
          rw [Finset.mem_insert] at hm
          rcases hm with rfl | hm
          · exact ⟨hge2 ▸ Dvd.intro_left 2 rfl, by omega, h2eM⟩
          · exact hS'b m hm)
      rw [Finset.card_insert_of_notMem hnm, hcard'] at this
      linarith
    · have hnm : g' ∉ insert (a i) S := by
        intro hm
        have := hInv'.2.2.2.2.1 g' hm hge2
        omega
      have := card_mul_le_of_multiples hg'0 (S := insert g' (insert (a i) S)) (M := M)
        (by
          intro m hm
          rw [Finset.mem_insert] at hm
          rcases hm with rfl | hm
          · exact ⟨dvd_rfl, hg'0, by have := hg'g.trans hge; have := Nat.le_of_dvd he0 this; omega⟩
          · exact hS'b m hm)
      rw [Finset.card_insert_of_notMem hnm, hcard'] at this
      linarith
  have hpos : ∀ S g, Inv S g → 0 < g := fun S g h => h.1
  have hU0card : U₀.card = 4 := by rw [hU₀, Finset.card_image_of_injective _ hb]; simp
  have hxU : x ∉ U₀ := by
    intro h; obtain ⟨i, hi⟩ := hmemU h; exact (hbmem i).2.1 hi
  have hres := propagate_inv (L := L) (M := M) (e * ∏ i, a i) Inv lab wit U₀ hpos hstep 4
    {x} U₀ (fun _ => ∏ i, p i) {e} e hU0card subset_rfl
    (by intro z hz; rw [Finset.mem_singleton] at hz; rw [hz]; exact hx)
    (by intro z hz; obtain ⟨i, rfl⟩ := hmemU hz; exact (hbmem i).1)
    (Finset.disjoint_singleton_left.mpr hxU)
    (by intro v hv; rw [Finset.mem_singleton] at hv; rw [hv]; exact hPx)
    (by intro u hu; obtain ⟨i, rfl⟩ := hmemU hu; simp only [lab, hidx]; exact (hbmem i).2.2)
    (by
      intro u hu v hv huv
      obtain ⟨i, rfl⟩ := hmemU hu
      obtain ⟨j, rfl⟩ := hmemU hv
      simp only [wit, hidx] at huv
      rw [haInj huv])
    (by
      intro u hu
      obtain ⟨i, rfl⟩ := hmemU hu
      simp only [wit, hidx, Finset.mem_singleton]
      exact hea i)
    ⟨he0, dvd_rfl, Finset.mem_singleton_self e,
      (by intro s hs; rw [Finset.mem_singleton] at hs; subst hs; exact ⟨dvd_rfl, he0, heM⟩),
      (by intro s hs hse; rw [Finset.mem_singleton] at hs; exact absurd hs hse),
      (by intro _ h; rw [Finset.mem_singleton] at h; omega)⟩
    (by simp)
    ⟨y, hy, hey, by rw [Finset.mem_singleton]; exact fun h => hxy h.symm⟩
    (by
      rw [Finset.prod_singleton, hU₀, Finset.prod_image (fun i _ j _ h => hb h)]
      simp only [lab, hidx]
      have : ∏ i, a i = (∏ i, p i) * ∏ i, r i := by
        rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _ => (hpr i).symm)
      rw [this]
      exact ⟨1, by ring⟩)
  obtain ⟨B, hB, hBcard, hBdvd⟩ := hres
  refine ⟨B, hB, ?_, hBdvd⟩
  rw [Finset.card_singleton, hU0card] at hBcard
  exact hBcard

end Erdos708.Five
