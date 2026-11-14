module

public import Erdos708.Five.SiteArith
public import Erdos708.InitialMultiple

@[expose] public section

/-!
# The missing-one repair (Lemma 1 of the g(4) source)

If all but one of finitely many distinct positive moduli at most `M` sit at distinct interval
multiples, then one more site suffices: the full product is covered by at most (number of
moduli) sites. The proof is the gcd/lcm propagation. A collision with an occupied site merges
the two labels into their lcm and carries their gcd forward. The involved originals are
distinct multiples of the carried gcd, so a fresh multiple always exists.

This is proved here for arbitrary finite families. The five-modulus argument uses it when four or
five anchors are occupied.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

/-- `n` distinct positive multiples of `g` that are at most `M` force `n g ≤ M`. -/
theorem card_mul_le_of_multiples {S : Finset ℕ} {g M : ℕ} (hg : 0 < g)
    (hS : ∀ m ∈ S, g ∣ m ∧ 0 < m ∧ m ≤ M) : S.card * g ≤ M := by
  classical
  have hinj : Set.InjOn (fun m => m / g) S := by
    intro m hm n hn hmn
    obtain ⟨s, rfl⟩ := (hS m hm).1
    obtain ⟨t, rfl⟩ := (hS n hn).1
    simp only [Nat.mul_div_cancel_left _ hg] at hmn
    rw [hmn]
  have hmaps : ∀ m ∈ S, m / g ∈ Finset.Icc 1 (M / g) := by
    intro m hm
    obtain ⟨hgm, hm0, hmM⟩ := hS m hm
    rw [Finset.mem_Icc]
    constructor
    · exact (Nat.le_div_iff_mul_le hg).mpr (by rw [one_mul]; exact Nat.le_of_dvd hm0 hgm)
    · exact Nat.div_le_div_right hmM
  have hcard : S.card ≤ M / g := by
    calc S.card = (S.image (fun m => m / g)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 (M / g)).card := Finset.card_le_card (fun y hy => by
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
          exact hmaps m hm)
      _ = M / g := by simp
  calc S.card * g ≤ M / g * g := Nat.mul_le_mul_right g hcard
    _ ≤ M := Nat.div_mul_le_self M g

/-- **Propagation invariant.** Involved sites `V` carry payments `pay`; uninvolved occupied
sites `U` carry original labels `lab`; the carried debt `g` divides every involved original in
`S`, with `|S| = |V| + 1`. Then at most `|V| + |U| + 1` sites cover `T`. -/
theorem propagate {L : ℤ} {M : ℕ} (T : ℕ) :
    ∀ (r : ℕ) (V U : Finset ℤ) (pay lab : ℤ → ℕ) (S : Finset ℕ) (g : ℕ) (p : ℤ),
      U.card = r →
      V ⊆ integerInterval L M → U ⊆ integerInterval L M → Disjoint V U →
      (∀ v ∈ V, (pay v : ℤ) ∣ v) → (∀ u ∈ U, (lab u : ℤ) ∣ u) →
      Set.InjOn lab U → (∀ u ∈ U, 0 < lab u ∧ lab u ≤ M ∧ lab u ∉ S) →
      0 < g → (∀ m ∈ S, g ∣ m ∧ 0 < m ∧ m ≤ M) → S.card = V.card + 1 →
      p ∈ integerInterval L M → (g : ℤ) ∣ p →
      T ∣ (∏ v ∈ V, pay v) * g * ∏ u ∈ U, lab u →
      ∃ B : Finset ℤ, B ⊆ integerInterval L M ∧ B.card ≤ V.card + U.card + 1 ∧
        (T : ℤ) ∣ ∏ z ∈ B, z := by
  classical
  intro r
  induction r with
  | zero =>
    intro V U pay lab S g p hU hV hUI hdisj hpay hlab hinj hlabS hg hS hSV hp hgp hT
    have hU0 : U = ∅ := Finset.card_eq_zero.mp hU
    subst hU0
    have hM : (V.card + 1) * g ≤ M := by
      rw [← hSV]; exact card_mul_le_of_multiples hg hS
    obtain ⟨w, hw, hgw, hwV⟩ := exists_multiple_outside V hg hp hgp (k := V.card) hM le_rfl
    refine ⟨insert w V, ?_, ?_, ?_⟩
    · intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact hw
      · exact hV hz
    · rw [Finset.card_insert_of_notMem hwV]; simp
    · rw [Finset.prod_insert hwV]
      simp only [Finset.prod_empty, mul_one] at hT
      have h1 : ((∏ v ∈ V, pay v : ℕ) : ℤ) ∣ ∏ v ∈ V, v := by
        push_cast
        exact Finset.prod_dvd_prod_of_dvd _ _ (fun v hv => hpay v hv)
      have h2 := mul_dvd_mul hgw h1
      have hT' : (T : ℤ) ∣ ((∏ v ∈ V, pay v : ℕ) : ℤ) * (g : ℤ) := by exact_mod_cast hT
      exact hT'.trans (by rw [mul_comm]; exact h2)
  | succ r ih =>
    intro V U pay lab S g p hU hV hUI hdisj hpay hlab hinj hlabS hg hS hSV hp hgp hT
    have hM : (V.card + 1) * g ≤ M := by
      rw [← hSV]; exact card_mul_le_of_multiples hg hS
    obtain ⟨w, hw, hgw, hwV⟩ := exists_multiple_outside V hg hp hgp (k := V.card) hM le_rfl
    by_cases hwU : w ∈ U
    · -- collision with an occupied site: merge and propagate
      set b := lab w with hbdef
      obtain ⟨hb0, hbM, hbS⟩ := hlabS w hwU
      have hbw : (b : ℤ) ∣ w := hlab w hwU
      let pay' : ℤ → ℕ := Function.update pay w (Nat.lcm g b)
      have hpay'V : ∀ v ∈ V, pay' v = pay v := by
        intro v hv
        have : v ≠ w := fun h => hwV (h ▸ hv)
        simp [pay', this]
      have hpay'w : pay' w = Nat.lcm g b := by simp [pay']
      have hUe : (U.erase w).card = r := by rw [Finset.card_erase_of_mem hwU, hU]; rfl
      have key := ih (insert w V) (U.erase w) pay' lab (insert b S) (Nat.gcd g b) w hUe
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
          obtain ⟨h1, h2, h3⟩ := hlabS u (Finset.mem_of_mem_erase hu)
          refine ⟨h1, h2, ?_⟩
          rw [Finset.mem_insert, not_or]
          refine ⟨fun h => ?_, h3⟩
          have hune : u ≠ w := Finset.ne_of_mem_erase hu
          exact hune (hinj (Finset.mem_of_mem_erase hu) hwU h))
        (Nat.gcd_pos_of_pos_left b hg)
        (by
          intro m hm
          rw [Finset.mem_insert] at hm
          rcases hm with rfl | hm
          · exact ⟨Nat.gcd_dvd_right g _, hb0, hbM⟩
          · obtain ⟨h1, h2, h3⟩ := hS m hm
            exact ⟨(Nat.gcd_dvd_left g b).trans h1, h2, h3⟩)
        (by rw [Finset.card_insert_of_notMem hbS, Finset.card_insert_of_notMem hwV, hSV])
        hw (int_dvd_trans_nat (Nat.gcd_dvd_left g b) hgw)
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
    · -- a fresh site finishes
      refine ⟨insert w (V ∪ U), ?_, ?_, ?_⟩
      · intro z hz
        rw [Finset.mem_insert, Finset.mem_union] at hz
        rcases hz with rfl | hz | hz
        · exact hw
        · exact hV hz
        · exact hUI hz
      · have hwVU : w ∉ V ∪ U := by
          rw [Finset.mem_union, not_or]; exact ⟨hwV, hwU⟩
        rw [Finset.card_insert_of_notMem hwVU, Finset.card_union_of_disjoint hdisj]
      · have hwVU : w ∉ V ∪ U := by
          rw [Finset.mem_union, not_or]; exact ⟨hwV, hwU⟩
        rw [Finset.prod_insert hwVU, Finset.prod_union hdisj]
        have h1 : ((∏ v ∈ V, pay v : ℕ) : ℤ) ∣ ∏ v ∈ V, v := by
          push_cast
          exact Finset.prod_dvd_prod_of_dvd _ _ (fun v hv => hpay v hv)
        have h2 : ((∏ u ∈ U, lab u : ℕ) : ℤ) ∣ ∏ u ∈ U, u := by
          push_cast
          exact Finset.prod_dvd_prod_of_dvd _ _ (fun u hu => hlab u hu)
        have hT' : (T : ℤ) ∣ ((∏ v ∈ V, pay v : ℕ) : ℤ) * (g : ℤ) *
            ((∏ u ∈ U, lab u : ℕ) : ℤ) := by exact_mod_cast hT
        refine hT'.trans ?_
        have := mul_dvd_mul (mul_dvd_mul h1 hgw) h2
        calc ((∏ v ∈ V, pay v : ℕ) : ℤ) * (g : ℤ) * ((∏ u ∈ U, lab u : ℕ) : ℤ)
            = ((∏ v ∈ V, pay v : ℕ) : ℤ) * (g : ℤ) * ((∏ u ∈ U, lab u : ℕ) : ℤ) := rfl
          _ ∣ (∏ v ∈ V, v) * w * ∏ u ∈ U, u := by
              have := mul_dvd_mul (mul_dvd_mul h1 hgw) h2; exact this
          _ = w * ((∏ v ∈ V, v) * ∏ u ∈ U, u) := by ring

/-- **Missing-one repair.** Occupied distinct sites `U` carry distinct original labels; one
further original `m` (distinct from the labels, positive, at most `M`) is unplaced. Then
`|U| + 1` sites cover `m * ∏ labels`. -/
theorem missing_one {L : ℤ} {M m : ℕ} (U : Finset ℤ) (lab : ℤ → ℕ)
    (hUI : U ⊆ integerInterval L M) (hlab : ∀ u ∈ U, (lab u : ℤ) ∣ u)
    (hinj : Set.InjOn lab U) (hlabS : ∀ u ∈ U, 0 < lab u ∧ lab u ≤ M ∧ lab u ≠ m)
    (hm0 : 0 < m) (hmM : m ≤ M) :
    ∃ B : Finset ℤ, B ⊆ integerInterval L M ∧ B.card ≤ U.card + 1 ∧
      ((m * ∏ u ∈ U, lab u : ℕ) : ℤ) ∣ ∏ z ∈ B, z := by
  classical
  obtain ⟨p, hp, hmp⟩ := exists_interval_multiple_of_le_candidate (L := L) hm0 hmM
  have := propagate (L := L) (M := M) (m * ∏ u ∈ U, lab u) U.card ∅ U (fun _ => 1) lab {m} m p
    rfl (Finset.empty_subset _) hUI (Finset.disjoint_empty_left _) (by simp) hlab hinj
    (by
      intro u hu
      obtain ⟨h1, h2, h3⟩ := hlabS u hu
      exact ⟨h1, h2, by simpa using h3⟩)
    hm0 (by intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact ⟨dvd_rfl, hm0, hmM⟩)
    (by simp) hp hmp (by simp)
  simpa using this

end Erdos708.Five
