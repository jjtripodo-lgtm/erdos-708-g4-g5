module

public import Erdos708.Five.Case41Core
public import Erdos708.Five.Case41Reserve

@[expose] public section

/-!
# The (4,1) case

Source: `G5_COMPLETE_CANDIDATE.md` §7 and `FOUR_UPPER_PLUS_ONE_CANDIDATE.md`.

Four pairwise incomparable originals at `x`, the fifth original `e` at `y ≠ x`, with the
maximality consequences of `Case41Statement`. If no original equals `2e`, any distinct prime
units work (`case41_core`). If `2e` is an original, then `e ∣ x`. A bridge original (dividing
`x` and `y`) would then equal `e`, because both would be confined to `{x, y}`. So all four
originals have the unique multiple `x` and lie in the upper half. The reserve-or-odd-unit lemma
gives a split in which the residual of `2e` is not a multiple of `e`.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

/-- A positive modulus dividing both `x` and `y`, with all interval multiples in `{x, y}`, is
`|x - y|`. -/
theorem eq_abs_of_confined_two {L x y : ℤ} {M o : ℕ} (ho : 0 < o)
    (hx : x ∈ integerInterval L M) (hy : y ∈ integerInterval L M) (hxy : x ≠ y)
    (hox : (o : ℤ) ∣ x) (hoy : (o : ℤ) ∣ y)
    (hconf : ∀ w ∈ integerInterval L M, (o : ℤ) ∣ w → w = x ∨ w = y) :
    (o : ℤ) = |x - y| := by
  have hd : (o : ℤ) ∣ x - y := dvd_sub hox hoy
  have hle : (o : ℤ) ≤ |x - y| :=
    Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hxy)) ((dvd_abs _ _).mpr hd)
  by_contra hne
  have hlt : (o : ℤ) < |x - y| := lt_of_le_of_ne hle hne
  have ho' : (0 : ℤ) < o := by exact_mod_cast ho
  rw [mem_integerInterval] at hx hy
  rcases lt_or_gt_of_ne hxy with h | h
  · have habs : |x - y| = y - x := by rw [abs_sub_comm, abs_of_pos (by linarith)]
    have hw : x + o ∈ integerInterval L M := by
      rw [mem_integerInterval]; constructor <;> linarith
    rcases hconf (x + o) hw (dvd_add hox dvd_rfl) with h1 | h1 <;> linarith
  · have habs : |x - y| = x - y := abs_of_pos (by linarith)
    have hw : y + o ∈ integerInterval L M := by
      rw [mem_integerInterval]; constructor <;> linarith
    rcases hconf (y + o) hw (dvd_add hoy dvd_rfl) with h1 | h1 <;> linarith

/-- **The (4,1) case.** -/
theorem case41_holds : Case41Statement := by
  intro L M x y a b c d e hx hy hxy hax hbx hcx hdx hey ha0 hb0 hc0 hd0 he0 haM hbM hcM hdM heM
    hab hac had hae hbc hbd hbe hcd hce hde iab iba iac ica iad ida ibc icb ibd idb icd idc H1 H2
  classical
  let m : Fin 4 → ℕ := ![a, b, c, d]
  have hm0 : ∀ i, 0 < m i := by intro i; fin_cases i <;> simpa [m]
  have hmM : ∀ i, m i ≤ M := by intro i; fin_cases i <;> simpa [m]
  have hmx : ∀ i, (m i : ℤ) ∣ x := by intro i; fin_cases i <;> simpa [m]
  have hme : ∀ i, m i ≠ e := by intro i; fin_cases i <;> simpa [m]
  have hmS : ∀ i, m i ∈ ({a, b, c, d} : Finset ℕ) := by intro i; fin_cases i <;> simp [m]
  have hinc : ∀ i j, i ≠ j → ¬ m i ∣ m j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [m] at hij ⊢ <;> assumption
  have hinj : Function.Injective m := by
    intro i j h; by_contra hij; exact hinc i j hij (h ▸ dvd_rfl)
  have hm2 : ∀ i, 2 ≤ m i := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin 4, j ≠ i := by fin_cases i <;> decide
    by_contra h
    have h1 : m i = 1 := by have := hm0 i; omega
    exact hinc i j (Ne.symm hj) (by rw [h1]; exact one_dvd _)
  have hT : e * ∏ i, m i = a * b * c * d * e := by
    simp [m, Fin.prod_univ_four]
    ring
  have hL : ((Finset.univ.lcm m : ℕ) : ℤ) ∣ x :=
    Int.natCast_dvd.mpr (Finset.lcm_dvd (fun i _ => Int.natCast_dvd.mp (hmx i)))
  by_cases h2e : ∃ k, m k = 2 * e
  · obtain ⟨k, hk⟩ := h2e
    have hek : (e : ℤ) ∣ x :=
      (Int.natCast_dvd_natCast.mpr ⟨2, by rw [hk, mul_comm]⟩).trans (hmx k)
    have hnobridge : ∀ i, ¬ (m i : ℤ) ∣ y := by
      intro i hiy
      have h1 := eq_abs_of_confined_two (hm0 i) hx hy hxy (hmx i) hiy (H1 _ (hmS i))
      have h2 := eq_abs_of_confined_two he0 hx hy hxy hek hey (H2 _ (hmS i) hiy)
      exact hme i (by exact_mod_cast h1.trans h2.symm)
    have hhalf : ∀ i, M < 2 * m i := by
      intro i
      by_contra h; push Not at h
      obtain ⟨w, hw, hdw, hwx⟩ := exists_multiple_outside (L := L) {x} (hm0 i) hx (hmx i)
        (k := 1) (by omega) (by simp)
      rcases H1 _ (hmS i) w hw hdw with rfl | rfl
      · exact hwx (Finset.mem_singleton_self _)
      · exact hnobridge i hdw
    obtain ⟨p, hpa, hp2, hpL, hpk⟩ := reserve m k hk hm2 hinc hmM hhalf
    refine fiveCover_of_prodCover (case41_core m p hx hy hxy hm0 hinj hmM hmx hpa hp2
      ((Int.natCast_dvd_natCast.mpr hpL).trans hL) he0 heM hme hey ?_) hT
    intro i hi hdiv
    have hik : i = k := hinj (hi.trans hk.symm)
    subst hik
    obtain ⟨c', hc'⟩ := hdiv
    have hpr := Nat.mul_div_cancel' (hpa i)
    rw [hc', hi] at hpr
    have hpc : p i * c' = 2 := by
      apply Nat.eq_of_mul_eq_mul_left he0
      calc e * (p i * c') = p i * (e * c') := by ring
        _ = 2 * e := hpr
        _ = e * 2 := by ring
    have hle : p i ≤ 2 := Nat.le_of_dvd two_pos ⟨c', hpc.symm⟩
    exact hpk (by have := hp2 i; omega)
  · push Not at h2e
    have hm00 : ∀ i, m i ≠ 0 := fun i => (hm0 i).ne'
    have hhall : ∀ S : Finset (Fin 4),
        S.card ≤ (S.biUnion (fun i => rawPrimeUnits (m i))).card :=
      fun S => small_pairwise_incomparable_biUnion_card_candidate S _
        (by simpa using Finset.card_le_univ S)
        (fun i _ => rawPrimeUnits_nonempty_candidate (by have := hm2 i; omega))
        (fun i _ j _ hij hs => hinc i j hij
          ((rawPrimeUnits_subset_iff_dvd_candidate (hm00 i) (hm00 j)).mp hs))
    obtain ⟨u, hu, huC⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective _).mp hhall
    let p : Fin 4 → ℕ := fun i => (u i).1
    have hpP : ∀ i, (p i).Prime ∧ p i ∣ m i := by
      intro i
      have := huC i
      rw [show u i = ((u i).1, (u i).2) from rfl, mem_rawPrimeUnits_candidate] at this
      exact ⟨(Nat.mem_primeFactors.mp this.1).1, (Nat.mem_primeFactors.mp this.1).2.1⟩
    have hL0 : Finset.univ.lcm m ≠ 0 := by
      rw [Ne, Finset.lcm_eq_zero_iff]; push Not; intro j _; exact hm00 j
    have hpL : (∏ i, p i) ∣ Finset.univ.lcm m := by
      have hsub : Finset.univ.image u ⊆ rawPrimeUnits (Finset.univ.lcm m) := by
        intro w hw
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
        exact (rawPrimeUnits_subset_iff_dvd_candidate (hm00 i) hL0).mpr
          (Finset.dvd_lcm (Finset.mem_univ i)) (huC i)
      have h := prod_rawPrimeUnits_subset_dvd_candidate hL0 _ hsub
      rwa [Finset.prod_image (fun i _ j _ h => hu h)] at h
    exact fiveCover_of_prodCover (case41_core m p hx hy hxy hm0 hinj hmM hmx
      (fun i => (hpP i).2) (fun i => (hpP i).1.two_le)
      ((Int.natCast_dvd_natCast.mpr hpL).trans hL) he0 heM hme hey
      (fun i hi => absurd hi (h2e i))) hT

end Erdos708.Five
