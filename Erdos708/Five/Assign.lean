module

public import Erdos708.Five.MissingOne

@[expose] public section

/-!
# Antichain anchor assignments

An assignment places every original `m i` at an interval multiple `f i`, so that comparable
originals never share a site. Assignments exist: process the originals in decreasing order.
Among the finitely many assignments, one maximizes the number of occupied sites.
This is Section 2 of `G5_COMPLETE_CANDIDATE.md`.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `f` is an antichain anchor assignment for the originals `m`. -/
def ValidAssign (L : ℤ) (M : ℕ) (m : ι → ℕ) (f : ι → ℤ) : Prop :=
  (∀ i, f i ∈ integerInterval L M) ∧ (∀ i, (m i : ℤ) ∣ f i) ∧
    (∀ i j, i ≠ j → m i ∣ m j → f i ≠ f j)

/-- Greedy existence on any subfamily `S`. -/
theorem exists_valid_on {L : ℤ} {M : ℕ} (m : ι → ℕ) (hinj : Function.Injective m)
    (hpos : ∀ i, 0 < m i) (hle : ∀ i, m i ≤ M) :
    ∀ (n : ℕ) (S : Finset ι), S.card = n → ∃ f : ι → ℤ,
      (∀ i ∈ S, f i ∈ integerInterval L M ∧ (m i : ℤ) ∣ f i) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → m i ∣ m j → f i ≠ f j) := by
  classical
  intro n
  induction n with
  | zero =>
    intro S hS
    rw [Finset.card_eq_zero] at hS
    subst hS
    exact ⟨fun _ => 0, by simp, by simp⟩
  | succ n ih =>
    intro S hS
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀, hmin⟩ := S.exists_min_image m hne
    obtain ⟨f, hfS, hfv⟩ := ih (S.erase i₀) (by rw [Finset.card_erase_of_mem hi₀, hS]; rfl)
    set D := (S.erase i₀).filter (fun j => m i₀ ∣ m j) with hD
    set F := D.image f with hF
    -- the larger multiples of `m i₀`, together with it, are distinct multiples at most `M`
    have hDbound : (D.card + 1) * m i₀ ≤ M := by
      have hcard : (insert (m i₀) (D.image m)).card = D.card + 1 := by
        rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn (hinj.injOn)]
        intro h
        obtain ⟨j, hj, hjm⟩ := Finset.mem_image.mp h
        have := hinj hjm
        rw [hD, Finset.mem_filter, Finset.mem_erase] at hj
        exact hj.1.1 this
      rw [← hcard]
      apply card_mul_le_of_multiples (hpos i₀)
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ⟨dvd_rfl, hpos i₀, hle i₀⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        rw [hD, Finset.mem_filter] at hj
        exact ⟨hj.2, hpos j, hle j⟩
    obtain ⟨p, hp, hmp⟩ := exists_interval_multiple_of_le_candidate (L := L) (hpos i₀) (hle i₀)
    obtain ⟨w, hw, hmw, hwF⟩ := exists_multiple_outside F (hpos i₀) hp hmp (k := D.card)
      hDbound Finset.card_image_le
    refine ⟨Function.update f i₀ w, ?_, ?_⟩
    · intro i hi
      by_cases h : i = i₀
      · subst h; simp [hw, hmw]
      · simp only [Function.update, h, dite_false]
        exact hfS i (Finset.mem_erase.mpr ⟨h, hi⟩)
    · intro i hi j hj hij hdvd
      by_cases hi0 : i = i₀
      · subst hi0
        have hj0 : j ≠ i := fun h => hij h.symm
        simp only [Function.update, hj0, dite_false, dite_true]
        intro hwf
        apply hwF
        rw [hF, Finset.mem_image]
        exact ⟨j, by rw [hD, Finset.mem_filter, Finset.mem_erase]; exact ⟨⟨hj0, hj⟩, hdvd⟩,
          hwf.symm⟩
      · by_cases hj0 : j = i₀
        · subst hj0
          exfalso
          have h1 := hmin i hi
          have h2 := Nat.le_of_dvd (hpos j) hdvd
          exact hij (hinj (le_antisymm h2 h1))
        · simp only [Function.update, hi0, hj0, dite_false]
          exact hfv i (Finset.mem_erase.mpr ⟨hi0, hi⟩) j (Finset.mem_erase.mpr ⟨hj0, hj⟩)
            hij hdvd

/-- Some valid assignment exists. -/
theorem exists_validAssign {L : ℤ} {M : ℕ} (m : ι → ℕ) (hinj : Function.Injective m)
    (hpos : ∀ i, 0 < m i) (hle : ∀ i, m i ≤ M) : ∃ f, ValidAssign L M m f := by
  classical
  obtain ⟨f, hf1, hf2⟩ := exists_valid_on (L := L) m hinj hpos hle _ Finset.univ rfl
  exact ⟨f, fun i => (hf1 i (Finset.mem_univ i)).1, fun i => (hf1 i (Finset.mem_univ i)).2,
    fun i j hij h => hf2 i (Finset.mem_univ i) j (Finset.mem_univ j) hij h⟩

/-- A valid assignment maximizing the number of occupied sites. -/
theorem exists_max_validAssign {L : ℤ} {M : ℕ} (m : ι → ℕ) (hinj : Function.Injective m)
    (hpos : ∀ i, 0 < m i) (hle : ∀ i, m i ≤ M) :
    ∃ f, ValidAssign L M m f ∧
      ∀ f', ValidAssign L M m f' → (Finset.univ.image f').card ≤ (Finset.univ.image f).card := by
  classical
  let A := (Fintype.piFinset (fun _ : ι => integerInterval L M)).filter
    (fun f => ValidAssign L M m f)
  obtain ⟨f₀, hf₀⟩ := exists_validAssign (L := L) m hinj hpos hle
  have hA : A.Nonempty := ⟨f₀, by
    rw [Finset.mem_filter, Fintype.mem_piFinset]; exact ⟨hf₀.1, hf₀⟩⟩
  obtain ⟨f, hfA, hmax⟩ := A.exists_max_image (fun f => (Finset.univ.image f).card) hA
  rw [Finset.mem_filter] at hfA
  refine ⟨f, hfA.2, fun f' hf' => hmax f' ?_⟩
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  exact ⟨hf'.1, hf'⟩

end Erdos708.Five
