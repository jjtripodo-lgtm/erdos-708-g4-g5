module

public import Erdos708.SpernerHelpers
public import Mathlib.Tactic

@[expose] public section

/-!
Small combinatorial lemma for the Erdős #708 prime-unit Hall step.

Key simplification: for k<=4 we do not need to identify the neighborhood union
with the prime units of an lcm or compute its big-Omega value.  The candidate
sets themselves form an antichain inside the Boolean lattice on their own
union.  Sperner then forces the union to have at least k elements.

This module is part of the trusted one-anchor dependency graph.
-/

namespace Erdos708

/--
A nonempty antichain of at most four nonempty subsets of a finite ambient type
cannot contain more sets than ambient points.
-/
theorem small_nonempty_antichain_card_le_ambient_candidate
    {α : Type*} [Fintype α]
    {A : Finset (Finset α)}
    (hanti : IsAntichain (· ⊆ ·) (A : Set (Finset α)))
    (hnonempty : ∀ s ∈ A, s.Nonempty)
    (hfour : A.card ≤ 4) :
    A.card ≤ Fintype.card α := by
  by_cases h0 : A.card = 0
  · omega
  by_cases h1 : A.card = 1
  · rcases Finset.card_eq_one.mp h1 with ⟨s, hs⟩
    have hsA : s ∈ A := by simp [hs]
    have hsne := hnonempty s hsA
    have hamb : 0 < Fintype.card α := by
      rcases hsne with ⟨x, hx⟩
      haveI : Nonempty α := ⟨x⟩
      exact Fintype.card_pos
    omega
  · have htwo : 2 ≤ A.card := by omega
    exact small_sperner_forces_ambient_card_candidate
      hanti rfl htwo hfour

/--
Let C_i be pairwise incomparable nonempty finite sets for indices in S, with
|S|<=4. Then their union has cardinality at least |S|.

This is the exact Hall neighborhood inequality needed by the prime-unit
assignment once divisibility is converted to set inclusion.
-/
theorem small_pairwise_incomparable_biUnion_card_candidate
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (S : Finset ι)
    (C : ι → Finset α)
    (hfour : S.card ≤ 4)
    (hnonempty : ∀ i ∈ S, (C i).Nonempty)
    (hincomp : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ¬ C i ⊆ C j) :
    S.card ≤ (S.biUnion C).card := by
  classical
  let U : Finset α := S.biUnion C
  let β := {x : α // x ∈ U}
  let lift : ι → Finset β := fun i =>
    Finset.univ.filter fun x => (x.1 ∈ C i)

  have hmem_lift {i : ι} {x : β} :
      x ∈ lift i ↔ x.1 ∈ C i := by
    simp [lift]

  have hCsubU (i : ι) (hi : i ∈ S) : C i ⊆ U := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩

  have hlift_nonempty (i : ι) (hi : i ∈ S) :
      (lift i).Nonempty := by
    rcases hnonempty i hi with ⟨x, hx⟩
    let xu : β := ⟨x, hCsubU i hi hx⟩
    exact ⟨xu, by simp [lift, xu, hx]⟩

  have hlift_subset_iff {i j : ι} (hi : i ∈ S) (hj : j ∈ S) :
      lift i ⊆ lift j ↔ C i ⊆ C j := by
    constructor
    · intro h x hx
      let xu : β := ⟨x, hCsubU i hi hx⟩
      have hxli : xu ∈ lift i := by
        simp [lift, xu, hx]
      have hxlj := h hxli
      simpa [lift, xu] using hxlj
    · intro h x hx
      have hxCi : x.1 ∈ C i := by
        simpa [lift] using hx
      have hxCj := h hxCi
      simpa [lift] using hxCj

  have hlift_inj_on :
      Set.InjOn lift (S : Set ι) := by
    intro i hi j hj hij
    by_contra hijIndex
    have hsub : lift i ⊆ lift j := by rw [hij]
    have hCsub : C i ⊆ C j :=
      (hlift_subset_iff hi hj).1 hsub
    exact (hincomp i hi j hj hijIndex) hCsub

  let A : Finset (Finset β) := S.image lift
  have hAcard : A.card = S.card := by
    dsimp [A]
    exact Finset.card_image_iff.mpr
      (fun i hi j hj h => hlift_inj_on hi hj h)

  have hA_nonempty : ∀ T ∈ A, T.Nonempty := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨i, hi, rfl⟩
    exact hlift_nonempty i hi

  have hanti : IsAntichain (· ⊆ ·) (A : Set (Finset β)) := by
    intro X hX Y hY hXY hsub
    rcases Finset.mem_image.mp hX with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hY with ⟨j, hj, rfl⟩
    have hij : i ≠ j := by
      intro h
      subst j
      exact hXY rfl
    exact (hincomp i hi j hj hij)
      ((hlift_subset_iff hi hj).1 hsub)

  have hAambient :
      A.card ≤ Fintype.card β :=
    small_nonempty_antichain_card_le_ambient_candidate
      hanti hA_nonempty (by simpa [hAcard] using hfour)

  have hβcard : Fintype.card β = U.card := by
    simp [β, U]

  rw [hAcard, hβcard] at hAambient
  simpa [U] using hAambient

end Erdos708
