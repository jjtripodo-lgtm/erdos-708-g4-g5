module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

/-!
Finite matching/exhaustion infrastructure for Erdős #708.

The manuscript uses a maximum-matching deficiency statement. For four left
vertices we can avoid formalizing a general deficiency theorem.

Add one common dummy value none to every candidate family. A full Hall
matching in the augmented family uses none at most once, hence gives at least
three real representatives. The augmented Hall inequalities reduce to:

* every original family is nonempty;
* every three-family union has at least two real points;
* the full four-family union has at least three real points.

Therefore, for four nonempty families, either there is a real matching on at
least three left vertices, or a triple has at most one neighbor, or the full
union has at most two neighbors.

This module is part of the trusted theorem graph.
-/

namespace Erdos708

def optionAugment {α : Type*} [DecidableEq α]
    (S : Finset α) : Finset (Option α) :=
  insert none (S.image some)

theorem card_optionAugment_candidate
    {α : Type*} [DecidableEq α] (S : Finset α) :
    (optionAugment S).card = S.card + 1 := by
  classical
  have hnone : (none : Option α) ∉ S.image some := by
    simp
  rw [optionAugment, Finset.card_insert_of_notMem hnone]
  rw [Finset.card_image_of_injective _ (by intro a b h; exact Option.some.inj h)]

theorem biUnion_optionAugment_candidate
    {α : Type*} [DecidableEq α]
    (C : Fin 4 → Finset α)
    {s : Finset (Fin 4)}
    (hs : s.Nonempty) :
    s.biUnion (fun i => optionAugment (C i)) =
      optionAugment (s.biUnion C) := by
  classical
  ext o
  cases o with
  | none =>
      simp [optionAugment]
      exact hs
  | some z =>
      simp [optionAugment]

theorem hall_augmented_fin_four_candidate
    {α : Type*} [DecidableEq α]
    (C : Fin 4 → Finset α)
    (hnonempty : ∀ i, (C i).Nonempty)
    (htriple :
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        2 ≤ ((C i ∪ C j) ∪ C k).card)
    (hfull : 3 ≤ (Finset.univ.biUnion C).card) :
    ∀ s : Finset (Fin 4),
      s.card ≤
        (s.biUnion (fun i => optionAugment (C i))).card := by
  classical
  intro s
  have hsle : s.card ≤ 4 := by
    calc
      s.card ≤ (Finset.univ : Finset (Fin 4)).card :=
        Finset.card_le_univ s
      _ = 4 := by simp
  interval_cases hscard : s.card
  · have hs : s = ∅ := Finset.card_eq_zero.mp hscard
    simp [hs]
  · rcases Finset.card_eq_one.mp hscard with ⟨i, rfl⟩
    have hci : 1 ≤ (C i).card :=
      Finset.one_le_card.mpr (hnonempty i)
    have hcard := card_optionAugment_candidate (C i)
    have hle : 1 ≤ (optionAugment (C i)).card := by
      rw [hcard]
      omega
    simpa using hle
  · rcases Finset.card_eq_two.mp hscard with ⟨i, j, hij, rfl⟩
    have hrealNonempty : (C i ∪ C j).Nonempty := by
      rcases hnonempty i with ⟨z, hz⟩
      exact ⟨z, Finset.mem_union_left _ hz⟩
    have hreal : 1 ≤ (C i ∪ C j).card :=
      Finset.one_le_card.mpr hrealNonempty
    have hsne : ({i, j} : Finset (Fin 4)).Nonempty := by simp
    rw [biUnion_optionAugment_candidate C hsne]
    have hcard := card_optionAugment_candidate (C i ∪ C j)
    have htwo : 2 ≤ (optionAugment (C i ∪ C j)).card := by
      rw [hcard]
      omega
    simpa [Finset.biUnion_insert, hij] using htwo
  · rcases Finset.card_eq_three.mp hscard with
      ⟨i, j, k, hij, hik, hjk, rfl⟩
    have hsne : ({i, j, k} : Finset (Fin 4)).Nonempty := by simp
    rw [biUnion_optionAugment_candidate C hsne]
    have hreal := htriple i j k hij hik hjk
    have hcard :=
      card_optionAugment_candidate ((C i ∪ C j) ∪ C k)
    have hthree : 3 ≤ (optionAugment ((C i ∪ C j) ∪ C k)).card := by
      rw [hcard]
      omega
    simpa [Finset.biUnion_insert, hij, hik, hjk, Finset.union_assoc] using hthree
  · have hs : s = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hscard
    subst s
    have hsne : (Finset.univ : Finset (Fin 4)).Nonempty := by simp
    rw [biUnion_optionAugment_candidate C hsne]
    have hcard :=
      card_optionAugment_candidate (Finset.univ.biUnion C)
    rw [hcard]
    omega

theorem real_matching_of_augmented_matching_candidate
    {α : Type*} [DecidableEq α]
    (C : Fin 4 → Finset α)
    {f : Fin 4 → Option α}
    (hfInj : Function.Injective f)
    (hfMem : ∀ i, f i ∈ optionAugment (C i)) :
    (∃ g : Fin 4 → α,
        Function.Injective g ∧ ∀ i, g i ∈ C i) ∨
    (∃ m : Fin 4,
      ∃ g : {i : Fin 4 // i ≠ m} → α,
        Function.Injective g ∧
        ∀ i, g i ∈ C i.1) := by
  classical
  by_cases hnone : ∃ m, f m = none
  · rcases hnone with ⟨m, hm⟩
    have hreal :
        ∀ i : {j : Fin 4 // j ≠ m},
          ∃ x, x ∈ C i.1 ∧ f i.1 = some x := by
      intro i
      have hfiNe : f i.1 ≠ none := by
        intro hi
        have heq : i.1 = m := hfInj (hi.trans hm.symm)
        exact i.2 heq
      have hmem := hfMem i.1
      simp only [optionAugment, Finset.mem_insert, Finset.mem_image] at hmem
      rcases hmem with hnone' | himage
      · exact (hfiNe hnone').elim
      · rcases himage with ⟨x, hx, hsome⟩
        exact ⟨x, hx, hsome.symm⟩
    let g : {i : Fin 4 // i ≠ m} → α :=
      fun i => Classical.choose (hreal i)
    have hgSpec :
        ∀ i, g i ∈ C i.1 ∧ f i.1 = some (g i) := by
      intro i
      exact Classical.choose_spec (hreal i)
    have hgInj : Function.Injective g := by
      intro i j hij
      apply Subtype.ext
      apply hfInj
      rw [(hgSpec i).2, (hgSpec j).2, hij]
    right
    exact ⟨m, g, hgInj, fun i => (hgSpec i).1⟩
  · have hreal :
        ∀ i : Fin 4, ∃ x, x ∈ C i ∧ f i = some x := by
      intro i
      have hfiNe : f i ≠ none := by
        intro hi
        exact hnone ⟨i, hi⟩
      have hmem := hfMem i
      simp only [optionAugment, Finset.mem_insert, Finset.mem_image] at hmem
      rcases hmem with hnone' | himage
      · exact (hfiNe hnone').elim
      · rcases himage with ⟨x, hx, hsome⟩
        exact ⟨x, hx, hsome.symm⟩
    let g : Fin 4 → α := fun i => Classical.choose (hreal i)
    have hgSpec :
        ∀ i, g i ∈ C i ∧ f i = some (g i) := by
      intro i
      exact Classical.choose_spec (hreal i)
    have hgInj : Function.Injective g := by
      intro i j hij
      apply hfInj
      rw [(hgSpec i).2, (hgSpec j).2, hij]
    left
    exact ⟨g, hgInj, fun i => (hgSpec i).1⟩

theorem exists_real_matching_three_or_four_candidate
    {α : Type*} [DecidableEq α]
    (C : Fin 4 → Finset α)
    (hnonempty : ∀ i, (C i).Nonempty)
    (htriple :
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        2 ≤ ((C i ∪ C j) ∪ C k).card)
    (hfull : 3 ≤ (Finset.univ.biUnion C).card) :
    (∃ g : Fin 4 → α,
        Function.Injective g ∧ ∀ i, g i ∈ C i) ∨
    (∃ m : Fin 4,
      ∃ g : {i : Fin 4 // i ≠ m} → α,
        Function.Injective g ∧
        ∀ i, g i ∈ C i.1) := by
  classical
  let A : Fin 4 → Finset (Option α) :=
    fun i => optionAugment (C i)
  have hhall : ∀ s : Finset (Fin 4),
      s.card ≤ (s.biUnion A).card := by
    intro s
    simpa [A] using
      hall_augmented_fin_four_candidate C hnonempty htriple hfull s
  obtain ⟨f, hfInj, hfMem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective A).mp hhall
  exact real_matching_of_augmented_matching_candidate C hfInj hfMem

theorem matching_or_anchor_deficiency_fin_four_candidate
    {α : Type*} [DecidableEq α]
    (C : Fin 4 → Finset α)
    (hnonempty : ∀ i, (C i).Nonempty) :
    ((∃ g : Fin 4 → α,
        Function.Injective g ∧ ∀ i, g i ∈ C i) ∨
      (∃ m : Fin 4,
        ∃ g : {i : Fin 4 // i ≠ m} → α,
          Function.Injective g ∧
          ∀ i, g i ∈ C i.1)) ∨
    (∃ i j k : Fin 4,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ((C i ∪ C j) ∪ C k).card ≤ 1) ∨
    ((∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        2 ≤ ((C i ∪ C j) ∪ C k).card) ∧
      (Finset.univ.biUnion C).card ≤ 2) := by
  classical
  by_cases htriple :
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        2 ≤ ((C i ∪ C j) ∪ C k).card
  · by_cases hfull : 3 ≤ (Finset.univ.biUnion C).card
    · left
      exact exists_real_matching_three_or_four_candidate
        C hnonempty htriple hfull
    · right
      right
      exact ⟨htriple, by omega⟩
  · right
    left
    push_neg at htriple
    rcases htriple with ⟨i, j, k, hij, hik, hjk, hbad⟩
    exact ⟨i, j, k, hij, hik, hjk, by omega⟩

end Erdos708
