module

public import Erdos708.ProperDivisorHall
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

/-!
Four-family Hall assembly for the proper-divisor SDR theorem.

This module is part of the trusted SDR dependency graph.

This generic combinatorial wrapper isolates the final Erdos708 number-theory
layer from Finset subfamily bureaucracy.

For four candidate families, it is enough to prove the union-cardinality lower
bound for every singleton, every pair, every triple, and the full union.
-/

namespace Erdos708

theorem hall_fin_four_of_union_bounds_candidate
    {α : Type*} [DecidableEq α]
    (C : Fin 4 → Finset α)
    (h1 : ∀ i, 1 ≤ (C i).card)
    (h2 : ∀ i j, i ≠ j → 2 ≤ (C i ∪ C j).card)
    (h3 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      3 ≤ ((C i ∪ C j) ∪ C k).card)
    (h4 : 4 ≤ (Finset.univ.biUnion C).card) :
    ∀ s : Finset (Fin 4), s.card ≤ (s.biUnion C).card := by
  classical
  intro s
  have hsle : s.card ≤ 4 := by
    calc
      s.card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_le_univ s
      _ = 4 := by simp
  interval_cases hscard : s.card
  · have hs : s = ∅ := Finset.card_eq_zero.mp hscard
    simp [hs]
  · rcases Finset.card_eq_one.mp hscard with ⟨i, rfl⟩
    simpa using h1 i
  · rcases Finset.card_eq_two.mp hscard with ⟨i, j, hij, rfl⟩
    simpa [hij] using h2 i j hij
  · rcases Finset.card_eq_three.mp hscard with
      ⟨i, j, k, hij, hik, hjk, rfl⟩
    simpa [hij, hik, hjk, Finset.union_assoc] using h3 i j k hij hik hjk
  · have hs : s = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hscard
    simpa [hs] using h4

/-- Hall plus the four-family union-bound wrapper gives an SDR immediately. -/
theorem exists_distinct_representatives_fin_four_of_union_bounds_candidate
    {α : Type*} [DecidableEq α]
    (C : Fin 4 → Finset α)
    (h1 : ∀ i, 1 ≤ (C i).card)
    (h2 : ∀ i j, i ≠ j → 2 ≤ (C i ∪ C j).card)
    (h3 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      3 ≤ ((C i ∪ C j) ∪ C k).card)
    (h4 : 4 ≤ (Finset.univ.biUnion C).card) :
    ∃ f : Fin 4 → α, Function.Injective f ∧ ∀ i, f i ∈ C i := by
  classical
  have hhall :=
    hall_fin_four_of_union_bounds_candidate C h1 h2 h3 h4
  exact (Finset.all_card_le_biUnion_card_iff_exists_injective C).mp hhall

end Erdos708
