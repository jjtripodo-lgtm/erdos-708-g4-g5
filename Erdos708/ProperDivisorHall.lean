module

public import Erdos708.Intervals
public import Mathlib.Combinatorics.Hall.Basic

@[expose] public section

namespace Erdos708

/-- Candidate multiples for one divisor, inside an integer interval and
excluding a distinguished common anchor. -/
def properDivisorCandidates {k : ℕ} (L : ℤ) (M : ℕ) (x : ℤ)
    (r : Fin k → ℕ) (i : Fin k) : Finset ℤ :=
  (integerInterval L M).filter fun z => z ≠ x ∧ (r i : ℤ) ∣ z

/-- The Hall condition on the divisor-candidate families gives distinct
representatives. This packages Mathlib's marriage theorem in the exact
candidate-set form used by the proper-divisor step. -/
theorem exists_distinct_divisor_representatives_of_hall
    {k : ℕ} (L : ℤ) (M : ℕ) (x : ℤ) (r : Fin k → ℕ)
    (hhall : ∀ s : Finset (Fin k),
      s.card ≤ (s.biUnion (properDivisorCandidates L M x r)).card) :
    ∃ f : Fin k → ℤ, Function.Injective f ∧
      ∀ i, f i ∈ properDivisorCandidates L M x r i := by
  classical
  exact (Finset.all_card_le_biUnion_card_iff_exists_injective
    (properDivisorCandidates L M x r)).mp hhall

end Erdos708
