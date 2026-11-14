module

public import Mathlib.Tactic

@[expose] public section

/-! Finite #708 statements. At-most convention; exact-cardinality endpoints are separate. -/
noncomputable section

namespace Erdos708Finite
open scoped BigOperators

def interval (L : ℤ) (M : ℕ) : Finset ℤ := Finset.Icc L (L + (M : ℤ) - 1)

def CoverBound (n k : ℕ) : Prop :=
  ∀ (m : Fin n → ℕ), Function.Injective m → (∀ i, 2 ≤ m i) → ∀ L : ℤ,
    ∃ B : Finset ℤ, B ⊆ interval L (Finset.univ.sup m) ∧ B.card ≤ k ∧
      (∏ i, (m i : ℤ)) ∣ ∏ z ∈ B, z

def ExactCoverBound (n k : ℕ) : Prop :=
  ∀ (m : Fin n → ℕ), Function.Injective m → (∀ i, 2 ≤ m i) → ∀ L : ℤ,
    ∃ B : Finset ℤ, B ⊆ interval L (Finset.univ.sup m) ∧ B.card = k ∧
      (∏ i, (m i : ℤ)) ∣ ∏ z ∈ B, z

end Erdos708Finite
