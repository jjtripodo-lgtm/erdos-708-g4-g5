module

public import Erdos708.Intervals
public import Mathlib.Tactic

@[expose] public section

/-!
# Five-modulus product covers

`FiveModuliCover L M a b c d e k` says that the interval of `M` consecutive integers starting
at `L` contains at most `k` distinct entries whose product is divisible by `a*b*c*d*e`.
The five-modulus #708 question asks for the least `k` that works for every five distinct
positive moduli with maximum `M` and every interval of length `M`.
-/

namespace Erdos708

open scoped BigOperators

/-- A product cover of five moduli by at most `k` distinct interval entries. -/
def FiveModuliCover (L : ℤ) (M : ℕ) (a b c d e k : ℕ) : Prop :=
  ∃ B : Finset ℤ,
    B ⊆ integerInterval L M ∧
    B.card ≤ k ∧
    (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) * (e : ℤ) ∣ ∏ z ∈ B, z

/-- Covers are monotone in the allowed number of entries. -/
theorem FiveModuliCover.mono {L : ℤ} {M a b c d e k k' : ℕ}
    (h : FiveModuliCover L M a b c d e k) (hk : k ≤ k') :
    FiveModuliCover L M a b c d e k' := by
  obtain ⟨B, hB, hcard, hdvd⟩ := h
  exact ⟨B, hB, hcard.trans hk, hdvd⟩

end Erdos708
