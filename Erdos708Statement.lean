module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Interval.Finset.Nat

/-! Solution-side copy of the four Challenge definitions, byte-identical in body. -/

@[expose] public section

namespace Erdos708

/-- The `M` consecutive integers that start at `L`. -/
noncomputable def interval (L : ℤ) (M : ℕ) : Finset ℤ := Finset.Icc L (L + (M : ℤ) - 1)

/-- For every set of `n` distinct moduli at least two, and every interval of length the
largest modulus, some `k` elements of the interval have a product that the product of the
moduli divides. The moduli are given as an injective enumeration `m : Fin n → ℕ`. -/
def ExactCover (n k : ℕ) : Prop :=
  ∀ m : Fin n → ℕ, Function.Injective m → (∀ i, 2 ≤ m i) → ∀ L : ℤ,
    ∃ B ⊆ interval L (Finset.univ.sup m), B.card = k ∧
      (∏ i, (m i : ℤ)) ∣ ∏ z ∈ B, z

/-- Formal Conjectures PR #4388 (`HasCoveringSize`, copied verbatim): every `n`-set of
integers at least two has, in every window of `max A` consecutive positive integers, at
most `k` elements whose product the product of the set divides. -/
def HasCoveringSize (n k : ℕ) : Prop :=
  ∀ A : Finset ℕ, A.card = n → (∀ a ∈ A, 2 ≤ a) →
    ∀ m : ℕ, 0 < m →
      ∃ B ⊆ Finset.Ico m (m + A.sup id), B.card ≤ k ∧ (∏ a ∈ A, a) ∣ ∏ b ∈ B, b

/-- Formal Conjectures PR #4388 (`IsMinCoveringSize`, copied verbatim): `g` is the
Erdős–Surányi function in the at-most reading. -/
def IsMinCoveringSize (g : ℕ → ℕ) : Prop :=
  ∀ n, IsLeast {k | HasCoveringSize n k} (g n)

end Erdos708
