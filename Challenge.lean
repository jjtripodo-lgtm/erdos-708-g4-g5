module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem 708: four and five moduli

Reference: [erdosproblems.com/708](https://www.erdosproblems.com/708).

Let $g(n)$ be minimal such that, for any $A\subseteq [2,\infty)\cap\mathbb{N}$ with
$\lvert A\rvert=n$ and any set $I$ of $\max(A)$ consecutive integers, there is
$B\subseteq I$ with $\lvert B\rvert=g(n)$ such that $\prod_{a\in A}a\mid\prod_{b\in B}b$.

This file states $g(4)=5$ and $g(5)=6$ twice: with the source's exact cardinality
(`ExactCover`), and with the at-most definitions of Formal Conjectures pull request #4388
(`HasCoveringSize`, `IsMinCoveringSize`, copied verbatim; Apache License 2.0). For $k\le n+1$ the two readings
agree. The general problem stays open.
-/

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

/-- $g(4)=5$. -/
theorem erdos_708.variants.four : IsLeast {k | ExactCover 4 k} 5 := by
  sorry

/-- $g(5)=6$. -/
theorem erdos_708.variants.five : IsLeast {k | ExactCover 5 k} 6 := by
  sorry

/-- $g(4)=5$, stated with the definitions of Formal Conjectures PR #4388. -/
theorem erdos_708.variants.g_four (g : ℕ → ℕ) (hg : IsMinCoveringSize g) : g 4 = 5 := by
  sorry

/-- $g(5)=6$, stated with the definitions of Formal Conjectures PR #4388. -/
theorem erdos_708.variants.g_five (g : ℕ → ℕ) (hg : IsMinCoveringSize g) : g 5 = 6 := by
  sorry

end Erdos708
