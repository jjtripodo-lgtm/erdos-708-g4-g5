module

public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.Tactic

@[expose] public section

/-!
Small combinatorial helpers for the Erdős #708 one-anchor case.

This module is part of the trusted one-anchor dependency graph.  Helper names
retain their historical `_candidate` suffix.
-/

namespace Erdos708

/--
Two positive upper-half integers at most M cannot properly divide one another.
This is the divisibility-antichain fact used by the one-anchor proof.
-/
theorem upper_half_dvd_eq_candidate
    {M a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (haM : a ≤ M) (hbM : b ≤ M)
    (haHalf : M < 2 * a)
    (hab : a ∣ b) :
    a = b := by
  rcases dvd_iff_exists_eq_mul_right.mp hab with ⟨k, hk⟩
  have hkPos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk, hk0] at hb
    simp at hb
  by_cases hk1 : k = 1
  · rw [hk, hk1]
    simp
  · have hk2 : 2 ≤ k := by omega
    have h2a : 2 * a ≤ b := by
      rw [hk]
      nlinarith
    omega

/--
For an ambient type of cardinality at most three, every antichain of finite
subsets has size at most max 1 |alpha|.

This is just Sperner's theorem evaluated at n=0,1,2,3.
-/
theorem small_sperner_bound_candidate
    {α : Type*} [Fintype α]
    {A : Finset (Finset α)}
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset α)))
    (hcard : Fintype.card α ≤ 3) :
    A.card ≤ max 1 (Fintype.card α) := by
  have hs := hA.sperner
  let n := Fintype.card α
  have hn : n ≤ 3 := by simpa [n] using hcard
  have hchoose : n.choose (n / 2) ≤ max 1 n := by
    interval_cases n <;> norm_num
  have hA' : A.card ≤ max 1 n := hs.trans hchoose
  simpa [n] using hA'

/--
A k-element antichain with 2<=k<=4 cannot live in a Boolean lattice on fewer
than k ambient units.
-/
theorem small_sperner_forces_ambient_card_candidate
    {α : Type*} [Fintype α]
    {A : Finset (Finset α)} {k : ℕ}
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset α)))
    (hAcard : A.card = k)
    (hk2 : 2 ≤ k) (hk4 : k ≤ 4) :
    k ≤ Fintype.card α := by
  by_contra h
  have hamb : Fintype.card α < k := by omega
  have hamb3 : Fintype.card α ≤ 3 := by omega
  have hs :=
    small_sperner_bound_candidate
      (α := α) (A := A) hA hamb3
  rw [hAcard] at hs
  have hmaxlt : max 1 (Fintype.card α) < k := by
    have h1 : 1 < k := by omega
    omega
  omega

end Erdos708
