module

public import Erdos708.Five.Defs
public import Erdos708.Five.Antichain
public import Erdos708.ResidualMultiples

@[expose] public section

/-!
# Site utilities for five-modulus covers

* `cover_of_sites`: distinct interval sites `f i`, each divisible by a payment `r i`, whose
  payments' product is divisible by the target, give a cover.
* Counting facts for multiples of `q` in an interval: confinement to three sites forces
  `M < 4q`, and then two incomparable multiples of `q` are `2q` and `3q`.
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

/-- Distinct sites with divisor payments whose product covers the target give a cover. -/
theorem cover_of_sites {L : ℤ} {M a b c d e k : ℕ} (f : Fin k → ℤ) (r : Fin k → ℤ)
    (hf : Function.Injective f) (hI : ∀ i, f i ∈ integerInterval L M)
    (hr : ∀ i, r i ∣ f i)
    (ht : (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) * (e : ℤ) ∣ ∏ i, r i) :
    FiveModuliCover L M a b c d e k := by
  classical
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact hI i
  · rw [Finset.card_image_of_injective _ hf]
    simp
  · rw [Finset.prod_image (fun i _ j _ h => hf h)]
    exact ht.trans (Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hr i))

/-- There is a multiple of `q` outside any set of at most `k` points when `(k+1)q ≤ M`. -/
theorem exists_multiple_outside {L x : ℤ} {M q k : ℕ} (F : Finset ℤ) (hq : 0 < q)
    (hx : x ∈ integerInterval L M) (hxq : (q : ℤ) ∣ x) (hM : (k + 1) * q ≤ M)
    (hF : F.card ≤ k) :
    ∃ y ∈ integerInterval L M, (q : ℤ) ∣ y ∧ y ∉ F :=
  exists_interval_multiple_outside_finset_candidate F hq hx hxq hM hF

/-- If every multiple of `q` in the interval lies in a set of at most three points, and the
interval contains one multiple, then `M < 4q`. -/
theorem lt_four_mul_of_confined {L x : ℤ} {M q : ℕ} (S : Finset ℤ) (hq : 0 < q)
    (hx : x ∈ integerInterval L M) (hxq : (q : ℤ) ∣ x) (hS : S.card ≤ 3)
    (hconf : ∀ y ∈ integerInterval L M, (q : ℤ) ∣ y → y ∈ S) :
    M < 4 * q := by
  classical
  by_contra h
  push Not at h
  obtain ⟨y, hyI, hyq, hyS⟩ := exists_multiple_outside S hq hx hxq (k := 3) (by omega) hS
  exact hyS (hconf y hyI hyq)

/-- If `M < 4q`, two incomparable positive multiples of `q` that are at most `M` are `2q` and
`3q` in some order. -/
theorem eq_two_three_of_incomparable {q x y M : ℕ}
    (hx : q ∣ x) (hy : q ∣ y) (hx0 : 0 < x) (hy0 : 0 < y) (hxM : x ≤ M) (hyM : y ≤ M)
    (hM : M < 4 * q) (hxy : ¬ x ∣ y) (hyx : ¬ y ∣ x) :
    (x = 2 * q ∧ y = 3 * q) ∨ (x = 3 * q ∧ y = 2 * q) := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hs : s < 4 := by
    by_contra h; push Not at h; nlinarith
  have ht : t < 4 := by
    by_contra h; push Not at h; nlinarith
  have hs0 : 0 < s := Nat.pos_of_mul_pos_left hx0
  have ht0 : 0 < t := Nat.pos_of_mul_pos_left hy0
  interval_cases s <;> interval_cases t <;> simp_all [Nat.mul_comm]

end Erdos708.Five
