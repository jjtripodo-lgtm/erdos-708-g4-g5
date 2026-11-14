module

public import Erdos708.PrimeUnitsRaw
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Residual arithmetic for the Erdős #708 one-anchor proof.

This module is part of the trusted one-anchor dependency graph.  Helper names
retain their historical `_candidate` suffix.
It packages the elementary facts obtained after Hall chooses one labeled
prime-exponent unit from each modulus.
-/

namespace Erdos708

/-- Underlying prime selected by a raw prime unit. -/
def selectedPrime {ι : Type*} (f : ι → RawPrimeUnit) (i : ι) : ℕ :=
  (f i).1

/-- Residual modulus after removing one selected prime factor. -/
def selectedResidual {ι : Type*}
    (a : ι → ℕ) (f : ι → RawPrimeUnit) (i : ι) : ℕ :=
  a i / selectedPrime f i

/-- Membership of a selected raw unit certifies primality of its first coordinate. -/
theorem selectedPrime_prime_candidate
    {ι : Type*} {a : ι → ℕ} {f : ι → RawPrimeUnit} {i : ι}
    (hmem : f i ∈ rawPrimeUnits (a i)) :
    (selectedPrime f i).Prime := by
  have hu := mem_rawPrimeUnits_candidate.mp hmem
  exact (Nat.mem_primeFactors.mp hu.1).1

/-- Membership of a selected raw unit certifies divisibility by its prime. -/
theorem selectedPrime_dvd_candidate
    {ι : Type*} {a : ι → ℕ} {f : ι → RawPrimeUnit} {i : ι}
    (hmem : f i ∈ rawPrimeUnits (a i)) :
    selectedPrime f i ∣ a i := by
  have hu := mem_rawPrimeUnits_candidate.mp hmem
  exact (Nat.mem_primeFactors.mp hu.1).2.1

/-- The selected residual is positive for a positive original modulus. -/
theorem selectedResidual_pos_candidate
    {ι : Type*} {a : ι → ℕ} {f : ι → RawPrimeUnit} {i : ι}
    (ha : 0 < a i)
    (hmem : f i ∈ rawPrimeUnits (a i)) :
    0 < selectedResidual a f i := by
  have hp := selectedPrime_prime_candidate hmem
  have hpdvd := selectedPrime_dvd_candidate hmem
  have hple : selectedPrime f i ≤ a i :=
    Nat.le_of_dvd ha hpdvd
  exact Nat.div_pos hple hp.pos

/-- Dividing by the selected prime leaves a divisor of the original modulus. -/
theorem selectedResidual_dvd_candidate
    {ι : Type*} {a : ι → ℕ} {f : ι → RawPrimeUnit} {i : ι}
    (hmem : f i ∈ rawPrimeUnits (a i)) :
    selectedResidual a f i ∣ a i := by
  exact Nat.div_dvd_of_dvd (selectedPrime_dvd_candidate hmem)

/-- The selected residual is a proper divisor of a positive original modulus. -/
theorem selectedResidual_proper_candidate
    {ι : Type*} {a : ι → ℕ} {f : ι → RawPrimeUnit} {i : ι}
    (ha : 0 < a i)
    (hmem : f i ∈ rawPrimeUnits (a i)) :
    a i ≠ selectedResidual a f i := by
  have hp := selectedPrime_prime_candidate hmem
  have hlt :
      selectedResidual a f i < a i := by
    exact Nat.div_lt_self ha hp.one_lt
  exact ne_of_gt hlt

/-- The selected prime times its residual reconstructs the original modulus. -/
theorem selectedPrime_mul_residual_candidate
    {ι : Type*} {a : ι → ℕ} {f : ι → RawPrimeUnit} {i : ι}
    (hmem : f i ∈ rawPrimeUnits (a i)) :
    selectedPrime f i * selectedResidual a f i = a i := by
  exact Nat.mul_div_cancel' (selectedPrime_dvd_candidate hmem)

/-- Product version of prime-times-residual reconstruction over a finite type. -/
theorem selectedPrime_prod_mul_residual_prod_candidate
    {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (f : ι → RawPrimeUnit)
    (hmem : ∀ i, f i ∈ rawPrimeUnits (a i)) :
    (∏ i : ι, selectedPrime f i) *
        (∏ i : ι, selectedResidual a f i) =
      ∏ i : ι, a i := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact selectedPrime_mul_residual_candidate (hmem i)

/--
If the original modulus divides a signed anchor, then its selected residual
also divides that anchor.
-/
theorem selectedResidual_dvd_anchor_candidate
    {ι : Type*} {a : ι → ℕ} {f : ι → RawPrimeUnit}
    {i : ι} {x : ℤ}
    (hmem : f i ∈ rawPrimeUnits (a i))
    (hax : (a i : ℤ) ∣ x) :
    (selectedResidual a f i : ℤ) ∣ x := by
  have hrNat : selectedResidual a f i ∣ a i :=
    selectedResidual_dvd_candidate hmem
  have hrInt : (selectedResidual a f i : ℤ) ∣ (a i : ℤ) := by
    exact_mod_cast hrNat
  exact hrInt.trans hax

end Erdos708
