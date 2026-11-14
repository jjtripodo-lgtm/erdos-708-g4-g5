module

public import Erdos708.PrimeUnitsRaw
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Payment lemmas for the Erdős #708 one-anchor prime-unit route.

This module is part of the trusted one-anchor dependency graph.  Helper names
retain their historical `_candidate` suffix.

The key idea is to avoid introducing an ambient lcm merely to pay for selected
prime units.  The raw labeled units of n contain exactly one slot for every
prime occurrence in the factorization of n, so multiplying their underlying
primes gives n itself.  Any selected subset therefore has prime product
dividing n.  Applied to n = |x| for the common anchor x, this pays for repeated
selections of the same prime at distinct exponent slots.
-/

namespace Erdos708

/--
Multiplying the underlying prime of every labeled prime-exponent unit of n
reconstructs n exactly.
-/
theorem prod_rawPrimeUnits_fst_candidate
    {n : ℕ} (hn : n ≠ 0) :
    (∏ u ∈ rawPrimeUnits n, u.1) = n := by
  classical
  calc
    (∏ u ∈ rawPrimeUnits n, u.1)
        =
      ∏ p ∈ n.primeFactors,
        ∏ u ∈
          (Finset.range (n.factorization p)).image (fun j => (p, j)),
          u.1 := by
            unfold rawPrimeUnits
            rw [Finset.prod_biUnion]
            intro p hp q hq hpq
            exact rawPrimeUnits_fiber_disjoint_candidate hpq
    _ =
      ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [Finset.prod_image]
        · simp [Finset.prod_const]
        · intro i hi j hj hij
          exact congrArg Prod.snd hij
    _ = n := by
        simpa only [Finsupp.prod, Nat.support_factorization] using
          Nat.prod_factorization_pow_eq_self hn

/--
The prime product attached to any subset of n's labeled units divides n.
-/
theorem prod_rawPrimeUnits_subset_dvd_candidate
    {n : ℕ} (hn : n ≠ 0)
    (S : Finset RawPrimeUnit)
    (hS : S ⊆ rawPrimeUnits n) :
    (∏ u ∈ S, u.1) ∣ n := by
  have hprod :=
    Finset.prod_dvd_prod_of_subset
      S (rawPrimeUnits n) (fun u : RawPrimeUnit => u.1) hS
  rw [prod_rawPrimeUnits_fst_candidate hn] at hprod
  exact hprod

/--
A positive natural modulus dividing a signed integer also divides its natural
absolute value.
-/
theorem nat_dvd_natAbs_of_int_dvd_candidate
    {a : ℕ} {x : ℤ}
    (h : (a : ℤ) ∣ x) :
    a ∣ x.natAbs := by
  have h' :
      Int.natAbs (a : ℤ) ∣ Int.natAbs x :=
    (Int.natAbs_dvd_natAbs).2 h
  simpa using h'

/--
If f selects distinct labeled prime units, one from each of four positive
moduli a_i, and every a_i divides the signed common anchor x, then the product
of the selected underlying primes divides |x|.

This is the exact payment statement needed after the prime-unit Hall matching.
-/
theorem selected_prime_product_dvd_anchor_natAbs_candidate
    {a : Fin 4 → ℕ} {x : ℤ}
    (haPos : ∀ i, 0 < a i)
    (hx0 : x ≠ 0)
    (hxDiv : ∀ i, (a i : ℤ) ∣ x)
    (f : Fin 4 → RawPrimeUnit)
    (hfInj : Function.Injective f)
    (hfMem : ∀ i, f i ∈ rawPrimeUnits (a i)) :
    (∏ i : Fin 4, (f i).1) ∣ x.natAbs := by
  classical
  let S : Finset RawPrimeUnit := Finset.univ.image f

  have hxAbs0 : x.natAbs ≠ 0 := by
    exact Int.natAbs_ne_zero.mpr hx0

  have hSsub : S ⊆ rawPrimeUnits x.natAbs := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
    have hai0 : a i ≠ 0 := Nat.ne_of_gt (haPos i)
    have haiDiv : a i ∣ x.natAbs :=
      nat_dvd_natAbs_of_int_dvd_candidate (hxDiv i)
    exact rawPrimeUnits_subset_of_dvd_candidate
      hai0 hxAbs0 haiDiv (hfMem i)

  have hprod :
      (∏ u ∈ S, u.1) ∣ x.natAbs :=
    prod_rawPrimeUnits_subset_dvd_candidate hxAbs0 S hSsub

  have hEq :
      (∏ u ∈ S, u.1) = ∏ i : Fin 4, (f i).1 := by
    dsimp [S]
    rw [Finset.prod_image hfInj.injOn]

  rw [hEq] at hprod
  exact hprod

end Erdos708
