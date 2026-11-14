module

public import Erdos708.PrimeUnitsRaw
public import Erdos708.SmallAntichainUnion
public import Erdos708.PrimeUnitBounds
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Prime-unit Hall assignment for the Erdős #708 one-anchor case.

Key simplification: the Hall candidate family for modulus a_i is simply its
raw labeled prime-unit Finset.  No lcm/Omega union formula is needed.  For any
subfamily of at most four upper-half moduli, the candidate sets are nonempty
and pairwise incomparable, so the small Sperner union theorem gives Hall
directly.

The public composition theorem is in `OneAnchor.lean` and registered in the
banked axiom audit.  Helper names retain their historical `_candidate` suffix.
-/

namespace Erdos708

/--
Four distinct upper-half moduli admit distinct labeled prime units, one drawn
from each modulus's factorization.
-/
theorem exists_distinct_prime_units_upper_half_candidate
    {M : ℕ}
    (a : Fin 4 → ℕ)
    (haTwo : ∀ i, 2 ≤ a i)
    (haM : ∀ i, a i ≤ M)
    (haHalf : ∀ i, M < 2 * a i)
    (haInj : Function.Injective a) :
    ∃ f : Fin 4 → RawPrimeUnit, Function.Injective f ∧
      ∀ i, f i ∈ rawPrimeUnits (a i) := by
  classical
  let C : Fin 4 → Finset RawPrimeUnit := fun i => rawPrimeUnits (a i)
  have hhall : ∀ S : Finset (Fin 4),
      S.card ≤ (S.biUnion C).card := by
    intro S
    by_cases hS : S = ∅
    · simp [hS]
    · have hfour : S.card ≤ 4 := by
        calc
          S.card ≤ Finset.univ.card := Finset.card_le_univ S
          _ = 4 := by simp
      have hnonempty : ∀ i ∈ S, (C i).Nonempty := by
        intro i hi
        dsimp [C]
        exact rawPrimeUnits_nonempty_candidate (by have hi := haTwo i; omega)
      have hincomp : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
          ¬ C i ⊆ C j := by
        intro i hi j hj hij hsub
        have hai0 : a i ≠ 0 := by have hi := haTwo i; omega
        have haj0 : a j ≠ 0 := by have hj := haTwo j; omega
        have hdvd : a i ∣ a j :=
          (rawPrimeUnits_subset_iff_dvd_candidate hai0 haj0).1 hsub
        have hne : a i ≠ a j := by
          intro h
          exact hij (haInj h)
        exact (upper_half_not_dvd_of_ne
          (by have hi' := haTwo i; omega)
          (by have hj' := haTwo j; omega)
          (haM i) (haM j) (haHalf i) hne) hdvd
      exact small_pairwise_incomparable_biUnion_card_candidate
        S C hfour hnonempty hincomp
  exact (Finset.all_card_le_biUnion_card_iff_exists_injective C).mp hhall

end Erdos708
