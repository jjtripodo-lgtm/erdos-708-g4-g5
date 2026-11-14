module

public import Erdos708.ProperDivisorFullUnionMixedB
public import Erdos708.MixedHall
public import Mathlib.Tactic

@[expose] public section

/-!
Equality-pattern dispatcher for the full four-family Hall bound, plus the
zero-anchor Fin-4 proper-divisor SDR theorem.

This module is in the trusted graph; the translated public SDR theorem is
`proper_divisor_sdr_fin_four` in `ProperDivisorSDR.lean`.
-/

namespace Erdos708

/--
The full four-family union has at least four candidates for every equality
pattern among the four divisor labels.
-/
theorem proper_divisor_full_union_bound_candidate
    {L : ℤ} {M : ℕ}
    (a r : Fin 4 → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haInj : Function.Injective a)
    (hrPos : ∀ i, 0 < r i)
    (hrDiv : ∀ i, r i ∣ a i)
    (hrProper : ∀ i, a i ≠ r i)
    (haM : ∀ i, a i ≤ M)
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1)
    (q : ℤ) (hq : q = 1 ∨ q = -1)
    (hqmem : ∀ i, q * (r i : ℤ) ∈ integerInterval L M) :
    4 ≤ (Finset.univ.biUnion (fullC L M r)).card := by
  by_cases h01 : r 0 = r 1
  · by_cases h02 : r 0 = r 2
    · by_cases h03 : r 0 = r 3
      · exact proper_divisor_full_union_all_equal_candidate
          a r haPos haInj hrPos hrDiv hrProper haM
          h01 h02 h03 hL hU
      · exact proper_divisor_full_union_rrrs_candidate
          a r haPos haInj hrPos hrDiv hrProper haM
          hL hU q hq hqmem
          0 1 2 3
          (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
          h01 h02 h03
    · by_cases h03 : r 0 = r 3
      · exact proper_divisor_full_union_rrrs_candidate
          a r haPos haInj hrPos hrDiv hrProper haM
          hL hU q hq hqmem
          0 1 3 2
          (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
          h01 h03 h02
      · by_cases h23 : r 2 = r 3
        · exact proper_divisor_full_union_rrss_candidate
            a r haPos haInj hrPos hrDiv hrProper haM
            hL hU q hq hqmem
            0 1 2 3
            (by decide) (by decide)
            h01 h23 h02
        · exact proper_divisor_full_union_rrst_candidate
            a r haPos haInj hrPos hrDiv hrProper haM
            hL hU q hq hqmem
            0 1 2 3
            (by decide) h01 h02 h03 h23
  · by_cases h02 : r 0 = r 2
    · by_cases h03 : r 0 = r 3
      · exact proper_divisor_full_union_rrrs_candidate
          a r haPos haInj hrPos hrDiv hrProper haM
          hL hU q hq hqmem
          0 2 3 1
          (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
          h02 h03 h01
      · by_cases h13 : r 1 = r 3
        · exact proper_divisor_full_union_rrss_candidate
            a r haPos haInj hrPos hrDiv hrProper haM
            hL hU q hq hqmem
            0 2 1 3
            (by decide) (by decide)
            h02 h13 h01
        · exact proper_divisor_full_union_rrst_candidate
            a r haPos haInj hrPos hrDiv hrProper haM
            hL hU q hq hqmem
            0 2 1 3
            (by decide) h02 h01 h03 h13
    · by_cases h03 : r 0 = r 3
      · by_cases h12 : r 1 = r 2
        · exact proper_divisor_full_union_rrss_candidate
            a r haPos haInj hrPos hrDiv hrProper haM
            hL hU q hq hqmem
            0 3 1 2
            (by decide) (by decide)
            h03 h12 h01
        · exact proper_divisor_full_union_rrst_candidate
            a r haPos haInj hrPos hrDiv hrProper haM
            hL hU q hq hqmem
            0 3 1 2
            (by decide) h03 h01 h02 h12
      · by_cases h12 : r 1 = r 2
        · by_cases h13 : r 1 = r 3
          · exact proper_divisor_full_union_rrrs_candidate
              a r haPos haInj hrPos hrDiv hrProper haM
              hL hU q hq hqmem
              1 2 3 0
              (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide)
              h12 h13 (Ne.symm h01)
          · exact proper_divisor_full_union_rrst_candidate
              a r haPos haInj hrPos hrDiv hrProper haM
              hL hU q hq hqmem
              1 2 0 3
              (by decide) h12 (Ne.symm h01) h13 h03
        · by_cases h13 : r 1 = r 3
          · exact proper_divisor_full_union_rrst_candidate
              a r haPos haInj hrPos hrDiv hrProper haM
              hL hU q hq hqmem
              1 3 0 2
              (by decide) h13 (Ne.symm h01) h12 h02
          · by_cases h23 : r 2 = r 3
            · exact proper_divisor_full_union_rrst_candidate
                a r haPos haInj hrPos hrDiv hrProper haM
                hL hU q hq hqmem
                2 3 0 1
                (by decide) h23 (Ne.symm h02) (Ne.symm h12) h01
            · exact proper_divisor_full_union_all_distinct_candidate
                r hrPos q hq hqmem
                h01 h02 h03 h12 h13 h23

/--
Zero-anchor version of the four-label proper-divisor SDR theorem.

The arbitrary-anchor manuscript statement can later be obtained by translating
the interval and all representatives by the common anchor.
-/
theorem proper_divisor_sdr_fin_four_zero_anchor_candidate
    {L : ℤ} {M : ℕ}
    (a r : Fin 4 → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haInj : Function.Injective a)
    (hrPos : ∀ i, 0 < r i)
    (hrDiv : ∀ i, r i ∣ a i)
    (hrProper : ∀ i, a i ≠ r i)
    (haM : ∀ i, a i ≤ M)
    (hL : L ≤ 0) (hU : 0 ≤ L + (M : ℤ) - 1) :
    ∃ f : Fin 4 → ℤ, Function.Injective f ∧
      ∀ i, f i ∈ properDivisorCandidates4 L M r i := by
  classical
  have hrSmall :=
    proper_divisor_small_candidate
      (M := M) a r haPos hrPos hrDiv hrProper haM
  obtain ⟨q, hq, hqall⟩ :=
    exists_common_signed_first_multiple_candidate
      (L := L) (M := M) hL hU
  have hqmem : ∀ i, q * (r i : ℤ) ∈ integerInterval L M := by
    intro i
    exact hqall (r i) (hrPos i) (hrSmall i)
  have h1 :=
    proper_divisor_singleton_union_bound_candidate
      (L := L) (M := M) r hrPos hrSmall q hq hqmem
  have h2 :=
    proper_divisor_pair_union_bound_candidate
      (L := L) (M := M)
      hL hU a r haPos haInj hrPos hrDiv hrProper haM
      q hq hqmem
  have h3 :=
    proper_divisor_triple_union_bound_candidate
      (L := L) (M := M)
      hL hU a r haPos haInj hrPos hrDiv hrProper haM
      q hq hqmem
  have h4 :=
    proper_divisor_full_union_bound_candidate
      (L := L) (M := M)
      a r haPos haInj hrPos hrDiv hrProper haM
      hL hU q hq hqmem
  exact exists_distinct_representatives_fin_four_of_union_bounds_candidate
    (C := properDivisorCandidates4 L M r) h1 h2 h3 h4

end Erdos708
