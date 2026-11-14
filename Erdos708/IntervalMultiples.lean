module

public import Erdos708.Intervals
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Tactic

@[expose] public section

namespace Erdos708

/-- In an interval containing zero, the number of nonzero multiples of `d`
is at least `k` whenever the interval has length at least `(k+1)d`. -/
theorem card_nonzero_multiples_ge
    {L : ℤ} {M d k : ℕ}
    (hL : L ≤ 0)
    (hU : 0 ≤ L + (M : ℤ) - 1)
    (hd : 0 < d)
    (hM : (k + 1) * d ≤ M) :
    k ≤ ((integerInterval L M).filter
      (fun z => z ≠ 0 ∧ (d : ℤ) ∣ z)).card := by
  classical
  let U : ℤ := L + (M : ℤ) - 1
  let A : ℤ := L - 1
  let s : Finset ℤ := (integerInterval L M).filter (fun z => (d : ℤ) ∣ z)
  have hIoc : integerInterval L M = Finset.Ioc A U := by
    ext z
    simp [integerInterval, A, U]
  have hcard : (s.card : ℤ) =
      max (⌊(U : ℚ) / (d : ℚ)⌋ - ⌊(A : ℚ) / (d : ℚ)⌋) 0 := by
    dsimp [s]
    rw [hIoc]
    exact Int.Ioc_filter_dvd_card A U (by exact_mod_cast hd)
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hquot : ((k + 1 : ℕ) : ℚ) ≤ (M : ℚ) / (d : ℚ) := by
    rw [le_div_iff₀ hdq]
    exact_mod_cast hM
  have hdiff :
      (k : ℚ) <
        ((⌊(U : ℚ) / (d : ℚ)⌋ : ℤ) : ℚ) -
          ((⌊(A : ℚ) / (d : ℚ)⌋ : ℤ) : ℚ) := by
    have hfloorU := Int.lt_floor_add_one ((U : ℚ) / (d : ℚ))
    have hfloorA := Int.floor_le ((A : ℚ) / (d : ℚ))
    have hUA : (U : ℚ) - (A : ℚ) = M := by
      dsimp [U, A]
      push_cast
      ring
    have hquot' : ((k + 1 : ℕ) : ℚ) ≤
        ((U : ℚ) - (A : ℚ)) / (d : ℚ) := by rw [hUA]; exact hquot
    have hdecomp :
        (U : ℚ) / (d : ℚ) - (A : ℚ) / (d : ℚ) =
          ((U : ℚ) - (A : ℚ)) / (d : ℚ) := by ring
    rw [← hdecomp] at hquot'
    push_cast at hquot'
    have hquotMinus : (k : ℚ) ≤
        (U : ℚ) / (d : ℚ) - (A : ℚ) / (d : ℚ) - 1 := by
      linarith
    have hfloorGap :
        (U : ℚ) / (d : ℚ) - (A : ℚ) / (d : ℚ) - 1 <
          ((⌊(U : ℚ) / (d : ℚ)⌋ : ℤ) : ℚ) -
            ((⌊(A : ℚ) / (d : ℚ)⌋ : ℤ) : ℚ) := by
      linarith
    exact lt_of_le_of_lt hquotMinus hfloorGap
  have hdiffInt : k <
      ⌊(U : ℚ) / (d : ℚ)⌋ - ⌊(A : ℚ) / (d : ℚ)⌋ := by
    exact_mod_cast hdiff
  have hdiffNonneg :
      0 ≤ ⌊(U : ℚ) / (d : ℚ)⌋ - ⌊(A : ℚ) / (d : ℚ)⌋ := by omega
  have hcard' : (s.card : ℤ) =
      ⌊(U : ℚ) / (d : ℚ)⌋ - ⌊(A : ℚ) / (d : ℚ)⌋ := by
    rw [hcard, max_eq_left hdiffNonneg]
  have hs0 : (0 : ℤ) ∈ s := by
    simp [s, integerInterval, hL, hU]
    omega
  have hnonzero : s.erase 0 =
      (integerInterval L M).filter (fun z => z ≠ 0 ∧ (d : ℤ) ∣ z) := by
    ext z
    simp [s, Finset.mem_erase, integerInterval, and_assoc, and_left_comm, and_comm]
  rw [← hnonzero, Finset.card_erase_of_mem hs0]
  have hcardNat : k + 1 ≤ s.card := by
    have : (k : ℤ) < (s.card : ℤ) := by rw [hcard']; exact_mod_cast hdiffInt
    omega
  omega

end Erdos708
