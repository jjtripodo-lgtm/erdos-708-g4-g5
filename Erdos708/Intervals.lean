module

public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
Integer-interval facts for the four-modulus Erdős #708 argument.

The ambient entries are integers so intervals crossing zero are represented
without a special case.
-/

namespace Erdos708

/-- The `M` consecutive integers beginning at `L`. -/
def integerInterval (L : ℤ) (M : ℕ) : Finset ℤ :=
  Finset.Icc L (L + (M : ℤ) - 1)

@[simp] theorem mem_integerInterval {L z : ℤ} {M : ℕ} :
    z ∈ integerInterval L M ↔ L ≤ z ∧ z ≤ L + (M : ℤ) - 1 := by
  simp [integerInterval]

theorem integerInterval_card {L : ℤ} {M : ℕ} (hM : 0 < M) :
    (integerInterval L M).card = M := by
  rw [integerInterval, Int.card_Icc]
  have htop : L + (M : ℤ) - 1 + 1 - L = (M : ℤ) := by ring
  rw [htop]
  simp

/-- Translation carries an interval to the interval with translated start. -/
theorem integerInterval_mem_translate {L z q : ℤ} {M : ℕ} :
    z ∈ integerInterval L M ↔ z + q ∈ integerInterval (L + q) M := by
  simp [mem_integerInterval]
  omega

/-- Every point between two points of an integer interval is in the interval.
This order-convexity fact is used in mixed divisor-multiplicity cases. -/
theorem integerInterval_mem_of_between {L z₁ z₂ z : ℤ} {M : ℕ}
    (h₁ : z₁ ∈ integerInterval L M)
    (h₂ : z₂ ∈ integerInterval L M)
    (h : min z₁ z₂ ≤ z ∧ z ≤ max z₁ z₂) :
    z ∈ integerInterval L M := by
  rw [mem_integerInterval] at h₁ h₂ ⊢
  rcases h with ⟨hlo, hhi⟩
  constructor <;> omega

/-- If an interval contains its anchor and one signed multiple, it contains
every intermediate signed multiple on that side. -/
theorem integerInterval_mem_signed_double {L : ℤ} {M r s : ℕ} {q : ℤ}
    (hzero : (0 : ℤ) ∈ integerInterval L M)
    (hs : q * (s : ℤ) ∈ integerInterval L M)
    (hq : q = 1 ∨ q = -1)
    (hrs : 2 * r ≤ s) :
    q * ((2 * r : ℕ) : ℤ) ∈ integerInterval L M := by
  rcases hq with hq | hq
  · subst q
    have hs' : (s : ℤ) ∈ integerInterval L M := by simpa using hs
    have hbetween :
        min (0 : ℤ) (s : ℤ) ≤ ((2 * r : ℕ) : ℤ) ∧
          ((2 * r : ℕ) : ℤ) ≤ max (0 : ℤ) (s : ℤ) := by
      constructor <;> push_cast <;> omega
    have h := integerInterval_mem_of_between hzero hs' hbetween
    simpa using h
  · subst q
    have hs' : -(s : ℤ) ∈ integerInterval L M := by simpa using hs
    have hbetween :
        min (-(s : ℤ)) (0 : ℤ) ≤ -((2 * r : ℕ) : ℤ) ∧
          -((2 * r : ℕ) : ℤ) ≤ max (-(s : ℤ)) (0 : ℤ) := by
      constructor <;> push_cast <;> omega
    have h := integerInterval_mem_of_between hs' hzero hbetween
    simpa using h

/-- Divisibility is unchanged by translating by a multiple of the modulus. -/
theorem dvd_iff_of_dvd_translation {d z q : ℤ}
    (hq : d ∣ q) : d ∣ z ↔ d ∣ z + q := by
  constructor
  · intro hz
    rcases hz with ⟨u, rfl⟩
    rcases hq with ⟨v, rfl⟩
    refine ⟨u + v, ?_⟩
    ring
  · intro hz
    rcases hz with ⟨u, hu⟩
    rcases hq with ⟨v, hv⟩
    refine ⟨u - v, ?_⟩
    calc
      z = (z + q) - q := by omega
      _ = d * u - d * v := by rw [hu, hv]
      _ = d * (u - v) := by ring

/-- If the interval is at least twice as long as `d`, every one of its
multiples of `d` has a distinct neighboring multiple still in the interval. -/
theorem exists_distinct_multiple_of_two_mul_le
    {L x : ℤ} {M d : ℕ}
    (hd : 0 < d) (hM : 2 * d ≤ M)
    (hx : x ∈ integerInterval L M)
    (hxd : (d : ℤ) ∣ x) :
    ∃ y ∈ integerInterval L M, y ≠ x ∧ (d : ℤ) ∣ y := by
  rcases hxd with ⟨q, hq⟩
  rcases (le_or_gt (L + (d : ℤ)) x) with hleft | hleft
  · refine ⟨x - d, ?_, ?_, ?_⟩
    · rw [mem_integerInterval] at hx ⊢
      omega
    · omega
    · refine ⟨q - 1, ?_⟩
      rw [hq]
      push_cast
      ring
  · refine ⟨x + d, ?_, ?_, ?_⟩
    · rw [mem_integerInterval] at hx ⊢
      omega
    · omega
    · refine ⟨q + 1, ?_⟩
      rw [hq]
      push_cast
      ring

/-- A unique interval multiple forces the modulus into the upper half. -/
theorem modulus_gt_half_of_unique_multiple
    {L x : ℤ} {M d : ℕ}
    (hd : 0 < d) (hx : x ∈ integerInterval L M)
    (hxd : (d : ℤ) ∣ x)
    (hunique : ∀ y ∈ integerInterval L M, (d : ℤ) ∣ y → y = x) :
    M < 2 * d := by
  by_contra h
  have htwo := exists_distinct_multiple_of_two_mul_le hd (by omega) hx hxd
  rcases htwo with ⟨y, hy, hne, hyd⟩
  exact hne (hunique y hy hyd)

end Erdos708
