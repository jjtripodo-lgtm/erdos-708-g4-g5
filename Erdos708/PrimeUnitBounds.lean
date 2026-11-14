module

public import Erdos708.UpperHalf
public import Mathlib.Tactic

@[expose] public section

namespace Erdos708

/-- Distinct upper-half moduli cannot divide one another properly. -/
theorem upper_half_not_dvd_of_ne
    {M a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (haM : a ≤ M) (hbM : b ≤ M)
    (haHalf : M < 2 * a)
    (hab : a ≠ b) :
    ¬ a ∣ b := by
  intro hdvd
  rcases dvd_iff_exists_eq_mul_right.mp hdvd with ⟨k, hk⟩
  have hkPos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk, hk0] at hb
    simp at hb
  have hkNeOne : k ≠ 1 := by
    intro hk1
    apply hab
    rw [hk, hk1]
    simp
  have hkTwo : 2 ≤ k := by omega
  have htwo : 2 * a ≤ b := by
    rw [hk]
    calc
      2 * a = a * 2 := by omega
      _ ≤ a * k := Nat.mul_le_mul_left a hkTwo
  omega

end Erdos708
