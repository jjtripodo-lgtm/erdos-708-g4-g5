module

public import Erdos708.RepeatedDivisor
public import Mathlib.Tactic

@[expose] public section

/-!
Arithmetic kernel for the bounded four-modulus one-defect route.

This module is part of the trusted one-defect dependency graph.  Its helper
name retains the historical `_candidate` suffix.
-/

namespace Erdos708

/-- Distinct positive multiples of d bounded by M force m*d <= M.

This is the non-proper analogue of repeated_proper_moduli_force_bound and is
the counting invariant needed by the four-modulus one-defect collision chain. -/
theorem distinct_multiples_force_bound_candidate
    {m M d : ℕ}
    (hm : 0 < m) (hd : 0 < d)
    (a : Fin m → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haDiv : ∀ i, d ∣ a i)
    (haM : ∀ i, a i ≤ M)
    (haInj : Function.Injective a) :
    m * d ≤ M := by
  classical
  by_contra hbound
  have hM : M < m * d := by omega
  let q : Fin m → ℕ := fun i =>
    Classical.choose (dvd_iff_exists_eq_mul_right.mp (haDiv i))
  have hqmul (i : Fin m) : a i = d * q i :=
    Classical.choose_spec (dvd_iff_exists_eq_mul_right.mp (haDiv i))
  have hqPos (i : Fin m) : 0 < q i := by
    have ha := haPos i
    rw [hqmul i] at ha
    by_contra h
    have hzero : q i = 0 := by omega
    simp [hzero] at ha
  have hqUpper (i : Fin m) : q i < m := by
    have hmul : d * q i < d * m := by
      calc
        d * q i = a i := (hqmul i).symm
        _ ≤ M := haM i
        _ < m * d := hM
        _ = d * m := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hqInj : Function.Injective q := by
    intro i j hij
    apply haInj
    calc
      a i = d * q i := hqmul i
      _ = d * q j := congrArg (fun n => d * n) hij
      _ = a j := (hqmul j).symm
  let image := Finset.univ.image q
  have hcardImage : image.card = m := by
    dsimp [image]
    simp [Finset.card_image_of_injective, hqInj]
  have himageSubset : image ⊆ Finset.Icc 1 (m - 1) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact Finset.mem_Icc.mpr ⟨hqPos i, Nat.le_pred_of_lt (hqUpper i)⟩
  have hcardIcc : (Finset.Icc 1 (m - 1)).card < m := by
    simp
    omega
  have hle := Finset.card_le_card himageSubset
  omega

end Erdos708
