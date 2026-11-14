module

public import Erdos708.TwoAnchorCombined
public import Erdos708.TripleAnchor
public import Erdos708.OneAnchor
public import Erdos708.OneDefectFinite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Trusted packaging layer for the final Erdős #708 four-modulus theorem.

All trusted case theorems currently expose their chosen interval entries in
slightly different shapes.  This file gives them one common publication-facing
target: a Finset of at most five interval entries whose product is divisible by
the product of the four moduli.

This file is intentionally outside the trusted import graph and is NOT Banked.
-/

namespace Erdos708

open scoped BigOperators

def FourModuliCover
    (L : ℤ) (M : ℕ) (a b c d : ℕ) : Prop :=
  ∃ B : Finset ℤ,
    B ⊆ integerInterval L M ∧
    B.card ≤ 5 ∧
    (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣ ∏ z ∈ B, z

/-- Package five explicitly distinct interval entries. -/
theorem fourModuliCover_of_five_points_candidate
    {L x y u v w : ℤ} {M a b c d : ℕ}
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (huI : u ∈ integerInterval L M)
    (hvI : v ∈ integerInterval L M)
    (hwI : w ∈ integerInterval L M)
    (hxy : x ≠ y)
    (hxu : x ≠ u) (hxv : x ≠ v) (hxw : x ≠ w)
    (hyu : y ≠ u) (hyv : y ≠ v) (hyw : y ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hpay :
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
        x * y * u * v * w) :
    FourModuliCover L M a b c d := by
  classical
  let B : Finset ℤ := {x, y, u, v, w}
  refine ⟨B, ?_, ?_, ?_⟩
  · intro z hz
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact hxI
    · exact hyI
    · exact huI
    · exact hvI
    · exact hwI
  · have hcard : B.card = 5 := by
      simp [B, hxy, hxu, hxv, hxw, hyu, hyv, hyw, huv, huw, hvw]
    omega
  · simpa [B, hxy, hxu, hxv, hxw, hyu, hyv, hyw, huv, huw, hvw,
      mul_assoc, mul_comm, mul_left_comm] using hpay

/-- Package four explicitly distinct interval entries. -/
theorem fourModuliCover_of_four_points_candidate
    {L x y u v : ℤ} {M a b c d : ℕ}
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (huI : u ∈ integerInterval L M)
    (hvI : v ∈ integerInterval L M)
    (hxy : x ≠ y)
    (hxu : x ≠ u) (hxv : x ≠ v)
    (hyu : y ≠ u) (hyv : y ≠ v)
    (huv : u ≠ v)
    (hpay :
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
        x * y * u * v) :
    FourModuliCover L M a b c d := by
  classical
  let B : Finset ℤ := {x, y, u, v}
  refine ⟨B, ?_, ?_, ?_⟩
  · intro z hz
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hxI
    · exact hyI
    · exact huI
    · exact hvI
  · have hcard : B.card = 4 := by
      simp [B, hxy, hxu, hxv, hyu, hyv, huv]
    omega
  · simpa [B, hxy, hxu, hxv, hyu, hyv, huv,
      mul_assoc, mul_comm, mul_left_comm] using hpay

/-- The common two-anchor conclusion packages directly into a cover. -/
theorem fourModuliCover_of_twoAnchorCover_candidate
    {L x y : ℤ} {M a b c d : ℕ}
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hxy : x ≠ y)
    (h : TwoAnchorCover L M x y a b c d) :
    FourModuliCover L M a b c d := by
  rcases h with h5 | h4
  · rcases h5 with
      ⟨u, v, w, huI, hvI, hwI,
        huX, huY, hvX, hvY, hwX, hwY,
        huv, huw, hvw, hpay⟩
    exact fourModuliCover_of_five_points_candidate
      hxI hyI huI hvI hwI hxy
      (Ne.symm huX) (Ne.symm hvX) (Ne.symm hwX)
      (Ne.symm huY) (Ne.symm hvY) (Ne.symm hwY)
      huv huw hvw hpay
  · rcases h4 with
      ⟨u, v, huI, hvI, huX, huY, hvX, hvY, huv, hpay⟩
    exact fourModuliCover_of_four_points_candidate
      hxI hyI huI hvI hxy
      (Ne.symm huX) (Ne.symm hvX)
      (Ne.symm huY) (Ne.symm hvY)
      huv hpay

/-- Package the already-banked triple-anchor theorem. -/
theorem fourModuliCover_of_triple_anchor_candidate
    {L x y : ℤ} {M a b c d : ℕ}
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hxy : x ≠ y)
    (h :
      (∃ u v w : ℤ,
        u ∈ integerInterval L M ∧
        v ∈ integerInterval L M ∧
        w ∈ integerInterval L M ∧
        u ≠ x ∧ u ≠ y ∧
        v ≠ x ∧ v ≠ y ∧
        w ≠ x ∧ w ≠ y ∧
        u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
        (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
          x * y * u * v * w) ∨
      (∃ u v : ℤ,
        u ∈ integerInterval L M ∧
        v ∈ integerInterval L M ∧
        u ≠ x ∧ u ≠ y ∧
        v ≠ x ∧ v ≠ y ∧
        u ≠ v ∧
        (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
          x * y * u * v)) :
    FourModuliCover L M a b c d := by
  exact fourModuliCover_of_twoAnchorCover_candidate
    hxI hyI hxy h


/-- FourModuliCover depends on the moduli only through their integer product. -/
theorem fourModuliCover_of_same_product_candidate
    {L : ℤ} {M a b c d a' b' c' d' : ℕ}
    (hprod :
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) =
        (a' : ℤ) * (b' : ℤ) * (c' : ℤ) * (d' : ℤ))
    (h : FourModuliCover L M a' b' c' d') :
    FourModuliCover L M a b c d := by
  rcases h with ⟨B, hBI, hBcard, hpay⟩
  refine ⟨B, hBI, hBcard, ?_⟩
  rw [hprod]
  exact hpay

/-- Package a common anchor together with four injective off-anchor repairs. -/
theorem fourModuliCover_of_anchor_plus_four_candidate
    {L x : ℤ} {M a b c d : ℕ}
    (hxI : x ∈ integerInterval L M)
    (y : Fin 4 → ℤ)
    (hyInj : Function.Injective y)
    (hyBasic : ∀ i, y i ∈ integerInterval L M ∧ y i ≠ x)
    (hpay :
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
        x * ∏ i : Fin 4, y i) :
    FourModuliCover L M a b c d := by
  classical
  let Y : Finset ℤ := Finset.univ.image y
  let B : Finset ℤ := insert x Y
  have hxNotY : x ∉ Y := by
    intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, hix⟩
    exact (hyBasic i).2 hix
  have hYcard : Y.card = 4 := by
    dsimp [Y]
    simp [Finset.card_image_of_injective, hyInj]
  have hBcard : B.card = 5 := by
    dsimp [B]
    rw [Finset.card_insert_of_notMem hxNotY, hYcard]
  have hYprod : ∏ z ∈ Y, z = ∏ i : Fin 4, y i := by
    dsimp [Y]
    rw [Finset.prod_image hyInj.injOn]
  refine ⟨B, ?_, by omega, ?_⟩
  · intro z hz
    simp only [B, Finset.mem_insert] at hz
    rcases hz with rfl | hzY
    · exact hxI
    · rcases Finset.mem_image.mp hzY with ⟨i, hi, rfl⟩
      exact (hyBasic i).1
  · have hBprod : ∏ z ∈ B, z = x * ∏ i : Fin 4, y i := by
      dsimp [B]
      rw [Finset.prod_insert hxNotY, hYprod]
    rw [hBprod]
    exact hpay


/-- If zero lies in the interval, the singleton {0} already covers every
four-modulus product. -/
theorem fourModuliCover_of_zero_mem_candidate
    {L : ℤ} {M a b c d : ℕ}
    (hzero : (0 : ℤ) ∈ integerInterval L M) :
    FourModuliCover L M a b c d := by
  refine ⟨{0}, ?_, ?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_singleton] at hz
    simpa [hz] using hzero
  · simp
  · simp

end Erdos708
