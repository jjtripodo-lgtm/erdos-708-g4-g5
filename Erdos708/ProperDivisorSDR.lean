module

public import Erdos708.ProperDivisorSDRFinFour
public import Mathlib.Tactic

@[expose] public section

/-! Translation from the zero-anchor Fin-4 SDR statement to the arbitrary
common-anchor proper-divisor lemma used in the manuscript. -/

namespace Erdos708

/--
Four-label version of the manuscript proper-divisor SDR lemma.

If four distinct positive originals a_i <= M have positive proper divisors r_i
and an M-term integer interval contains a common multiple x of all r_i, then
there are four distinct off-anchor representatives in the interval, one
divisible by each r_i.
-/
theorem proper_divisor_sdr_fin_four
    {L x : ℤ} {M : ℕ}
    (a r : Fin 4 → ℕ)
    (haPos : ∀ i, 0 < a i)
    (haInj : Function.Injective a)
    (hrPos : ∀ i, 0 < r i)
    (hrDiv : ∀ i, r i ∣ a i)
    (hrProper : ∀ i, a i ≠ r i)
    (haM : ∀ i, a i ≤ M)
    (hx : x ∈ integerInterval L M)
    (hxDiv : ∀ i, (r i : ℤ) ∣ x) :
    ∃ f : Fin 4 → ℤ, Function.Injective f ∧
      ∀ i, f i ∈ properDivisorCandidates L M x r i := by
  classical
  let L' : ℤ := L - x
  have hzero : (0 : ℤ) ∈ integerInterval L' M := by
    have h :=
      (integerInterval_mem_translate
        (L := L) (z := x) (q := -x) (M := M)).1 hx
    simpa [L', sub_eq_add_neg] using h
  have hL' : L' ≤ 0 := by
    rw [mem_integerInterval] at hzero
    exact hzero.1
  have hU' : 0 ≤ L' + (M : ℤ) - 1 := by
    rw [mem_integerInterval] at hzero
    exact hzero.2
  obtain ⟨g, hgInj, hgMem⟩ :=
    proper_divisor_sdr_fin_four_zero_anchor_candidate
      (L := L') (M := M)
      a r haPos haInj hrPos hrDiv hrProper haM hL' hU'
  let f : Fin 4 → ℤ := fun i => g i + x
  have hfInj : Function.Injective f := by
    intro i j hij
    apply hgInj
    dsimp [f] at hij
    omega
  refine ⟨f, hfInj, ?_⟩
  intro i
  have hgi := hgMem i
  simp only [properDivisorCandidates4, properDivisorCandidates,
    Finset.mem_filter] at hgi ⊢
  rcases hgi with ⟨hgiI, hgiNe, hgiDiv⟩
  have hfiI : f i ∈ integerInterval L M := by
    have htrans :=
      (integerInterval_mem_translate
        (L := L') (z := g i) (q := x) (M := M)).1 hgiI
    have hstart : L' + x = L := by
      dsimp [L']
      omega
    simpa [f, hstart] using htrans
  have hfiNe : f i ≠ x := by
    dsimp [f]
    omega
  have hfiDiv : (r i : ℤ) ∣ f i := by
    dsimp [f]
    exact dvd_add hgiDiv (hxDiv i)
  exact ⟨hfiI, hfiNe, hfiDiv⟩

end Erdos708
