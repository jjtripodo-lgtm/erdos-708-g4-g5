module

public import Erdos708.MatchingExhaustion
public import Erdos708.MatchingToCover
public import Erdos708.TripleAnchorRouting
public import Erdos708.TwoAnchorRouting
public import Erdos708.CoverPackaging
public import Mathlib.Tactic

@[expose] public section

/-!
Universal four-modulus upper theorem for Erdős #708.

The theorem is slightly stronger than the publication specialization: it needs
only four distinct moduli in [2,M], not that one of them is literally equal to
M. The ambient interval has M consecutive integer entries.

Proof structure:
* if zero is in the interval, {0} is an immediate cover;
* otherwise apply the finite dummy-Hall matching/exhaustion trichotomy;
* a four- or three-matching routes through matching/one-defect;
* a deficient triple routes through one-anchor/triple-anchor;
* the residual two-point branch routes through the combined two-anchor theorem.

All number-theoretic case lemmas used here are in the trusted theorem graph.
-/

namespace Erdos708

theorem four_moduli_five_cover
    {L : ℤ} {M a b c d : ℕ}
    (haTwo : 2 ≤ a) (hbTwo : 2 ≤ b) (hcTwo : 2 ≤ c) (hdTwo : 2 ≤ d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    FourModuliCover L M a b c d := by
  classical
  by_cases hzero : (0 : ℤ) ∈ integerInterval L M
  · exact fourModuliCover_of_zero_mem_candidate hzero
  · let C : Fin 4 → Finset ℤ :=
      fourMultipleCandidates L M a b c d
    have hnonempty : ∀ i, (C i).Nonempty := by
      intro i
      exact fourMultipleCandidates_nonempty_candidate
        (by omega) (by omega) (by omega) (by omega)
        haM hbM hcM hdM i
    have hstruct :=
      matching_or_anchor_deficiency_fin_four_candidate C hnonempty
    rcases hstruct with hmatch | hdef
    · exact fourModuliCover_of_matching_output_candidate
        (by omega) (by omega) (by omega) (by omega)
        haM hbM hcM hdM
        hab hac had hbc hbd hcd
        (by simpa [C] using hmatch)
    · rcases hdef with htripleDef | htwoPoint
      · exact fourModuliCover_of_triple_deficiency_candidate
          haTwo hbTwo hcTwo hdTwo
          haM hbM hcM hdM
          hab hac had hbc hbd hcd hzero
          (by simpa [C] using htripleDef)
      · rcases htwoPoint with ⟨htriple, hfull⟩
        exact fourModuliCover_of_two_point_deficiency_candidate
          haTwo hbTwo hcTwo hdTwo
          haM hbM hcM hdM
          hab hac had hbc hbd hcd
          (by simpa [C] using htriple)
          (by simpa [C] using hfull)

end Erdos708
