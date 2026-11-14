module

public import Erdos708.TwoAnchorExceptional
public import Erdos708.TwoAnchorBridgeRegular
public import Erdos708.TwoAnchorNoBridge
public import Mathlib.Tactic

@[expose] public section

/-!
Composition of the three trusted two-anchor branches.

This module is part of the trusted theorem graph.
It introduces one normalized interface: a,b are unique at x and c is unique
at y. The fourth modulus d is either unique at y (no bridge), or it is the
bridge distance and divides both anchors. In the bridge branch we split only on
whether h=gcd(c,d) has an off-anchor multiple. That dichotomy dispatches
directly to the already-banked regular or exceptional bridge theorems.

No new number theory is introduced here.
-/

namespace Erdos708

/-- Common conclusion used by the combined two-anchor and later exhaustion
layers. Either three mutually distinct repairs or two mutually distinct repairs
away from the two anchors pay the four-modulus product. -/
def TwoAnchorCover
    (L : ℤ) (M : ℕ) (x y : ℤ) (a b c d : ℕ) : Prop :=
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
        x * y * u * v)

/-- Turn the Fin-3 output of the exceptional theorem into the common
three-repair branch. -/
theorem twoAnchorCover_of_exceptional_candidate
    {L x y : ℤ} {M a b c d : ℕ}
    (h :
      ∃ f : Fin 3 → ℤ,
        Function.Injective f ∧
        (∀ i, f i ∈ integerInterval L M ∧ f i ≠ x ∧ f i ≠ y) ∧
        (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
          x * y * (f 0 * f 1 * f 2)) :
    TwoAnchorCover L M x y a b c d := by
  rcases h with ⟨f, hfInj, hfBasic, hfPay⟩
  left
  refine ⟨f 0, f 1, f 2,
    (hfBasic 0).1, (hfBasic 1).1, (hfBasic 2).1,
    (hfBasic 0).2.1, (hfBasic 0).2.2,
    (hfBasic 1).2.1, (hfBasic 1).2.2,
    (hfBasic 2).2.1, (hfBasic 2).2.2,
    ?_, ?_, ?_, ?_⟩
  · intro h01
    have hi : (0 : Fin 3) = 1 := hfInj h01
    exact (by decide : (0 : Fin 3) ≠ 1) hi
  · intro h02
    have hi : (0 : Fin 3) = 2 := hfInj h02
    exact (by decide : (0 : Fin 3) ≠ 2) hi
  · intro h12
    have hi : (1 : Fin 3) = 2 := hfInj h12
    exact (by decide : (1 : Fin 3) ≠ 2) hi
  · simpa [mul_assoc] using hfPay

/-- A two-repair branch is already a TwoAnchorCover. -/
theorem twoAnchorCover_of_two_repairs_candidate
    {L x y : ℤ} {M a b c d : ℕ}
    (h :
      ∃ u v : ℤ,
        u ∈ integerInterval L M ∧
        v ∈ integerInterval L M ∧
        u ≠ x ∧ u ≠ y ∧
        v ≠ x ∧ v ≠ y ∧
        u ≠ v ∧
        (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) ∣
          x * y * u * v) :
    TwoAnchorCover L M x y a b c d :=
  Or.inr h

/--
Combined normalized two-anchor theorem.

The first three moduli have the normalized pattern
  a,b unique at x; c unique at y.
For d there are exactly the two routes consumed here:
  * unique at y: no bridge;
  * d is the positive anchor distance and divides both anchors: bridge.

In the bridge route the existence or absence of an off-anchor
gcd(c,d)-multiple is a complete dichotomy, routed respectively to the trusted
regular and exceptional branch theorems.
-/
theorem two_anchor_combined_candidate
    {L x y : ℤ} {M a b c d : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (hcPos : 0 < c) (hdPos : 0 < d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hxy : x ≠ y)
    (haX : (a : ℤ) ∣ x)
    (hbX : (b : ℤ) ∣ x)
    (hcY : (c : ℤ) ∣ y)
    (huniqueA :
      ∀ z, z ∈ integerInterval L M → (a : ℤ) ∣ z → z = x)
    (huniqueB :
      ∀ z, z ∈ integerInterval L M → (b : ℤ) ∣ z → z = x)
    (huniqueC :
      ∀ z, z ∈ integerInterval L M → (c : ℤ) ∣ z → z = y)
    (hdRoute :
      (((d : ℤ) ∣ y) ∧
        (∀ z, z ∈ integerInterval L M → (d : ℤ) ∣ z → z = y)) ∨
      ((y = x + (d : ℤ) ∨ x = y + (d : ℤ)) ∧
        (d : ℤ) ∣ x ∧ (d : ℤ) ∣ y)) :
    TwoAnchorCover L M x y a b c d := by
  rcases hdRoute with hnoBridge | hbridge
  · rcases hnoBridge with ⟨hdY, huniqueD⟩
    exact twoAnchorCover_of_two_repairs_candidate
      (two_anchor_no_bridge
        haPos hbPos hcPos hdPos
        haM hbM hcM hdM
        hab hac had hbc hbd hcd
        hxI hyI hxy
        haX hbX hcY hdY
        huniqueA huniqueB huniqueC huniqueD)
  · rcases hbridge with ⟨hdir, hdX, hdY⟩
    by_cases hOff :
        ∃ zh, zh ∈ integerInterval L M ∧
          (Nat.gcd c d : ℤ) ∣ zh ∧ zh ≠ x ∧ zh ≠ y
    · rcases hOff with ⟨zh, hzhI, hzhDiv, hzhX, hzhY⟩
      exact twoAnchorCover_of_two_repairs_candidate
        (two_anchor_regular_bridge
          haPos hbPos hcPos hdPos
          haM hbM hcM hdM
          hab hac had hbc hbd hcd
          hxI hyI hxy
          haX hbX hcY hdY
          huniqueA huniqueB
          hzhI hzhDiv hzhX hzhY)
    · have honlyH :
          ∀ z, z ∈ integerInterval L M →
            (Nat.gcd c d : ℤ) ∣ z → z = x ∨ z = y := by
        intro z hzI hzDiv
        by_contra hz
        push_neg at hz
        exact hOff ⟨z, hzI, hzDiv, hz.1, hz.2⟩
      exact twoAnchorCover_of_exceptional_candidate
        (two_anchor_exceptional_bridge
          haPos hbPos hcPos hdPos
          haM hbM hcM hdM
          hab hac had hbc hbd hcd
          hxI hyI hdir
          haX hbX hdX hdY hcY
          huniqueA huniqueB huniqueC honlyH)

end Erdos708
