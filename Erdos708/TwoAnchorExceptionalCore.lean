module

public import Erdos708.ResidualMultiples
public import Erdos708.TripleAnchorRepairs
public import Erdos708.ProperDivisorAssembly
public import Erdos708.UpperHalf
public import Mathlib.Tactic

@[expose] public section

/-!
Reusable core lemmas for the exceptional two-anchor bridge in Erdős #708.
It replaces the brittle "equal four-point arithmetic progressions have equal
step" argument by a smaller divisibility argument.

If the off-anchor r- and s-multiple sets coincide, move one r-step from one
anchor toward the other.  Because r is a proper divisor of the anchor distance,
that point lies strictly between the anchors.  Equality of the candidate sets
makes it an s-multiple; subtracting the common s-multiple anchor gives s | r.
Swapping r and s gives r | s, hence r=s.

The rest of the file isolates the h=D, c=2D reduction and the finite Hall
cardinality facts so the eventual exceptional-bridge theorem can mostly be
composition.
-/

namespace Erdos708

/-- Interval multiples of d excluding both distinguished anchors. -/
def offTwoAnchorMultiples
    (L : ℤ) (M : ℕ) (x y : ℤ) (d : ℕ) : Finset ℤ :=
  (integerInterval L M).filter
    (fun z => z ≠ x ∧ z ≠ y ∧ (d : ℤ) ∣ z)

/-- One positive d-step from x toward y stays strictly between the anchors
whenever their distance is D and d<D. -/
theorem exists_intermediate_d_multiple_between_anchors
    {L x y : ℤ} {M d D : ℕ}
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hdir : y = x + (D : ℤ) ∨ x = y + (D : ℤ))
    (hdPos : 0 < d)
    (hdD : d < D)
    (hdX : (d : ℤ) ∣ x) :
    ∃ z ∈ integerInterval L M,
      z ≠ x ∧ z ≠ y ∧ (d : ℤ) ∣ z := by
  rcases hdir with hxy | hyx
  · let z : ℤ := x + (d : ℤ)
    have hdPosZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hdPos
    have hdDZ : (d : ℤ) < (D : ℤ) := by exact_mod_cast hdD
    have hxyLt : x < y := by
      rw [hxy]
      omega
    have hzBetween : min x y ≤ z ∧ z ≤ max x y := by
      rw [min_eq_left hxyLt.le, max_eq_right hxyLt.le]
      dsimp [z]
      rw [hxy]
      constructor <;> omega
    have hzI : z ∈ integerInterval L M :=
      integerInterval_mem_of_between hxI hyI hzBetween
    have hzX : z ≠ x := by
      dsimp [z]
      omega
    have hzY : z ≠ y := by
      dsimp [z]
      rw [hxy]
      omega
    have hzDvd : (d : ℤ) ∣ z := by
      rcases hdX with ⟨q, hq⟩
      refine ⟨q + 1, ?_⟩
      dsimp [z]
      rw [hq]
      ring
    exact ⟨z, hzI, hzX, hzY, hzDvd⟩
  · let z : ℤ := x - (d : ℤ)
    have hdPosZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hdPos
    have hdDZ : (d : ℤ) < (D : ℤ) := by exact_mod_cast hdD
    have hyxLt : y < x := by
      rw [hyx]
      omega
    have hzBetween : min x y ≤ z ∧ z ≤ max x y := by
      rw [min_eq_right hyxLt.le, max_eq_left hyxLt.le]
      dsimp [z]
      rw [hyx]
      constructor <;> omega
    have hzI : z ∈ integerInterval L M :=
      integerInterval_mem_of_between hxI hyI hzBetween
    have hzX : z ≠ x := by
      dsimp [z]
      omega
    have hzY : z ≠ y := by
      dsimp [z]
      rw [hyx]
      omega
    have hzDvd : (d : ℤ) ∣ z := by
      rcases hdX with ⟨q, hq⟩
      refine ⟨q - 1, ?_⟩
      dsimp [z]
      rw [hq]
      ring
    exact ⟨z, hzI, hzX, hzY, hzDvd⟩

/-- If d divides the anchor distance and the only interval d-multiples are the
two anchors, then d must equal that distance. -/
theorem modulus_eq_anchor_distance_of_only_anchor_multiples
    {L x y : ℤ} {M d D : ℕ}
    (hDPos : 0 < D)
    (hdPos : 0 < d)
    (hdDvd : d ∣ D)
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hdir : y = x + (D : ℤ) ∨ x = y + (D : ℤ))
    (hdX : (d : ℤ) ∣ x)
    (honly :
      ∀ z, z ∈ integerInterval L M → (d : ℤ) ∣ z →
        z = x ∨ z = y) :
    d = D := by
  have hdLe : d ≤ D := Nat.le_of_dvd hDPos hdDvd
  by_contra hne
  have hdLt : d < D := by omega
  obtain ⟨z, hzI, hzX, hzY, hzD⟩ :=
    exists_intermediate_d_multiple_between_anchors
      hxI hyI hdir hdPos hdLt hdX
  rcases honly z hzI hzD with h | h
  · exact hzX h
  · exact hzY h

/-- The arithmetic step used after h=D in the exceptional bridge:
D | c, c≠D, c≤M<3D forces c=2D. -/
theorem eq_two_mul_of_dvd_ne_of_lt_three_mul
    {c D M : ℕ}
    (hDPos : 0 < D)
    (hcPos : 0 < c)
    (hDc : D ∣ c)
    (hcD : c ≠ D)
    (hcM : c ≤ M)
    (hM3 : M < 3 * D) :
    c = 2 * D := by
  rcases dvd_iff_exists_eq_mul_right.mp hDc with ⟨k, hk⟩
  have hkPos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk, hk0] at hcPos
    simp at hcPos
  have hkNeOne : k ≠ 1 := by
    intro hk1
    apply hcD
    rw [hk, hk1]
    simp
  have hkLtThree : k < 3 := by
    have hcLt : c < 3 * D := lt_of_le_of_lt hcM hM3
    rw [hk] at hcLt
    nlinarith
  have hkTwo : k = 2 := by omega
  rw [hk, hkTwo]
  omega

/-- Under M<3D, a positive D-multiple at most M is either D or 2D.  Hence if
c=2D and a is distinct from both D and c, D cannot divide a. -/
theorem not_dvd_of_bounded_below_three_mul_and_distinct
    {a c D M : ℕ}
    (hDPos : 0 < D)
    (haPos : 0 < a)
    (haM : a ≤ M)
    (hM3 : M < 3 * D)
    (hcTwo : c = 2 * D)
    (haD : a ≠ D)
    (hac : a ≠ c) :
    ¬ D ∣ a := by
  intro hDa
  rcases dvd_iff_exists_eq_mul_right.mp hDa with ⟨k, hk⟩
  have hkPos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk, hk0] at haPos
    simp at haPos
  have hkLtThree : k < 3 := by
    have haLt : a < 3 * D := lt_of_le_of_lt haM hM3
    rw [hk] at haLt
    nlinarith
  have hkCases : k = 1 ∨ k = 2 := by omega
  rcases hkCases with hk1 | hk2
  · apply haD
    rw [hk, hk1]
    simp
  · apply hac
    rw [hk, hk2, hcTwo]
    omega

/-- gcd(a,D) is a positive proper divisor of D when D does not divide a. -/
theorem gcd_proper_divisor_right
    {a D : ℕ}
    (haPos : 0 < a)
    (hDPos : 0 < D)
    (hnot : ¬ D ∣ a) :
    0 < Nat.gcd a D ∧
      Nat.gcd a D ∣ D ∧
      Nat.gcd a D ≠ D := by
  have hgPos : 0 < Nat.gcd a D :=
    Nat.gcd_pos_of_pos_left D haPos
  have hgD : Nat.gcd a D ∣ D := Nat.gcd_dvd_right a D
  have hgNe : Nat.gcd a D ≠ D := by
    intro h
    apply hnot
    have hga : Nat.gcd a D ∣ a := Nat.gcd_dvd_left a D
    simpa [h] using hga
  exact ⟨hgPos, hgD, hgNe⟩

/-- Four d-units of interval length suffice to produce two distinct d-multiples
outside both anchors. -/
theorem off_two_anchor_card_ge_two_of_four_mul_le
    {L x y : ℤ} {M d : ℕ}
    (hdPos : 0 < d)
    (hxI : x ∈ integerInterval L M)
    (hdX : (d : ℤ) ∣ x)
    (hfour : 4 * d ≤ M) :
    2 ≤ (offTwoAnchorMultiples L M x y d).card := by
  classical
  obtain ⟨z₁, hz₁I, hz₁D, hz₁F⟩ :=
    exists_interval_multiple_outside_finset_candidate
      (F := ({x, y} : Finset ℤ))
      (L := L) (x := x) (M := M) (d := d) (k := 2)
      hdPos hxI hdX (by omega) Finset.card_le_two
  have hz₁X : z₁ ≠ x := by
    intro h
    apply hz₁F
    simp [h]
  have hz₁Y : z₁ ≠ y := by
    intro h
    apply hz₁F
    simp [h]
  obtain ⟨z₂, hz₂I, hz₂D, hz₂F⟩ :=
    exists_interval_multiple_outside_finset_candidate
      (F := ({x, y, z₁} : Finset ℤ))
      (L := L) (x := x) (M := M) (d := d) (k := 3)
      hdPos hxI hdX (by simpa using hfour) Finset.card_le_three
  have hz₂X : z₂ ≠ x := by
    intro h
    apply hz₂F
    simp [h]
  have hz₂Y : z₂ ≠ y := by
    intro h
    apply hz₂F
    simp [h]
  have hz₂Z₁ : z₂ ≠ z₁ := by
    intro h
    apply hz₂F
    simp [h]
  have hsub :
      ({z₁, z₂} : Finset ℤ) ⊆ offTwoAnchorMultiples L M x y d := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [offTwoAnchorMultiples, hz₁I, hz₁X, hz₁Y, hz₁D]
    · simp [offTwoAnchorMultiples, hz₂I, hz₂X, hz₂Y, hz₂D]
  have hle := Finset.card_le_card hsub
  have hpair : ({z₁, z₂} : Finset ℤ).card = 2 := by
    simp [hz₂Z₁.symm]
  rw [hpair] at hle
  exact hle

/-- If two off-anchor candidate families are both forced into a union of size at
most two, they are the same family. -/
theorem equal_of_two_large_subsets_of_card_le_two
    {α : Type*} [DecidableEq α]
    {A B U : Finset α}
    (hA : A ⊆ U)
    (hB : B ⊆ U)
    (hAc : 2 ≤ A.card)
    (hBc : 2 ≤ B.card)
    (hUc : U.card ≤ 2) :
    A = B := by
  have hAU : A = U := by
    apply Finset.eq_of_subset_of_card_le hA
    have hle := Finset.card_le_card hA
    omega
  have hBU : B = U := by
    apply Finset.eq_of_subset_of_card_le hB
    have hle := Finset.card_le_card hB
    omega
  rw [hAU, hBU]

/-- Equality of the off-anchor r- and s-multiple families forces s|r.  This is
the compiler-friendly replacement for the four-point AP rigidity argument. -/
theorem dvd_of_equal_off_two_anchor_multiples
    {L x y : ℤ} {M r s D : ℕ}
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hdir : y = x + (D : ℤ) ∨ x = y + (D : ℤ))
    (hrPos : 0 < r)
    (hrLtD : r < D)
    (hrX : (r : ℤ) ∣ x)
    (hsX : (s : ℤ) ∣ x)
    (hEq :
      offTwoAnchorMultiples L M x y r =
        offTwoAnchorMultiples L M x y s) :
    s ∣ r := by
  rcases hdir with hxy | hyx
  · let z : ℤ := x + (r : ℤ)
    have hrPosZ : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hrPos
    have hrDZ : (r : ℤ) < (D : ℤ) := by exact_mod_cast hrLtD
    have hxyLt : x < y := by
      rw [hxy]
      omega
    have hzBetween : min x y ≤ z ∧ z ≤ max x y := by
      rw [min_eq_left hxyLt.le, max_eq_right hxyLt.le]
      dsimp [z]
      rw [hxy]
      constructor <;> omega
    have hzI : z ∈ integerInterval L M :=
      integerInterval_mem_of_between hxI hyI hzBetween
    have hzX : z ≠ x := by
      dsimp [z]
      omega
    have hzY : z ≠ y := by
      dsimp [z]
      rw [hxy]
      omega
    have hrZ : (r : ℤ) ∣ z := by
      rcases hrX with ⟨q, hq⟩
      refine ⟨q + 1, ?_⟩
      dsimp [z]
      rw [hq]
      ring
    have hzR : z ∈ offTwoAnchorMultiples L M x y r := by
      simp [offTwoAnchorMultiples, hzI, hzX, hzY, hrZ]
    have hzS : z ∈ offTwoAnchorMultiples L M x y s := by
      rw [← hEq]
      exact hzR
    have hsZ : (s : ℤ) ∣ z :=
      (Finset.mem_filter.mp hzS).2.2.2
    have hsRInt : (s : ℤ) ∣ (r : ℤ) := by
      rcases hsX with ⟨u, hu⟩
      rcases hsZ with ⟨v, hv⟩
      refine ⟨v - u, ?_⟩
      calc
        (r : ℤ) = z - x := by
          dsimp [z]
          ring
        _ = (s : ℤ) * v - (s : ℤ) * u := by rw [hv, hu]
        _ = (s : ℤ) * (v - u) := by ring
    exact_mod_cast hsRInt
  · let z : ℤ := x - (r : ℤ)
    have hrPosZ : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hrPos
    have hrDZ : (r : ℤ) < (D : ℤ) := by exact_mod_cast hrLtD
    have hyxLt : y < x := by
      rw [hyx]
      omega
    have hzBetween : min x y ≤ z ∧ z ≤ max x y := by
      rw [min_eq_right hyxLt.le, max_eq_left hyxLt.le]
      dsimp [z]
      rw [hyx]
      constructor <;> omega
    have hzI : z ∈ integerInterval L M :=
      integerInterval_mem_of_between hxI hyI hzBetween
    have hzX : z ≠ x := by
      dsimp [z]
      omega
    have hzY : z ≠ y := by
      dsimp [z]
      rw [hyx]
      omega
    have hrZ : (r : ℤ) ∣ z := by
      rcases hrX with ⟨q, hq⟩
      refine ⟨q - 1, ?_⟩
      dsimp [z]
      rw [hq]
      ring
    have hzR : z ∈ offTwoAnchorMultiples L M x y r := by
      simp [offTwoAnchorMultiples, hzI, hzX, hzY, hrZ]
    have hzS : z ∈ offTwoAnchorMultiples L M x y s := by
      rw [← hEq]
      exact hzR
    have hsZ : (s : ℤ) ∣ z :=
      (Finset.mem_filter.mp hzS).2.2.2
    have hsRInt : (s : ℤ) ∣ (r : ℤ) := by
      rcases hsX with ⟨u, hu⟩
      rcases hsZ with ⟨v, hv⟩
      refine ⟨u - v, ?_⟩
      calc
        (r : ℤ) = x - z := by
          dsimp [z]
          ring
        _ = (s : ℤ) * u - (s : ℤ) * v := by rw [hu, hv]
        _ = (s : ℤ) * (u - v) := by ring
    exact_mod_cast hsRInt

/-- Symmetric divisibility gives equality of the two moduli. -/
theorem eq_of_equal_off_two_anchor_multiples
    {L x y : ℤ} {M r s D : ℕ}
    (hxI : x ∈ integerInterval L M)
    (hyI : y ∈ integerInterval L M)
    (hdir : y = x + (D : ℤ) ∨ x = y + (D : ℤ))
    (hrPos : 0 < r)
    (hsPos : 0 < s)
    (hrLtD : r < D)
    (hsLtD : s < D)
    (hrX : (r : ℤ) ∣ x)
    (hsX : (s : ℤ) ∣ x)
    (hEq :
      offTwoAnchorMultiples L M x y r =
        offTwoAnchorMultiples L M x y s) :
    r = s := by
  apply Nat.dvd_antisymm
  · exact dvd_of_equal_off_two_anchor_multiples
      hxI hyI hdir hsPos hsLtD hsX hrX hEq.symm
  · exact dvd_of_equal_off_two_anchor_multiples
      hxI hyI hdir hrPos hrLtD hrX hsX hEq

end Erdos708
