module

public import Erdos708.TwoPointClassification
public import Erdos708.TwoAnchorCombined
public import Erdos708.CoverPackaging
public import Erdos708.MatchingToCover
public import Erdos708.TwoAnchorExceptionalCore
public import Mathlib.Tactic

@[expose] public section

/-!
routing for the full two-point neighborhood branch in the
Erdős #708 exhaustion.

Input:
* the four concrete modulus-candidate families are nonempty;
* every triple union has at least two real points;
* the full union has at most two real points;
* zero is not in the interval.

Output: FourModuliCover.

The proof first shows the full union is exactly two points.  It then classifies
the four families as singleton/singleton/singleton/(singleton or bridge), with
at most one bridge.  The already-staged combined two-anchor theorem handles
that normalized pattern.

This file is intentionally outside the trusted import graph and is NOT Banked.
-/

namespace Erdos708

/-- Two distinct integer anchors have a positive natural distance, oriented in
one of the two possible directions. -/
theorem exists_positive_anchor_distance_candidate
    {x y : ℤ} (hxy : x ≠ y) :
    ∃ D : ℕ, 0 < D ∧
      (y = x + (D : ℤ) ∨ x = y + (D : ℤ)) := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · let D : ℕ := (y - x).natAbs
    have hnonneg : 0 ≤ y - x := by omega
    have hcast : (D : ℤ) = y - x := by
      dsimp [D]
      rw [Int.natAbs_of_nonneg hnonneg]
    have hDPosZ : (0 : ℤ) < (D : ℤ) := by
      rw [hcast]
      omega
    have hDPos : 0 < D := by exact_mod_cast hDPosZ
    refine ⟨D, hDPos, Or.inl ?_⟩
    rw [hcast]
    omega
  · let D : ℕ := (x - y).natAbs
    have hnonneg : 0 ≤ x - y := by omega
    have hcast : (D : ℤ) = x - y := by
      dsimp [D]
      rw [Int.natAbs_of_nonneg hnonneg]
    have hDPosZ : (0 : ℤ) < (D : ℤ) := by
      rw [hcast]
      omega
    have hDPos : 0 < D := by exact_mod_cast hDPosZ
    refine ⟨D, hDPos, Or.inr ?_⟩
    rw [hcast]
    omega

/-- Membership of a concrete candidate family exposes interval membership and
the appropriate indexed divisibility. -/
theorem candidate_pair_point_data_candidate
    {L x y : ℤ} {M a b c d : ℕ} {i : Fin 4}
    (hEq : fourMultipleCandidates L M a b c d i = {x, y})
    (hxy : x ≠ y) :
    x ∈ integerInterval L M ∧
    y ∈ integerInterval L M ∧
    (fourModulus a b c d i : ℤ) ∣ x ∧
    (fourModulus a b c d i : ℤ) ∣ y := by
  have hx : x ∈ fourMultipleCandidates L M a b c d i := by
    rw [hEq]
    simp
  have hy : y ∈ fourMultipleCandidates L M a b c d i := by
    rw [hEq]
    simp [hxy]
  have hxd := mem_fourMultipleCandidates_candidate.mp hx
  have hyd := mem_fourMultipleCandidates_candidate.mp hy
  exact ⟨hxd.1, hyd.1, hxd.2, hyd.2⟩

/-- A concrete modulus whose candidate family is exactly the two anchors equals
the positive anchor distance. -/
theorem bridge_modulus_eq_anchor_distance_candidate
    {L x y : ℤ} {M a b c d D : ℕ} {i : Fin 4}
    (hDPos : 0 < D)
    (hdir : y = x + (D : ℤ) ∨ x = y + (D : ℤ))
    (hmodPos : 0 < fourModulus a b c d i)
    (hEq : fourMultipleCandidates L M a b c d i = {x, y}) :
    fourModulus a b c d i = D := by
  have hxy : x ≠ y := by
    rcases hdir with h | h <;> rw [h] <;> push_cast <;> omega
  have hdata :=
    candidate_pair_point_data_candidate hEq hxy
  have hmX := hdata.2.2.1
  have hmY := hdata.2.2.2
  have hmDInt :
      (fourModulus a b c d i : ℤ) ∣ (D : ℤ) := by
    rcases hmX with ⟨u, hu⟩
    rcases hmY with ⟨v, hv⟩
    rcases hdir with hxyDir | hyxDir
    · refine ⟨v - u, ?_⟩
      calc
        (D : ℤ) = y - x := by rw [hxyDir]; ring
        _ = (fourModulus a b c d i : ℤ) * v -
            (fourModulus a b c d i : ℤ) * u := by rw [hv, hu]
        _ = (fourModulus a b c d i : ℤ) * (v - u) := by ring
    · refine ⟨u - v, ?_⟩
      calc
        (D : ℤ) = x - y := by rw [hyxDir]; ring
        _ = (fourModulus a b c d i : ℤ) * u -
            (fourModulus a b c d i : ℤ) * v := by rw [hu, hv]
        _ = (fourModulus a b c d i : ℤ) * (u - v) := by ring
  have hmD : fourModulus a b c d i ∣ D := by
    exact_mod_cast hmDInt
  have honly :
      ∀ z, z ∈ integerInterval L M →
        (fourModulus a b c d i : ℤ) ∣ z →
        z = x ∨ z = y := by
    intro z hzI hzD
    have hz : z ∈ fourMultipleCandidates L M a b c d i :=
      mem_fourMultipleCandidates_candidate.mpr ⟨hzI, hzD⟩
    rw [hEq] at hz
    simpa using hz
  exact modulus_eq_anchor_distance_of_only_anchor_multiples
    hDPos hmodPos hmD hdata.1 hdata.2.1 hdir
    hdata.2.2.1 honly

/-- Distinct original moduli imply there is at most one family using both
anchors. -/
theorem bridge_family_unique_candidate
    {L x y : ℤ} {M a b c d D : ℕ}
    (hDPos : 0 < D)
    (hdir : y = x + (D : ℤ) ∨ x = y + (D : ℤ))
    (hTwo : ∀ i, 2 ≤ fourModulus a b c d i)
    (hInj : Function.Injective (fourModulus a b c d)) :
    ∀ i j,
      fourMultipleCandidates L M a b c d i = {x, y} →
      fourMultipleCandidates L M a b c d j = {x, y} →
      i = j := by
  intro i j hi hj
  apply hInj
  have hiD :=
    bridge_modulus_eq_anchor_distance_candidate
      hDPos hdir (by have := hTwo i; omega) hi
  have hjD :=
    bridge_modulus_eq_anchor_distance_candidate
      hDPos hdir (by have := hTwo j; omega) hj
  exact hiD.trans hjD.symm

/-- Singleton candidate set gives a unique assigned anchor for that modulus. -/
theorem unique_anchor_of_candidate_singleton_candidate
    {L x : ℤ} {M a b c d : ℕ} {i : Fin 4}
    (hEq : fourMultipleCandidates L M a b c d i = {x}) :
    x ∈ integerInterval L M ∧
    (fourModulus a b c d i : ℤ) ∣ x ∧
    ∀ z, z ∈ integerInterval L M →
      (fourModulus a b c d i : ℤ) ∣ z → z = x := by
  have hx : x ∈ fourMultipleCandidates L M a b c d i := by
    rw [hEq]
    simp
  have hdata := mem_fourMultipleCandidates_candidate.mp hx
  refine ⟨hdata.1, hdata.2, ?_⟩
  intro z hzI hzD
  have hz : z ∈ fourMultipleCandidates L M a b c d i :=
    mem_fourMultipleCandidates_candidate.mpr ⟨hzI, hzD⟩
  rw [hEq] at hz
  simpa using hz

/-- The full two-point deficiency branch routes to the combined two-anchor
theorem after finite family classification. -/
theorem fourModuliCover_of_two_point_deficiency_candidate
    {L : ℤ} {M a b c d : ℕ}
    (haTwo : 2 ≤ a) (hbTwo : 2 ≤ b) (hcTwo : 2 ≤ c) (hdTwo : 2 ≤ d)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (htriple :
      ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
        2 ≤
          ((fourMultipleCandidates L M a b c d i ∪
            fourMultipleCandidates L M a b c d j) ∪
            fourMultipleCandidates L M a b c d k).card)
    (hfull :
      (Finset.univ.biUnion
        (fourMultipleCandidates L M a b c d)).card ≤ 2) :
    FourModuliCover L M a b c d := by
  classical
  let C : Fin 4 → Finset ℤ :=
    fourMultipleCandidates L M a b c d
  have hnonempty : ∀ i, (C i).Nonempty := by
    intro i
    exact fourMultipleCandidates_nonempty_candidate
      (by omega) (by omega) (by omega) (by omega)
      haM hbM hcM hdM i
  have hsubFull (i : Fin 4) :
      C i ⊆ Finset.univ.biUnion C := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨i, by simp, hz⟩
  have hfullGe2 :
      2 ≤ (Finset.univ.biUnion C).card := by
    have ht := htriple 0 1 2 (by decide) (by decide) (by decide)
    have hsub :
        (C 0 ∪ C 1) ∪ C 2 ⊆ Finset.univ.biUnion C := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz01 | hz2
      · rcases Finset.mem_union.mp hz01 with hz0 | hz1
        · exact hsubFull 0 hz0
        · exact hsubFull 1 hz1
      · exact hsubFull 2 hz2
    exact ht.trans (Finset.card_le_card hsub)
  have hfullEq2 :
      (Finset.univ.biUnion C).card = 2 := by
    have hfullLe : (Finset.univ.biUnion C).card ≤ 2 := by
      simpa [C] using hfull
    omega
  rcases Finset.card_eq_two.mp hfullEq2 with
    ⟨x, y, hxy, hUeq⟩
  have hxU : x ∈ Finset.univ.biUnion C := by
    rw [hUeq]
    simp
  have hyU : y ∈ Finset.univ.biUnion C := by
    rw [hUeq]
    simp [hxy]
  have hxI : x ∈ integerInterval L M := by
    rcases Finset.mem_biUnion.mp hxU with ⟨i, hi, hxi⟩
    exact (mem_fourMultipleCandidates_candidate.mp (by simpa [C] using hxi)).1
  have hyI : y ∈ integerInterval L M := by
    rcases Finset.mem_biUnion.mp hyU with ⟨i, hi, hyi⟩
    exact (mem_fourMultipleCandidates_candidate.mp (by simpa [C] using hyi)).1

  obtain ⟨D, hDPos, hdir⟩ :=
    exists_positive_anchor_distance_candidate hxy

  have hTwo :
      ∀ i, 2 ≤ fourModulus a b c d i :=
    fourModulus_two_le_candidate haTwo hbTwo hcTwo hdTwo
  have hBound :
      ∀ i, fourModulus a b c d i ≤ M :=
    fourModulus_le_candidate haM hbM hcM hdM
  have hModInj :
      Function.Injective (fourModulus a b c d) :=
    fourModulus_injective_candidate hab hac had hbc hbd hcd

  have hsubPair : ∀ i, C i ⊆ {x, y} := by
    intro i z hz
    have hzU := hsubFull i hz
    rw [hUeq] at hzU
    exact hzU
  have htripleC :
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        2 ≤ ((C i ∪ C j) ∪ C k).card := by
    intro i j k hij hik hjk
    simpa [C] using htriple i j k hij hik hjk
  have hBridgeUnique :
      ∀ i j, C i = {x, y} → C j = {x, y} → i = j := by
    intro i j hi hj
    apply bridge_family_unique_candidate
      (L := L) (M := M) (a := a) (b := b) (c := c) (d := d)
      hDPos hdir hTwo hModInj i j
    · simpa [C] using hi
    · simpa [C] using hj

  obtain
      ⟨x', y', p, q, r, s,
        hpair, hxy', hpq, hpr, hps, hqr, hqs, hrs,
        hpEq, hqEq, hrEq, hsRoute⟩ :=
    normalized_two_point_route_candidate
      C hxy hnonempty hsubPair htripleC hBridgeUnique

  have hx'Mem : x' ∈ ({x, y} : Finset ℤ) := by
    rw [← hpair]
    simp
  have hy'Mem : y' ∈ ({x, y} : Finset ℤ) := by
    rw [← hpair]
    simp [hxy']
  have hx'I : x' ∈ integerInterval L M := by
    rcases (by simpa using hx'Mem) with hxx | hxyv
    · simpa [hxx] using hxI
    · simpa [hxyv] using hyI
  have hy'I : y' ∈ integerInterval L M := by
    rcases (by simpa using hy'Mem) with hyxv | hyy
    · simpa [hyxv] using hxI
    · simpa [hyy] using hyI

  obtain ⟨D', hD'Pos, hdir'⟩ :=
    exists_positive_anchor_distance_candidate hxy'

  let A := fourModulus a b c d
  have hpData :
      x' ∈ integerInterval L M ∧
      (A p : ℤ) ∣ x' ∧
      ∀ z, z ∈ integerInterval L M → (A p : ℤ) ∣ z → z = x' := by
    apply unique_anchor_of_candidate_singleton_candidate
    simpa [C, A] using hpEq
  have hqData :
      x' ∈ integerInterval L M ∧
      (A q : ℤ) ∣ x' ∧
      ∀ z, z ∈ integerInterval L M → (A q : ℤ) ∣ z → z = x' := by
    apply unique_anchor_of_candidate_singleton_candidate
    simpa [C, A] using hqEq
  have hrData :
      y' ∈ integerInterval L M ∧
      (A r : ℤ) ∣ y' ∧
      ∀ z, z ∈ integerInterval L M → (A r : ℤ) ∣ z → z = y' := by
    apply unique_anchor_of_candidate_singleton_candidate
    simpa [C, A] using hrEq

  have hApq : A p ≠ A q := by
    exact fun h => hpq (hModInj h)
  have hApr : A p ≠ A r := by
    exact fun h => hpr (hModInj h)
  have hAps : A p ≠ A s := by
    exact fun h => hps (hModInj h)
  have hAqr : A q ≠ A r := by
    exact fun h => hqr (hModInj h)
  have hAqs : A q ≠ A s := by
    exact fun h => hqs (hModInj h)
  have hArs : A r ≠ A s := by
    exact fun h => hrs (hModInj h)

  have hCoverOrdered :
      TwoAnchorCover L M x' y' (A p) (A q) (A r) (A s) := by
    apply two_anchor_combined_candidate
      (haPos := by have := hTwo p; omega)
      (hbPos := by have := hTwo q; omega)
      (hcPos := by have := hTwo r; omega)
      (hdPos := by have := hTwo s; omega)
      (haM := hBound p) (hbM := hBound q)
      (hcM := hBound r) (hdM := hBound s)
      hApq hApr hAps hAqr hAqs hArs
      hpData.1 hrData.1 hxy'
      hpData.2.1 hqData.2.1 hrData.2.1
      hpData.2.2 hqData.2.2 hrData.2.2
    rcases hsRoute with hsSingle | hsBridge
    · left
      have hsData :
          y' ∈ integerInterval L M ∧
          (A s : ℤ) ∣ y' ∧
          ∀ z, z ∈ integerInterval L M → (A s : ℤ) ∣ z → z = y' := by
        apply unique_anchor_of_candidate_singleton_candidate
        simpa [C, A] using hsSingle
      exact ⟨hsData.2.1, hsData.2.2⟩
    · right
      have hsEqD :
          A s = D' := by
        apply bridge_modulus_eq_anchor_distance_candidate
          (L := L) (M := M) (a := a) (b := b) (c := c) (d := d)
          hD'Pos hdir' (by have := hTwo s; omega)
        simpa [C, A] using hsBridge
      have hsPair :
          x' ∈ integerInterval L M ∧
          y' ∈ integerInterval L M ∧
          (A s : ℤ) ∣ x' ∧
          (A s : ℤ) ∣ y' := by
        apply candidate_pair_point_data_candidate
        · simpa [C, A] using hsBridge
        · exact hxy'
      refine ⟨?_, hsPair.2.2.1, hsPair.2.2.2⟩
      rcases hdir' with hdir' | hdir'
      · left
        change y' = x' + (A s : ℤ)
        rw [hsEqD]
        exact hdir'
      · right
        change x' = y' + (A s : ℤ)
        rw [hsEqD]
        exact hdir'

  have hCoverPerm :
      FourModuliCover L M (A p) (A q) (A r) (A s) :=
    fourModuliCover_of_twoAnchorCover_candidate
      hpData.1 hrData.1 hxy' hCoverOrdered
  have hprod :
      (a : ℤ) * (b : ℤ) * (c : ℤ) * (d : ℤ) =
        (A p : ℤ) * (A q : ℤ) * (A r : ℤ) * (A s : ℤ) := by
    symm
    exact fourModulus_product_of_distinct_indices_candidate
      hpq hpr hps hqr hqs hrs
  exact fourModuliCover_of_same_product_candidate hprod hCoverPerm

end Erdos708
