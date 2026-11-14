module

public import Erdos708.IntervalMultiples
public import Mathlib.Tactic

@[expose] public section

/-!
Interval infrastructure for the four-modulus one-defect proof.

This module is part of the trusted one-defect dependency graph.  Its helper
names retain the historical `_candidate` suffix.
-/

namespace Erdos708

/--
If an M-term interval contains one multiple x of d and (k+1)d <= M, then the
interval contains at least k+1 multiples of d.

The proof translates x to zero, uses the already-banked nonzero-multiple count,
and transports cardinality back by the translation bijection.
-/
theorem card_interval_multiples_ge_of_known_multiple_candidate
    {L x : ℤ} {M d k : ℕ}
    (hd : 0 < d)
    (hx : x ∈ integerInterval L M)
    (hxd : (d : ℤ) ∣ x)
    (hM : (k + 1) * d ≤ M) :
    k + 1 ≤
      ((integerInterval L M).filter (fun z => (d : ℤ) ∣ z)).card := by
  classical
  let L' : ℤ := L - x
  let T := integerInterval L' M
  let Tm := T.filter (fun z => (d : ℤ) ∣ z)
  let S := (integerInterval L M).filter (fun z => (d : ℤ) ∣ z)

  have hzeroT : (0 : ℤ) ∈ T := by
    have htrans :=
      (integerInterval_mem_translate (L := L) (z := x) (q := -x) (M := M)).1 hx
    simpa [L', T, sub_eq_add_neg] using htrans

  have hL' : L' ≤ 0 := by
    rw [mem_integerInterval] at hzeroT
    exact hzeroT.1
  have hU' : 0 ≤ L' + (M : ℤ) - 1 := by
    rw [mem_integerInterval] at hzeroT
    exact hzeroT.2

  have hnonzero :
      k ≤ (T.filter (fun z => z ≠ 0 ∧ (d : ℤ) ∣ z)).card := by
    simpa [T] using
      (card_nonzero_multiples_ge
        (L := L') (M := M) (d := d) (k := k)
        hL' hU' hd hM)

  have hzeroTm : (0 : ℤ) ∈ Tm := by
    simp [Tm, T, hzeroT]

  have hErase :
      Tm.erase 0 =
        T.filter (fun z => z ≠ 0 ∧ (d : ℤ) ∣ z) := by
    ext z
    simp [Tm, and_assoc, and_left_comm, and_comm]

  have hTmCard : k + 1 ≤ Tm.card := by
    have hEraseCard : (Tm.erase 0).card + 1 = Tm.card := by
      rw [Finset.card_erase_of_mem hzeroTm]
      have hcardpos : 0 < Tm.card := Finset.card_pos.mpr ⟨0, hzeroTm⟩
      omega
    rw [hErase] at hEraseCard
    omega

  have hnegx : (d : ℤ) ∣ -x := dvd_neg.mpr hxd

  have hcard : S.card = Tm.card := by
    apply Finset.card_bij (fun z _ => z - x)
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      have hzI : z ∈ integerInterval L M := hz'.1
      have hzd : (d : ℤ) ∣ z := hz'.2
      have hzT :
          z - x ∈ integerInterval (L - x) M := by
        have htrans :=
          (integerInterval_mem_translate
            (L := L) (z := z) (q := -x) (M := M)).1 hzI
        simpa [sub_eq_add_neg] using htrans
      have hdiv : (d : ℤ) ∣ z - x := by
        have hiff := dvd_iff_of_dvd_translation (d := (d : ℤ)) (z := z) (q := -x) hnegx
        simpa [sub_eq_add_neg] using hiff.1 hzd
      exact Finset.mem_filter.mpr ⟨by simpa [T, L'] using hzT, hdiv⟩
    · intro a ha b hb hab
      omega
    · intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hyT : y ∈ integerInterval (L - x) M := by
        simpa [T, L'] using hy'.1
      have hyT' : y ∈ integerInterval (L + -x) M := by
        simpa [sub_eq_add_neg] using hyT
      have hyd : (d : ℤ) ∣ y := hy'.2
      let z : ℤ := y + x
      have hzI : z ∈ integerInterval L M := by
        have hback :=
          (integerInterval_mem_translate
            (L := L) (z := z) (q := -x) (M := M))
        have hzminus : z - x = y := by
          dsimp [z]
          omega
        apply hback.2
        simpa [z, sub_eq_add_neg, hzminus] using hyT'
      have hzd : (d : ℤ) ∣ z := by
        dsimp [z]
        exact dvd_add hyd hxd
      refine ⟨z, Finset.mem_filter.mpr ⟨hzI, hzd⟩, ?_⟩
      dsimp [z]
      omega

  simpa [S] using hTmCard.trans_eq hcard.symm

/--
If at most k interval points are forbidden, the same hypotheses produce a
d-multiple outside the forbidden set.
-/
theorem exists_interval_multiple_outside_finset_candidate
    {L x : ℤ} {M d k : ℕ}
    (F : Finset ℤ)
    (hd : 0 < d)
    (hx : x ∈ integerInterval L M)
    (hxd : (d : ℤ) ∣ x)
    (hM : (k + 1) * d ≤ M)
    (hF : F.card ≤ k) :
    ∃ y ∈ integerInterval L M, (d : ℤ) ∣ y ∧ y ∉ F := by
  classical
  let S := (integerInterval L M).filter (fun z => (d : ℤ) ∣ z)
  have hScard : k + 1 ≤ S.card := by
    simpa [S] using
      (card_interval_multiples_ge_of_known_multiple_candidate
        (L := L) (x := x) (M := M) (d := d) (k := k)
        hd hx hxd hM)
  have hnsub : ¬ S ⊆ F := by
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  have hex : ∃ y, y ∈ S ∧ y ∉ F := by
    simpa [Finset.not_subset] using hnsub
  rcases hex with ⟨y, hyS, hyF⟩
  have hy := Finset.mem_filter.mp hyS
  exact ⟨y, hy.1, hy.2, hyF⟩

end Erdos708
