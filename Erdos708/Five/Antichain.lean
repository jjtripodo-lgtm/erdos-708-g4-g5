module

public import Mathlib.Tactic

@[expose] public section

/-!
# Divisibility antichains in `{1, …, N}`

Odd-part chains show that a divisibility antichain in `{1, …, N}` has at most `⌈N/2⌉`
elements. Consequences used by the five-modulus argument:
* two incomparable multiples of `q` that are at most `M` force `3q ≤ M`;
* three pairwise incomparable multiples force `5q ≤ M`.
-/

namespace Erdos708.Five

/-- Two positive integers with the same odd part are comparable under divisibility. -/
theorem dvd_or_dvd_of_ordCompl_eq {m n : ℕ}
    (h : ordCompl[2] m = ordCompl[2] n) : m ∣ n ∨ n ∣ m := by
  have hm' := Nat.ordProj_mul_ordCompl_eq_self m 2
  have hn' := Nat.ordProj_mul_ordCompl_eq_self n 2
  rcases le_total (m.factorization 2) (n.factorization 2) with hle | hle
  · left
    rw [← hm', ← hn', h]
    exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 hle) _
  · right
    rw [← hm', ← hn', h]
    exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 hle) _

theorem ordCompl_two_odd {n : ℕ} (hn : n ≠ 0) : ordCompl[2] n % 2 = 1 := by
  have hcop := Nat.coprime_ordCompl Nat.prime_two hn
  have hodd : Odd (ordCompl[2] n) := (Nat.coprime_two_left).mp hcop
  exact Nat.odd_iff.mp hodd

/-- **Antichain bound.** A divisibility antichain of positive integers at most `N` has at most
`(N + 1) / 2` elements. -/
theorem card_le_of_dvd_antichain {S : Finset ℕ} {N : ℕ}
    (hpos : ∀ n ∈ S, 0 < n) (hle : ∀ n ∈ S, n ≤ N)
    (hanti : ∀ m ∈ S, ∀ n ∈ S, m ∣ n → m = n) :
    S.card ≤ (N + 1) / 2 := by
  classical
  let f : ℕ → ℕ := fun n => (ordCompl[2] n - 1) / 2
  have hmaps : ∀ n ∈ S, f n ∈ Finset.range ((N + 1) / 2) := by
    intro n hn
    have hn0 : n ≠ 0 := (hpos n hn).ne'
    have hodd := ordCompl_two_odd hn0
    have hleN : ordCompl[2] n ≤ N := (Nat.ordCompl_le n 2).trans (hle n hn)
    rw [Finset.mem_range]
    simp only [f]
    generalize ordCompl[2] n = o at hodd hleN ⊢
    omega
  have hinj : Set.InjOn f S := by
    intro m hm n hn hfmn
    have hm0 : m ≠ 0 := (hpos m hm).ne'
    have hn0 : n ≠ 0 := (hpos n hn).ne'
    have hoddm := ordCompl_two_odd hm0
    have hoddn := ordCompl_two_odd hn0
    have heq : ordCompl[2] m = ordCompl[2] n := by
      simp only [f] at hfmn
      generalize ordCompl[2] m = o₁ at hoddm hfmn ⊢
      generalize ordCompl[2] n = o₂ at hoddn hfmn ⊢
      omega
    rcases dvd_or_dvd_of_ordCompl_eq heq with h | h
    · exact hanti m hm n hn h
    · exact (hanti n hn m hm h).symm
  calc S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range ((N + 1) / 2)).card :=
        Finset.card_le_card (fun y hy => by
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
          exact hmaps n hn)
    _ = (N + 1) / 2 := Finset.card_range _

/-- Two incomparable multiples of `q` that are at most `M` force `3q ≤ M`. -/
theorem three_mul_le_of_incomparable {q x y M : ℕ} (hq : 0 < q)
    (hx : q ∣ x) (hy : q ∣ y) (hx0 : 0 < x) (hy0 : 0 < y) (hxM : x ≤ M) (hyM : y ≤ M)
    (hxy : ¬ x ∣ y) (hyx : ¬ y ∣ x) :
    3 * q ≤ M := by
  classical
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hs0 : 0 < s := Nat.pos_of_mul_pos_left hx0
  have ht0 : 0 < t := Nat.pos_of_mul_pos_left hy0
  have hst : s ≠ t := by
    rintro rfl
    exact hxy dvd_rfl
  have hcard := card_le_of_dvd_antichain (S := {s, t}) (N := M / q)
    (by intro n hn; simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with rfl | rfl <;> assumption)
    (by intro n hn; simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with rfl | rfl
        · exact (Nat.le_div_iff_mul_le hq).mpr (by linarith [mul_comm q n])
        · exact (Nat.le_div_iff_mul_le hq).mpr (by linarith [mul_comm q n]))
    (by intro m hm n hn hmn
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm hn
        rcases hm with rfl | rfl <;> rcases hn with rfl | rfl
        · rfl
        · exact absurd (Nat.mul_dvd_mul_left q hmn) hxy
        · exact absurd (Nat.mul_dvd_mul_left q hmn) hyx
        · rfl)
  rw [Finset.card_pair hst] at hcard
  have h3 : 3 ≤ M / q := by omega
  calc 3 * q ≤ M / q * q := Nat.mul_le_mul_right q h3
    _ ≤ M := Nat.div_mul_le_self M q

/-- Three pairwise incomparable multiples of `q` that are at most `M` force `5q ≤ M`. -/
theorem five_mul_le_of_incomparable_three {q x y z M : ℕ} (hq : 0 < q)
    (hx : q ∣ x) (hy : q ∣ y) (hz : q ∣ z)
    (hx0 : 0 < x) (hy0 : 0 < y) (hz0 : 0 < z)
    (hxM : x ≤ M) (hyM : y ≤ M) (hzM : z ≤ M)
    (hxy : ¬ x ∣ y) (hyx : ¬ y ∣ x) (hxz : ¬ x ∣ z) (hzx : ¬ z ∣ x)
    (hyz : ¬ y ∣ z) (hzy : ¬ z ∣ y) :
    5 * q ≤ M := by
  classical
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  obtain ⟨u, rfl⟩ := hz
  have hs0 : 0 < s := Nat.pos_of_mul_pos_left hx0
  have ht0 : 0 < t := Nat.pos_of_mul_pos_left hy0
  have hu0 : 0 < u := Nat.pos_of_mul_pos_left hz0
  have hst : s ≠ t := by rintro rfl; exact hxy dvd_rfl
  have hsu : s ≠ u := by rintro rfl; exact hxz dvd_rfl
  have htu : t ≠ u := by rintro rfl; exact hyz dvd_rfl
  have hbound : ∀ n, q * n ≤ M → n ≤ M / q := fun n h =>
    (Nat.le_div_iff_mul_le hq).mpr (by linarith [mul_comm q n])
  have hcard := card_le_of_dvd_antichain (S := {s, t, u}) (N := M / q)
    (by intro n hn; simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with rfl | rfl | rfl <;> assumption)
    (by intro n hn; simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with rfl | rfl | rfl
        · exact hbound _ hxM
        · exact hbound _ hyM
        · exact hbound _ hzM)
    (by intro m hm n hn hmn
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm hn
        have key := Nat.mul_dvd_mul_left q hmn
        rcases hm with rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl <;>
          first | rfl | exact absurd key ‹_›)
  have h3 : ({s, t, u} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hst, hsu]), Finset.card_pair htu]
  rw [h3] at hcard
  have h5 : 5 ≤ M / q := by omega
  calc 5 * q ≤ M / q * q := Nat.mul_le_mul_right q h5
    _ ≤ M := Nat.div_mul_le_self M q

end Erdos708.Five
