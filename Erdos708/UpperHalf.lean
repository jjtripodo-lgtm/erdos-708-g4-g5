module

public import Erdos708.Arithmetic
public import Mathlib.Tactic

@[expose] public section

namespace Erdos708

/-- Two distinct upper-half multiples of a common divisor force three
copies of that divisor into the ambient range. -/
theorem pair_gcd_le_one_third {M a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (haM : a ≤ M) (hbM : b ≤ M)
    (haHalf : M < 2 * a) (hbHalf : M < 2 * b)
    (hab : a ≠ b) :
    3 * Nat.gcd a b ≤ M := by
  let d := Nat.gcd a b
  have hd : 0 < d := Nat.gcd_pos_of_pos_left b ha
  have hda : d ∣ a := Nat.gcd_dvd_left a b
  have hdb : d ∣ b := Nat.gcd_dvd_right a b
  rcases dvd_iff_exists_eq_mul_right.mp hda with ⟨u, hu⟩
  rcases dvd_iff_exists_eq_mul_right.mp hdb with ⟨v, hv⟩
  have hu0 : 0 < u := by
    by_contra h
    have huZero : u = 0 := by omega
    rw [huZero] at hu
    simp at hu
    omega
  have hv0 : 0 < v := by
    by_contra h
    have hvZero : v = 0 := by omega
    rw [hvZero] at hv
    simp at hv
    omega
  by_contra hbound
  have hMlt : M < 3 * d := by
    dsimp [d]
    omega
  have huLt : d * u < d * 3 := by
    calc
      d * u = a := hu.symm
      _ ≤ M := haM
      _ < 3 * d := hMlt
      _ = d * 3 := by omega
  have hvLt : d * v < d * 3 := by
    calc
      d * v = b := hv.symm
      _ ≤ M := hbM
      _ < 3 * d := hMlt
      _ = d * 3 := by omega
  have hu2 : u ≤ 2 := by
    have := Nat.lt_of_mul_lt_mul_left huLt
    omega
  have hv2 : v ≤ 2 := by
    have := Nat.lt_of_mul_lt_mul_left hvLt
    omega
  have huNe : u ≠ 1 := by
    intro hu1
    have hvNe : v ≠ 1 := by
      intro hv1
      apply hab
      rw [hu, hv, hu1, hv1]
    have hvLower : 2 ≤ v := by omega
    have hMlower : 2 * d ≤ M := by
      calc
        2 * d = d * 2 := by omega
        _ ≤ d * v := Nat.mul_le_mul_left d hvLower
        _ = b := hv.symm
        _ ≤ M := hbM
    have hMupper : M < 2 * d := by
      calc
        M < 2 * a := haHalf
        _ = 2 * d := by rw [hu, hu1]; simp
    omega
  have hvNe : v ≠ 1 := by
    intro hv1
    have huNe' : u ≠ 1 := by
      intro hu1
      apply hab
      rw [hu, hv, hu1, hv1]
    have huLower : 2 ≤ u := by omega
    have hMlower : 2 * d ≤ M := by
      calc
        2 * d = d * 2 := by omega
        _ ≤ d * u := Nat.mul_le_mul_left d huLower
        _ = a := hu.symm
        _ ≤ M := haM
    have hMupper : M < 2 * d := by
      calc
        M < 2 * b := hbHalf
        _ = 2 * d := by rw [hv, hv1]; simp
    omega
  have huEq : u = 2 := by omega
  have hvEq : v = 2 := by omega
  apply hab
  rw [hu, hv, huEq, hvEq]

/-- Three distinct multiples of one positive integer, each in the upper half
of `[1,M]`, force five copies of that integer into the range. -/
theorem three_distinct_upper_half_multiples {M d a b c : ℕ}
    (hd : 0 < d)
    (hda : d ∣ a) (hdb : d ∣ b) (hdc : d ∣ c)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M)
    (haHalf : M < 2 * a) (hbHalf : M < 2 * b) (hcHalf : M < 2 * c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    5 * d ≤ M := by
  rcases dvd_iff_exists_eq_mul_right.mp hda with ⟨u, rfl⟩
  rcases dvd_iff_exists_eq_mul_right.mp hdb with ⟨v, rfl⟩
  rcases dvd_iff_exists_eq_mul_right.mp hdc with ⟨w, rfl⟩
  have hu0 : 0 < u := by
    by_contra h
    have : u = 0 := by omega
    simp [this] at haHalf
  have hv0 : 0 < v := by
    by_contra h
    have : v = 0 := by omega
    simp [this] at hbHalf
  have hw0 : 0 < w := by
    by_contra h
    have : w = 0 := by omega
    simp [this] at hcHalf
  by_contra hbound
  have hMbound : M < 5 * d := by omega
  have hUeqV : u ≠ v := by
    intro h
    exact hab (by rw [h])
  have hUeqW : u ≠ w := by
    intro h
    exact hac (by rw [h])
  have hVeqW : v ≠ w := by
    intro h
    exact hbc (by rw [h])
  have hlt2 (hM : M < 2 * d) : u < 2 ∧ v < 2 ∧ w < 2 := by
    have hu : d * u < d * 2 := by
      calc
        d * u ≤ M := haM
        _ < 2 * d := hM
        _ = d * 2 := by omega
    have hv : d * v < d * 2 := by
      calc
        d * v ≤ M := hbM
        _ < 2 * d := hM
        _ = d * 2 := by omega
    have hw : d * w < d * 2 := by
      calc
        d * w ≤ M := hcM
        _ < 2 * d := hM
        _ = d * 2 := by omega
    exact ⟨Nat.lt_of_mul_lt_mul_left hu, Nat.lt_of_mul_lt_mul_left hv,
      Nat.lt_of_mul_lt_mul_left hw⟩
  have hge2 (hM : 2 * d ≤ M) : 2 ≤ u ∧ 2 ≤ v ∧ 2 ≤ w := by
    have hu : 2 * (d * u) ≤ 2 * d → False := by
      intro h
      omega
    have hv : 2 * (d * v) ≤ 2 * d → False := by
      intro h
      omega
    have hw : 2 * (d * w) ≤ 2 * d → False := by
      intro h
      omega
    have hu' : ¬ u ≤ 1 := by
      intro h
      have hm : 2 * (d * u) ≤ 2 * d := by
        calc
          2 * (d * u) ≤ 2 * (d * 1) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left d h)
          _ = 2 * d := by simp
      have hhalf : M < 2 * (d * u) := haHalf
      omega
    have hv' : ¬ v ≤ 1 := by
      intro h
      have hm : 2 * (d * v) ≤ 2 * d := by
        calc
          2 * (d * v) ≤ 2 * (d * 1) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left d h)
          _ = 2 * d := by simp
      have hhalf : M < 2 * (d * v) := hbHalf
      omega
    have hw' : ¬ w ≤ 1 := by
      intro h
      have hm : 2 * (d * w) ≤ 2 * d := by
        calc
          2 * (d * w) ≤ 2 * (d * 1) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left d h)
          _ = 2 * d := by simp
      have hhalf : M < 2 * (d * w) := hcHalf
      omega
    omega
  have hge3 (hM : 4 * d ≤ M) : 3 ≤ u ∧ 3 ≤ v ∧ 3 ≤ w := by
    have hu : ¬ u ≤ 2 := by
      intro h
      have hm : 2 * (d * u) ≤ 4 * d := by
        calc
          2 * (d * u) ≤ 2 * (d * 2) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left d h)
          _ = 4 * d := by omega
      omega
    have hv : ¬ v ≤ 2 := by
      intro h
      have hm : 2 * (d * v) ≤ 4 * d := by
        calc
          2 * (d * v) ≤ 2 * (d * 2) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left d h)
          _ = 4 * d := by omega
      omega
    have hw : ¬ w ≤ 2 := by
      intro h
      have hm : 2 * (d * w) ≤ 4 * d := by
        calc
          2 * (d * w) ≤ 2 * (d * 2) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left d h)
          _ = 4 * d := by omega
      omega
    omega
  by_cases hM2 : M < 2 * d
  · have hr := hlt2 hM2
    have hu : u = 1 := by omega
    have hv : v = 1 := by omega
    have hw : w = 1 := by omega
    exact hUeqV (by rw [hu, hv])
  · by_cases hM3 : M < 3 * d
    · have hlow := hge2 (by omega)
      have hu : u ≤ 2 := by
        have hm : d * u < d * 3 := by
          calc d * u ≤ M := haM
            _ < 3 * d := hM3
            _ = d * 3 := by omega
        have := Nat.lt_of_mul_lt_mul_left hm
        omega
      have hv : v ≤ 2 := by
        have hm : d * v < d * 3 := by
          calc d * v ≤ M := hbM
            _ < 3 * d := hM3
            _ = d * 3 := by omega
        have := Nat.lt_of_mul_lt_mul_left hm
        omega
      have hw : w ≤ 2 := by
        have hm : d * w < d * 3 := by
          calc d * w ≤ M := hcM
            _ < 3 * d := hM3
            _ = d * 3 := by omega
        have := Nat.lt_of_mul_lt_mul_left hm
        omega
      omega
    · by_cases hM4 : M < 4 * d
      · have hlow := hge2 (by omega)
        have hu : u ≤ 3 := by
          have hm : d * u < d * 4 := by
            calc d * u ≤ M := haM
              _ < 4 * d := hM4
              _ = d * 4 := by omega
          have := Nat.lt_of_mul_lt_mul_left hm
          omega
        have hv : v ≤ 3 := by
          have hm : d * v < d * 4 := by
            calc d * v ≤ M := hbM
              _ < 4 * d := hM4
              _ = d * 4 := by omega
          have := Nat.lt_of_mul_lt_mul_left hm
          omega
        have hw : w ≤ 3 := by
          have hm : d * w < d * 4 := by
            calc d * w ≤ M := hcM
              _ < 4 * d := hM4
              _ = d * 4 := by omega
          have := Nat.lt_of_mul_lt_mul_left hm
          omega
        omega
      · have hlow := hge3 (by omega)
        have hu : u ≤ 4 := by
          have hm : d * u < d * 5 := by
            calc d * u ≤ M := haM
              _ < 5 * d := hMbound
              _ = d * 5 := by omega
          have := Nat.lt_of_mul_lt_mul_left hm
          omega
        have hv : v ≤ 4 := by
          have hm : d * v < d * 5 := by
            calc d * v ≤ M := hbM
              _ < 5 * d := hMbound
              _ = d * 5 := by omega
          have := Nat.lt_of_mul_lt_mul_left hm
          omega
        have hw : w ≤ 4 := by
          have hm : d * w < d * 5 := by
            calc d * w ≤ M := hcM
              _ < 5 * d := hMbound
              _ = d * 5 := by omega
          have := Nat.lt_of_mul_lt_mul_left hm
          omega
        omega

/-- Three distinct upper-half moduli have common gcd at most `M/5`, in
multiplication form. -/
theorem triple_gcd_le_one_fifth {M a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M)
    (haHalf : M < 2 * a) (hbHalf : M < 2 * b) (hcHalf : M < 2 * c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    5 * tripleGcd a b c ≤ M := by
  apply three_distinct_upper_half_multiples
    (d := tripleGcd a b c) (a := a) (b := b) (c := c) (M := M)
  · dsimp [tripleGcd]
    exact Nat.gcd_pos_of_pos_left c (Nat.gcd_pos_of_pos_left b ha)
  · dsimp [tripleGcd]
    exact dvd_trans (Nat.gcd_dvd_left (Nat.gcd a b) c) (Nat.gcd_dvd_left a b)
  · dsimp [tripleGcd]
    exact dvd_trans (Nat.gcd_dvd_left (Nat.gcd a b) c) (Nat.gcd_dvd_right a b)
  · dsimp [tripleGcd]
    exact Nat.gcd_dvd_right (Nat.gcd a b) c
  · exact haM
  · exact hbM
  · exact hcM
  · exact haHalf
  · exact hbHalf
  · exact hcHalf
  · exact hab
  · exact hac
  · exact hbc

end Erdos708
