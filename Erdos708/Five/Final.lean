module

public import Erdos708.Five.Upper
public import Erdos708.Five.Case5
public import Erdos708.Five.Case41
public import Erdos708.Five.Sharpness

@[expose] public section

/-!
# `g(5) = 6` for Erdős #708

Five distinct positive moduli at most `M` have, in every interval of `M` consecutive integers,
at most six distinct entries whose product is divisible by the product of the moduli
(`five_moduli_six_cover`). Five entries do not always suffice (`sharp5_no_five_cover`).
-/

namespace Erdos708.Five

open scoped BigOperators
open Erdos708

/-- `g(5) ≤ 6`, conditional only on the (4,1) case statement. -/
theorem upper_of_case41 (h41 : Case41Statement) {L : ℤ} {M : ℕ} (m : Fin 5 → ℕ)
    (hinj : Function.Injective m) (hpos : ∀ i, 0 < m i) (hle : ∀ i, m i ≤ M) :
    ProdCover L M (∏ i, m i) 6 :=
  upper_of_cases h41 case5_holds m hinj hpos hle

/-- **`g(5) ≤ 6`.** -/
theorem five_moduli_six_cover {L : ℤ} {M a b c d e : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) (hdM : d ≤ M) (heM : e ≤ M)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    FiveModuliCover L M a b c d e 6 := by
  classical
  let m : Fin 5 → ℕ := ![a, b, c, d, e]
  have hinj : Function.Injective m := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [m] at h ⊢ <;> omega
  have hpos : ∀ i, 0 < m i := by intro i; fin_cases i <;> simpa [m]
  have hle : ∀ i, m i ≤ M := by intro i; fin_cases i <;> simpa [m]
  exact fiveCover_of_prodCover (upper_of_cases case41_holds case5_holds m hinj hpos hle)
    (by simp [m, Fin.prod_univ_five])

/-- **`g(5) = 6`.** Six entries always suffice, and five do not. -/
theorem g5_eq_six :
    (∀ {L : ℤ} {M a b c d e : ℕ}, 0 < a → 0 < b → 0 < c → 0 < d → 0 < e →
      a ≤ M → b ≤ M → c ≤ M → d ≤ M → e ≤ M →
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
      FiveModuliCover L M a b c d e 6) ∧
    ∃ (L : ℤ) (M a b c d e : ℕ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧
      a ≤ M ∧ b ≤ M ∧ c ≤ M ∧ d ≤ M ∧ e ≤ M ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
      ¬ FiveModuliCover L M a b c d e 5 :=
  ⟨fun ha hb hc hd he haM hbM hcM hdM heM hab hac had hae hbc hbd hbe hcd hce hde =>
      five_moduli_six_cover ha hb hc hd he haM hbM hcM hdM heM hab hac had hae hbc hbd hbe
        hcd hce hde,
    ⟨51, 20, 5, 10, 12, 15, 20, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      sharp5_no_five_cover⟩⟩

end Erdos708.Five
