module

public import Erdos708Statement
public import Adapter
public import FC4388.Bridge

/-!
# Erdős Problem 708: proof of $g(4)=5$ and $g(5)=6$

`Adapter` proves the at-most least values and the padded exact covers from the
four- and five-modulus theorems. The bridge below turns them into the exact-cardinality
least values of `Challenge`.
-/

@[expose] public section

namespace Erdos708

/-- An exact-cardinality cover is an at-most cover. -/
theorem cover_of_exact {n k : ℕ} (h : ExactCover n k) : Erdos708Finite.CoverBound n k := by
  intro m hm h2 L
  obtain ⟨B, hB, hc, hd⟩ := h m hm h2 L
  exact ⟨B, hB, hc.le, hd⟩

/-- The exact least value follows from the at-most least value and an exact cover. -/
theorem least_exact {n g : ℕ} (hl : IsLeast {k | Erdos708Finite.CoverBound n k} g)
    (he : Erdos708Finite.ExactCoverBound n g) : IsLeast {k | ExactCover n k} g :=
  ⟨he, fun _ hk ↦ hl.2 (cover_of_exact hk)⟩

theorem erdos_708.variants.four : IsLeast {k | ExactCover 4 k} 5 :=
  least_exact Erdos708Finite.four_least Erdos708Finite.four_exact

theorem erdos_708.variants.five : IsLeast {k | ExactCover 5 k} 6 :=
  least_exact Erdos708Finite.five_least Erdos708Finite.five_exact

end Erdos708

#print axioms Erdos708.erdos_708.variants.four
#print axioms Erdos708.erdos_708.variants.five
#print axioms Erdos708.erdos_708.variants.g_four
#print axioms Erdos708.erdos_708.variants.g_five
