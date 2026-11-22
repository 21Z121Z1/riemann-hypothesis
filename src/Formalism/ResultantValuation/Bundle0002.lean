import Mathlib
import Formalism.CyclotomicNorms.Bundle0001
import Formalism.ResultantValuation.Bundle0001

-- bundled from Formalism.ResultantValuation.PrimePairDisjointBB
section
noncomputable section

namespace Formalism.ResultantValuation

def PrimePairDisjointBB : Prop :=
  ∀ (adm : ℕ → Prop) (N : ℕ) (Y cond C : ℝ), 8 ≤ N → 0 < Y → 0 < cond →
    Y * cond ^ (-C) ≤ (Nat.card {p : ℕ // p.Prime ∧ adm p ∧ Y ≤ p ∧ (p : ℝ) ≤ 2 * Y} : ℝ) →
    (N : ℝ) ^ 4 * cond ^ C ≤ Y ^ (1 / 4 : ℝ) →
    ∃ g₁ g₂ : ℕ, g₁.Prime ∧ g₂.Prime ∧ adm g₁ ∧ adm g₂ ∧
      Y ≤ g₁ ∧ (g₁ : ℝ) ≤ 2 * Y ∧ Y ≤ g₂ ∧ (g₂ : ℝ) ≤ 2 * Y ∧
      g₁ ≠ g₂ ∧ Disjoint (Formalism.CyclotomicNorms.BB N g₁) (Formalism.CyclotomicNorms.BB N g₂)

end Formalism.ResultantValuation
end
end

-- bundled from Formalism.ResultantValuation.SubspaceCount
section
noncomputable section

namespace Formalism.ResultantValuation

def SubspaceCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (j : ℕ),
    (Nat.card {W : Submodule F V // Module.finrank F W = j} : ℤ) *
        ∏ i ∈ Finset.range j, ((Fintype.card F : ℤ) ^ j - (Fintype.card F : ℤ) ^ i) =
      ∏ i ∈ Finset.range j,
        ((Fintype.card F : ℤ) ^ Module.finrank F V - (Fintype.card F : ℤ) ^ i)

end Formalism.ResultantValuation
end
end

