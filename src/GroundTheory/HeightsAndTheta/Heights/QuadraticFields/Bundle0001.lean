import Mathlib
import GroundTheory.HeightsAndTheta.Heights.QuadraticFields.SqfField

-- bundled from GroundTheory.HeightsAndTheta.Heights.QuadraticFields.SqfDiscr
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Rows

def SqfDiscr.Statement : Prop :=
  ∀ d : ℕ, Squarefree d → d % 4 = 3 →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      ∀ x : K, x ^ 2 = -(d : K) → NumberField.discr K = -(d : ℤ)

end GroundTheory.Heights₂.Heights.Rows
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.QuadraticFields.SqfZetaFactor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Rows

def SqfZetaFactor.Statement : Prop :=
  ∀ (d : ℕ) [NeZero d], Squarefree d → d % 4 = 3 →
    ∀ χ : DirichletCharacter ℂ d, (∀ k : ℕ, χ k = ((jacobiSym k d : ℤ) : ℂ)) →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → (∃ x : K, x ^ 2 = -(d : K)) →
      ∀ s : ℂ, 1 < s.re →
        NumberField.dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s

end GroundTheory.Heights₂.Heights.Rows
end

