import Formalism.HermitianLattices.Bundle0003
import Formalism.HermitianLattices.StatementLat
import Mathlib

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InertPrimesSquareNorm
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField IsDedekindDomain

def InertPrimesSquareNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ P : HeightOneSpectrum (𝓞 E), Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal → IsSquare (Ideal.absNorm P.asIdeal)

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ShortVectorEveryPlace
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Formalism.HermitianLatticesTheory

def rootDiscriminant (K : Type) [Field K] [NumberField K] : ℝ :=
  |(discr K : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ K : ℝ))

def ShortVectorEveryPlace (K : Type) [Field K] [NumberField K] [StarRing K] (B : ℝ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ M ∈ genus h L, ∃ x ∈ M, x ≠ 0 ∧ ∀ φ : K →+* ℂ, ‖φ (h x x)‖ ≤ B

end Formalism.MainNotions.BridgeLemma₂

end
end

