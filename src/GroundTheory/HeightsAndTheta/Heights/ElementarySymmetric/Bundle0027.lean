import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHcEqCoh
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CohMkEqZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDSq
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CuspFamily
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0030
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PEulerVarX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem EulerVar.proof : GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerVar.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerVar.proof
    GroundTheory.Heights₂.Heights.Kleiman.KHCechDSq.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES.full

end GroundTheory.Heights₂.Heights.Swarm
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StMuSheetLeviNonnegFam
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology

def MuSheetLeviNonnegFam.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (X : ComponentFamilySetting D)
    (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D.n + 1) → ℂ)),
    IsGoodProj (mCoordIdeal D.y) Q →
      ∀ᵐ y : Fin D.n → ℂ, ∀ (w : ((k : K) → ι k) → ℂ) (γ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ),
        IsSheet (mCoordIdeal D.y) Q y w γ →
          ContDiffAt ℝ 2 (fun y' => phMu X.H (γ y')) y ∧
            ∀ v : Fin D.n → ℂ, 0 ≤ leviForm (fun y' => phMu X.H (γ y')) y v

section Bridge

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type}
  [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E}
  {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

end Bridge

namespace Line

open GroundTheory.Heights₂.Heights.LowerBoundFree.Line

end Line

end GroundTheory.Heights₂.Heights.NineStatements
end
end

