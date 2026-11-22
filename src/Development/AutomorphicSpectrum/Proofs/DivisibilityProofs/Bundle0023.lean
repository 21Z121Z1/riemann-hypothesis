import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0019

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightGapDeltaEqAntisymmetricStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_gap_delta_eq_antisymmetric : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), PB.toWt (gapDelta Ψ N) = GroundTheory.Heights₂.Heights.antisymDelta Ψ N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_gapDelta_eq_antisymDelta | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_gapDelta_eq_antisymDelta | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_gapDelta_eq_antisymDelta <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightMapInjectiveStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_map_injective : ∀ (Ψ : Type) (N : ℕ), Function.Injective (PB.toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_leftInverse_injective | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_leftInverse_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_leftInverse_injective <;> assumption)
end

