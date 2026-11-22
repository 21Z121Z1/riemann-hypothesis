import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsOrthogonalLocalBasisExtension
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0069
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0087
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0074
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0086
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0076
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0077

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsOrthogonalLocalBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La), p + q = D.p + D.q → (gramE D x').det ≠ 0 → (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧ ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 := by
  exact @PositivityTheory.Xgf.exists_orthogonal_local_basis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelRootIndependentStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_root_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootIndep.main | exact GlobalTheory.CompanionTheory.Ar.RootIndep.main | (intros; apply GlobalTheory.CompanionTheory.Ar.RootIndep.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralFubiniStudySumConeStatement
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fubini_study_sum_cone : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f → linForm u ∉ W →
    Integrable (fsSum h u (coneSet h W)) (gaussM (e + 1) n) ∧
      ∫ π, fsSum h u (coneSet h W) π ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * coneIntegral h W e (fsLog h u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton <;> assumption)
end

