import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0074
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0076
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.CroftonFormulaFibreSum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0061
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0060
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0084
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0055
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaFibreSum
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ φ : EuclideanSpace ℂ (Fin n) → ℝ≥0∞, Measurable φ →
    (∀ s : ℝ≥0∞, IsOpen {y | s < φ y} ∧ IsScaleStable {y | s < φ y}) →
    Measurable (fun π : Fin (e + 1) → Fin n → ℂ => ∑' y : fibrePts (coneSet h W) π, φ y) ∧
      planeMass n e * ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, φ y ∂(gaussM (e + 1) n) =
        gaussM (e + 1) n Set.univ * ∫⁻ y in coneBall h W, φ y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  intro n e δ h W f hW hf hδ φ hφ hlev
  have hcnt : ∀ s : ℝ≥0∞, Measurable fun π : Fin (e + 1) → Fin n → ℂ =>
      cntOver (coneSet h W ∩ {y | s < φ y}) π (firstCoordVec (e + 1)) := fun s =>
    ModelDimension.FnCrofton.measurable_cntOver_first (isSigmaCompact_cone_inter h W (hlev s).1)
  obtain ⟨hm, hi⟩ := GlobalTheory.T.random_set_sum_expectation (planeMass n e • gaussM (e + 1) n)
    ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict (coneBall h W))
    (fun π => fibrePts (coneSet h W) π) φ (gaussM (e + 1) n Set.univ) hφ
    (fun s => by
      simp only [ModelDimension.FnCrofton.encard_fibrePts_inter]
      exact hcnt s)
    (fun s => by
      have hA := (hlev s).1
      have T := GlobalTheory.T.crofton_formula_open_cone n e δ h W f hW hf hδ {y | s < φ y} hA (hlev s).2
      simp only [ModelDimension.FnCrofton.encard_fibrePts_inter]
      rw [lintegral_smul_measure, smul_eq_mul, Measure.restrict_apply hA.measurableSet, gaussM,
        lintegral_withDensity_eq_lintegral_mul _ (ModelDimension.FnCrofton.measurable_matrix_gaussian _ _) (hcnt s)]
      have hset : {y | s < φ y} ∩ coneBall h W =
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ {y | s < φ y}} := by
        ext y
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h2, h3, h1⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h3, h1, h2⟩
      rw [hset]
      simpa only [Pi.mul_apply, gaussM] using T)
  refine ⟨hm, ?_⟩
  rw [lintegral_smul_measure, smul_eq_mul] at hi
  exact hi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependent
section
namespace GlobalTheory.CompanionTheory.CommAlg.FlagModelValue

open GroundTheory.Heights₂.Heights.NumbersDVR in

theorem main : FlagModelValueIndependence.Statement :=
  FlagModelValueIndependence.proof
    (FlagPairValueIndependence.proof GlobalTheory.T.flag_plain_value_independent GlobalTheory.T.flag_further_term_independent_statement)
    (FlagModelCommonModel.proof GlobalTheory.CompanionTheory.CommAlg.joinTwoModels GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt.main
      GlobalTheory.CompanionTheory.Heights.join_vertical_divisor_statement GlobalTheory.T.flag_model_join_left GlobalTheory.T.flag_model_join_right)

end GlobalTheory.CompanionTheory.CommAlg.FlagModelValue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDetLogNormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_basis_gram_det_log_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → (∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) → (gramE D (x ∘ Sum.inr)).det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D (x ∘ Sum.inr)).det‖ = -(q : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.orthogonalBlock_gram_det_log_norm | exact GlobalTheory.CompanionTheory.Ar.Fl.orthogonalBlock_gram_det_log_norm | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.orthogonalBlock_gram_det_log_norm <;> assumption)
end

