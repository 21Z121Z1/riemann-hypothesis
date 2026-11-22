import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGroupDictionary
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0168
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0071
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0162
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0115
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0103
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0136
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0064
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0127
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0160
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0144
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SiuInequalityIntegralHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0128

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGroupDictionaryStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_group_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ), Nonempty (GroupDict F) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.groupDict_nonempty | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.groupDict_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.groupDict_nonempty <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightPolynomialReflectionSumStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_polynomial_reflection_sum : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (Re.PB II) + eval (fun x => c x + u / 2 * ε x) (Re.PB II) = (tsgPoly (d + 1) kappa (linePoly c ε SY.degPoly)).eval u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.thmA_limit | exact GlobalTheory.CompanionTheory.Ar.PB.thmA_limit | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.thmA_limit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG7sOfStatements
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem smallSections_upper_of_moriwaki :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement →
      ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ArithmeticHilbertSamuelUpperBoundNumberField := by
  intro hAIS hHS hRes
  have hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement :=
    degreeGeneric_of_degree (degree_of_system hAIS)
  have a0 := GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersectionAnyDegree.proof (GlobalTheory.T.embedding_pieces_of_intersection_and_resolution hAIS hRes) hDG
  have a1 := GroundTheory.Heights₂.Heights.HilbertSamuel.TwistMetric.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.proof a0
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeNefDual.proof (GlobalTheory.T.hodge_index_implies_height_bound hHS) GlobalTheory.T.packing'
    GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.full a1

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LintegralFibreLogNormFiniteStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fibre_logNorm_finite : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackInputsOfStatements
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem pullbackInputs_of_hypotheses :
    ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.PB.Inputs := by
  intro hII hHS hBig hRes
  exact ⟨⟨GlobalTheory.T.convergence_statement_holds, GlobalTheory.T.signed_convergence_statement_holds, GlobalTheory.T.convergence_rate_statement_holds, GlobalTheory.T.uniform_integrability_statement_holds, GlobalTheory.T.pullback_statement_holds, GlobalTheory.T.global_regularization_statement_holds⟩,
    ⟨GlobalTheory.T.resolution_exists_of_resolution_statement hRes, degree_of_system hII, (hsLinks_of_moriwaki hHS hBig).1⟩,
    ⟨GlobalTheory.T.rationality_of_resolution_statement hRes, metricLocal⟩,
    ⟨GlobalTheory.T.projection_formula_of_arith_system hII, lineFibre_holds, fibreDim⟩,
    ⟨GlobalTheory.T.kleiman_nef_criteria_hold.1, GlobalTheory.T.kleiman_nef_criteria_hold.2, GlobalTheory.T.siu_inequality_integral_holds⟩⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

