import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesTelescope
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0061
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0028
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0130
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0065
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0062
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0143
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0155
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0144
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

noncomputable section

namespace ModelDimension.OrbitMargin

theorem margin_of_orbit (hOrb : LocalOrbitChart.Statement) : APrimeChartMargin.Statement :=
  have hP : ProjHoloLocal.Statement :=
    ProjHoloLocal.proof hOrb (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof))
  APrimeChartMargin.proof
    (APrimeChartLevi.proof (APrimeChartLeviLocal.proof hP) (ChartVelLift.proof hP))
    (ChartVelLift.proof hP)

theorem stokes_of_statements (hOrb : LocalOrbitChart.Statement)
    (hLevi : GroundTheory.Heights₂.Heights.NineStatements.NbarLeviChartReg.Statement) (hMar : APrimeChartMargin.Statement)
    (hMPI : ModelPtsIntegrable.Statement) (hMix : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → TopNMixedLimit.Statement)
    (hVb : StokesLimitTVb.Statement) (hMuL : MuMeasureLimit.Statement) : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B := by
  intro h1 h2 h3 h4 h5 E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U hFull hAdm hCw _ O Lt _ _ _ X hH hU hPos B hB hAr a hyp
  have hRes : ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement := h1.resExists
  have hInt : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement :=
    GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists hRes
  have hG := GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.proof (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree h1.degree)
  have hTel := StokesTelescope.proof (StokesStep.proof hRes)
  have hVP := VertFactorPos.proof
  have hVS := VertFactorSmooth.proof hVP
  have hHE := HermExtend.proof
  have hPsa := ProjSmoothAlong.proof HoloInjDerivInj.proof hOrb
  have hS := NbarSmooth.proof hHE hPsa hVS
  have hMu := MuRegSmooth.proof hHE hPsa hVS hVP
  have hIso := GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance.proof (GroundTheory.Heights₂.Heights.Inter.RatR.proof hInt)
  have hE := TopNMixedExpand.proof hIso hMu
  have hTP := TopNPoly.proof hIso hVP hMu
  have hLim := TpIntegrandLimit.proof BoundaryPtsNull.proof
  have hAbove := RegAboveWeight.proof (BdPtsNull.proof ParamImageNull.proof) (DivisorPreimageNull.proof ParamImageNull.proof)
  have hConv := PtsBddConv.proof (GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.proof hInt
    (GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.proof hRes))
  have hMono := PtsMonoSemipos.proof
  have hNs := NbarSemipos.proof (NbarChartSemipos.proof hS (GroundTheory.Heights₂.Heights.NineStatements.NbarLeviChart.of_reg hLevi) hMar)
  have hCU := TpCuspIntegrable.proof (ModelLogIntegrable.proof hMPI) BoundaryNull.proof
  have hTp := StokesLimitTp.proof hLim hAbove hCU hConv hMono
  have hT := StokesLimitT.proof hG hNs (StokesLimitTTop.proof hE (hMix h3)) hVb
  have hEps := StokesLimitEps.proof hT hTP (OmNPoly.proof hNs (OmNVbInt.proof hCU hS) hInt) hMuL
  exact StokesLimitPos.proof hG hTel hNs hTp hT hEps II (CMType H) K J Ω W Dc O Lt X B a hFull.1 hPos hB hAr hyp

theorem stokes_of_model : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B :=
  stokes_of_statements GlobalTheory.T.local_orbit_chart_statement_holds GlobalTheory.T.levi_chart_regularity_statement_holds (margin_of_orbit GlobalTheory.T.local_orbit_chart_statement_holds) GlobalTheory.T.model_points_integrable_statement_holds GlobalTheory.T.top_mixed_limit_of_resolution GlobalTheory.T.stokes_limit_statement_holds GlobalTheory.T.measure_limit_statement_holds

end ModelDimension.OrbitMargin

theorem ModelDimension.abelian_cm_stokes_identity : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B :=
  ModelDimension.OrbitMargin.stokes_of_model
