import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0167
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothContinuous
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0142
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0154
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0162
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PIntCoordChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSimpleStacked
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcCycle
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcLinPrimeLe
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinPrimeCut
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcGeoFirst
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0116
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometric
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0020
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0053
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0052
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0058
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0119
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0144
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionIndexNorm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointResidue
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PInvertibleIdealIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.POrderIdealIndexExtension
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointSurj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointUnitSection
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointNagata
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartHessCompare
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartCutoffEnergy
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0055
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0141
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0129
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0132
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0134
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0122
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapSquareSystemStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_swap_square_system : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∃ (Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a)) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (e : RW.X → Q.SW.X), HoloMap RW.A Q.SW.A e ∧ IsDegreeOff Q.SW.A RW.A e 1 ∅ ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) fun p => RW.lift x x ⟨some p.1, p.2⟩) ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 1 (e x) → ∃ z₁, SameOrbit (FA.Re.R.lift x₀ x₀) z₁ ∧ (∀ p : (Σ k, ι k), p.1 ≠ k₀ → z₁ p = RW.lift x x ⟨some p.1, p.2⟩) ∧ ∀ m : ι k₀, z₁ ⟨k₀, m⟩ = RW.lift x x ⟨none, m⟩) ∧ (Function.Injective fun w => (Q.q 0 w, Q.q 1 w)) ∧ ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) F (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → (∀ x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₀) → (∀ x₀, FA.Re.π x₀ = Q.q 1 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₁) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → logNormSec Q.L' Q.v (e x) + Q.cst = Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1) else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.ansq_exists | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.ansq_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.ansq_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDataFubiniStudyStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_data_fubini_study : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → bdry BM.s = ∅ → (∀ p, BM.hom p = fsHerm ι (M.dy p)) → ∃ FA : FlagAn BM d, ∀ p t, FA.Re.line (some p) t = fsHerm ι (M.dy p) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_analytic_data_fubini_study | exact GlobalTheory.CompanionTheory.Relay.flag_analytic_data_fubini_study | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_analytic_data_fubini_study <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelArithDimensionBoundaryStatement
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_arith_dimension_boundary : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → (∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) → (x' ∈ bdry BM.s ↔ x ∈ bdry BM.s) ∧ rW BM.L BM.s x' = rW BM.L BM.s x) → (∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry BM.s → SameOrbit (basePart M.blk z) (BM.Rb.lift x x) → (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z) → ∃ FA : FlagAn BM d, ∀ a t, IsConjInvariantH (FA.Re.line a t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.ConjOf.flagAn_exists_conj | exact GlobalTheory.CompanionTheory.Ar.PB.ConjOf.flagAn_exists_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.ConjOf.flagAn_exists_conj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightPolynomialReflectionSum
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tendsto_polar {σ : Type} [Fintype σ] {n : ℕ} {α : Type} {l : Filter α} {f : α → (Fin n → σ) → ℝ}
    {a : (Fin n → σ) → ℝ} (c : Fin n → σ → ℝ) (h : ∀ w, Tendsto (fun t => f t w) l (𝓝 (a w))) :
    Tendsto (fun t => polar n (f t) c) l (𝓝 (polar n a c)) := by
  unfold polar
  exact tendsto_finsetSum _ fun w _ => (h w).const_mul _

theorem Realis.limNum_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type}
    {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) {II : IntersectionSystem}
    (hII : IsFullIntersectionSystem II) (hpos : 0 < S.t₀) (π : Equiv.Perm (Fin (D + 1)))
    (w : Fin (D + 1) → σ) : Re.limNum II (w ∘ π) = Re.limNum II w := by
  have hev : (fun t => Re.num II t (w ∘ π)) =ᶠ[𝓝[>] 0] fun t => Re.num II t w := by
    filter_upwards [Ioc_mem_nhdsGT hpos] with t ht
    have h := (hII.1 K ι).1 P (D + 1) (fun j => Re.line (w j) t) π Re.arith
      fun j => Re.line_smooth _ t ht.1 ht.2
    unfold Realis.num
    exact congrArg (· / (Re.deg : ℝ)) h
  unfold Realis.limNum limUnder
  rw [Filter.map_congr hev]

theorem AnSys.degNum_perm {e : ℕ} {σ : Type} (S : AnSys e σ) (π : Equiv.Perm (Fin e)) (w : Fin e → σ) :
    S.degNum (w ∘ π) = S.degNum w :=
  ReciprocityTheory.AnForm.M.mIntSymm S.A (fun j => S.th (w j)) π fun _ => 1

theorem thmA_limit : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (Re.PB II) + eval (fun x => c x + u / 2 * ε x) (Re.PB II) = (tsgPoly (d + 1) kappa (linePoly c ε SY.degPoly)).eval u := by
  intro hI hF II hII K _ ι _ d σ _ SY P Re a₀ ε Q c hc u
  have hpos : 0 < SY.t₀ := (SY.reg a₀).1
  have hposW : 0 < Q.an.SW.t₀ := (Q.an.SW.reg none).1
  obtain ⟨C₃, s₀, -, hAg⟩ := GlobalTheory.T.agreement_positive hI (d + 1) σ SY 0 hpos
  have hlim := (hAg II hII K ι P Re).1
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ Q.an.SW.t₀ := by
    filter_upwards [Ioc_mem_nhdsGT hposW] with t ht using ⟨ht.1, ht.2⟩
  refine GlobalTheory.T.polar_identity_from_symmetric_forms σ (d + 1) (Re.limNum II) SY.degNum kappa ε a₀ (Re.limNum_perm hII hpos)
    SY.degNum_perm (fun n hn => ?_) c hc u
  have hsq := GlobalTheory.T.square_system_polar_vanishing hI II hII K ι d σ SY P Re a₀ ε Q n hn
  refine ⟨?_, fun k hk hk2 => ?_⟩
  · have h1 := tendsto_polar (fun _ (x : σ) => (n x : ℝ)) hlim
    have h2 : Tendsto (fun t => polar (d + 2) (Re.num II t) fun _ (x : σ) => (n x : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).1.symm)
    exact tendsto_nhds_unique h1 h2
  · have h1 := tendsto_polar (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ)) hlim
    have h2 : Tendsto (fun t => -∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t))
          (Q.an.wcoef (fun a => (n a : ℝ)) k i)) (𝓝[>] 0)
        (𝓝 (-∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potH (w r)) Q.an.gH)
          (Q.an.wcoef (fun a => (n a : ℝ)) k i))) :=
      (tendsto_finsetSum _ fun i _ => tendsto_polar _ fun w =>
        (GlobalTheory.T.analytic_square_regularized_convergence hI d σ SY a₀ ε Q.an w).2).neg
    have h3 := tendsto_nhds_unique (h1.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).2 k hk hk2)) h2
    have h4 := GlobalTheory.T.square_polar_integral_identity hI hF d σ SY a₀ ε Q.an (fun a => (n a : ℝ)) (by simp [hn]) k hk hk2
    rw [h3, h4]
    ring

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeIndexImpliesHeightBoundStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_index_implies_height_bound : MoriwakiHSStatement → ArithmeticHilbertSamuelUpperBound := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.smallCountUpper_of_moriwaki | exact GlobalTheory.CompanionTheory.Ar.Small.smallCountUpper_of_moriwaki | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.smallCountUpper_of_moriwaki <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LineOfLargeDegreeOfMoriwaki
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights in

theorem lineOfLargeDegree_of_moriwaki :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
        GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement := by
  intro hAIS hHS hBig hResK
  have hZ2 : SuccessiveMinimaUpperBound := (hsLinks_of_moriwaki hHS hBig).2.2.1
  have hI : ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := GlobalTheory.T.intersection_exists_of_arith_system hAIS
  have hGr : GraphStatement := GlobalTheory.T.graph_statement_holds
  have hAI3 : Inter.PushforwardArithIntersection.Statement := GlobalTheory.T.generic_degree_of_arith_system hAIS
  have hPts : PtsIntegrableStatement := GlobalTheory.T.points_integrable_of_resolution_statement hResK
  have hInd : PtsIndepStatement :=
    ReciprocityTheory.ChartRestriction.G.Geo.ptsIndep_of (GlobalTheory.T.resolution_exists_of_resolution_statement hResK) HilbertSamuel.Closed.ReciprocityTheory.ChartRestriction.G.Geo.ResBridge
  have hSheet : SheetIndepStatement :=
    ReciprocityTheory.ChartRestriction.G.Geo.sheetIndep_of ReciprocityTheory.ChartRestriction.G.Geo.osgood
      HilbertSamuel.Closed.ReciprocityTheory.ChartRestriction.G.Geo.FibreFinite
  have hChange : IntCoordChange.Statement :=
    IntCoordChange.proof Inter.Closed.ReciprocityTheory.ChartRestriction.G.AI.I2.Unique IntCoordGeoNum.proof
      (IntCoordArInt.proof hInd hSheet)
  have hBasis : DualTopBasisChange.Statement := DualTopBasisChange.proof hChange
  have hSDeg : DualStackedDegree.Statement := DualStackedDegree.proof DualLatticeIndex.proof
  have hCC : CurveCharts.Statement :=
    CurveCharts.proof (ClosedPointChart.proof ClosedPointUnitSection.proof)
  have hVPC : VertPointChart.Statement := VertPointChart.proof hCC
  have hVRI : VertRIndex.Statement :=
    VertRIndex.proof LogCardLength.proof SectionQuotFinite.closed
      (VertPointLength.proof hVPC (VertPointInj.proof hVPC)
        (VertPointSurj.proof hCC SectionQuotLocal.proof)
        (VertPointMultChart.proof hVPC (VertPointNagata.proof hVPC)) SectionQuotLocal.proof)
      (VertPointResidue.proof hCC)
  have hSN : SectionIndexNorm.Statement :=
    SectionIndexNorm.proof hCC
      (InvertibleIdealIndex.proof OrderIdealIndexExtension.proof LocallyPrincipalCoprime.proof)
  have hCELI : ChartEnergyLinearInvariant.Statement :=
    ChartEnergyLinearInvariant.proof ChartEnergySwapInvariant.proof
  have hCE : ChartEnergy.Statement :=
    ChartEnergy.proof hCELI
      (ChartEnergyDiagonal.proof hCELI
        (ChartEnergyCocycle.proof
          (ChartEnergySymm.proof
            (ChartIbpSymm.proof
              (ChartIbpCutoff.proof ChartCutoffEnergy.proof
                (ChartDiffEnergy.proof ChartCutoffEnergy.proof))))))
  have hEnergy : DualMetricEnergy.Statement :=
    DualMetricEnergy.proof
      (DualEnergyCharts.proof
        (ChartEnergyIntegrable.proof HermFormCompare.proof
          (ChartHessCompare.proof HermFormCompare.proof)))
      hCE GrassGeomDegChart.proof ChartMassInvariant.proof
  have hStdGenDeg : DualStdGenDeg.Statement :=
    DualStdGenDeg.proof OneBlockPointDeg.proof
      (DualStdFibreRatios.proof GenFibreModelTransport.proof DualStdGraphModel.proof
        DualStdModelRank.proof DualStdModelTransc.proof)
  have hLinear : DualStackedExcLinear.Statement :=
    DualStackedExcLinear.proof (DualStackedExcResidueExists.proof DualLatticeModPrime.proof)
      (DualStackedExcBaseLe.proof GlobalTheory.T.dual_stacked_graph_bihomogeneous GlobalTheory.T.dual_stacked_exceptional_leading_form)
      (DualStackedExcLinPrimeLe.proof DualCotangentKer.proof)
  have hFib : DualStackedGraphFibre.Statement :=
    DualStackedGraphFibre.proof
      (DualStackedExcCycle.proof
        (DualStackedExcReduced.proof GlobalTheory.T.dual_stacked_exceptional_coords GlobalTheory.T.dual_stacked_exceptional_base GlobalTheory.T.dual_stacked_exceptional_chart))
      (DualStackedExcGeoSecond.proof hLinear LinPrimeCut.proof LinPrimeBase.proof)
      DualStackedExcGeoFirst.proof
  have hStep : DualTopSimpleStacked.Statement :=
    DualTopSimpleStacked.proof hAI3 hGr (DualStackedGraphImage.proof hGr GlobalTheory.CompanionTheory.Ar.Giv.fibreDim)
      DualStackedGraphHorizontal.proof hFib GrassFibreDegree.proof
  have hStacked : DualTopStacked.Statement :=
    DualTopStacked.proof (DualTopSimpleSub.proof hBasis hStep hSDeg) hBasis hSDeg
  have hCM : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement :=
    Targets.ChangeOfModel.of_found hAI3 hGr
      (HilbertSamuel.IsomInvariance.proof (Inter.RatR.proof hPts))
      HilbertSamuel.GraphIsometric.proof
  have hBC : DualStdBaseChange.Statement :=
    DualStdBaseChange.proof hCM hGr Targets.genFibreExists
      (fun F _ K _ ι _ => Targets.ExistsUnique.full F ι)
      DualStdBasePtFree.proof DualStdImageBot.proof hStdGenDeg DualStdMetricPull.proof
  exact LineOfLargeDegree.proof hHS hZ2 hI hVRI hSN
    hEnergy hBasis hStacked hSDeg hBC (GrassLinesProj.proof (GlobalTheory.T.coordinate_projection_of_arith_system hAIS))
    (DualGeomDegCharts.proof ChartDensityIntegrable.proof) GrassGeomDegChart.proof ChartMassInvariant.proof
    (degree_of_system hAIS) hInd

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LintegralFibreLogNormFinite
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

section Assembly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem setSheetDensity_eq_zero {e : ℕ} {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ S, g z = 0) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : setSheetDensity S Ψ φ g y w = 0 := by
  unfold setSheetDensity
  split_ifs with hγ
  · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
  · rfl

theorem setSheetDensity_sum {e : ℕ} {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {τ : Type*} (t : Finset τ) (G : τ → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    setSheetDensity S Ψ φ (fun z => ∑ i ∈ t, G i z) y w = ∑ i ∈ t, setSheetDensity S Ψ φ (G i) y w := by
  unfold setSheetDensity
  split_ifs with hγ
  · rw [Finset.sum_mul]
  · simp

theorem exists_mem_domCell [DecidableEq K] {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) :
    ∃ i, z ∈ domCell i := by
  choose i1 _ using hz
  have : Nonempty ((k : K) → ι k) := ⟨i1⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun i' : (k : K) → ι k => ‖segre z i'‖
  exact ⟨i, hi⟩

theorem segre_ne_zero_of_mem_domCell {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0)
    {i : (k : K) → ι k} (hi : z ∈ domCell i) : segre z i ≠ 0 := by
  choose i1 hi1 using hz
  have h1 : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hi1 k
  intro h0
  have := hi i1
  rw [h0, norm_zero] at this
  exact h1 (norm_le_zero_iff.1 this)

end Assembly

theorem cell_mass_lt_top {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {N : Fin e → HermLine ι}
    {A : HermLine ι} {s : MRingOver ℂ ι} {a : K → ℕ}
    (hQ : IsCxVar Q e) (hΨ : IsSetGoodProj (conePts Q) Ψ) (hΨ0 : ∀ w, Ψ w 0 = w i)
    (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hAa : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) (hsQ : s ∉ Q)
    (hnn : ∀ y w, 0 ≤ setSheetDensity (conePts Q) Ψ (pot N) ((domCell i).indicator (absLogNorm A s)) y w) :
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) ((domCell i).indicator (absLogNorm A s)) y) < ⊤ := by
  classical
  set σ : Fin (Fintype.card ((k : K) → ι k)) ≃ ((k : K) → ι k) := (Fintype.equivFin _).symm with hσ
  set G := (domCell i).indicator (absLogNorm A s) with hG
  obtain ⟨hGm, hGi⟩ := GlobalTheory.T.domCell_logNorm_measurable_invariant K ι A s a i hA hAa hs
  have hzero := GlobalTheory.T.zeroSet_chartIdeal_eq_chartSet K ι Q _ σ i hQ.2.1.2.1
  have hdim := GlobalTheory.T.ringKrullDim_chartComponents K ι Q e _ σ i hQ
  have hfin := GlobalTheory.T.chartComponents_finite_projection K ι Q e _ σ i Ψ hQ hΨ hΨ0 hdim
  have hfs := GlobalTheory.T.chart_density_integrable K ι Q e _ σ i N G Ψ hQ hN hGi hΨ0 (GlobalTheory.T.setFibre_finite_of_goodProj K ι Q e Ψ hQ hΨ) hzero hdim hfin
  have hsm : ∀ j, ∀ J ∈ chartComponents (conePts Q) σ i, GroundTheory.Heights₂.Heights.SmoothNear
      (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (chartPot σ i N j) := fun j J hJ =>
    GroundTheory.Heights₂.Heights.smoothNear_chartPot σ i hN (fun x hx => by
      have hx' : x ∈ chartSet (conePts Q) σ i := by
        rw [← hzero]
        exact fun q hq => hx q ((mem_chartComponents.1 hJ).1.2 hq)
      obtain ⟨z, -, hzi, rfl⟩ := hx'
      simpa using hzi) j
  have hint : Integrable (fun y => ∑ J ∈ chartComponents (conePts Q) σ i,
      chartAbsDens J (chartProjMatrix σ Ψ) (chartWeight σ i G) (chartPot σ i N) y) :=
    integrable_finset_sum _ fun J hJ =>
      GlobalTheory.T.integrable_domCell_logNorm_chart K ι Q e _ σ i Ψ N A s a J hA hAa hs hGm hzero hJ (hfin J hJ) fun R C =>
        GlobalTheory.T.integrable_chartAbsDensity _ e J _ _ _ R C (mem_chartComponents.1 hJ).1.1 (hdim J hJ) (hfin J hJ)
          (GlobalTheory.T.chartSection_not_mem_components K ι Q e _ σ i s a hQ hs hsQ J hJ) fun j => hsm j J hJ
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
  filter_upwards [hfs] with y hy
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : cxPosDens (conePts Q) Ψ (pot N) G y =
      ∑ᶠ w ∈ setFibre (conePts Q) Ψ y, setSheetDensity (conePts Q) Ψ (pot N) G y w := by
    unfold cxPosDens
    exact finsum_congr fun w => finsum_congr fun _ => max_eq_left (hnn y w)
  rw [hpos, hy]
  exact Finset.sum_le_sum fun J _ =>
    GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.chartDens_le_chartAbsDens _ _ _ _ _

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open GlobalTheory.CompanionTheory.Ar.Pub.CxChart in

theorem GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) < ⊤ := by
  intro K _ ι _ Q e Ψ L A s a hQ hΨ hL hA hAa hs hsQ
  classical
  obtain ⟨N, hN, hTw⟩ := GlobalTheory.T.exists_smooth_metrics_nonneg_density K ι e L hL
  obtain ⟨hnn, hbd⟩ := hTw (conePts Q) Ψ fun z hz => hz.1
  set G : ((k : K) → ι k) → ((Σ k, ι k) → ℂ) → ℝ := fun i => (domCell i).indicator (absLogNorm A s) with hG
  have hG0 : ∀ i z, 0 ≤ G i z := fun i z => Set.indicator_nonneg (fun z _ => by
    unfold absLogNorm
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl) z
  have hWm := fun i => GlobalTheory.T.domCell_logNorm_measurable_invariant K ι A s a i hA hAa hs
  have hcell : ∀ i, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) < ⊤ := by
    intro i
    by_cases hi : ∃ z ∈ conePts Q, segre z i ≠ 0
    · obtain ⟨Ψ', hΨ', hΨ0⟩ := GlobalTheory.T.exists_goodProj_first_coordinate K ι Q e i hQ hi
      rw [GlobalTheory.T.integral_density_independent_projection K ι Q e Ψ Ψ' N (G i) hQ hΨ hΨ' hN (hWm i).1 (hWm i).2]
      exact cell_mass_lt_top hQ hΨ' hΨ0 hN hA hAa hs hsQ fun y w => (hTw (conePts Q) Ψ' fun z hz => hz.1).1 _ y w (hG0 i)
    · have h0 : ∀ z ∈ conePts Q, G i z = 0 := fun z hz => Set.indicator_of_notMem (fun hzi =>
        hi ⟨z, hz, segre_ne_zero_of_mem_domCell hz.1 hzi⟩) _
      have : ∀ y, cxPosDens (conePts Q) Ψ (pot N) (G i) y = 0 := fun y => by
        unfold cxPosDens
        simp [setSheetDensity_eq_zero (pot N) h0]
      simp [this]
  have hfib := GlobalTheory.T.setFibre_finite_of_goodProj K ι Q e Ψ hQ hΨ
  have hcov : ∀ z ∈ conePts Q, |logNormC A s z| ≤ ∑ i, G i z := by
    intro z hz
    obtain ⟨i, hi⟩ := exists_mem_domCell hz.1
    have : |logNormC A s z| = G i z := by
      simp only [hG, Set.indicator_of_mem hi, absLogNorm, if_pos hz.1]
    rw [this]
    exact Finset.single_le_sum (f := fun i => G i z) (fun i _ => hG0 i z) (Finset.mem_univ i)
  have hpt : ∀ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) ≤
      ENNReal.ofReal (3 ^ e) * ∑ i, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) := by
    intro y
    have hnnd : ∀ i, 0 ≤ cxPosDens (conePts Q) Ψ (pot N) (G i) y := fun i =>
      finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hnnd i, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold cxPosDens
    simp only [finsum_mem_eq_finite_toFinset_sum _ (hfib y)]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    refine (hbd _ (fun z => ∑ i, G i z) y w hcov).trans ?_
    rw [setSheetDensity_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => le_max_left _ _) (by positivity)
  calc ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
        |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|)
      ≤ ∫⁻ y, ENNReal.ofReal (3 ^ e) * ∑ i, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (3 ^ e) * ∑ i, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finset_sum' _ fun i _ =>
          (GlobalTheory.T.aemeasurable_cxPosDensity K ι Q e Ψ N (G i) hQ hΨ hN (hWm i).1 (hWm i).2).ennreal_ofReal]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.sum_lt_top.2 fun i _ => hcell i)
end
end

