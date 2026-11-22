import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0108
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartDensityIntegrable
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentOrbitComparison
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0089
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0119
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareBaseIntersectionStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_square_base_intersection : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (Xi : HermLine ι) (X₀ X₁ : HermLine Q.ιW), Xi.a = xi2 → IsSmoothHerm Xi → IsPullHerm (Q.κ 0) (Q.v 0) Xi X₀ → IsPullHerm (Q.κ 1) (Q.v 1) Xi X₁ → ∀ (A : HermLine ι) (A₀ : HermLine Q.ιW), IsSmoothHerm A → FromBase k₀ A → IsPullHerm (Q.κ 0) (Q.v 0) A A₀ → II K ι P (d + 2) (fun _ => A) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → II K ι P (d + 2) (mix (2 * k) Xi A) = -∑ i ∈ Finset.range k, (ptsIntegral Q.PW (pot (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.SqFirst.firstHalf | exact GlobalTheory.CompanionTheory.Ar.PB.SqFirst.firstHalf | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.SqFirst.firstHalf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BigLineImpliesHeightPositivityStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.big_line_implies_height_positivity : MoriwakiBigStatement → BirationalPullbackPushforwardFormula := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig | exact GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockGBlockDiagPosDefStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockG_blockDiag_posDef : ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef → IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartDensityIntegrableStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_density_integrable : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → (∀ j, IsSmoothHerm (L j)) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    (∀ w, Ψ w 0 = w i) → (∀ y, (setFibre (conePts Q) Ψ y).Finite) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    (∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ)) →
    ∀ᵐ y, ∑ᶠ w ∈ setFibre (conePts Q) Ψ y, setSheetDensity (conePts Q) Ψ (pot L) g y w =
      ∑ J ∈ chartComponents (conePts Q) σ i,
        chartDens J (chartProjMatrix σ Ψ) (chartWeight σ i g) (chartPot σ i L) y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum.fibreSum | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum.fibreSum | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum.fibreSum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_tangent_lift_in_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts), ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∀ v, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) ((D.chart a).γ t) v → ∃ (u : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) (c : K → ℂ), v = fderiv ℂ (D.chart a).γ t u + torusSmul c ((D.chart a).γ t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.coneTangent_eq_fderiv_add_torusSmul | exact GlobalTheory.CompanionTheory.Ar.Cusp.coneTangent_eq_fderiv_add_torusSmul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.coneTangent_eq_fderiv_add_torusSmul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CutoffFunctionOnCompatibleAtlasStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_function_on_compatible_atlas : ∀ (n p q : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas n X) (Z Cl U : Set X) (r : X → ℝ) (Γ : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), A.Compatible B → (∀ k, Metric.closedBall (0 : Fin n → ℂ) 2 ⊆ (B.chart k).target) → (∀ x, ∃ k, x ∈ (B.chart k).source ∧ B.chart k x ∈ Metric.ball (0 : Fin n → ℂ) 1) → IsClosed Z → IsClosed Cl → IsOpen U → U ⊆ Cl → (∀ x, x ∉ Z → Real.exp 1 ≤ r x) → (∀ (k : Fin B.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → (B.chart k).symm w₀ ∈ Cl → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (B.chart k).symm w ∉ Z → (Γ ((B.chart k).symm w)).PosDef ∧ ((Γ ((B.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)).PosSemidef ∧ (((C * r ((B.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - (Γ ((B.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => Γ ((B.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => Γ ((B.chart k).symm w') a b) w‖ ≤ C * Real.exp (r ((B.chart k).symm w) / 2)) → (∀ a b, A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).re) ∧ A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).im)) ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → (∀ x ∈ Cl \ Z, (((r x ^ C : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - blockG (Γ x)).PosSemidef ∧ (((r x ^ C : ℝ) : ℂ) • blockG (Γ x) - 1).PosSemidef) ∧ ∀ (a b : Fin (p + q)) (k : Fin B.n), ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2), (B.chart k).symm w ∈ Cl \ Z → ‖fderiv ℝ (fun w' => blockG (Γ ((B.chart k).symm w')) a b) w‖ ≤ C * r ((B.chart k).symm w) ^ C * Real.exp (r ((B.chart k).symm w) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds | exact GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds | (intros; apply GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFiniteFrameCoverStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_frame_cover : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), ∃ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι Ψ N M.Ω M.blk), (∀ l, IsOpen (O l)) ∧ (∀ x, ∃ l, x ∈ O l) ∧ (∀ l, M.IsFrame (F l)) ∧ ∀ l, ∀ x ∈ closure (O l), M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames.exists_finite_good_frames | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames.exists_finite_good_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames.exists_finite_good_frames <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExpandMInt
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.ExpandMInt

theorem expand_mInt : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X) (g : X → ℝ), IsOpen U → (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → (∀ T : Finset (Fin e), MIntegrable A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g) → MIntegrable A (fun i => P i + LocPot.ofFun (f i)) g ∧ mInt A (fun i => P i + LocPot.ofFun (f i)) g = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * mInt A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g := by
  intro e X _ _ _ A U P f Θ g hU hnull hP hΘ hf hT

  have hae : ∀ j, ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∈ (A.chart j).target →
      locDens A (fun i => P i + LocPot.ofFun (f i)) j y =
        ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
          locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
            LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
    intro j
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) (hnull j)
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hy
    refine ⟨hy.1, fun hyU => hy.2 ?_⟩
    exact GlobalTheory.T.local_density_inclusion_exclusion A U P f Θ hU hP hΘ hf j y ⟨hy.1, hyU⟩
  refine ⟨?_, ?_⟩
  · intro j K hK hKc
    have hsum : IntegrableOn (fun y => ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        (g ((A.chart j).symm y) * locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
            LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y)) K :=
      integrable_finsetSum _ fun T _ => (hT T j K hK hKc).const_mul _
    refine hsum.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae (hae j), ae_restrict_mem hKc.measurableSet] with y hy hyK
    rw [hy (hK hyK), Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  · unfold mInt
    split_ifs with h
    · unfold integralWith
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ fun T _ => (integrableOn_weight A h.some _ g (hT T) j).const_mul _]
      refine setIntegral_congr_ae (A.chart j).open_target.measurableSet ?_
      filter_upwards [hae j] with y hy hyt
      rw [hy hyt, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      ring
    · simp

end GlobalTheory.CompanionTheory.Metric.ExpandMInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentOrbitComparisonStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_orbit_comparison : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, M.ExactAt F (τ, i) z₀' h') → (∀ i, M.ExactAt F (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F z₀' z₁' h' t' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same.normRhs_same | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same.normRhs_same | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same.normRhs_same <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapVarietiesArithmeticStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 3) ∧ IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) (d + 2) ∧ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0) ∧ imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y ∧ ∀ v₁ : (Σ k, ι k) → (Σ o : Option K, ι (o.getD k₀)), (∀ p : (Σ k, ι k), p.1 ≠ k₀ → v₁ p = ⟨some p.1, p.2⟩) → (∀ m : ι k₀, v₁ ⟨k₀, m⟩ = ⟨none, m⟩) → imageZ v₁ (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic | exact GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t → ¬ SameOrbit (fstPt k₀ (RW.lift x x)) (sndPt k₀ (RW.lift x x)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.not_sameOrbit_of_ptData | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.not_sameOrbit_of_ptData | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.not_sameOrbit_of_ptData <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirst
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem base_orbit {σ : Type} {blk : σ → Option K} {z₁ z : (Σ k, ι k) → ℂ} (h : SameOrbit z₁ z) :
    SameOrbit (basePart blk z₁) (basePart blk z) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem comp_orbit {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) {b₁ b : (Σ k, ι' k) → ℂ} (h : SameOrbit b₁ b) :
    SameOrbit (b₁ ∘ v) (b ∘ v) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext q
  simp only [Function.comp]
  rw [hv.2.2.1 q]

theorem ideal_orbit {b₁ b : (Σ k, ι k) → ℂ} (h : SameOrbit b₁ b) : mCoordIdeal b₁ = mCoordIdeal b := by
  obtain ⟨c, hc, rfl⟩ := h
  exact StepW.TorusAct.mCoordIdeal_torus c hc b

theorem valAt_orbit {x : (Σ k, ι k) → Ω} {b₁ b : (Σ k, ι k) → ℂ} (h : SameOrbit b₁ b)
    (hb : b ∈ mcPts (mCoordIdeal x)) (s : Ω) : valAt x s b₁ = valAt x s b := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ((StepW.TorusAct.main K ι Ω x b c hc).2 hb).2 s

end Orbit

theorem img_spec (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K']
    (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j)
    (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F₀' : FrameData ι' Ψ N M'.Ω M'.blk)
    (F₀ : FrameData ι Ψ N M.Ω M.blk) (hz : z ∈ mcPts (mCoordIdeal y')) (hF' : M'.IsFrame F₀') (hF : M.IsFrame F₀)
    (hg' : M'.GoodAt F₀' (mCoordIdeal (basePart M'.blk z)))
    (hg : M.GoodAt F₀ (mCoordIdeal (basePart M'.blk z ∘ Cv.v))) :
    img Cv F₀' F₀ z ∈ mcPts (mCoordIdeal y) ∧ IsImg Cv z (img Cv F₀' F₀ z) := by
  have hb : basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z hz
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨h₀, hh₀, hz₀⟩ := GlobalTheory.T.exists_block_diag_frame_change K' ι' Φ' y' Ψ N j M' F₀' z hz hF' hg'
  have hT₀ := GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F₀' F₀ hb hF' hF hg' hg
  have hH₀ : ∀ τ, IsBlockDiag j (Cv.trans F₀' F₀ (basePart M'.blk z) τ * h₀ τ) ∧
      (Cv.trans F₀' F₀ (basePart M'.blk z) τ * h₀ τ).det ≠ 0 := fun τ =>
    ⟨(hT₀ τ).1.mul (hh₀ τ).1, by rw [det_mul]; exact mul_ne_zero (hT₀ τ).2 (hh₀ τ).2⟩
  have hform := GlobalTheory.T.flag_cover_frames_value_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z F₀' F₀ h₀ hb hF' hF hg' hg
    (fun τ => (hh₀ τ).1) hz₀
  have hwb : basePart M.blk (img Cv F₀' F₀ z) = basePart M'.blk z ∘ Cv.v := img_base Cv F₀' F₀ z
  have hw : img Cv F₀' F₀ z ∈ mcPts (mCoordIdeal y) :=
    (GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F₀ (img Cv F₀' F₀ z) _ hF (by rw [hwb]; exact hbv) (by rw [hwb]; exact hg) hH₀
      (by rw [hwb]; exact hform)).1
  refine ⟨hw, ?_⟩
  intro z₁ h1 F' F hF1' hF1 hg1' hg1 h hfl
  have hbo : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z) := base_orbit h1
  have hbov := comp_orbit Cv.block hbo
  rw [ideal_orbit hbo] at hg1'
  rw [ideal_orbit hbov] at hg1
  have htrans : ∀ τ, Cv.trans F' F (basePart M'.blk z₁) τ = Cv.trans F' F (basePart M'.blk z) τ := fun τ => by
    ext a c
    exact valAt_orbit hbo hb _
  obtain ⟨-, hhinv, hflag⟩ := hfl
  have hpl : ∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k',
      plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1) =
        a * plk M' F₀' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h₀ p.1) := fun p k' hp => by
    obtain ⟨a, ha, e⟩ := hflag p k' hp
    obtain ⟨a₀, ha₀, e₀⟩ := hz₀ p k' hp
    obtain ⟨c, hc, rfl⟩ := h1
    refine ⟨a⁻¹ * c k' * a₀, mul_ne_zero (mul_ne_zero (inv_ne_zero ha) (hc k')) ha₀, fun m' => ?_⟩
    have e1 := e m'
    have e2 := e₀ m'
    have e3 : ∑ I, valAt M'.x (F'.u ⟨k', m'⟩ I) (basePart M'.blk fun p => c p.1 * z p) *
        minorIJ (h p.1) I (stepCols N j p.2) = plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1) :=
      Finset.sum_congr rfl fun I _ => by rw [valAt_orbit hbo hb]
    rw [e3] at e1
    simp only at e1
    rw [e2] at e1
    field_simp
    linear_combination -e1
  have hind := GlobalTheory.T.flag_cover_two_frames_comparison K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F₀' F F₀ h h₀ hb hF1' hF' hF1 hF hg1' hg' hg1 hg
    (fun τ => (hhinv τ).1) (fun τ => (hh₀ τ).1) hpl
  have hT := GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hb hF1' hF1 hg1' hg1
  obtain ⟨-, z₀, o1, o2, fl⟩ := GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F (img Cv F₀' F₀ z)
    (fun τ => Cv.trans F' F (basePart M'.blk z) τ * h τ) hF1 (by rw [hwb]; exact hbv) (by rw [hwb]; exact hg1)
    (fun τ => ⟨(hT τ).1.mul (hhinv τ).1, by rw [det_mul]; exact mul_ne_zero (hT τ).2 (hhinv τ).2⟩)
    (fun p k hp => by
      obtain ⟨a₁, ha₁, e₁⟩ := hform p k hp
      obtain ⟨a₂, ha₂, e₂⟩ := hind p k hp
      refine ⟨a₁ * a₂⁻¹, mul_ne_zero ha₁ (inv_ne_zero ha₂), fun m => ?_⟩
      rw [e₁ m, hwb, e₂ m]
      field_simp)
  refine ⟨z₀, o1, Cj.sameOrbit_trans (hwb ▸ o2) (Cj.sameOrbit_symm hbov), ?_⟩
  simp only [htrans]
  exact fl

theorem local_img : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), f z' ∈ mcPts (mCoordIdeal y) ∧ CovMap.IsImg Cv z' (f z') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _ z hz
  have hb : basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z hz
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨F', hF', hg'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 _ hb
  obtain ⟨F, hF, hg⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ hbv
  obtain ⟨V, f, hV, hzV, hf, hs⟩ := GlobalTheory.T.flag_cover_frames_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z F' F hz hF' hF hg' hg
  refine ⟨V, f, hV, hzV, hf, fun z' hz' => ?_⟩
  obtain ⟨g1, g2, e⟩ := hs z' hz'
  rw [e]
  exact img_spec K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z' F' F hz'.2 hF' hF g1 g2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

