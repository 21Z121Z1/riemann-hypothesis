import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0009
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0093
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0089
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFamilyExistsOnEigenspaceStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_family_exists_on_eigenspace : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  first | exact @GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace | exact GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace | (intros; apply GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticVarietyGenericFibreProjectiveStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_variety_generic_fibre_projective : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (n : ℕ), (∀ V : Ideal (MRingOver ℚ ι), Nonempty K → IsProjVarF V n → IsArithVar (V.comap (MvPolynomial.map (Int.castRingHom ℚ))) (n + 1) ∧ (V.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = V) ∧ ∀ P : Ideal (MRing ι), IsArithVar P (n + 1) → IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) n ∧ (P.map (MvPolynomial.map (Int.castRingHom ℚ))).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.varieties_over_rat_arith_contract | exact GlobalTheory.CompanionTheory.Ar.PB.varieties_over_rat_arith_contract | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.varieties_over_rat_arith_contract <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricExplicitMatrixFormStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_metric_explicit_matrix_form : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ), M.blk p = some k₀ → IsGrChart N j p.2 I₀ C B → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → plk M (BM.F l) k₀ z I₀ ≠ 0 → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) (grMat C B I₀ (plk M (BM.F l) k₀ z)) + Real.log ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricRowEchelonLocalStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_metric_row_echelon_local : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → ∃ I₀, IsStepRows N j p.2 I₀ ∧ plk M (BM.F l) k₀ z I₀ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.exists_plk_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.exists_plk_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.exists_plk_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CauchyBinetSumPositionedMinorsStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchyBinet_sum_positioned_minors : ∀ {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω)
    (hBC : ∀ s, B s * C s = 1) (t : StepIx Ψ p q) (I I' : Finset (Fin (p + q)))
    (hI : I.card = (t.2 : ℕ) + 1) (hI' : I'.card = (t.2 : ℕ) + 1)
    (hp : ∀ a ∈ I, ∃ l, posOf p q t.1 l = a) (hp' : ∀ a ∈ I', ∃ l, posOf p q t.1 l = a),
    ∑ J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1), sMin B t I J * cMin C t J I' = if I = I' then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv.sum_sMin_mul_cMin | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv.sum_sMin_mul_cMin | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv.sum_sMin_mul_cMin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open ReciprocityTheory.AnForm.R

def chPrime {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (g : MvPolynomial (Fin m) ℂ) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  (Ideal.span {algebraMap _ (locRing I t) g}).comap (algebraMap _ (locRing I t))

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartSectionNotMemComponentsStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartSection_not_mem_components : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsMultiHomog s a → s ∉ Q →
    ∀ J ∈ chartComponents (conePts Q) σ i, chartSection σ i s ∉ J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSection_notMem_component | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSection_notMem_component | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSection_notMem_component <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartWSaturatedAndContinuousSectionStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartW_saturated_and_continuous_section : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (k : ℤ), k ≠ 0 → k • x ∈ chartW bas B → x ∈ chartW bas B) ∧ (∀ x ∈ chartW bas B, ContinuousAt (chartS bas A T0 x) 0 ∧ ∀ w ∈ logCover L.a_le, chartS bas A T0 x (expCover a w) = L.P w x) ∧ Function.Injective (chartPer bas A T0 B) ∧ Submodule.span ℂ (Set.range (chartPer bas A T0 B)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.noMonodromy_lattice | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.noMonodromy_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.noMonodromy_lattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceRateStatementHolds
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.Rate

theorem mInt_congr_φ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ Ψ : Fin e → LocPot X) (h : ∀ i, (Φ i).φ = (Ψ i).φ) (g : X → ℝ) :
    mInt A Φ g = mInt A Ψ g := by
  have hD : locDens A Φ = locDens A Ψ := by
    funext j y
    simp only [locDens, h]
  unfold mInt integralWith
  rw [hD]

theorem maMeasure_univ_eq {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ : LocPot X)
    (th : Fin e → LocPot X) (u : Fin e → X → ℝ) (hΘ : IsPotential A Θ)
    (hth : ∀ i, IsPotential A (th i)) (hu : ∀ i, A.Smooth (u i))
    (hP : ∀ i, IsPotential A (th i + LocPot.ofFun (u i) + Θ))
    (hPsh : ∀ i, IsPsh A (th i + LocPot.ofFun (u i) + Θ)) :
    maMeasure A (fun i => th i + LocPot.ofFun (u i) + Θ) Set.univ =
      ENNReal.ofReal (mInt A (fun i => th i + Θ) (fun _ => 1)) := by
  obtain ⟨hfin, hg⟩ := maMeasure_thm A _ hP hPsh
  have hI : Integrable (fun _ : X => (1 : ℝ)) (maMeasure A (fun i => th i + LocPot.ofFun (u i) + Θ)) :=
    integrable_const 1
  have hM := (hg _ measurable_const).1.2 hI
  have h2 := (hg _ measurable_const).2 hM
  have h3 : mInt A (fun i => th i + LocPot.ofFun (u i) + Θ) (fun _ => 1) =
      mInt A (fun i => (th i + Θ) + LocPot.ofFun (u i)) (fun _ => 1) := by
    refine mInt_congr_φ A _ _ (fun i => ?_) _
    funext x y
    show (th i).φ x y + u i y + Θ.φ x y = (th i).φ x y + Θ.φ x y + u i y
    ring
  rw [massIndep A (fun i => th i + Θ) u (fun i => isPotentialAdd A _ _ (hth i) hΘ) hu] at h3
  rw [← h3, h2, integral_const, smul_eq_mul, mul_one, ofReal_measureReal (measure_ne_top _ _)]

end GlobalTheory.CompanionTheory.Ar.Giv.Rate

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GlobalTheory.CompanionTheory.Ar.Giv.Rate in

theorem convergenceRate_holds : ConvergenceRateStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT th₀ ph₀ phT₀ C₅ C t₀
    hW hR hW₀ hR₀
  obtain ⟨K, t₂, ht₂, -, hT⟩ := tail_uniform tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC hnorm
    th ph phT C₅ C t₀ hW hR
  have ht₀ : 0 < t₀ := hR₀.1
  refine ⟨(3 + |C|) * |mInt A (fun i => th i + Θ) (fun _ => 1)| + (|C| + |C₅|) * |K|,
    min t₂ (min t₀ (Real.exp (-Real.exp 1))), lt_min ht₂ (lt_min ht₀ (Real.exp_pos _)), ?_⟩
  intro t t' ht' htt' ht1 c
  have htpos : 0 < t := ht'.trans_le htt'
  have ht_t₂ : t ≤ t₂ := ht1.trans (min_le_left _ _)
  have ht_t₀ : t ≤ t₀ := ht1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht_e : t ≤ Real.exp (-Real.exp 1) := ht1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlogt : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
  have hℓe : Real.exp 1 ≤ Real.log (1 / t) := by
    have := Real.log_le_log htpos ht_e
    rw [Real.log_exp] at this
    linarith
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Real.log (1 / t) = ℓ := ⟨_, rfl⟩
  rw [hℓ] at hℓe hlogt
  rw [hℓ]
  have hℓpos : 0 < ℓ := by linarith
  have hlogℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hℓe
  have hℓu : ∀ u, 0 < u → u ≤ t → ℓ ≤ Real.log (1 / u) := fun u hu hut =>
    hℓ ▸ Real.log_le_log (by positivity) (one_div_le_one_div_of_le hu hut)

  have heps : ∀ u, 0 < u → u ≤ t → epsT C u ≤ |C| * (Real.log ℓ / ℓ) := by
    intro u hu hut
    have hlu := hℓu u hu hut
    have hmono := Real.log_div_self_antitoneOn (Set.mem_Ici.2 hℓe) (Set.mem_Ici.2 (hℓe.trans hlu)) hlu
    have hnn : 0 ≤ Real.log (Real.log (1 / u)) / Real.log (1 / u) :=
      div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
    unfold epsT
    rw [mul_div_assoc]
    calc C * (Real.log (Real.log (1 / u)) / Real.log (1 / u))
        ≤ |C| * (Real.log (Real.log (1 / u)) / Real.log (1 / u)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hnn
      _ ≤ |C| * (Real.log ℓ / ℓ) := mul_le_mul_of_nonneg_left hmono (abs_nonneg C)
  have hrpow : ∀ u, 0 < u → u ≤ t → u ^ ((1 : ℝ) / 3) ≤ 3 / ℓ := by
    intro u hu hut
    refine (Real.rpow_le_rpow hu.le hut (by norm_num)).trans ?_
    rw [Real.rpow_def_of_pos htpos]
    have h3 : Real.log t * (1 / 3) = -(ℓ / 3) := by rw [hlogt]; ring
    rw [h3, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    linarith [Real.add_one_le_exp (ℓ / 3)]
  obtain ⟨q, hq⟩ : ∃ q, q = Real.log ℓ ^ 2 / ℓ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : 1 / ℓ ≤ q := hq ▸ div_le_div_of_nonneg_right (by nlinarith) hℓpos.le
  have hq2 : Real.log ℓ / ℓ ≤ q := hq ▸ div_le_div_of_nonneg_right (by nlinarith) hℓpos.le
  have hsmall : ∀ u, 0 < u → u ≤ t → u ^ ((1 : ℝ) / 3) + epsT C u ≤ (3 + |C|) * q := by
    intro u hu hut
    have h1 := hrpow u hu hut
    have h2 := heps u hu hut
    have h3 : |C| * (Real.log ℓ / ℓ) ≤ |C| * q := mul_le_mul_of_nonneg_left hq2 (abs_nonneg C)
    have h4 : 3 / ℓ = 3 * (1 / ℓ) := by ring
    nlinarith

  obtain ⟨-, hCt, hat, -, -, hdt, -, -⟩ := hR₀.2.2 t htpos ht_t₀
  obtain ⟨-, hCt', hat', -, -, hdt', -, -⟩ := hR₀.2.2 t' ht' (htt'.trans ht_t₀)
  have hsw := hW₀.2.2.2
  have hin : ∀ y ∉ bdry s, rW L s y < ℓ → |phT₀ t y - phT₀ t' y| ≤ (3 + |C|) * q := by
    intro y hy hry
    have h1 := hdt y hy (by rw [hℓ]; exact hry.le)
    have h2 := hdt' y hy (hry.le.trans (hℓu t' ht' htt'))
    have h3 := hsmall t htpos le_rfl
    have h4 := hsmall t' ht' htt'
    have h5 := hat y hy
    have h6 := hat' y hy
    rw [abs_le]
    constructor <;> linarith
  have hout : ∀ y ∉ bdry s, ℓ ≤ rW L s y →
      |phT₀ t y - phT₀ t' y| ≤ (|C| + |C₅|) * Real.log (rW L s y) := by
    intro y hy hry
    have hr1 : 1 ≤ Real.log (rW L s y) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (hℓe.trans hry)
    have h1 := hCt y
    have h2 := hCt' y
    have h5 := hat y hy
    have h6 := hat' y hy
    have h7 := (hsw y hy).1
    have h8 : C ≤ |C| * Real.log (rW L s y) := (le_abs_self C).trans (by nlinarith [abs_nonneg C])
    have h9 : C₅ * Real.log (rW L s y) ≤ |C₅| * Real.log (rW L s y) :=
      mul_le_mul_of_nonneg_right (le_abs_self C₅) (by linarith)
    rw [abs_le]
    constructor <;> nlinarith

  have hτ : ∀ i, 0 < (fun i => if c i then t else t') i ∧ (fun i => if c i then t else t') i ≤ t₂ := by
    intro i
    by_cases h : c i
    · simp only [h, if_true]; exact ⟨htpos, ht_t₂⟩
    · simp only [h]; exact ⟨ht', htt'.trans ht_t₂⟩
  obtain ⟨hPP, hTR⟩ := hT _ hτ
  obtain ⟨-, hlogR⟩ := hTR ℓ hℓe
  beta_reduce at hPP hlogR
  have hsm : ∀ i, A.Smooth (phT i (if c i then t else t')) := by
    intro i
    by_cases h : c i
    · simp only [h, if_true]; exact ((hR i).2.2 t htpos ht_t₀).1
    · simp only [h]; exact ((hR i).2.2 t' ht' (htt'.trans ht_t₀)).1
  have hmass := maMeasure_univ_eq A Θ th (fun i => phT i (if c i then t else t')) hΘ
    (fun i => (hW i).1) hsm (fun i => (hPP i).1) (fun i => (hPP i).2)
  have hnull : maMeasure A (fun i => th i + LocPot.ofFun (phT i (if c i then t else t')) + Θ)
      (bdry s) = 0 := bdry_null A L s m W hL hS hSNC _ (fun i => (hPP i).1)
  have hae := measure_eq_zero_iff_ae_notMem.1 hnull
  set μ := maMeasure A (fun i => th i + LocPot.ofFun (phT i (if c i then t else t')) + Θ) with hμ
  set M := mInt A (fun i => th i + Θ) (fun _ => (1 : ℝ)) with hM
  set k := |C| + |C₅| with hkdef
  have hk : 0 ≤ k := by positivity
  have ha : 0 ≤ (3 + |C|) * q := mul_nonneg (by positivity) hq0
  have hpt : ∀ᵐ y ∂μ, ENNReal.ofReal |phT₀ t y - phT₀ t' y| ≤
      ENNReal.ofReal ((3 + |C|) * q) + ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
        (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y := by
    filter_upwards [hae] with y hy
    by_cases hry : ℓ ≤ rW L s y
    · rw [Set.indicator_of_mem (show y ∈ (bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y} from ⟨hy, hry⟩),
        ← ENNReal.ofReal_mul hk]
      exact (ENNReal.ofReal_le_ofReal (hout y hy hry)).trans le_add_self
    · rw [Set.indicator_of_notMem (fun h => hry h.2), add_zero]
      exact ENNReal.ofReal_le_ofReal (hin y hy (not_le.1 hry))
  have hsec : ∫⁻ y, ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
        (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y ∂μ ≤
      ENNReal.ofReal k * ENNReal.ofReal (|K| * q) := by
    refine (lintegral_indicator_le _ _).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hKq : K * Real.log ℓ ^ 2 / ℓ ≤ |K| * q := by
      rw [hq, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    gcongr
    exact hlogR.trans (ENNReal.ofReal_le_ofReal hKq)
  calc ∫⁻ y, ENNReal.ofReal |phT₀ t y - phT₀ t' y| ∂μ
      ≤ ∫⁻ y, (ENNReal.ofReal ((3 + |C|) * q) + ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
          (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y) ∂μ :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal ((3 + |C|) * q) * μ Set.univ + ∫⁻ y, ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
          (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ ENNReal.ofReal ((3 + |C|) * q) * ENNReal.ofReal |M| +
          ENNReal.ofReal k * ENNReal.ofReal (|K| * q) := by
        rw [hmass]
        gcongr
        exact le_abs_self _
    _ = ENNReal.ofReal ((3 + |C|) * q * |M| + k * (|K| * q)) := by
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hk,
          ← ENNReal.ofReal_add (mul_nonneg ha (abs_nonneg _)) (mul_nonneg hk (mul_nonneg (abs_nonneg _) hq0))]
    _ ≤ ENNReal.ofReal (((3 + |C|) * |M| + k * |K|) * Real.log ℓ ^ 2 / ℓ) :=
        ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hq]; ring))

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspSubmodulesLocallyFiniteStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_submodules_locally_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsOpen U → IsHolFam U R → IsCMFam σ → (∀ t ∈ U, (R t).HasRank σ m) → ∀ t₀ ∈ U, ∃ (ε : ℝ) (F : Finset (Submodule (𝓞 E) Λ)), 0 < ε ∧ ∀ t ∈ U ∩ Metric.ball t₀ ε, (∀ I ∈ F, (R t).IsCusp I) ∧ ∀ I, (R t).IsCusp I → (R t).nz σ I ≤ 1 → I ∈ F := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cusp_submodules_locally_finite | exact GlobalTheory.CompanionTheory.Relay.cusp_submodules_locally_finite | (intros; apply GlobalTheory.CompanionTheory.Relay.cusp_submodules_locally_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentAppendIndependentSpan
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep

theorem eq_zero_of_sum_mem_span : ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : 𝓞 E →+* Module.End ℂ V) (s₀ : 𝓞 E →+* ℂ) (I₀ : AddSubgroup V) (r k : ℕ) (v : Fin r → V) (q : Fin k → V),
    IsOFamily ρ I₀ v → (∀ (c : 𝓞 E), ∀ x ∈ I₀, ρ c x ∈ I₀) → (∀ c, q c ∈ eigSp ρ s₀) →
    LinearIndependent ℂ (Fin.append (fun a => eigComp ρ s₀ (v a)) q) →
    ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ Submodule.span ℂ (I₀ : Set V) → l = 0 := by
  intro E _ _ V _ _ ρ s₀ I₀ r k v q hF _ hq hli l hl
  obtain ⟨c, hc⟩ := EigCoef.eigComp_eq_combination E s₀
  obtain ⟨h1, h2, h3⟩ := hc V ρ
  let π : V →ₗ[ℂ] V := ∑ a ∈ c.support, c a • ρ a
  have hπ : ∀ x, π x = eigComp ρ s₀ x := by
    intro x
    rw [h1 x]
    simp [π, LinearMap.sum_apply]
  have hact : ∀ (b : 𝓞 E) x, π (ρ b x) = s₀ b • π x := by
    intro b x
    have e : π (ρ b x) = ρ b (π x) := by
      simp only [π, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      have : ρ a * ρ b = ρ b * ρ a := by rw [← map_mul, ← map_mul, mul_comm]
      exact LinearMap.congr_fun this x
    rw [e, EigCoef.mem_eigSp_iff.1 (hπ x ▸ h2 x) b]
  let W : Submodule ℂ V := Submodule.span ℂ (Set.range fun a => eigComp ρ s₀ (v a))
  have hO : ∀ y ∈ oSpan ρ v, π y ∈ W := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, i, rfl⟩ := hy
      rw [hact, hπ]
      exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact W.add_mem hx hy
    | neg x _ hx =>
      rw [map_neg]
      exact W.neg_mem hx
  have hI : ∀ x ∈ I₀, π x ∈ W := by
    intro x hx
    obtain ⟨_, _, hN⟩ := hF
    have hm := hO _ (AddSubgroup.nsmul_relIndex_mem (oSpan ρ v) hx)
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ] at hm
    have hN' : (((oSpan ρ v).relIndex I₀ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    exact (W.smul_mem_iff hN').1 hm
  have hS : Submodule.span ℂ (I₀ : Set V) ≤ W.comap π := Submodule.span_le.2 hI
  have hxe : ∑ c, l c • q c ∈ eigSp ρ s₀ := Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hq c)
  have hW : ∑ c, l c • q c ∈ W := by
    have h := hS hl
    rw [Submodule.mem_comap, hπ, h3 _ hxe] at h
    exact h
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hW
  have hz := Fintype.linearIndependent_iff.1 hli (Fin.append (-m) l) (by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    rw [hm]
    simp)
  funext j
  have := hz (Fin.natAdd r j)
  simpa using this

end GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsComponentInChartRegularStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_component_in_chart_regular : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (tie : CoordTie ℤ ξ (seg y)) (Q : Ideal (MRing J))
    (hQ : Q.IsPrime) (hle : mCoordIdeal y ≤ Q) (c : ∀ k, J k)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ Q),
    ∃ P : Cpt ξ, InChart ξ (seg y) c P ∧ ∀ a ∈ regAt ξ P, RegAt y Q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime <;> assumption)
end

