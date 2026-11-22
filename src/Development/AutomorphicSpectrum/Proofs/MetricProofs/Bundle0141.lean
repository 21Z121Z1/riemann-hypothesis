import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0138
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
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0108
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0019
import Development.WeilBound.CoreStatements.PluriharmonicCharts.EvalFam
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0032
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0099
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0120
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0139
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0022
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0013
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0063
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0095
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0131
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralDensityIndependentProjectionStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_density_independent_projection : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) g y) =
      ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) g y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerBoundHeightOnBoundary
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.lowerBound_height_on_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal x) ∩ mcPts bd) : Set (mcPts (mCoordIdeal x))) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → ∃ (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Rb.X), IsPotential Rb.A L ∧ IsSection Rb.A L s ∧ IsSNC Rb.A L s m W ∧ (∀ p, logNormSec L s p ≤ 0) ∧ (∀ p, p ∈ bdry s ↔ Rb.lift p p ∈ mcPts bd) ∧ ∀ p p', SameOrbit (Rb.lift p' p') (fun q => starRingEnd ℂ (Rb.lift p p q)) → rW L s p' = rW L s p := by
  intro K _ J _ Ω _ _ x n bd hsnc harith _ htor hconj
  obtain ⟨I, hIh, hIle, hIsnc, hIeq⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.exists_homogIdeal x n bd hsnc harith htor
  obtain ⟨Rb, nb, W, hloc⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.exists_res x n I harith hIh hIle hIsnc
  rw [hIeq] at hloc
  obtain ⟨L, s, h1, h2, h3, h4, h5, h6⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.assemble Rb (mcPts (mCoordIdeal x) ∩ mcPts bd)
      (fun z hz c hc => htor z hz c hc) (fun z hz => hconj z hz) nb W hloc
  refine ⟨Rb, L, s, nb, fun _ => 1, W, h1, h2, h3, h4, fun p => ?_, h6⟩
  rw [h5 p]
  exact ⟨fun hp => hp.2, fun hp => ⟨Rb.mem p p (Rb.mem_U p), hp⟩⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentOrbitEqualityStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_unipotent_orbit_equality : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ L L' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → (∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ')) → SameOrbit (FC.flagPt M (BM.F l) (FC.bvec BM l b) L) (FC.flagPt M (BM.F l) (FC.bvec BM l b) L') → L = L' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flag_uniq | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flag_uniq | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flag_uniq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralLimitOnModel
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem continuous_of_atlasSmooth {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    have := (hf j).continuousOn
    simpa [Set.preimage_univ, Set.inter_univ] using this
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    (h1.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).comp
      ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

theorem tendsto_ptsIntegral_of_chart_conv : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas) (Θ : LocPot M.Xc) (Pp : Fin n → LocPot M.Xc) (f : Fin n → M.Xc → ℝ) (fT : Fin n → ℝ → M.Xc → ℝ) (G : M.Xc → ℝ) (GT : ℝ → M.Xc → ℝ) (C : ℝ) (L : ℝ → Fin n → HermLine ι) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ), IsArithVar P (n + 1) → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → (∀ i, IsPotential M.atlas (Pp i)) → (∀ i, M.atlas.SmoothOn R.Yo (f i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, M.atlas.Smooth (fT i t) ∧ IsPsh M.atlas (Pp i + LocPot.ofFun (fT i t) + Θ) ∧ ∀ x ∈ R.Yo, |fT i t x| ≤ C + C * Real.log (R.r x) ∧ fT i t x ≤ C) → (∀ i, ∀ j, ∀ K' ⊆ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fT i t ∘ (M.atlas.chart j).symm) (f i ∘ (M.atlas.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm)) (fderiv ℝ (f i ∘ (M.atlas.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm))) (fderiv ℝ (fderiv ℝ (f i ∘ (M.atlas.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (GT t) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i x, ∀ y₀ ∈ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G' : M.Xc → ℂ, M.atlas.HoloOn U G' ∧ ∀ y' ∈ U, (Pp i + LocPot.ofFun (fT i t)).φ x y' - Real.log ((L t i).h (s y')) = (G' y').re) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ mcPts P, g t z = GT t (M.proj z)) → ∃ l : ℝ, Tendsto (fun t => ptsIntegral P (pot (L t)) (g t)) (𝓝[>] 0) (𝓝 l) := by
  intro K _ ι _ P n M R Θ Pp f fT G GT C L g hV hΘ hΘp hP hf hfT hconv hGT hGc hrel hg
  classical
  by_cases hQ : ∃ Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ), IsGoodProj P Q
  · have hYo := (GlobalTheory.T.regular_chart_data_properties n M.Xc M.atlas R).1
    have hmeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable M.Xc ℝ (borel M.Xc) _ (R.Yo.indicator (GT t)) ∧
        ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x) := by
      filter_upwards [hGT] with t ht
      refine ⟨?_, ht.2⟩
      letI : MeasurableSpace M.Xc := borel M.Xc
      haveI : BorelSpace M.Xc := ⟨rfl⟩
      exact (continuous_of_atlasSmooth ht.1).measurable.indicator hYo.measurableSet
    obtain ⟨-, hint, hlim⟩ := GlobalTheory.T.mixed_integral_tendsto_off_divisor n M.Xc M.atlas R Θ hΘ hΘp Pp f fT G GT C hP hf hfT hconv
      hmeas hGc
    refine ⟨_, hlim.congr' ?_⟩
    filter_upwards [hint, hfT, hGT, hrel, hg] with t hit hft hgt hrt hgt'
    have hpush := GlobalTheory.T.mixed_integral_model_formula K ι P n M hQ.choose Set.univ ∅ ∅ (fun _ => 1) (L t)
      (fun i => Pp i + LocPot.ofFun (fT i t)) (g t) (GT t) hV hQ.choose_spec isOpen_univ
      (fun j => by simp)
      (fun Ψ _ => by simp)
      (fun i x => by
        intro j
        have h1 := (hP i).1 x j
        have h2 := (hft i).1 j
        have h3 := h1.add (h2.mono (fun y hy => ⟨hy.1, Set.mem_univ _⟩))
        refine (h3.mono ?_).congr ?_
        · rintro y ⟨hy, hy'⟩
          exact ⟨hy, hy'.1.1⟩
        · intro y _
          rfl)
      (fun i x y₀ hy₀ => by
        obtain ⟨U, hU, hyU, hUs, s, hs, hsp, G', hG', hrel'⟩ := hrt i x y₀ hy₀
        exact ⟨U, hU, hyU, hUs, s, hs, hsp, G', hG', fun y' hy' => by
          simpa using hrel' y' hy'⟩)
      (fun z hz _ _ _ => hgt' z hz)
      (fun j => ((continuous_of_atlasSmooth hgt.1).comp_continuousOn
        (M.atlas.chart j).continuousOn_symm).aestronglyMeasurable (M.atlas.chart j).open_target.measurableSet)
    have h3 := (hpush.2.2 hit).2
    have hpot : (fun i z => (fun _ : Fin n => (1 : ℝ)) i * Real.log ((L t i).h z)) = pot (L t) := by
      funext i z
      simp [pot]
    rw [hpot] at h3
    rw [ptsIntegral, dif_pos hQ, h3]
  · refine ⟨0, ?_⟩
    have : (fun t => ptsIntegral P (pot (L t)) (g t)) = fun _ => (0 : ℝ) := by
      funext t
      rw [ptsIntegral, dif_neg hQ]
    rw [this]
    exact tendsto_const_nhds

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelPointsIntegrableStatementHolds
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree

section Transfer

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem modelChart_injOn (χ φ : OpenPartialHomeomorph X (Fin e → ℂ)) :
    Set.InjOn (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source) := by
  intro u hu u' hu' h
  have h1 : χ.symm u = χ.symm u' := φ.injOn hu.2 hu'.2 h
  have h2 := congrArg χ h1
  rwa [χ.right_inv hu.1, χ.right_inv hu'.1] at h2

theorem modelChart_null (χ φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : AnalyticOnNhd ℂ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source)) (E : Set X)
    (hE : volume (χ.target ∩ χ.symm ⁻¹' E) = 0) :
    volume (φ.target ∩ φ.symm ⁻¹' (E ∩ χ.source)) = 0 := by
  have hd : DifferentiableOn ℝ (φ ∘ χ.symm)
      (χ.target ∩ χ.symm ⁻¹' φ.source ∩ χ.symm ⁻¹' E) :=
    (hσ.differentiableOn.restrictScalars ℝ).mono Set.inter_subset_left
  have h0 : volume (χ.target ∩ χ.symm ⁻¹' φ.source ∩ χ.symm ⁻¹' E) = 0 :=
    measure_mono_null (t := χ.target ∩ χ.symm ⁻¹' E) (fun u hu => ⟨hu.1.1, hu.2⟩) hE
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd h0
  refine measure_mono_null ?_ himg
  rintro y ⟨hy, hyE, hyχ⟩
  refine ⟨χ (φ.symm y), ⟨⟨χ.map_source hyχ, ?_⟩, ?_⟩, ?_⟩
  · show χ.symm (χ (φ.symm y)) ∈ φ.source
    rw [χ.left_inv hyχ]; exact φ.map_target hy
  · show χ.symm (χ (φ.symm y)) ∈ E
    rw [χ.left_inv hyχ]; exact hyE
  · simp [χ.left_inv hyχ, φ.right_inv hy]

theorem modelChart_integrableOn (χ φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : AnalyticOnNhd ℂ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source)) (v : X → ℝ)
    (hv : ∀ Q ⊆ χ.target, IsCompact Q → IntegrableOn (fun y => v (χ.symm y)) Q)
    {Q : Set (Fin e → ℂ)} (hQ : IsCompact Q) (hQs : Q ⊆ φ.target ∩ φ.symm ⁻¹' χ.source) :
    IntegrableOn (fun y => v (φ.symm y)) Q := by
  have hSo : IsOpen (χ.target ∩ χ.symm ⁻¹' φ.source) :=
    χ.isOpen_inter_preimage_symm φ.open_source
  have hρc : ContinuousOn (χ ∘ φ.symm) Q :=
    χ.continuousOn.comp (φ.continuousOn_symm.mono fun y hy => (hQs hy).1) fun y hy => (hQs hy).2
  have hQ' : IsCompact ((χ ∘ φ.symm) '' Q) := hQ.image_of_continuousOn hρc
  have hQS : (χ ∘ φ.symm) '' Q ⊆ χ.target ∩ χ.symm ⁻¹' φ.source := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨χ.map_source (hQs hy).2, ?_⟩
    show χ.symm (χ (φ.symm y)) ∈ φ.source
    rw [χ.left_inv (hQs hy).2]; exact φ.map_target (hQs hy).1
  have himg : (φ ∘ χ.symm) '' ((χ ∘ φ.symm) '' Q) = Q := by
    rw [Set.image_image]
    refine Set.ext fun y => ⟨?_, fun hy => ⟨y, hy, ?_⟩⟩
    · rintro ⟨y', hy', rfl⟩
      simpa [χ.left_inv (hQs hy').2, φ.right_inv (hQs hy').1] using hy'
    · simp [χ.left_inv (hQs hy).2, φ.right_inv (hQs hy).1]
  have hσR : AnalyticOnNhd ℝ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source) :=
    hσ.restrictScalars
  have hder : ∀ u ∈ (χ ∘ φ.symm) '' Q,
      HasFDerivWithinAt (φ ∘ χ.symm) (fderiv ℝ (φ ∘ χ.symm) u) ((χ ∘ φ.symm) '' Q) u :=
    fun u hu => ((hσR u (hQS hu)).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  have hinj : Set.InjOn (φ ∘ χ.symm) ((χ ∘ φ.symm) '' Q) := (modelChart_injOn χ φ).mono hQS
  have hcont : ContinuousOn (fun u => |(fderiv ℝ (φ ∘ χ.symm) u).det|) ((χ ∘ φ.symm) '' Q) := by
    have h1 : ContinuousOn (fderiv ℝ (φ ∘ χ.symm)) (χ.target ∩ χ.symm ⁻¹' φ.source) :=
      (hσR.fderiv).continuousOn
    exact (ContinuousLinearMap.continuous_det.comp_continuousOn (h1.mono hQS)).abs
  have hint := (hv _ (fun u hu => (hQS hu).1) hQ').continuousOn_mul hcont hQ'
  rw [← himg]
  refine (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hQ'.measurableSet hder
    hinj _).2 ?_
  refine hint.congr_fun (fun u hu => ?_) hQ'.measurableSet
  have hu := hQS hu
  simp only [smul_eq_mul, Function.comp_apply, φ.left_inv hu.2]

theorem modelChart_integrableOn_cover {n : ℕ} (χ : Fin n → OpenPartialHomeomorph X (Fin e → ℂ))
    (φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : ∀ k, AnalyticOnNhd ℂ (φ ∘ (χ k).symm) ((χ k).target ∩ (χ k).symm ⁻¹' φ.source))
    (hcov : ∀ x, ∃ k, x ∈ (χ k).source) (v : X → ℝ)
    (hv : ∀ k, ∀ Q ⊆ (χ k).target, IsCompact Q → IntegrableOn (fun y => v ((χ k).symm y)) Q) :
    LocallyIntegrableOn (fun y => v (φ.symm y)) φ.target := by
  intro y hy
  obtain ⟨k, hk⟩ := hcov (φ.symm y)
  have hWo : IsOpen (φ.target ∩ φ.symm ⁻¹' (χ k).source) :=
    φ.isOpen_inter_preimage_symm (χ k).open_source
  obtain ⟨Q, hQn, hQs, hQc⟩ := local_compact_nhds (hWo.mem_nhds ⟨hy, hk⟩)
  exact ⟨Q, mem_nhdsWithin_of_mem_nhds hQn, modelChart_integrableOn (χ k) φ (hσ k) v (hv k) hQc hQs⟩

theorem modelChart_null_cover {n : ℕ} (χ : Fin n → OpenPartialHomeomorph X (Fin e → ℂ))
    (φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : ∀ k, AnalyticOnNhd ℂ (φ ∘ (χ k).symm) ((χ k).target ∩ (χ k).symm ⁻¹' φ.source))
    (hcov : ∀ x, ∃ k, x ∈ (χ k).source) (E : Set X)
    (hE : ∀ k, volume ((χ k).target ∩ (χ k).symm ⁻¹' E) = 0) :
    volume (φ.target ∩ φ.symm ⁻¹' E) = 0 := by
  refine measure_mono_null (t := ⋃ k, φ.target ∩ φ.symm ⁻¹' (E ∩ (χ k).source)) ?_
    (measure_iUnion_null fun k => modelChart_null (χ k) φ (hσ k) E (hE k))
  rintro y ⟨hy, hyE⟩
  obtain ⟨k, hk⟩ := hcov (φ.symm y)
  exact Set.mem_iUnion.2 ⟨k, hy, hyE, hk⟩

end Transfer

theorem modelPtsIntegrable : ModelPtsIntegrable.Statement := by
  intro K _ ι _ P e M n ψ L c N E v g hV hL hN hψ hcov hE hv hg Ψ hΨ
  obtain ⟨Φ₀, hΦ₀, hloc⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K ι P e M L hL
  have hΦ : IsPotential M.atlas (Φ₀.rsmul c) := isPotentialRsmul M.atlas c Φ₀ hΦ₀
  have hli : ∀ j, LocallyIntegrableOn (fun y => v ((M.atlas.chart j).symm y))
      (M.atlas.chart j).target := fun j =>
    modelChart_integrableOn_cover ψ (M.atlas.chart j) (fun k => (hψ k j).2) hcov v hv
  have hint : ∀ j, ∀ Q ⊆ (M.atlas.chart j).target, IsCompact Q →
      IntegrableOn (fun y => v ((M.atlas.chart j).symm y)) Q := fun j Q hQ hQc =>
    (hli j).integrableOn_compact_subset hQ hQc
  have hnull : ∀ j, volume ((M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' ((Set.univ : Set M.Xc)ᶜ ∪ E)) = 0 := fun j => by
    simpa using modelChart_null_cover ψ (M.atlas.chart j) (fun k => (hψ k j).2) hcov E hE
  have hMI : MIntegrable M.atlas (fun _ : Fin e => Φ₀.rsmul c) v := fun j Q hQ hQc =>
    (hint j Q hQ hQc).mul_continuousOn
      ((locDensCont M.atlas _ (fun _ => hΦ) j).mono hQ) hQc
  refine ((GlobalTheory.T.mixed_integral_model_formula K ι P e M Ψ Set.univ E N (fun _ => c) (fun _ => L)
    (fun _ => Φ₀.rsmul c) g v hV hΨ isOpen_univ hnull hN ?_ ?_ ?_ ?_).2.2 hMI).1
  · exact fun _ x j => (hΦ.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  · intro _ x y₀ hy₀
    obtain ⟨U, hUo, hyU, hUs, s, hs, hsh, G, hG, hGe⟩ := hloc x y₀ hy₀
    refine ⟨U, hUo, hyU, hUs, s, hs, hsh, fun z => (c : ℂ) * G z, holoOn_mul M.atlas hG c,
      fun y' hy' => ?_⟩
    have h1 : Φ₀.φ x y' - Real.log (L.h (s y')) = (G y').re := hGe y' hy'
    show c * Φ₀.φ x y' - c * Real.log (L.h (s y')) = ((c : ℂ) * G y').re
    rw [Complex.re_ofReal_mul, ← h1]
    ring
  · exact fun z hz hzN _ hzE => hg z hz hzN hzE
  · exact fun j => (hli j).aestronglyMeasurable

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionOfChartAnalyticStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_of_chart_analytic : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (a : Fin D.nCharts) (k : Fin M.atlas.n), ∀ t ∈ Metric.ball (0 : Fin D.n → ℂ) 1, M.proj ((D.chart a).γ t) ∈ (M.atlas.chart k).source → AnalyticAt ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t ∧ Function.Bijective (fderiv ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic | exact GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic | (intros; apply GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralLogNormRatEqBase
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem ptsIntegral_logNormRat_eq_base : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R.X → X) (hπ : HoloMap R.A A π) (dg : ℕ) (br : Set X), IsArithVar P (D + 1) → IsDegreeOff A R.A π dg br → ∀ (L : Fin D → HermLine ι) (Φ : Fin D → LocPot X), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPotential A (Φ j)) → (∀ j, SamePot R.A Set.univ (potOf R (L j)) ((Φ j).pullback π hπ.1)) → ∀ (Am : HermLine ι) (f g : MRing ι) (u : X → ℝ) (N : Set R.X), IsSmoothHerm Am → IsRatSectionOn P Am f g → IsNull R.A N → (∀ x ∉ N, logNormRat Am f g (R.lift x x) = u (π x)) → MIntegrable A Φ u → ptsIntegral P (pot L) (logNormRat Am f g) = dg * mInt A Φ u :=
  @PositivityTheory.Xgp.t_re_bridge

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedLeviLowerBoundEventually
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.regularized_levi_lower_bound_eventually : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), S'.IsTied → ∀ δ > (0 : ℝ), ∀ᶠ t' in 𝓝[>] (0 : ℝ), ∀ a, ∀ t : Fin D.n → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, -(δ * ‖v‖ ^ 2) ≤ levi (fun s : Fin D.n → ℂ => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v := by
  first | exact @LevelTowerAlt.tied_regularization_asymptotic | exact LevelTowerAlt.tied_regularization_asymptotic
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)

namespace GlobalTheory.CompanionTheory.Ar.Giv

namespace ResTop

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem coord_ne_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (p : Σ k, ι k)
    (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  unfold mCoordIdeal
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem charZero_of_horizontal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) :
    CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have h1 : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, map_natCast, map_natCast,
      ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [IsHorizontal] at h
  rw [h, Ideal.mem_bot] at h1
  exact_mod_cast h1

variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem isBlockMap_joinInl : IsBlockMap (Sum.inl : K → K ⊕ K₂) (joinInl ι ι₂) := by
  refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 : k = k' := Sum.inl_injective (congrArg Sigma.fst h)
    subst h1
    have h2 : i = i' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [h2]
  · rintro ⟨k, i⟩ ⟨k', rfl⟩
    exact ⟨⟨k', i⟩, rfl⟩

theorem evC_rename_inl (z : (Σ k, joinIdx ι ι₂ k) → ℂ) (f : MRing ι) :
    evC z (rename (joinInl ι ι₂) f) = evC (z ∘ joinInl ι ι₂) f := by
  unfold evC
  rw [map_rename, eval_rename]

theorem comp_inl_mem {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω)
    {z : (Σ k, joinIdx ι ι₂ k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (joinVec y y₂))) :
    z ∘ joinInl ι ι₂ ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩
  have hc : (mConeMap (joinVec y y₂)).comp (rename (joinInl ι ι₂)) =
      ((rename (Sum.inl : K → K ⊕ K₂) : MvPolynomial K Ω →ₐ[Ω] _).restrictScalars ℤ).comp (mConeMap y) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    obtain ⟨k, i⟩ := p
    simp [mConeMap, joinInl, joinVec]
  have hf' : rename (joinInl ι ι₂) f ∈ mCoordIdeal (joinVec y y₂) := by
    have h1 := AlgHom.congr_fun hc f
    have h0 : mConeMap y f = 0 := hf
    simp only [AlgHom.comp_apply, h0, map_zero] at h1
    exact h1
  exact (evC_rename_inl z f).symm.trans (hz.2 _ hf')

end ResTop

open ResTop in

theorem resExists_of_resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ResExistsStatement := by
  intro hRes K _ ι _ P J e hP hJ hJP
  obtain ⟨Ω, _, y, rfl, -⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.proof K ι P (e + 1) hP
  haveI : CharZero Ω := charZero_of_horizontal y hP.2.2.1
  have hprime : (mCoordIdeal y).IsPrime := hP.2.1.1
  obtain ⟨β, hβJ, ⟨b, hβ⟩, hβP⟩ : ∃ β ∈ J, (∃ b, IsMultiHomog β b) ∧ β ∉ mCoordIdeal y := by
    obtain ⟨S, hS, rfl⟩ := hJ
    by_contra hcon
    push Not at hcon
    exact hJP (Ideal.span_le.mpr fun f hf => hcon f (Ideal.subset_span hf) (hS f hf))
  obtain ⟨β', b', M, y', J₁, hβ', hβ'P, hzero, hy', hfield, hJ₁h, hJ₁, hsnc, hz, hG⟩ :=
    GlobalTheory.T.multihomogeneous_lift_to_join hRes K ι Ω y e β b hP hβ hβP
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    exact ⟨i, coord_ne_zero y ⟨k, i⟩ hi⟩
  have hblocks : ∀ k, ∃ i, joinVec y y' ⟨k, i⟩ ≠ 0 := by
    rintro (k | u)
    · exact hy k
    · exact hy'
  have hcomp : joinVec y y' ∘ joinInl ι (fun _ : Unit => Fin M) = y := rfl
  have harith : IsArithVar (mCoordIdeal (joinVec y y')) (e + 1) := by
    refine isArithVar_of_isAlgebraic_image K ι (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Sum.inl
      (joinInl ι fun _ : Unit => Fin M) Ω (joinVec y y') (e + 1) isBlockMap_joinInl hblocks ?_ ?_
    · rw [hcomp]; exact hP
    · rw [hcomp, hfield]
      intro t ht
      exact isAlgebraic_algebraMap (⟨t, ht⟩ : blockFnField y)
  obtain ⟨R, hR⟩ := GlobalTheory.T.snc_model_embedded_log_resolution (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Ω (joinVec y y') e J₁
    harith hJ₁h hJ₁ hsnc
  have hγ := homog_mul hβ hβ'
  have hγP : β * β' ∉ mCoordIdeal y := fun h => (hprime.mem_or_mem h).elim hβP hβ'P
  have hmul : ∀ z : (Σ k, ι k) → ℂ, evC z (β * β') = evC z β * evC z β' := fun z => by
    simp only [evC, map_mul]
  refine ⟨Ideal.span {β * β'}, ?_, ⟨{β * β'}, ?_, rfl⟩, ?_, ?_⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact J.mul_mem_right _ hβJ
  · rintro f rfl
    exact ⟨_, hγ⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact hγP
  · refine GlobalTheory.T.multihomogeneous_nonvanishing_on_join K ι Ω y e M y' J₁ R (β * β') (b + b') hR hy' hy hγ hγP ?_ ?_
    · intro z hzm h0
      apply hz z hzm
      rw [evC_rename_inl] at h0 ⊢
      rw [hmul] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · exact hzero _ (comp_inl_mem y y' hzm) h
      · exact h
    · intro z hzm hne
      apply hG z hzm
      rw [hmul] at hne
      exact right_ne_zero_of_mul hne

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalFactorSmoothHermitianMetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.vertical_factor_smooth_hermitian_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∀ p ∈ D.S, (∃ A : HermLine J, A.a = D.vdeg p ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z) ∧ ∀ a, ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ G : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, Real.log (D.vertFactor p ((D.chart a).γ t')) = (G t').re := by
  first | exact @LevelTowerAlt.vertical_factor_smooth_line | exact LevelTowerAlt.vertical_factor_smooth_line
end

