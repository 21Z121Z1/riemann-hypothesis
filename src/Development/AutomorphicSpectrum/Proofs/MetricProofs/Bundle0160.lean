import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0115
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0120
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0132
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0117
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0148
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0140
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0143
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0153
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0147
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0154
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0145
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormSqEqAdaptedFrameSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetCoverOfArithmeticVariety
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0155

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Main
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W}

theorem tuo_const {A₁ B₁ C₂ : Type*} [UniformSpace B₁] (l : Filter C₂) (f : A₁ → B₁) (s : Set A₁) :
    TendstoUniformlyOn (fun _ : C₂ => f) f l s :=
  fun _ hu => Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu

theorem mem_Xo_of_proj_mem {Hd : HodgeData D} {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine Hd))
    {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) (hY : M.proj z ∈ S.R.Yo) : z ∈ D.Xo := by
  obtain ⟨z', ⟨hz'X, hz'P⟩, hz'⟩ := S.Yo_sub _ hY
  obtain ⟨c, hc, hzc⟩ := (M.fibre z' hz'P z hz).1 hz'
  refine ⟨hz, fun hB => ?_⟩
  have hinv : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have h1 := D.bd_torus z hB (fun k => (c k)⁻¹) hinv
  have h2 : torusSmul (fun k => (c k)⁻¹) z = z' := by
    funext p
    rw [hzc]
    simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]
  rw [h2] at h1
  exact hz'X.2 h1

theorem tendsto_arLimFun (hLoc : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement) {Hd : HodgeData D} {M : XModel D}
    (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (hS : S.IsTied) (B : ℕ) (hII : IsFullIntersectionSystem II)
    (Nb : HermLine J) (hNb : IsSmoothHerm Nb) (hNa : Nb.a = muTwDeg Hd B) :
    Tendsto (arLimFun Hd S B) (𝓝[>] 0) (𝓝 (limTop Hd B Nb)) := by
  obtain ⟨Pn, hPn, hPnS⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K J (mCoordIdeal D.y) D.n M Nb hNb
  obtain ⟨Θ, hΘ, hΘp, hΘN⟩ := GlobalTheory.T.exists_positive_potential_dominating K J II Ψ Ω W D M Pn hPn
  obtain ⟨-, ⟨C₁, hC₁⟩, hpsh⟩ := GlobalTheory.T.regularized_weight_psh_and_bounds K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S Θ hS hΘ hΘp
  obtain ⟨κ, hκc, hκ⟩ := GlobalTheory.T.exists_continuous_metric_ratio K J II Ψ Ω W D Hd M S B Nb hNb hNa
  obtain ⟨Bκ, hBκ⟩ : ∃ b : ℝ, ∀ x, |κ x| ≤ b := by
    obtain ⟨b, hb⟩ := (isCompact_univ.image hκc).isBounded.exists_norm_le
    exact ⟨b, fun x => hb _ ⟨x, Set.mem_univ _, rfl⟩⟩
  obtain ⟨hYo, hYnull, -, -⟩ := GlobalTheory.T.regular_chart_data_properties D.n M.Xc M.atlas S.R
  have hph := S.R.ph_smooth

  set Cc : ℝ := |C₁| + |S.R.Clog| + |Bκ| + 1 with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  have hlogr : ∀ x ∈ S.R.Yo, 0 ≤ Real.log (S.R.r x) := fun x hx => Real.log_nonneg (S.R.one_le_r x hx)

  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧
      ∀ x ∈ S.R.Yo, |S.regWeight t x| ≤ |C₁| + |S.R.Clog| * Real.log (S.R.r x) ∧ S.regWeight t x ≤ |C₁| := by
    filter_upwards [hC₁] with t ht
    refine ⟨ht.1, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := ht.2 x hx
    have h3 := S.R.ph_ge x hx
    have h4 : -(|S.R.Clog| * Real.log (S.R.r x)) ≤ -S.R.Clog * Real.log (S.R.r x) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self S.R.Clog) (hlogr x hx)
      linarith
    have h5 : C₁ ≤ |C₁| := le_abs_self _
    have h6 : 0 ≤ |S.R.Clog| * Real.log (S.R.r x) := mul_nonneg (abs_nonneg _) (hlogr x hx)
    have h7 : 0 ≤ |C₁| := abs_nonneg _
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, by linarith⟩
  set G : M.Xc → ℝ := S.R.Yo.indicator fun x => κ x - S.R.ph x with hG
  set GT : ℝ → M.Xc → ℝ := fun t x => κ x - S.regWeight t x with hGT
  have hconv : ∀ i : ℕ, MIntegrable M.atlas (positionPot S.R.th Pn S.R.ph i) G ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t)) ∧
      Tendsto (fun t => mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t)) (𝓝[>] 0)
        (𝓝 (mInt M.atlas (positionPot S.R.th Pn S.R.ph i) G)) := by
    intro i
    refine GlobalTheory.T.mixed_integral_tendsto_off_divisor D.n M.Xc M.atlas S.R Θ hΘ hΘp
      (fun j : Fin D.n => if (j : ℕ) < i then S.R.th else Pn)
      (fun j : Fin D.n => if (j : ℕ) < i then S.R.ph else fun _ => 0)
      (fun (j : Fin D.n) t => if (j : ℕ) < i then S.regWeight t else fun _ => 0) G GT Cc
      ?_ ?_ ?_ ?_ ?_ ?_
    · intro j
      by_cases h : (j : ℕ) < i
      · simpa [h] using S.R.th_pot
      · simpa [h] using hPn
    · intro j
      by_cases h : (j : ℕ) < i
      · simpa [h] using hph
      · simp only [h, if_false]
        intro j'
        exact contDiffOn_const
    · have h1 := hpsh 1 one_pos
      filter_upwards [hbd, h1] with t ht ht1 j
      by_cases h : (j : ℕ) < i
      · simp only [h, if_true]
        refine ⟨ht.1, ?_, fun x hx => ?_⟩
        · have : Θ.rsmul 1 = Θ := by
            cases Θ
            simp [LocPot.rsmul]
          rwa [this] at ht1
        · obtain ⟨h2, h3⟩ := ht.2 x hx
          have hL := hlogr x hx
          have h4 : |S.R.Clog| * Real.log (S.R.r x) ≤ Cc * Real.log (S.R.r x) :=
            mul_le_mul_of_nonneg_right (by rw [hCc]; linarith [abs_nonneg C₁, abs_nonneg Bκ]) hL
          have h5 : |C₁| ≤ Cc := by rw [hCc]; linarith [abs_nonneg S.R.Clog, abs_nonneg Bκ]
          exact ⟨by linarith, by linarith⟩
      · simp only [h, if_false]
        refine ⟨fun j' => contDiffOn_const, hΘN, fun x hx => ?_⟩
        have hL := hlogr x hx
        have := mul_nonneg hCc0 hL
        simp only [abs_zero]
        exact ⟨by linarith, hCc0⟩
    · intro j k K' hK' hK'c
      by_cases h : (j : ℕ) < i
      · simp only [h, if_true]
        exact GlobalTheory.T.regularized_weight_tendsto_C2 K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S hS k K' hK' hK'c
      · simp only [h, if_false]
        exact ⟨tuo_const _ _ _, tuo_const _ _ _, tuo_const _ _ _⟩
    · filter_upwards [hbd] with t ht
      refine ⟨?_, fun x hx => ?_⟩
      · letI : MeasurableSpace M.Xc := borel M.Xc
        haveI : BorelSpace M.Xc := ⟨rfl⟩
        have hc : Continuous (GT t) := hκc.sub (GlobalTheory.T.smooth_on_atlas_continuous D.n M.Xc M.atlas _ ht.1)
        exact hc.measurable.indicator hYo.measurableSet
      · obtain ⟨h2, -⟩ := ht.2 x hx
        have hL := hlogr x hx
        have h4 : |S.R.Clog| * Real.log (S.R.r x) ≤ Cc * Real.log (S.R.r x) :=
          mul_le_mul_of_nonneg_right (by rw [hCc]; linarith [abs_nonneg C₁, abs_nonneg Bκ]) hL
        have h5 : |C₁| + |κ x| ≤ Cc := by
          have := hBκ x
          have h6 := le_abs_self Bκ
          rw [hCc]; linarith [abs_nonneg S.R.Clog]
        have h7 : |GT t x| ≤ |κ x| + |S.regWeight t x| := abs_sub _ _
        linarith
    · intro K' hK' hK'c
      have hu := GlobalTheory.T.regularized_weight_tendsto_uniformly K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S hS K' hK' hK'c
      have hu2 : TendstoUniformlyOn GT (fun x => κ x - S.R.ph x) (𝓝[>] 0) K' := by
        rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
        intro ε hε
        filter_upwards [hu ε hε] with t ht x hx
        have := ht x hx
        simp only [hGT, Real.dist_eq] at this ⊢
        rwa [show κ x - S.R.ph x - (κ x - S.regWeight t x) = -(S.R.ph x - S.regWeight t x) by ring, abs_neg]
      exact hu2.congr_right fun x hx => by simp [hG, Set.indicator_of_mem (hK' hx)]

  have hmeasT : ∀ t, M.atlas.Smooth (S.regWeight t) → ∀ j, AEStronglyMeasurable (GT t ∘ (M.atlas.chart j).symm)
      (volume.restrict (M.atlas.chart j).target) := by
    intro t ht j
    have hc : Continuous (GT t) := hκc.sub (GlobalTheory.T.smooth_on_atlas_continuous D.n M.Xc M.atlas _ ht)
    exact (hc.comp_continuousOn (M.atlas.chart j).continuousOn_symm).aestronglyMeasurable
      (M.atlas.chart j).open_target.measurableSet
  have hmeasG : ∀ j, AEStronglyMeasurable (G ∘ (M.atlas.chart j).symm)
      (volume.restrict (M.atlas.chart j).target) := by
    intro j
    set V : Set (Fin D.n → ℂ) := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo with hV
    have hVo : IsOpen V := (M.atlas.chart j).continuousOn_symm.isOpen_inter_preimage
      (M.atlas.chart j).open_target hYo
    have hF : ContinuousOn (fun y => κ ((M.atlas.chart j).symm y) - S.R.ph ((M.atlas.chart j).symm y)) V := by
      refine ContinuousOn.sub ?_ (hph j).continuousOn
      exact hκc.comp_continuousOn ((M.atlas.chart j).continuousOn_symm.mono Set.inter_subset_left)
    have h1 : AEStronglyMeasurable (V.indicator fun y => κ ((M.atlas.chart j).symm y) -
        S.R.ph ((M.atlas.chart j).symm y)) volume :=
      (aestronglyMeasurable_indicator_iff hVo.measurableSet).2 (hF.aestronglyMeasurable hVo.measurableSet)
    refine (h1.mono_measure Measure.restrict_le_self).congr ?_
    refine (ae_restrict_iff' (M.atlas.chart j).open_target.measurableSet).2 (Filter.Eventually.of_forall fun y hy => ?_)
    by_cases hyY : (M.atlas.chart j).symm y ∈ S.R.Yo
    · have hyV : y ∈ V := ⟨hy, hyY⟩
      simp [hG, Set.indicator_of_mem hyY, Set.indicator_of_mem hyV]
    · have hyV : y ∉ V := fun h => hyY h.2
      simp [hG, Set.indicator_of_notMem hyY, Set.indicator_of_notMem hyV]

  have hwl : ∀ i, ptsIntegral (mCoordIdeal D.y)
      (pot fun j : Fin D.n => if (j : ℕ) < i then muVert Hd B else Nb)
      (fun z => Real.log (Nb.h z) - Real.log ((muVert Hd B).h z)) =
      mInt M.atlas (positionPot S.R.th Pn S.R.ph i) G := by
    intro i
    refine GlobalTheory.T.regularized_hodge_height_limit K J II Ψ Ω W D Hd M S B Nb (muVert Hd B) Pn i S.R.ph G _ hPn hPnS hph ?_ ?_ hmeasG (hconv i).1
    · intro z hz hY
      have h1 := S.ph_eq z ⟨mem_Xo_of_proj_mem S hz hY, hz⟩ hY
      rw [GlobalTheory.T.vertical_hodge_metric_log_formula K J II Ψ Ω W D Hd B z hz, h1]
      ring
    · intro z hz hY
      have h1 := S.ph_eq z ⟨mem_Xo_of_proj_mem S hz hY, hz⟩ hY
      have h2 := GlobalTheory.T.vertical_hodge_metric_log_formula K J II Ψ Ω W D Hd B z hz
      have h3 := hκ z hz
      simp only [hG, Set.indicator_of_mem hY]
      rw [h1, h2, h3]
      ring
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) - ∑ i ∈ Finset.range (D.n + 1),
        mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t) = arLimFun Hd S B t := by
    have hint : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.range (D.n + 1),
        MIntegrable M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t) :=
      (Filter.eventually_all_finset _).2 fun i _ => (hconv i).2.1
    filter_upwards [GlobalTheory.T.regularized_hodge_metric_smooth K J II Ψ Ω W D Hd M S B hS, hbd, hint] with t hsp hb hi
    obtain ⟨hsm, hdeg, hlog⟩ := hsp
    have hT := GlobalTheory.T.intersection_number_metric_change hLoc K J II (mCoordIdeal D.y) D.n Nb (muReg Hd S B t) hII D.arith hNb hsm
      (hdeg.trans hNa.symm)
    rw [arLimFun, hT]
    congr 1
    refine Finset.sum_congr rfl fun i hi' => ?_
    refine (GlobalTheory.T.regularized_hodge_height_limit K J II Ψ Ω W D Hd M S B Nb (muReg Hd S B t) Pn i (S.regWeight t) (GT t) _ hPn hPnS
      (fun j => (hb.1 j).mono fun y hy => ⟨hy.1, Set.mem_univ _⟩) ?_ ?_ (hmeasT t hb.1) (hi i hi')).symm
    · intro z hz _
      exact hlog z hz
    · intro z hz _
      simp only [hGT]
      rw [hlog z hz, hκ z hz]
      ring
  have hlim : Tendsto (fun t => II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) -
      ∑ i ∈ Finset.range (D.n + 1), mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t))
      (𝓝[>] 0) (𝓝 (limTop Hd B Nb)) := by
    rw [limTop]
    simp only [hwl]
    exact tendsto_const_nhds.sub (tendsto_finset_sum _ fun i _ => (hconv i).2.2)
  exact hlim.congr' hev

theorem arLim_exists_eq : Top.Given → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M M' : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (S₁ : LogLogRegularisationSetting M' D.Xo (muLine Hd)) (B : ℕ), IsFullIntersectionSystem II → S.IsTied → S₁.IsTied → ArLimExists Hd S B ∧ arLim Hd S B = arLim Hd S₁ B := by
  intro hG _ K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M M' S S₁ B hII hS hS₁
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hNb : IsSmoothHerm (fsHerm J (muTwDeg Hd B)) := PB.StepW.fsHerm_isSmoothHerm K J _
  have h1 := tendsto_arLimFun hIn.metricLocal S hS B hII _ hNb rfl
  have h2 := tendsto_arLimFun hIn.metricLocal S₁ hS₁ B hII _ hNb rfl
  exact ⟨⟨_, h1⟩, by rw [arLim, arLim, h1.limUnder_eq, h2.limUnder_eq]⟩

end Main
end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeStabilizerEquivAutomorphismsStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stabilizer_equiv_automorphisms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), ∃ α : latticeStab C.h C.e.range ≃* autGrp (E := E) F.form, ∀ γ x, C.e ((α γ).1 x) = ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.exists_alpha | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.exists_alpha | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.exists_alpha <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentOfGramDetUnit
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem linearIndependent_of_isUnit_gram_det :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
      [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (d : Fin m → Fin g → ℂ),
      IsUnit (R.gram d).det → LinearIndependent ℂ d := by
  intro E _ _ _ g Λ _ _ R m d hdet
  rw [Fintype.linearIndependent_iff]
  intro x hx
  have hmul : (R.gram d) *ᵥ x = 0 := by
    funext a
    have hsum : (∑ b, x b • d b) ⬝ᵥ (R.Hm *ᵥ star (d a)) = 0 := by
      rw [hx, zero_dotProduct]
    rw [sum_dotProduct] at hsum
    simp only [smul_dotProduct, smul_eq_mul] at hsum
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hsum ⊢
    rw [← hsum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mulVec, dotProduct]
    rw [mul_comm]
  have hx0 : x = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet.ne_zero hmul
  intro i
  rw [hx0, Pi.zero_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetChange
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.PointLog

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem gram_change (R : RiemLat E g Λ) {m : ℕ} (bb d : Fin m → Fin g → ℂ) (Y : Matrix (Fin m) (Fin m) ℂ)
    (hd : ∀ b, d b = ∑ c, Y c b • bb c) : R.gram d = Yᴴ * R.gram bb * Y := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RiemLat.gram, Matrix.of_apply, RiemLat.ip, hd,
    star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem log_det_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (bb d : Fin m → Fin g → ℂ) (Y M : Matrix (Fin m) (Fin m) ℂ) (κ : ℝ), 0 < κ → (∀ b, d b = ∑ c, Y c b • bb c) → R.gram d * M = (κ : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) → M.PosDef → Y.det ≠ 0 ∧ -Real.log M.det.re = 2 * Real.log ‖Y.det‖ + Real.log (R.gram bb).det.re - m * Real.log κ := by
  intro E _ _ _ g Λ _ _ R m bb d Y M κ hκ hd hM hpos
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, gram_change R bb d Y hd, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hMp : 0 < M.det := hpos.det_pos
  obtain ⟨hr, hi⟩ := Complex.pos_iff.mp hMp
  set r := M.det.re with hrdef
  have hMr : M.det = (r : ℂ) := by
    apply Complex.ext <;> simp [hrdef, ← hi]
  set y := Y.det with hy
  set G := (R.gram bb).det with hG
  have hyy : star y * y = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.conj_mul' y
  have hκm : 0 < κ ^ m := pow_pos hκ m
  have e1 : ((‖y‖ ^ 2 : ℝ) : ℂ) * G * (r : ℂ) = ((κ ^ m : ℝ) : ℂ) := by
    rw [← hyy, ← hMr]
    push_cast
    linear_combination hdet
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at e1
    have : ((κ ^ m : ℝ) : ℂ) = 0 := by simpa using e1.symm
    exact hκm.ne' (by exact_mod_cast this)
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hGr : G = ((κ ^ m / (‖y‖ ^ 2 * r) : ℝ) : ℂ) := by
    have h2 : ((‖y‖ ^ 2 * r : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (pow_pos hn 2) hr).ne'
    push_cast at h2 e1 ⊢
    field_simp
    linear_combination e1
  refine ⟨hy0, ?_⟩
  rw [hGr, Complex.ofReal_re, Real.log_div hκm.ne' (mul_pos (pow_pos hn 2) hr).ne',
    Real.log_mul (pow_pos hn 2).ne' hr.ne', Real.log_pow, Real.log_pow]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.PointLog
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEqBallPotentialStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_eq_ball_potential : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (R : RiemLat E g Λ), t ∈ ballDom q → R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ → R.logDet (fun τ (i : Fin j') => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = ballPot q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormSqEqAdaptedFrameSumStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_eq_adapted_frame_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), R.form = F.form → C.IsAdapted R A → ∀ x, R.normSq x = 2 * C.c * ∑ τ, (star (C.cinv (A τ) τ *ᵥ C.vec x τ) ⬝ᵥ (C.cinv (A τ) τ *ᵥ C.vec x τ)).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen.normSq_adapted | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen.normSq_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen.normSq_adapted <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodExtensionImaginaryForm
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.im_perExt_eq_Fm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ), R.form = F.form → ∀ y y', (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im = C.Fm y y' := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R hR y y'
  exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen.form_ext C R hR y y'
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatementStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationality_of_resolution_statement : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK | exact GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealBasisFromLatticeBasisStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_basis_from_lattice_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g N : ℕ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → g = Fintype.card Ψ * N → ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin N → E)), (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ lam : Module.Basis (Fin (2 * g)) ℤ Λ, ∃ bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin N → ℂ), ∀ k τ i, bas k τ i = embOf (σ τ) (e (lam k) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.exists_realBasis_of_latBasis | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.exists_realBasis_of_latBasis | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.exists_realBasis_of_latBasis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetCoverOfArithmeticVarietyStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheet_cover_of_arithmetic_variety : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n nc : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : Fin nc → GroundTheory.Heights₂.Heights.LowerBoundFree.SncChart P n Bd) (V B : ℕ → Set (Fin n → ℂ)) (γ : ℕ → (Fin n → ℂ) → (Σ k, J k) → ℂ) (A : HermLine J) (G : ((Σ k, J k) → ℂ) → ℝ), IsArithVar P (n + 1) → (∀ z ∈ mcPts P, ∃ a, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ z ∈ torusSat {(χ a).γ t}) → IsSheetCover χ V B γ → (∀ m, ContDiffOn ℝ 2 (fun t => Real.log (A.h (γ m t))) (V m)) → (∀ w ∈ mcPts P \ Bd, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, IntegrableOn (fun t => G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t) (B m)) → Summable (fun m => ∫ t in B m, |G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t|) → ptsIntegral (e := n) P (fun _ z => Real.log (A.h z)) G = ∑' m, ∫ t in B m, G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets | exact GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelNormalFormOfHermitianStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_normal_form_of_hermitian : ∀ {I : Type} [Fintype I] [DecidableEq I] (L : (I → ℂ) →ₗ[ℝ] (I → ℂ)) (H : Matrix I I ℂ), H.IsHermitian → (∀ z : I → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H *ᵥ star z).re) → (∀ z w : I → ℂ, (L z ⬝ᵥ H *ᵥ star (L w)).im = (z ⬝ᵥ star w).im) → ∃ (A : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)) (Z : Matrix I I ℂ), Zᵀ = Z ∧ (1 - Zᴴ * Z).PosDef ∧ ∀ z, L z = A (tz Z z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformCommutesActionStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_transform_commutes_action : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ a x, tz (bigZe e q t) (B a x) = B a (tz (bigZe e q t) x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm <;> assumption)
end

