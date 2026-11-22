import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0032
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0099
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartLeviThGe
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ChartFun
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricFormula
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

private theorem hermOfFun_h_eq_of_homogeneous_of_pos {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hF : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    (hpos : 0 < F z) : (hermOfFun ι a F).h z = F z := by
  have h0 : (torusSetoid (ι := ι)).r (orbitRep z) z := Quotient.mk_out (s := torusSetoid) z
  obtain ⟨c, hc, hcz⟩ := h0
  have ho : orbitRep z = torusSmul (fun k => (c k)⁻¹) z := by
    funext p
    conv_rhs => rw [hcz]
    simp only [torusSmul]
    rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]
  have hc' : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have hpc : 0 < ∏ k, ‖(c k)⁻¹‖ ^ a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc' k)) _
  have hr := refNorm_pos a hz
  show refNorm a z * Real.exp (Real.log (F (orbitRep z) / refNorm a (orbitRep z))) = F z
  rw [ho, hF _ hc', refNorm_smul, mul_div_mul_left _ _ hpc.ne', Real.exp_log (div_pos hpos hr)]
  field_simp

private theorem smoothRep_h_eq_of_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (A : HermLine ι) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) :
    (smoothRep P A).h z = A.h z := by
  unfold smoothRep
  split_ifs with h
  · exact h.choose_spec.2.2 z hz
  · rfl

private theorem eval_torusSmul_map_eq_eval_mConeMap {K : Type} {ι : K → Type} (c : K → ℂ) (z : (Σ k, ι k) → ℂ)
    (f : MRing ι) :
    eval (torusSmul c z) (map (Int.castRingHom ℂ) f) = MvPolynomial.eval c (mConeMap z f) := by
  have h : (eval (torusSmul c z)).comp (map (Int.castRingHom ℂ)) =
      (MvPolynomial.eval c).comp (mConeMap z).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · intro q
      simp [mConeMap, torusSmul, mul_comm]
  exact RingHom.congr_fun h f

private theorem torusSmul_mem_mcPts_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    torusSmul c z ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hf' : f ∈ mCoordIdeal z := VertFactorPos.mCoordIdeal_le hz hf
    rw [eval_torusSmul_map_eq_eval_mConeMap, RingHom.mem_ker.1 hf', map_zero]

theorem muReg_h_eq_of_mem_mcPts : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ), ∀ z ∈ mcPts (mCoordIdeal D.y), (muReg X.H X.S B t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B t z hz
  have hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz.1
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D
  have hsm := VertFactorSmooth.proof VertFactorPos.proof II Ψ K ι Ω E D
  have hproj : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → X.M.proj (torusSmul c z) = X.M.proj z := fun c hc =>
    ((X.M.fibre z hz (torusSmul c z) (torusSmul_mem_mcPts_mCoordIdeal D.y hz hc)).2 ⟨c, hc, rfl⟩).symm
  have hreg : (X.S.regLine t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) := by
    refine hermOfFun_h_eq_of_homogeneous_of_pos (muLine X.H).a
      (fun w => X.S.ref.h w * Real.exp (X.S.regWeight t (X.M.proj w))) z hz' ?_
      (mul_pos (X.S.ref.pos z hz') (Real.exp_pos _))
    intro c hc
    show X.S.ref.h (torusSmul c z) * Real.exp (X.S.regWeight t (X.M.proj (torusSmul c z))) =
      (∏ k, ‖c k‖ ^ (muLine X.H).a k) * (X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)))
    have hs : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ (muLine X.H).a k) * X.S.ref.h z := by
      rw [← X.S.ref_deg]
      exact X.S.ref.smul c z hc
    rw [hproj c hc, hs, mul_assoc]
  rw [muReg, smoothRep_h_eq_of_mem_mcPts _ _ z hz]
  refine (hermOfFun_h_eq_of_homogeneous_of_pos (muTwDeg X.H B)
    (fun w => (X.S.regLine t).h w * ∏ p ∈ D.SB B, D.vertFactor p w) z hz' ?_ ?_).trans ?_
  · intro c hc
    show (X.S.regLine t).h (torusSmul c z) * ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
      (∏ k, ‖c k‖ ^ muTwDeg X.H B k) * ((X.S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z)
    have h1 : (X.S.regLine t).h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * (X.S.regLine t).h z :=
      (X.S.regLine t).smul c z hc
    have h2 : ∀ p ∈ D.SB B,
        D.vertFactor p (torusSmul c z) = (∏ k, ‖c k‖ ^ D.vdeg p k) * D.vertFactor p z :=
      fun p hp => (hsm p (Finset.mem_filter.1 hp).1).1 z hz c hc
    rw [h1, Finset.prod_congr rfl h2, Finset.prod_mul_distrib, muTwDeg,
      MuRegSmooth.prod_norm_zpow_add_sum hc]
    ring
  · exact mul_pos ((X.S.regLine t).pos z hz')
      (Finset.prod_pos fun p hp => hpos p (Finset.mem_filter.1 hp).1 z hz)
  · show (X.S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z = _
    rw [hreg]

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBounds
section
set_option maxSynthPendingDepth 1

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
open ReciprocityTheory.AnForm.M.PLAux (analyticAt_compat)

section Charts

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem analyticAt_transition (P : PotentialCharts A) (j : Fin A.n) (k : Fin P.N) {y : Fin D → ℂ}
    (hy : y ∈ (A.chart j).target) (hk : (A.chart j).symm y ∈ (P.chart k).source) :
    AnalyticAt ℂ (P.chart k ∘ (A.chart j).symm) y := by
  have h := analyticAt_compat (P.compat k) j ((A.chart j).map_target hy) hk
  rwa [(A.chart j).right_inv hy] at h

theorem levi_th_add_chart (P : PotentialCharts A) (f : X → ℝ) (x : X) (j : Fin A.n) (k : Fin P.N)
    {y : Fin D → ℂ} (w : Fin D → ℂ) (hy : y ∈ (A.chart j).target)
    (hθ : (A.chart j).symm y ∈ P.th.U x) (hk : (A.chart j).symm y ∈ (P.chart k).source)
    (hcf : ContDiffAt ℝ 2 (P.chartFun f k) (P.chart k ((A.chart j).symm y))) :
    ContDiffAt ℝ 2 ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y ∧
      levi ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y w =
        levi (P.chartFun f k) (P.chart k ((A.chart j).symm y))
          (fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w) := by
  have hg := analyticAt_transition P j k hy hk
  obtain ⟨W, hWo, hpW, G, hG, hEq⟩ := P.q_th k x _ ⟨hθ, hk⟩
  have hN : W ∩ P.th.U x ∩ (P.chart k).source ∈ 𝓝 ((A.chart j).symm y) :=
    ((hWo.inter (P.th.isOpen_U x)).inter (P.chart k).open_source).mem_nhds ⟨⟨hpW, hθ⟩, hk⟩
  have hev : (fun z => P.th.φ x z + f z) ∘ (A.chart j).symm =ᶠ[𝓝 y]
      fun y' => (P.chartFun f k ∘ (P.chart k ∘ (A.chart j).symm)) y' +
        (-1) * (G ((A.chart j).symm y')).re := by
    filter_upwards [((A.chart j).continuousAt_symm hy).preimage_mem_nhds hN] with y' hy'
    have h1 := hEq _ hy'
    simp only [Function.comp, PotentialCharts.chartFun, (P.chart k).left_inv hy'.2]
    linarith
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hpW⟩
  have hcf' : ContDiffAt ℝ 2 (P.chartFun f k) ((P.chart k ∘ (A.chart j).symm) y) := hcf
  have hcg : ContDiffAt ℝ 2 (P.chartFun f k ∘ (P.chart k ∘ (A.chart j).symm)) y :=
    hcf'.comp y ((hg.contDiffAt (n := 2)).restrict_scalars ℝ)
  have hre : ContDiffAt ℝ 2 (fun y' => (G ((A.chart j).symm y')).re) y := by
    have := (Complex.reCLM.contDiff (𝕜 := ℝ) (n := 2)).contDiffAt.comp y
      ((hGa.contDiffAt (n := 2)).restrict_scalars ℝ)
    simpa [Function.comp_def] using this
  have h0 : levi (fun y' => (G ((A.chart j).symm y')).re) y w = 0 := levi_re_analytic hGa w
  refine ⟨(hcg.add (contDiffAt_const.mul hre)).congr_of_eventuallyEq hev, ?_⟩
  rw [levi_congr hev w, levi_add_smul (-1) hcg hre w, h0, levi_comp w hg hcf']
  simp

theorem isPshOn_th_ph (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) :
    ReciprocityTheory.AnForm.P.IsPshOn A R.Yo (R.th + LocPot.ofFun R.ph) := by
  intro x j y hy w
  have hyt : y ∈ (A.chart j).target := hy.1
  have hθ : (A.chart j).symm y ∈ R.th.U x := hy.2.1.1
  have hY : (A.chart j).symm y ∈ R.Yo := hy.2.2
  obtain ⟨k, hk⟩ := R.cover ((A.chart j).symm y)
  have hks := R.toPotentialCharts.mid_subset_source k (R.inner_subset_mid k hk)
  have hξ : R.chart k ((A.chart j).symm y) ∈
      (R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k) :=
    ⟨(R.chart k).map_source hks, (R.mem_Yo k _ hks).1 hY⟩
  have hUo : IsOpen ((R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k)) :=
    (R.chart k).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have hC2 : ContDiffOn ℝ 2 (R.u k) ((R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k)) :=
    fun ξ hξ => (RegChartData.contDiffAt_u R k hξ).contDiffWithinAt
  have hL := ((ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm _ _ _ hUo hC2).1 (R.u_psh k)).2
  have hcf : ContDiffAt ℝ 2 (R.chartFun R.ph k) (R.chart k ((A.chart j).symm y)) :=
    RegChartData.contDiffAt_u R k hξ
  have h := (levi_th_add_chart R.toPotentialCharts R.ph x j k w hyt hθ hks hcf).2
  change 0 ≤ levi ((fun z => R.th.φ x z + R.ph z) ∘ (A.chart j).symm) y w
  rw [h]
  exact hL _ hξ _

theorem exists_isPsh_of_chart_bound [CompactSpace X] (P : PotentialCharts A) (Θ : LocPot X)
    (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) :
    ∃ c : Fin P.N → ℝ, (∀ k, 0 < c k) ∧ ∀ (f : X → ℝ) (a ε : ℝ), A.Smooth f → 0 ≤ ε →
      (∀ k : Fin P.N, ∀ x ∈ P.mid k, ∀ w : Fin D → ℂ,
        -a * ‖w‖ ^ 2 ≤ levi (P.chartFun f k) (P.chart k x) w) →
      (∀ k, a ≤ ε * c k) → IsPsh A (P.th + LocPot.ofFun f + Θ.rsmul ε) := by
  have hc : ∀ k : Fin P.N, ∃ c : ℝ, 0 < c ∧ ∀ p ∈ closure (P.mid k), ∀ x, p ∈ Θ.U x →
      ∀ v : Fin D → ℂ, c * ‖v‖ ^ 2 ≤ levi (Θ.φ x ∘ (P.chart k).symm) (P.chart k p) v := fun k =>
    exists_levi_lower hΘ hpos (P.compat k) isClosed_closure.isCompact (P.closure_mid k)
  choose c hc0 hc using hc
  refine ⟨c, hc0, fun f a ε hf hε hlev hac x j y hy w => ?_⟩
  have hyt : y ∈ (A.chart j).target := hy.1
  have hθ : (A.chart j).symm y ∈ P.th.U x := hy.2.1.1
  have hΘx : (A.chart j).symm y ∈ Θ.U x := hy.2.2
  have hpA : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hyt
  obtain ⟨k, hk⟩ := P.cover ((A.chart j).symm y)
  have hkm := P.inner_subset_mid k hk
  have hks := P.mid_subset_source k hkm
  have hcf : ContDiffAt ℝ 2 (P.chartFun f k) (P.chart k ((A.chart j).symm y)) := by
    have hq : ContDiffAt ℝ 2 (P.q k) (P.chart k ((A.chart j).symm y)) :=
      ((P.q_smooth k).contDiffAt ((P.chart k).open_target.mem_nhds
        ((P.chart k).map_source hks))).of_le (WithTop.coe_le_coe.2 le_top)
    exact hq.add (contDiffAt_comp_symm isOpen_univ hf (P.compat k) (Set.mem_univ _) hks)
  obtain ⟨hF, hFl⟩ := levi_th_add_chart P f x j k w hyt hθ hks hcf
  have hG : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y := by
    have := contDiffAt_comp_symm (Θ.isOpen_U x) (hΘ.1 x) (compat_chart A j) hΘx hpA
    rwa [(A.chart j).right_inv hyt] at this
  have hg := analyticAt_transition P j k hyt hks
  have hGl : levi (Θ.φ x ∘ (A.chart j).symm) y w =
      levi (Θ.φ x ∘ (P.chart k).symm) (P.chart k ((A.chart j).symm y))
        (fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w) := by
    have hev := eventuallyEq_comp_chart (Θ.φ x) (P.chart k) (A.chart j) hyt hks
    have hcd : ContDiffAt ℝ 2 (Θ.φ x ∘ (P.chart k).symm) ((P.chart k ∘ (A.chart j).symm) y) :=
      contDiffAt_comp_symm (Θ.isOpen_U x) (hΘ.1 x) (P.compat k) hΘx hks
    rw [levi_congr hev w, levi_comp w hg hcd]
    rfl
  change 0 ≤ levi (fun y' => ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y' +
    ε * (Θ.φ x ∘ (A.chart j).symm) y') y w
  rw [levi_add_smul ε hF hG w, hFl, hGl]
  set v := fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w
  have h1 := hlev k _ hkm v
  have h2 := hc k _ (subset_closure hkm) x hΘx v
  have h3 := mul_le_mul_of_nonneg_left h2 hε
  have h4 := mul_le_mul_of_nonneg_right (hac k) (sq_nonneg ‖v‖)
  nlinarith

end Charts

theorem tied_regularisation_weak : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B) (Θ : LocPot M.Xc), S.IsTied → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → ReciprocityTheory.AnForm.P.IsPshOn M.atlas S.R.Yo (S.R.th + LocPot.ofFun S.R.ph) ∧ (∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧ ∀ x ∈ S.R.Yo, S.R.ph x ≤ S.regWeight t x ∧ S.regWeight t x ≤ C) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsPsh M.atlas (S.R.th + LocPot.ofFun (S.regWeight t) + Θ.rsmul ε) := by
  intro K _ ι _ P n M Xo B S Θ hS hΘ hpos
  obtain ⟨C₀, t₀, ht₀, hb⟩ := GroundTheory.Heights₂.Heights.Regular.ChartMollifiedBounds.proof
    GroundTheory.Heights₂.Heights.Regular.TruncPsh.proof M.Xc n M.atlas S.R S.ρ
  refine ⟨isPshOn_th_ph S.R, ⟨C₀ + 1, ?_⟩, fun ε hε => ?_⟩
  · filter_upwards [S.eventually_chartLevi hS, self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀),
      hS.K_tendsto.eventually_ge_atTop 0,
      hS.e1_tendsto_zero.eventually (eventually_le_nhds one_pos)] with t hsm ht htt hK he
    have ht0 : (0 : ℝ) < t := ht
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    refine ⟨hsm.1, fun x hx => ⟨?_, ?_⟩⟩
    · obtain ⟨k, hk⟩ := S.R.cover x
      have hkm := S.R.inner_subset_mid k hk
      have h1 := ((hb t ht0 htt).2 (S.K t) hK k x hkm).2.2 hx
      have h2 := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.le_glue S.R.toPotentialCharts
        (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 hkm
      have h3 : S.regWeight t x = S.R.glue
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := rfl
      have hη := S.cutoff.eq_zero k x hk
      simp only [hη, mul_zero, add_zero] at h2
      rw [h3]
      linarith
    · have hg := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.glue_le S.R.toPotentialCharts
        (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 (c := C₀) (x := x)
        fun j hj => by
          have h1 := ((hb t ht0 htt).2 (S.K t) hK j x hj).2.1
          have h2 := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * S.e1 t)
            (S.cutoff.bounds j x hj).2
          show S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x ≤ C₀
          linarith
      have h3 : S.regWeight t x = S.R.glue
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := rfl
      rw [h3]
      linarith
  · obtain ⟨c, hc0, hc⟩ := exists_isPsh_of_chart_bound S.R.toPotentialCharts Θ hΘ hpos
    have hlim : Tendsto (fun t => 4 * S.Cη * S.e1 t) (𝓝[>] 0) (𝓝 0) := by
      simpa using hS.e1_tendsto_zero.const_mul (4 * S.Cη)
    have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, 4 * S.Cη * S.e1 t ≤ ε * c k :=
      Filter.eventually_all.2 fun k =>
        hlim.eventually (eventually_le_nhds (mul_pos hε (hc0 k)))
    filter_upwards [S.eventually_chartLevi hS, hall] with t ht hle
    exact hc (S.regWeight t) (4 * S.Cη * S.e1 t) ε ht.1 hε.le ht.2 hle

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightIdentity
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.OriginEps

open AlgebraicGeometry CategoryTheory

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem mem_adjoin_rat_of_regular {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x)
    {c : κ} (hc : x c ≠ 0) {f : Ω}
    (hf : ∀ p : Cpt ξ, InChart ξ x c p → (∀ r : ℕ, r.Prime → ¬ InFibre ξ r p) → f ∈ regAt ξ p) :
    f ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x c) := by
  classical
  set B := Algebra.adjoin ℚ (Set.range fun j => x j / x c) with hB
  have hle : ∀ a ∈ chartRing ℤ x c, a ∈ B := by
    intro a ha
    have h2 : chartRing ℤ x c ≤ B.restrictScalars ℤ := Algebra.adjoin_le Algebra.subset_adjoin
    exact h2 ha
  let I : Ideal (chartRing ℤ x c) :=
    { carrier := {a | (a : Ω) * f ∈ B}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : chartRing ℤ x c) : Ω) * f ∈ B
        rw [Subalgebra.coe_add, add_mul]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : chartRing ℤ x c) : Ω) * f ∈ B
        simp
      smul_mem' := fun a u hu => by
        show ((a • u : chartRing ℤ x c) : Ω) * f ∈ B
        rw [smul_eq_mul, Subalgebra.coe_mul, _root_.mul_assoc]
        exact mul_mem (hle _ a.2) hu }
  let T : Submonoid (chartRing ℤ x c) :=
    { carrier := {u | ∃ b : ℕ, b ≠ 0 ∧ (u : Ω) = b}
      one_mem' := ⟨1, one_ne_zero, by simp⟩
      mul_mem' := by
        rintro u v ⟨b, hb, hu⟩ ⟨b', hb', hv⟩
        exact ⟨b * b', mul_ne_zero hb hb', by rw [Subalgebra.coe_mul, hu, hv]; push_cast; rfl⟩ }
  by_contra hcon
  have hdisj : Disjoint (I : Set (chartRing ℤ x c)) (T : Set (chartRing ℤ x c)) := by
    rw [Set.disjoint_left]
    rintro u hu ⟨b, hb, hub⟩
    have hu' : (b : Ω) * f ∈ B := by rw [← hub]; exact hu
    apply hcon
    have h2 := B.smul_mem hu' ((b : ℚ)⁻¹)
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 hb
    have e : ((b : ℚ)⁻¹) • ((b : Ω) * f) = f := by
      rw [Algebra.smul_def, map_inv₀, map_natCast, ← _root_.mul_assoc, inv_mul_cancel₀ hb0, _root_.one_mul]
    rwa [e] at h2
  obtain ⟨P, hP, hIP, hPT⟩ := Ideal.exists_le_prime_disjoint I T hdisj
  obtain ⟨p, hp, hpP⟩ := TieVB.exists_point hT hc P hP
  have h0 : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p := by
    intro r hr hfib
    have hrT : (r : chartRing ℤ x c) ∈ T := ⟨r, hr.ne_zero, by simp⟩
    have hnot : (r : chartRing ℤ x c) ∉ P := fun h => Set.disjoint_left.1 hPT h hrT
    have hu := not_not.1 (mt (hpP (r : chartRing ℤ x c)).2 hnot)
    apply hfib
    simpa using hu
  obtain ⟨s, hsA, hsu, hsf⟩ := TieVB.exists_den hT hp (hf p hp h0)
  have hI : (⟨s, hsA⟩ : chartRing ℤ x c) ∈ I := hle _ hsf
  exact (hpP ⟨s, hsA⟩).1 (hIP hI) hsu

theorem adjoin_segre_le {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω} (c : (k : K) → ι k) :
    Algebra.adjoin ℚ (Set.range fun c' : (k : K) → ι k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) ≤
      Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨c', rfl⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ _
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩

theorem zpow_sum_of_ne {R : Type} {a : Ω} (ha : a ≠ 0) (s : Finset R) (f : R → ℤ) :
    a ^ (∑ r ∈ s, f r) = ∏ r ∈ s, a ^ f r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.prod_insert hr, zpow_add₀ ha, ih]

theorem eps_identity {K R : Type} [Fintype K] [Fintype R] {Y : K → Ω} (hY : ∀ k, Y k ≠ 0) (xd : R → K → ℤ)
    {e : R → Ω} (n : R → ℤ) (A : K → ℤ) (k₀ : K) (hA₀ : A k₀ = 1)
    (hA : ∀ k, k ≠ k₀ → A k = 0) (q : ℕ) (s : Ω) :
    (s * ∏ r, e r ^ n r) * ∏ k, Y k ^ (-(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k)) =
      s * Y k₀ ^ q / ∏ r, ((∏ k, Y k ^ xd r k) * e r) ^ (-n r) := by
  have h1 : ∀ k, Y k ^ (-(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k)) =
      (∏ r, (Y k ^ xd r k) ^ n r) * Y k ^ ((q : ℤ) * A k) := by
    intro k
    have e1 : -(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k) = ∑ r, xd r k * n r + (q : ℤ) * A k := by
      rw [neg_add, ← Finset.sum_neg_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun r _ => by ring
      · ring
    rw [e1, zpow_add₀ (hY k), zpow_sum_of_ne (hY k)]
    simp only [zpow_mul]
  have h2 : ∏ k, Y k ^ ((q : ℤ) * A k) = Y k₀ ^ q := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [hA k hk]; simp) (fun h => absurd (Finset.mem_univ _) h), hA₀]
    simp
  have h3 : ∏ r, ((∏ k, Y k ^ xd r k) * e r) ^ (-n r) =
      ((∏ k, ∏ r, (Y k ^ xd r k) ^ n r) * ∏ r, e r ^ n r)⁻¹ := by
    simp only [zpow_neg, Finset.prod_inv_distrib]
    congr 1
    simp only [mul_zpow, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun r _ => (Finset.prod_zpow _ _ _).symm
  simp only [h1, Finset.prod_mul_distrib]
  rw [h2, h3, div_inv_eq_mul]
  ring

end General

theorem section_on_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → ∃ (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ j, (n₀ j : ℝ) = (Fx.kA * Fx.q' : ℕ) * RM.coef nu (-1) j) ∧ 0 < N₀ ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ∈ chartLatNm RM.y (combLine (RM.line 1) n₀).a 1 := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx o nu hn
  classical
  haveI : CharZero c.F := inferInstance
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom o.𝔐.cst.injective
  have hkA : (RM.kA : ℝ) = Fx.kA := by exact_mod_cast o.kA_eq
  have hkpos : (0 : ℝ) < Fx.kA := by rw [← hkA]; exact_mod_cast RM.kA_pos
  let n₀ : Option (RootIx D) → ℤ := fun j => j.elim (-(Fx.q' : ℤ)) fun r => -Fx.n r
  have hs0 : o.g Fx.sE * ∏ r, o.e r ^ Fx.n r ≠ 0 :=
    mul_ne_zero ((map_ne_zero o.g).2 Fx.sE_ne)
      (Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (o.lines r).1)
  have ha : ∀ k, (combLine (RM.line 1) n₀).a k =
      ∑ r, (-Fx.n r) * RM.xdeg r k + (-(Fx.q' : ℤ)) * RM.A.a k := by
    intro k
    show (∑ j, n₀ j • (RM.line 1 j).a) k = _
    rw [Finset.sum_apply, Fintype.sum_option, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun r _ => ?_
      simp [n₀, RootModel.line, RM.x_deg]
  have key : ∀ c' : ∀ k, RM.ι k, (∀ k, RM.y ⟨k, c' k⟩ ≠ 0) →
      IsIntegral (Algebra.adjoin ℚ (Set.range fun p : Σ k, RM.ι k => RM.y p / RM.y ⟨p.1, c' p.1⟩))
        ((o.g Fx.sE * ∏ r, o.e r ^ Fx.n r) * ∏ k, RM.y ⟨k, c' k⟩ ^ (-((combLine (RM.line 1) n₀).a k))) := by
    intro c' hc'
    have hx : (∏ k, RM.y ⟨k, c' k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc' k
    have ya : o.g (Fx.yf (o.ix.symm (c' o.k₀))) = RM.y ⟨o.k₀, c' o.k₀⟩ := by
      rw [← o.y_eq, Equiv.apply_symm_apply]
    have hfeq : (o.g Fx.sE * ∏ r, o.e r ^ Fx.n r) * ∏ k, RM.y ⟨k, c' k⟩ ^ (-((combLine (RM.line 1) n₀).a k)) =
        o.g Fx.sE * o.g (Fx.yf (o.ix.symm (c' o.k₀))) ^ Fx.q' /
          ∏ r, ((∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) ^ (-Fx.n r) := by
      simp only [ha]
      rw [ya]
      exact eps_identity hc' RM.xdeg Fx.n RM.A.a o.k₀ o.A_deg.1 o.A_deg.2 Fx.q' _
    have hreg : ∀ p : Cpt o.𝔐.ξ, InChart o.𝔐.ξ (fun c'' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c'' k⟩) c' p →
        (∀ r : ℕ, r.Prime → ¬ InFibre o.𝔐.ξ r p) →
        o.g Fx.sE * o.g (Fx.yf (o.ix.symm (c' o.k₀))) ^ Fx.q' /
          ∏ r, ((∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) ^ (-Fx.n r) ∈ regAt o.𝔐.ξ p := by
      intro p hp hp0
      have hch : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) (o.ix.symm (c' o.k₀)) p := by
        refine ⟨?_, fun j => ?_⟩
        · show o.g (Fx.yf (o.ix.symm (c' o.k₀))) ≠ 0
          rw [ya]; exact hc' _
        · show o.g (Fx.yf j) / o.g (Fx.yf (o.ix.symm (c' o.k₀))) ∈ _
          rw [ya, ← o.y_eq]
          exact Lat.block_ratio_mem hp o.k₀ (o.ix j)
      have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (Λ := o.Fl.rootLat) (fun r => -Fx.n r) (p := p)
        (s := fun r => (∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) fun r =>
          ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc' k)) (o.lines r).1,
            (o.lines r).2 _ trivial c' hp⟩
      exact (o.eff p hp0 _ _ hch ht).1
    have hB := adjoin_segre_le c' (mem_adjoin_rat_of_regular o.𝔐.tie hx hreg)
    rw [hfeq]
    exact isIntegral_algebraMap (x := (⟨_, hB⟩ : Algebra.adjoin ℚ
      (Set.range fun p : Σ k, RM.ι k => RM.y p / RM.y ⟨p.1, c' p.1⟩)))
  obtain ⟨N₀, hN, hmem⟩ := GlobalTheory.T.integral_section_lattice_multiple RM.K RM.ι RM.Ω RM.y 0 (combLine (RM.line 1) n₀).a _ key
  refine ⟨n₀, N₀, ?_, hN, ?_, ?_⟩
  · intro j
    cases j with
    | none =>
      show ((-(Fx.q' : ℤ) : ℤ) : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-1 / (RM.kA : ℝ))
      rw [hkA]
      push_cast
      field_simp
    | some r =>
      show ((-Fx.n r : ℤ) : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-nu r.1 r.2)
      push_cast
      rw [hn r]
      push_cast
      ring
  · rw [_root_.mul_assoc]
    exact mul_ne_zero (Nat.cast_ne_zero.2 hN.ne') hs0
  · rw [_root_.mul_assoc]
    exact hmem

end GlobalTheory.CompanionTheory.Ar.Small.OriginEps
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnAtlasContinuous
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.AtlasSmooth

theorem continuous_of_atlas_smooth :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X) (f : X → ℝ),
      A.Smooth f → Continuous f :=
  fun _ _ _ A _ hf => ReciprocityTheory.AnForm.M.st_smooth_continuous A hf

end GlobalTheory.CompanionTheory.Ar.AtlasSmooth
end

