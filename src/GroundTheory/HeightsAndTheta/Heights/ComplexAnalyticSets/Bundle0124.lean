import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ProjectiveLineZeroFormHolds
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContDiffOfContDiffOnZeroOff
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0097
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0120
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0105
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0121

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolydiscLelongLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace PolydiscLelongLimit

theorem hypIncl_mem_ball {d : ℕ} {r : ℝ} (w : Fin d → ℂ) :
    hypIncl w ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r ↔ w ∈ Metric.ball 0 r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [Metric.ball_eq_empty.2 hr]
  · simp only [mem_ball_zero_iff, pi_norm_lt_iff hr, Fin.forall_fin_succ, hypIncl, Fin.cons_zero,
      Fin.cons_succ, norm_zero, hr, true_and]

theorem extend_by_zero {D : ℕ} {r ρ : ℝ} {χ : (Fin D → ℂ) → ℝ} (hρ : ρ < r)
    (hχ : ContDiffOn ℝ ∞ χ (Metric.ball 0 r))
    (hsupp : ∀ τ ∈ Metric.ball (0 : Fin D → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) :
    ContDiff ℝ ∞ ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      HasCompactSupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      tsupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ⊆ Metric.closedBall 0 ρ ∧
      Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) := by
  have h0 : ∀ τ ∉ Metric.closedBall (0 : Fin D → ℂ) ρ,
      (Metric.ball (0 : Fin D → ℂ) r).indicator χ τ = 0 := by
    intro τ hτ
    by_cases hU : τ ∈ Metric.ball (0 : Fin D → ℂ) r
    · rw [Set.indicator_of_mem hU]
      by_contra h
      exact hτ (Metric.ball_subset_closedBall (hsupp τ hU h))
    · exact Set.indicator_of_notMem hU _
  have heq : Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) :=
    fun τ hτ => Set.indicator_of_mem hτ _
  exact ⟨contDiff_of_contDiffOn_zero_off Metric.isOpen_ball Metric.isClosed_closedBall
    (Metric.closedBall_subset_ball hρ) (hχ.congr heq) h0,
    HasCompactSupport.intro (isCompact_closedBall 0 ρ) h0,
    closure_minimal (fun τ hτ => by_contra fun h => (Function.mem_support.1 hτ) (h0 τ h))
      Metric.isClosed_closedBall, heq⟩

theorem logReg_contDiffOn {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {F : (Fin D → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F U) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := by
  intro z hz
  have h1 : ContDiffAt ℝ ∞ F z :=
    ((ReciprocityTheory.AnForm.Osgood.osgood D U F hU hF z hz).contDiffAt (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun τ => ‖F τ‖ ^ 2 + ε) z := (h1.norm_sq ℝ).add contDiffAt_const
  exact ((h2.log (by positivity)).div_const 2).contDiffWithinAt

end PolydiscLelongLimit

open PolydiscLelongLimit in

theorem PolydiscLelongLimit.proof : PolydiscLelongLimit.Statement := by
  intro d m r ρ F χ ψ hρ hF hχ hsupp hψ
  obtain ⟨H, hHd, hH0, hFH⟩ := hF
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  obtain ⟨hv, hvc, hvt, hvχ⟩ := extend_by_zero hρ hχ hsupp
  set U : Set (Fin (d + 1) → ℂ) := Metric.ball 0 r with hUdef
  set v := U.indicator χ with hvdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hvU : tsupport v ⊆ U := hvt.trans (Metric.closedBall_subset_ball hρ)
  have hFd : DifferentiableOn ℂ F U :=
    (((differentiable_apply 0).pow m).differentiableOn.mul hHd).congr fun t ht => hFH t ht
  have hFne : ∀ τ ∈ U, τ 0 ≠ 0 → F τ ≠ 0 := fun τ hτ h0 => by
    rw [hFH τ hτ]; exact mul_ne_zero (pow_ne_zero _ h0) (hH0 τ hτ)
  have hdens0 : ∀ τ, τ ∉ tsupport v → densV v ψ τ = 0 := fun τ hτ => maDens_cons_eq_zero ψ hτ
  have hIon : ∀ f : (Fin (d + 1) → ℂ) → ℝ, IntegrableOn (fun z => f z * densV v ψ z) U →
      Integrable (fun z => f z * densV v ψ z) := fun f h =>
    (integrableOn_iff_integrable_of_support_subset fun z hz => by_contra fun h' =>
      (Function.mem_support.1 hz) (mul_eq_zero_of_right _ (hdens0 z fun h'' => h' (hvU h'')))).1 h

  have hgood : ∀ ε : ℝ, 0 < ε →
      Integrable (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ) ∧
      maInt (Matrix.vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ U =
        ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ := by
    intro ε hε
    have hP := parts_thm d ψ v (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U
      ⟨hU, (hv.of_le h3).contDiffOn, hvc, hvU, (logReg_contDiffOn hU hFd hε).of_le h3,
        fun k => (hψ k).of_le h3⟩
    refine ⟨hIon _ hP.2.1, ?_⟩
    calc maInt (Matrix.vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ U
        = maInt (Fin.cons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) v U := by
          unfold maInt
          exact setIntegral_congr_fun hU.measurableSet fun τ hτ => by
            simp only [hvχ hτ]; try rfl
      _ = maInt (Fin.cons v ψ) (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := hP.2.2.2.2.symm
      _ = ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ := by
          unfold maInt
          exact setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ =>
            mul_eq_zero_of_right _ (hdens0 τ fun h => hτ (hvU h))

  have hL0 := log_norm_integral_formula_unit d (m : ℤ) U v ψ H ⟨hU, hv.of_le h3, hvc, hvU, hψ⟩ hHd hH0
  have hlogF : (fun z => Real.log ‖F z‖ * densV v ψ z) =
      fun z => Real.log ‖z 0 ^ (m : ℤ) * H z‖ * densV v ψ z := by
    funext z
    by_cases hz : z ∈ U
    · rw [hFH z hz, zpow_natCast]
    · rw [hdens0 z fun h => hz (hvU h), mul_zero, mul_zero]
  have hint : Integrable (fun τ => Real.log ‖F τ‖ * densV v ψ τ) := by rw [hlogF]; exact hL0.1
  have hdensI : Integrable (densV v ψ) := by
    have hP1 := parts_thm d ψ v (fun _ => (1 : ℝ)) U
      ⟨hU, (hv.of_le h3).contDiffOn, hvc, hvU, contDiffOn_const, fun k => (hψ k).of_le h3⟩
    exact (hIon (fun _ => 1) hP1.2.1).congr (Eventually.of_forall fun z => one_mul _)
  obtain ⟨C, hC⟩ : ∃ C, ∀ τ ∈ tsupport v, ‖(1 / 2 : ℝ) * Real.log (‖F τ‖ ^ 2 + 1)‖ ≤ C :=
    hvc.isCompact.exists_bound_of_continuousOn fun τ hτ =>
      (continuousAt_const.mul ((((hFd.continuousOn.continuousAt (hU.mem_nhds (hvU hτ))).norm.pow 2).add
        continuousAt_const).log (by positivity : ‖F τ‖ ^ 2 + 1 ≠ 0))).continuousWithinAt

  have hlim : Tendsto (fun ε : ℝ => ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ) (𝓝[>] 0)
      (𝓝 (∫ τ, Real.log ‖F τ‖ * densV v ψ τ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ => |Real.log ‖F τ‖ * densV v ψ τ| + C * |densV v ψ τ|)
      (eventually_mem_nhdsWithin.mono fun ε hε => (hgood ε hε).1.aestronglyMeasurable) ?_
      (hint.abs.add (hdensI.abs.const_mul C)) ?_
    · filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε
      filter_upwards [ae_coord_ne_zero (0 : Fin (d + 1))] with τ hτ0
      by_cases hτ : τ ∈ tsupport v
      · have h1 := gReg_abs_le hε.1 hε.2 (hFne τ (hvU hτ) hτ0)
        have h2 := hC τ hτ
        rw [Real.norm_eq_abs] at h2
        have e : Real.log (‖F τ‖ ^ 2 + ε) / 2 = gReg ε (F τ) := by unfold gReg; ring
        have h4 : |gReg ε (F τ)| ≤ |Real.log ‖F τ‖| + C :=
          h1.trans (by linarith [le_abs_self ((1 / 2 : ℝ) * Real.log (‖F τ‖ ^ 2 + 1))])
        rw [Real.norm_eq_abs, abs_mul, abs_mul, e]
        calc |gReg ε (F τ)| * |densV v ψ τ| ≤ (|Real.log ‖F τ‖| + C) * |densV v ψ τ| :=
              mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
          _ = _ := by ring
      · rw [hdens0 τ hτ]; simp
    · filter_upwards [ae_coord_ne_zero (0 : Fin (d + 1))] with τ hτ0
      by_cases hτ : τ ∈ U
      · have hpos : 0 < ‖F τ‖ ^ 2 := pow_pos (norm_pos_iff.2 (hFne τ hτ hτ0)) 2
        have hc : Tendsto (fun ε : ℝ => ‖F τ‖ ^ 2 + ε) (𝓝[>] 0) (𝓝 (‖F τ‖ ^ 2 + 0)) :=
          (tendsto_const_nhds.add tendsto_id).mono_left nhdsWithin_le_nhds
        rw [add_zero] at hc
        have e : Real.log ‖F τ‖ = Real.log (‖F τ‖ ^ 2) / 2 := by rw [Real.log_pow]; push_cast; ring
        rw [e]
        exact (((Real.continuousAt_log hpos.ne').tendsto.comp hc).div_const 2).mul_const _
      · rw [hdens0 τ fun h => hτ (hvU h)]
        simp only [mul_zero]
        exact tendsto_const_nhds

  have hR : ∫ w in Metric.ball (0 : Fin d → ℂ) r, χ (hypIncl w) * densHyp ψ w =
      ∫ w, v (hypIncl w) * densHyp ψ w := by
    rw [setIntegral_congr_fun (g := fun w => v (hypIncl w) * densHyp ψ w)
      Metric.isOpen_ball.measurableSet fun w hw => by
      simp only [hvχ ((hypIncl_mem_ball w).2 hw)]]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw =>
      mul_eq_zero_of_left (Set.indicator_of_notMem (mt (hypIncl_mem_ball w).1 hw) _) _
  have hlimF : ∫ τ, Real.log ‖F τ‖ * densV v ψ τ = (m : ℝ) * ∫ w, v (hypIncl w) * densHyp ψ w := by
    rw [hlogF, hL0.2, Int.cast_natCast]
  rw [hR, ← hlimF]
  exact hlim.congr' (eventually_mem_nhdsWithin.mono fun ε hε => (hgood ε hε).2.symm)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSameOrderBranchesMeet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable def VarBranch.restrictInto {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I k q) (ε : ℝ) (hε : 0 < ε)
    (h : ∀ t ∈ Metric.ball (0 : Fin k → ℂ) ε, c.toFun t ∈ zeroSet J) : VarBranch J k q where
  radius := min ε c.radius
  radius_pos := lt_min hε c.radius_pos
  toFun := c.toFun
  differentiableOn := c.differentiableOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  injOn := c.injOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  map_zero := c.map_zero
  mapsTo := fun t ht ↦ h t (Metric.ball_subset_ball (min_le_left _ _) ht)

theorem VarBranch.eventually_mem_zeroSet {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I 1 q) (h : ∀ f ∈ J, branchOrder c f = ⊤) :
    ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), c.toFun t ∈ zeroSet J := by
  have key : ∀ f ∈ J, ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), eval (c.toFun t) f = 0 := by
    intro f hf
    have h0 := analyticOrderAt_eq_top.1 (h f hf)
    have ht : Tendsto (fun t : Fin 1 → ℂ ↦ t 0) (𝓝 0) (𝓝 0) := (continuous_apply 0).tendsto' _ _ rfl
    filter_upwards [ht.eventually h0] with t ht
    have : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
    rwa [this] at ht
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian J : J.FG)
  filter_upwards [(s.eventually_all).2 fun g hg ↦ key g (hs ▸ Submodule.subset_span hg)] with t ht f hf
  have hle : Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) ≤ RingHom.ker (eval (c.toFun t)) :=
    Ideal.span_le.2 fun g hg ↦ ht g hg
  have hf' : f ∈ Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) := by
    rw [Ideal.span, hs]
    exact hf
  exact hle hf'

theorem SameOrderBranchesMeet.proof (hC : BranchInCurveComponent.Statement) (hO : SameOrdersLiftCentre.Statement)
    (hL : IndefiniteRowSideFullHecke.ComplexSets.BranchLift.Statement) : SameOrderBranchesMeet.Statement := by
  intro n I q c c' _ hdim hord
  obtain ⟨J, hJmin, hJdim, hev⟩ := hC n I q c hdim
  have hJ : J.IsPrime := hJmin.1.1
  have htop : ∀ f ∈ J, branchOrder c f = ⊤ := fun f hf ↦ by
    refine analyticOrderAt_eq_top.2 ?_
    have hι : Tendsto (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (𝓝 0) (𝓝 0) :=
      (continuous_pi fun _ ↦ continuous_id).tendsto' _ _ rfl
    filter_upwards [hι.eventually hev] with τ hτ using hτ f hf
  have hev' := c'.eventually_mem_zeroSet J fun f hf ↦ (hord f).symm.trans (htop f hf)
  obtain ⟨ε, hε, hεJ⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨ε', hε', hεJ'⟩ := Metric.eventually_nhds_iff_ball.1 hev'
  let γ := c.restrictInto J ε hε hεJ
  let γ' := c'.restrictInto J ε' hε' hεJ'
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨Γ, hΓd, hΓ, -⟩ := hL n 1 J q M γ hJ hJdim
  obtain ⟨Γ', hΓ'd, hΓ', hΓ'o⟩ := hL n 1 J q M γ' hJ hJdim
  have hw : Γ 0 = Γ' 0 := hO n J q M γ γ' Γ Γ' hJ hJdim hΓd hΓ hΓ'd hΓ' hord
  obtain ⟨U, hUo, hU⟩ := hΓ'o _ subset_rfl Metric.isOpen_ball
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball 0 γ.radius := Metric.mem_ball_self γ.radius_pos
  have hΓ0U : Γ 0 ∈ U := by
    rw [hw]
    exact (hU ▸ Set.mem_image_of_mem Γ' (Metric.mem_ball_self γ'.radius_pos)).2
  have hcont : ContinuousAt Γ 0 := hΓd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 γ.radius_pos)
  have hnear : ∀ᶠ τ in 𝓝[≠] (0 : Fin 1 → ℂ), τ ≠ 0 ∧ τ ∈ Metric.ball 0 γ.radius ∧ Γ τ ∈ U := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 γ.radius_pos),
      nhdsWithin_le_nhds (hcont.preimage_mem_nhds (hUo.mem_nhds hΓ0U))] with τ h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨τ, hτ0, hτ, hτU⟩ := hnear.exists
  obtain ⟨τ', hτ', hτ'eq⟩ : Γ τ ∈ Γ' '' Metric.ball 0 γ'.radius := hU ▸ ⟨(hΓ τ hτ).1, hτU⟩
  have hτc : τ ∈ Metric.ball 0 c.radius := Metric.ball_subset_ball (min_le_right _ _) hτ
  refine ⟨c.toFun τ, ⟨⟨τ, hτc, rfl⟩, ⟨τ', Metric.ball_subset_ball (min_le_right _ _) hτ', ?_⟩⟩, fun hq ↦ hτ0 ?_⟩
  · have e1 := (hΓ' τ' hτ').2
    have e2 := (hΓ τ hτ).2
    rw [hτ'eq] at e1
    exact e1.symm.trans e2
  · exact c.injOn hτc (Metric.mem_ball_self c.radius_pos) (hq.trans c.map_zero.symm)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSameOrdersLiftCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem eventually_const_mem_ball_one {r : ℝ} (hr : 0 < r) :
    ∀ᶠ τ in 𝓝 (0 : ℂ), (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
  have hc : Continuous (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) := continuous_pi fun _ ↦ continuous_id
  exact hc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (0 : Fin 1 → ℂ) hr)

theorem analyticAt_comp_const_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {φ : (Fin 1 → ℂ) → E} {r : ℝ} (hr : 0 < r) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 r)) :
    AnalyticAt ℂ (fun τ : ℂ ↦ φ (fun _ ↦ τ)) 0 := by
  have hc : Differentiable ℂ (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) :=
    differentiable_pi.2 fun _ ↦ differentiable_id
  exact DifferentiableOn.analyticAt (s := (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) ⁻¹' Metric.ball 0 r)
    (hφ.comp hc.differentiableOn fun _ h ↦ h) (eventually_const_mem_ball_one hr)

theorem analyticAt_eval_of_analyticAt_zero {n : ℕ} {F : ℂ → Fin n → ℂ} (hF : AnalyticAt ℂ F 0)
    (p : MvPolynomial (Fin n) ℂ) : AnalyticAt ℂ (fun τ ↦ eval (F τ) p) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (analyticAt_pi_iff.mp hF i)

theorem branchOrder_ne_top_of_not_mem (hB : BranchOffHypersurface.Statement) {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (γ : VarBranch J 1 q) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)) {b : MvPolynomial (Fin n) ℂ} (hb : b ∉ J) :
    branchOrder γ b ≠ ⊤ := by
  intro htop
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1 (analyticOrderAt_eq_top.1 htop)
  have hU : Metric.ball (0 : Fin 1 → ℂ) (min ε γ.radius) ⊆ Metric.ball 0 γ.radius :=
    Metric.ball_subset_ball (min_le_right _ _)
  obtain ⟨t, ht, hne⟩ := hB n 1 J b _ γ.toFun hJ hdim hb Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self (lt_min hε γ.radius_pos)⟩ (γ.differentiableOn.mono hU) (γ.injOn.mono hU)
    fun t ht ↦ γ.mapsTo (hU ht)
  have ht0 : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
  apply hne
  rw [← ht0]
  apply hεb
  rw [Metric.mem_ball, dist_zero_right] at ht ⊢
  exact lt_of_le_of_lt (norm_le_pi_norm t 0) (lt_of_lt_of_le ht (min_le_left _ _))

theorem SameOrdersLiftCentre.proof (hB : BranchOffHypersurface.Statement) : SameOrdersLiftCentre.Statement := by
  intro n J q M γ γ' Γ Γ' hJ hdim hΓd hΓ hΓ'd hΓ' hord
  funext s
  rcases s with j | i
  · have e := congrFun (hΓ 0 (Metric.mem_ball_self γ.radius_pos)).2 j
    have e' := congrFun (hΓ' 0 (Metric.mem_ball_self γ'.radius_pos)).2 j
    simp only [firstCoords] at e e'
    rw [e, e', γ.map_zero, γ'.map_zero]
  obtain ⟨a, b, hb, hab⟩ := M.birational i

  have key : ∀ (c : VarBranch J 1 q) (L : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
      DifferentiableOn ℂ L (Metric.ball 0 c.radius) →
      (∀ τ ∈ Metric.ball 0 c.radius, L τ ∈ zeroSetIn M.ideal ∧ firstCoords (L τ) = c.toFun τ) → ∀ l : ℂ,
      branchOrder c (a - C l * b) =
        branchOrder c b + analyticOrderAt (fun τ : ℂ ↦ L (fun _ ↦ τ) (Sum.inr i) - l) 0 := by
    intro c L hLd hL l
    have hLa : AnalyticAt ℂ (fun τ : ℂ ↦ L (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
      ((analyticAt_pi_iff.mp (analyticAt_comp_const_one c.radius_pos hLd)) (Sum.inr i)).sub analyticAt_const
    have hBa := analyticAt_eval_of_analyticAt_zero (analyticAt_comp_const_one c.radius_pos c.differentiableOn) b
    rw [branchOrder, branchOrder, ← analyticOrderAt_mul hBa hLa]
    apply analyticOrderAt_congr
    filter_upwards [eventually_const_mem_ball_one c.radius_pos] with τ hτ
    have h := (hL _ hτ).1 _ hab
    simp only [eval_sub, eval_mul, eval_X, eval_rename] at h
    change eval (firstCoords (L fun _ ↦ τ)) b * _ - eval (firstCoords (L fun _ ↦ τ)) a = 0 at h
    rw [(hL _ hτ).2] at h
    simp only [eval_sub, eval_mul, eval_C, Pi.mul_apply]
    linear_combination -h
  set l := Γ 0 (Sum.inr i)
  have k1 := key γ Γ hΓd hΓ l
  have k2 := key γ' Γ' hΓ'd hΓ' l
  rw [← hord, ← hord] at k2
  have heq := WithTop.add_left_cancel (branchOrder_ne_top_of_not_mem hB γ hJ hdim hb) (k1.symm.trans k2)
  have hGa : AnalyticAt ℂ (fun τ : ℂ ↦ Γ (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
    ((analyticAt_pi_iff.mp (analyticAt_comp_const_one γ.radius_pos hΓd)) (Sum.inr i)).sub analyticAt_const
  have hG'a : AnalyticAt ℂ (fun τ : ℂ ↦ Γ' (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
    ((analyticAt_pi_iff.mp (analyticAt_comp_const_one γ'.radius_pos hΓ'd)) (Sum.inr i)).sub analyticAt_const
  have hz : analyticOrderAt (fun τ : ℂ ↦ Γ (fun _ ↦ τ) (Sum.inr i) - l) 0 ≠ 0 :=
    hGa.analyticOrderAt_ne_zero.2 (sub_self _)
  rw [heq] at hz
  exact (sub_eq_zero.1 (hG'a.analyticOrderAt_ne_zero.1 hz)).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceFormMass.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (c : Fin (e + 1) → ℝ) (ψ : Fin (e + 1) → (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W →
    IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → f (t • x) = f x) → ContinuousOn f {x | x ≠ 0} →
    (∀ (k : Fin (e + 1)) (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → ψ k (t • x) = ψ k x) →
    (∀ k, ContDiffOn ℝ ∞ (ψ k) {x | x ≠ 0}) →
      Integrable (chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A f
        (fun k x => c k * Real.log (h.dualNorm x) + ψ k x))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserLocallyInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def UniformiserLocallyInjective.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) →
      ∃ U ∈ 𝓝 w, Set.InjOn (fun z : σ → ℂ ↦ eval z t) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I ∩ U)

end

end GroundTheory.Heights₂.Heights
end

