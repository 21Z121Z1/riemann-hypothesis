import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BorelDiagNeZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviTransfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in

theorem borel_diag_ne_zero {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (τ : Ψ) (i : Fin r) : b τ i i ≠ 0 := by
  have hdet := (hb τ).1
  have htri : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  rw [Matrix.det_of_upperTriangular htri] at hdet
  exact (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)

omit [NumberField E] [IsCMField E] in

theorem borel_char_ne_zero {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (la : Wt Ψ r) : bchar la b ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ =>
    zpow_ne_zero _ (borel_diag_ne_zero hb τ i)

omit [NumberField E] [IsCMField E] in

theorem left_act_one {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1) * mat x τ :
    Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

theorem normFactor_pos {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < X.nfac la x :=
  Finset.prod_pos fun τ _ => Finset.prod_pos fun _ _ => Real.rpow_pos_of_pos
    (norm_pos_iff.2 (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))) _

theorem metric_rmul (h : NfacRmulStatement (E := E)) {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    phla X la (rmul x b) = phla X la x + Real.log (Complex.normSq (bchar la b)) := by
  have h1 := normFactor_pos X la hx
  have h2 : 0 < ‖bchar la b‖ := norm_pos_iff.2 (borel_char_ne_zero hb la)
  unfold phla
  rw [h r X la x hx b hb, Real.log_mul (inv_pos.2 h2).ne' h1.ne', Real.log_inv,
    Complex.normSq_eq_norm_sq, Real.log_pow]
  push_cast
  ring

theorem levi_transfer :
    (KapGGStatement (E := E)) → (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)), cpt X x0 z ∈ X.dom → ∃ (x1 : Frame X.Ψ r) (D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ)), IsOrth X x1 ∧ Function.Injective D ∧ ∀ (la : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ), leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 (D ξ)) := by
  intro hK hN r X x0 z hz
  obtain ⟨x1, ho, b, hb, hxb⟩ := ortho_holds r X _ hz
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero, ← hxb] at h0
  have hcd : Differentiable ℂ (cpt X x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c =>
      (IW.cpt_entry_cd X x0 τ a c).differentiable (by simp)
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter
      (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = 0 := h0.2.1
  have hdet := hK r X x0 x1 1 U Φ bf hU hΦ (fun w hw =>
    ⟨hw.1, (hsplit _ hw.1 hw.2).2.1, by
      rw [left_act_one]; exact (hsplit _ hw.1 hw.2).2.2⟩) z hzU
  have hdet' : (fderiv ℂ Φ z).det ≠ 0 := by
    rw [hdet]; exact borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hinj : Function.Injective (fderiv ℂ Φ z) := by
    have hu : IsUnit ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet')
    exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hu)
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  refine ⟨x1, (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).toLinearMap ∘ₗ
    ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.toLinearMap, ho, ?_, ?_⟩
  · exact (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).injective.comp
      (hinj.comp (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.injective)
  intro la ξ
  have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
    classical
    intro w hw
    unfold bchar
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
      fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
      fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
    have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
      differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
    have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
      differentiableAt_zpow.2 (Or.inl (borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
    exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
  have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
    (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
  have hne : bchar la (bf z) ≠ 0 := borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hev : (fun w => ((phla X la (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => ((phla X la (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
    rw [← metric_rmul hN.1 X la h1 h2, ← h3]
  have hg : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 w)) (Φ z) := by
    rw [hΦz]
    exact (IW.phla_cpt_cdAt X x1 (IW.zero_mem_OmF X x1 ho) la).of_le HE.two_le_inf
  have h1 : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 (Φ w))) z :=
    hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
    (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
  have hgC : ContDiffAt ℝ 2 (fun w => ((phla X la (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
  have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
  rw [hΦz] at hc
  unfold leviM
  rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
    HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
  exact congrArg Complex.re hc

end GlobalTheory.LeviTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnOfCharts
section
namespace GlobalTheory.KronMetric

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem inv_rmul {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ) {x b : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : ψ (rmul x b) = ψ x := by
  have := h 1 X.Γ.one_mem x hx b hb
  rwa [FundSetPf.lact_one] at this

theorem inv_lact {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : ψ (lact γ x) = ψ x := by
  have := h γ hγ x hx _ (ExtFPf.oneF_mem X)
  rwa [ExtFPf.rmul_oneF] at this

theorem continuousOn_of_charts {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ)
    (hs : ∀ x0, IsOrth X x0 → ContinuousOn (fun z => ψ (cpt X x0 z)) (OmF X x0)) :
    ContinuousOn ψ X.dom := by
  intro x hx
  obtain ⟨x1, ho, b, hb, hxe⟩ := ortho_holds r X x hx
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x1 ho
  have h0 : (0 : V (nd X)) ∈ OmF X x1 := by
    show cpt X x1 0 ∈ X.dom
    rw [IW.cpt_zero]
    exact IW.orth_mem_dom X x1 ho
  have hΔ : D.Δ x ≠ 0 := by
    have := (D.uniq 0 h0 b hb).1
    rwa [IW.cpt_zero, ← hxe] at this
  have hc : ContinuousOn (fun y => ψ (cpt X x1 (D.zOf y))) (ExtFPf.cell D) :=
    (hs x1 ho).comp D.hz.continuousOn fun y hy => (D.split y hy.1 hy.2).1
  have hc' : ContinuousOn ψ (ExtFPf.cell D) := by
    refine hc.congr fun y hy => ?_
    obtain ⟨h1, h2, h3⟩ := D.split y hy.1 hy.2
    show ψ y = ψ (cpt X x1 (D.zOf y))
    conv_lhs => rw [h3]
    exact inv_rmul h h1 h2
  exact (hc'.continuousAt ((ExtFPf.isOpen_cell D).mem_nhds ⟨hx, hΔ⟩)).continuousWithinAt

theorem exp_neg_phla {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  unfold phla
  rw [neg_mul, neg_neg, show 2 * Real.log (X.nfac la x) = Real.log (X.nfac la x ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

theorem exp_neg_add {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    Real.exp (-(phla X la x + ψ x)) = X.nfac la x ^ 2 * Real.exp (-ψ x) := by
  rw [neg_add, Real.exp_add, exp_neg_phla X la hx]

theorem kronMetric :
    (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ ψ : Frame X.Ψ r → ℝ, IsInvFn X ψ → (∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → ContinuousOn ψ X.dom ∧ IsMetricW X la (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) ∧ WLower X la (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))))) := by
  rintro ⟨hR, hL, -⟩ r X la ψ hinv hs ⟨C, hC⟩
  classical
  have hψc : ContinuousOn ψ X.dom := continuousOn_of_charts hinv fun x0 h => (hs x0 h).continuousOn
  refine ⟨hψc, ⟨?_, ?_, ?_⟩, Real.exp (-C), Real.exp_pos _, ?_⟩
  · have hc : ContinuousOn (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) X.dom := by
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine (((ExtFPf.nfac_contOn X la).pow 2).mul
        (Real.continuous_exp.comp_continuousOn hψc.neg)).congr fun x hx => ?_
      exact exp_neg_add X la ψ hx
    rw [← Set.piecewise_eq_indicator]
    exact hc.measurable_piecewise continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet
  · intro x hx b hb
    have hxb := OntoS.dom_rmul X hx hb
    have hpos : 0 < ‖bchar la b‖ := norm_pos_iff.2 (OntoE.bchar_ne X la hb)
    rw [Set.indicator_of_mem hxb, Set.indicator_of_mem hx, exp_neg_add X la ψ hxb,
      exp_neg_add X la ψ hx, hR r X la x hx b hb, inv_rmul hinv hx hb,
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · intro γ hγ x hx
    have hγx := OntoS.dom_lact X hγ hx
    rw [Set.indicator_of_mem hγx, Set.indicator_of_mem hx, exp_neg_add X la ψ hγx,
      exp_neg_add X la ψ hx, hL r X la γ hγ x hx, inv_lact hinv hγ hx]
  · intro x hx
    rw [Set.indicator_of_mem hx, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    linarith [hC x hx]

end GlobalTheory.KronMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CptDifferentiable
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ProperImmersionPoint

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pnorm_sq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : X.pnorm la P x ^ 2 = ‖P x‖ ^ 2 * Real.exp (-phla X la x) := by
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  have e : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  have e2 : -phla X la x = ((2 : ℕ) : ℝ) * Real.log (X.nfac la x) := by
    unfold phla; push_cast; ring
  rw [e, e2, Real.exp_nat_mul, Real.exp_log hn, mul_pow]

theorem pnorm_contOn {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ}
    (hP : DifferentiableOn ℂ P X.dom) : ContinuousOn (X.pnorm la P) X.dom :=
  hP.continuousOn.norm.mul (ExtFPf.nfac_contOn X la)

theorem phla_lin {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (L eW : Wt X.Ψ r) (a : ℕ) :
    phla X (a • L - eW) x = a * phla X L x - phla X eW x := by
  rw [IW.phla_eq X hx, IW.phla_eq X hx, IW.phla_eq X hx, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem cpt_differentiable {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) :
    Differentiable ℂ (cpt X x0) :=
  differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
    (IW.cpt_entry_cd X x0 τ a b).differentiable (by simp)

noncomputable def ratio {r : ℕ} (X : Data E r) (L eW : Wt X.Ψ r) {N : ℕ} (a : ℕ)
    (w : Fin N → Frame X.Ψ r → ℂ) (et : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  X.pnorm eW et x ^ 2 / (∑ k, X.pnorm L (w k) x ^ 2) ^ a

theorem sum_pnorm_sq {r : ℕ} {X : Data E r} (L : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∑ k, X.pnorm L (w k) x ^ 2 = (∑ k, ‖w k x‖ ^ 2) * Real.exp (-phla X L x) := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => pnorm_sq X _ _ hx

theorem sum_norm_pos {r : ℕ} {X : Data E r} {N : ℕ} {w : Fin N → Frame X.Ψ r → ℂ}
    (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, ‖w k x‖ ^ 2 := by
  obtain ⟨k, hk⟩ := hnz x hx
  exact Finset.sum_pos' (fun j _ => by positivity)
    ⟨k, Finset.mem_univ k, pow_pos (norm_pos_iff.2 hk) 2⟩

theorem sum_pnorm_pos {r : ℕ} {X : Data E r} {L : Wt X.Ψ r} {N : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ}
    (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, X.pnorm L (w k) x ^ 2 := by
  rw [sum_pnorm_sq L w hx]
  exact mul_pos (sum_norm_pos hnz hx) (Real.exp_pos _)

theorem ratio_pos {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ}
    (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : et x ≠ 0) : 0 < ratio X L eW a w et x := by
  refine div_pos ?_ (pow_pos (sum_pnorm_pos hnz hx) _)
  rw [pnorm_sq X _ _ hx]
  exact mul_pos (pow_pos (norm_pos_iff.2 h) 2) (Real.exp_pos _)

theorem ratio_contOn {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ}
    (hw : ∀ k, X.IsSec L (w k)) (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) (het : X.IsSec eW et) :
    ContinuousOn (ratio X L eW a w et) X.dom := by
  refine ContinuousOn.div ((pnorm_contOn X _ het.1).pow 2) (ContinuousOn.pow ?_ _)
    fun x hx => (pow_pos (sum_pnorm_pos hnz hx) _).ne'
  exact continuousOn_finsetSum _ fun k _ => (pnorm_contOn X _ (hw k).1).pow 2

theorem exists_max {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ}
    (hw : ∀ k, X.IsSec L (w k)) (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) (het : X.IsSec eW et)
    (hne : ∃ x ∈ X.dom, et x ≠ 0)
    (hprop : ∀ δ : ℝ, 0 < δ → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom,
      δ * (∑ k, X.pnorm L (w k) x ^ 2) ^ a ≤ X.pnorm eW et x ^ 2 →
        ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) :
    ∃ x ∈ X.dom, et x ≠ 0 ∧ ∀ y ∈ X.dom, ratio X L eW a w et y ≤ ratio X L eW a w et x := by
  obtain ⟨x1, hx1, he1⟩ := hne
  have h1 : 0 < ratio X L eW a w et x1 := ratio_pos hnz hx1 he1
  have hP : PnormInvStatement (E := E) := pointwiseNorm_invariance_holds
  have hinv : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      ratio X L eW a w et (lact γ (rmul x b)) = ratio X L eW a w et x := by
    intro γ hγ x hx b hb
    unfold ratio
    rw [hP r X _ _ het γ hγ x hx b hb]
    congr 2
    exact Finset.sum_congr rfl fun k _ => by rw [hP r X _ _ (hw k) γ hγ x hx b hb]
  obtain ⟨K, hK, hKd, hKs⟩ := hprop _ h1
  have hbig : ∀ y ∈ X.dom, ratio X L eW a w et x1 ≤ ratio X L eW a w et y →
      ∃ y' ∈ K, ratio X L eW a w et y' = ratio X L eW a w et y := by
    intro y hy hle
    obtain ⟨γ, hγ, b, hb, hk⟩ := hKs y hy
      ((le_div_iff₀ (pow_pos (sum_pnorm_pos hnz hy) a)).1 hle)
    exact ⟨_, hk, hinv γ hγ y hy b hb⟩
  obtain ⟨y1, hy1K, hy1⟩ := hbig x1 hx1 le_rfl
  obtain ⟨x, hxK, hxmax⟩ := hK.exists_isMaxOn ⟨y1, hy1K⟩
    ((ratio_contOn (a := a) hw hnz het).mono hKd)
  have hx1x : ratio X L eW a w et x1 ≤ ratio X L eW a w et x := hy1 ▸ isMaxOn_iff.1 hxmax y1 hy1K
  refine ⟨x, hKd hxK, fun h0 => ?_, fun y hy => ?_⟩
  · have : ratio X L eW a w et x ≤ 0 := by
      unfold ratio
      rw [pnorm_sq X _ _ (hKd hxK), h0]
      simp
    linarith
  · rcases lt_or_ge (ratio X L eW a w et y) (ratio X L eW a w et x1) with h | h
    · exact h.le.trans hx1x
    · obtain ⟨y', hy'K, hy'⟩ := hbig y hy h
      exact hy' ▸ isMaxOn_iff.1 hxmax y' hy'K

theorem log_ratio {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ}
    (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : et x ≠ 0) : Real.log (ratio X L eW a w et x) =
      Real.log (Complex.normSq (et x)) + phla X (a • L - eW) x +
        (-(a : ℝ)) * Real.log (∑ k, ‖w k x‖ ^ 2) := by
  have hA : 0 < ‖et x‖ ^ 2 := pow_pos (norm_pos_iff.2 h) 2
  have hW := sum_norm_pos hnz hx
  unfold ratio
  rw [phla_lin X hx, pnorm_sq X _ _ hx, sum_pnorm_sq L w hx,
    Real.log_div (mul_pos hA (Real.exp_pos _)).ne' (pow_pos (mul_pos hW (Real.exp_pos _)) _).ne',
    Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow _ a,
    Real.log_mul hW.ne' (Real.exp_pos _).ne', Real.log_exp, Complex.normSq_eq_norm_sq]
  ring

theorem levi_pos {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ} (ha : 0 < a)
    (hw : ∀ k, X.IsSec L (w k)) (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) (het : X.IsSec eW et)
    (hpos : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X (a • L - eW)) x0 z ξ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (he : et x ≠ 0) (hmax : ∀ y ∈ X.dom, ratio X L eW a w et y ≤ ratio X L eW a w et x) (ξ : Fin (nd X) → ℂ)
    (hξ : ξ ≠ 0) :
    0 < (leviV (nd X) (fun z => ((Real.log (∑ k, ‖w k (cpt X x z)‖ ^ 2) : ℝ) : ℂ)) 0 ξ).re := by
  have hz : cpt X x 0 = x := IW.cpt_zero X x
  have h0 : (0 : V (nd X)) ∈ OmF X x := by
    change cpt X x 0 ∈ X.dom
    rwa [hz]
  have hO := ExF.isOpen_OmF X x
  have htn : OmF X x ∈ 𝓝 (0 : V (nd X)) := hO.mem_nhds h0
  have holo : ∀ {P : Frame X.Ψ r → ℂ}, DifferentiableOn ℂ P X.dom →
      ContDiffAt ℂ 2 (fun z => P (cpt X x z)) 0 := by
    intro P hP
    have h1 : DifferentiableOn ℂ (fun z => P (cpt X x z)) (OmF X x) :=
      hP.comp (cpt_differentiable X x).differentiableOn fun _ hz => hz
    exact ((contDiffOn_of_differentiableOn _ _ _ hO h1).contDiffAt htn).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hga := holo het.1
  have hgw : ∀ k, ContDiffAt ℂ 2 (fun z => w k (cpt X x z)) 0 := fun k =>
    holo (hw k).1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (a : ℝ) := ⟨_, rfl⟩
  have hm' : (1 : ℝ) ≤ m := by
    rw [hm]
    exact_mod_cast ha
  obtain ⟨fα, hfα⟩ : ∃ f : V (nd X) → ℝ,
      f = fun v => Real.log (Complex.normSq (et (cpt X x v))) := ⟨_, rfl⟩
  obtain ⟨fP, hfP⟩ : ∃ f : V (nd X) → ℝ, f = fun v => phla X (a • L - eW) (cpt X x v) := ⟨_, rfl⟩
  obtain ⟨fW, hfW⟩ : ∃ f : V (nd X) → ℝ,
      f = fun v => Real.log (∑ k, ‖w k (cpt X x v)‖ ^ 2) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ f : V (nd X) → ℝ,
      f = fun v => (fα v + fP v) + (-m) * fW v := ⟨_, rfl⟩
  have hαc : ContDiffAt ℝ 2 (fun v => Complex.normSq (et (cpt X x v))) 0 := by
    have := (contDiff_norm_sq ℝ).comp_contDiffAt (0 : V (nd X)) (hga.restrict_scalars ℝ)
    simpa [Function.comp_def, Complex.normSq_eq_norm_sq] using this
  have hα0 : Complex.normSq (et (cpt X x 0)) ≠ 0 := by
    rw [hz]; exact (Complex.normSq_pos.2 he).ne'
  have hcα : ContDiffAt ℝ 2 fα 0 := by rw [hfα]; exact hαc.log hα0
  have hcP : ContDiffAt ℝ 2 fP 0 := by
    rw [hfP]; exact (IW.phla_cpt_cdAt X x h0 _).of_le (WithTop.coe_le_coe.2 le_top)
  have hWc : ContDiffAt ℝ 2 (fun v => ∑ k, ‖w k (cpt X x v)‖ ^ 2) 0 :=
    ContDiffAt.sum (fun k _ => (contDiff_norm_sq ℝ).comp_contDiffAt _ ((hgw k).restrict_scalars ℝ))
  have hW0 : (∑ k, ‖w k (cpt X x 0)‖ ^ 2) ≠ 0 := (sum_norm_pos hnz h0).ne'
  have hcW : ContDiffAt ℝ 2 fW 0 := by rw [hfW]; exact hWc.log hW0
  have hc1 : ContDiffAt ℝ 2 (fun v => fα v + fP v) 0 := hcα.add hcP
  have hc2 : ContDiffAt ℝ 2 (fun v => (-m) * fW v) 0 := contDiffAt_const.mul hcW
  have hch : ContDiffAt ℝ 2 h 0 := by rw [hh]; exact hc1.add hc2
  have hne : ∀ᶠ v in 𝓝 (0 : V (nd X)), et (cpt X x v) ≠ 0 :=
    hga.continuousAt.eventually_ne (by rw [hz]; exact he)
  have hloc : ∀ᶠ v in 𝓝 (0 : V (nd X)), h v = Real.log (ratio X L eW a w et (cpt X x v)) := by
    filter_upwards [htn, hne] with v hv hv'
    rw [log_ratio hnz hv hv', hh, hfα, hfP, hfW, hm]
  have hmaxh : IsLocalMax h 0 := by
    have h00 := hloc.self_of_nhds
    rw [hz] at h00
    filter_upwards [hloc, htn, hne] with v hv hvt hv'
    rw [hv, h00]
    exact Real.log_le_log (ratio_pos hnz hvt hv') (hmax _ hvt)
  have hL := Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hch hmaxh ξ
  have e1 : leviV (nd X) (fun y => ((h y : ℝ) : ℂ)) 0 ξ =
      leviV (nd X) (fun y => ((fα y + fP y : ℝ) : ℂ)) 0 ξ +
        leviV (nd X) (fun y => (((-m) * fW y : ℝ) : ℂ)) 0 ξ := by
    rw [hh]; exact Y.LocalMaximumSecondDerivative.leviV_ofReal_add hc1 hc2 ξ
  have e2 : leviV (nd X) (fun y => ((fα y + fP y : ℝ) : ℂ)) 0 ξ =
      leviV (nd X) (fun y => ((fα y : ℝ) : ℂ)) 0 ξ +
        leviV (nd X) (fun y => ((fP y : ℝ) : ℂ)) 0 ξ :=
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add hcα hcP ξ
  rw [e1, e2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ hcW] at hL
  simp only [Complex.add_re, Complex.re_ofReal_mul] at hL
  have hαnn : 0 ≤ (leviV (nd X) (fun y => ((fα y : ℝ) : ℂ)) 0 ξ).re := by
    have hpos' : 0 < ∑ _j : Fin 1, Complex.normSq (et (cpt X x 0)) := by
      simp only [Fin.sum_univ_one, hz]; exact Complex.normSq_pos.2 he
    have := leviV_log_sum_nonneg (m := 1)
      (u := fun _ v => Complex.normSq (et (cpt X x v))) (x := 0)
      (fun _ => hαc) (fun _ => logPshAt_normSq hga) hpos' ξ
    rw [hfα]; simpa using this
  have hPpos : 0 < (leviV (nd X) (fun y => ((fP y : ℝ) : ℂ)) 0 ξ).re := by
    rw [hfP]; exact hpos x hx 0 h0 ξ hξ
  have hfin : 0 < (leviV (nd X) (fun y => ((fW y : ℝ) : ℂ)) 0 ξ).re := by
    by_contra hle
    push Not at hle
    have h1 := mul_nonneg (by linarith : (0 : ℝ) ≤ m) (neg_nonneg.2 hle)
    nlinarith
  rw [hfW] at hfin
  exact hfin

end

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (L eW : Wt X.Ψ r) (N a : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (et : Frame X.Ψ r → ℂ), 0 < a → (∀ k, X.IsSec L (w k)) → (∀ x ∈ X.dom, ∃ k, w k x ≠ 0) → X.IsSec eW et → (∃ x ∈ X.dom, et x ≠ 0) → (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 → 0 < leviM X (phla X (a • L - eW)) x0 z ξ) → (∀ δ : ℝ, 0 < δ → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom, δ * (∑ k, X.pnorm L (w k) x ^ 2) ^ a ≤ X.pnorm eW et x ^ 2 → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) → ∃ x ∈ X.dom, ∃ (j0 : Fin N) (jj : Fin (nd X) → Fin N), w j0 x ≠ 0 ∧ (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => w (jj k) (cpt X x z) / w j0 (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
  intro E _ _ _ r X L eW N a w et ha hw hnz het hne hpos hprop
  obtain ⟨x, hx, he, hmax⟩ := exists_max hw hnz het hne hprop
  have hz : cpt X x 0 = x := IW.cpt_zero X x
  have h0 : (0 : V (nd X)) ∈ OmF X x := by
    change cpt X x 0 ∈ X.dom
    rwa [hz]
  obtain ⟨j0, jj, hj0, hdet⟩ := GlobalTheory.LeviRank.main (nd X) N (fun k z => w k (cpt X x z))
    (OmF X x) (ExF.isOpen_OmF X x) h0
    (fun k => (hw k).1.comp (cpt_differentiable X x).differentiableOn fun _ hz => hz)
    (hnz _ h0) (levi_pos ha hw hnz het hpos hx he hmax)
  exact ⟨x, hx, j0, jj, by simpa only [hz] using hj0, hdet⟩

end GlobalTheory.ProperImmersionPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsUnitaryElemOfIsUStab
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_unitary_elem_of_isUStab :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∃ g : H, ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) :=
  fun _ X _ hH γ hγ =>
    ⟨⟨embGL X.Ψ γ, (hH _).mpr (isUnitaryC_of_isUStab X hγ)⟩, fun τ => embGL_val X.Ψ γ τ⟩

end GlobalTheory.FiniteCovolume
end

