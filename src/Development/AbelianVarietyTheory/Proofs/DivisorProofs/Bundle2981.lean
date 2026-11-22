import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2885
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcOmegaFormEqC2SubC1Product
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.HermFrame GlobalTheory.SecForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped Classical ComplexOrder

namespace GlobalTheory.LineForm.DdcLine

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

def hseq (hX : IsRegVar p D) (σ : k →+* ℂ) {E : X.Modules} (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) :
    HermSeq (hX.atlas σ) 1 1 :=
  hX.seq (lineSC_shortExact fl) (h₁ := h.restrict (fl.isSubbundle 1) (fl.isVB 1)) (h₂ := h)
    (h₃ := VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1))
    (H.restrict _ _) H (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) _ _ _ H) σ

variable (hX : IsRegVar p D) (σ : k →+* ℂ) {E : X.Modules} (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2)

theorem crd_mem (x : (hX.atlas σ).Pt) : x.crd ∈ chartSet (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1 := by
  refine ⟨x.ch.map_source x.2, ?_⟩
  show (x.ch.symm x.crd) ∈ ptsIn p σ (frameAt fl x.pt).U
  rw [x.ch.left_inv x.2]
  exact mem_frameAt fl x.pt

theorem loc_omF (x : (hX.atlas σ).Pt) :
    (hX.atlas σ).loc (fld _ (omF hX σ h fl)) x.1.1 =ᶠ[𝓝 x.crd]
      fun v => (ofValues (extTrace (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1) v) : Alt D) := by
  filter_upwards [(isOpen_chartSet (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1).mem_nhds (crd_mem hX σ h H fl x)] with v hv
  have hv1 : v ∈ ((hX.atlas σ).e x.1.1).target := hv.1
  rw [HolAtlas.loc, dif_pos hv1]
  set y : (hX.atlas σ).Pt := ⟨(x.1.1, ((hX.atlas σ).e x.1.1).symm v), ((hX.atlas σ).e x.1.1).map_target hv1⟩ with hy
  have hb : v ∈ chartSet (hseq hX σ h H fl) (frameAt fl y.pt) x.1.1 := ⟨hv1, mem_frameAt fl y.pt⟩
  have e1 : y.crd = v := ((hX.atlas σ).e x.1.1).right_inv hv1
  change (ofValues (extTrace (midIn (hseq hX σ h H fl) (frameAt fl y.pt) x.1.1) y.crd) : Alt D) = _
  rw [e1, GlobalTheory.T.extTrace_chart_indep (hseq hX σ h H fl) (frameAt fl y.pt) (frameAt fl x.pt) x.1.1 ⟨hb, hv⟩]

end GlobalTheory.LineForm.DdcLine

namespace GlobalTheory.LineForm.DdcLine

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
variable (hX : IsRegVar p D) (σ : k →+* ℂ)

theorem c1F_det_metric_eq_chernOne {F : X.Modules} {r : ℕ} {m : VMetric p F r} (Hm : m.IsCInf) (x : (hX.atlas σ).Pt) (c : Chart F r)
    (hc : x.pt ∈ ptsIn p σ c.U) :
    c1F hX σ (VMetric.det Hm) x = ofValues (chernOne (fun w => (m.met σ).G c (x.ch.symm w)) x.crd) := by
  obtain ⟨⟨a, y⟩, hy⟩ := x
  have hy' : y ∈ a.e.source := hy
  change y ∈ ptsIn p σ c.U at hc
  set b := pick ((VMetric.det Hm).φ σ).isLB y
  have hb : y ∈ ptsIn p σ ((VMetric.det Hm).B.U b) := mem_pick _ y
  have hc' : y ∈ ptsIn p σ ((VMetric.det Hm).B.U c) := hc
  have ho := ChartGlue.isOpen_over a.e (isOpen_ptsIn (p := p) (σ := σ) ((VMetric.det Hm).B.U c ⊓ (VMetric.det Hm).B.U b))
  have hm := ChartGlue.mem_over a.e hy' (mem_ptsIn_inf.2 ⟨hc', hb⟩)
  set u := c.isFrame.detUnit b.isFrame inf_le_left inf_le_right
  have hg := a.holo _ u.val
  have hf : ContDiffAt ℂ 2 (ev p σ _ u.val ∘ a.e.symm) (a.e y) :=
    (SCV.analyticAt_of_differentiableOn (hg.mono fun v hv => ⟨hv.1, hv.2⟩) (ho.mem_nhds hm)).contDiffAt
  have h0 : (ev p σ _ u.val ∘ a.e.symm) (a.e y) ≠ 0 := ev_ne_zero hm.2 u.isUnit
  have hC : ContDiffAt ℝ 2 (fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v)) (a.e y) :=
    ((VMetric.det Hm).cInf σ).contDiffAt a hy' hc'
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(ev p σ _ u.val ∘ a.e.symm) v‖ ^ 2)) (a.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have key : leviForm (fun v => ((VMetric.det Hm).φ σ).φ b (a.e.symm v)) (a.e y) =
      leviForm (fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v)) (a.e y) := by
    rw [leviForm_congr (u' := fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v) +
        -Real.log (‖(ev p σ _ u.val ∘ a.e.symm) v‖ ^ 2)), leviForm_add hC hlog.neg,
      leviForm_neg, leviForm_log_normSq_eq_zero hf h0, neg_zero, add_zero]
    filter_upwards [ho.mem_nhds hm] with v hv
    rw [((VMetric.det Hm).φ σ).trans c b _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, sub_eq_add_neg]
    rfl
  have eL : c1F hX σ (VMetric.det Hm) ⟨(a, y), hy⟩ =
      ofValues (HermFrame.ddc (fun v => ((VMetric.det Hm).φ σ).φ b (a.e.symm v)) (a.e y)) := rfl
  rw [eL]
  unfold HermFrame.ddc
  rw [key]
  have hM : MContDiffAt 2 (fun w => (m.met σ).G c (a.e.symm w)) (a.e y) :=
    (((Hm σ) c y hc).mContDiffAt a hy').of_le (WithTop.coe_le_coe.2 le_top)
  have hH : ∀ᶠ w in 𝓝 (a.e y), ((m.met σ).G c (a.e.symm w)).IsHermitian := by
    filter_upwards [ho.mem_nhds hm] with v hv
    exact ((m.met σ).posDef c _ (mem_ptsIn_inf.1 hv.2).1).1
  have hU : IsUnit ((m.met σ).G c (a.e.symm (a.e y))).det := by
    rw [a.e.left_inv hy']
    exact ((m.met σ).posDef c y hc).det_pos.ne'.isUnit
  have e2 : (fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v)) =
      fun v => -Real.log ((m.met σ).G c (a.e.symm v)).det.re := rfl
  change _ = ofValues (chernOne (fun w => (m.met σ).G c (a.e.symm w)) (a.e y))
  congr 1
  funext ξ η
  rw [chernOne_eq_neg_ddc_log_det hM hH hU, e2, leviForm_neg, ddc]
  simp

end GlobalTheory.LineForm.DdcLine

namespace GlobalTheory.LineForm.DdcLine

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
variable (hX : IsRegVar p D) (σ : k →+* ℂ) {E : X.Modules} (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2)

theorem restrict_G_sub (a : VBExt.AdaptedChart (lineSC fl) 1 1) (y : CxPts p σ) :
    ((h.restrict (fl.isSubbundle 1) (fl.isVB 1)).met σ).G a.sub y = subGram ((h.met σ).gram a.frame y) := by
  ext i j
  simp only [VMetric.restrict, Met.restrict, Met.gram, subGram, Matrix.toBlocks₁₁, Matrix.of_apply,
    VBExt.AdaptedChart.frame, VBExt.AdaptedChart.sub, Sum.elim_inl]

theorem quot_G_line (a : VBExt.AdaptedChart (lineSC fl) 1 1) {y : CxPts p σ} (hy : y ∈ ptsIn p σ a.U) :
    ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1)).met σ).G
      a.quot y = quotGram ((h.met σ).gram a.frame y) :=
  Met.quot_G (S := lineSC fl) (r := 1) (s := 1) (h.met σ) (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1) a hy

theorem isometric_quot_line :
    (VMetric.det (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1) H)).Isometric
      (VMetric.det (VMetric.IsCInf.quot (S := .mk _ _ (line_lineQuot fl)) (r := 1) (s := 1) (shortExact_lineQuot fl)
        (fl.isVB 1) (fl.isVB_gr 1) H)) :=
  (isometric_detQuot_and_bcInt_eq_of_iso k X p (lineSC fl) (.mk _ _ (line_lineQuot fl)) 1 1 h h H H
    (lineSC_shortExact fl) (shortExact_lineQuot fl) (fl.isVB 1) (fl.isVB_cokernel 1) (fl.isVB 1) (fl.isVB_gr 1)
    (Iso.refl _) (Iso.refl _) (by simp) (fun σ V s t y hy => by simp)).1

theorem c1F_grLB_zero_eq_chernOne_subGram (x : (hX.atlas σ).Pt) : c1F hX σ (VMetric.grLB fl 0 H) x =
    ofValues (chernOne (fun w => subGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) x.crd) := by
  have e₁ : c1F hX σ (VMetric.grLB fl 0 H) x =
      c1F hX σ (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))) x := by
    rw [c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_zero H fl)]
  have e₂ : c1F hX σ (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))) x =
      ofValues (chernOne (fun w => ((h.restrict (fl.isSubbundle 1) (fl.isVB 1)).met σ).G (frameAt fl x.pt).sub
        (x.ch.symm w)) x.crd) :=
    c1F_det_metric_eq_chernOne hX σ _ x (frameAt fl x.pt).sub (mem_frameAt fl x.pt)
  have e₃ : (fun w => ((h.restrict (fl.isSubbundle 1) (fl.isVB 1)).met σ).G (frameAt fl x.pt).sub (x.ch.symm w)) =
      fun w => subGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w)) :=
    funext fun w => restrict_G_sub σ h fl _ _
  rw [e₁, e₂, e₃]

theorem c1F_grLB_one_eq_chernOne_quotGram (x : (hX.atlas σ).Pt) : c1F hX σ (VMetric.grLB fl 1 H) x =
    ofValues (chernOne (fun w => quotGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) x.crd) := by
  have e₁ : c1F hX σ (VMetric.grLB fl 1 H) x = c1F hX σ (VMetric.det (VMetric.IsCInf.quot (S := lineSC fl) (r := 1)
      (s := 1) (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1) H)) x := by
    rw [c1F_eq_of_isometric k X p D hX σ _ _ (isometric_quot_line h H fl),
      c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_one H fl)]
  have e₂ : c1F hX σ (VMetric.det (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) (lineSC_shortExact fl)
      (fl.isVB 1) (fl.isVB_cokernel 1) H)) x =
      ofValues (chernOne (fun w => ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
        (fl.isVB_cokernel 1)).met σ).G (frameAt fl x.pt).quot (x.ch.symm w)) x.crd) :=
    c1F_det_metric_eq_chernOne hX σ (m := VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1)) (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1) H) x (frameAt fl x.pt).quot (mem_frameAt fl x.pt)
  have he : (fun w => ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1)).met σ).G (frameAt fl x.pt).quot (x.ch.symm w)) =ᶠ[𝓝 x.crd]
      (fun w => quotGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) := by
    filter_upwards [(isOpen_chartSet (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1).mem_nhds (crd_mem hX σ h H fl x)]
      with v hv
    have hv2 : x.ch.symm v ∈ ptsIn p σ (frameAt fl x.pt).U := hv.2
    exact quot_G_line σ h fl (frameAt fl x.pt) hv2
  have e₃ : chernOne (fun w => ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1)).met σ).G (frameAt fl x.pt).quot (x.ch.symm w)) x.crd =
      chernOne (fun w => quotGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) x.crd := by
    funext ξ η
    simp only [chernOne]
    rw [curv_congr he]
  rw [e₁, e₂, e₃]

theorem ofValuesTwo_sub {n : ℕ} (Ψ Φ : V n → V n → V n → V n → ℂ) :
    ofValuesTwo (fun a b c d => Ψ a b c d - Φ a b c d) = ofValuesTwo Ψ - ofValuesTwo Φ := by
  simp only [ofValuesTwo, sub_smul, Finset.sum_sub_distrib, smul_sub]

theorem ddc_omF : (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) =
    fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H)) := by
  funext x
  have hmem := crd_mem hX σ h H fl x
  have hpos := isPosFrame_midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1
  rw [GlobalTheory.T.ddc_eq_of_local_eq _ _ x _ (loc_omF hX σ h H fl x), GlobalTheory.T.ddc_ofValues_eq _ _ (fun a b =>
    ((GlobalTheory.T.contDiffOn_extTrace_of_isPosFrame hpos _ _).contDiffAt (hpos.1.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top))]
  have hc := (((GlobalTheory.SubQuotCurv.subQuotCurvature _ (Fin 1) (Fin 1) _ _).2 hpos).2.2.2 (by simp) (by simp) _ hmem).2.2.2
  have hd : ddcForm (extTrace (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1)) x.crd = fun ξ₁ η₁ ξ₂ η₂ =>
      chernTwo (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1) x.crd ξ₁ η₁ ξ₂ η₂ -
        wedge (chernOne (GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramS (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1)) x.crd)
          (chernOne (GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramQ (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1)) x.crd) ξ₁ η₁ ξ₂ η₂ := by
    funext ξ₁ η₁ ξ₂ η₂; exact hc ξ₁ η₁ ξ₂ η₂
  rw [hd, ofValuesTwo_sub, ← GlobalTheory.T.chernAt_two_eq_ofValuesTwo_chernTwo, ← GlobalTheory.T.ofValues_mul_ofValues']
  simp only [fld, Pi.sub_apply, Pi.mul_apply, c1F_grLB_zero_eq_chernOne_subGram hX σ h H fl x, c1F_grLB_one_eq_chernOne_quotGram hX σ h H fl x]
  rfl

end GlobalTheory.LineForm.DdcLine

theorem GlobalTheory.LineForm.ddc_omF_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) =
      fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H)) :=
  fun _ _ _ _ _ _ hX σ _ h H fl => GlobalTheory.LineForm.DdcLine.ddc_omF hX σ h H fl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDegreeTwoClassPullbackOfCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.PullTwo

section Lift

variable {D : Data} (Λ : Lift D)

def j1 (U : AffOp D.X) : Ω[Sec D.s U.unop.1⁄D.R] →+ K1 D.R (Λ.L.obj U).δ where
  toFun ω := Submodule.Quotient.mk ((Λ.semi U).m1 ω)
  map_zero' := by rw [map_zero, Submodule.Quotient.mk_zero]
  map_add' a b := by rw [map_add, Submodule.Quotient.mk_add]

def j2 (U : AffOp D.X) : Om D.R (Sec D.s U.unop.1) 2 →+ K D.R (Λ.L.obj U).δ 2 where
  toFun ω := Submodule.Quotient.mk ((Λ.semi U).mOm 2 ω)
  map_zero' := by rw [map_zero, Submodule.Quotient.mk_zero]
  map_add' a b := by rw [map_add, Submodule.Quotient.mk_add]

theorem compatibleOneFormClass_restriction_natural {U V : AffOp D.X} (a : U ⟶ V) (ω : Ω[Sec D.s U.unop.1⁄D.R]) :
    j1 Λ V (p1 (OAff D.s) a ω) = km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (j1 Λ U ω) := by
  show (Submodule.Quotient.mk ((Λ.semi V).m1 ((semiHom_mp (OAff D.s) a).m1 ω)) : K1 D.R (Λ.L.obj V).δ) =
    km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (Submodule.Quotient.mk ((Λ.semi U).m1 ω))
  rw [divPowerCompatOneFormMap_mk]
  congr 1
  rw [SemiHom.oneFormMap_comp_oneFormMap (semiHom_mp (OAff D.s) a) (Λ.semi V) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
      (fun _ ↦ rfl),
    SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) (SemiHom.of_algHom (Λ.L.map a).φ) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
      (fun b ↦ (Λ.nat a b).symm)]

theorem compatibleOneFormClass_kaehler_differential (U : AffOp D.X) (b : Sec D.s U.unop.1) :
    j1 Λ U (KaehlerDifferential.D D.R _ b) = kd0 D.R (Λ.L.obj U).δ (Λ.e U b) := by
  show (Submodule.Quotient.mk ((Λ.semi U).m1 (KaehlerDifferential.D D.R _ b)) : K1 D.R (Λ.L.obj U).δ) = _
  rw [SemiHom.m1_D, divPowerCompatFunctionDifferential_apply]
  all_goals rfl

theorem compatibleTwoFormClass_exterior_derivative (U : AffOp D.X) (ω : Ω[Sec D.s U.unop.1⁄D.R]) :
    j2 Λ U (dOne D.R _ ω) = kd1 D.R (Λ.L.obj U).δ (j1 Λ U ω) := by
  show (Submodule.Quotient.mk ((Λ.semi U).mOm 2 (dOne D.R _ ω)) : K D.R (Λ.L.obj U).δ 2) =
    kd1 D.R (Λ.L.obj U).δ (Submodule.Quotient.mk ((Λ.semi U).m1 ω))
  rw [SemiHom.mOm_dOne, divPowerCompatOneFormDerivative_mk]

end Lift

section Pull

variable {D D' : Data} (Λ : Lift D) (Λ' : Lift D') {σ : D.R →+* D'.R} {φ : D'.X ⟶ D.X} {φ₀ : D'.X₀ ⟶ D.X₀}
  (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
  (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
    Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))

include hθ

theorem movedDatum_compatibleOneFormClass (p : (Pair φ)ᵒᵖ) (ω : Ω[Sec D.s p.unop.1.2.1⁄D.R]) :
    ((pairB Λ' φ m).pre θ).a1 p (j1 Λ (Opposite.op p.unop.1.2) ω) =
      j1 Λ' (Opposite.op p.unop.1.1) ((semiHom_secPull hφ p.unop).m1 ω) := by
  exact congrArg Submodule.Quotient.mk
    (((congrArg (morSemi m ((pairFst φ ⋙ Λ'.L).obj p)).m1 (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (fun _ ↦ rfl) ω)).trans
      (SemiHom.oneFormMap_comp_oneFormMap ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (morSemi m ((pairFst φ ⋙ Λ'.L).obj p))
        ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1))) (fun b ↦ hθ p b) ω)).trans
      (SemiHom.oneFormMap_comp_oneFormMap (semiHom_secPull hφ p.unop) (Λ'.semi (Opposite.op p.unop.1.1)) ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1)))
        (fun _ ↦ rfl) ω).symm)

theorem movedDatum_compatibleTwoFormClass (p : (Pair φ)ᵒᵖ) (ω : Om D.R (Sec D.s p.unop.1.2.1) 2) :
    ((pairB Λ' φ m).pre θ).a2 p (j2 Λ (Opposite.op p.unop.1.2) ω) =
      j2 Λ' (Opposite.op p.unop.1.1) ((semiHom_secPull hφ p.unop).mOm 2 ω) := by
  exact congrArg Submodule.Quotient.mk
    (((congrArg ((morSemi m ((pairFst φ ⋙ Λ'.L).obj p)).mOm 2) (SemiHom.mOm_mOm (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (fun _ ↦ rfl) ω)).trans
      (SemiHom.mOm_mOm ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (morSemi m ((pairFst φ ⋙ Λ'.L).obj p))
        ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1))) (fun b ↦ hθ p b) ω)).trans
      (SemiHom.mOm_mOm (semiHom_secPull hφ p.unop) (Λ'.semi (Opposite.op p.unop.1.1)) ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1)))
        (fun _ ↦ rfl) ω).symm)

end Pull

section Pairs

variable {D D' : Data} (Λ' : Lift D') (φ : D'.X ⟶ D.X)

abbrev Kp : Cx (Pair φ)ᵒᵖ := (KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)

def i0 (p : (Pair φ)ᵒᵖ) : (OPair φ D'.s).obj p →+ (Kp Λ' φ).M0.obj p :=
  (Λ'.e ((pairFst φ).obj p)).toAddEquiv.toAddMonoidHom

def i1 (p : (Pair φ)ᵒᵖ) : Ω[(OPair φ D'.s).obj p⁄D'.R] →+ (Kp Λ' φ).M1.obj p := j1 Λ' ((pairFst φ).obj p)

def i2 (p : (Pair φ)ᵒᵖ) : Om D'.R ((OPair φ D'.s).obj p) 2 →+ (Kp Λ' φ).M2.obj p := j2 Λ' ((pairFst φ).obj p)

variable {φ}

theorem pairFirstOpenFunctionSections_natural {p q : (Pair φ)ᵒᵖ} (a : p ⟶ q) (x : (OPair φ D'.s).obj p) :
    i0 Λ' φ q (mp (OPair φ D'.s) a x) = (Kp Λ' φ).M0.map a (i0 Λ' φ p x) := Λ'.nat ((pairFst φ).map a) x

theorem pairFirstOpenOneForms_natural {p q : (Pair φ)ᵒᵖ} (a : p ⟶ q) (x : Ω[(OPair φ D'.s).obj p⁄D'.R]) :
    i1 Λ' φ q (p1 (OPair φ D'.s) a x) = (Kp Λ' φ).M1.map a (i1 Λ' φ p x) := compatibleOneFormClass_restriction_natural Λ' ((pairFst φ).map a) x

theorem pairFirstOpenOneForms_kaehler_differential (p : (Pair φ)ᵒᵖ) (x : (OPair φ D'.s).obj p) :
    i1 Λ' φ p (KaehlerDifferential.D D'.R _ x) = (Kp Λ' φ).d0 p (i0 Λ' φ p x) := compatibleOneFormClass_kaehler_differential Λ' _ x

theorem pairFirstOpenTwoForms_exterior_derivative (p : (Pair φ)ᵒᵖ) (x : Ω[(OPair φ D'.s).obj p⁄D'.R]) :
    i2 Λ' φ p (dOne D'.R _ x) = (Kp Λ' φ).d1 p (i1 Λ' φ p x) := compatibleTwoFormClass_exterior_derivative Λ' _ x

def Cor (k : (Kp Λ' φ).T2) (w : Tot2 (OPair φ D'.s)) : Prop :=
  (∀ p q r a b, i0 Λ' φ r (w.1 p q r a b) = k.1 p q r a b) ∧ (∀ p q a, i1 Λ' φ q (w.2.1 p q a) = k.2.1 p q a) ∧
    ∀ p, i2 Λ' φ p (w.2.2 p) = k.2.2 p

theorem Cor.sub {k k' : (Kp Λ' φ).T2} {w w' : Tot2 (OPair φ D'.s)} (h : Cor Λ' k w) (h' : Cor Λ' k' w') :
    Cor Λ' (k - k') (w - w') := by
  unfold Cor at h h' ⊢
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, map_sub, h1, h1']
  · simp only [Prod.snd_sub, Prod.fst_sub, Pi.sub_apply, map_sub, h2, h2']
  · simp only [Prod.snd_sub, Pi.sub_apply, map_sub, h3, h3']

theorem deRhamCochainCorrespondence_degree_one_coboundary {g : (Kp Λ' φ).T1} {c : Tot1 (OPair φ D'.s)} (hf : ∀ p q a, i0 Λ' φ q (c.1 p q a) = g.1 p q a)
    (hω : ∀ p, i1 Λ' φ p (c.2 p) = g.2 p) : Cor Λ' ((Kp Λ' φ).D1 g) (dTot1 _ c) := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamTotalDifferentialOne_functionPart, map_add, map_sub, pairFirstOpenFunctionSections_natural, hf, hf, hf]
    all_goals rfl
  · rw [dTot1_a, map_sub, map_sub, hω, pairFirstOpenOneForms_natural, hω, pairFirstOpenOneForms_kaehler_differential, hf]
    all_goals rfl
  · rw [dTot1_η, pairFirstOpenTwoForms_exterior_derivative, hω]
    all_goals rfl

theorem Cor.unique {k : (Kp Λ' φ).T2} {w w' : Tot2 (OPair φ D'.s)} (h : Cor Λ' k w) (h' : Cor Λ' k w') : w = w' := by
  unfold Cor at h h'
  have e0 : ∀ p, Function.Injective (i0 Λ' φ p) := fun p ↦ (Λ'.e _).injective
  have e1 : ∀ p, Function.Injective (i1 Λ' φ p) := fun p ↦ (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' _).1.1
  have e2 : ∀ p, Function.Injective (i2 Λ' φ p) := fun p ↦ (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' _).2.1
  exact Tot2.ext (fun p q r a b ↦ e0 r ((h.1 p q r a b).trans (h'.1 p q r a b).symm))
    (fun p q a ↦ e1 q ((h.2.1 p q a).trans (h'.2.1 p q a).symm))
    (fun p ↦ e2 p ((h.2.2 p).trans (h'.2.2 p).symm))

theorem cor_res {k' : (KK D'.κ D'.t).T2} {w' : Tot2 (OAff D'.s)}
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k') w') :
    Cor Λ' (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k') (pullTot2 (pairRes φ D'.s) w') := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamPullbackTotalDegreeTwo_function_part]
    exact (hw'.1 _ _ _ _ _).symm
  · rw [pullTot2_a]
    exact (congrArg (i1 Λ' φ q) (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff D'.s) (pairFst φ) q _)).trans (hw'.2.1 _ _ _).symm
  · rw [pullTot2_η]
    exact (congrArg (i2 Λ' φ p) (qOm_restrict (OAff D'.s) (pairFst φ) p _)).trans (hw'.2.2 _).symm

theorem cor_pull (Λ : Lift D) {σ : D.R →+* D'.R} {φ₀ : D'.X₀ ⟶ D.X₀}
    (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    {k : (KK D.κ D.t).T2} {w : Tot2 (OAff D.s)} (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k) w) :
    Cor Λ' (((pairB Λ' φ m).pre θ).p2 k) (pullTot2 (pairPull hφ) w) := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamPullbackTotalDegreeTwo_function_part]
    refine (hθ r _).symm.trans ?_
    exact congrArg (fun y ↦ (θ.app r).φ y) (hw.1 _ _ _ _ _).symm
  · rw [pullTot2_a]
    refine (movedDatum_compatibleOneFormClass (Λ := Λ) (Λ' := Λ') (hφ := hφ) (m := m) (θ := θ) (hθ := hθ) q _).symm.trans ?_
    exact congrArg _ (hw.2.1 _ _ _).symm
  · rw [pullTot2_η]
    refine (movedDatum_compatibleTwoFormClass (Λ := Λ) (Λ' := Λ') (hφ := hφ) (m := m) (θ := θ) (hθ := hθ) p _).symm.trans ?_
    exact congrArg _ (hw.2.2 _).symm

theorem exists_deRhamCochainCorrespondence_degree_one (g : (Kp Λ' φ).T1) : ∃ c : Tot1 (OPair φ D'.s), Cor Λ' ((Kp Λ' φ).D1 g) (dTot1 _ c) := by
  obtain ⟨c1, hc1⟩ : ∃ c1 : ∀ (p q : (Pair φ)ᵒᵖ) (_ : p ⟶ q), (OPair φ D'.s).obj q,
      ∀ p q a, i0 Λ' φ q (c1 p q a) = g.1 p q a :=
    ⟨fun p q a ↦ (Λ'.e _).symm (g.1 p q a), fun p q a ↦ (Λ'.e _).apply_symm_apply _⟩
  choose c2 hc2 using fun p ↦ (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' ((pairFst φ).obj p)).1.2 (g.2 p)
  exact ⟨(c1, c2), deRhamCochainCorrespondence_degree_one_coboundary Λ' (c := (c1, c2)) hc1 hc2⟩

set_option maxHeartbeats 1000000 in
private theorem isPull2_aux_lemma (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    (k : (KK D.κ D.t).Z2) (k' : (KK D'.κ D'.t).Z2) (w : cechDeRhamTotalCocyclesTwo (OAff D.s)) (w' : cechDeRhamTotalCocyclesTwo (OAff D'.s))
    (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1) w.1)
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k'.1) w'.1)
    (g : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).T1)
    (hg : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D1 g = ((pairB Λ' φ m).pre θ).p2 k.1 -
      ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) :
    IsPull2 hφ (Hyp2.mk _ w) (Hyp2.mk _ w') := by
  have h1 := cor_pull Λ' Λ hφ m θ hθ hw
  have h2 := cor_res Λ' (φ := φ) hw'
  obtain ⟨c, hc⟩ := exists_deRhamCochainCorrespondence_degree_one Λ' g
  rw [hg] at hc
  have h3 := Cor.unique Λ' hc (Cor.sub Λ' h1 h2)
  unfold IsPull2
  rw [pullHyp2_mk, pullHyp2_mk, Hyp2.mk_eq_mk]
  refine ⟨c, ?_⟩
  rw [coe_pullZZ2, coe_pullZZ2]
  exact h3

end Pairs

theorem isPull2_of_coboundary (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    (k : (KK D.κ D.t).Z2) (k' : (KK D'.κ D'.t).Z2) (w : cechDeRhamTotalCocyclesTwo (OAff D.s)) (w' : cechDeRhamTotalCocyclesTwo (OAff D'.s))
    (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1) w.1)
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k'.1) w'.1)
    (g : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).T1)
    (hg : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D1 g = ((pairB Λ' φ m).pre θ).p2 k.1 -
      ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) :
    IsPull2 hφ (Hyp2.mk _ w) (Hyp2.mk _ w') := isPull2_aux_lemma D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' g hg

end GlobalTheory.PDForm.PullTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaRingRegularAtExtensionPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deeperThetaRing_regular_at_extension_point : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective io → 𝔗.Ext ev io ev₂ → RegAt X₁ z₁ ev → RegAt 𝔗.X₂ z₂ ev₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Tower.regAt | exact GlobalTheory.Poinc.Sep.Tower.regAt | (intros; apply GlobalTheory.Poinc.Sep.Tower.regAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaValueGaloisConjugateExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deeperTheta_value_galoisConjugate_extension : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₂ : 𝔗.X₂.M.Z} {V' : Type} [CommRing V'] [IsDomain V'] (ev₂ ev₂' : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → RegAt 𝔗.X₂ z₂ ev₂ → RegAt 𝔗.X₂ z₂ ev₂' → ∀ a : 𝔗.X₂.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) a = 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.sR σ a) := by
  first | exact @GlobalTheory.Poinc.Sep.val_galois_conj | exact GlobalTheory.Poinc.Sep.val_galois_conj | (intros; apply GlobalTheory.Poinc.Sep.val_galois_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaValueImageEqImageValueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deeperTheta_value_image_eq_image_value : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → 𝔗.Ext ev io ev₂ → RegAt X₁ z₁ ev → ∀ a : X₁.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.om a) = f (X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) := by
  first | exact @GlobalTheory.Poinc.Sep.Tower.val_om_ext | exact GlobalTheory.Poinc.Sep.Tower.val_om_ext | (intros; apply GlobalTheory.Poinc.Sep.Tower.val_om_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleThetaKernelLeftRationalInvarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottomTriple_thetaKernel_left_rational_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ (t : T) (P : PolF D WW.rank A.rank) (h : Formalism.L2.Theta.GA D WW),
    ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t P h (γ * g) = X.ker W.ψ W.θ t P h g := by
  first | exact @GlobalTheory.ClassSumLeft.ker_left_rat | exact GlobalTheory.ClassSumLeft.ker_left_rat | (intros; apply GlobalTheory.ClassSumLeft.ker_left_rat <;> assumption)
end

