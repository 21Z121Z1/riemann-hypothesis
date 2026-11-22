import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinors
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0310
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0317
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGVolMt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrime
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0312
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermNormsGeOneAndBounded
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PairsLab

theorem norms_of_relevant : ∀ (Cg cb Cw cT CT C0 CH C' Cl : ℝ), 0 ≤ CH → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word), HostC → NFExC → LabC → TermC → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
    ∀ t ∈ relSet Y u, 1 ≤ k2Del D (jT t) (labT t) ∧ 1 ≤ DbL D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 ∧
      DbL D (jT t) (labT t) ≤ (Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2) ^ D.R.rS := by
  intro Cg cb Cw cT CT C0 CH C' Cl hCH D large₂ X Y u hHost hNF hLab hTerm hH t ht
  have hS : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := hHost D large₂ hS
  obtain ⟨N, hN, hNj, hNT⟩ := hNF D large₂ X Y u hS t ht
  have hT : N.IsTerm (gS D) t.lam := hTerm D large₂ X Y u hS t N hN
  obtain ⟨-, -, hDel, hDb, -⟩ := hLab D large₂ X Y u hS t N hN
  obtain ⟨𝔠, -, hDb1, hDel1, -⟩ := GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal D.host.E (VS D).V (HV D) hK D.R.rS N (gS D)
    t.lam (by omega) hT
  have hPF : PFHost D := PFHost_of_data D hH.1.2.1
  have hC : 2 * (CH + 1) ≤ 2 * (CH + 1) := le_rfl
  have hup := (delta_pos_le_height_sq hPF large₂ hCH hC t ht).2
  have hb := two_le_scale_b D large₂
  have hHb : (1 : ℝ) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f := by
    unfold Hb
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hS1 := one_le_sigma_product (D := D) (H1C large₂ CH) (jT t) (labT t)
  have hA : (1 : ℝ) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hHb (one_le_pow₀ hS1)
  refine ⟨hDel ▸ hDel1, hDb ▸ hDb1, hup, ?_⟩
  have hcard : (k2ends D (jT t) (labT t)).card ≤ D.R.rS := by
    unfold k2ends
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]
    unfold jT
    omega
  calc DbL D (jT t) (labT t)
      ≤ ∏ _l ∈ k2ends D (jT t) (labT t),
          Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
        unfold DbL
        refine Finset.prod_le_prod (fun l _ => ?_) (fun l hl => localNorm_le_height_sq hPF large₂ hCH hC t l hl)
        unfold Nloc
        exact_mod_cast FractionalIdeal.absNorm_nonneg _
    _ = _ ^ (k2ends D (jT t) (labT t)).card := Finset.prod_const _
    _ ≤ _ := pow_le_pow_right₀ hA hcard

end GlobalTheory.TypeAsm.PairsLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvUniqueAddSmulMulComm
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.WeakConv

section General

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (μ : Measure G) (π : G → (H →L[ℂ] H))

def IsWeakInt (e : G → ℂ) (T : H →L[ℂ] H) : Prop :=
  Integrable e μ ∧ ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ

variable {μ π}

private theorem integrable_mul_of_bounded {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f c : α → ℂ} (hf : Integrable f ν) (hc : AEStronglyMeasurable c ν) (C : ℝ)
    (hb : ∀ a, ‖c a‖ ≤ C) : Integrable (fun a => f a * c a) ν := by
  refine Integrable.mono' (hf.norm.mul_const C) (hf.aestronglyMeasurable.mul hc) (ae_of_all _ fun a => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb a) (norm_nonneg _)

omit [Group G] [IsTopologicalGroup G] [SecondCountableTopology G] [CompleteSpace H] in

theorem integrable_mul_coeff (hn : ∀ g y, ‖π g y‖ = ‖y‖) (hc : ∀ y, Continuous fun g => π g y)
    {e : G → ℂ} (he : Integrable e μ) (x y : H) :
    Integrable (fun g => e g * ⟪x, π g y⟫_ℂ) μ := by
  have hcm : Continuous fun g => ⟪x, π g y⟫_ℂ := continuous_const.inner (hc y)
  refine integrable_mul_of_bounded he hcm.aestronglyMeasurable (‖x‖ * ‖y‖) fun g => ?_
  calc ‖⟪x, π g y⟫_ℂ‖ ≤ ‖x‖ * ‖π g y‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [hn]

omit [Group G] [IsTopologicalGroup G] [SecondCountableTopology G] [TopologicalSpace G] [BorelSpace G] in

theorem IsWeakInt.inner_comp {e : G → ℂ} {T : H →L[ℂ] H} (h : IsWeakInt μ π e T) (A : H →L[ℂ] H)
    (x y : H) : ⟪x, A (T y)⟫_ℂ = ∫ g, e g * ⟪x, A (π g y)⟫_ℂ ∂μ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, h.2]
  simp_rw [ContinuousLinearMap.adjoint_inner_left]

theorem IsWeakInt.conv [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (hm : ∀ g h, π (g * h) = (π g).comp (π h))
    (hn : ∀ g y, ‖π g y‖ = ‖y‖) (hc : ∀ y, Continuous fun g => π g y)
    {e e' : G → ℂ} {T T' : H →L[ℂ] H} (h : IsWeakInt μ π e T) (h' : IsWeakInt μ π e' T') :
    IsWeakInt μ π (fun k => ∫ g, e g * e' (g⁻¹ * k) ∂μ) (T.comp T') := by
  have hP : Integrable (fun z : G × G => e z.1 * e' (z.1⁻¹ * z.2)) (μ.prod μ) := by
    have h0 : Integrable (fun z : G × G => e z.1 * e' z.2) (μ.prod μ) := h.1.mul_prod h'.1
    exact ((measurePreserving_prod_inv_mul μ μ).integrable_comp h0.aestronglyMeasurable).2 h0
  refine ⟨hP.integral_prod_right, fun x y => ?_⟩
  have hcm : Continuous fun k => ⟪x, π k y⟫_ℂ := continuous_const.inner (hc y)
  have hcm2 : Measurable fun z : G × G => ⟪x, π z.2 y⟫_ℂ := hcm.measurable.comp measurable_snd
  have hQ : Integrable (fun z : G × G => e z.1 * e' (z.1⁻¹ * z.2) * ⟪x, π z.2 y⟫_ℂ) (μ.prod μ) := by
    refine integrable_mul_of_bounded hP hcm2.aestronglyMeasurable (‖x‖ * ‖y‖) fun z => ?_
    calc ‖⟪x, π z.2 y⟫_ℂ‖ ≤ ‖x‖ * ‖π z.2 y‖ := norm_inner_le_norm _ _
      _ = ‖x‖ * ‖y‖ := by rw [hn]
  have hin : ∀ g, ⟪x, π g (T' y)⟫_ℂ = ∫ k, e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ := by
    intro g
    rw [h'.inner_comp (π g) x y]
    refine (integral_mul_left_eq_self _ g⁻¹).symm.trans ?_
    congr 1
    ext k
    have hk : π g (π (g⁻¹ * k) y) = π k y := by
      rw [← ContinuousLinearMap.comp_apply, ← hm, mul_inv_cancel_left]
    simp only [hk]
  calc ⟪x, (T.comp T') y⟫_ℂ = ∫ g, e g * ⟪x, π g (T' y)⟫_ℂ ∂μ := h.2 x (T' y)
    _ = ∫ g, ∫ k, e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ ∂μ := by
        congr 1
        ext g
        rw [hin, ← integral_const_mul]
        congr 1
        ext k
        ring
    _ = ∫ k, ∫ g, e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ ∂μ :=
        integral_integral_swap (f := fun g k => e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ) hQ
    _ = ∫ k, (∫ g, e g * e' (g⁻¹ * k) ∂μ) * ⟪x, π k y⟫_ℂ ∂μ := by
        congr 1
        ext k
        rw [integral_mul_const]

end General

theorem rightConv_unique_add_smul_mul_comm : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)), I.IsFundDom (I.muA μf) fund → I.IsRightReg μf fund R → (∀ e T T', I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e T' → T = T') ∧ (∀ e e' T T', I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e' T' → I.IsRConvF μf fund R (e + e') (T + T')) ∧ (∀ (c : ℂ) e T, I.IsRConvF μf fund R e T → I.IsRConvF μf fund R (c • e) (c • T)) ∧ (∀ e e' T T', Continuous e → Continuous e' → I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e' T' → I.IsRConvF μf fund R (I.convF μf e e') (T.comp T')) ∧ ∀ e T (x : I.Ginf), I.IsRConvF μf fund R e T → T.comp (R (x, 1)) = (R (x, 1)).comp T := by
  intro I μf hH hS fund R hfund hR
  obtain ⟨-, hmul, hn, hc⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous I μf fund hfund R hR
  have := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I
  have hm' : ∀ g h : I.Gf, R (1, g * h) = (R (1, g)).comp (R (1, h)) := by
    intro g h
    rw [← hmul, Prod.mk_mul_mk, one_mul]
  have hn' : ∀ (g : I.Gf) (F : I.L2 μf fund), ‖R (1, g) F‖ = ‖F‖ := fun g F => hn _ F
  have hc' : ∀ F : I.L2 μf fund, Continuous fun g : I.Gf => R (1, g) F := fun F =>
    Continuous.comp (g := fun x : I.GA => R x F) (f := fun g : I.Gf => ((1 : I.Ginf), g)) (hc F)
      (continuous_const.prodMk continuous_id)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e T T' h h'
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun z => ?_
    rw [h.2, h'.2]
  · intro e e' T T' h h'
    refine ⟨h.1.add h'.1, fun z y => ?_⟩
    have i1 := integrable_mul_coeff (μ := μf) (π := fun g : I.Gf => R (1, g)) hn' hc' h.1 z y
    have i2 := integrable_mul_coeff (μ := μf) (π := fun g : I.Gf => R (1, g)) hn' hc' h'.1 z y
    rw [ContinuousLinearMap.add_apply, inner_add_right, h.2, h'.2, ← integral_add i1 i2]
    congr 1
    ext g
    simp only [Pi.add_apply]
    ring
  · intro c e T h
    refine ⟨h.1.smul c, fun z y => ?_⟩
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, h.2, ← integral_const_mul]
    congr 1
    ext g
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro e e' T T' _ _ h h'
    exact IsWeakInt.conv (μ := μf) (π := fun g : I.Gf => R (1, g)) hm' hn' hc' h h'
  · intro e T x h
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun z => ?_
    have hcomm : ∀ g : I.Gf, R (1, g) (R (x, 1) y) = R (x, 1) (R (1, g) y) := by
      intro g
      have key : R ((1, g) * (x, 1)) = R ((x, 1) * (1, g)) := by
        congr 1
        simp
      rw [hmul, hmul] at key
      exact congrArg (fun A : I.L2 μf fund →L[ℂ] I.L2 μf fund => A y) key
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h.2 z (R (x, 1) y),
      IsWeakInt.inner_comp (μ := μf) (π := fun g : I.Gf => R (1, g)) h (R (x, 1)) z y]
    simp only [hcomm]

end GlobalTheory.WeakConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
section
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

namespace GlobalTheory.RightRegFund

theorem isRightReg_props (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (hR : I.IsRightReg μf fund R) :
    R 1 = 1 ∧ (∀ g h, R (g * h) = R g * R h) ∧ (∀ g F, ‖R g F‖ = ‖F‖) ∧
      (∀ F, Continuous fun g => R g F) ∧ ∀ F : I.L2 μf fund,
        (∀ᵐ y ∂(I.muA μf), ∀ γ ∈ I.GFset, I.ext F (γ * y) = I.ext F y) ∧
          AEStronglyMeasurable (I.ext F) (I.muA μf) := by
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.T.finiteAdelicUnitary_congruenceTopology I
  obtain ⟨Γ, hΓ, hc, -, hfd⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain I
  obtain ⟨hl, hrt, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant I μf
  have hD := hfd μf fund hfund
  have : BorelSpace I.GA := inferInstance
  have : (I.muA μf).IsMulLeftInvariant := ⟨hl⟩
  have : (I.muA μf).IsMulRightInvariant := ⟨hrt⟩
  have : IsFiniteMeasureOnCompacts (I.muA μf) := by
    unfold AutInst.muA; infer_instance
  have hr : ∀ y, ∃ γ : Γ, I.rep fund y = (γ : I.GA) * y ∧ I.rep fund y ∈ fund := by
    intro y
    have h := hfund.2.1 y
    have e : I.rep fund y = h.choose * y := by
      unfold AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  refine ⟨map_one hD hfund.1 hr hR, map_mul hD hfund.1 hr hR, norm_map hD hfund.1 hr hR,
    continuous_map hD hfund.1 hr hR, fun F => ⟨?_, ?_⟩⟩
  · refine (ae_good hD).mono fun y hy γ hγ => ?_
    have hm : γ ∈ (Γ : Set I.GA) := hΓ ▸ hγ
    unfold AutInst.ext
    rw [rep_mul hr hy ⟨γ, hm⟩]
  · exact aestronglyMeasurable_comp_rep hD hfund.1 hr (Lp.stronglyMeasurable F)

theorem rightReg_unitary_continuous : ∀ B : RowsAut, B.R 1 = 1 ∧ (∀ g h, B.R (g * h) = B.R g * B.R h) ∧ (∀ g F, ‖B.R g F‖ = ‖F‖) ∧ (∀ F, Continuous fun g => B.R g F) ∧ ∀ F : B.I.L2 B.μf B.fund, (∀ᵐ y ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, B.I.ext F (γ * y) = B.I.ext F y) ∧ AEStronglyMeasurable (B.I.ext F) (B.I.muA B.μf) :=
  fun B => isRightReg_props B.I B.μf B.fund B.fund_spec B.R B.R_spec

end GlobalTheory.RightRegFund
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuousStatement
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightRegularRepresentation_unitary_mul_continuous : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → R 1 = ContinuousLinearMap.id ℂ _ ∧ (∀ x y, R (x * y) = (R x).comp (R y)) ∧ (∀ x F, ‖R x F‖ = ‖F‖) ∧ ∀ F, Continuous fun x => R x F := by
  first | exact @GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous | exact GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous | (intros; apply GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesEqOfAdaptedIsometryInnerLatticesEqStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLattices_eq_of_adaptedIsometry_innerLattices_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (v : D.what₂.Word) (B : LFlag (VS D) D.R.rS ((Tu D v : ℕ) : D.host.E)) (ψ₀ ψ₁ : GV D) (Λa Λb : LV D), Λa ∈ Y.what₂ v → Λb ∈ Y.what₂ v → Adapt ψ₀ (lf D (X.Fu v)) B → Adapt ψ₁ (lf D (X.Fu v)) B → Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ Λa) B = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ Λb) B → Λb = Λa ∧ ∃ n ∈ NRat (lf D (X.Fu v)), n * (ψ₁⁻¹ * ψ₀) ∈ Aut0 (lf D (X.Fu v)) Λa := by
  first | exact @GlobalTheory.Unfold.SideEq.side | exact GlobalTheory.Unfold.SideEq.side | (intros; apply GlobalTheory.Unfold.SideEq.side <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigRMemOAd
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.IotaConj

theorem sigR_inclE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (x : E) :
    sigR σ R (inclE (F := F) R x) = inclE (F := F) R (σ x) := by
  simp [sigR, inclE]

theorem sigR_mem_OAd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {a : E ⊗[F] Ad F} (ha : a ∈ OAd F E) : sigR σ (Ad F) a ∈ OAd F E := by

  have key : OAd F E ≤ (OAd F E).comap (sigR σ (Ad F)) := by
    show tensInt (F := F) (Ad F) (intOE E) (intAd F) ≤
      (tensInt (F := F) (Ad F) (intOE E) (intAd F)).comap (sigR σ (Ad F))
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := hx
      have hint : IsIntegral ℤ (σ (algebraMap (𝓞 E) E z)) :=
        (RingOfIntegers.isIntegral_coe z).map (σ : E →+* E).toIntAlgHom
      refine Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E z), ⟨⟨_, hint⟩, rfl⟩⟩, ?_⟩)
      simp [sigR]
    · refine Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)
      simp [sigR]
  exact key ha

theorem iota_sigR (F E F' E' : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E']
    (σ : E →ₐ[F] E) (σ' : E' →ₐ[F'] E') (e : E ≃+* E') (ι : E ⊗[F] Ad F ≃+* E' ⊗[F'] Ad F')
    (he : ∀ x, e (σ x) = σ' (e x))
    (hι : ∀ x, ι (inclE (F := F) (Ad F) x) = inclE (F := F') (Ad F') (e x))
    (hO : ∀ a, a ∈ OAd F E ↔ ι a ∈ OAd F' E') (a : E ⊗[F] Ad F) :
    ι (sigR σ (Ad F) a) = sigR σ' (Ad F') (ι a) := by
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F E
  obtain ⟨-, -, h3', -, -⟩ := GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F' E'

  set D : E ⊗[F] Ad F → E' ⊗[F'] Ad F' :=
    fun b => ι (sigR σ (Ad F) b) - sigR σ' (Ad F') (ι b) with hD
  have Dadd : ∀ b c, D (b + c) = D b + D c := by
    intro b c; simp only [hD, map_add]; abel
  have Dmul : ∀ (m : ℕ) b, D ((m : E ⊗[F] Ad F) * b) = (m : E' ⊗[F'] Ad F') * D b := by
    intro m b; simp only [hD, map_mul, map_natCast]; ring
  have Dincl : ∀ x : E, D (inclE (F := F) (Ad F) x) = 0 := by
    intro x; simp only [hD, sigR_inclE, hι, he, sub_self]
  have DO : ∀ b ∈ OAd F E, D b ∈ OAd F' E' := by
    intro b hb
    exact Subring.sub_mem _ ((hO _).1 (sigR_mem_OAd σ hb)) (sigR_mem_OAd σ' ((hO _).1 hb))
  have Dzero : ∀ b ∈ OAd F E, D b = 0 := by
    intro b hb
    refine h3' (D b) fun m hm => ?_
    obtain ⟨x, t, ht, hbt⟩ := h2 b hb m hm
    exact ⟨D t, DO t ht, by rw [hbt, Dadd, Dincl, Dmul, zero_add]⟩
  obtain ⟨m, hm, hma⟩ := h4 a
  have h0 : (m : E' ⊗[F'] Ad F') * D a = 0 := by rw [← Dmul]; exact Dzero _ hma
  have hu : IsUnit (m : E' ⊗[F'] Ad F') := by
    rw [← map_natCast (inclE (F := F') (E := E') (Ad F')) m]
    exact (IsUnit.mk0 (m : E') (Nat.cast_ne_zero.2 hm.ne')).map _
  have hDa : D a = 0 := hu.mul_right_eq_zero.1 h0
  simp only [hD] at hDa
  exact sub_eq_zero.1 hDa

end GlobalTheory.St.G.IotaConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasure
section
noncomputable section

namespace GlobalTheory.GaugeKExists

theorem gaugeK : PI.RhsWLim.W.GaugeK := by
  intro k r _
  exact ⟨Formalism.L2.SG.Pf.GV.nu0 k r, Formalism.L2.SG.Pf.GV.gauge_measure_is_gauge⟩

end GlobalTheory.GaugeKExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrimeStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdditiveCharacter_local_ne_one_splitPrime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∀ x : E, psi (inclE (F := F) (Ad F) x) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ)) = 1) → ∀ (p : ℕ), p.Prime → SplitsIn E p → ∀ (v : HeightOneSpectrum (𝓞 F)), (p : 𝓞 F) ∈ v.asIdeal → ∀ e ∈ intV E v, e * e = e → e ≠ 0 → ∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((p : F)⁻¹) * (e * a))) ≠ 1 := by
  first | exact @GlobalTheory.St.G.psi_local_ne_one | exact GlobalTheory.St.G.psi_local_ne_one | (intros; apply GlobalTheory.St.G.psi_local_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdGaugeMeasuresGaugeBody
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConstBox

theorem local_vag {n d : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (h : IsCut ε S E) (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub S d μ) :
    SigmaFinite μ ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      IsFiniteMeasure (μ.restrict {g | nrm (uMat g - 1) < t}) ∧
      Vag (μ.restrict {g | nrm (uMat g - 1) < t}) (fun g => crd E (uMat g - 1)) volume d := by
  obtain ⟨A, hA, hON, hspan, rfl⟩ := h
  obtain ⟨hσ, hcpt, -, r₀, hr₀, hlim⟩ := GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hON hspan μ hμ
  refine ⟨hσ, Real.sqrt r₀, Real.sqrt_pos.2 hr₀, fun t ht htt => ⟨?_, ?_⟩⟩
  ·
    refine isFiniteMeasure_restrict.2 (ne_of_lt ?_)
    refine lt_of_le_of_lt (measure_mono ?_) (isCompact_hsBall ε t).measure_lt_top
    intro g hg
    exact (show nrm (uMat g - 1) < t from hg).le
  ·
    intro φ hφ hsupp
    have hset : {g : Formalism.REAL.UJ ε | nrm (uMat g - 1) < t} =
        {g | Formalism.REAL.hs (uMat g - 1) < t ^ 2} := by
      ext g
      exact Real.sqrt_lt' ht
    have h1 : 0 < t ^ 2 := by positivity
    have h2 : t ^ 2 ≤ r₀ := by
      calc t ^ 2 ≤ Real.sqrt r₀ ^ 2 := pow_le_pow_left₀ ht.le htt 2
        _ = r₀ := Real.sq_sqrt hr₀.le
    rw [hset]
    refine (hlim (t ^ 2) h1 h2 φ hφ hsupp).congr (fun r => ?_)
    congr 2
    funext g
    congr 1
    funext i
    simp only [crd, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

theorem prod_gauge_body : ∀ (n : ℕ) (ε : Fin n → Bool) (SN SM MainNotions : Set (Formalism.REAL.UJ ε)), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε SN EN → IsCut ε SM EM → IsCut ε MainNotions EK → (∀ v, gau EN EM EK EL v = 0 → v = 0) → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub SN dN μN → IsGaugeSub SM dM μM → IsGaugeSub MainNotions dK μK → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → Filter.Tendsto (fun r : ℝ => (μN.prod (μM.prod μK)) {x | (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧ gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ r} / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  intro n ε SN SM MainNotions dN dM dK dL EN EM EK EL hN hM hK hgau μN μM μK hμN hμM hμK
  obtain ⟨hσN, tN, htN, hN'⟩ := local_vag hN μN hμN
  obtain ⟨hσM, tM, htM, hM'⟩ := local_vag hM μM hμM
  obtain ⟨hσK, tK, htK, hK'⟩ := local_vag hK μK hμK
  refine ⟨min tN (min tM tK), lt_min htN (lt_min htM htK), fun t ht htt => ?_⟩
  obtain ⟨fN, vN⟩ := hN' t ht (htt.trans (min_le_left _ _))
  obtain ⟨fM, vM⟩ := hM' t ht (htt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨fK, vK⟩ := hK' t ht (htt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  set s : Set (Formalism.REAL.UJ ε) := {g | nrm (uMat g - 1) < t} with hs
  have hsm : MeasurableSet s := (continuous_nrm_uMat ε).measurable measurableSet_Iio
  have mc : ∀ {e : ℕ} (E : Fin e → Matrix (Fin n) (Fin n) ℂ),
      Measurable fun g : Formalism.REAL.UJ ε => crd E (uMat g - 1) :=
    fun E => (continuous_crd_uMat ε E).measurable

  have vMK := GlobalTheory.T.vague_limit_rescaled_measures_prod _ _ _ _ (μM.restrict s) (μK.restrict s) (fun g => crd EM (uMat g - 1))
    (fun g => crd EK (uMat g - 1)) volume volume dM dK (mc EM) (mc EK) vM vK
  have vNMK := GlobalTheory.T.vague_limit_rescaled_measures_prod _ _ _ _ (μN.restrict s) ((μM.restrict s).prod (μK.restrict s))
    (fun g => crd EN (uMat g - 1)) (Prod.map (fun g => crd EM (uMat g - 1)) (fun g => crd EK (uMat g - 1)))
    volume (volume.prod volume) dN (dM + dK) (mc EN) (Measurable.prodMap (mc EM) (mc EK)) vN vMK
  have h2 : (volume.prod volume : Measure ((Fin dM → ℝ) × (Fin dK → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have h3 : (volume.prod (volume.prod volume) :
      Measure ((Fin dN → ℝ) × (Fin dM → ℝ) × (Fin dK → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have key := GlobalTheory.T.tendsto_rescaled_measure_gauge_unit_body _ _ ((μN.restrict s).prod ((μM.restrict s).prod (μK.restrict s)))
    (Prod.map (fun g => crd EN (uMat g - 1))
      (Prod.map (fun g => crd EM (uMat g - 1)) (fun g => crd EK (uMat g - 1))))
    (volume.prod (volume.prod volume)) (dN + (dM + dK)) (gau EN EM EK EL)
    (Measurable.prodMap (mc EN) (Measurable.prodMap (mc EM) (mc EK))) (continuous_gau EN EM EK EL)
    (gau_nonneg EN EM EK EL) (fun c hc v => gau_smul EN EM EK EL c hc v) hgau vNMK
  refine key.congr (fun r => ?_)
  congr 1
  rw [Measure.prod_restrict, Measure.prod_restrict,
    Measure.restrict_apply' (hsm.prod (hsm.prod hsm))]
  congr 1
  ext ⟨a, b, c⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, Prod.map_apply, hs]
  tauto

end GlobalTheory.IwConstBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzPropertiesStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties : TauLip := by
  first | exact @GlobalTheory.TauLipschitz.tauLip | exact GlobalTheory.TauLipschitz.tauLip | (intros; apply GlobalTheory.TauLipschitz.tauLip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedAdditiveCharacterConductor
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocalDensityValue

def placeHom (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Fv F v →+ AF F :=
  (AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom

theorem continuous_placeHom (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (placeHom F v) :=
  Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v)

def localChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (placeHom F v)

theorem coe_localChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) : (localChar F ψ v : Fv F v → ℂ) = psiV F ψ v := rfl

theorem isLocalChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) (v : HeightOneSpectrum (𝓞 F)) (m : ℤ)
    (hm : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.IsLocalChar F v (localChar F ψ v) := by
  refine ⟨hψ.1.comp (continuous_placeHom F v), fun t => hψ.2.1 _, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (m + 1))
  have := (hm t).1 fun s _ => h _
  rw [ht, WithZero.exp_le_exp] at this
  omega

end GlobalTheory.LocalDensityValue
end
end

