import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0163
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0162
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0130
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnReal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0153
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0157
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0141
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0146
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0189
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0319
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0194
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0266
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRDatumConst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0317
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0114
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0115
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0125
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0123
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0126
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPPSCalc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerUnipotentHasRepresentation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHPhaseInvOfCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHPhaseSec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0268
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0273
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0320
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFFormIdS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0318
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0316
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0306

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreDone
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTCRefTrace_of_rotK (h : GTRRotK) : GTCRefTrace :=
  gTCRefTrace_of_cutK radial_gauge_move radial_gauge_constant_holds top_normal_form_of_curvature top_action_on_gauge_holds h radial_gauge_integrality_holds radial_gauge_transition_holds gauge_reality_holds

theorem gTCRef_of_rotK (h : GTRRotK) : GTCRef :=
  gTCRef_of_cut gauge_reality_holds curvature_identity_holds curvature_trace_holds (gTCRefTrace_of_rotK h) reference_annulus_holds

theorem gTConn_of_rotK (h : GTRRotK) : GTConn :=
  gTConn_of_leaves gauge_locality_holds gauge_reality_holds (gTCCurv_of_ref (gTCRef_of_rotK h)) (gTCHol_of_ref (gTCRef_of_rotK h)) annulus_condition_holds

theorem genTransfer_of_rotK (h : GTRRotK) : GenTransfer :=
  genTransfer_of_cut GT.gauge_function_holds gauge_kappa_holds (gTConn_of_rotK h) second_shift_gauge_holds

theorem gCore_of_rotK (h : GTRRotK) : GCore := gCore_of_genTransfer (genTransfer_of_rotK h)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_rotK (hJ : JfSmoothDS) (hR : Gauge.GC.GTRRotK) (h : JA.SSn.SSnRep) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_ssnRep hJ (Gauge.GC.genTransfer_of_rotK hR) h

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRRest
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem phase_invariance_holds : PhaseInv :=
  PH.phase_invariance_of_truncation PH.phase_section_holds PH.lower_unipotent_rotation_holds PH.rotation_radial_space_holds PH.theta_rotation_holds kappa_line_holds algebraic_shift_holds
    datum_constancy_holds fibre_stability_holds

theorem corePoly_of (hD : CP.Decomp) (hW : CP.WordPSVOfCut) : CorePoly :=
  CP.radial_polynomial_of_truncation CP.lower_unipotent_matrix_words
    (hW CP.radial_coefficient_linearity CP.radial_coefficient_smoothness CP.radial_coefficient_commutation CP.left_covariance_holds CP.right_covariance_holds CP.section_derivative_holds hD
      CP.polynomial_shift_calculation)
    CP.polynomial_shift_calculation

theorem polyRadialS_of (hD : CP.Decomp) (hW : CP.WordPSVOfCut) : PolyRadialS :=
  polynomialRadial_of_base polynomial_radial_base_holds SSn.Rep.theta_facts_hold transfer_holds datum_constancy_holds kappa_line_holds
    fibre_stability_holds algebraic_shift_holds (corePoly_of hD hW) phase_invariance_holds phase_extraction_holds word_nonvanishing_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFMainS
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def flCutS (k r : ℕ) (n : ℕ) (g : B.Mat k r) : ℂ :=
  ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)

theorem domination_measurability_holds : NFDomMeas := by
  intro Cb
  obtain ⟨Cc, hFL⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  obtain ⟨hχ, hInD, hfck, hfcc, hA, -⟩ := hH
  have hck : B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) := by
    rw [fpm_id]; exact ckOn_Gpow_smul _ _ p₀ hfck
  obtain ⟨hcpt, hlim⟩ := hFL Wp Wq P p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) χ ε
    (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N (flCutS P.k P.r) hInD hχ hε hck (inCC_fpm_id p p₀ hfcc) hA
    (fun n g => rfl)
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n => topD p (fun g => flCutS P.k P.r n g •
      D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε g) w)
    (fun n => top_domination_measurable_compact Wp Wq P p _ w Cb hInD (hcpt n) hw.1) (ae_of_all _ fun c => ?_)
  have h := hlim (P.r + 1) w hw.1 hN (TBB.bigPt P.r c) (TBB.bigPt P.r c)
  unfold topD TBB.Ew TBB.NP
  exact (Complex.continuous_re.tendsto _).comp (h.const_mul _)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_main6 (hA : P5.ThmPActual) (hT : NFTieHatS) (hH : NFHatProdKBS) (hJC : NFJCutFF) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      B.JF p.T.base f ∈ FFKB p →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by

  have hTM : TopDMeasCpt := Formalism.FourierDecayAlt.P.CutBP.top_domination_measurable_compact

  have hCore : NFCoreNS := Formalism.FourierDecayAlt.P.CutBP.nFCoreNS_of_cut Formalism.FourierDecayAlt.P.CutBP.leibniz_vector_estimate_holds hT hH Formalism.FourierDecayAlt.P.CutBP.trace_norm_bound_constant_one Formalism.FourierDecayAlt.P.CutBP.operator_multiplication_admissible
  have hDP : NFDomPtwS := Formalism.FourierDecayAlt.P.CutBP.nfDomPtwS_of_cut Formalism.FourierDecayAlt.P.CutBP.unfolding_top_term_holds Formalism.FourierDecayAlt.P.CutBP.vector_multiplication_holds Formalism.FourierDecayAlt.P.CutBP.truncated_supremum_bound_holds
    Formalism.FourierDecayAlt.P.CutBP.leibniz_vector_estimate_holds hCore Formalism.FourierDecayAlt.P.CutBP.empty_operator_list_holds
  have hApx : NFApxDomAllS := Formalism.FourierDecayAlt.P.CutBP.nfApxDomAllS_of_cut Formalism.FourierDecayAlt.P.CutBP.domination_at_zero_holds hDP Formalism.FourierDecayAlt.P.CutBP.dominated_L2_truncation_bound_holds
  have hForm : NFTopFormAllS := Formalism.FourierDecayAlt.P.CutBP.nFTopFormAllS_of hTM hApx
  have hDom : NFTopDomAllS := Formalism.FourierDecayAlt.P.CutBP.nfTopDomAllS_of_cut Formalism.FourierDecayAlt.P.CutBP.domination_at_zero_holds hDP Formalism.FourierDecayAlt.P.CutBP.dominated_L2_operator_bound_holds domination_measurability_holds

  have hPQ : NFPolQuadAllS := Formalism.FourierDecayAlt.P.CutBP.nfPolQuadAllS_of hTM hApx
  have hPF : NFPolFormAllS := Formalism.FourierDecayAlt.P.CutBP.nfPolFormAllS_of hPQ Formalism.FourierDecayAlt.P.CutBP.pairing_middle_all_levels_holds Formalism.FourierDecayAlt.P.CutBP.top_middle_all_levels_holds
  have hId : NFTopIdAllS := Formalism.FourierDecayAlt.P.CutBP.nfTopIdAllS_of hA hDom hPF Formalism.FourierDecayAlt.P.CutBP.pairing_pointwise_all_levels_holds Formalism.FourierDecayAlt.P.CutBP.beta_limit_all_levels_holds
  exact Formalism.FourierDecayAlt.P.CutBP.thmBpAt_main5 hA hForm Formalism.FourierDecayAlt.P.CutBP.top_pointwise_all_levels_holds hDom hId hJC Cb C₃ CΛ C₀ hC₃ hCΛ hC₀

end

end Formalism.FourierDecayAlt.P.CutBP
end

