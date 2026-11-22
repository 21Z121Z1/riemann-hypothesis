import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramProductIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteOfEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialFlipCommuteDiagScalarOfFree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix
import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0021
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KroneckerEmbedMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QEFirstMulSecondEqSwap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0023
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2OfFourEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbedLoweringConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PlusLetterFrameOfData
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussFormMinusLetter
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommuteLevelZeroElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusLetterFrameOfData
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
import Formalism.HermitianCurvature.StatementWd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0027
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMatrixTransferConjTransposeCommute

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DualKernelLemmas
section
namespace Formalism.FourierDecayAlt.P.DualKernelLemmas

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem pair_smul_left (ρ : Rep A V) (c : ℂ) (X X' : Ix S → V) :
    pair ρ (c • X) X' = c * pair ρ X X' := by
  simp [pair, Finset.mul_sum]

end Rep

theorem star_ofReal (Y : ℝ) : star (Y : ℂ) = Y := Complex.conj_ofReal Y

theorem real_bound (u v c b : ℂ) (hc : c ≠ 0) (hu : u.im = 0) (hv : v.im = 0)
    (hb : ‖b‖ ^ 2 ≤ u.re * v.re) :
    (u * (c * v) / c).im = 0 ∧ ‖b‖ ^ 2 ≤ (u * (c * v) / c).re := by
  have h : u * (c * v) / c = u * v := by field_simp <;> ring
  rw [h]
  constructor
  · simp [Complex.mul_im, hu, hv]
  · simpa [Complex.mul_re, hu, hv] using hb

theorem d1a : DualityPairingFormula := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ Ω RR TT q a Y hD X₁ X₂
  obtain ⟨hM, hFR, hFT, hY, hY1, hq⟩ := hD
  have hd := Formalism.FourierDecayAlt.P.duality_plus ℂ A S Ω RR TT q a (Y : ℂ) hM hFR hFT hY hY1
    (star_ofReal Y) hq
  simp only [frm]
  rw [pair_act', ← act_mul, hd.2.2.2.1]

theorem d1b : DualityIsometry := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ Ω RR TT q a Y hD X₂ X₂'
  obtain ⟨hM, hFR, hFT, hY, hY1, hq⟩ := hD
  have hd := Formalism.FourierDecayAlt.P.duality_plus ℂ A S Ω RR TT q a (Y : ℂ) hM hFR hFT hY hY1
    (star_ofReal Y) hq
  simp only [frm]
  rw [pair_act', ← act_mul, ← act_mul, hd.2.2.2.2.1, act_csmul, pair_smul_left]

theorem d1c : DualityCauchySchwarz := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ Ω RR TT q a Y hD hP X₁ X₂
  have ha := d1a A S V ρ Ω RR TT q a Y hD X₁ X₂
  have hb := d1b A S V ρ Ω RR TT q a Y hD X₂ X₂
  have hq : q Y ≠ 0 := hD.2.2.2.2.2
  have hm : frm ρ (RR * ins a (TT (↑Y + 1))ᵀ) X₂ X₂ =
      q Y * frm ρ (RR * ins a (TT ↑Y)) (act (PsiP TT q a ↑Y) X₂) (act (PsiP TT q a ↑Y) X₂) := by
    rw [hb]; field_simp
  rw [hm, ha]
  refine real_bound _ _ _ _ hq (hP X₁).2 (hP _).2 ?_
  exact csPos A S V ρ _ X₁ _ hP

theorem duality_of_letters : LetterDuality := ⟨d1a, d1b, d1c⟩

theorem letter_duality_of_clauses : LetterDualityOfParts := fun _ _ _ _ => duality_of_letters

theorem qw_append_ne {S : Type} (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (hq : qw q w Y ≠ 0) :
    ∀ L : List (Letter ℂ S), (∀ l ∈ L, l.plus = true ∧ Y - l.pt ≠ 0 ∧ Y - l.pt + 1 ≠ 0) →
      qw q (L ++ w) Y ≠ 0 := by
  intro L hL
  induction L with
  | nil => simpa using hq
  | cons l L ih =>
    have hl := hL l (by simp)
    rw [List.cons_append]
    simp only [qw]
    rw [if_pos hl.1]
    exact mul_ne_zero (ih fun l' hl' => hL l' (by simp [hl'])) (div_ne_zero hl.2.2 hl.2.1)

theorem good_tail {S : Type} {l : Letter ℂ S} {w : List (Letter ℂ S)} (h : Good (l :: w)) : Good w := by
  unfold Good at *
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'), (List.pairwise_cons.1 h3).2⟩
  simp only [List.map_cons, List.nodup_cons] at h1
  exact h1.2

theorem dkDualOK : DKDualOK := by
  intro S _ _ q w L hD
  induction L with
  | nil => trivial
  | cons l L ih =>
    obtain ⟨hP, hG, hGd, hPw, hq⟩ := hD
    have hl : l.plus = true := hP l (by simp)
    have hG' : Good (L ++ w) := good_tail hG
    have hGd' : Good (L.map dl ++ w) := good_tail (by simpa using hGd)
    have hpw := List.pairwise_cons.mp hPw
    refine ⟨?_, ?_, ih ⟨fun l' h => hP l' (by simp [h]), hG', hGd', hpw.2,
      fun l' h => hq l' (by simp [h])⟩⟩
    ·
      intro l' hl'
      have hdl : dl l = ⟨false, l.intersection_update_fsHerm_neg_one, l.pt + 1⟩ := by simp [dl, hl]
      rw [hdl]
      rcases List.mem_append.mp hl' with h | h
      · have hpl : l'.plus = true := hP l' (by simp [h])
        have := (hpw.1 l' h).1
        simp only [RegL, hpl, if_true]
        intro h0; apply this; linear_combination h0
      · have hgd : Good (dl l :: (L.map dl ++ w)) := by simpa using hGd
        have := (List.pairwise_cons.mp hgd.2.2).1 l' (by simp [h])
        rw [hdl] at this
        exact this
    · simp only [ypt, hl, if_true]
      refine qw_append_ne q w l.pt (hq l (by simp)) L fun l' hl' => ⟨hP l' (by simp [hl']), ?_, ?_⟩
      · exact (hpw.1 l' hl').1
      · intro h0; exact (hpw.1 l' hl').2.2 (by linear_combination h0)

theorem dkStep1 : DKStep1 := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q w L hS hD X₁ X₂
  have hdl := Formalism.FourierDecayAlt.P.duality_list_holds ℂ A S QQ q w L hS hD.2.1 hD.2.2.1 (dkDualOK S q w L hD)
  simp only [frm]
  rw [pair_act', ← act_mul, hdl.2.2.1]

theorem lemmaDK : LemmaDK := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q w L hS hD hP X₁ X₂
  have hok := dkDualOK S q w L hD
  have hdl := Formalism.FourierDecayAlt.P.duality_list_holds ℂ A S QQ q w L hS hD.2.1 hD.2.2.1 hok
  have hkap := Formalism.FourierDecayAlt.P.kappa_formula_holds ℂ S q w L hD.2.1 hD.2.2.1 hok
  have h4 := Formalism.FourierDecayAlt.P.GramProductIdentities.dkStep4 S q w L hD.1
  have hk0 : kap q w L ≠ 0 := hdl.2.1
  have hprod : (L.map fun l => qw q w l.pt).prod = kap q w L := by rw [hkap, h4]
  have h1 := dkStep1 A S V ρ QQ q w L hS hD X₁ X₂
  have hm : frm ρ (RRw QQ (L.map dl ++ w)) X₂ X₂ = kap q w L *
      frm ρ (RRw QQ (L ++ w)) (act (Ps QQ q w L) X₂) (act (Ps QQ q w L) X₂) := by
    simp only [frm]
    rw [pair_act', ← act_mul, ← act_mul, hdl.2.2.2.1, act_csmul, pair_smul_left]
    field_simp
  rw [hprod, hm, h1]
  refine real_bound _ _ _ _ hk0 (hP X₁).2 (hP _).2 ?_
  exact csPos A S V ρ _ X₁ _ hP

theorem lemmaDKOfParts : LemmaDKOfParts := fun _ _ _ _ _ _ => lemmaDK

theorem normW_pos {S : Type} (nn : ℝ → ℝ) (w : List (Letter ℂ S)) (h : ∀ l ∈ w, 0 < nn l.pt.re) :
    0 < normW nn w := by
  unfold normW
  apply List.prod_pos
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  exact h l hl

theorem p1a : PlaneWaveNormBound := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ f fi s nn w x hW hWQ hnd hP hnn
  have hV := (Formalism.FourierDecayAlt.P.plane_wave_word_identity ℂ A S QQ f fi s w hW hWQ hnd).2.2.1
  have hb := p1aBound A S V ρ (RRw QQ w) (Vw f s w) x hP hV
  unfold N0
  exact div_le_div_of_nonneg_right hb (normW_pos nn w hnn).le

theorem p1aOfParts : PlaneWaveNormBoundOfParts := fun _ _ => p1a

end Formalism.FourierDecayAlt.P.DualKernelLemmas

theorem Formalism.FourierDecayAlt.P.duality_pairing_formula : Formalism.FourierDecayAlt.FormPairingAction.DualityPairingFormula := Formalism.FourierDecayAlt.P.DualKernelLemmas.d1a
theorem Formalism.FourierDecayAlt.P.duality_isometry : Formalism.FourierDecayAlt.FormPairingAction.DualityIsometry := Formalism.FourierDecayAlt.P.DualKernelLemmas.d1b
theorem Formalism.FourierDecayAlt.P.duality_cauchy_schwarz : Formalism.FourierDecayAlt.FormPairingAction.DualityCauchySchwarz := Formalism.FourierDecayAlt.P.DualKernelLemmas.d1c
theorem Formalism.FourierDecayAlt.P.letter_duality : Formalism.FourierDecayAlt.FormPairingAction.LetterDuality := Formalism.FourierDecayAlt.P.DualKernelLemmas.duality_of_letters
theorem Formalism.FourierDecayAlt.P.letter_duality_of_components : Formalism.FourierDecayAlt.FormPairingAction.LetterDualityOfParts := Formalism.FourierDecayAlt.P.DualKernelLemmas.letter_duality_of_clauses
theorem Formalism.FourierDecayAlt.P.dual_kernel_duality : Formalism.FourierDecayAlt.FormPairingAction.DKDualOK := Formalism.FourierDecayAlt.P.DualKernelLemmas.dkDualOK
theorem Formalism.FourierDecayAlt.P.first_reduction_estimate : Formalism.FourierDecayAlt.FormPairingAction.DKStep1 := Formalism.FourierDecayAlt.P.DualKernelLemmas.dkStep1
theorem Formalism.FourierDecayAlt.P.formPairingAction_dual_kernel : Formalism.FourierDecayAlt.FormPairingAction.LemmaDK := Formalism.FourierDecayAlt.P.DualKernelLemmas.lemmaDK
theorem Formalism.FourierDecayAlt.P.dual_kernel_lemma_of_parts : Formalism.FourierDecayAlt.FormPairingAction.LemmaDKOfParts := Formalism.FourierDecayAlt.P.DualKernelLemmas.lemmaDKOfParts
theorem Formalism.FourierDecayAlt.P.plane_wave_norm_bound' : Formalism.FourierDecayAlt.FormPairingAction.PlaneWaveNormBound := Formalism.FourierDecayAlt.P.DualKernelLemmas.p1a
theorem Formalism.FourierDecayAlt.P.first_polynomial_bound_of_parts : Formalism.FourierDecayAlt.FormPairingAction.PlaneWaveNormBoundOfParts := Formalism.FourierDecayAlt.P.DualKernelLemmas.p1aOfParts
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameOfAdmissibleWord
section
namespace Formalism.FourierDecayAlt.P

theorem plus_letter_maps_frames : Formalism.FourierDecayAlt.Fr.PlusStep :=
  plus_letter_frame_of_data position_insertion_mul_compat position_insertion_star_compat position_insertion_diagonal_compat position_insertion_free_compat letter_module_plus
    rtt_relation_entries plus_letter_form plus_letter_tau plus_letter_l

theorem minus_letter_maps_frames : Formalism.FourierDecayAlt.Fr.MinusStep :=
  minus_letter_frame_of_data position_insertion_mul_compat position_insertion_star_compat position_insertion_diagonal_compat position_insertion_free_compat letter_module_minus
    rtt_relation_entries minus_letter_form minus_letter_tau minus_letter_l

theorem frame_of_admissible_word : Formalism.FourierDecayAlt.Fr.FrameAll :=
  (frame_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position frame_module_of_word).1

theorem frame_eq_word_module : Formalism.FourierDecayAlt.Fr.FrameWord :=
  (frame_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position frame_module_of_word).2

theorem frame_of_recursive_word : Formalism.FourierDecayAlt.Fr.FrameAllRec :=
  frame_rec_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtBrReal
section
open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def ug (TT : ℝ) (α : ℂ → ℂ) (s : Bool) (z : ℂ) : ℂ := Complex.exp (I * (th TT α (br s z) : ℂ))

theorem hasFDerivAt_br_real (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) :
    HasFDerivAt (br s) ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹) ζ := by
  have h : HasFDerivAt (br s)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ζ⁻¹).restrictScalars ℝ) ζ :=
    (hasDerivAt_br s hs).hasFDerivAt.restrictScalars ℝ
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp [mul_comm]

theorem hasFDerivAt_ug (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s)
    (hζ : ζ ∈ An TT) :
    HasFDerivAt (ug TT α s)
      (((ContinuousLinearMap.mul ℝ ℂ) (ug TT α s ζ)).comp
        (I • Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹)))) ζ := by
  have h1 : HasFDerivAt (fun z => th TT α (br s z))
      ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹)) ζ :=
    (hasFDerivAt_th hTT hα hcurv (br_mem_Hh s hTT hζ)).comp ζ (hasFDerivAt_br_real s hs)
  have h2 : HasFDerivAt (fun z => ((th TT α (br s z) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹))) ζ :=
    Complex.ofRealCLM.hasFDerivAt.comp ζ h1
  have h3 : HasFDerivAt (fun z => I * ((th TT α (br s z) : ℝ) : ℂ))
      (I • Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹))) ζ :=
    h2.const_smul I
  have h4 := h3.cexp
  show HasFDerivAt (fun z => Complex.exp (I * (th TT α (br s z) : ℂ))) _ ζ
  refine h4.congr_fderiv ?_
  ext v
  simp [ug]

theorem fderiv_uu_apply (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) {ζ : ℂ} (hζ : ζ ∈ An TT) (v : ℂ) :
    fderiv ℝ (uu TT α) ζ v = uu TT α ζ * (I * ((2 * (α ζ * v).im : ℝ) : ℂ)) := by
  have hne := ne_zero_of_An hTT hζ
  obtain ⟨s, hs⟩ := exists_br hne
  have hev : uu TT α =ᶠ[𝓝 ζ] ug TT α s := by
    filter_upwards [(isOpen_An TT).mem_nhds hζ] with z hz
    exact uu_eq_br hTT hα hcurv hhol s hz
  have hu : ug TT α s ζ = uu TT α ζ := (uu_eq_br hTT hα hcurv hhol s hζ).symm
  rw [hev.fderiv_eq, (hasFDerivAt_ug hTT hα hcurv s hs hζ).fderiv]
  have hb : α ζ * ζ * (ζ⁻¹ * v) = α ζ * v := by field_simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, om_apply, bet, exp_br s hne,
    smul_eq_mul, hu, hb]

theorem wZ_uu (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) {ζ : ℂ} (hζ : ζ ∈ An TT) :
    wZ (uu TT α) ζ = uu TT α ζ * α ζ ∧ wZb (uu TT α) ζ = -(uu TT α ζ * (starRingEnd ℂ) (α ζ)) := by
  have h1 := fderiv_uu_apply hTT hα hcurv hhol hζ 1
  have h2 := fderiv_uu_apply hTT hα hcurv hhol hζ I
  have e1 : (1 / 2 : ℂ) * (I * ((2 * (α ζ * 1).im : ℝ) : ℂ) - I * (I * ((2 * (α ζ * I).im : ℝ) : ℂ)))
      = α ζ := by
    apply Complex.ext <;> simp
  have e2 : (1 / 2 : ℂ) * (I * ((2 * (α ζ * 1).im : ℝ) : ℂ) + I * (I * ((2 * (α ζ * I).im : ℝ) : ℂ)))
      = -(starRingEnd ℂ) (α ζ) := by
    apply Complex.ext <;> simp
  refine ⟨?_, ?_⟩
  · rw [wZ, h1, h2]
    linear_combination (uu TT α ζ) * e1
  · rw [wZb, h1, h2]
    linear_combination (uu TT α ζ) * e2

theorem contDiffOn_uu (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uu TT α) (An TT) := by
  intro ζ hζ
  obtain ⟨s, hs⟩ := exists_br (ne_zero_of_An hTT hζ)
  have hev : uu TT α =ᶠ[𝓝 ζ] fun z => Complex.exp (I * (th TT α (br s z) : ℂ)) := by
    filter_upwards [(isOpen_An TT).mem_nhds hζ] with z hz
    exact uu_eq_br hTT hα hcurv hhol s hz
  have hth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (th TT α) (br s ζ) :=
    (contDiffOn_th hTT hα hcurv).contDiffAt ((isOpen_Hh TT).mem_nhds (br_mem_Hh s hTT hζ))
  have hbr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ :=
    (contDiffAt_br s hs).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ((th TT α (br s z) : ℝ) : ℂ)) ζ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp ζ (hth.comp ζ hbr)
  exact ((contDiffAt_const.mul h2).cexp.congr_of_eventuallyEq hev).contDiffWithinAt

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordsAssembleHolds
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.Wd

theorem words_assemble_holds : Formalism.FourierDecayAlt.Wd.WordsAssemble := by
  intro _hInsMul hInsStar _hInsDiag hInsFree _hSlotP _hSlotM hStart _hExchP _hExchM hLetP hLetM hWF
    hTTF hE1 hE2 hE3 hE4 hXp hXm _hVecA _hVecB hDualP hDualM _hRhUU _hRhtUU
  have hWM : WordModule := Wd5.wordModule_of hStart hLetP hLetM hWF
  exact ⟨hWM, wd_siteStep_of hE1 hE2 hE3 hE4, word_matrix_entry_one,
    Wd8.cwEigen_of hE1 hE2 hXp hXm hTTF, Wd8.uwProduct,
    Wd10.dualityList_of hInsFree hInsStar hWF hWM hDualP hDualM, kappa_formula_holds,
    plane_wave_vector_identity, plane_wave_word_identity⟩

end Formalism.FourierDecayAlt.P
end

