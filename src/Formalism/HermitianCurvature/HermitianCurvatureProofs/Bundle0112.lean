import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0105
import Formalism.HermitianCurvature.Bundle0003
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0049
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylCellRange.ReflectionMultiplicationOnBigCell
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0104
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiRegOf
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem ag_lt_a {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : AG k r < aOf r h := by
  have h1 := hG.2.2.2
  have h2 := ag_nonneg k r
  have h3 : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem phiReg_of (hSch : SchurH) (hNI : NormIdSm) (hGG : GrowthG) (hDD : DecDD) (hBC : BeConv) :
    More.PhiReg := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hbe x hx
  have hS' := hS
  obtain ⟨hl, hds, -, hG, hw0, -, hT, -, hπ, hW, hN, hGm, hq⟩ := hS'
  have hxs : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := DDSmoothness.DD_smooth hIn.2.2.1 hl hds hw0 x hx
  have hfacts := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hfacts.1 hfacts.2 hq
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  · obtain ⟨v, hv, hlv⟩ := hA
    set cc : ℂ := ((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹ with hcc
    have hlx : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        l (σ g x) = cc • (be z c π σ μW μN (σ g x) v) (l v) :=
      fun g hg => l_of_be (hbe _ (dd_stable hds hg x hx) v hv) hlv
    refine ⟨?_, ?_, ?_⟩
    · have hc := (hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS).2.2.1 x hxs v (Or.inl hv)
      have hc2 : ContinuousOn (fun g => cc • (ContinuousLinearMap.apply ℂ Wp (l v))
          (be z c π σ μW μN (σ g x) v)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
        ((ContinuousLinearMap.apply ℂ Wp (l v)).continuous.comp_continuousOn hc).const_smul cc
      exact hc2.congr (fun g hg => hlx g hg)
    · obtain ⟨C, hC⟩ := hDD hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v hv
      have hI := hGG k r μG (aOf r h) hGm (ag_lt_a hG)
      have hfin := l1_quotient_integral_bound hds hW hN hGm hq hC hI
      have hb : ∀ᵐ g ∂νq, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ≤
          (‖cc‖ₑ * ‖l v‖ₑ) * ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) := by
        filter_upwards [hae] with g hg
        rw [← enorm_eq_nnnorm, hlx _ hg]
        have hbe' := be_enorm_le (c := c) hds hT hπ hW hN (x := x) (v := v) hg
        calc ‖cc • (be z c π σ μW μN (σ (Matrix.of g) x) v) (l v)‖ₑ
            = ‖cc‖ₑ * ‖(be z c π σ μW μN (σ (Matrix.of g) x) v) (l v)‖ₑ := enorm_smul _ _
          _ ≤ ‖cc‖ₑ * (‖be z c π σ μW μN (σ (Matrix.of g) x) v‖ₑ * ‖l v‖ₑ) := by
            gcongr
            exact ContinuousLinearMap.le_opENorm _ _
          _ ≤ ‖cc‖ₑ * ((∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) *
              ‖l v‖ₑ) := by gcongr
          _ = _ := by ring
      calc ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ∂νq
          ≤ ∫⁻ g, (‖cc‖ₑ * ‖l v‖ₑ) *
              ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) ∂νq :=
            lintegral_mono_ae hb
        _ = (‖cc‖ₑ * ‖l v‖ₑ) *
              ∫⁻ g, ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) ∂νq :=
            lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])
        _ < ⊤ := ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top]) hfin
    · have hN2 := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hxs v (Or.inl hv) (l v)).1
      have hfin : PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v (l v)) < ⊤ := by
        rw [hN2]; exact ENNReal.ofReal_lt_top
      unfold PI.BesselPeriodGGP.l2SG at hfin ⊢
      calc ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq
          = ∫⁻ g, ((‖cc‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 *
              ((‖be z c π σ μW μN (σ (Matrix.of g) x) v (l v)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq := by
            apply lintegral_congr_ae
            filter_upwards [hae] with g hg
            rw [hlx _ hg, nnnorm_smul, ENNReal.coe_mul, mul_pow]
        _ = ((‖cc‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 *
              ∫⁻ g, ((‖be z c π σ μW μN (σ (Matrix.of g) x) v (l v)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq :=
            lintegral_const_mul' _ _ (by simp)
        _ < ⊤ := ENNReal.mul_lt_top (by simp) hfin
  · push Not at hA
    have hz : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), l (σ g x) = 0 :=
      fun g hg => hA _ (dd_stable hds hg x hx)
    refine ⟨?_, ?_, ?_⟩
    · exact (continuousOn_const (c := (0 : Wp))).congr (fun g hg => hz g hg)
    · have : ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ∂νq = 0 := by
        rw [lintegral_congr_ae (g := fun _ => 0) (by filter_upwards [hae] with g hg; simp [hz _ hg])]
        simp
      rw [this]; exact ENNReal.zero_lt_top
    · unfold PI.BesselPeriodGGP.l2SG
      have : ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq = 0 := by
        rw [lintegral_congr_ae (g := fun _ => 0) (by filter_upwards [hae] with g hg; simp [hz _ hg])]
        simp
      rw [this]; exact ENNReal.zero_lt_top

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothLevOfCk
section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.Rad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def retV (g₀ : B.Mat k r) : Set (B.Mat k r) := {Y | IsUnit (g₀⁻¹ * Y + 1).det}

def retDom (g₀ : B.Mat k r) : Set (B.Mat k r) :=
  retV g₀ ∩ (fun Y => prj (iot (g₀⁻¹ * Y))) ⁻¹' {X | IsUnit (1 - X).det}

def ret (g₀ : B.Mat k r) (Y : B.Mat k r) : B.Mat k r := g₀ * kap (prj (iot (g₀⁻¹ * Y)))

lemma isOpen_unitDet {X : Type*} [TopologicalSpace X] {f : X → B.Mat k r} (hf : Continuous f) :
    IsOpen {x | IsUnit (f x).det} := by
  simp_rw [isUnit_iff_ne_zero]
  exact isOpen_ne_fun hf.matrix_det continuous_const

lemma isOpen_retV (g₀ : B.Mat k r) : IsOpen (retV g₀) := isOpen_unitDet ((continuous_const.mul continuous_id).add continuous_const)

lemma cd_iotL (g₀ : B.Mat k r) : ContDiffOn ℝ ∞ (fun Y => iot (g₀⁻¹ * Y)) (retV g₀) := by
  have h1 : ContDiffOn ℝ ∞ (fun Y : B.Mat k r => g₀⁻¹ * Y) (retV g₀) := cdm_mul contDiffOn_const contDiffOn_id
  show ContDiffOn ℝ ∞ (fun Y => (g₀⁻¹ * Y - 1) * (g₀⁻¹ * Y + 1)⁻¹) (retV g₀)
  exact cdm_mul (h1.sub contDiffOn_const) (cdm_inv (h1.add contDiffOn_const) fun Y hY => hY)

lemma isOpen_retDom (g₀ : B.Mat k r) : IsOpen (retDom g₀) := by
  exact (cdm_prj (cd_iotL g₀)).continuousOn.isOpen_inter_preimage (isOpen_retV g₀)
    (isOpen_unitDet (f := fun X : B.Mat k r => 1 - X) (continuous_const.sub continuous_id))

lemma cd_ret (g₀ : B.Mat k r) : ContDiffOn ℝ ∞ (ret g₀) (retDom g₀) := by
  have hA : ContDiffOn ℝ ∞ (fun Y => prj (iot (g₀⁻¹ * Y))) (retDom g₀) :=
    cdm_prj ((cd_iotL g₀).mono Set.inter_subset_left)
  show ContDiffOn ℝ ∞ (fun Y => g₀ * ((1 + prj (iot (g₀⁻¹ * Y))) * (1 - prj (iot (g₀⁻¹ * Y)))⁻¹)) (retDom g₀)
  exact cdm_mul contDiffOn_const
    (cdm_mul (contDiffOn_const.add hA) (cdm_inv (contDiffOn_const.sub hA) fun Y hY => hY.2))

lemma ret_mem {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) {Y : B.Mat k r} (hY : Y ∈ retDom g₀) :
    ret g₀ Y ∈ B.GV k r :=
  Formalism.FourierDecayAlt.P.B2x8.al_mul_mem hg₀ (kap_mem (prj_lie (iot (g₀⁻¹ * Y))) hY.2)

private lemma prj_eq_self_of_inLie {X : B.Mat k r} (hX : B.inLie k r X) : prj X = X := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX'
  have h2 : Hpk k r * Xᴴ * Hpk k r = -X := by
    rw [Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.Ux10.hpk_sq', Matrix.one_mul]
  unfold prj
  rw [h2, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

lemma ret_self {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) {Y : B.Mat k r} (hY : Y ∈ B.GV k r)
    (hu : IsUnit (g₀⁻¹ * Y + 1).det) : ret g₀ Y = Y := by
  have hh : g₀⁻¹ * Y ∈ B.GV k r := Formalism.FourierDecayAlt.P.B2x8.al_mul_mem (Formalism.FourierDecayAlt.P.B2x8.al_inv_mem hg₀) hY
  obtain ⟨hl, -, hk⟩ := iot_facts hh hu
  show g₀ * kap (prj (iot (g₀⁻¹ * Y))) = Y
  rw [prj_eq_self_of_inLie hl, hk, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_GV hg₀), Matrix.one_mul]

lemma self_mem_retDom {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) : g₀ ∈ retDom g₀ := by
  have e : g₀⁻¹ * g₀ = 1 := Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_GV hg₀)
  refine ⟨?_, ?_⟩
  · show IsUnit (g₀⁻¹ * g₀ + 1).det
    rw [e, ← two_smul ℂ (1 : B.Mat k r), Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
  · show IsUnit (1 - prj (iot (g₀⁻¹ * g₀))).det
    rw [e, show iot (1 : B.Mat k r) = 0 by simp [iot], prj_zero, sub_zero, Matrix.det_one]
    exact isUnit_one

lemma ret_at {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) : ret g₀ g₀ = g₀ := ret_self hg₀ hg₀ (And.left (self_mem_retDom hg₀))

lemma glev0 {g : Mx k r} (hg : g ∈ B.GV k r) : g ∈ Glev k r 0 := by
  refine ⟨hg, ?_⟩
  intro a ha
  simp at ha

theorem smoothLev_of_ck {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
    {f : Mx k r → E} (hf : ∀ m : ℕ, CkLev k r 0 m D f) : SmoothLev k r 0 D f := by
  intro g₀ hg₀
  have hG₀ : g₀ ∈ B.GV k r := hg₀.1.1
  have hU : IsOpen (retDom g₀ ∩ ret g₀ ⁻¹' D) :=
    (cd_ret g₀).continuousOn.isOpen_inter_preimage (isOpen_retDom g₀) hD
  refine ⟨retDom g₀ ∩ ret g₀ ⁻¹' D, fun Y => f (ret g₀ Y), hU, ⟨self_mem_retDom hG₀, ?_⟩, ?_, ?_⟩
  · show ret g₀ g₀ ∈ D
    rw [ret_at hG₀]
    exact hg₀.2
  · intro Y hY
    refine ContDiffAt.contDiffWithinAt ?_
    have hr : ContDiffAt ℝ ∞ (ret g₀) Y := (cd_ret g₀).contDiffAt ((isOpen_retDom g₀).mem_nhds hY.1)
    refine contDiffAt_infty.2 fun m => ?_
    have hZ : ret g₀ Y ∈ Glev k r 0 ∩ D := ⟨glev0 (ret_mem hG₀ hY.1), hY.2⟩
    obtain ⟨U, F, hUo, hZU, hF, hfF⟩ := hf m (ret g₀ Y) hZ
    have hc : ContDiffAt ℝ m (fun Y' => F (ret g₀ Y')) Y :=
      (hF.contDiffAt (hUo.mem_nhds hZU)).comp Y (contDiffAt_infty.1 hr m)
    refine hc.congr_of_eventuallyEq ?_
    have h1 : ∀ᶠ Y' in 𝓝 Y, Y' ∈ retDom g₀ := (isOpen_retDom g₀).mem_nhds hY.1
    have h2 : ∀ᶠ Y' in 𝓝 Y, ret g₀ Y' ∈ U := hr.continuousAt.preimage_mem_nhds (hUo.mem_nhds hZU)
    filter_upwards [h1, h2] with Y' h1' h2'
    exact hfF _ h2' (glev0 (ret_mem hG₀ h1'))
  · intro g hg hgl
    show f g = f (ret g₀ g)
    rw [ret_self hG₀ hgl.1 hg.1.1]

end Formalism.FourierDecayAlt.P5.Rad
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
section
namespace Formalism.FourierDecayAlt.P.PBJ

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

section rw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rw_vanish_GV {O : Set (Mat k r)} (hO : IsOpen O) {f : Mat k r → E}
    (h : ∀ g ∈ O, g ∈ GV k r → f g = 0) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ g ∈ O, g ∈ GV k r → Rw w f g = 0
  | [], _ => h
  | X :: w, hw => by
    intro g hg hgG
    have ih := rw_vanish_GV hO h w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    have hX : inLie k r X := hw X List.mem_cons_self
    show RdV X (Rw w f) g = 0
    unfold RdV
    have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
      (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
    have h0 : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 ∈ O := by
      simp only; rw [Formalism.FourierDecayAlt.P.B5.curve_zero]; exact hg
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ O :=
      hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
    have e : (fun t : ℝ => Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hev] with t ht
      exact ih _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)
    rw [e.deriv_eq]; simp

end rw

section op

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem opApply_eq_zero (Θ : DiffOp k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r)
    (h : ∀ T ∈ Θ, Rw T.word F g = 0) : opApply Θ F g = 0 := by
  unfold opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [h T hT, map_zero]

theorem ckOn_opApply_list (UU : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp))
    (hF : CkOn ⊤ (GV k r) F) (hs : closure {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ UU) :
    ∀ Θ : DiffOp k r Wp Wq, (∀ T ∈ Θ, CkOn ⊤ UU T.coef) →
      (∀ T ∈ Θ, closure {g | g ∈ GV k r ∧ Rw T.word F g ≠ 0} ⊆ UU) → CkOn ⊤ (GV k r) (opApply Θ F)
  | [], _, _ => by
    have e : opApply ([] : DiffOp k r Wp Wq) F = fun _ => 0 := by funext g; simp [opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, hc, hsu => by
    have e : opApply (T :: Θ) F = fun g => T.coef g (Rw T.word F g) + opApply Θ F g := by
      funext g; simp [opApply]
    rw [e]
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add ?_ (ckOn_opApply_list UU F hF hs Θ (fun T' hT' => hc T' (List.mem_cons_of_mem _ hT'))
      (fun T' hT' => hsu T' (List.mem_cons_of_mem _ hT')))
    exact Formalism.FourierDecayAlt.P.B5.ckOn_coef (hc T List.mem_cons_self)
      (Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top hF T.word_lie) (hsu T List.mem_cons_self)

end op

end Formalism.FourierDecayAlt.P.PBJ

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem theta_compact_support : Formalism.FourierDecayAlt.KB.ThetaCpt := by
  intro Wp Wq _ _ _ _ _ _ P p F w e Cb hDD hF hw
  obtain ⟨nf, fib, o, κ, Dop, _, hIn, _, _, hΘeq⟩ := hDD w hw e
  obtain ⟨hFs, ⟨R, hR⟩, ε, hε, hεF⟩ := hF
  have hGc : Continuous (Gf P.k P.r p.T.base.z p.T.base.z') := Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _

  have hv1 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat P.k P.r | Gf P.k P.r p.T.base.z p.T.base.z' g < ε}, g ∈ GV P.k P.r →
      Rw T.word F g = 0 := fun T _ =>
    PBJ.rw_vanish_GV (isOpen_lt hGc continuous_const)
      (fun g hg hgG => by by_contra hne; exact absurd (hεF g hgG hne) (not_le.2 hg)) T.word T.word_lie
  have hv2 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat P.k P.r | R < gN g}, g ∈ GV P.k P.r → Rw T.word F g = 0 := fun T _ =>
    PBJ.rw_vanish_GV (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous)
      (fun g hg hgG => by by_contra hne; exact absurd (hR g hgG hne) (not_le.2 hg)) T.word T.word_lie
  have hcl : IsClosed {g : Mat P.k P.r | g ∈ GV P.k P.r ∧ ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g} :=
    Formalism.FourierDecayAlt.P.B5.GV_closed.inter (isClosed_le continuous_const hGc)
  have hsub : {g : Mat P.k P.r | g ∈ GV P.k P.r ∧ ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g} ⊆
      C6.domL p.T.base ∅ := fun g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2, by simp⟩
  have hsF : closure {g | g ∈ GV P.k P.r ∧ F g ≠ 0} ⊆ C6.domL p.T.base ∅ := by
    refine subset_trans (closure_minimal ?_ hcl) hsub
    intro g hg; exact ⟨hg.1, hεF g hg.1 hg.2⟩
  have hsT : ∀ T ∈ Dop, closure {g | g ∈ GV P.k P.r ∧ Rw T.word F g ≠ 0} ⊆ C6.domL p.T.base ∅ := by
    intro T hT
    refine subset_trans (closure_minimal ?_ hcl) hsub
    intro g hg
    refine ⟨hg.1, ?_⟩
    by_contra hlt
    exact hg.2 (hv1 T hT g (not_le.1 hlt) hg.1)
  refine ⟨opApply Dop F, ⟨?_, ⟨R, ?_⟩, ε, hε, ?_⟩, fun g hg => hΘeq F g hg, ?_⟩
  · exact PBJ.ckOn_opApply_list _ F hFs hsF Dop (fun T hT => (hIn.1 T hT).1) hsT
  · intro g hgG hne
    by_contra hlt
    exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv2 T hT g (not_le.1 hlt) hgG)
  · intro g hgG hne
    by_contra hlt
    exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g (not_le.1 hlt) hgG)
  · intro a
    show D.vecV p.T.base p.ν' p.m₀ _ a = D.vecV p.T.base p.ν' p.m₀ _ a
    unfold D.vecV
    split_ifs with h1 h2
    · have hγ := h2.choose_spec
      have hG : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h2.choose := by
        rw [← Formalism.FourierDecayAlt.P.ptG_spec _ _ _ _ a _ h1.1 hγ.2.1]; exact h1.2
      rw [Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae p.T.base h2.choose _ (p.Θ.Θ w e F) (opApply Dop F) 1 ?_, one_smul]
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS p.T.base] with q hq
      rw [one_smul]
      simp only [D.orbIntegrand, rho]
      rw [hΘeq F _ ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem p.T.base hq hγ.1,
        by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs p.T.base hq]; exact hG, by simp⟩]
    · rfl
    · rfl

end Formalism.FourierDecayAlt.P
end

