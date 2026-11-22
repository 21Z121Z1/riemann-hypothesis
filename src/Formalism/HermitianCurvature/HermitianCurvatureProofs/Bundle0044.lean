import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.Bundle0003
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0038
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstNormRealNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionWithDensities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonSummationDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0025
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0024
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0010
import Formalism.HermitianCurvature.LemmaDensOfSteps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0035
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartIntegralLocal
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.ChartIntegralLocal

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma step_loc {b : Bool} {X : Mat k r} (hX : inLie k r X) (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1)
    (hψm : AEStronglyMeasurable ψ μ) (G : α → Mat k r → E) (hG1 : ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (G ξ))
    {g : Mat k r} (hg : g ∈ GV k r) {ε : ℝ} (hε : 0 < ε)
    (hGm : ∀ t ∈ Metric.ball (0 : ℝ) ε, AEStronglyMeasurable (fun ξ => G ξ (cv b X t g)) μ)
    (hG'm : AEStronglyMeasurable (fun ξ => op b X (G ξ) g) μ)
    (β : α → ℝ) (hβ : Integrable β μ)
    (hb0 : ∀ ξ, ‖G ξ g‖ ≤ β ξ) (hb1 : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ ξ, ‖op b X (G ξ) (cv b X t g)‖ ≤ β ξ)
    (Φ : Mat k r → E) (hΦ : ∀ t ∈ Metric.ball (0 : ℝ) ε, Φ (cv b X t g) = ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ) :
    op b X Φ g = ∫ ξ, ψ ξ • op b X (G ξ) g ∂μ := by
  have hcurve : ∀ t, cv b X t g ∈ GV k r := fun t => cv_mem hX hg t
  have hd : ∀ ξ, ∀ g₁ ∈ GV k r, HasDerivAt (fun s : ℝ => G ξ (cv b X s g₁)) (op b X (G ξ) g₁) 0 :=
    fun ξ g₁ hg₁ => (ckOn_diff 0 b (hG1 ξ) hX hg₁).hasDerivAt
  have hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have hs : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hε
  have h00 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) ε := Metric.mem_ball_self hε
  have hm0 : AEStronglyMeasurable (fun ξ => G ξ (cv b X 0 g)) μ := hGm 0 h00
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (bound := β)
    (F := fun t ξ => ψ ξ • G ξ (cv b X t g)) (x₀ := 0) (s := Metric.ball 0 ε) hs
    (Filter.mem_of_superset hs fun t ht => hψm.smul (hGm t ht))
    (hβ.mono' (hψm.smul hm0) (Eventually.of_forall fun ξ => (hsm ξ _).trans (by rw [cv_zero]; exact hb0 ξ)))
    (F' := fun t ξ => ψ ξ • op b X (G ξ) (cv b X t g))
    (by simp only [cv_zero]; exact hψm.smul hG'm)
    (Eventually.of_forall fun ξ t ht => (hsm ξ _).trans (hb1 t ht ξ)) hβ
    (Eventually.of_forall fun ξ t _ => by
      have e : (fun t' : ℝ => G ξ (cv b X t' g)) = fun t' => G ξ (cv b X (t' - t) (cv b X t g)) := by
        funext t'; rw [← cv_add]; congr 2; ring
      have h2 : HasDerivAt (fun s => G ξ (cv b X s (cv b X t g))) (op b X (G ξ) (cv b X t g)) (t - t) := by
        rw [sub_self]; exact hd ξ _ (hcurve t)
      have h3 := (h2.comp_sub_const t t)
      rw [← e] at h3
      exact h3.const_smul (ψ ξ))
  have e1 : (fun t : ℝ => Φ (cv b X t g)) =ᶠ[𝓝 0] fun t => ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ :=
    Filter.mem_of_superset hs fun t ht => hΦ t ht
  show deriv (fun t : ℝ => Φ (cv b X t g)) 0 = _
  rw [e1.deriv_eq, key.2.deriv]
  simp only [cv_zero]

theorem int_chart_loc (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1) (hψm : AEStronglyMeasurable ψ μ) (h : α → Mat k r → E)
    (mm : ℕ) (hh : ∀ ξ, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (h ξ)) {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {δ : ℝ}
    (hδp : 0 < δ) (hcl : Metric.closedBall (0 : J k r → ℝ) δ ⊆ Dom k r)
    (hM : ∀ w : List (J k r), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ,
      AEStronglyMeasurable (fun ξ => dLR (w.map Lt) [] (h ξ) (chart g0 Y)) μ)
    (β : α → ℝ) (hβ : Integrable β μ)
    (hbd : ∀ w : List (J k r), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∀ ξ,
      ‖dLR (w.map Lt) [] (h ξ) (chart g0 Y)‖ ≤ β ξ) :
    ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (fun Y => ∫ ξ, ψ ξ • h ξ (chart g0 Y) ∂μ) (Metric.ball 0 δ) := by
  have hΩ : Metric.ball (0 : J k r → ℝ) δ ⊆ Dom k r := Metric.ball_subset_closedBall.trans hcl
  have hcomp : IsCompact (Metric.closedBall (0 : J k r → ℝ) δ) := isCompact_closedBall _ _
  have hac : ContinuousOn (fun Y => ∑ i, ‖aC g0 i Y‖) (Metric.closedBall (0 : J k r → ℝ) δ) :=
    continuousOn_finsetSum _ fun i _ => ((aC_cd hg0 i).continuousOn.mono hcl).norm
  obtain ⟨Ba, hBa⟩ := hcomp.exists_bound_of_continuousOn hac
  have hBa' : ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∑ i, ‖aC g0 i Y‖ ≤ Ba := by
    intro Y hY
    have h1 := hBa Y (Metric.ball_subset_closedBall hY)
    rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
  have hunit : ∀ w : List (J k r), ∀ X ∈ w.map Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Lt_unit i
  have hckw : ∀ ξ (w : List (J k r)) (m : ℕ), m + w.length ≤ mm →
      CkOn ((m : ℕ) : ℕ∞) (GV k r) (dLR (w.map Lt) [] (h ξ)) := by
    intro ξ w m hm'
    rw [dLR_eq]
    exact smooth_on_of_word_derivatives _ (allLie_lr (hunit w) (by simp)) m (ckOn_mono (by rw [length_lr]; simp; omega) (hh ξ))
  have hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have hbw : ∀ (w : List (J k r)), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∀ ξ,
      ‖ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)‖ ≤ β ξ := fun w hw Y hY ξ =>
    (hsm ξ _).trans (hbd w hw Y hY ξ)
  have hmw : ∀ (w : List (J k r)), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ,
      AEStronglyMeasurable (fun ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)) μ := fun w hw Y hY =>
    hψm.smul (hM w hw Y hY)
  set L : List (J k r) → (J k r → ℝ) → E :=
    fun w Y => ∫ ξ, ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y) ∂μ with hL
  have hLc : ∀ w : List (J k r), w.length ≤ mm → ContinuousOn (L w) (Metric.ball (0 : J k r → ℝ) δ) := by
    intro w hw
    refine continuousOn_of_dominated (F := fun Y ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)) (bound := β)
      (fun Y hY => hmw w hw Y hY) (fun Y hY => Eventually.of_forall fun ξ => hbw w hw Y hY ξ) hβ
      (Eventually.of_forall fun ξ => ?_)
    exact ((cont_chart hg0 (hckw ξ w 0 (by omega))).mono hΩ).const_smul (ψ ξ)
  have hLd : ∀ w : List (J k r), w.length < mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ,
      HasFDerivAt (L w) (∑ i, (aC g0 i Y).smulRight (L (i :: w) Y)) Y := by
    intro w hw Y hY
    have hD : ∀ ξ, ∀ Y' ∈ Metric.ball (0 : J k r → ℝ) δ,
        HasFDerivAt (fun Y'' => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y''))
          (∑ i, (aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))) Y' := by
      intro ξ Y' hY'
      have h1 := (hasFDeriv_chart hg0 (hckw ξ w 1 (by omega)) (hΩ hY')).const_smul (ψ ξ)
      refine h1.congr_fderiv ?_
      ext1 W
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
        ContinuousLinearMap.smulRight_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm]
      rfl
    have hβ0 : ∀ ξ, 0 ≤ β ξ := fun ξ =>
      (norm_nonneg _).trans (hbd [] (by simp) 0 (Metric.mem_ball_self hδp) ξ)
    have hF'm : AEStronglyMeasurable (fun ξ => ∑ i, (aC g0 i Y).smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y))) μ := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).continuous.comp_aestronglyMeasurable
        (hmw (i :: w) (by simp; omega) Y hY)
    have hbF' : ∀ ξ, ∀ Y' ∈ Metric.ball (0 : J k r → ℝ) δ, ‖∑ i, (aC g0 i Y').smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))‖ ≤ Ba * β ξ := by
      intro ξ Y' hY'
      calc _ ≤ ∑ i, ‖(aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i, ‖aC g0 i Y'‖ * β ξ := Finset.sum_le_sum fun i _ => by
            rw [ContinuousLinearMap.norm_smulRight_apply]
            exact mul_le_mul_of_nonneg_left (hbw (i :: w) (by simp; omega) Y' hY' ξ) (norm_nonneg _)
        _ = (∑ i, ‖aC g0 i Y'‖) * β ξ := by rw [Finset.sum_mul]
        _ ≤ Ba * β ξ := mul_le_mul_of_nonneg_right (hBa' Y' hY') (hβ0 ξ)
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ)
      (F := fun Y' ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y'))
      (F' := fun Y' ξ => ∑ i, (aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y')))
      (bound := fun ξ => Ba * β ξ) (Metric.isOpen_ball.mem_nhds hY)
      (by filter_upwards [Metric.isOpen_ball.mem_nhds hY] with Y' hY' using hmw w hw.le Y' hY')
      (hβ.mono' (hmw w hw.le Y hY) (Eventually.of_forall fun ξ => hbw w hw.le Y hY ξ))
      hF'm (Eventually.of_forall fun ξ Y' hY' => hbF' ξ Y' hY') (hβ.const_mul Ba)
      (Eventually.of_forall fun ξ Y' hY' => hD ξ Y' hY')
    refine key.congr_fderiv ?_
    have hint : ∀ i, Integrable (fun ξ => ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y)) μ := fun i =>
      hβ.mono' (hmw (i :: w) (by simp; omega) Y hY)
        (Eventually.of_forall fun ξ => hbw (i :: w) (by simp; omega) Y hY ξ)
    have hI : ∀ i, Integrable (fun ξ => (aC g0 i Y).smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y))) μ := fun i =>
      (ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).integrable_comp (hint i)
    rw [integral_finsetSum _ (fun i _ => hI i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).integral_comp_comm (hint i)
  have hAL := ALd (𝔤 := J k r → ℝ) (E := E) Metric.isOpen_ball (aC g0) (fun i => (aC_cd hg0 i).mono hΩ) mm L
    hLc hLd
  exact hAL.congr fun Y _ => rfl

theorem ck_at_of_chart {F : Mat k r → E} {mm : ℕ} {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {δ : ℝ} (hδ : 0 < δ)
    (hAL : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Metric.ball 0 δ)) :
    ∃ (U : Set (Mat k r)) (F' : Mat k r → E), IsOpen U ∧ g0 ∈ U ∧
      ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) F' U ∧ ∀ g ∈ U, g ∈ GV k r → F g = F' g := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  set U := Sr g0 ∩ Formalism.FourierDecayAlt.P.Ux10.rho g0 ⁻¹' Metric.ball (0 : J k r → ℝ) δ with hUdef
  have hUo : IsOpen U :=
    (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) Metric.isOpen_ball
  have hg0U : g0 ∈ U := by
    have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
    refine ⟨?_, ?_⟩
    · show IsUnit (g0 * g0⁻¹ + 1).det
      rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
    · show Formalism.FourierDecayAlt.P.Ux10.rho g0 g0 ∈ Metric.ball (0 : J k r → ℝ) δ
      have h3 : Formalism.FourierDecayAlt.P.Ux10.rho g0 g0 = 0 := by
        funext i
        simp only [Formalism.FourierDecayAlt.P.Ux10.rho, hg1, iot, sub_self, Matrix.zero_mul]
        exact co_zero i
      rw [h3]; exact Metric.mem_ball_self hδ
  refine ⟨U, fun x => F (chart g0 (Formalism.FourierDecayAlt.P.Ux10.rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · have h4 : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (Formalism.FourierDecayAlt.P.Ux10.rho g0) U :=
      ((rho_cd g0).mono Set.inter_subset_left).of_le (by exact_mod_cast le_top)
    exact hAL.comp h4 (by intro x hx; exact hx.2)
  · intro x hx hxG
    have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
    obtain ⟨hl, -, hk⟩ := iot_facts hh hx.1
    show F x = F (kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0)
    rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]

end Formalism.FourierDecayAlt.P.ChartIntegralLocal
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CommuteMatrixTwoEntries
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

namespace TwistedTransfer

section Alg

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem io_mul' (x y : A) : (io (x * y) : SlopeTestRemainingChoices S A) = io x * io y := by
  simp only [io, map_mul]

theorem io_add' (x y : A) : (io (x + y) : SlopeTestRemainingChoices S A) = io x + io y := by
  simp only [io, map_add]

theorem io_sub' (x y : A) : (io (x - y) : SlopeTestRemainingChoices S A) = io x - io y := by
  simp only [io, map_sub]

theorem io_neg' (x : A) : (io (-x) : SlopeTestRemainingChoices S A) = -io x := by
  simp only [io, map_neg]

theorem io_one' : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by
  simp only [io, map_one]

theorem io_zero' : (io (0 : A) : SlopeTestRemainingChoices S A) = 0 := by
  simp only [io, map_zero]

theorem io_algebraMap (t : ℂ) : (io (algebraMap ℂ A t) : SlopeTestRemainingChoices S A) = t • (1 : SlopeTestRemainingChoices S A) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [io, Algebra.algebraMap_eq_smul_one]
  · simp [io, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]

theorem commute_io_io {x y : A} (h : Commute x y) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  unfold io
  exact h.map _

theorem commute_smul_one (t : ℂ) (z : SlopeTestRemainingChoices S A) : Commute z (t • (1 : SlopeTestRemainingChoices S A)) :=
  (Commute.one_right z).smul_right t

theorem commute_inv {R : Type*} [Ring R] {a x y : R} (h : Commute a x) (h1 : x * y = 1) (h2 : y * x = 1) :
    Commute a y := by
  show a * y = y * a
  calc a * y = (y * x) * (a * y) := by rw [h2, one_mul]
    _ = y * (x * a) * y := by simp only [mul_assoc]
    _ = y * (a * x) * y := by rw [h.eq]
    _ = y * a * (x * y) := by simp only [mul_assoc]
    _ = y * a := by rw [h1, mul_one]

def cj (f fi : A) (z : SlopeTestRemainingChoices S A) : SlopeTestRemainingChoices S A := io fi * z * io f

variable {f fi : A}

theorem io_f_fi (h : f * fi = 1) : (io f : SlopeTestRemainingChoices S A) * io fi = 1 := by
  rw [← io_mul', h, io_one']

theorem cj_mul (h : f * fi = 1) (z w : SlopeTestRemainingChoices S A) : cj f fi (z * w) = cj f fi z * cj f fi w := by
  have h' : (io f : SlopeTestRemainingChoices S A) * io fi = 1 := io_f_fi h
  simp only [cj, mul_assoc]
  rw [← mul_assoc (io f : SlopeTestRemainingChoices S A) (io fi), h', one_mul]

theorem cj_add (z w : SlopeTestRemainingChoices S A) : cj f fi (z + w) = cj f fi z + cj f fi w := by
  simp only [cj, mul_add, add_mul]

theorem cj_smul (t : ℂ) (z : SlopeTestRemainingChoices S A) : cj f fi (t • z) = t • cj f fi z := by
  simp only [cj, mul_smul_comm, smul_mul_assoc]

theorem cj_zero : cj f fi (0 : SlopeTestRemainingChoices S A) = 0 := by
  simp only [cj, mul_zero, zero_mul]

theorem cj_of_comm (h : fi * f = 1) {z : SlopeTestRemainingChoices S A} (hz : Commute (io f) z) : cj f fi z = z := by
  have h' : (io fi : SlopeTestRemainingChoices S A) * io f = 1 := io_f_fi h
  unfold cj
  rw [mul_assoc, ← hz.eq, ← mul_assoc, h', one_mul]

theorem cj_io (x : A) : cj f fi (io x : SlopeTestRemainingChoices S A) = io (fi * x * f) := by
  simp only [cj, io_mul']

private theorem io_mul_eU_comm (c : A) (a : S) (i j : Fin 2) :
    (io c : SlopeTestRemainingChoices S A) * eU a i j = eU a i j * io c := by
  ext x y
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, eU, Matrix.of_apply]
  split_ifs <;> simp

theorem cj_ins (a : S) (M : M2 (SlopeTestRemainingChoices S A)) : cj f fi (ins a M) = ins a (M.map (cj f fi)) := by
  simp only [cj, ins, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hc : (io fi : SlopeTestRemainingChoices S A) * eU a i j = eU a i j * io fi := io_mul_eU_comm fi a i j
  calc (io fi : SlopeTestRemainingChoices S A) * (eU a i j * M i j) * io f = ((io fi : SlopeTestRemainingChoices S A) * eU a i j) * M i j * io f := by
        simp only [mul_assoc]
    _ = eU a i j * ((io fi : SlopeTestRemainingChoices S A) * M i j * io f) := by
        rw [hc]
        simp only [mul_assoc]

def Tw (f fi : A) (t : ℂ) (z : SlopeTestRemainingChoices S A) : Prop := cj f fi z = z - t • (1 : SlopeTestRemainingChoices S A)

theorem lift_unipotent_inverse (t : ℂ) : (lift0 (Uinv (A := A) t) : M2 (SlopeTestRemainingChoices S A)) = !![1, 0; t • 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lift0, Uinv, io_one', io_zero', io_algebraMap]

end Alg

end TwistedTransfer

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ConcreteBoundOfRecursion
section
namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C

noncomputable section

theorem real_inputs_by_parts : C.RealInputsConcreteOfParts := by
  intro hEmb hEF hTD hLG hGram hWP hWave hPI hLift hBlock hE hCut E _ _ _ Wp Wq _ _ _ _ S jv H _ _ Vt C₄ hg1 hg2 hP hG hI hP1 hP23 hT hLE hPG Kr hK0 Th e
  exact ⟨hGram E Wp Wq S hP hG Kr hK0 Th e, hWP E Wp Wq S hG Kr hK0 Th e, hWave E Wp Wq S hG hI hP1 Kr hK0 Th e,
    hPI hEmb hEF hTD hLG E Wp Wq S hg1 hg2 hP hG hI Kr hK0 Th e, hLift E Wp Wq S hP23 Kr hK0 Th e,
    hBlock E Wp Wq S C₄ hT Kr hK0 Th e, hE E Wp Wq S jv hG hLE Kr hK0 Th e,
    hCut E Wp Wq S H Vt hPG Kr hK0 Th e⟩

theorem real_inputs_concrete_holds : C.RealInputsConcrete :=
  real_inputs_by_parts embedding_facts euclidean_frame trace_dual_alt
    lattice_facts_general gram_positive_semidefinite words_pos_of_parts wave_estimate_of_integral
    poisson_input_of_parts lift_estimate_of_base block_estimate_of_base level_zero_estimate_product
    cutoff_of_parts

theorem concrete_bound_of_recursion : C.TheoremAConcreteOfParts := by
  intro hTA hPT hPJ hPSJ hRI C₁ C₄ hC₁ hC₄
  obtain ⟨C, C', hCC⟩ := hTA C₁ C₄ hC₁ hC₄
  refine ⟨C, C', ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ S jv cE Kr hK0 Th e Θ H _ _ _ Vt c hf hg1 hg2 hΘ hC'Θ hsmall hSz hP hG hI hP1
    hP23 hT hLE _ hPG hKr hA2 hEB hDom hLS hA4 R
  obtain ⟨hGram, hWP, hWave, hPI, hLift, hBlock, hE, hCut⟩ :=
    hRI E Wp Wq S jv H Vt C₄ hg1 hg2 hP hG hI hP1 hP23 hT hLE hPG Kr hK0 Th e
  obtain ⟨V, _, _, _, _, _, ι, _, π, Λ, hD, hZ, emb, dmap, hbij, hFr, hWF⟩ := hPI
  have hPS : (S.mkData Kr hK0 Th e).PoissonStep :=
    @hPSJ hPT hPJ E S.W _ (S.mkData Kr hK0 Th e) V _ _ _ _ _ ι _ π hbij Λ hD hZ emb dmap hFr hWF
  have hr : (S.G.r : ℝ) * (C / Θ) ^ S.f ≤ 1 := by
    rcases le_or_gt 0 ((C / Θ) ^ S.f) with hx | hx
    · nlinarith
    · have : (S.G.r : ℝ) * (C / Θ) ^ S.f ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hx.le
      linarith
  have hK : 4 ≤ (S.mkData Kr hK0 Th e).K := by
    show 4 ≤ Kst
    unfold Kst
    norm_num
  exact hCC E S.W (S.mkData Kr hK0 Th e) Θ (∏ v, jv v) H Vt c hK hf hΘ hC'Θ hr hSz hGram hKr hWP hA2 hEB hDom
    hWave hPS hLift hBlock hLS hE hCut hA4 R

theorem concrete_bound_holds : C.TheoremAConcrete :=
  concrete_bound_of_recursion theorem_a_after poisson_summation_level_statement poisson_joint
    poisson_level_joint real_inputs_concrete_holds

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousExtensionOfFourierDecay
section
open MeasureTheory Real Complex Module

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

theorem unif_bound {X : Type*} (f : ℕ → X → ℝ) (m : ℕ) (h : ∀ j ≤ m, ∃ B, ∀ t, f j t ≤ B) :
    ∃ B, ∀ j ≤ m, ∀ t, f j t ≤ B := by
  choose! B hB using h
  refine ⟨∑ j ∈ Finset.range (m + 1), |B j|, fun j hj t => ?_⟩
  calc f j t ≤ B j := hB j hj t
    _ ≤ |B j| := le_abs_self _
    _ ≤ ∑ j ∈ Finset.range (m + 1), |B j| :=
        Finset.single_le_sum (f := fun j => |B j|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))

theorem smooth_extension_of_fourier_decay (D : ℂ → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hE : Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t))
    (hc : ∀ t, t ≠ 0 → ContinuousAt D t)
    (hdD : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3)))
    (hdE : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3))) :
    ∃ D' : ℂ → ℂ, ContDiff ℝ m D' ∧ (∀ t, t ≠ 0 → D' t = D t) ∧ (∫ t, D' t = ∫ t, D t) ∧
      (∃ C', ∀ j ≤ m, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ C' * (1 + ‖t‖) ^ (-(4 : ℝ))) ∧
      ∀ j, 1 ≤ j → j ≤ m → Integrable (iteratedFDeriv ℝ j D') ∧ ∫ t, iteratedFDeriv ℝ j D' t = 0 := by
  set E : ℂ → ℂ := fun t => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t with hEdef
  obtain ⟨D', hD'c, -, hD'eq⟩ := smooth_bounded_of_fourier_decay D m C hD hdD
  obtain ⟨E', hE'c, hE'b, hE'eq⟩ := smooth_bounded_of_fourier_decay E m C hE hdE
  have hEc : ∀ t, t ≠ 0 → ContinuousAt E t := fun t ht => by
    show ContinuousAt (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) t
    exact (((continuous_const.add (continuous_norm.pow 2)).pow 2).continuousAt).smul (hc t ht)
  have hw : ∀ x, E' x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x := by
    have hcont1 : Continuous E' := hE'c.continuous
    have hcont2 : Continuous (fun x : ℂ => ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x) :=
      ((continuous_const.add (continuous_norm.pow 2)).pow 2).smul hD'c.continuous
    have h := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hcont1 hcont2 (fun x hx => by
      have hx0 : x ≠ 0 := hx
      show E' x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x
      rw [hE'eq x (hEc x hx0), hD'eq x (hc x hx0)])
    exact fun x => congrFun h x
  obtain ⟨B, hB⟩ := unif_bound (fun j t => ‖iteratedFDeriv ℝ j E' t‖) m hE'b
  obtain ⟨-, hdec, hint⟩ := smooth_decay_of_weighted (V := ℂ) (by rw [Complex.finrank_real_complex]; norm_num) hE'c B hB hw
  have hae : D' =ᵐ[volume] D := by
    have : ∀ᵐ t ∂(volume : Measure ℂ), t ≠ 0 := by
      rw [ae_iff]; simpa using (measure_singleton (0 : ℂ))
    filter_upwards [this] with t ht
    exact hD'eq t (hc t ht)
  exact ⟨D', hD'c, fun t ht => hD'eq t (hc t ht), integral_congr_ae hae, hdec, hint⟩

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityLemmaOfReductions
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

theorem nonzero_minor_count_le {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : Formalism.FourierDecayAlt.DensityAveraging.nzMin D γ ≤ r + 2 := by
  unfold Formalism.FourierDecayAlt.DensityAveraging.nzMin
  calc _ ≤ (Finset.univ : Finset (Fin (r + 2))).card := Finset.card_filter_le _ _
    _ = r + 2 := by simp

theorem density_lemma_of_reductions : Formalism.FourierDecayAlt.DensityAveraging.LemmaDensOfSteps := by
  rintro ⟨C0, hB⟩ ⟨C1, hJ⟩ ⟨C2, hT⟩
  refine ⟨max C0 (max C1 C2), ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ O hr hε hA hmm hF hsupp hbig hrel hG
  have H : Formalism.FourierDecayAlt.DensityAveraging.DensHyp (max C0 (max C1 C2)) D A ε mm F' := ⟨hr, hε, hA, hmm, hF, hsupp, hbig⟩
  have h0 : C0 ≤ max C0 (max C1 C2) := le_max_left _ _
  have h1 : C1 ≤ max C0 (max C1 C2) := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2 : C2 ≤ max C0 (max C1 C2) := le_trans (le_max_right _ _) (le_max_right _ _)
  have key : ∀ n : ℕ, ∀ γ : B.Mat k r, r + 2 - Formalism.FourierDecayAlt.DensityAveraging.nzMin D γ = n → IsRelevant D γ →
      0 < Gf k r D.z D.z' γ → Formalism.FourierDecayAlt.DensityAveraging.VanAt D F' γ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro γ hn hrelγ hGγ
      have hMore : Formalism.FourierDecayAlt.DensityAveraging.MoreBlocks D F' γ := by
        intro γ' hrel' hG' hlt
        have hle := nonzero_minor_count_le D γ'
        exact ih (r + 2 - Formalism.FourierDecayAlt.DensityAveraging.nzMin D γ') (by omega) γ' rfl hrel' hG'
      by_cases hbc : γ ∈ bigPos D
      · exact hB _ h0 k r Wp Wq D A ε mm F' γ H hbc hrelγ
      · have hz : ∃ l : Fin (r + 2), Dmin k r D.z D.z' γ l = 0 := by
          by_contra hne
          exact hbc ⟨hrelγ.1, hGγ, fun l _ hl => hne ⟨l, hl⟩⟩
        by_cases hcj : Formalism.FourierDecayAlt.DensityAveraging.CaseJ D γ
        · exact hJ _ h1 k r Wp Wq D A ε mm F' γ H hrelγ hGγ hcj hMore
        · exact hT _ h2 k r Wp Wq D A ε mm F' γ H hrelγ hGγ ⟨hz, hcj⟩ hMore
  exact key _ γ rfl hrel hG O

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualFromInputs
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem thmPActualFromInputs : ThmPActualFromInputs := by
  intro hHer hWC hWS hFA hOW hPW Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  obtain ⟨K, hAdj, hTD, hTT, hSl, hSD, hWK, hFS, hCor, hJ⟩ :=
    hHer Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  refine ⟨K, ?_, hSl, hCor, hJ⟩
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st K l0 hD hFA hOW hAdj
  have hST := stepTwistFromParts (S := S) P z z' π π' X μ L st K l0 hD hPW (hWS Wp Wq P z z' π π' X L)
    (hWC Wp Wq P z z' π π' X μ L st l0 hD) hWK
  exact thmPFromStepsAll Wp Wq S P z z' π π' μ L st K l0 hTI hTD hTT hSl hSD hST hFS

theorem thmPActualFromHer : ThmPActualFromHer := fun hHer hWC =>
  thmPActualFromInputs hHer hWC waveSiteAll Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR Formalism.FourierDecayAlt.P.plane_wave_vector_identity

end Formalism.FourierDecayAlt.P5
end
end

