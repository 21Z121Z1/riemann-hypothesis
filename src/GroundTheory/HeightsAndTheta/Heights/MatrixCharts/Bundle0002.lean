import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Period
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCPeriod

open Matrix

noncomputable section

theorem cfac_im (l : ℂ) :
    (l / (2 * Real.pi * Complex.I)).im = (2 * Real.pi)⁻¹ * Real.log ‖Complex.exp l‖⁻¹ := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : l / (2 * Real.pi * Complex.I) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-Complex.I * l) := by
    push_cast
    field_simp
    have := Complex.I_mul_I
    linear_combination l * this
  rw [h1, Complex.im_ofReal_mul, Complex.norm_exp, Real.log_inv, Real.log_exp]
  simp

theorem period_im (D : PeriodChartData) (z : Fin D.n → ℂ) (l : Fin D.a → ℂ)
    (h : ∀ j, Complex.exp (l j) = cuspCoord D.a_le z j) :
    (D.period z l).map Complex.im = D.Y z := by
  ext k m
  simp only [PeriodChartData.period, PeriodChartData.Y, chartImag, Matrix.map_apply,
    Matrix.add_apply, Matrix.sum_apply, Complex.add_im, Complex.im_sum, Matrix.smul_apply,
    smul_eq_mul, cuspTime]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.im_mul_ofReal, cfac_im, h j]

theorem schurQuotientPeriod : SchurQuotientPeriod.Statement := by
  intro r s τ hs hp
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun hs (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.toBlocks₂₂] using this
  · ext i j
    simp [Matrix.toBlocks₂₂]
  · have : (τ.toBlocks₂₂).map Complex.im = (τ.map Complex.im).submatrix Sum.inr Sum.inr := by
      ext i j
      simp [Matrix.toBlocks₂₂]
    rw [this]
    exact hp.submatrix Sum.inr_injective

end

end GroundTheory.Heights₂.Heights.MCPeriod
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshCore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCPsh

open Metric Filter Real

noncomputable section

theorem log_norm_le_circleAverage {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (h0 : h 0 ≠ 0) :
    Real.log ‖h 0‖ ≤ circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 := by
  have hh' : AnalyticOnNhd ℂ h (closedBall 0 |(1 : ℝ)|) := by simpa using hh
  rw [hh'.circleAverage_log_norm one_ne_zero h0]
  have hnn : ∀ u : ℂ, 0 ≤ (MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) *
      Real.log (1 * ‖(0:ℂ) - u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ closedBall (0:ℂ) |(1:ℝ)|
    · refine mul_nonneg ?_ ?_
      · exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hh') u
      · rw [one_mul, zero_sub, norm_neg]
        rcases eq_or_ne u 0 with rfl | hu0
        · simp
        · apply Real.log_nonneg
          have h1 : ‖u‖ ≤ 1 := by simpa using hu
          have h2 : 0 < ‖u‖ := norm_pos_iff.mpr hu0
          rw [le_inv_comm₀ zero_lt_one h2]
          simpa using h1
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  linarith [finsum_nonneg hnn]

theorem circleIntegrable_log_norm_of_analytic {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    CircleIntegrable (fun ζ => Real.log ‖h ζ‖) 0 1 := by
  have : MeromorphicOn h (sphere (0:ℂ) |(1:ℝ)|) :=
    (hh.mono (by simpa using sphere_subset_closedBall)).meromorphicOn
  exact this.circleIntegrable_log_norm

theorem le_circleAverage_of_minorant {φ ℓ : ℂ → ℝ} {h : ℂ → ℂ} {ℓ0 : ℝ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) (h0 : h 0 ≠ 0)
    (hφ : CircleIntegrable φ 0 1) (hℓ : CircleIntegrable ℓ 0 1)
    (hpt : ∀ ζ ∈ sphere (0:ℂ) 1, h ζ ≠ 0 → 2 * Real.log ‖h ζ‖ - ℓ ζ ≤ φ ζ)
    (hℓavg : circleAverage ℓ 0 1 ≤ ℓ0) (hφ0 : φ 0 ≤ 2 * Real.log ‖h 0‖ - ℓ0) :
    φ 0 ≤ circleAverage φ 0 1 := by
  have hlog := circleIntegrable_log_norm_of_analytic hh
  have hj := log_norm_le_circleAverage hh h0
  set ψ : ℂ → ℝ := fun ζ => 2 * Real.log ‖h ζ‖ - ℓ ζ with hψdef
  have h2 : CircleIntegrable (fun ζ => (2:ℝ) • Real.log ‖h ζ‖) 0 1 := hlog.const_fun_smul
  have hψ : CircleIntegrable ψ 0 1 := by
    have := h2.fun_sub hℓ
    simpa [ψ, smul_eq_mul] using this
  have havgψ : circleAverage ψ 0 1 = 2 * circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 -
      circleAverage ℓ 0 1 := by
    have := circleAverage_fun_sub h2 hℓ
    simp only [smul_eq_mul] at this
    rw [show ψ = fun ζ => 2 * Real.log ‖h ζ‖ - ℓ ζ from rfl, this]
    congr 1
    have := circleAverage_fun_smul (c := (0:ℂ)) (R := 1) (a := (2:ℝ)) (f := fun ζ => Real.log ‖h ζ‖)
    simpa [smul_eq_mul] using this
  have hzeros : h ⁻¹' {0}ᶜ ∈ codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|) := by
    have hconn : IsConnected (closedBall (0:ℂ) 1) :=
      ⟨⟨0, mem_closedBall_self zero_le_one⟩, (convex_closedBall (0:ℂ) 1).isPreconnected⟩
    have := hh.preimage_zero_mem_codiscreteWithin h0 (mem_closedBall_self zero_le_one) hconn
    exact codiscreteWithin_mono (by simpa using sphere_subset_closedBall) this
  have heq : (fun ζ => φ ζ - ψ ζ) =ᶠ[codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|)]
      (fun ζ => max (φ ζ - ψ ζ) 0) := by
    have hs : sphere (0:ℂ) |(1:ℝ)| ∈ codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|) :=
      self_mem_codiscreteWithin _
    filter_upwards [hzeros, hs] with ζ hζ hζs
    have hζs' : ζ ∈ sphere (0:ℂ) 1 := by simpa using hζs
    have := hpt ζ hζs' hζ
    rw [max_eq_left (by simp only [ψ]; linarith)]
  have hnn : 0 ≤ circleAverage (fun ζ => φ ζ - ψ ζ) 0 1 := by
    rw [circleAverage_congr_codiscreteWithin heq one_ne_zero]
    exact circleAverage_nonneg_of_nonneg fun ζ _ => le_max_right _ _
  rw [circleAverage_fun_sub hφ hψ, havgψ] at hnn
  linarith

end

end GroundTheory.Heights₂.Heights.MCPsh
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsPsh
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Metric

noncomputable section

def LogDetGramContinuous.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (s : Set X) (g rk : ℕ) (Y : X → Matrix (Fin g) (Fin g) ℝ)
    (F : X → Matrix (Fin g) (Fin rk) ℂ), ContinuousOn Y s → ContinuousOn F s →
    (∀ x ∈ s, (Y x).PosDef) → (∀ x ∈ s, (F x).rank = rk) →
    ContinuousOn (fun x => logDetGram (Y x) (F x)) s

def LogDetGramSubmean.Statement : Prop :=
  ∀ (g rk : ℕ) (Y : ℂ → Matrix (Fin g) (Fin g) ℝ) (F : ℂ → Matrix (Fin g) (Fin rk) ℂ),
    (∀ ζ ∈ closedBall (0 : ℂ) 1, (Y ζ).PosDef) → ContinuousOn Y (closedBall 0 1) →
    (∀ j k, Real.circleAverage (fun ζ => Y ζ j k) 0 1 = Y 0 j k) →
    (∀ j k, AnalyticOnNhd ℂ (fun ζ => F ζ j k) (closedBall 0 1)) →
    (∀ ζ ∈ closedBall (0 : ℂ) 1, (F ζ).rank = rk) →
    CircleIntegrable (fun ζ => logDetGram (Y ζ) (F ζ)) 0 1 ∧
      logDetGram (Y 0) (F 0) ≤ Real.circleAverage (fun ζ => logDetGram (Y ζ) (F ζ)) 0 1

def ChartImagContinuous.Statement : Prop :=
  ∀ D : PeriodChartData, ContinuousOn D.Y D.Ustar

def ChartImagMean.Statement : Prop :=
  ∀ (D : PeriodChartData) (z w : Fin D.n → ℂ), (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ D.Ustar) →
    ∀ j k, Real.circleAverage (fun ζ : ℂ => D.Y (z + ζ • w) j k) 0 1 = D.Y z j k

end

end GroundTheory.Heights₂.Heights
end

