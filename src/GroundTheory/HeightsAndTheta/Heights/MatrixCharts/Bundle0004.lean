import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartBounds
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MCBounds
open scoped ComplexOrder

noncomputable section

theorem MCBounds.map_smul_one_sub {g : ℕ} (s : ℝ) (A : Matrix (Fin g) (Fin g) ℝ) :
    (s • (1 : Matrix (Fin g) (Fin g) ℝ) - A).map (fun x : ℝ => (x : ℂ)) =
      (s : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ) - A.map (fun x : ℝ => (x : ℂ)) := by
  ext j k
  by_cases h : j = k <;> simp [h]

theorem MCBounds.map_sub_smul_one {g : ℕ} (s : ℝ) (A : Matrix (Fin g) (Fin g) ℝ) :
    (A - s • (1 : Matrix (Fin g) (Fin g) ℝ)).map (fun x : ℝ => (x : ℂ)) =
      A.map (fun x : ℝ => (x : ℂ)) - (s : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ) := by
  ext j k
  by_cases h : j = k <;> simp [h]

theorem MCBounds.conj_smul_one_sub {g k : ℕ} (F : Matrix (Fin g) (Fin k) ℂ) (s : ℂ)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    Fᴴ * (s • (1 : Matrix (Fin g) (Fin g) ℂ) - Z) * F = s • (Fᴴ * F) - Fᴴ * Z * F := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem MCBounds.conj_sub_smul_one {g k : ℕ} (F : Matrix (Fin g) (Fin k) ℂ) (s : ℂ)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    Fᴴ * (Z - s • (1 : Matrix (Fin g) (Fin g) ℂ)) * F = Fᴴ * Z * F - s • (Fᴴ * F) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem MCBounds.re_det_ofReal_smul {k : ℕ} (s : ℝ) (H : Matrix (Fin k) (Fin k) ℂ) :
    ((s : ℂ) • H).det.re = s ^ k * H.det.re := by
  rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem ChartBounds.proof : ChartBounds.Statement := by
  intro D
  obtain ⟨C1, hC1, hY⟩ := exists_Y_le D
  obtain ⟨δ, M, hδ, hM, hG⟩ := exists_gram_bounds D
  set C2 : ℝ := (D.rk : ℝ) * (|Real.log C1| + 1) + |Real.log δ| with hC2
  set C3 : ℝ := |Real.log (D.c⁻¹ ^ D.rk * M)| with hC3
  have hCC1 : C1 ≤ max C1 (max C2 (max C3 1)) := le_max_left _ _
  have hCC2 : C2 ≤ max C1 (max C2 (max C3 1)) := (le_max_left _ _).trans (le_max_right _ _)
  have hCC3 : C3 ≤ max C1 (max C2 (max C3 1)) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  set C := max C1 (max C2 (max C3 1)) with hC
  refine ⟨C, by linarith, fun p hp hps => ?_⟩
  have hz : p.1 ∈ D.U := (D.K_subset hp).1
  have hr1 : 1 ≤ D.radius p.1 := one_le_radius D hz
  have hlog1 : 1 ≤ Real.log (D.radius p.1) := one_le_log_radius D hz
  set r := D.radius p.1 with hr
  have hYc : (D.Y p.1 - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)).PosSemidef := D.Y_ge p.1 hps
  have hYpd : (D.Y p.1).PosDef := posDef_of_ge D.c_pos hYc
  have hYle1 := hY p hp
  have hYle : ((C * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef := by
    have e : (C * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1 =
        ((C1 * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1) +
          ((C - C1) * r) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) := by
      rw [sub_mul, sub_smul]; abel
    rw [e]
    exact hYle1.add (PosSemidef.one.smul (by nlinarith))
  set F := D.f p with hF
  set Yc := (D.Y p.1)⁻¹.map (fun x : ℝ => (x : ℂ)) with hYcdef
  have hYcPSD : Yc.PosSemidef := posSemidef_map_ofReal hYpd.inv.posSemidef
  have hGPSD : (Fᴴ * Yc * F).PosSemidef := hYcPSD.conjTranspose_mul_mul_same F
  have hHPSD : (Fᴴ * F).PosSemidef := posSemidef_conjTranspose_mul_self F
  have hup : (((D.c⁻¹ : ℝ) : ℂ) • (Fᴴ * F) - Fᴴ * Yc * F).PosSemidef := by
    have h1 := posSemidef_map_ofReal (inv_le_of_ge D.c_pos hYc)
    rw [map_smul_one_sub] at h1
    have := h1.conjTranspose_mul_mul_same F
    rwa [conj_smul_one_sub] at this
  have hdup : (Fᴴ * Yc * F).det.re ≤ D.c⁻¹ ^ D.rk * (Fᴴ * F).det.re := by
    have := MCDet.re_det_mono hGPSD hup
    simp only [RCLike.re_to_complex] at this
    rwa [re_det_ofReal_smul] at this
  have hlow : ∀ l : ℝ, 0 < l → (l • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef →
      l⁻¹ ^ D.rk * (Fᴴ * F).det.re ≤ (Fᴴ * Yc * F).det.re := by
    intro l hl hle
    have h1 := posSemidef_map_ofReal (inv_ge_of_le hl hYpd hle)
    rw [map_sub_smul_one] at h1
    have h2 := h1.conjTranspose_mul_mul_same F
    rw [conj_sub_smul_one] at h2
    have h3 : (((l⁻¹ : ℝ) : ℂ) • (Fᴴ * F)).PosSemidef :=
      hHPSD.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hl.le))
    have := MCDet.re_det_mono h3 h2
    simp only [RCLike.re_to_complex] at this
    rwa [re_det_ofReal_smul] at this
  have hδp := (hG p hp).1
  have hMp := (hG p hp).2
  have hl1 : 0 < C1 * r := by positivity
  have hdlow1 := hlow (C1 * r) hl1 hYle1
  have hdlowC := hlow (C * r) (by nlinarith) hYle
  have hμpos : 0 < (C1 * r)⁻¹ ^ D.rk * δ := by positivity
  have hμ : (C1 * r)⁻¹ ^ D.rk * δ ≤ (Fᴴ * Yc * F).det.re :=
    le_trans (mul_le_mul_of_nonneg_left hδp (by positivity)) hdlow1
  have hdpos : 0 < (Fᴴ * Yc * F).det.re := lt_of_lt_of_le hμpos hμ
  have hu : D.u p = Real.log (Fᴴ * Yc * F).det.re := rfl
  refine ⟨hYc, hYle, hdlowC, hdup, ?_, ?_⟩
  · rw [hu]
    have h1 := Real.log_le_log hμpos hμ
    rw [Real.log_mul (by positivity) hδ.ne', Real.log_pow, Real.log_inv,
      Real.log_mul hC1.ne' (by linarith)] at h1
    have a1 : Real.log C1 ≤ |Real.log C1| * Real.log r :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog1)
    have a2 : -Real.log δ ≤ |Real.log δ| * Real.log r :=
      (neg_le_abs _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog1)
    have hk : (0 : ℝ) ≤ D.rk := Nat.cast_nonneg _
    have b1 := mul_le_mul_of_nonneg_left a1 hk
    have b2 := mul_le_mul_of_nonneg_right hCC2 (by linarith : (0 : ℝ) ≤ Real.log r)
    rw [hC2] at b2
    nlinarith
  · rw [hu]
    have h1 := Real.log_le_log hdpos (hdup.trans (mul_le_mul_of_nonneg_left hMp
      (pow_nonneg (inv_nonneg.mpr D.c_pos.le) _)))
    exact h1.trans ((le_abs_self _).trans hCC3)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartImagContinuous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem cuspTime_continuousOn {n a : ℕ} (h : a ≤ n) (U : Set (Fin n → ℂ)) (j : Fin a) :
    ContinuousOn (fun z => cuspTime h z j) (puncturedChart h U) := by
  have hc : Continuous (fun z : Fin n → ℂ => cuspCoord h z j) := continuous_apply _
  have hne : ∀ z ∈ puncturedChart h U, ‖cuspCoord h z j‖ ≠ 0 := fun z hz =>
    norm_ne_zero_iff.mpr (hz.2 j)
  have hinv : ContinuousOn (fun z => ‖cuspCoord h z j‖⁻¹) (puncturedChart h U) :=
    hc.norm.continuousOn.inv₀ hne
  exact continuousOn_const.mul (hinv.log fun z hz => inv_ne_zero (hne z hz))

theorem ChartImagContinuous.proof : ChartImagContinuous.Statement := by
  intro D
  have hsub : D.Ustar ⊆ D.U := fun z hz => hz.1
  have hτ : ∀ k l, ContinuousOn (fun z => (D.τ0 z k l).im) D.Ustar := fun k l =>
    Complex.continuous_im.comp_continuousOn ((D.τ0_analytic k l).continuousOn.mono hsub)
  have ht : ∀ j, ContinuousOn (fun z => cuspTime D.a_le z j) D.Ustar := fun j =>
    cuspTime_continuousOn D.a_le D.U j
  show ContinuousOn (fun z => chartImag D.a_le D.τ0 D.B z) D.Ustar
  refine continuousOn_pi.mpr fun k => continuousOn_pi.mpr fun l => ?_
  simp only [chartImag, Matrix.add_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  exact (hτ k l).add (continuousOn_finsetSum _ fun j _ => (ht j).mul continuousOn_const)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartImagMean
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Metric Real

noncomputable section

theorem ChartImagMean.proof : ChartImagMean.Statement := by
  intro D z w hdisc j k
  have hball : ∀ ζ ∈ closedBall (0 : ℂ) 1, z + ζ • w ∈ D.Ustar := fun ζ hζ =>
    hdisc ζ (mem_closedBall_zero_iff.mp hζ)

  have hY : ∀ x, D.Y x j k = (D.τ0 x j k).im +
      ∑ i, (-(2 * π)⁻¹ * D.B i j k) * Real.log ‖x (Fin.castLE D.a_le i)‖ := by
    intro x
    simp only [PeriodChartData.Y, chartImag, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.map_apply, cuspTime, cuspCoord, smul_eq_mul, Real.log_inv]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

  have hτ : AnalyticOnNhd ℂ (fun ζ : ℂ => D.τ0 (z + ζ • w) j k) (closedBall 0 1) := by
    intro ζ hζ
    exact AnalyticAt.comp (g := fun x => D.τ0 x j k) (f := fun ζ : ℂ => z + ζ • w)
      (D.τ0_analytic j k _ (hball ζ hζ).1)
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  have hc : ∀ i, AnalyticOnNhd ℂ
      (fun ζ : ℂ => z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)) (closedBall 0 1) :=
    fun i ζ _ => analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hcne : ∀ i, ∀ ζ ∈ closedBall (0 : ℂ) 1,
      z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i) ≠ 0 := by
    intro i ζ hζ
    have := (hball ζ hζ).2 i
    simpa [cuspCoord] using this

  have hτc : ContinuousOn (fun ζ : ℂ => (D.τ0 (z + ζ • w) j k).im) (closedBall 0 1) :=
    Complex.continuous_im.comp_continuousOn hτ.continuousOn
  have hlc : ∀ i, ContinuousOn
      (fun ζ : ℂ => (-(2 * π)⁻¹ * D.B i j k) *
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖) (closedBall 0 1) := by
    intro i
    refine continuousOn_const.mul ((hc i).continuousOn.norm.log fun ζ hζ => ?_)
    exact norm_ne_zero_iff.mpr (hcne i ζ hζ)
  have hint : ∀ {f : ℂ → ℝ}, ContinuousOn f (closedBall 0 1) → CircleIntegrable f 0 1 :=
    fun hf => (hf.mono sphere_subset_closedBall).circleIntegrable zero_le_one
  have hfun : (fun ζ : ℂ => D.Y (z + ζ • w) j k) = fun ζ : ℂ =>
      (D.τ0 (z + ζ • w) j k).im + ∑ i, (-(2 * π)⁻¹ * D.B i j k) *
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖ := by
    funext ζ
    rw [hY]
    simp
  rw [hfun, circleAverage_fun_add (hint hτc)
    (hint (continuousOn_finsetSum _ fun i _ => hlc i)),
    circleAverage_fun_sum fun i _ => hint (hlc i), MCPsh.circleAverage_im_of_analytic hτ, hY z]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hs : circleAverage (fun ζ : ℂ => (-(2 * π)⁻¹ * D.B i j k) *
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖) 0 1 =
        (-(2 * π)⁻¹ * D.B i j k) * circleAverage (fun ζ : ℂ =>
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖) 0 1 :=
      circleAverage_fun_smul (E := ℝ) (𝕜 := ℝ) (a := -(2 * π)⁻¹ * D.B i j k)
        (f := fun ζ : ℂ => Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖)
    rw [hs, MCPsh.circleAverage_log_norm_of_ne_zero (hc i) (hcne i)]
    simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartLowerHeightsound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace ChartLowerBlockBound

theorem period_apply_of_le (D : PeriodChartData) (T : ToricBlock D) (z : Fin D.n → ℂ)
    (ℓ : Fin D.a → ℂ) (i l : Fin D.g) (h : T.r ≤ i.val) :
    D.period z ℓ i l = D.τ0 z i l := by
  simp [PeriodChartData.period, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.map_apply, T.support _ i l (Or.inl h)]

theorem entry_bound (D : PeriodChartData) (i l : Fin D.g) :
    ∃ C : ℝ, ∀ p ∈ D.K, ‖D.τ0 p.1 i l‖ ≤ C := by
  have hc : IsCompact (Prod.fst '' D.K) := D.isCompact_K.image continuous_fst
  have hsub : Prod.fst '' D.K ⊆ D.U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (D.K_subset hp).1
  have hcont : ContinuousOn (fun z => D.τ0 z i l) (Prod.fst '' D.K) :=
    ((D.τ0_analytic i l).continuousOn).mono hsub
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hcont
  exact ⟨C, fun p hp => hC p.1 ⟨p, hp, rfl⟩⟩

end ChartLowerBlockBound

theorem ChartLowerBlockBound.proof : ChartLowerBlockBound.Statement := by
  intro D T
  choose C hC using ChartLowerBlockBound.entry_bound D
  refine ⟨1 + ∑ i, ∑ l, |C i l|, ?_, ?_⟩
  · have : 0 ≤ ∑ i, ∑ l, |C i l| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  · intro p hp ℓ i l hi
    rw [ChartLowerBlockBound.period_apply_of_le D T p.1 ℓ i l hi]
    have h1 : |C i l| ≤ ∑ l', |C i l'| :=
      Finset.single_le_sum (f := fun l' => |C i l'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
    have h2 : ∑ l', |C i l'| ≤ ∑ i', ∑ l', |C i' l'| :=
      Finset.single_le_sum (f := fun i' => ∑ l', |C i' l'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h3 := hC i l p hp
    have h4 := le_abs_self (C i l)
    linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartPeriodImPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem ChartPeriodImPos.proof : ChartPeriodImPos.Statement := by
  intro D z hz ℓ hℓ
  rw [MCPeriod.period_im D z ℓ hℓ]
  have hY : (D.Y z - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)).PosSemidef := D.Y_ge z hz
  refine ⟨?_, ?_⟩
  · have e : D.Y z = (D.Y z - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)) +
        D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) := by abel
    rw [e]
    exact Matrix.PosDef.posSemidef_add hY (PosDef.one.smul D.c_pos)
  · intro x
    have h := hY.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul] at h
    have hx : x ⬝ᵥ x = ∑ k, x k ^ 2 := by
      simp only [dotProduct, sq]
    rw [hx] at h
    rw [MCSchur.qf]
    linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartPotentialPsh
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Metric Real MCPsh

noncomputable section

theorem splitCoord_add_smul (n m : ℕ) (z w : Fin (n + m) → ℂ) (ζ : ℂ) :
    splitCoord n m (z + ζ • w) = splitCoord n m z + ζ • splitCoord n m w := by
  ext <;> simp [splitCoord]

theorem continuous_splitCoord (n m : ℕ) : Continuous (splitCoord n m) :=
  Continuous.prodMk (continuous_pi fun _ => continuous_apply _)
    (continuous_pi fun _ => continuous_apply _)

theorem PeriodChartData.Y_posDef (D : PeriodChartData) {z : Fin D.n → ℂ} (hz : z ∈ D.Ustar) :
    (D.Y z).PosDef := by
  have h := Matrix.PosDef.posSemidef_add (D.Y_ge z hz) (PosDef.one.smul D.c_pos)
  simpa [PeriodChartData.Y] using h

theorem ChartPotentialPsh.proof (hcont : LogDetGramContinuous.Statement)
    (hsub : LogDetGramSubmean.Statement) (hYc : ChartImagContinuous.Statement)
    (hmean : ChartImagMean.Statement) : ChartPotentialPsh.Statement := by
  intro D
  set S := splitCoord D.n D.m ⁻¹' (D.Ustar ×ˢ D.V) with hS
  have hUs : ∀ x ∈ S, splitCoord D.n D.m x ∈ D.U ×ˢ D.V := fun x hx => ⟨hx.1.1, hx.2⟩
  have hYS : ContinuousOn (fun x => D.Y (splitCoord D.n D.m x).1) S :=
    (hYc D).comp (continuous_fst.comp (continuous_splitCoord _ _)).continuousOn
      (fun x hx => hx.1)
  have hFS : ContinuousOn (fun x => D.f (splitCoord D.n D.m x)) S :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
      (D.f_analytic j k).continuousOn.comp (continuous_splitCoord _ _).continuousOn hUs
  have hc := hcont (Fin (D.n + D.m) → ℂ) S D.g D.rk (fun x => D.Y (splitCoord D.n D.m x).1)
    (fun x => D.f (splitCoord D.n D.m x)) hYS hFS (fun x hx => D.Y_posDef hx.1)
    (fun x hx => D.f_rank _ (hUs x hx))
  refine ⟨hc.upperSemicontinuousOn, ?_⟩
  intro z w hdisc
  set z' := splitCoord D.n D.m z
  set w' := splitCoord D.n D.m w
  have hline : ∀ ζ ∈ closedBall (0:ℂ) 1, z' + ζ • w' ∈ D.Ustar ×ˢ D.V := fun ζ hζ => by
    have := hdisc ζ (by simpa using hζ)
    rwa [Set.mem_preimage, splitCoord_add_smul] at this
  have hline1 : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z'.1 + ζ • w'.1 ∈ D.Ustar := fun ζ hζ =>
    (hline ζ (by simpa using hζ)).1
  have haff : ∀ ζ : ℂ, AnalyticAt ℂ (fun ζ : ℂ => z' + ζ • w') ζ := fun ζ =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hf : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => D.f (z' + ζ • w') j k) (closedBall 0 1) :=
    fun j k ζ hζ => AnalyticAt.comp (g := fun p => D.f p j k) (f := fun ζ : ℂ => z' + ζ • w')
      (D.f_analytic j k _ ⟨(hline ζ hζ).1.1, (hline ζ hζ).2⟩) (haff ζ)
  have hYd : ContinuousOn (fun ζ : ℂ => D.Y (z'.1 + ζ • w'.1)) (closedBall 0 1) :=
    (hYc D).comp ((continuous_const.add (continuous_id.smul continuous_const)).continuousOn)
      (fun ζ hζ => (hline ζ hζ).1)
  have hm : ∀ j k, circleAverage (fun ζ : ℂ => D.Y (z'.1 + ζ • w'.1) j k) 0 1 =
      D.Y (z'.1 + (0:ℂ) • w'.1) j k := fun j k => by
    rw [zero_smul, add_zero]; exact hmean D z'.1 w'.1 hline1 j k
  obtain ⟨hint, hle⟩ := hsub D.g D.rk (fun ζ => D.Y (z'.1 + ζ • w'.1))
    (fun ζ => D.f (z' + ζ • w')) (fun ζ hζ => D.Y_posDef (hline ζ hζ).1) hYd hm hf
    (fun ζ hζ => D.f_rank _ ⟨(hline ζ hζ).1.1, (hline ζ hζ).2⟩)
  have hfun : (fun ζ : ℂ => (D.u ∘ splitCoord D.n D.m) (z + ζ • w)) =
      fun ζ => logDetGram (D.Y (z'.1 + ζ • w'.1)) (D.f (z' + ζ • w')) := by
    funext ζ
    simp only [Function.comp_apply, PeriodChartData.u, splitCoord_add_smul, z', w',
      Prod.fst_add, Prod.smul_fst]
  rw [hfun]
  refine ⟨hint, ?_⟩
  have e : (D.u ∘ splitCoord D.n D.m) z =
      logDetGram (D.Y (z'.1 + (0:ℂ) • w'.1)) (D.f (z' + (0:ℂ) • w')) := by
    simp [PeriodChartData.u, z']
  rw [e]; exact hle

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspCovolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace CuspCovolume

theorem periodGram_castAdd {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : Fin g) :
    periodGram τ (Fin.castAdd g k) (Fin.castAdd g k) = (τ.map Complex.im)⁻¹ k k := by
  simp only [periodGram, of_apply, periodBasis, Fin.append_left]
  rw [show hermPair (τ.map Complex.im)⁻¹ (Pi.single k 1) (Pi.single k 1) =
      hermValue (τ.map Complex.im)⁻¹ (Pi.single k 1) from rfl, MCSchur.hermValue_eq_qf]
  have h1 : (fun j => ((Pi.single k (1 : ℂ) : Fin g → ℂ) j).re) = Pi.single k (1 : ℝ) := by
    ext j
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  have h2 : (fun j => ((Pi.single k (1 : ℂ) : Fin g → ℂ) j).im) = 0 := by
    ext j
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  rw [h1, h2]
  simp [MCSchur.qf, mulVec_single]

theorem inv_diag_le_of_ge {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) {c : ℝ}
    (hc : 0 < c) (h : ∀ x : Fin g → ℝ, c * ∑ k, x k ^ 2 ≤ MCSchur.qf Y x) (k : Fin g) :
    Y⁻¹ k k ≤ 1 / c := by
  refine MCCusp.inv_diag_le hY k hc fun x => ?_
  have hs : x k ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ k)
  have := h x
  nlinarith

end CuspCovolume

theorem CuspCovolume.proof (hImPos : ChartPeriodImPos.Statement)
    (hPG : PeriodGramPosDef.Statement) (hCB : CuspCoordinateBound.Statement)
    (hPB : PivotBounds.Statement) (hGP : GramPivotProduct.Statement)
    (hPP : PivotProductBound.Statement) (hLC : PeriodLatticeCovolume.Statement)
    (hLead : LeadingCovolume.Statement) : CuspCovolume.Statement := by
  intro D T
  obtain ⟨ε, hε, hεb⟩ := hCB D T
  set κ : ℝ := min 1 ε ^ (D.g + D.g) * (max 1 (1 / D.c))⁻¹ ^ T.r with hκ
  have hκpos : 0 < κ := by
    have h1 : 0 < min 1 ε := lt_min one_pos hε
    have h2 : 0 < max 1 (1 / D.c) := lt_max_of_lt_left one_pos
    positivity
  refine ⟨Real.sqrt κ, Real.sqrt_pos.mpr hκpos, ?_⟩
  intro p hpK hpU ℓ hℓ k v hv hind
  set τ := D.period p.1 ℓ with hτ
  obtain ⟨hYpos, hYc⟩ := hImPos D p.1 hpU ℓ hℓ
  have hS : (periodGram τ).PosDef := (hPG D.g τ hYpos).1
  obtain ⟨N, -, hN, hcov⟩ := hLC D.g τ k v hv hind
  obtain ⟨P, hPd, hPdet⟩ := hGP (D.g + D.g) (periodGram τ) hS k N hN
  have hlow : ∀ i, i < T.r → pivot (periodGram τ) i ≤ 1 / D.c := by
    intro i hi
    have hig : i < D.g := lt_of_lt_of_le hi T.r_le
    have hb := (hPB (D.g + D.g) (periodGram τ) hS (Fin.castAdd D.g ⟨i, hig⟩)).1
    simp only [Fin.val_castAdd] at hb
    rw [CuspCovolume.periodGram_castAdd] at hb
    exact hb.trans (CuspCovolume.inv_diag_le_of_ge hYpos D.c_pos hYc _)
  have hhigh : ∀ i, T.r ≤ i → i < D.g + D.g → ε ≤ pivot (periodGram τ) i := by
    intro i hri hid
    exact (hPB (D.g + D.g) (periodGram τ) hS ⟨i, hid⟩).2 ε hε fun y =>
      hεb p hpK hpU ℓ hℓ y ⟨i, hid⟩ hri
  have hprod := hPP (D.g + D.g) T.r (periodGram τ) hS (T.r_le.trans (Nat.le_add_right _ _))
    (1 / D.c) ε hε hlow hhigh P hPd
  rw [hcov, hLead D.g τ T.r T.r_le, ← Real.sqrt_mul hκpos.le]
  exact Real.sqrt_le_sqrt (hprod.trans hPdet)

end

end GroundTheory.Heights₂.Heights
end

