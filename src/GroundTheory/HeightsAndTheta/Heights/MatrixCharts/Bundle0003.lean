import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bounds
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCBounds

open Matrix
open scoped ComplexOrder

noncomputable section

variable (D : PeriodChartData)

theorem cusp_norm_lt {z : Fin D.n → ℂ} (hz : z ∈ D.U) (j : Fin D.a) :
    ‖cuspCoord D.a_le z j‖ < 1 :=
  D.U_subset hz (Fin.castLE D.a_le j)

theorem log_inv_sq_nonneg {w : ℂ} (hw : ‖w‖ < 1) : 0 ≤ Real.log (‖w‖ ^ 2)⁻¹ := by
  rw [Real.log_inv]
  exact neg_nonneg.mpr (Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg w) hw.le))

theorem exp_one_le_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) : Real.exp 1 ≤ D.radius z := by
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => log_inv_sq_nonneg (cusp_norm_lt D hz j)
  simp only [PeriodChartData.radius, chartRadius]
  linarith

theorem one_le_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) : 1 ≤ D.radius z := by
  have := exp_one_le_radius D hz
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem one_le_log_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) : 1 ≤ Real.log (D.radius z) := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (exp_one_le_radius D hz)

theorem cuspTime_le_radius {z : Fin D.n → ℂ} (hz : z ∈ D.U) (j : Fin D.a) :
    cuspTime D.a_le z j ≤ D.radius z := by
  have hlt := cusp_norm_lt D hz j
  have hL : 0 ≤ -Real.log ‖cuspCoord D.a_le z j‖ :=
    neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hlt.le)
  have hterm : Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹ = 2 * -Real.log ‖cuspCoord D.a_le z j‖ := by
    rw [Real.log_inv, Real.log_pow]; push_cast; ring
  have hsum : Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹ ≤
      ∑ i, Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹ :=
    Finset.single_le_sum (f := fun i => Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹)
      (fun i _ => log_inv_sq_nonneg (cusp_norm_lt D hz i)) (Finset.mem_univ j)
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have he := Real.exp_pos 1
  have h1 : cuspTime D.a_le z j = (2 * Real.pi)⁻¹ * -Real.log ‖cuspCoord D.a_le z j‖ := by
    rw [cuspTime, Real.log_inv]
  have h2 := mul_le_mul_of_nonneg_right hpi hL
  rw [h1]
  simp only [PeriodChartData.radius, chartRadius]
  linarith

theorem Y_transpose {z : Fin D.n → ℂ} (hz : z ∈ D.U) : (D.Y z)ᵀ = D.Y z := by
  ext j k
  simp only [transpose_apply, PeriodChartData.Y, chartImag, Matrix.add_apply, map_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [show D.τ0 z k j = D.τ0 z j k from by simpa using congrFun (congrFun (D.τ0_symm z hz) j) k]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show D.B i k j = D.B i j k from by simpa using (D.B_psd i).isHermitian.apply j k]

theorem exists_bound_imτ0 : ∃ M : ℝ, 0 ≤ M ∧
    ∀ p ∈ D.K, entrySum ((D.τ0 p.1).map Complex.im) ≤ M := by
  have hcont : ContinuousOn (fun z => entrySum ((D.τ0 z).map Complex.im)) D.U := by
    unfold entrySum
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
    simp only [map_apply]
    exact continuous_abs.comp_continuousOn
      (Complex.continuous_im.comp_continuousOn (D.τ0_analytic j k).continuousOn)
  have hKc : IsCompact (Prod.fst '' D.K) := D.isCompact_K.image continuous_fst
  have hsub : Prod.fst '' D.K ⊆ D.U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (D.K_subset hp).1
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max M 0, le_max_right _ _, fun p hp => ?_⟩
  have h := hM p.1 ⟨p, hp, rfl⟩
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

theorem quad_Y_le {z : Fin D.n → ℂ} (hz : z ∈ D.U) (M : ℝ)
    (hM : entrySum ((D.τ0 z).map Complex.im) ≤ M) (x : Fin D.g → ℝ) :
    x ⬝ᵥ (D.Y z *ᵥ x) ≤ (M + ∑ j, entrySum (D.B j)) * D.radius z * (x ⬝ᵥ x) := by
  have hr1 := one_le_radius D hz
  have hxx := dot_self_nonneg x
  have hM0 : 0 ≤ M := (entrySum_nonneg _).trans hM
  simp only [PeriodChartData.Y, chartImag]
  rw [add_mulVec, dotProduct_add, quad_sum]
  have h0 : x ⬝ᵥ ((D.τ0 z).map Complex.im *ᵥ x) ≤ M * D.radius z * (x ⬝ᵥ x) := by
    have h3 := (le_abs_self _).trans (abs_quad_le ((D.τ0 z).map Complex.im) x)
    have h2 : entrySum ((D.τ0 z).map Complex.im) * (x ⬝ᵥ x) ≤ M * D.radius z * (x ⬝ᵥ x) := by
      apply mul_le_mul_of_nonneg_right _ hxx
      nlinarith
    linarith
  have h1 : ∀ j, x ⬝ᵥ ((cuspTime D.a_le z j • D.B j) *ᵥ x) ≤
      entrySum (D.B j) * D.radius z * (x ⬝ᵥ x) := by
    intro j
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    have ht1 := cuspTime_le_radius D hz j
    have hq := (le_abs_self _).trans (abs_quad_le (D.B j) x)
    have hq0 := quad_nonneg (D.B_psd j) x
    have hr0 : 0 ≤ D.radius z := by linarith
    calc cuspTime D.a_le z j * (x ⬝ᵥ (D.B j *ᵥ x)) ≤ D.radius z * (entrySum (D.B j) * (x ⬝ᵥ x)) :=
          mul_le_mul ht1 hq hq0 hr0
      _ = _ := by ring
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h1 j
  rw [← Finset.sum_mul, ← Finset.sum_mul] at hsum
  linarith

theorem exists_Y_le : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ D.K,
    ((C * D.radius p.1) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_imτ0 D
  have hβ : 0 ≤ ∑ j, entrySum (D.B j) := Finset.sum_nonneg fun j _ => entrySum_nonneg _
  refine ⟨M + ∑ j, entrySum (D.B j) + 1, by positivity, fun p hp => ?_⟩
  have hz : p.1 ∈ D.U := (D.K_subset hp).1
  have hr1 := one_le_radius D hz
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, Y_transpose D hz]
  · rw [quad_smul_one_sub]
    have h := quad_Y_le D hz M (hM p hp) x
    have hxx := dot_self_nonneg x
    nlinarith

theorem injective_of_rank {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    Function.Injective F.mulVec := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin F)
  rw [Module.finrank_fin_fun] at h1
  have h2 : Module.finrank ℂ (LinearMap.ker F.mulVecLin) = 0 := by
    unfold Matrix.rank at h; omega
  have h3 : LinearMap.ker F.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h2
  exact LinearMap.ker_eq_bot.mp h3

theorem gram_posDef {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    (Fᴴ * F).PosDef :=
  PosDef.conjTranspose_mul_self F (injective_of_rank F h)

theorem continuousOn_f : ContinuousOn D.f (D.U ×ˢ D.V) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_matrix fun j k => (D.f_analytic j k).continuousOn.domRestrict

theorem exists_gram_bounds : ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ p ∈ D.K,
    δ ≤ ((D.f p)ᴴ * D.f p).det.re ∧ ((D.f p)ᴴ * D.f p).det.re ≤ M := by
  have hc : ContinuousOn (fun p => ((D.f p)ᴴ * D.f p).det.re) D.K := by
    have h := (continuousOn_f D).mono D.K_subset
    rw [continuousOn_iff_continuous_domRestrict] at h ⊢
    exact Complex.continuous_re.comp (h.matrix_conjTranspose.matrix_mul h).matrix_det
  have hpos : ∀ p ∈ D.K, 0 < ((D.f p)ᴴ * D.f p).det.re := fun p hp =>
    MCDet.re_det_pos (gram_posDef _ (D.f_rank p (D.K_subset hp)))
  rcases D.K.eq_empty_or_nonempty with hK | hK
  · exact ⟨1, 1, one_pos, one_pos, fun p hp => by simp [hK] at hp⟩
  obtain ⟨p0, hp0, hmin⟩ := D.isCompact_K.exists_isMinOn hK hc
  obtain ⟨M, hM⟩ := D.isCompact_K.exists_bound_of_continuousOn hc
  refine ⟨_, max M 1, hpos p0 hp0, by positivity, fun p hp => ⟨hmin hp, ?_⟩⟩
  have h := hM p hp
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

end

end GroundTheory.Heights₂.Heights.MCBounds
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshMatrix
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCPsh

open Matrix Metric Real
open scoped MatrixOrder ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

abbrev cx (Y : Matrix ι ι ℝ) : Matrix ι ι ℂ := Y.map (fun x : ℝ => (x : ℂ))

theorem cx_mul (Y Z : Matrix ι ι ℝ) : cx (Y * Z) = cx Y * cx Z :=
  Matrix.map_mul (f := Complex.ofRealHom)

theorem cx_one : cx (1 : Matrix ι ι ℝ) = 1 := Matrix.map_one _ (by simp) (by simp)

theorem cx_inv {Y : Matrix ι ι ℝ} (hY : IsUnit Y.det) : (cx Y)⁻¹ = cx Y⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← cx_mul, Matrix.nonsing_inv_mul _ hY, cx_one]

theorem cx_posDef {Y : Matrix ι ι ℝ} (hY : Y.PosDef) : (cx Y).PosDef := by
  have hsymm : ∀ i j, Y j i = Y i j := fun i j => by
    have := congrFun (congrFun hY.isHermitian i) j
    simpa [conjTranspose_apply] using this
  refine PosDef.of_dotProduct_mulVec_pos (hY.isHermitian.map _ fun x => by simp) fun x hx => ?_
  set a : ι → ℝ := fun i => (x i).re
  set b : ι → ℝ := fun i => (x i).im
  have hre : ∀ (u v : ℂ) (y : ℝ), (star u * ((y : ℂ) * v)).re = y * (u.re * v.re + u.im * v.im) :=
    fun u v y => by simp [Complex.mul_re, Complex.mul_im]; ring
  have him : ∀ (u v : ℂ) (y : ℝ), (star u * ((y : ℂ) * v)).im = y * (u.re * v.im - u.im * v.re) :=
    fun u v y => by simp [Complex.mul_re, Complex.mul_im]; ring
  have e1 : star x ⬝ᵥ (cx Y *ᵥ x) = ∑ i, ∑ j, star (x i) * ((Y i j : ℂ) * x j) := by
    simp [dotProduct, mulVec, Finset.mul_sum]
  have e2 : a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) =
      ∑ i, ∑ j, Y i j * ((x i).re * (x j).re + (x i).im * (x j).im) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib, a, b]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have e3 : ∑ i, ∑ j, Y i j * ((x i).re * (x j).im - (x i).im * (x j).re) = 0 := by
    have hswap : ∑ i, ∑ j, Y i j * ((x i).im * (x j).re) =
        ∑ i, ∑ j, Y i j * ((x i).re * (x j).im) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsymm]; ring
    simp only [mul_sub, Finset.sum_sub_distrib, hswap, sub_self]
  have key : star x ⬝ᵥ (cx Y *ᵥ x) = ((a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) : ℝ) : ℂ) := by
    rw [e1]
    apply Complex.ext
    · simp only [Complex.re_sum, hre, Complex.ofReal_re, e2]
    · simp only [Complex.im_sum, him, Complex.ofReal_im, e3]
  rw [key]
  have ha := hY.posSemidef.dotProduct_mulVec_nonneg a
  have hb := hY.posSemidef.dotProduct_mulVec_nonneg b
  simp only [star_trivial] at ha hb
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push Not at h; exact hx (funext h)
  have hpos : 0 < a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) := by
    by_cases hai : a = 0
    · have hbi : b ≠ 0 := by
        intro hbi
        apply hi
        apply Complex.ext
        · simpa using congrFun hai i
        · simpa using congrFun hbi i
      have := hY.dotProduct_mulVec_pos hbi
      simp only [star_trivial] at this
      linarith
    · have := hY.dotProduct_mulVec_pos hai
      simp only [star_trivial] at this
      linarith
  exact_mod_cast hpos

theorem exists_factor {A : Matrix κ κ ℂ} (hA : A.PosDef) :
    ∃ B : Matrix κ κ ℂ, IsUnit B.det ∧ A = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  refine ⟨B, ?_, hB⟩
  have hdet : A.det ≠ 0 := (hA.det_pos).ne'
  rw [hB, det_mul, star_eq_conjTranspose, det_conjTranspose] at hdet
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)

theorem mulVec_injective_of_rank {F : Matrix ι κ ℂ} (h : F.rank = Fintype.card κ) :
    Function.Injective F.mulVec := by
  have hrn := LinearMap.finrank_range_add_finrank_ker F.mulVecLin
  rw [← Matrix.rank, h, Module.finrank_fintype_fun_eq_card] at hrn
  have hk : LinearMap.ker F.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  exact LinearMap.ker_eq_bot.mp hk

theorem analyticOnNhd_det {s : Set ℂ} {M : ℂ → Matrix κ κ ℂ}
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun ζ => M ζ i j) s) :
    AnalyticOnNhd ℂ (fun ζ => (M ζ).det) s := by
  have : (fun ζ => (M ζ).det) =
      fun ζ => ∑ σ : Equiv.Perm κ, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M ζ (σ i) i := by
    funext ζ
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [this]
  intro z hz
  refine Finset.univ.analyticAt_fun_sum fun σ _ => ?_
  exact analyticAt_const.mul (Finset.univ.analyticAt_fun_prod fun i _ => hM _ _ z hz)

theorem re_trace_eq (W : Matrix ι κ ℂ) (Y : Matrix ι ι ℝ) :
    RCLike.re (Wᴴ * cx Y * W).trace =
      ∑ j, ∑ k, (∑ a, (star (W j a) * W k a).re) * Y j k := by
  calc RCLike.re (Wᴴ * cx Y * W).trace
      = ∑ a, ∑ k, ∑ j, (star (W j a) * W k a).re * Y j k := by
        simp only [trace, diag, mul_apply, conjTranspose_apply, map_apply, RCLike.re_to_complex,
          Complex.re_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
    _ = ∑ j, ∑ k, ∑ a, (star (W j a) * W k a).re * Y j k := by
        rw [Finset.sum_comm]
        rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
        rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.sum_mul]

end

end GroundTheory.Heights₂.Heights.MCPsh
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshMean
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCPsh

open Metric Real

noncomputable section

theorem circleAverage_of_analytic {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    circleAverage h 0 1 = h 0 := by
  apply DiffContOnCl.circleAverage
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball _ (by norm_num : |(1:ℝ)| ≠ 0), abs_one]
  exact hh.differentiableOn

theorem circleIntegrable_of_analytic {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    CircleIntegrable h 0 1 :=
  (hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable zero_le_one

theorem circleAverage_im_of_analytic {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    circleAverage (fun ζ => (h ζ).im) 0 1 = (h 0).im := by
  have := Complex.imCLM.circleAverage_comp_comm (circleIntegrable_of_analytic hh)
  rw [circleAverage_of_analytic hh] at this
  simpa [Function.comp_def] using this

theorem circleAverage_log_norm_of_ne_zero {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hne : ∀ ζ ∈ closedBall (0:ℂ) 1, h ζ ≠ 0) :
    circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 = Real.log ‖h 0‖ := by
  have hh' : AnalyticOnNhd ℂ h (closedBall 0 |(1 : ℝ)|) := by simpa using hh
  rw [hh'.circleAverage_log_norm one_ne_zero (hne 0 (mem_closedBall_self zero_le_one))]
  have hzero : ∀ u : ℂ, (MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) *
      Real.log (1 * ‖(0:ℂ) - u‖⁻¹) = 0 := by
    intro u
    by_cases hu : u ∈ closedBall (0:ℂ) |(1:ℝ)|
    · have hu' : u ∈ closedBall (0:ℂ) 1 := by simpa using hu
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hh' hu, (hh' u hu).analyticOrderAt_eq_zero.mpr (hne u hu')]
      simp
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  have hz2 : ∀ u : ℂ, -((MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) * Real.log ‖u‖) = 0 := by
    intro u
    have := hzero u
    simp only [one_mul, zero_sub, norm_neg, Real.log_inv, mul_neg] at this
    linarith
  simp only [one_mul, zero_sub, norm_neg, Real.log_inv, mul_neg, hz2, finsum_zero, zero_add]

end

end GroundTheory.Heights₂.Heights.MCPsh
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCCusp

open Matrix GroundTheory.Heights₂.Heights.MCSchur

noncomputable section

section QF

variable {ι : Type*} [Fintype ι]

theorem dot_mulVec_symm {Z : Matrix ι ι ℝ} (hZ : Zᵀ = Z) (u w : ι → ℝ) :
    u ⬝ᵥ (Z *ᵥ w) = w ⬝ᵥ (Z *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hZ, dotProduct_comm]

theorem transpose_eq_of_posSemidef {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) : Zᵀ = Z := by
  have := hZ.1
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

theorem qf_nonneg {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (u : ι → ℝ) : 0 ≤ qf Z u := by
  have := hZ.dotProduct_mulVec_nonneg u
  simpa [qf] using this

theorem bil_sq_le {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (u w : ι → ℝ) :
    (w ⬝ᵥ (Z *ᵥ u)) ^ 2 ≤ qf Z w * qf Z u := by
  have hs := transpose_eq_of_posSemidef hZ
  have key : ∀ x : ℝ, 0 ≤ qf Z w * (x * x) + (-2 * (w ⬝ᵥ (Z *ᵥ u))) * x + qf Z u := by
    intro x
    have h := qf_nonneg hZ (u - x • w)
    have e : qf Z (u - x • w) = qf Z w * (x * x) + (-2 * (w ⬝ᵥ (Z *ᵥ u))) * x + qf Z u := by
      simp only [qf, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      rw [dot_mulVec_symm hs u w]
      ring
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

variable [DecidableEq ι]

theorem sq_le_inv_diag_mul_qf {Z : Matrix ι ι ℝ} (hZ : Z.PosDef) (x : ι → ℝ) (i : ι) :
    x i ^ 2 ≤ Z⁻¹ i i * qf Z x := by
  have hs := transpose_eq_of_posSemidef hZ.posSemidef
  have hu : IsUnit Z.det := (Matrix.isUnit_iff_isUnit_det _).mp hZ.isUnit
  set w := Z⁻¹ *ᵥ Pi.single i 1 with hw
  have hZw : Z *ᵥ w = Pi.single i 1 := by
    rw [hw, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have h1 : w ⬝ᵥ (Z *ᵥ x) = x i := by
    rw [dot_mulVec_symm hs, hZw, dotProduct_single, mul_one]
  have h2 : qf Z w = Z⁻¹ i i := by
    rw [qf, hZw, dotProduct_single, mul_one, hw, mulVec_single]
    simp
  have := bil_sq_le hZ.posSemidef x w
  rwa [h1, h2] at this

theorem inv_diag_le {Z : Matrix ι ι ℝ} (hZ : Z.PosDef) (i : ι) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x, ε * x i ^ 2 ≤ qf Z x) : Z⁻¹ i i ≤ 1 / ε := by
  have hs := transpose_eq_of_posSemidef hZ.posSemidef
  have hu : IsUnit Z.det := (Matrix.isUnit_iff_isUnit_det _).mp hZ.isUnit
  set w := Z⁻¹ *ᵥ Pi.single i 1 with hw
  have hZw : Z *ᵥ w = Pi.single i 1 := by
    rw [hw, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hwi : w i = Z⁻¹ i i := by rw [hw, mulVec_single]; simp
  have h2 : qf Z w = Z⁻¹ i i := by rw [qf, hZw, dotProduct_single, mul_one, hwi]
  have hpos : 0 < Z⁻¹ i i := hZ.inv.diag_pos
  have := h w
  rw [h2, hwi] at this
  rw [le_div_iff₀ hε]
  nlinarith

end QF

end

end GroundTheory.Heights₂.Heights.MCCusp
end

