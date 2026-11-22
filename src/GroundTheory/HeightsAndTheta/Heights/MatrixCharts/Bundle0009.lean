import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0008

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PAnalyticDerivBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem AnalyticDerivBound.proof : AnalyticDerivBound.Statement := by
  intro E _ _ f U K hU hf hK hKU
  have hcd : ContDiffOn ℂ 1 f U := hf.contDiffOn hU.uniqueDiffOn
  have hf' : ContinuousOn (fderiv ℂ f) U := hcd.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn (hcd.continuousOn.mono hKU)
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn (hf'.mono hKU)
  refine ⟨max (max C₁ C₂) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
  have hd : DifferentiableAt ℂ f x := (hf x (hKU hx)).differentiableAt
  refine ⟨hd.restrictScalars ℝ, ?_, ?_⟩
  · exact (hC₁ x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [hd.fderiv_restrictScalars ℝ, ContinuousLinearMap.norm_restrictScalars]
    exact (hC₂ x hx).trans ((le_max_right _ _).trans (le_max_left _ _))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartFrameDeriv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

namespace MCChartFrameDeriv

theorem le_one_add_sum {g r : ℕ} (A : Fin g → Fin r → ℝ) (hA : ∀ j l, 0 < A j l) (j : Fin g)
    (l : Fin r) : A j l ≤ 1 + ∑ j', ∑ l', A j' l' := by
  have h1 : A j l ≤ ∑ l', A j l' :=
    Finset.single_le_sum (f := fun l' => A j l') (fun l' _ => (hA j l').le) (Finset.mem_univ l)
  have h2 : ∑ l', A j l' ≤ ∑ j', ∑ l', A j' l' :=
    Finset.single_le_sum (f := fun j' => ∑ l', A j' l')
      (fun j' _ => Finset.sum_nonneg fun l' _ => (hA j' l').le) (Finset.mem_univ j)
  linarith

end MCChartFrameDeriv

open MCChartFrameDeriv in

theorem ChartFrameDeriv.proof (h₁ : AnalyticDerivBound.Statement) : ChartFrameDeriv.Statement := by
  intro D
  have hU : IsOpen (D.U ×ˢ D.V) := D.isOpen_U.prod D.isOpen_V
  have hex : ∀ j l, ∃ A : ℝ, 0 < A ∧ ∀ x ∈ D.K,
      DifferentiableAt ℝ (fun q => D.f q j l) x ∧ ‖D.f x j l‖ ≤ A ∧
        ‖fderiv ℝ (fun q => D.f q j l) x‖ ≤ A := fun j l =>
    h₁ (fun q => D.f q j l) (D.U ×ˢ D.V) D.K hU (D.f_analytic j l) D.isCompact_K D.K_subset
  choose A hApos hA using hex
  have hsum : 0 ≤ ∑ j, ∑ l, A j l :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => (hApos j l).le
  refine ⟨1 + ∑ j, ∑ l, A j l, by linarith, fun p hp j l => ?_⟩
  obtain ⟨hd, hb, hb'⟩ := hA j l p hp
  have hle := le_one_add_sum A hApos j l
  exact ⟨hd, hb.trans hle, hb'.trans hle⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartGradient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace MCChartGradient

theorem u_eq (D : PeriodChartData) :
    D.u = fun q => logDetGram (D.Y q.1) (D.f q) := rfl

theorem bound_arith (S A C₁ δ r e : ℝ) (k : ℕ) (hS : 0 ≤ S) (hA : 0 ≤ A) (hC₁ : 0 < C₁)
    (hδ : 0 < δ) (hr : 0 < r) (he : 1 ≤ e) :
    S * (1 + A * e) / ((C₁ * r)⁻¹ ^ k * δ) ≤ S * (1 + A) * C₁ ^ k / δ * r ^ k * e := by
  have hCr : 0 < C₁ * r := mul_pos hC₁ hr
  have h1 : S * (1 + A * e) / ((C₁ * r)⁻¹ ^ k * δ) =
      S * (1 + A * e) * (C₁ ^ k * r ^ k / δ) := by
    rw [inv_pow, ← mul_pow]
    field_simp
  rw [h1]
  have h2 : S * (1 + A * e) ≤ S * (1 + A) * e := by
    nlinarith [mul_le_mul_of_nonneg_left he hS]
  have h3 : 0 ≤ C₁ ^ k * r ^ k / δ := by positivity
  calc S * (1 + A * e) * (C₁ ^ k * r ^ k / δ) ≤ S * (1 + A) * e * (C₁ ^ k * r ^ k / δ) :=
        mul_le_mul_of_nonneg_right h2 h3
    _ = S * (1 + A) * C₁ ^ k / δ * r ^ k * e := by ring

theorem pow_le_rpow_of_le {r C : ℝ} {k : ℕ} (hr : 1 ≤ r) (hk : (k : ℝ) ≤ C) :
    r ^ k ≤ r ^ C := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hr hk

end MCChartGradient

open MCChartGradient in

theorem ChartGradient.proof (h₁ : LogDetGramDeriv.Statement) (h₂ : ChartFrameDeriv.Statement)
    (h₃ : ChartImagDeriv.Statement) (h₄ : ChartBounds.Statement) : ChartGradient.Statement := by
  intro D
  obtain ⟨K₀, hK₀, hK⟩ := h₁ D.g D.rk
  obtain ⟨AF, hAF, hF⟩ := h₂ D
  obtain ⟨AY, hAY, hY⟩ := h₃ D
  obtain ⟨C₁, hC₁, hB⟩ := h₄ D
  obtain ⟨δ, M, hδ, -, hG⟩ := MCBounds.exists_gram_bounds D
  have hc : 0 ≤ D.c⁻¹ := inv_nonneg.mpr D.c_pos.le
  set S : ℝ := K₀ * (1 + AF) ^ (2 * D.rk) * (1 + D.c⁻¹) ^ (D.rk + 1) with hSdef
  have hS : 0 ≤ S := by positivity
  set K' : ℝ := S * (1 + AY) * C₁ ^ D.rk / δ with hK'def
  have hK'0 : 0 ≤ K' := by positivity
  have hC1 : (1 : ℝ) ≤ max K' (max (D.rk : ℝ) 1) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max K' (max (D.rk : ℝ) 1), lt_of_lt_of_le one_pos hC1, fun p hp hps => ?_⟩
  set C := max K' (max (D.rk : ℝ) 1) with hCdef
  have hz : p.1 ∈ D.U := (D.K_subset hp).1
  have hr1 : 1 ≤ D.radius p.1 := MCBounds.one_le_radius D hz
  set r := D.radius p.1 with hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have he : 1 ≤ Real.exp (r / 2) := Real.one_le_exp (by linarith)
  obtain ⟨hYc, -, hdet, -, -, -⟩ := hB p hp hps
  have hCr : 0 < C₁ * r := mul_pos hC₁ hr0
  have hμpos : 0 < (C₁ * r)⁻¹ ^ D.rk * δ := mul_pos (pow_pos (inv_pos.mpr hCr) _) hδ
  have hμ : (C₁ * r)⁻¹ ^ D.rk * δ ≤
      ((D.f p)ᴴ * (D.Y p.1)⁻¹.map (fun x : ℝ => (x : ℂ)) * D.f p).det.re :=
    le_trans (mul_le_mul_of_nonneg_left (hG p hp).1 (pow_nonneg (inv_pos.mpr hCr).le _)) hdet
  obtain ⟨hd, hn⟩ := hK (E := (Fin D.n → ℂ) × (Fin D.m → ℂ)) D.f (fun q => D.Y q.1) p AF
    (AY * Real.exp (r / 2)) D.c ((C₁ * r)⁻¹ ^ D.rk * δ) D.c_pos hμpos hAF.le
    (mul_nonneg hAY.le (Real.exp_pos _).le) (hF p hp) (fun j l => hY p hp hps j l) hYc hμ
  rw [u_eq]
  refine ⟨hd, hn.trans ?_⟩
  have hb := bound_arith S AY C₁ δ r (Real.exp (r / 2)) D.rk hS hAY.le hC₁ hδ hr0 he
  refine hb.trans ?_
  have hpow : r ^ D.rk ≤ r ^ C :=
    pow_le_rpow_of_le hr1 ((le_max_left _ _).trans (le_max_right _ _))
  have hKC : K' ≤ C := le_max_left _ _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hKC hpow (pow_nonneg hr0.le _) (by linarith)) (Real.exp_pos _).le

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartImagDeriv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace MCChartImagDeriv

theorem Y_apply (D : PeriodChartData) (z : Fin D.n → ℂ) (j l : Fin D.g) :
    D.Y z j l = (D.τ0 z j l).im + ∑ i, cuspTime D.a_le z i * D.B i j l := by
  simp [PeriodChartData.Y, chartImag, Matrix.add_apply, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]

end MCChartImagDeriv

open MCChartImagDeriv in

theorem ChartImagDeriv.proof (h₁ : AnalyticDerivBound.Statement) (h₂ : CuspTimeDeriv.Statement) :
    ChartImagDeriv.Statement := by
  intro D
  have hKc : IsCompact (Prod.fst '' D.K) := D.isCompact_K.image continuous_fst
  have hKs : Prod.fst '' D.K ⊆ D.U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (D.K_subset hp).1
  have hA := fun j l => h₁ (fun z => D.τ0 z j l) D.U (Prod.fst '' D.K) D.isOpen_U
    (D.τ0_analytic j l) hKc hKs
  choose A hApos hA using hA
  set A₁ : ℝ := ∑ j, ∑ l, A j l with hA₁def
  set S : ℝ := ∑ i, ∑ j, ∑ l, |D.B i j l| with hSdef
  have hA_le : ∀ j l, A j l ≤ A₁ := by
    intro j l
    calc A j l ≤ ∑ l', A j l' :=
          Finset.single_le_sum (fun l' _ => (hApos j l').le) (Finset.mem_univ l)
      _ ≤ A₁ := Finset.single_le_sum (f := fun j' => ∑ l', A j' l')
          (fun j' _ => Finset.sum_nonneg fun l' _ => (hApos j' l').le) (Finset.mem_univ j)
  have hB_le : ∀ j l, ∑ i, |D.B i j l| ≤ S := by
    intro j l
    refine Finset.sum_le_sum fun i _ => ?_
    calc |D.B i j l| ≤ ∑ l', |D.B i j l'| :=
          Finset.single_le_sum (fun l' _ => abs_nonneg (D.B i j l')) (Finset.mem_univ l)
      _ ≤ ∑ j', ∑ l', |D.B i j' l'| := Finset.single_le_sum (f := fun j' => ∑ l', |D.B i j' l'|)
          (fun j' _ => Finset.sum_nonneg fun l' _ => abs_nonneg _) (Finset.mem_univ j)
  have hA₁ : 0 ≤ A₁ := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => (hApos j l).le
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun l _ => abs_nonneg _
  refine ⟨A₁ + S + 1, by linarith, ?_⟩
  intro p hp hpU j l
  have hx : p.1 ∈ Prod.fst '' D.K := ⟨p, hp, rfl⟩
  obtain ⟨hd, -, hb⟩ := hA j l p.1 hx

  set L₁ := (Complex.imCLM.comp (fderiv ℝ (fun z => D.τ0 z j l) p.1)).comp
    (ContinuousLinearMap.fst ℝ (Fin D.n → ℂ) (Fin D.m → ℂ)) with hL₁
  have h1 : HasFDerivAt (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) => (D.τ0 q.1 j l).im) L₁ p :=
    Complex.imCLM.hasFDerivAt.comp p (hd.hasFDerivAt.comp p hasFDerivAt_fst)

  have hT := fun i => h₂ D p.1 hpU i
  set L₂ := fun i => (fderiv ℝ (fun w => cuspTime D.a_le w i) p.1).comp
    (ContinuousLinearMap.fst ℝ (Fin D.n → ℂ) (Fin D.m → ℂ)) with hL₂
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin D.a)), HasFDerivAt
      (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) => cuspTime D.a_le q.1 i * D.B i j l)
      (D.B i j l • L₂ i) p :=
    fun i _ => ((hT i).1.hasFDerivAt.comp p hasFDerivAt_fst).mul_const (D.B i j l)
  have hfun : (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) => D.Y q.1 j l) =
      fun q => (D.τ0 q.1 j l).im + ∑ i, cuspTime D.a_le q.1 i * D.B i j l := by
    funext q
    exact Y_apply D q.1 j l
  have hall : HasFDerivAt
      (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) =>
        (D.τ0 q.1 j l).im + ∑ i, cuspTime D.a_le q.1 i * D.B i j l)
      (L₁ + ∑ i, D.B i j l • L₂ i) p :=
    h1.add (HasFDerivAt.fun_sum h2)
  rw [hfun]
  refine ⟨hall.differentiableAt, ?_⟩
  rw [hall.fderiv]
  have hfst : ‖ContinuousLinearMap.fst ℝ (Fin D.n → ℂ) (Fin D.m → ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.norm_fst_le _ _ _
  have hE1 : 1 ≤ Real.exp (D.radius p.1 / 2) :=
    Real.one_le_exp (by linarith [MCBounds.one_le_radius D hpU.1])
  have hn1 : ‖L₁‖ ≤ A₁ := by
    calc ‖L₁‖ ≤ ‖Complex.imCLM.comp (fderiv ℝ (fun z => D.τ0 z j l) p.1)‖ *
          ‖ContinuousLinearMap.fst ℝ (Fin D.n → ℂ) (Fin D.m → ℂ)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Complex.imCLM.comp (fderiv ℝ (fun z => D.τ0 z j l) p.1)‖ * 1 :=
          mul_le_mul_of_nonneg_left hfst (norm_nonneg _)
      _ ≤ ‖(Complex.imCLM : ℂ →L[ℝ] ℝ)‖ * ‖fderiv ℝ (fun z => D.τ0 z j l) p.1‖ := by
          rw [mul_one]; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ A₁ := by rw [Complex.imCLM_norm, one_mul]; exact hb.trans (hA_le j l)
  have hn2 : ∀ i, ‖D.B i j l • L₂ i‖ ≤ |D.B i j l| * Real.exp (D.radius p.1 / 2) := by
    intro i
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc ‖L₂ i‖ ≤ ‖fderiv ℝ (fun w => cuspTime D.a_le w i) p.1‖ *
          ‖ContinuousLinearMap.fst ℝ (Fin D.n → ℂ) (Fin D.m → ℂ)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Real.exp (D.radius p.1 / 2) * 1 :=
          mul_le_mul (hT i).2 hfst (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (D.radius p.1 / 2) := mul_one _
  have hsum : ‖∑ i, D.B i j l • L₂ i‖ ≤ S * Real.exp (D.radius p.1 / 2) := by
    calc ‖∑ i, D.B i j l • L₂ i‖ ≤ ∑ i, ‖D.B i j l • L₂ i‖ := norm_sum_le _ _
      _ ≤ ∑ i, |D.B i j l| * Real.exp (D.radius p.1 / 2) := Finset.sum_le_sum fun i _ => hn2 i
      _ = (∑ i, |D.B i j l|) * Real.exp (D.radius p.1 / 2) := (Finset.sum_mul _ _ _).symm
      _ ≤ S * Real.exp (D.radius p.1 / 2) :=
          mul_le_mul_of_nonneg_right (hB_le j l) (Real.exp_pos _).le
  calc ‖L₁ + ∑ i, D.B i j l • L₂ i‖ ≤ ‖L₁‖ + ‖∑ i, D.B i j l • L₂ i‖ := norm_add_le _ _
    _ ≤ A₁ * Real.exp (D.radius p.1 / 2) + S * Real.exp (D.radius p.1 / 2) := by
        gcongr
        calc ‖L₁‖ ≤ A₁ := hn1
          _ = A₁ * 1 := (mul_one _).symm
          _ ≤ A₁ * Real.exp (D.radius p.1 / 2) := mul_le_mul_of_nonneg_left hE1 hA₁
    _ ≤ (A₁ + S + 1) * Real.exp (D.radius p.1 / 2) := by nlinarith [Real.exp_pos (D.radius p.1 / 2)]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspTimeDeriv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace MCCuspTimeDeriv

theorem lipschitz_norm_coord {n : ℕ} (c : Fin n) :
    LipschitzWith 1 (fun w : Fin n → ℂ => ‖w c‖) := by
  have h := (lipschitzWith_one_norm (E := ℂ)).comp (LipschitzWith.eval (α := fun _ : Fin n => ℂ) c)
  rw [mul_one] at h
  exact h

theorem inv_le_exp_half_log {x : ℝ} (hx : 0 < x) :
    x⁻¹ ≤ Real.exp (Real.log (x ^ 2)⁻¹ / 2) := by
  have h : Real.log (x ^ 2)⁻¹ / 2 = Real.log x⁻¹ := by
    rw [Real.log_inv, Real.log_inv, Real.log_pow]; push_cast; ring
  rw [h, Real.exp_log (inv_pos.mpr hx)]

end MCCuspTimeDeriv

open MCCuspTimeDeriv in

theorem CuspTimeDeriv.proof : CuspTimeDeriv.Statement := by
  intro D z hz i
  set c : Fin D.n := Fin.castLE D.a_le i with hc
  have hz0 : z c ≠ 0 := hz.2 i
  have hlt : ‖z c‖ < 1 := MCBounds.cusp_norm_lt D hz.1 i
  have hpos : 0 < ‖z c‖ := norm_pos_iff.mpr hz0

  let N : (Fin D.n → ℂ) → ℝ := fun w => ‖w c‖
  let φ : ℝ → ℝ := fun y => (2 * Real.pi)⁻¹ * -Real.log y
  have hfun : (fun w => cuspTime D.a_le w i) = φ ∘ N := by
    funext w
    simp only [cuspTime, cuspCoord, φ, N, Function.comp, Real.log_inv, hc]
  have hNd : DifferentiableAt ℝ N z :=
    DifferentiableAt.norm ℂ (differentiableAt_apply (𝕜 := ℝ) c z) hz0
  have hφ : HasDerivAt φ ((2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹) (N z) :=
    ((Real.hasDerivAt_log hpos.ne').neg).const_mul _
  have hcomp : HasFDerivAt (φ ∘ N) (((2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹) • fderiv ℝ N z) z :=
    hφ.comp_hasFDerivAt z hNd.hasFDerivAt
  rw [hfun]
  refine ⟨hcomp.differentiableAt, ?_⟩
  rw [hcomp.fderiv, norm_smul]
  have hNle : ‖fderiv ℝ N z‖ ≤ 1 := by
    have := norm_fderiv_le_of_lipschitz ℝ (x₀ := z) (lipschitz_norm_coord c)
    simpa using this
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have hpi0 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hcoef : ‖(2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹‖ ≤ (‖z c‖)⁻¹ := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hpi0, abs_of_pos (inv_pos.mpr hpos)]
    exact mul_le_of_le_one_left (inv_pos.mpr hpos).le hpi

  have hterm : Real.log (‖z c‖ ^ 2)⁻¹ ≤ D.radius z := by
    have hsum : Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹ ≤
        ∑ j, Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹ :=
      Finset.single_le_sum (f := fun j => Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹)
        (fun j _ => MCBounds.log_inv_sq_nonneg (MCBounds.cusp_norm_lt D hz.1 j)) (Finset.mem_univ i)
    have he := Real.exp_pos 1
    show Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹ ≤ _
    simp only [PeriodChartData.radius, chartRadius]
    linarith
  have hexp : (‖z c‖)⁻¹ ≤ Real.exp (D.radius z / 2) :=
    (inv_le_exp_half_log hpos).trans (Real.exp_le_exp.mpr (by linarith))
  calc ‖(2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹‖ * ‖fderiv ℝ N z‖ ≤ (‖z c‖)⁻¹ * 1 :=
        mul_le_mul hcoef hNle (norm_nonneg _) (inv_pos.mpr hpos).le
    _ ≤ Real.exp (D.radius z / 2) := by rw [mul_one]; exact hexp

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PGramEntryDeriv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace MCGramEntryDeriv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem comp_linearIsometry {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : F' →ₗᵢ[ℝ] ℂ) (φ : F' → ℂ) (hφ : ∀ x, L x = φ x) {f : E → F'} {p : E}
    (hf : DifferentiableAt ℝ f p) :
    DifferentiableAt ℝ (fun q => φ (f q)) p ∧
      ‖fderiv ℝ (fun q => φ (f q)) p‖ = ‖fderiv ℝ f p‖ := by
  have hfun : (fun q => φ (f q)) = fun q => L (f q) := funext fun q => (hφ _).symm
  have hL : HasFDerivAt (fun q => L (f q)) (L.toContinuousLinearMap.comp (fderiv ℝ f p)) p :=
    L.toContinuousLinearMap.hasFDerivAt.comp p hf.hasFDerivAt
  rw [hfun]
  exact ⟨hL.differentiableAt, by rw [hL.fderiv, L.norm_toContinuousLinearMap_comp]⟩

theorem triple {u v w : E → ℂ} {p : E} (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) (hw : DifferentiableAt ℝ w p) :
    DifferentiableAt ℝ (fun q => u q * v q * w q) p ∧
      ‖fderiv ℝ (fun q => u q * v q * w q) p‖ ≤
        ‖fderiv ℝ u p‖ * ‖v p‖ * ‖w p‖ + ‖u p‖ * ‖fderiv ℝ v p‖ * ‖w p‖ +
          ‖u p‖ * ‖v p‖ * ‖fderiv ℝ w p‖ := by
  have huv : DifferentiableAt ℝ (fun q => u q * v q) p := hu.mul hv
  refine ⟨huv.mul hw, ?_⟩
  rw [fderiv_fun_mul huv hw, fderiv_fun_mul hu hv]
  have h1 := norm_add_le ((u p * v p) • fderiv ℝ w p)
    (w p • (u p • fderiv ℝ v p + v p • fderiv ℝ u p))
  have h2 := norm_add_le (u p • fderiv ℝ v p) (v p • fderiv ℝ u p)
  rw [norm_smul, norm_smul, norm_mul] at h1
  rw [norm_smul, norm_smul] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (w p))
  nlinarith

theorem mul_three_le_mul_three {x y z X Y W : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hx : x ≤ X)
    (hy : y ≤ Y) (hz : z ≤ W) : x * y * z ≤ X * Y * W :=
  mul_le_mul (mul_le_mul hx hy hy0 (hx0.trans hx)) hz hz0
    (mul_nonneg (hx0.trans hx) (hy0.trans hy))

end MCGramEntryDeriv

open MCGramEntryDeriv in

theorem GramEntryDeriv.proof : GramEntryDeriv.Statement := by
  intro E _ _ g k F Z p a e e' hF hZ j l
  have hent : ∀ q, ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l =
      ∑ t, ∑ s, star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l := by
    intro q
    simp [Matrix.mul_apply, Finset.sum_mul]
  have hfun : (fun q => ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l) =
      fun q => ∑ t, ∑ s, star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l := funext hent
  rw [hfun, hent p]
  have hterm : ∀ t s : Fin g,
      DifferentiableAt ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p ∧
      ‖star (F p s j) * ((Z p s t : ℝ) : ℂ) * F p t l‖ ≤ a ^ 2 * e ∧
      ‖fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p‖ ≤
        2 * a ^ 2 * e + a ^ 2 * e' := by
    intro t s
    obtain ⟨hd1, hn1, hD1⟩ := hF s j
    obtain ⟨hd3, hn3, hD3⟩ := hF t l
    obtain ⟨hd2, hn2, hD2⟩ := hZ s t
    obtain ⟨hu, hu'⟩ := comp_linearIsometry Complex.conjLIE.toLinearIsometry
      (fun z : ℂ => star z) (fun z => rfl) hd1
    obtain ⟨hv, hv'⟩ := comp_linearIsometry Complex.ofRealLI
      (fun x : ℝ => (x : ℂ)) (fun x => rfl) hd2
    obtain ⟨hdiff, hbound⟩ := triple hu hv hd3
    have hnu : ‖star (F p s j)‖ ≤ a := by rw [norm_star]; exact hn1
    have hnv : ‖((Z p s t : ℝ) : ℂ)‖ ≤ e := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hn2
    have hDu : ‖fderiv ℝ (fun q => star (F q s j)) p‖ ≤ a := hu'.le.trans hD1
    have hDv : ‖fderiv ℝ (fun q => ((Z q s t : ℝ) : ℂ)) p‖ ≤ e' := hv'.le.trans hD2
    refine ⟨hdiff, ?_, ?_⟩
    · rw [norm_mul, norm_mul]
      calc ‖star (F p s j)‖ * ‖((Z p s t : ℝ) : ℂ)‖ * ‖F p t l‖ ≤ a * e * a :=
            mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hnu hnv hn3
        _ = a ^ 2 * e := by ring
    · refine hbound.trans ?_
      have b1 := mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hDu hnv hn3
      have b2 := mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hnu hDv hn3
      have b3 := mul_three_le_mul_three (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hnu hnv hD3
      nlinarith
  have hH : HasFDerivAt (fun q => ∑ t, ∑ s, star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l)
      (∑ t, ∑ s, fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p) p :=
    HasFDerivAt.fun_sum fun t _ => HasFDerivAt.fun_sum fun s _ => (hterm t s).1.hasFDerivAt
  refine ⟨hH.differentiableAt, ?_, ?_⟩
  · calc ‖∑ t, ∑ s, star (F p s j) * ((Z p s t : ℝ) : ℂ) * F p t l‖
          ≤ ∑ t : Fin g, ∑ s : Fin g, ‖star (F p s j) * ((Z p s t : ℝ) : ℂ) * F p t l‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => norm_sum_le _ _)
      _ ≤ ∑ t : Fin g, ∑ s : Fin g, a ^ 2 * e :=
            Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun s _ => (hterm t s).2.1
      _ = (g : ℝ) ^ 2 * a ^ 2 * e := by simp [Finset.sum_const]; ring
  · rw [hH.fderiv]
    calc ‖∑ t, ∑ s, fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p‖
          ≤ ∑ t : Fin g, ∑ s : Fin g,
              ‖fderiv ℝ (fun q => star (F q s j) * ((Z q s t : ℝ) : ℂ) * F q t l) p‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => norm_sum_le _ _)
      _ ≤ ∑ t : Fin g, ∑ s : Fin g, (2 * a ^ 2 * e + a ^ 2 * e') :=
            Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun s _ => (hterm t s).2.2
      _ = (g : ℝ) ^ 2 * (2 * a ^ 2 * e + a ^ 2 * e') := by simp [Finset.sum_const]; ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace MCInvEntryBound

theorem single_dot_mulVec_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (j l : ι) : Pi.single j (1 : ℝ) ⬝ᵥ (A *ᵥ Pi.single l 1) = A j l := by
  simp [mulVec_single, single_dotProduct]

theorem inv_diag_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (Y - c • (1 : Matrix ι ι ℝ)).PosSemidef) (j : ι) :
    0 ≤ Y⁻¹ j j ∧ Y⁻¹ j j ≤ c⁻¹ := by
  have hinv : (Y⁻¹).PosSemidef := (MCBounds.posDef_of_ge hc h).inv.posSemidef
  have hle := MCBounds.quad_nonneg (MCBounds.inv_le_of_ge hc h) (Pi.single j 1)
  have hge := MCBounds.quad_nonneg hinv (Pi.single j 1)
  rw [single_dot_mulVec_single] at hle hge
  refine ⟨hge, ?_⟩
  simpa [Matrix.sub_apply, Matrix.smul_apply] using hle

end MCInvEntryBound

theorem InvEntryBound.proof : InvEntryBound.Statement := by
  intro g Y c hc h j l
  have hinv : (Y⁻¹).PosSemidef := (MCBounds.posDef_of_ge hc h).inv.posSemidef
  have hcs := MCBounds.quad_cs hinv (Pi.single j 1) (Pi.single l 1)
  simp only [MCInvEntryBound.single_dot_mulVec_single] at hcs
  obtain ⟨hj0, hj⟩ := MCInvEntryBound.inv_diag_bounds hc h j
  obtain ⟨hl0, hl⟩ := MCInvEntryBound.inv_diag_bounds hc h l
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hsq : (Y⁻¹ j l) ^ 2 ≤ c⁻¹ ^ 2 := by
    calc (Y⁻¹ j l) ^ 2 ≤ Y⁻¹ j j * Y⁻¹ l l := hcs
      _ ≤ c⁻¹ * c⁻¹ := mul_le_mul hj hl hl0 hci
      _ = c⁻¹ ^ 2 := (sq _).symm
  exact abs_le_of_sq_le_sq' hsq hci |> fun h => abs_le.mpr h

end

end GroundTheory.Heights₂.Heights
end

