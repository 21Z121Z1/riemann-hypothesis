import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenPolar
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ComplexHessianIsHermitianOfContDiffAt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001

-- bundled from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LeviOneEqLaplacianThm
section
open MeasureTheory Set Filter Topology InnerProductSpace
open scoped Laplacian

namespace ReciprocityTheory.AnForm.A

open GreenFunction

noncomputable section

theorem exists_R_of_compact {F : Type} [NormedAddCommGroup F] {u : F → ℝ}
    (hc : HasCompactSupport u) : ∃ R > 0, ∀ q, q ∈ tsupport u → ‖q‖ ≤ R := by
  obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : F)).1 hc.isCompact.isBounded
  refine ⟨max R0 0 + 1, by positivity, fun q hq => ?_⟩
  have := hR0 hq
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R0 0]

theorem leviOne (u : ℂ → ℝ) (z : ℂ) :
    ReciprocityTheory.AnForm.levi (fun w : Fin 1 → ℂ => u (w 0)) (fun _ => z) (Pi.single 0 1) =
      Δ u z / 4 := by
  set e0 : (Fin 1 → ℂ) ≃L[ℝ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ with he0
  set Φ : (ℂ →L[ℝ] ℝ) ≃L[ℝ] ((Fin 1 → ℂ) →L[ℝ] ℝ) :=
    e0.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) with hΦ
  have h1 : (fun w : Fin 1 → ℂ => u (w 0)) = u ∘ e0 := rfl
  have h2 : fderiv ℝ (u ∘ e0) = Φ ∘ (fderiv ℝ u ∘ e0) := by
    funext w
    rw [e0.comp_right_fderiv]
    ext v
    simp [Φ]
  have h3 : ∀ x, fderiv ℝ (Φ ∘ (fderiv ℝ u ∘ e0)) x =
      (Φ : (ℂ →L[ℝ] ℝ) →L[ℝ] ((Fin 1 → ℂ) →L[ℝ] ℝ)).comp
        ((fderiv ℝ (fderiv ℝ u) (e0 x)).comp (e0 : (Fin 1 → ℂ) →L[ℝ] ℂ)) := fun x => by
    rw [Φ.comp_fderiv, e0.comp_right_fderiv]
  simp only [ReciprocityTheory.AnForm.levi, h1, h2, h3, laplacian_eq_fderiv_fderiv]
  simp [Φ, e0]

theorem greenOrigin_main : GreenOriginStatement := by
  intro u hu hc
  obtain ⟨R, hR0, hR⟩ := exists_R_of_compact hc
  have h := green_at hu 0 (R := R + 1) (by linarith) (fun z hz =>
    image_eq_zero_of_notMem_tsupport fun hm => by
      have := hR z hm; rw [sub_zero] at hz; linarith)
  simpa using h

theorem greenDdcOrigin_main : GreenDdcOriginStatement := by
  intro u hu hc
  obtain ⟨h1, h2⟩ := greenOrigin_main u hu hc
  have e : (fun z : ℂ => Real.log ‖z‖ * ddcDens u z) =
      fun z => (1 / (2 * Real.pi)) * (Real.log ‖z‖ * Δ u z) := by
    funext z; simp only [ddcDens]; ring
  rw [e]
  refine ⟨h1.const_mul _, ?_⟩
  rw [integral_const_mul, h2]
  field_simp

theorem greenPoint_main : GreenPointStatement := by
  intro u a hu hc
  obtain ⟨R, hR0, hR⟩ := exists_R_of_compact hc
  exact green_at hu a (R := ‖a‖ + R + 1) (by positivity) (fun z hz =>
    image_eq_zero_of_notMem_tsupport fun hm => by
      have := hR z hm
      have := norm_sub_le z a
      linarith)

theorem greenParamFiber_main : GreenParamFiberStatement := by
  intro E _ _ _ u hu hc p
  obtain ⟨R, hR0, hR⟩ := exists_R_of_compact hc
  have hv : ContDiff ℝ 2 (fun w : ℂ => u (w, p)) := hu.comp (contDiff_id.prodMk contDiff_const)
  have h := green_at hv 0 (R := R + 1) (by linarith) (fun z hz =>
    image_eq_zero_of_notMem_tsupport fun hm => by
      have := hR _ hm
      have := norm_fst_le (z, p)
      simp only [sub_zero] at hz
      linarith)
  simpa using h

theorem lap_fiber {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℂ × E → ℝ}
    (hu : ContDiff ℝ 2 u) (z : ℂ) (p : E) :
    Δ (fun w : ℂ => u (w, p)) z = fderiv ℝ (fderiv ℝ u) (z, p) (1, 0) (1, 0)
      + fderiv ℝ (fderiv ℝ u) (z, p) (Complex.I, 0) (Complex.I, 0) := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  set L : ℂ →L[ℝ] ℂ × E := (ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] E) with hL
  set Ψ : ((ℂ × E) →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ ℂ (ℂ × E) ℝ).flip L with hΨ
  have hpath : ∀ w : ℂ, HasFDerivAt (fun w : ℂ => (w, p)) L w := fun w =>
    (hasFDerivAt_id w).prodMk (hasFDerivAt_const p w)
  have h1 : fderiv ℝ (fun w : ℂ => u (w, p)) = fun w => Ψ (fderiv ℝ u (w, p)) := by
    funext w
    exact ((hd _).hasFDerivAt.comp w (hpath w)).fderiv
  have h2 : HasFDerivAt (fun w : ℂ => Ψ (fderiv ℝ u (w, p)))
      (Ψ.comp ((fderiv ℝ (fderiv ℝ u) (z, p)).comp L)) z :=
    Ψ.hasFDerivAt.comp z ((hd2 _).hasFDerivAt.comp z (hpath z))
  rw [laplacian_eq_fderiv_fderiv, h1, h2.fderiv]
  simp [Ψ, L]

theorem greenParam_main : GreenParamStatement := by
  intro E _ _ _ _ _ μ _ u hu hc
  obtain ⟨R, hR0, hR⟩ := exists_R_of_compact hc
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  set G : ℂ × E → ℝ := fun q => fderiv ℝ (fderiv ℝ u) q (1, 0) (1, 0)
      + fderiv ℝ (fderiv ℝ u) q (Complex.I, 0) (Complex.I, 0) with hG
  have hGc : Continuous G := by fun_prop
  have hF : (fun q : ℂ × E => Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1) =
      fun q => Real.log ‖q.1‖ * G q := by
    funext q; rw [lap_fiber hu]
  have hG0 : ∀ q, q ∉ tsupport u → G q = 0 := fun q hq => by
    have : fderiv ℝ (fderiv ℝ u) q = 0 := by
      by_contra h
      exact hq (tsupport_fderiv_subset ℝ (tsupport_fderiv_subset ℝ
        (subset_tsupport (fderiv ℝ (fderiv ℝ u)) h)))
    simp [G, this]
  obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn hGc.continuousOn
  have hint : Integrable (fun q : ℂ × E => Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1)
      ((volume : Measure ℂ).prod μ) := by
    rw [hF]
    have hg1 : Integrable (fun z : ℂ => max C 0 * (Iic R).indicator (fun t => ‖Real.log t‖) ‖z‖) :=
      (integrable_log_norm_ball hR0).const_mul _
    have hg2 : Integrable (fun p : E => (Metric.closedBall (0 : E) R).indicator (fun _ => (1 : ℝ)) p) μ :=
      (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
        (integrableOn_const (isCompact_closedBall 0 R).measure_lt_top.ne)
    refine (hg1.mul_prod hg2).mono'
      ((Real.measurable_log.comp (measurable_norm.comp measurable_fst)).aestronglyMeasurable.mul
        hGc.aestronglyMeasurable) (Eventually.of_forall fun q => ?_)
    by_cases hq : q ∈ tsupport u
    · have hn := hR q hq
      have h1 : ‖q.1‖ ∈ Iic R := by simp only [mem_Iic]; linarith [norm_fst_le q]
      have h2 : q.2 ∈ Metric.closedBall (0 : E) R := by
        rw [Metric.mem_closedBall, dist_zero_right]; linarith [norm_snd_le q]
      simp only [indicator_of_mem h1, indicator_of_mem h2, mul_one, norm_mul]
      rw [mul_comm (max C 0)]
      exact mul_le_mul_of_nonneg_left ((hC q hq).trans (le_max_left _ _)) (norm_nonneg _)
    · rw [hG0 q hq, mul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (le_max_right _ _)
        (indicator_nonneg (fun _ _ => norm_nonneg _) _))
        (indicator_nonneg (fun _ _ => zero_le_one) _)
  refine ⟨hint, ?_⟩
  rw [integral_prod_symm _ hint]
  simp only
  rw [integral_congr_ae (Eventually.of_forall fun p => (greenParamFiber_main E u hu hc p).2)]
  exact integral_const_mul _ _

theorem greenMaDens_main : GreenMaDensStatement := by
  intro u hu hc
  set v : ℂ → ℝ := fun w => u (fun _ => w) with hv
  have hvc : ContDiff ℝ 2 v := hu.comp (contDiff_pi.2 fun _ => contDiff_id)
  obtain ⟨R, hR0, hR⟩ := exists_R_of_compact hc
  have hvR : ∀ w, R + 1 ≤ ‖w - 0‖ → v w = 0 := fun w hw => by
    show u (fun _ => w) = 0
    exact image_eq_zero_of_notMem_tsupport fun hm => by
      have := hR _ hm
      have := norm_le_pi_norm (fun _ : Fin 1 => w) 0
      simp only [sub_zero] at hw
      linarith
  obtain ⟨h1, h2⟩ := green_at hvc 0 (by linarith) hvR
  simp only [sub_zero] at h1 h2
  have hd : ∀ z : Fin 1 → ℂ, ReciprocityTheory.AnForm.maDens ![u] z =
      (1 / (2 * Real.pi)) * Δ v (z 0) := by
    intro z
    have hu1 : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
    have hz : z = fun _ => z 0 := funext fun i => by fin_cases i; rfl
    have hl : (ReciprocityTheory.AnForm.hessC u z 0 0).re = ReciprocityTheory.AnForm.levi u z (Pi.single 0 1) := by
      simp [ReciprocityTheory.AnForm.hessC, ReciprocityTheory.AnForm.levi]
    have huv : u = fun w : Fin 1 → ℂ => v (w 0) :=
      funext fun w => congrArg u (funext fun i => by fin_cases i; rfl)
    have hm : ReciprocityTheory.AnForm.maDens ![u] z = (2 / Real.pi) * (ReciprocityTheory.AnForm.hessC u z 0 0).re := by
      simp [ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc, hu1]
    rw [hm, hl, huv, hz, leviOne v (z 0)]
    ring
  have e : (fun z : Fin 1 → ℂ => Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z) =
      (fun w : ℂ => (1 / (2 * Real.pi)) * (Real.log ‖w‖ * Δ v w)) ∘
        (MeasurableEquiv.funUnique (Fin 1) ℂ) := by
    funext z; simp only [Function.comp, hd]; simp; ring
  have mp := volume_preserving_funUnique (Fin 1) ℂ
  have hi := mp.integral_comp (MeasurableEquiv.measurableEmbedding _)
    (fun w : ℂ => (1 / (2 * Real.pi)) * (Real.log ‖w‖ * Δ v w))
  have hv0 : v 0 = u 0 := rfl
  rw [e]
  refine ⟨(mp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 (h1.const_mul _),
    hi.trans ?_⟩
  rw [integral_const_mul, h2, hv0]
  field_simp

theorem leviOneEqLaplacian_thm : LeviOneEqLaplacianStatement := leviOne

theorem greenOrigin_thm : GreenOriginStatement := greenOrigin_main

theorem greenDdcOrigin_thm : GreenDdcOriginStatement := greenDdcOrigin_main

theorem greenPoint_thm : GreenPointStatement := greenPoint_main

theorem greenParamFiber_thm : GreenParamFiberStatement := greenParamFiber_main

theorem greenParam_thm : GreenParamStatement := greenParam_main

theorem greenMaDens_thm : GreenMaDensStatement := greenMaDens_main

end

end ReciprocityTheory.AnForm.A
end

-- bundled from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory Matrix

noncomputable section

variable {D E : ℕ}

def jacC (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ) : Matrix (Fin E) (Fin D) ℂ :=
  Matrix.of fun a k => fderiv ℂ τ z (Pi.single k 1) a

theorem jacC_id (z : Fin D → ℂ) : jacC (id : (Fin D → ℂ) → (Fin D → ℂ)) z = 1 := by
  ext a k
  simp only [jacC, Matrix.of_apply, fderiv_id, ContinuousLinearMap.coe_id', id_eq,
    Matrix.one_apply, Pi.single_apply]

theorem jacC_eq_toMatrix' (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ) :
    jacC τ z = LinearMap.toMatrix' (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin E → ℂ)) := by
  ext a k
  rw [LinearMap.toMatrix'_apply]
  rfl

theorem jacC_mulVec (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z w : Fin D → ℂ) :
    jacC τ z *ᵥ w = fderiv ℂ τ z w := by
  rw [jacC_eq_toMatrix', LinearMap.toMatrix'_mulVec]
  rfl

theorem det_jacC (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ) :
    (jacC τ z).det = LinearMap.det (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) := by
  rw [jacC_eq_toMatrix', LinearMap.det_toMatrix']

theorem hessC_isHermitian (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) :
    (hessC φ z).IsHermitian := by
  exact TraceConjugationCover.complexHessian_isHermitian_of_contDiffAt φ z hφ

theorem hessC_add (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  exact TraceConjugationCover.complexHessian_add_of_contDiffAt φ ψ z hφ hψ

theorem hessC_comp (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ)
    (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) :
    hessC (φ ∘ τ) z = (jacC τ z)ᵀ * hessC φ (τ z) * (jacC τ z).map (starRingEnd ℂ) := by
  exact TraceConjugationCover.complexHessian_comp_holomorphic_matrix φ τ z hτ hφ

theorem maDens_comp (φ : Fin D → (Fin D → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin D → ℂ))
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z)) :
    maDens (fun k => φ k ∘ τ) z = maDens φ (τ z) * Complex.normSq (jacC τ z).det := by
  have h : (fun k => hessC (φ k ∘ τ) z) =
      fun k => (jacC τ z)ᵀ * hessC (φ k) (τ z) * (jacC τ z).map (starRingEnd ℂ) :=
    funext fun k => hessC_comp (φ k) τ z hτ (hφ k)
  simp only [maDens]
  rw [h, mdisc_transpose_mul_mul_conj, Complex.re_ofReal_mul]
  ring

theorem hessC_log_norm (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hg : AnalyticAt ℂ g z)
    (hz : g z ≠ 0) : hessC (fun w => Real.log ‖g w‖) z = 0 := by
  exact hessC_log_norm' g z hg hz

theorem hessC_add_log_norm (φ : (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    hessC (fun w => φ w + Real.log ‖g w‖) z = hessC φ z := by
  exact hessC_add_log_norm' φ g z hφ hg hz

theorem hessC_re_analytic (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => (G w).re) z = 0 := by
  exact hessC_re_analytic' G z hG

theorem hessC_add_re_analytic (φ : (Fin D → ℂ) → ℝ) (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => φ w + (G w).re) z = hessC φ z := by
  exact hessC_add_re_analytic' φ G z hφ hG

theorem det_restrictScalars_real {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] V) :
    LinearMap.det (f.restrictScalars ℝ) = Complex.normSq (LinearMap.det f) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

theorem det_fderiv_real_eq_normSq (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ)
    (hτ : DifferentiableAt ℂ τ z) :
    (fderiv ℝ τ z).det = Complex.normSq (jacC τ z).det := by
  rw [(hτ.hasFDerivAt.restrictScalars ℝ).fderiv, det_jacC]
  exact det_restrictScalars_real (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))

theorem integral_image_eq_integral_normSq_det_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U : Set (Fin D → ℂ)) (hU : IsOpen U)
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (f : (Fin D → ℂ) → F) :
    ∫ w in τ '' U, f w = ∫ z in U, Complex.normSq (jacC τ z).det • f (τ z) := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem lintegral_image_eq_lintegral_normSq_det_mul (τ : (Fin D → ℂ) → (Fin D → ℂ))
    (U : Set (Fin D → ℂ)) (hU : IsOpen U) (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U)
    (f : (Fin D → ℂ) → ENNReal) :
    ∫⁻ w in τ '' U, f w = ∫⁻ z in U, ENNReal.ofReal (Complex.normSq (jacC τ z).det) * f (τ z) := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem integrableOn_image_iff_analytic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U : Set (Fin D → ℂ)) (hU : IsOpen U)
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (f : (Fin D → ℂ) → F) :
    IntegrableOn f (τ '' U) ↔
      IntegrableOn (fun z => Complex.normSq (jacC τ z).det • f (τ z)) U := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem maInt_comp (φ : Fin D → (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℝ)
    (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U U' : Set (Fin D → ℂ)) (hU : IsOpen U) (hU' : IsOpen U')
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (himg : τ '' U = U')
    (hφ : ∀ k, ContDiffOn ℝ 2 (φ k) U') :
    maInt (fun k => φ k ∘ τ) (g ∘ τ) U = maInt φ g U' := by
  unfold maInt
  rw [← himg, integral_image_eq_integral_normSq_det_smul τ U hU hτ hinj]
  first
    | apply setIntegral_congr_fun hU.measurableSet
    | apply setIntegral_congr hU.measurableSet
  intro z hz
  have hz' : τ z ∈ U' := himg ▸ Set.mem_image_of_mem τ hz
  have hc : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z) := fun k => (hφ k).contDiffAt (hU'.mem_nhds hz')
  simp only [Function.comp_apply, smul_eq_mul]
  rw [maDens_comp φ τ z (hτ z hz) hc]
  ring

theorem hessC_sum_normSq (z : Fin D → ℂ) :
    hessC (fun w => ∑ i, Complex.normSq (w i)) z = 1 := by
  exact TraceConjugationCover.complexHessian_sum_normSq_coord z

end

end ReciprocityTheory.AnForm.A
end

