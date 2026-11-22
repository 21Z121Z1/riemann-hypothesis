import Mathlib

-- bundled from ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDefs
section
noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

def bGram (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => ∫ x, starRingEnd ℂ (s i x) * s j x * (w x : ℂ) ∂μ

def bNormSq (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (c : Fin r → ℂ) : ℝ :=
  ∫ x, ‖∑ i, c i * s i x‖ ^ 2 * w x ∂μ

def bergmanDensity (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (x : X) : ℝ :=
  w x * (∑ i, ∑ j, (bGram μ s w)⁻¹ i j * s i x * starRingEnd ℂ (s j x)).re

end ReciprocityTheory.GeometryOfNumbersTheory
end
end

-- bundled from ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.DiscSt
section
noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Filter Topology

open Set

theorem pgds_cont_polar_symm : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  have : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
      fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
    funext p; simp [Complex.polarCoord_symm_apply]
  rw [this]; fun_prop

theorem pgds_integral_ball_polar {r : ℝ} (F : ℂ → ℝ) (hF : ContinuousOn F (Metric.closedBall 0 r)) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p))
        (Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi) ∧
    ∫ z in Metric.ball (0 : ℂ) r, F z =
      ∫ s in Ioo 0 r, ∫ θ in Ioo (-Real.pi) Real.pi, s * F (Complex.polarCoord.symm (s, θ)) := by
  have hc := pgds_cont_polar_symm
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p))
      (Icc 0 r ×ˢ Icc (-Real.pi) Real.pi) := by
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    apply ContinuousOn.mul (continuous_fst.continuousOn)
    refine hF.comp hc.continuousOn ?_
    intro p hp
    simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm]
    rw [abs_of_nonneg hp.1.1]; exact hp.1.2
  have hint' := hint.mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  refine ⟨hint', ?_⟩
  have hpre : MeasurableSet ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r) :=
    hc.measurable Metric.isOpen_ball.measurableSet
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, ← Complex.integral_comp_polarCoord_symm,
    polarCoord_target]
  have h1 : (fun p : ℝ × ℝ => p.1 • (Metric.ball (0:ℂ) r).indicator F (Complex.polarCoord.symm p)) =
      ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r).indicator
        (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p)) := by
    funext p
    by_cases hp : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) r
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ _ from hp), smul_eq_mul]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ _ from hp), smul_zero]
  rw [h1, setIntegral_indicator hpre]
  have h2 : Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi ∩
      ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r) =
      Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_preimage, Metric.mem_ball,
      dist_zero_right, Complex.norm_polarCoord_symm]
    constructor
    · rintro ⟨⟨h0, hθ⟩, hr⟩; rw [abs_of_pos h0] at hr; exact ⟨⟨h0, hr⟩, hθ⟩
    · rintro ⟨⟨h0, hr⟩, hθ⟩; refine ⟨⟨h0, hθ⟩, ?_⟩; rw [abs_of_pos h0]; exact hr
  rw [h2, Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod] at hint'
  exact setIntegral_prod _ hint'

def discI (a R : ℝ) : ℝ :=
  ∫ z in Metric.ball (0 : ℂ) R, Real.exp (-(a * ‖z‖ ^ 2))

theorem pgds_discI_eq (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    discI a R = ∫ s in (0:ℝ)..R, 2 * Real.pi * (s * Real.exp (-(a * s ^ 2))) := by
  unfold discI
  rw [(pgds_integral_ball_polar (r := R) (fun z : ℂ => Real.exp (-(a * ‖z‖ ^ 2)))
    (by fun_prop)).2, intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
  simp only [Complex.norm_polarCoord_symm]
  rw [abs_of_pos hs.1, setIntegral_const]
  simp only [measureReal_def, Real.volume_Ioo, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

theorem discI_of_pos {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    discI a R = Real.pi * (1 - Real.exp (-(a * R ^ 2))) / a := by
  rw [pgds_discI_eq a hR]
  have hd : ∀ x ∈ uIcc 0 R, HasDerivAt (fun s => -(Real.pi / a) * Real.exp (-(a * s ^ 2)))
      (2 * Real.pi * (x * Real.exp (-(a * x ^ 2)))) x := by
    intro x _
    have := (((hasDerivAt_pow 2 x).const_mul a).neg.exp).const_mul (-(Real.pi / a))
    refine this.congr_deriv ?_
    rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
    simp only [Pi.neg_apply, Nat.cast_ofNat]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero,
    Real.exp_zero, mul_one]
  ring

theorem discI_zero {R : ℝ} (hR : 0 ≤ R) : discI 0 R = Real.pi * R ^ 2 := by
  rw [pgds_discI_eq 0 hR]
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

theorem discI_pos {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) : 0 < discI a R := by
  rcases ha.lt_or_eq with ha | ha
  · rw [discI_of_pos ha hR.le]
    have : Real.exp (-(a * R ^ 2)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hR])
    have := Real.pi_pos
    apply div_pos _ ha
    nlinarith
  · subst ha; rw [discI_zero hR.le]; have := Real.pi_pos; positivity

theorem discI_scale {a R t : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) (ht : 0 < t) :
    discI (t * a) (R / Real.sqrt t) = discI a R / t := by
  have hs : (R / Real.sqrt t) ^ 2 = R ^ 2 / t := by
    rw [div_pow, Real.sq_sqrt ht.le]
  have hR' : 0 ≤ R / Real.sqrt t := div_nonneg hR (Real.sqrt_nonneg t)
  rcases ha.lt_or_eq with ha | ha
  · rw [discI_of_pos (mul_pos ht ha) hR', discI_of_pos ha hR, hs]
    have : t * a * (R ^ 2 / t) = a * R ^ 2 := by field_simp
    rw [this]
    field_simp
  · subst ha; rw [mul_zero, discI_zero hR', discI_zero hR, hs]; ring

theorem pgds_circle {R s : ℝ} (hs : 0 < s) (hsR : s < R) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) :
    2 * Real.pi * ‖g 0‖ ^ 2 ≤
      ∫ θ in Ioo (-Real.pi) Real.pi, ‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 := by
  have hpi := Real.pi_pos
  set h : ℂ → ℂ := fun z => g z ^ 2 with hh
  have habs : |s| = s := abs_of_pos hs
  have hdiff : DiffContOnCl ℂ h (Metric.ball 0 |s|) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by rw [habs]; exact hs.ne'), habs]
    exact (hg.pow 2).mono (Metric.closedBall_subset_ball hsR)
  have hav := hdiff.circleAverage
  rw [Real.circleAverage_def] at hav
  have hper : Function.Periodic (fun θ => ‖h (circleMap 0 s θ)‖) (2 * Real.pi) := by
    intro θ; simp only; rw [periodic_circleMap 0 s θ]
  have e1 := hper.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at e1
  have hle : ‖h 0‖ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖h (circleMap 0 s θ)‖ := by
    rw [← hav, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    gcongr
    exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
  rw [e1, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo] at hle
  have hcm : ∀ θ : ℝ, circleMap 0 s θ = Complex.polarCoord.symm (s, θ) := by
    intro θ
    simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  simp only [hcm, hh, norm_pow] at hle
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)] at hle
  linarith

theorem disc_mean_le {R r : ℝ} (hr : 0 < r) (hrR : r < R) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) (w : ℝ → ℝ) (hwc : Continuous w)
    (hw : ∀ s, 0 ≤ w s) :
    ‖g 0‖ ^ 2 * ∫ z in Metric.ball (0 : ℂ) r, w ‖z‖ ≤
      ∫ z in Metric.ball (0 : ℂ) r, ‖g z‖ ^ 2 * w ‖z‖ := by
  have hgc : ContinuousOn g (Metric.closedBall 0 r) :=
    hg.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  obtain ⟨hiR, eR⟩ := pgds_integral_ball_polar (r := r) (fun z => ‖g z‖ ^ 2 * w ‖z‖)
    ((hgc.norm.pow 2).mul (hwc.comp continuous_norm).continuousOn)
  obtain ⟨-, eL⟩ := pgds_integral_ball_polar (r := r) (fun z => w ‖z‖)
    (hwc.comp continuous_norm).continuousOn
  rw [eL, eR, ← integral_const_mul]
  have hI : Integrable (fun p : ℝ × ℝ => p.1 * (‖g (Complex.polarCoord.symm p)‖ ^ 2 *
      w ‖Complex.polarCoord.symm p‖))
      ((volume.restrict (Ioo 0 r)).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hiR
  refine integral_mono_of_nonneg ?_ hI.integral_prod_left ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioo
      fun θ _ => mul_nonneg hs.1.le (hw _))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have key := pgds_circle hs.1 (hs.2.trans hrR) g hg
    simp only [Complex.norm_polarCoord_symm, abs_of_pos hs.1]
    rw [setIntegral_const]
    simp only [measureReal_def, Real.volume_Ioo, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    have e : ∀ θ : ℝ, s * (‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 * w s) =
        (s * w s) * ‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 := fun θ => by ring
    simp only [e]
    rw [integral_const_mul]
    have hsw : 0 ≤ s * w s := mul_nonneg hs.1.le (hw s)
    have := mul_le_mul_of_nonneg_left key hsw
    nlinarith

end ReciprocityTheory.GeometryOfNumbersTheory
end
end

-- bundled from ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt
section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix MeasureTheory
open scoped ComplexOrder

theorem trace_adjugate_mul_eq_sum_perm {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) :
    (A.adjugate * B).trace = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i := by
  have hcol : ∀ i, (A.adjugate * B) i i = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) *
      ((∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i) := by
    intro i
    have h1 : (A.adjugate * B) i i = (A.updateCol i (fun k => B k i)).det := by
      rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), smul_eq_mul, mul_comm]
    congr 1
    all_goals first
      | (refine Finset.prod_congr rfl fun j hj => ?_
         simp [Matrix.updateCol_apply, Finset.ne_of_mem_erase hj])
      | simp [Matrix.updateCol_apply]
  simp only [Matrix.trace, Matrix.diag, hcol]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]

theorem hasDerivAt_det {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ) (G' : Matrix (Fin r) (Fin r) ℂ)
    (t : ℝ) (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t) :
    HasDerivAt (fun s => (G s).det) ((G t).adjugate * G').trace t := by
  rw [trace_adjugate_mul_eq_sum_perm]
  have hfun : (fun s => (G s).det) = fun s => ∑ σ : Equiv.Perm (Fin r),
      (Equiv.Perm.sign σ : ℂ) * ∏ j, G s (σ j) j := by
    funext s; exact Matrix.det_apply' _
  rw [hfun]
  have hσ : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin r))),
      HasDerivAt (fun s => (Equiv.Perm.sign σ : ℂ) * ∏ j, G s (σ j) j)
        ((Equiv.Perm.sign σ : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, G t (σ j) j) • G' (σ i) i) t :=
    fun σ _ => by
      first
        | exact (HasDerivAt.fun_finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)).const_mul _
        | (have hp := HasDerivAt.finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)
           simp only [Finset.prod_apply] at hp
           exact hp.const_mul _)
        | (have hp := HasDerivAt.finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)
           convert hp.const_mul (Equiv.Perm.sign σ : ℂ) using 2
           funext s
           simp [Finset.prod_apply])
  first
    | exact HasDerivAt.fun_sum hσ
    | exact HasDerivAt.sum hσ
    | simpa using HasDerivAt.sum hσ

theorem hasDerivAt_log_det {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hpos : (G t).PosDef) :
    HasDerivAt (fun s => Real.log (G s).det.re) ((G t)⁻¹ * G').trace.re t := by
  have hd := hasDerivAt_det G G' t hG
  have hre : HasDerivAt (fun s => (G s).det.re) ((G t).adjugate * G').trace.re t := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
    simpa [Function.comp_def] using this
  have hdpos : 0 < (G t).det := hpos.det_pos
  have hre0 : 0 < (G t).det.re ∧ (G t).det.im = 0 := by
    have := Complex.lt_def.1 hdpos
    simp only [Complex.zero_re, Complex.zero_im] at this
    exact ⟨this.1, this.2.symm⟩
  have hlog := hre.log hre0.1.ne'
  convert hlog using 1
  have hdet : (G t).det = (((G t).det.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hre0.2])
  rw [Matrix.inv_def, Matrix.smul_mul, Matrix.trace_smul, Ring.inverse_eq_inv', smul_eq_mul, hdet,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  simp only [Complex.ofReal_re]
  ring

noncomputable def betaNatInt (i j : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, t ^ i * (1 - t) ^ j

theorem bI_zero (j : ℕ) : ((j : ℝ) + 1) * betaNatInt 0 j = 1 := by
  unfold betaNatInt
  simp only [pow_zero, one_mul]
  have h := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ j) (a := 0) (b := 1) 1
  simp only [sub_zero, sub_self] at h
  rw [h, integral_pow]
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  simp
  field_simp

theorem bI_succ (i j : ℕ) : ((j : ℝ) + 1) * betaNatInt (i + 1) j = ((i : ℝ) + 1) * betaNatInt i (j + 1) := by
  unfold betaNatInt
  have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => x ^ (i + 1)) (((i:ℝ) + 1) * x ^ i) x := by
    intro x _
    simpa using hasDerivAt_pow (i + 1) x
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => -(1 - x) ^ (j + 1)) (((j:ℝ) + 1) * (1 - x) ^ j) x := by
    intro x _
    have h2 := (((hasDerivAt_id x).const_sub 1).pow (j + 1)).neg
    refine h2.congr_deriv ?_
    first
      | (simp only [id, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]; ring)
      | (simp; ring)
      | simp
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  have e1 : ∫ x in (0:ℝ)..1, ((j:ℝ) + 1) * (x ^ (i + 1) * (1 - x) ^ j) =
      ∫ x in (0:ℝ)..1, x ^ (i + 1) * (((j:ℝ) + 1) * (1 - x) ^ j) := by
    congr 1; funext x; ring
  have e2 : ∫ x in (0:ℝ)..1, ((i:ℝ) + 1) * (x ^ i * (1 - x) ^ (j + 1)) =
      -∫ x in (0:ℝ)..1, ((i:ℝ) + 1) * x ^ i * (-(1 - x) ^ (j + 1)) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, e1, e2, hparts]
  simp

theorem bI_closed (i j : ℕ) : ((i : ℝ) + j + 1) * ((i + j).choose i : ℝ) * betaNatInt i j = 1 := by
  induction i generalizing j with
  | zero => simpa using bI_zero j
  | succ i ih =>
    have h1 := bI_succ i j
    have h2 := ih (j + 1)
    have e3 : i + (j + 1) = i + j + 1 := by omega
    rw [e3] at h2
    push_cast at h2
    have h3 : ((i + j + 1).choose (i + 1) : ℝ) * ((i:ℝ) + 1) =
        ((i + j + 1).choose i : ℝ) * ((j:ℝ) + 1) := by
      have := Nat.choose_succ_right_eq (i + j + 1) i
      have e : i + j + 1 - i = j + 1 := by omega
      rw [e] at this
      exact_mod_cast this
    have hj : ((j:ℝ) + 1) ≠ 0 := by positivity
    have e2 : i + 1 + j = i + j + 1 := by omega
    rw [e2]
    push_cast
    apply mul_right_cancel₀ hj
    linear_combination ((i:ℝ) + j + 2) * ((i + j + 1).choose (i + 1) : ℝ) * h1 +
      ((i:ℝ) + j + 2) * betaNatInt i (j + 1) * h3 + ((j:ℝ) + 1) * h2

theorem integral_bernstein (D i : ℕ) (hi : i ≤ D) :
    ∫ t in (0 : ℝ)..1, (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) = 1 / (D + 1 : ℝ) := by
  have h := bI_closed i (D - i)
  have e : i + (D - i) = D := by omega
  rw [e] at h
  have hcast : ((i:ℝ) + ((D - i : ℕ) : ℝ) + 1) = (D:ℝ) + 1 := by
    rw [Nat.cast_sub hi]; ring
  rw [hcast] at h
  unfold betaNatInt at h
  have hD : (D:ℝ) + 1 ≠ 0 := by positivity
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, eq_div_iff hD]
  linear_combination h

end ReciprocityTheory.GeometryOfNumbersTheory
end

-- bundled from ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.MorseGenStA
section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix MeasureTheory Complex

theorem morseGen_ident (fz qz : ℂ) (φz φ0 νz ν0 : ℝ) (n : ℕ) :
    ‖fz * cexp (-(n : ℂ) * qz / 2)‖ ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re))) * (νz / ν0) =
      ‖fz‖ ^ 2 * Real.exp (-((n : ℝ) * φz)) * νz * (Real.exp ((n : ℝ) * φ0) / ν0) := by
  have hre : (-(n : ℂ) * qz / 2).re = -((n : ℝ) * qz.re) / 2 := by simp
  have e1 : Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re))) =
      Real.exp (-((n : ℝ) * φz)) * Real.exp ((n : ℝ) * φ0) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [norm_mul, Complex.norm_exp, hre, mul_pow]
  calc ‖fz‖ ^ 2 * Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re)))
        * (νz / ν0)
      = ‖fz‖ ^ 2 * (Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 *
          Real.exp (-((n : ℝ) * (φz - φ0 - qz.re)))) * (νz / ν0) := by ring
    _ = _ := by rw [e1]; ring

theorem morseGen_sq_le_sum {D : ℕ} (z : Fin D → ℂ) : ‖z‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 := by
  have hs : 0 ≤ ∑ j, ‖z j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have h : ‖z‖ ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  calc ‖z‖ ^ 2 ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hs

theorem morseGen_levi_le {D : ℕ} (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (B z z + B (I • z) (I • z)) / 4 ≤ ‖B‖ / 2 * ‖z‖ ^ 2 := by
  have h1 : B z z ≤ ‖B‖ * ‖z‖ * ‖z‖ := (le_abs_self _).trans (B.le_opNorm₂ z z)
  have h2 : B (I • z) (I • z) ≤ ‖B‖ * ‖I • z‖ * ‖I • z‖ :=
    (le_abs_self _).trans (B.le_opNorm₂ _ _)
  have hI : ‖I • z‖ = ‖z‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  rw [hI] at h2
  nlinarith

end ReciprocityTheory.GeometryOfNumbersTheory
end

