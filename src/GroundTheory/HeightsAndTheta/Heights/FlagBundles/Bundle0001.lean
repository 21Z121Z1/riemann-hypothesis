import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyIntegral

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PBarCurveForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped ComplexConjugate Topology
open GroundTheory.Heights₂.Heights

noncomputable section

namespace BarCurve

lemma normSqSum_one (u : Fin 1 → ℂ) : normSqSum u = ‖u 0‖ ^ 2 := by
  simp [normSqSum]

lemma continuous_normSqSum_one : Continuous (normSqSum : (Fin 1 → ℂ) → ℝ) := by
  unfold normSqSum; fun_prop

lemma hasFDerivAt_pot (u : Fin 1 → ℂ) (hu : normSqSum u < 1) :
    HasFDerivAt (fun v : Fin 1 → ℂ => ((-(1 / 2 * Real.log (1 - normSqSum v)) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (-((1 / 2 : ℝ) • ((1 - normSqSum u)⁻¹ • -dNormSqSum u)))) u := by
  have h := (((hasFDerivAt_normSqSum u).const_sub 1).log (sub_pos.mpr hu).ne').const_mul (1 / 2 : ℝ)
  exact Complex.ofRealCLM.hasFDerivAt.comp u h.neg

lemma wirtingerBar_pot (u : Fin 1 → ℂ) (hu : normSqSum u < 1) :
    wirtingerBar (fun v : Fin 1 → ℂ => ((-(1 / 2 * Real.log (1 - normSqSum v)) : ℝ) : ℂ)) 0 u =
      ((2⁻¹ * (1 - normSqSum u)⁻¹ : ℝ) : ℂ) * u 0 := by
  rw [wirtingerBar, (hasFDerivAt_pot u hu).fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, FunLike.coe_smul,
    Pi.smul_apply, dNormSqSum_single, Complex.ofRealCLM_apply, smul_eq_mul]
  have h1 : (1 * conj (u 0)).re = (u 0).re := by simp
  have h2 : (Complex.I * conj (u 0)).re = (u 0).im := by simp
  rw [h1, h2]
  conv_rhs => rw [← Complex.re_add_im (u 0)]
  push_cast
  ring

lemma inner_eventuallyEq (z : Fin 1 → ℂ) (hz : normSqSum z < 1) :
    (fun w => wirtingerBar
        (fun v : Fin 1 → ℂ => ((-(1 / 2 * Real.log (1 - normSqSum v)) : ℝ) : ℂ)) 0 w)
      =ᶠ[𝓝 z] fun w => (2⁻¹ * (1 - normSqSum w)⁻¹ : ℝ) • w 0 := by
  filter_upwards [(isOpen_lt continuous_normSqSum_one continuous_const).mem_nhds hz] with w hw
  rw [wirtingerBar_pot w hw, Complex.real_smul]

lemma hasFDerivAt_inner (z : Fin 1 → ℂ) (hz : normSqSum z < 1) :
    HasFDerivAt (fun w : Fin 1 → ℂ => (2⁻¹ * (1 - normSqSum w)⁻¹ : ℝ) • w 0)
      ((2⁻¹ * (1 - normSqSum z)⁻¹) • (ContinuousLinearMap.proj 0 : (Fin 1 → ℂ) →L[ℝ] ℂ) +
        ((2⁻¹ : ℝ) • ((-((1 - normSqSum z) ^ 2)⁻¹) • -dNormSqSum z)).smulRight (z 0)) z := by
  have hinv : HasFDerivAt (fun w : Fin 1 → ℂ => (1 - normSqSum w)⁻¹)
      ((-((1 - normSqSum z) ^ 2)⁻¹) • -dNormSqSum z) z :=
    (hasDerivAt_inv (sub_pos.mpr hz).ne').comp_hasFDerivAt z
      ((hasFDerivAt_normSqSum z).const_sub 1)
  exact (hinv.const_mul (2⁻¹ : ℝ)).smul
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0).hasFDerivAt

lemma wirtinger_wirtingerBar_pot (z : Fin 1 → ℂ) (hz : normSqSum z < 1) :
    wirtinger (fun w => wirtingerBar
        (fun v : Fin 1 → ℂ => ((-(1 / 2 * Real.log (1 - normSqSum v)) : ℝ) : ℂ)) 0 w) 0 z =
      ((2⁻¹ * ((1 - normSqSum z) ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [wirtinger, (inner_eventuallyEq z hz).fderiv_eq, (hasFDerivAt_inner z hz).fderiv]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.smulRight_apply,
    neg_apply, dNormSqSum_single, Pi.single_eq_same, smul_eq_mul,
    Complex.real_smul]
  have h1 : (1 * conj (z 0)).re = (z 0).re := by simp
  have h2 : (Complex.I * conj (z 0)).re = (z 0).im := by simp
  rw [h1, h2]
  have hS : normSqSum z = (z 0).re ^ 2 + (z 0).im ^ 2 := by
    rw [normSqSum_one, Complex.sq_norm, Complex.normSq_apply]; ring
  have ht : (1 - normSqSum z) ≠ 0 := (sub_pos.mpr hz).ne'
  have hc : ((1 - normSqSum z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  conv_lhs => rw [← Complex.re_add_im (z 0)]
  have hSc : ((normSqSum z : ℝ) : ℂ) = ((z 0).re : ℂ) ^ 2 + ((z 0).im : ℂ) ^ 2 := by
    rw [hS]; push_cast; ring
  push_cast at hc ⊢
  field_simp
  rw [hSc]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  push_cast
  linear_combination (((z 0).re : ℂ) ^ 2 - ((z 0).im : ℂ) ^ 2 - 1) * Complex.I_sq

end BarCurve

theorem BarCurveForm.proof : BarCurveForm.Statement := by
  intro z hz
  have hz' : normSqSum (fun _ : Fin 1 => z) < 1 := by
    rw [BarCurve.normSqSum_one]
    have := norm_nonneg z
    nlinarith
  have hfun : (fun u : Fin 1 → ℂ => ((-(1 / 2 * Real.log (1 - ‖u 0‖ ^ 2)) : ℝ) : ℂ)) =
      fun v => ((-(1 / 2 * Real.log (1 - normSqSum v)) : ℝ) : ℂ) := by
    funext v; rw [BarCurve.normSqSum_one]
  have hkey : ddcDensity (fun w => -((1 / 2) * Real.log (1 - ‖w‖ ^ 2))) z =
      Real.pi⁻¹ / (1 - ‖z‖ ^ 2) ^ 2 := by
    simp only [ddcDensity]
    rw [hfun, BarCurve.wirtinger_wirtingerBar_pot _ hz', Complex.ofReal_re,
      BarCurve.normSqSum_one]
    have hpi := Real.pi_ne_zero
    have ht : (1 - ‖z‖ ^ 2) ≠ 0 := by
      have := norm_nonneg z
      nlinarith
    field_simp
  refine ⟨hkey, ?_⟩
  rw [hkey]
  have ht : 0 < 1 - ‖z‖ ^ 2 := by
    have := norm_nonneg z
    nlinarith
  positivity

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PBlochOverlap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped InnerProductSpace ComplexConjugate Matrix

lemma blochVector_apply (e : EuclideanSpace ℂ (Fin 2)) :
    blochVector e 0 = 2 * ((e 0).re * (e 1).re + (e 0).im * (e 1).im) ∧
    blochVector e 1 = 2 * ((e 0).re * (e 1).im - (e 0).im * (e 1).re) ∧
    blochVector e 2 = (e 0).re ^ 2 + (e 0).im ^ 2 - (e 1).re ^ 2 - (e 1).im ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [blochVector, pauli, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

lemma norm_sq_complex_two_re_im (e : EuclideanSpace ℂ (Fin 2)) :
    ‖e‖ ^ 2 = (e 0).re ^ 2 + (e 0).im ^ 2 + (e 1).re ^ 2 + (e 1).im ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  ring

theorem BlochOverlap.proof : BlochOverlap.Statement := by
  refine ⟨fun e he => ?_, fun e₁ e₂ h₁ h₂ => ?_⟩
  · have hs := norm_sq_complex_two_re_im e
    rw [he] at hs
    obtain ⟨h0, h1, h2⟩ := blochVector_apply e
    have hn : ‖blochVector e‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, sq_abs, sq_abs, sq_abs, h0, h1, h2]
      linear_combination (-(1 : ℝ) - ((e 0).re ^ 2 + (e 0).im ^ 2 + (e 1).re ^ 2 + (e 1).im ^ 2)) * hs
    have h0' : 0 ≤ ‖blochVector e‖ := norm_nonneg _
    nlinarith [hn]
  · have hs₁ := norm_sq_complex_two_re_im e₁
    have hs₂ := norm_sq_complex_two_re_im e₂
    rw [h₁] at hs₁
    rw [h₂] at hs₂
    obtain ⟨a0, a1, a2⟩ := blochVector_apply e₁
    obtain ⟨b0, b1, b2⟩ := blochVector_apply e₂
    rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      Complex.sq_norm, Complex.normSq_apply]
    simp only [RCLike.inner_apply, conj_trivial, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, a0, a1, a2, b0, b1, b2]
    linear_combination (-(1 : ℝ) / 2) * (((e₂ 0).re ^ 2 + (e₂ 0).im ^ 2 + (e₂ 1).re ^ 2 + (e₂ 1).im ^ 2) * hs₁ + hs₂)

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PCompactPairCurveForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped ComplexConjugate

lemma fderiv_comp_coord_zero (h : ℂ → ℂ) (z : Fin 1 → ℂ) (hh : DifferentiableAt ℝ h (z 0))
    (v : Fin 1 → ℂ) :
    fderiv ℝ (fun w : Fin 1 → ℂ => h (w 0)) z v = fderiv ℝ h (z 0) (v 0) := by
  have := hh.hasFDerivAt.comp z (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 1 => ℂ) 0 z)
  rw [show (fun w : Fin 1 → ℂ => h (w 0)) = h ∘ fun f => f 0 from rfl, this.fderiv]
  rfl

lemma ddcDensity_eq_laplacian (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (z : ℂ) :
    ddcDensity f z = (2 * Real.pi)⁻¹ * InnerProductSpace.laplacianWithin f Set.univ z := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdc : ∀ c : ℂ, Differentiable ℝ (fun x => fderiv ℝ f x c) := fun c x =>
    (hd2 x).clm_apply (differentiableAt_const c)
  have hdd : ∀ c v : ℂ, fderiv ℝ (fun x => fderiv ℝ f x c) z v = fderiv ℝ (fderiv ℝ f) z v c := by
    intro c v
    rw [fderiv_clm_apply (hd2 z) (differentiableAt_const c)]
    simp

  have hof : ∀ x : ℂ, HasFDerivAt (fun y : ℂ => ((f y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ f x)) x := fun x =>
    Complex.ofRealCLM.hasFDerivAt.comp x (hd x).hasFDerivAt
  set g : ℂ → ℂ := fun x => (1 / 2 : ℂ) *
    (((fderiv ℝ f x 1 : ℝ) : ℂ) + Complex.I * ((fderiv ℝ f x Complex.I : ℝ) : ℂ)) with hg
  have hbar : (fun w : Fin 1 → ℂ => wirtingerBar (fun u : Fin 1 → ℂ => ((f (u 0) : ℝ) : ℂ)) 0 w) =
      fun w => g (w 0) := by
    funext w
    rw [wirtingerBar, fderiv_comp_coord_zero _ w (hof (w 0)).differentiableAt,
      fderiv_comp_coord_zero _ w (hof (w 0)).differentiableAt, (hof (w 0)).fderiv]
    simp [hg]

  have hga : ∀ c : ℂ, HasFDerivAt (fun x => ((fderiv ℝ f x c : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun x => fderiv ℝ f x c) z)) z := fun c =>
    Complex.ofRealCLM.hasFDerivAt.comp z (hdc c z).hasFDerivAt
  have hgd : HasFDerivAt g ((1 / 2 : ℂ) • (Complex.ofRealCLM.comp
      (fderiv ℝ (fun x => fderiv ℝ f x 1) z) + Complex.I • Complex.ofRealCLM.comp
      (fderiv ℝ (fun x => fderiv ℝ f x Complex.I) z))) z :=
    ((hga 1).add ((hga Complex.I).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  unfold ddcDensity
  rw [hbar, wirtinger, fderiv_comp_coord_zero g _ hgd.differentiableAt,
    fderiv_comp_coord_zero g _ hgd.differentiableAt, hgd.fderiv]
  simp only [InnerProductSpace.laplacianWithin_univ,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply]
  simp [hdd]
  field_simp

lemma ddcDensity_fubiniStudy (z : ℂ) :
    ddcDensity (fun w => (1 / 2) * Real.log (1 + ‖w‖ ^ 2)) z =
      Real.pi⁻¹ / (1 + ‖z‖ ^ 2) ^ 2 := by
  have hS : ∀ u : Fin 1 → ℂ, normSqSum u = ‖u 0‖ ^ 2 := fun u => by simp [normSqSum]
  set G : (Fin 1 → ℂ) → ℂ := fun u => ((Real.log (1 + normSqSum u) : ℝ) : ℂ) with hG
  have hF : (fun u : Fin 1 → ℂ => (((1 / 2) * Real.log (1 + ‖u 0‖ ^ 2) : ℝ) : ℂ)) =
      fun u => (1 / 2 : ℂ) * G u := by
    funext u; simp only [hG, hS]; push_cast; ring
  set H : (Fin 1 → ℂ) → ℂ := fun u => (1 + normSqSum u)⁻¹ • u 0 with hH
  have hbar : (fun w => wirtingerBar (fun u : Fin 1 → ℂ =>
      (((1 / 2) * Real.log (1 + ‖u 0‖ ^ 2) : ℝ) : ℂ)) 0 w) = fun w => (1 / 2 : ℂ) * H w := by
    funext w
    have h0 := wirtingerBar_logPot (0 : Fin 1) w
    rw [wirtingerBar] at h0 ⊢
    rw [hF, fderiv_const_mul (hasFDerivAt_logPot w).differentiableAt]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    simp only [hH, Complex.real_smul]
    rw [← h0]
    ring
  have hch := CP.chernCoeff_apply (N := 1) 0 (fun _ => z) 0 0
  have hpot : (fun w => wirtingerBar (fun u => ((CP.kahlerPotential 0 u : ℝ) : ℂ)) 0 w) = H := by
    funext w
    simp only [CP.kahlerPotential_eq, hH, Complex.real_smul]
    exact wirtingerBar_logPot 0 w
  rw [CP.chernCoeff, Matrix.of_apply, hpot] at hch
  have hHd : DifferentiableAt ℝ H (fun _ => z) := (hasFDerivAt_coordDiv 0 _).differentiableAt
  have hW : wirtinger (fun w => (1 / 2 : ℂ) * H w) 0 (fun _ => z) =
      (1 / 2 : ℂ) * wirtinger H 0 (fun _ => z) := by
    rw [wirtinger, wirtinger, fderiv_const_mul hHd]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  unfold ddcDensity
  rw [hbar, hW]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hSz : normSqSum (fun _ : Fin 1 => z) = ‖z‖ ^ 2 := hS _
  have hpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hWv : wirtinger H 0 (fun _ => z) = (((1 + ‖z‖ ^ 2) ^ 2)⁻¹ : ℝ) := by
    have hc : ((1 / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
      have : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    rw [hSz, Matrix.one_apply_eq, Complex.conj_mul'] at hch
    have hne : (1 + (‖z‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hpos.ne'
    apply mul_left_cancel₀ hc
    rw [hch]
    push_cast
    field_simp
    ring
  rw [hWv]
  have : ((1 / 2 : ℂ) * ((((1 + ‖z‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ)).re =
      (1 / 2) * ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
    rw [show (1 / 2 : ℂ) * ((((1 + ‖z‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) =
      (((1 / 2) * ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [this]
  field_simp

lemma integral_fubiniStudy_density :
    ∫ z : ℂ, Real.pi⁻¹ / (1 + ‖z‖ ^ 2) ^ 2 = 1 := by
  have h := (integral_complex_norm_pow_div 1 one_pos 0 0).2
  simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, zero_add, one_pow, div_one,
    mul_one, Nat.reduceAdd, one_div] at h
  have e : (fun z : ℂ => Real.pi⁻¹ / (1 + ‖z‖ ^ 2) ^ 2) =
      fun z => Real.pi⁻¹ * ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
    funext z; rw [div_eq_mul_inv]
  rw [e, integral_const_mul, h, Nat.factorial_one, Nat.cast_one, inv_one, mul_one]
  exact inv_mul_cancel₀ Real.pi_ne_zero

theorem CompactPairCurveForm.proof : CompactPairCurveForm.Statement :=
  ⟨ddcDensity_eq_laplacian, ddcDensity_fubiniStudy, integral_fubiniStudy_density⟩

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PDiagonalLocalDVR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial IsLocalRing

theorem localization_span_singleton_dvr {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (a : A) (ha : a ≠ 0) [hP : (Ideal.span {a}).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {a})) ∧
      Irreducible (algebraMap A (Localization.AtPrime (Ideal.span {a})) a) := by
  set L := Localization.AtPrime (Ideal.span {a})
  have : IsDomain L :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {a}))
  have : IsNoetherianRing L :=
    IsLocalization.isNoetherianRing (Ideal.span {a}).primeCompl L inferInstance
  have hmax : maximalIdeal L = Ideal.span {algebraMap A L a} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {a}) L, Ideal.map_span,
      Set.image_singleton]
  have hinj : Function.Injective (algebraMap A L) :=
    IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {a}))
  have hne : algebraMap A L a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have hnf : ¬ IsField L := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact hne
  have hdvr : IsDiscreteValuationRing L :=
    ((IsDiscreteValuationRing.TFAE L hnf).out 4 0).mp (⟨⟨_, hmax⟩⟩ : (maximalIdeal L).IsPrincipal)
  exact ⟨hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax⟩

theorem DiagonalLocalDVR.proof (h0 : DiagonalQuotient.Statement) : DiagonalLocalDVR.Statement := by
  intro R _ _ _
  have hd : (diagonalIdeal R).IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    exact (h0 R).2.2.1 inferInstance
  have hm : (mixedDiagonalIdeal R).IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    exact (h0 R).2.2.2.2.2 inferInstance
  have h1 : (X 0 - X 1 : MvPolynomial (Fin 2) R) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![(1 : R), 0]) h
    simp at this
  have h2 : (1 - X 0 * X 1 : MvPolynomial (Fin 2) R) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![(0 : R), 0]) h
    simp at this
  exact ⟨⟨hd, @localization_span_singleton_dvr _ _ _ _ _ h1 hd⟩,
    ⟨hm, @localization_span_singleton_dvr _ _ _ _ _ h2 hm⟩⟩

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PDiagonalQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial LaurentPolynomial

namespace DiagonalQuotient

variable (R : Type) [CommRing R]

noncomputable def diagEval : MvPolynomial (Fin 2) R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval fun _ => Polynomial.X

noncomputable def diagToPoly : (MvPolynomial (Fin 2) R ⧸ diagonalIdeal R) →ₐ[R] Polynomial R :=
  Ideal.Quotient.liftₐ (diagonalIdeal R) (diagEval R) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [diagEval])

noncomputable def polyToDiag : Polynomial R →ₐ[R] (MvPolynomial (Fin 2) R ⧸ diagonalIdeal R) :=
  Polynomial.aeval (Ideal.Quotient.mk (diagonalIdeal R) (X 0))

lemma mk_X_one_eq : Ideal.Quotient.mk (diagonalIdeal R) (X 1) =
    Ideal.Quotient.mk (diagonalIdeal R) (X 0) := by
  rw [Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton'.2 ⟨-1, by ring⟩

@[simp] lemma diagToPoly_mk (p : MvPolynomial (Fin 2) R) :
    diagToPoly R (Ideal.Quotient.mk _ p) = diagEval R p := rfl

@[simp] lemma diagEval_X (i : Fin 2) : diagEval R (X i) = Polynomial.X := by
  simp [diagEval]

noncomputable def diagEquiv : (MvPolynomial (Fin 2) R ⧸ diagonalIdeal R) ≃ₐ[R] Polynomial R :=
  AlgEquiv.ofAlgHom (diagToPoly R) (polyToDiag R)
    (by
      apply Polynomial.algHom_ext
      simp [polyToDiag])
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · simp [polyToDiag]
      · simp [polyToDiag, mk_X_one_eq])

noncomputable def mixedEval : MvPolynomial (Fin 2) R →ₐ[R] LaurentPolynomial R :=
  MvPolynomial.aeval ![T 1, T (-1)]

noncomputable def mixedToLaurent :
    (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) →ₐ[R] LaurentPolynomial R :=
  Ideal.Quotient.liftₐ (mixedDiagonalIdeal R) (mixedEval R) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have : (T 1 : LaurentPolynomial R) * T (-1) = 1 := by rw [← T_add]; simp
    simp [mixedEval, this])

noncomputable def mixedUnit : (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R)ˣ where
  val := Ideal.Quotient.mk _ (X 0)
  inv := Ideal.Quotient.mk _ (X 1)
  val_inv := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (mixedDiagonalIdeal R)), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.2 ⟨-1, by ring⟩
  inv_val := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (mixedDiagonalIdeal R)), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.2 ⟨-1, by ring⟩

@[simp] lemma mixedToLaurent_mk (p : MvPolynomial (Fin 2) R) :
    mixedToLaurent R (Ideal.Quotient.mk _ p) = mixedEval R p := rfl

@[simp] lemma mixedEval_X_zero : mixedEval R (X 0) = T 1 := by simp [mixedEval]

@[simp] lemma mixedEval_X_one : mixedEval R (X 1) = T (-1) := by simp [mixedEval]

@[simp] lemma mixedUnit_val : ((mixedUnit R : (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R)ˣ) :
    MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) = Ideal.Quotient.mk _ (X 0) := rfl

@[simp] lemma mixedUnit_inv_val : (((mixedUnit R)⁻¹ : (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R)ˣ) :
    MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) = Ideal.Quotient.mk _ (X 1) := rfl

noncomputable def laurentToMixed :
    LaurentPolynomial R →ₐ[R] (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) :=
  { LaurentPolynomial.eval₂ (algebraMap R _) (mixedUnit R) with
    commutes' := fun r => by
      show LaurentPolynomial.eval₂ _ _ (algebraMap R (LaurentPolynomial R) r) = _
      rw [← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.eval₂_C] }

@[simp] lemma laurentToMixed_alt (n : ℤ) :
    laurentToMixed R (T n) = ((mixedUnit R ^ n : (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R)ˣ) :
      MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) :=
  LaurentPolynomial.eval₂_T _ _ n

@[simp] lemma laurentToMixed_C (a : R) :
    laurentToMixed R (LaurentPolynomial.C a) = algebraMap R _ a := by
  rw [LaurentPolynomial.C_eq_algebraMap, AlgHom.commutes]

noncomputable def mixedEquiv :
    (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) ≃ₐ[R] LaurentPolynomial R :=
  AlgEquiv.ofAlgHom (mixedToLaurent R) (laurentToMixed R)
    (by
      apply AlgHom.coe_ringHom_injective
      apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
      apply Polynomial.ringHom_ext
      · intro a
        simp [algebraMap_eq_toLaurent]
      · simp [algebraMap_eq_toLaurent])
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · simp
      · simp)

end DiagonalQuotient

open DiagonalQuotient in

theorem DiagonalQuotient.proof : DiagonalQuotient.Statement := by
  intro R _
  refine ⟨⟨diagEquiv R, ?_, ?_⟩, ?_, ?_, ⟨mixedEquiv R, ?_, ?_⟩, ?_, ?_⟩
  · simp [diagEquiv]
  · simp [diagEquiv]
  · exact Module.Flat.of_linearEquiv (diagEquiv R).toLinearEquiv
  · intro _
    exact Function.Injective.isDomain (diagEquiv R) (diagEquiv R).injective
  · simp [mixedEquiv]
  · simp [mixedEquiv]
  · exact Module.Flat.of_linearEquiv (mixedEquiv R).toLinearEquiv
  · intro _
    exact Function.Injective.isDomain (mixedEquiv R) (mixedEquiv R).injective

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibrePushforward
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

theorem FibrePushforward.proof (h0 : SphereMoment.Statement) : FibrePushforward.Statement := by
  intro k hk a
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h2 : 2 * (m + 1) - 2 = 2 * m := by omega
  have h1 : m + 1 - 1 = m := by omega
  rw [h2, h1, (h0 a m).1, real_inner_self_eq_norm_sq, ← pow_mul]
  have hpos : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end GroundTheory.Heights₂.Heights.FlagBundles
end

