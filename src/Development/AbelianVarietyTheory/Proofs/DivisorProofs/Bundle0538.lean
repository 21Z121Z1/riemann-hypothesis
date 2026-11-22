import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0521
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryWithDeterminant
section
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.UnitDet

theorem exists_imag (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ ξ : E, ξ ≠ 0 ∧ IsCMField.complexConj E ξ = -ξ := by
  obtain ⟨t, ht⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)
  refine ⟨t - IsCMField.complexConj E t, sub_ne_zero.2 (fun h => ht h.symm), ?_⟩
  simp [IsCMField.complexConj_apply_apply]

theorem herm_single {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
  simp [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.single_apply, apply_ite, ite_mul]

theorem exists_aniso {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {G : Matrix (Fin r) (Fin r) E} (hdet : G.det ≠ 0) (hr : 0 < r) :
    ∃ e : Fin r → E, ReciprocityTheory.ChartRestriction.G.FD.herm G e e ≠ 0 := by
  by_contra hne
  push_neg at hne
  obtain ⟨ξ, hξ0, hξ⟩ := exists_imag E
  have h0 : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm G x y = 0 := by
    intro x y
    have h1 := hne (x + (1:E) • y)
    have h2 := hne (x + ξ • y)
    rw [GlobalTheory.FlagData.herm_add_smul_left, GlobalTheory.FlagData.herm_add_smul_right,
      GlobalTheory.FlagData.herm_add_smul_right, hne x, hne y] at h1 h2
    simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_one, hξ] at h1 h2
    have h3 : (-2 * ξ) * ReciprocityTheory.ChartRestriction.G.FD.herm G x y = 0 := by linear_combination h2 - ξ * h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (by simpa using hξ0)
    · exact h
  apply hdet
  have hG0 : G = 0 := by
    ext a b
    rw [← herm_single G a b, h0]
    rfl
  rw [hG0]
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  simp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (u : E), 0 < r → (∀ a b, IsCMField.complexConj E (G a b) = G b a) → G.det ≠ 0 → u * IsCMField.complexConj E u = 1 → ∃ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧ (γ : Matrix (Fin r) (Fin r) E).det = u := by
  intro E _ _ _ r G u hr hG hdet hu
  obtain ⟨e, he⟩ := exists_aniso hdet hr
  have hG' : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a := hG
  have hch : IsCMField.complexConj E (ReciprocityTheory.ChartRestriction.G.FD.herm G e e) = ReciprocityTheory.ChartRestriction.G.FD.herm G e e :=
    GlobalTheory.FlagData.cc_herm hG' e e
  set h := ReciprocityTheory.ChartRestriction.G.FD.herm G e e with hh
  set α : E := (u - 1) / h with hα
  have hdetT : (ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α).det = u := by
    set v : Fin r → E := fun b => α * ∑ k, G b k * ReciprocityTheory.ChartRestriction.G.FD.cc (e k) with hv
    have hT : ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α = 1 + replicateCol (Fin 1) e *
        replicateRow (Fin 1) v := by
      ext a b
      simp [ReciprocityTheory.ChartRestriction.G.FD.transvMat, replicateCol, replicateRow, Matrix.mul_apply, Matrix.one_apply]
      ring
    have hd := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) e v
    rw [hT]
    refine hd.trans ?_
    have : v ⬝ᵥ e = α * h := by
      rw [hh, hv]
      simp only [dotProduct, ReciprocityTheory.ChartRestriction.G.FD.herm, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this, hα]
    field_simp
    ring
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have key : IsCMField.complexConj E α + α + α * IsCMField.complexConj E α * h = 0 := by
    have hca : IsCMField.complexConj E α = (IsCMField.complexConj E u - 1) / h := by
      rw [hα, map_div₀, map_sub, map_one, hch]
    rw [hca, hα]
    field_simp
    linear_combination hu
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdetT ▸ hu0), ?_, ?_⟩
  · intro x y
    show ReciprocityTheory.ChartRestriction.G.FD.herm G (ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α *ᵥ x)
      (ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α *ᵥ y) = ReciprocityTheory.ChartRestriction.G.FD.herm G x y
    rw [GlobalTheory.FlagData.transvMat_mulVec, GlobalTheory.FlagData.transvMat_mulVec, GlobalTheory.FlagData.herm_add_smul_left,
      GlobalTheory.FlagData.herm_add_smul_right, GlobalTheory.FlagData.herm_add_smul_right]
    have e1 : ReciprocityTheory.ChartRestriction.G.FD.cc (α * ReciprocityTheory.ChartRestriction.G.FD.herm G y e) =
        IsCMField.complexConj E α * ReciprocityTheory.ChartRestriction.G.FD.herm G e y := by
      rw [← GlobalTheory.FlagData.cc_herm hG' y e]
      exact map_mul (IsCMField.complexConj E) _ _
    rw [e1, ← hh]
    linear_combination (ReciprocityTheory.ChartRestriction.G.FD.herm G x e * ReciprocityTheory.ChartRestriction.G.FD.herm G e y) * key
  · exact hdetT

end GlobalTheory.UnitDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSurjModIdealExistsCongrOneMulMemRangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sub_one_mem_mul_mem_range_of_finite_surj_mod : ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C), f.Finite → ∀ J : Ideal B, Function.Surjective ((Ideal.Quotient.mk (J.map f)).comp f) → ∃ r : B, r - 1 ∈ J ∧ ∀ c : C, ∃ b : B, f r * c = f b := by
  first | exact @GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range | exact GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range | (intros; apply GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumSemidirectCosetCharacterOrthZeroStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_semidirect_coset_character_orth_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X Y : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X → IsChar ℂ ℂ Y → ∑ᶠ g, X (inl g) * star (Y (inl g)) = 0 → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = 0 := by
  first | (exact @GlobalTheory.Shin.finsum_coset_mul_star_eq_zero) | (exact GlobalTheory.Shin.finsum_coset_mul_star_eq_zero) | (intros; apply GlobalTheory.Shin.finsum_coset_mul_star_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBoundsStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupDeterminantPowDepth_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C), IsSatFrame v u → 0 ≤ detDepth G u c ∧ detDepth G u c ≤ content v (detPow C i c) ∧ detDepth G u c ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) := by
  first | exact @GlobalTheory.FGDepth.detDepth_bounds | exact GlobalTheory.FGDepth.detDepth_bounds | (intros; apply GlobalTheory.FGDepth.detDepth_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCompCoordDilationByHalfExp
section
noncomputable section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory.HeckePoisson.Dilation

open GlobalTheory.HeckeTheta

variable {I : Type} [Fintype I]

def dilPi (y : I → ℝ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) :=
  LinearMap.pi fun i => (Real.exp (y i / 2) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i)

def dilE (y : I → ℝ) : EuclideanSpace ℂ I →ₗ[ℝ] EuclideanSpace ℂ I :=
  ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm : (I → ℂ) →ₗ[ℝ] EuclideanSpace ℂ I) ∘ₗ dilPi y ∘ₗ
    ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm.symm : EuclideanSpace ℂ I →ₗ[ℝ] (I → ℂ))

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma dilE_apply_eq_toLp_dil (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    _root_.GlobalTheory.HeckePoisson.Dilation.dilE y w = WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)) := by
  ext i
  simp [_root_.GlobalTheory.HeckePoisson.Dilation.dilE, _root_.GlobalTheory.HeckePoisson.Dilation.dilPi, _root_.GlobalTheory.HeckeTheta.dil]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma dilE_neg_apply_dilE_apply (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y w) = w := by
  ext i
  simp only [dilE_apply_eq_toLp_dil, _root_.GlobalTheory.HeckeTheta.dil, WithLp.ofLp_toLp, Pi.neg_apply, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma det_dilE_eq_exp_sum (y : I → ℝ) : LinearMap.det (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) = Real.exp (∑ i, y i) := by
  rw [_root_.GlobalTheory.HeckePoisson.Dilation.dilE, LinearMap.det_conj, _root_.GlobalTheory.HeckePoisson.Dilation.dilPi, LinearMap.det_pi, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma inner_dilE_dilE_neg (y : I → ℝ) (v l : EuclideanSpace ℂ I) :
    ⟪_root_.GlobalTheory.HeckePoisson.Dilation.dilE y v, _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) l⟫ = ⟪v, l⟫ := by
  simp [-Complex.ofReal_exp, dilE_apply_eq_toLp_dil, _root_.GlobalTheory.HeckeTheta.dil, real_inner_eq_re_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Real.exp (y i / 2) * Real.exp (-y i / 2) = 1 := by
    rw [← Real.exp_add, show y i / 2 + -y i / 2 = 0 by ring, Real.exp_zero]
  linear_combination ((l.ofLp i).re * (v.ofLp i).re + (l.ofLp i).im * (v.ofLp i).im) * h

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in

theorem _root_.GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ)
    (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l =
      (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by
  let e : EuclideanSpace ℂ I ≃ₗ[ℝ] EuclideanSpace ℂ I :=
    LinearEquiv.ofLinear (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) (_root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y))
      (LinearMap.ext fun w => by simpa using dilE_neg_apply_dilE_apply (-y) w)
      (LinearMap.ext fun w => dilE_neg_apply_dilE_apply y w)
  have hemb : MeasurableEmbedding (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) :=
    e.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hdet : LinearMap.det (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) ≠ 0 := by
    rw [det_dilE_eq_exp_sum]
    exact (Real.exp_pos _).ne'
  have key := hemb.integral_map (μ := volume)
    (fun u => 𝐞 (-⟪u, _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) l⟫) • f u)
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, integral_smul_measure] at key
  simp only [inner_dilE_dilE_neg] at key
  simp only [dilE_apply_eq_toLp_dil] at key
  rw [Real.fourier_eq, Real.fourier_eq, ← key, det_dilE_eq_exp_sum, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (inv_pos.mpr (Real.exp_pos _)), ← Real.exp_neg, Complex.real_smul]

end GlobalTheory.HeckePoisson.Dilation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierHarmonicMonomialMulGaussianComplex
section
noncomputable section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory.HeckeLemma

def lin (a b w : ℂ) : ℂ := a * (w.re : ℂ) + b * (w.im : ℂ)

def ker (l w : ℂ) : ℂ :=
  Complex.exp (-2 * Real.pi * ((w.re : ℂ) ^ 2 + (w.im : ℂ) ^ 2)
    - 2 * Real.pi * Complex.I * ((w.re : ℂ) * l.re + (w.im : ℂ) * l.im))

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem fourier_gaussian_two_pi (l : ℂ) :
    𝓕 (fun v : ℂ => Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ) := by
  have h := fourier_gaussian_innerProductSpace (V := ℂ) (b := 2 * (Real.pi : ℂ))
    (by simp [Real.pi_pos]) l
  have hf : (fun v : ℂ => Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) =
      fun v : ℂ => Complex.exp (-(2 * (Real.pi : ℂ)) * (‖v‖ : ℂ) ^ 2) := by
    funext v; push_cast; ring_nf
  rw [hf, h, Complex.finrank_real_complex]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : ((Real.pi : ℂ) / (2 * Real.pi)) ^ (((2 : ℕ) : ℂ) / 2) = 1 / 2 := by
    rw [show (((2 : ℕ) : ℂ) / 2) = 1 by norm_num, Complex.cpow_one]; field_simp
  rw [h1]
  congr 2
  rw [norm_div, Complex.norm_two]
  push_cast
  field_simp

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem integrable_exp_neg_pi_norm_sq : Integrable (fun v : ℂ => Real.exp (-Real.pi * ‖v‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (Real.pi : ℂ))
    (by simp [Real.pi_pos]) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem integrable_pow_norm_mul_gaussian (m : ℕ) :
    Integrable (fun v : ℂ => ‖v‖ ^ m * Real.exp (-2 * Real.pi * ‖v‖ ^ 2)) := by
  refine (integrable_exp_neg_pi_norm_sq.const_mul ((m.factorial : ℝ) * Real.exp 1)).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun v => ?_)
  have hr : 0 ≤ ‖v‖ := norm_nonneg v
  have h1 : ‖v‖ ^ m ≤ m.factorial * Real.exp ‖v‖ := by
    have := Real.pow_div_factorial_le_exp _ hr m
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : Real.exp ‖v‖ * Real.exp (-2 * Real.pi * ‖v‖ ^ 2) ≤
      Real.exp 1 * Real.exp (-Real.pi * ‖v‖ ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_gt_three, sq_nonneg (‖v‖ - 1 / 2)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖v‖ ^ m * Real.exp (-2 * Real.pi * ‖v‖ ^ 2)
      ≤ (m.factorial * Real.exp ‖v‖) * Real.exp (-2 * Real.pi * ‖v‖ ^ 2) := by gcongr
    _ = m.factorial * (Real.exp ‖v‖ * Real.exp (-2 * Real.pi * ‖v‖ ^ 2)) := by ring
    _ ≤ m.factorial * (Real.exp 1 * Real.exp (-Real.pi * ‖v‖ ^ 2)) := by gcongr
    _ = _ := by ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem norm_conj_pow_mul_gaussian (n : ℕ) (v : ℂ) :
    ‖(starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)‖ =
      ‖v‖ ^ n * Real.exp (-2 * Real.pi * ‖v‖ ^ 2) := by
  rw [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_exp_ofReal]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem integrable_conj_pow_mul_gaussian (n : ℕ) :
    Integrable (fun v : ℂ => (starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) :=
  (integrable_pow_norm_mul_gaussian n).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun v => (norm_conj_pow_mul_gaussian n v).le)

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem integrable_norm_mul_conj_pow_mul_gaussian (n : ℕ) :
    Integrable (fun v : ℂ =>
      ‖v‖ * ‖(starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)‖) := by
  refine (integrable_pow_norm_mul_gaussian (n + 1)).congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [norm_conj_pow_mul_gaussian]
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem hasFDerivAt_conj_pow_mul_gaussian_half (n : ℕ) (l : ℂ) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun z : ℂ => (1 / 2 : ℂ) * (-Complex.I) ^ n *
        ((starRingEnd ℂ) (z / 2) ^ n * Complex.exp ((-2 * Real.pi * ‖z / 2‖ ^ 2 : ℝ) : ℂ))) L l ∧
      L 1 - Complex.I * L Complex.I = -(2 * Real.pi) * ((1 / 2 : ℂ) * (-Complex.I) ^ n *
        ((starRingEnd ℂ) (l / 2) ^ (n + 1) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ))) := by
  have hlin : HasFDerivAt (fun z : ℂ => z / 2) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ) l := by
    refine (((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Complex.real_smul]
    push_cast; ring
  have hP : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) (z / 2))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ)) l :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp l hlin
  have hN := (hlin.norm_sq).const_mul (-2 * Real.pi)
  have hR : HasFDerivAt (fun z : ℂ => ((-2 * Real.pi * ‖z / 2‖ ^ 2 : ℝ) : ℂ)) _ l :=
    Complex.ofRealCLM.hasFDerivAt.comp l hN
  have hQ := hR.cexp
  refine ⟨_, ((hP.pow n).mul hQ).const_mul ((1 / 2 : ℂ) * (-Complex.I) ^ n), ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, Complex.conjCLE_apply, Complex.ofRealCLM_apply, innerSL_apply_apply,
    smul_eq_mul, Function.comp_apply]
  have c2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  have e1 : (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((1 / 2 : ℝ) • (1 : ℂ)) = 1 / 2 := by
    simp [Complex.real_smul, c2]
  have e2 : (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((1 / 2 : ℝ) • Complex.I) = -Complex.I / 2 := by
    simp [Complex.real_smul, c2]; ring
  have i1 : ⟪l / 2, (1 / 2 : ℝ) • (1 : ℂ)⟫ = l.re / 4 := by
    simp [Complex.inner, Complex.real_smul, c2]; ring
  have i2 : ⟪l / 2, (1 / 2 : ℝ) • Complex.I⟫ = l.im / 4 := by
    simp [Complex.inner, Complex.real_smul, c2]; ring
  have hc : (starRingEnd ℂ) (l / 2) = ((l.re : ℂ) - (l.im : ℂ) * Complex.I) / 2 := by
    apply Complex.ext <;> simp [c2]
  rw [e1, e2, i1, i2, pow_succ]
  simp only [nsmul_eq_mul]
  push_cast
  rw [hc]
  ring_nf
  simp only [Complex.I_sq]
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem fourier_fourierSMulRight_sub_I_mul_eq_fourier_conj_mul (g : ℂ → ℂ) (hg : Integrable g)
    (hg' : Integrable (fun v : ℂ => ‖v‖ * ‖g v‖)) (l : ℂ) :
    (𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) g) l) 1 -
        Complex.I * (𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) g) l) Complex.I =
      -(2 * Real.pi * Complex.I) * 𝓕 (fun v : ℂ => (starRingEnd ℂ) v * g v) l := by
  have hS : Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) g) := by
    refine (hg'.const_mul (2 * Real.pi * ‖(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)‖)).mono'
      hg.aestronglyMeasurable.fourierSMulRight (Filter.Eventually.of_forall fun v => ?_)
    calc _ ≤ 2 * Real.pi * ‖(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)‖ * ‖v‖ * ‖g v‖ :=
          VectorFourier.norm_fourierSMulRight_le _ _ _
      _ = _ := by ring
  have hΦ := (Real.fourierIntegral_convergent_iff (μ := volume) l).2 hS
  rw [Real.fourier_eq, Real.fourier_eq, ContinuousLinearMap.integral_apply hΦ,
    ContinuousLinearMap.integral_apply hΦ, ← integral_const_mul,
    ← integral_sub (hΦ.apply_continuousLinearMap 1) ((hΦ.apply_continuousLinearMap Complex.I).const_mul _),
    ← integral_const_mul]
  congr 1
  funext v
  simp only [ContinuousLinearMap.smul_apply, VectorFourier.fourierSMulRight_apply,
    Complex.inner, smul_eq_mul, Circle.smul_def]
  have hc : (starRingEnd ℂ) v = (v.re : ℂ) - (v.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have h1 : ((innerSL ℝ) v : ℂ →L[ℝ] ℝ) 1 = v.re := by
    first
    | (rw [innerSL_apply_apply]; simp [Complex.inner])
    | (show ⟪v, (1 : ℂ)⟫ = v.re; simp [Complex.inner])
  have hI : ((innerSL ℝ) v : ℂ →L[ℝ] ℝ) Complex.I = v.im := by
    first
    | (rw [innerSL_apply_apply]; simp [Complex.inner])
    | (show ⟪v, Complex.I⟫ = v.im; simp [Complex.inner])
  rw [hc, h1, hI]
  ring_nf
  simp only [Complex.I_sq, Complex.real_smul]
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem fourier_conj_pow_mul_gaussian (n : ℕ) : ∀ l : ℂ,
    𝓕 (fun v : ℂ => (starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * (-Complex.I) ^ n *
        ((starRingEnd ℂ) (l / 2) ^ n * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  induction n with
  | zero => intro l; simpa using fourier_gaussian_two_pi l
  | succ n ih =>
    intro l
    have hF : 𝓕 (fun v : ℂ => (starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) =
        fun z : ℂ => (1 / 2 : ℂ) * (-Complex.I) ^ n *
          ((starRingEnd ℂ) (z / 2) ^ n * Complex.exp ((-2 * Real.pi * ‖z / 2‖ ^ 2 : ℝ) : ℂ)) :=
      funext ih
    have hd := Real.hasFDerivAt_fourier (integrable_conj_pow_mul_gaussian n)
      (integrable_norm_mul_conj_pow_mul_gaussian n) l
    rw [hF] at hd
    obtain ⟨L, hL, hLv⟩ := hasFDerivAt_conj_pow_mul_gaussian_half n l
    have heq := hd.unique hL
    have hA := fourier_fourierSMulRight_sub_I_mul_eq_fourier_conj_mul _ (integrable_conj_pow_mul_gaussian n)
      (integrable_norm_mul_conj_pow_mul_gaussian n) l
    rw [heq, hLv] at hA
    have hfun : (fun v : ℂ => (starRingEnd ℂ) v *
        ((starRingEnd ℂ) v ^ n * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ))) =
        fun v : ℂ => (starRingEnd ℂ) v ^ (n + 1) * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ) := by
      funext v; ring
    rw [hfun] at hA
    have h2pi : -(2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ h2pi
    rw [← hA]
    linear_combination (-(2 * (Real.pi : ℂ)) * ((1 / 2 : ℂ) * (-Complex.I) ^ n *
      ((starRingEnd ℂ) (l / 2) ^ (n + 1) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)))) *
      Complex.I_sq

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
private theorem fourier_pow_mul_gaussian (m : ℕ) (l : ℂ) :
    𝓕 (fun v : ℂ => v ^ m * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * (-Complex.I) ^ m *
        ((l / 2) ^ m * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  have hconj : 𝓕 (fun v : ℂ => v ^ m * Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) l =
      (starRingEnd ℂ) (𝓕 (fun v : ℂ => (starRingEnd ℂ) v ^ m *
        Complex.exp ((-2 * Real.pi * ‖v‖ ^ 2 : ℝ) : ℂ)) (-l)) := by
    rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
    congr 1
    funext v
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, map_mul, map_pow,
      Complex.conj_conj, ← Complex.exp_conj, Complex.conj_ofReal, inner_neg_right, Complex.conj_I]
    congr 2
    push_cast
    ring
  rw [hconj, fourier_conj_pow_mul_gaussian m (-l)]
  simp only [map_mul, map_pow, map_neg, Complex.conj_conj, Complex.conj_I, ← Complex.exp_conj,
    Complex.conj_ofReal, neg_div, norm_neg, map_div₀, map_one, map_ofNat]
  rw [neg_pow (l / 2), neg_pow Complex.I]
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in

theorem _root_.GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian : ∀ (k : ℤ) (l : ℂ),
    𝓕 (fun w : ℂ => _root_.GlobalTheory.HeckeTheta.hmon k w *
        Complex.exp ((-2 * Real.pi * ‖w‖ ^ 2 : ℝ) : ℂ)) l =
      (1 / 2 : ℂ) * (-Complex.I) ^ k.natAbs * (_root_.GlobalTheory.HeckeTheta.hmon k (l / 2) *
        Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  intro k l
  unfold _root_.GlobalTheory.HeckeTheta.hmon
  by_cases hk : 0 ≤ k
  · simp only [hk, ↓reduceIte]
    rw [show k.natAbs = k.toNat by omega]
    exact fourier_conj_pow_mul_gaussian k.toNat l
  · simp only [hk, ↓reduceIte]
    rw [show k.natAbs = (-k).toNat by omega]
    exact fourier_pow_mul_gaussian (-k).toNat l

end GlobalTheory.HeckeLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierProdSingleCoordinateFunctions
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory

theorem fourier_prod_coord_complex (I : Type) [Fintype I] (f : I → ℂ → ℂ)
    (_hf : ∀ i, Integrable (f i)) (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => ∏ i, f i (w i)) l = ∏ i, 𝓕 (f i) (l i) := by
  simp only [Real.fourier_eq']
  rw [← integral_fintype_prod_volume_eq_prod,
    ← (volume_preserving_ofLp_complex I).integral_comp
      (MeasurableEquiv.toLp 2 (I → ℂ)).symm.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [smul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum,
    Complex.ofReal_sum, Finset.sum_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfSmoothOfSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem geometricallyConnected_of_smooth_of_section :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
      (e : Spec (CommRingCat.of k) ⟶ X),
      Smooth f → e ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f := by
  intro k _ X f e _ he _
  exact GlobalTheory.RatPointConn.of_section f e he

end GlobalTheory
end

