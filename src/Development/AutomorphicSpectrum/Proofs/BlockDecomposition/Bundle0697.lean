import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0680
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0683
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0667
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightDifferentiableLogarithmic
section
noncomputable section

open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2

namespace GlobalTheory.CompanionTheory.DInt2.DerivW

def cf (i j : Fin 2) : M22 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i)

theorem cf_apply (i j : Fin 2) (X : M22) : cf i j X = X i j := rfl

def colL (j : Fin 2) : M22 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (cf 0 j) + Complex.I • Complex.ofRealCLM.comp (cf 1 j)

theorem colL_zero (X : M22) : colL 0 X = al X := by
  simp [colL, al, cf_apply, mul_comm]

theorem colL_one (X : M22) : colL 1 X = be X := by
  simp [colL, be, cf_apply, mul_comm]

theorem hasFDerivAt_al (h : M22) : HasFDerivAt al (colL 0) h := by
  have : al = colL 0 := funext fun X => (colL_zero X).symm
  rw [this]
  exact (colL 0).hasFDerivAt

theorem hasFDerivAt_be (h : M22) : HasFDerivAt be (colL 1) h := by
  have : be = colL 1 := funext fun X => (colL_one X).symm
  rw [this]
  exact (colL 1).hasFDerivAt

def dc (h : M22) : ℂ := (((Matrix.of h).det : ℝ) : ℂ)

def dL (h : M22) : M22 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    (h 0 0 • cf 1 1 + h 1 1 • cf 0 0 - (h 0 1 • cf 1 0 + h 1 0 • cf 0 1))

theorem dL_apply (h X : M22) : dL h X = (dd h X : ℂ) := by
  simp only [dL, dd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, cf_apply, smul_eq_mul,
    Complex.ofRealCLM_apply]
  congr 1
  ring

theorem hasFDerivAt_dc (h : M22) : HasFDerivAt dc (dL h) h := by
  have e : dc = fun y : M22 => Complex.ofRealCLM
      (cf 0 0 y * cf 1 1 y - cf 0 1 y * cf 1 0 y) := by
    funext y
    simp [dc, Matrix.det_fin_two, cf_apply]
  rw [e]
  have h1 := ((cf 0 0).hasFDerivAt (x := h)).mul ((cf 1 1).hasFDerivAt (x := h))
  have h2 := ((cf 0 1).hasFDerivAt (x := h)).mul ((cf 1 0).hasFDerivAt (x := h))
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp h (h1.sub h2)
  exact h3

theorem hasFDerivAt_zpow_log {f : M22 → ℂ} {f' : M22 →L[ℝ] ℂ} {x : M22}
    (hf : HasFDerivAt f f' x) (n : ℤ) (h0 : f x ≠ 0) :
    HasFDerivAt (fun y => f y ^ n) ((f x ^ n * ((n : ℂ) / f x)) • f') x := by
  have h1 := (hasDerivAt_zpow n (f x) (Or.inl h0)).comp_hasFDerivAt x hf
  have e : (n : ℂ) * f x ^ (n - 1) = f x ^ n * ((n : ℂ) / f x) := by
    rw [zpow_sub_one₀ h0]
    field_simp
  rw [e] at h1
  exact h1

def cl (k : ℕ) (h : M22) : ℂ :=
  dc h ^ (((k - 1 : ℕ)) : ℤ) * al h ^ (-(2 * (k : ℤ) - 1)) *
    Complex.exp (2 * Real.pi * Complex.I * (be h * al h ^ (-1 : ℤ)))

theorem weight_eq_closed_form (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    w0 k h = cl k h := by
  rw [GlobalTheory.CompanionTheory.WeightClosed.main k hk h hΔ]
  simp only [cl, dc, al, be, zpow_natCast, zpow_neg_one, div_eq_mul_inv]

theorem weight_eventually_closed_form (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    w0 k =ᶠ[nhds h] cl k := by
  have hc : Continuous fun y : M22 => (Matrix.of y : Matrix (Fin 2) (Fin 2) ℝ).det :=
    (show Continuous (fun y : M22 => (Matrix.of y : Matrix (Fin 2) (Fin 2) ℝ)) from
      continuous_id).matrix_det
  filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hΔ] with y hy
  exact weight_eq_closed_form k hk y hy

theorem main_deriv (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    DifferentiableAt ℝ (w0 k) h ∧ ∀ X : M22, fderiv ℝ (w0 k) h X = w0 k h * ell k h X := by
  have hA0 : al h ≠ 0 := GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hΔ
  have hD0 : dc h ≠ 0 := by
    simp only [dc]
    exact_mod_cast hΔ.ne'
  have p1 := hasFDerivAt_zpow_log (hasFDerivAt_dc h) (((k - 1 : ℕ)) : ℤ) hD0
  have p2 := hasFDerivAt_zpow_log (hasFDerivAt_al h) (-(2 * (k : ℤ) - 1)) hA0
  have p3 := hasFDerivAt_zpow_log (hasFDerivAt_al h) (-1 : ℤ) hA0
  have q := ((hasFDerivAt_be h).mul p3).const_mul (2 * Real.pi * Complex.I : ℂ)
  have e := q.cexp
  have t := (p1.mul p2).mul e
  have hw := HasFDerivAt.congr_of_eventuallyEq t (weight_eventually_closed_form k hk h hΔ)
  refine ⟨hw.differentiableAt, fun X => ?_⟩
  rw [hw.fderiv, weight_eq_closed_form k hk h hΔ]
  have c1 : ((((k - 1 : ℕ)) : ℤ) : ℂ) = (k : ℂ) - 1 := by
    push_cast [Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  have c2 : ((-(2 * (k : ℤ) - 1) : ℤ) : ℂ) = 1 - 2 * (k : ℂ) := by
    push_cast
    ring
  have c3 : (((Matrix.of h).det : ℝ) : ℂ) = dc h := rfl
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    dL_apply, colL_zero, colL_one, Pi.mul_apply, cl, ell, c1, c2, c3, zpow_neg_one,
    Int.cast_neg, Int.cast_one]
  clear hw t e q p1 p2 p3
  generalize Complex.exp _ = E
  generalize dc h ^ (((k - 1 : ℕ)) : ℤ) = P
  generalize al h ^ (-(2 * (k : ℤ) - 1)) = Q
  generalize al h = A at hA0 ⊢
  generalize dc h = D at hD0 ⊢
  field_simp
  ring

end GlobalTheory.CompanionTheory.DInt2.DerivW

theorem GlobalTheory.CompanionTheory.DInt2.dw0 : ∀ k : ℕ, 3 ≤ k → ∀ h : M22, 0 < (Matrix.of h).det →
    DifferentiableAt ℝ (w0 k) h ∧ ∀ X : M22, fderiv ℝ (w0 k) h X = w0 k h * ell k h X :=
  fun k hk h hΔ => GlobalTheory.CompanionTheory.DInt2.DerivW.main_deriv k hk h hΔ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightMajorantBound
section
noncomputable section

open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2

namespace GlobalTheory.CompanionTheory.DInt2.WMaj

theorem al_re (h : M22) : (al h).re = h 0 0 := by simp [al]
theorem al_im (h : M22) : (al h).im = h 1 0 := by simp [al]
theorem be_re (h : M22) : (be h).re = h 0 1 := by simp [be]
theorem be_im (h : M22) : (be h).im = h 1 1 := by simp [be]

theorem al_ne (h : M22) (hΔ : 0 < (Matrix.of h).det) : al h ≠ 0 :=
  GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hΔ

theorem im_ratio (h : M22) (hΔ : 0 < (Matrix.of h).det) : (be h / al h).im = uu h := by
  have hn : Complex.normSq (al h) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using al_ne h hΔ
  rw [Complex.div_im, uu, Complex.sq_norm, Matrix.det_fin_two, al_re, al_im, be_re, be_im]
  simp only [Matrix.of_apply]
  field_simp

theorem uu_pos (h : M22) (hΔ : 0 < (Matrix.of h).det) : 0 < uu h := by
  have : 0 < ‖al h‖ := norm_pos_iff.mpr (al_ne h hΔ)
  unfold uu
  positivity

theorem norm_weight_closed_form (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    ‖w0 k h‖ = (Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) *
      Real.exp (-(2 * Real.pi * uu h)) := by
  have e := GlobalTheory.CompanionTheory.WeightClosed.main k hk h hΔ
  change w0 k h = (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) * (al h) ^ (-(2 * (k : ℤ) - 1)) *
    Complex.exp (2 * Real.pi * Complex.I * (be h / al h)) at e
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (be h / al h)).re = -(2 * Real.pi * uu h) := by
    rw [← im_ratio h hΔ]
    simp [Complex.mul_re, Complex.mul_im]
  rw [e, norm_mul, norm_mul, norm_pow, norm_zpow, Complex.norm_exp, hre, Complex.norm_real,
    Real.norm_of_nonneg hΔ.le]

theorem norm_Wm (k : ℕ) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    ‖Wm k (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹)‖ =
      (1 / 2 * ((Matrix.of h).det)⁻¹) ^ ((2 * (k : ℝ) - 1) / 2) *
        (‖al h‖ / (Matrix.of h).det) ^ (-(2 * (k : ℤ) - 1)) * Real.exp (-(Real.pi * uu h)) := by
  obtain ⟨i00, i01, i10, i11⟩ := GlobalTheory.CompanionTheory.WeightClosed.inv_entries h
  have hα := al_ne h hΔ
  have hD : (((Matrix.of h).det : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  have hdi : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hdet : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹).det =
      1 / 2 * ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_mul, Matrix.det_diagonal, hdi, Fin.prod_univ_two]
    simp
  have hpos : 0 < (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹).det := by
    rw [hdet]
    have := inv_pos.mpr hΔ
    positivity
  have m00 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 0 =
      1 / 2 * (((Matrix.of h).det)⁻¹ * h 1 1) := by
    rw [Matrix.diagonal_mul, i00]; simp
  have m01 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 1 =
      1 / 2 * (-(((Matrix.of h).det)⁻¹ * h 0 1)) := by
    rw [Matrix.diagonal_mul, i01]; simp
  have m10 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 0 =
      -(((Matrix.of h).det)⁻¹ * h 1 0) := by
    rw [Matrix.diagonal_mul, i10]; simp
  have m11 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 1 =
      ((Matrix.of h).det)⁻¹ * h 0 0 := by
    rw [Matrix.diagonal_mul, i11]; simp
  have e1 : (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 1 : ℝ) : ℂ) -
      (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 0 : ℝ) : ℂ) * Complex.I =
      al h / (((Matrix.of h).det : ℝ) : ℂ) := by
    rw [m11, m10, al]
    push_cast
    field_simp
    ring
  have e2 : (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 1 : ℝ) : ℂ) -
      (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 0 : ℝ) : ℂ) * Complex.I =
      -(be h) / (2 * (((Matrix.of h).det : ℝ) : ℂ)) := by
    rw [m01, m00, be]
    push_cast
    field_simp
    ring
  have hq : -2 * (Real.pi : ℂ) * Complex.I *
      ((-(be h) / (2 * (((Matrix.of h).det : ℝ) : ℂ))) / (al h / (((Matrix.of h).det : ℝ) : ℂ))) =
      (Real.pi : ℂ) * Complex.I * (be h / al h) := by
    field_simp
  have hre : ((Real.pi : ℂ) * Complex.I * (be h / al h)).re = -(Real.pi * uu h) := by
    rw [← im_ratio h hΔ]
    simp [Complex.mul_re, Complex.mul_im]
  have hb : 0 ≤ 1 / 2 * ((Matrix.of h).det)⁻¹ := by
    have := inv_pos.mpr hΔ
    positivity
  unfold Wm
  rw [if_pos hpos, e1, e2, hq, hdet, norm_mul, norm_mul, Complex.norm_real, norm_zpow,
    Complex.norm_exp, hre, norm_div, Complex.norm_real, Real.norm_of_nonneg hΔ.le,
    Real.norm_of_nonneg (Real.rpow_nonneg hb _)]

theorem sq_le_exp (u : ℝ) (hu : 0 ≤ u) : (1 + u) ^ 2 ≤ Real.exp (Real.pi * u) := by
  have hp := Real.pi_gt_three
  have hx : 0 ≤ Real.pi * u := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  have h2 : 3 * u ≤ Real.pi * u := by nlinarith
  have h3 : 9 * u ^ 2 ≤ (Real.pi * u) ^ 2 := by nlinarith [mul_nonneg hu hu]
  nlinarith [mul_nonneg hu hu]

theorem scaled (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    (2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) *
        (‖Wm k (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹)‖ *
          |(Matrix.of h).det| ^ (-(3 : ℝ) / 2)) =
      (Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) *
        Real.exp (-(Real.pi * uu h)) * ((Matrix.of h).det)⁻¹ := by
  have hreal := GlobalTheory.CompanionTheory.WeightClosed.real_factor k (by omega) _ hΔ
  rw [norm_Wm k h hΔ, abs_of_pos hΔ]
  set D := (Matrix.of h).det with hDdef
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hinv : 0 ≤ D⁻¹ := (inv_pos.mpr hΔ).le
  have h32 : D ^ (-(3 : ℝ) / 2) = D ^ (-(1 : ℝ) / 2) * D⁻¹ := by
    rw [← Real.rpow_neg_one D, ← Real.rpow_add hΔ]
    norm_num
  have h2 : (2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) * (1 / 2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) = 1 := by
    rw [← Real.mul_rpow (by norm_num) hhalf]
    norm_num
  rw [Real.mul_rpow hhalf hinv, h32, div_zpow, zpow_neg D, div_inv_eq_mul]
  calc _ = ((2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) * (1 / 2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2)) *
        (D⁻¹ ^ ((2 * (k : ℝ) - 1) / 2) * D ^ (-(1 : ℝ) / 2) * D ^ (2 * (k : ℤ) - 1)) *
        (‖al h‖ ^ (-(2 * (k : ℤ) - 1)) * Real.exp (-(Real.pi * uu h)) * D⁻¹) := by ring
    _ = _ := by rw [h2, hreal]; ring

end GlobalTheory.CompanionTheory.DInt2.WMaj

open GlobalTheory.CompanionTheory.DInt2.WMaj in

theorem GlobalTheory.CompanionTheory.DInt2.WMaj.main : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, ∀ (N : ℕ) (h : M22),
    0 < (Matrix.of h).det →
    (1 + uu h) ^ 2 * ‖w0 k h‖ * |(Matrix.of h).det|⁻¹ /
        ((1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N) ≤ C * Ad3.LR.B.maj k N (1 / 2) 1 h := by
  intro k hk
  refine ⟨(2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2), fun N h hΔ => ?_⟩
  have hsc := scaled k hk h hΔ
  have hu := uu_pos h hΔ
  have hden : 0 < (1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N := by positivity
  have hA : 0 < ‖al h‖ := norm_pos_iff.mpr (al_ne h hΔ)
  have hexp : (1 + uu h) ^ 2 * Real.exp (-(2 * Real.pi * uu h)) ≤ Real.exp (-(Real.pi * uu h)) := by
    have e : Real.exp (-(2 * Real.pi * uu h)) =
        Real.exp (-(Real.pi * uu h)) * Real.exp (-(Real.pi * uu h)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e' : Real.exp (Real.pi * uu h) * Real.exp (-(Real.pi * uu h)) = 1 := by
      rw [← Real.exp_add]; simp
    have := sq_le_exp _ hu.le
    have hp := Real.exp_pos (-(Real.pi * uu h))
    rw [e]
    calc (1 + uu h) ^ 2 * (Real.exp (-(Real.pi * uu h)) * Real.exp (-(Real.pi * uu h)))
        ≤ Real.exp (Real.pi * uu h) * (Real.exp (-(Real.pi * uu h)) * Real.exp (-(Real.pi * uu h))) := by
          gcongr
      _ = Real.exp (-(Real.pi * uu h)) := by rw [← mul_assoc, e', one_mul]
  unfold Ad3.LR.B.maj
  rw [abs_one, one_mul, ← mul_div_assoc, hsc, norm_weight_closed_form k hk h hΔ, abs_of_pos hΔ]
  apply div_le_div_of_nonneg_right _ hden.le
  have hc : 0 ≤ (Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) *
      ((Matrix.of h).det)⁻¹ := by
    have := inv_pos.mpr hΔ
    positivity
  calc _ = ((Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) * ((Matrix.of h).det)⁻¹) *
        ((1 + uu h) ^ 2 * Real.exp (-(2 * Real.pi * uu h))) := by ring
    _ ≤ ((Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) * ((Matrix.of h).det)⁻¹) *
        Real.exp (-(Real.pi * uu h)) := mul_le_mul_of_nonneg_left hexp hc
    _ = _ := by ring
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBoundStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_rank_extension_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V W₁ W₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ (GL (Fin N) k) V) (π : Representation ℂ (GL (Fin N) k) W₁) (σ : Representation ℂ (GL (Fin N) k) W₂), IsSmooth ρ → Module.rank ℂ (TwJacquet ρ (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 → π.IsIrreducible → σ.IsIrreducible → IsSubquotient π ρ → IsSubquotient σ ρ → IsGenericFor ψ π → IsGenericFor ψ σ → Nonempty (π.Equiv σ) := by
  first | exact @GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients | exact GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients | (intros; apply GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients <;> assumption)
end

