import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaBoundVerticalStrip
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.DigammaStrip

theorem exists_Gamma_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 5 / 2 → Real.Gamma x ≤ K := by
  have hc : ContinuousOn Real.Gamma (Set.Icc (1 / 2) (5 / 2)) := fun x hx =>
    (Real.differentiableAt_Gamma (fun m h => by
      have h1 := hx.1
      have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)).continuousAt.continuousWithinAt
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hc
  exact ⟨max K 1, lt_max_of_lt_right one_pos,
    fun x h1 h2 => (hK ⟨x, ⟨h1, h2⟩, rfl⟩).trans (le_max_left _ _)⟩

theorem norm_sin_le_exp (u : ℂ) : ‖Complex.sin u‖ ≤ Real.exp |u.im| := by
  have h1 : ‖Complex.exp (-u * I)‖ ≤ Real.exp |u.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by simpa using le_abs_self u.im)
  have h2 : ‖Complex.exp (u * I)‖ ≤ Real.exp |u.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by simpa using neg_le_abs u.im)
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h3 := norm_sub_le (Complex.exp (-u * I)) (Complex.exp (u * I))
  simp only [Complex.norm_ofNat]
  linarith

theorem norm_inv_Gamma_le {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 5 / 2 → Real.Gamma x ≤ K) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5 / 2) (h3 : 1 / 4 ≤ |w.im|) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ 16 * K * Real.exp (Real.pi * |w.im|) := by
  have hw0 : w.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at h3
    norm_num at h3
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsin : Complex.sin (Real.pi * w) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have := congrArg Complex.im hk
    exact hw0 (by simpa using this)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  have hinv : (Complex.Gamma w)⁻¹ = Complex.Gamma (1 - w) * Complex.sin (Real.pi * w) / Real.pi := by
    have h6 : Complex.Gamma w * Complex.Gamma (1 - w) * Complex.sin (Real.pi * w) = Real.pi := by
      rw [hrefl, div_mul_cancel₀ _ hsin]
    refine eq_div_of_mul_eq hpi ?_
    rw [inv_mul_eq_iff_eq_mul₀ hG]
    linear_combination -h6
  have hn1 : (1 - w) ≠ 0 := fun h => hw0 (by
    have := congrArg Complex.im h
    simpa using this)
  have hn2 : (2 - w) ≠ 0 := fun h => hw0 (by
    have := congrArg Complex.im h
    simpa using this)
  have hrec : Complex.Gamma (3 - w) = (2 - w) * ((1 - w) * Complex.Gamma (1 - w)) := by
    have e1 := Complex.Gamma_add_one (1 - w) hn1
    have e2 := Complex.Gamma_add_one (2 - w) hn2
    rw [show (2 - w) + 1 = 3 - w by ring] at e2
    rw [show (1 - w) + 1 = 2 - w by ring] at e1
    rw [e2, e1]
  have hb1 : 1 / 4 ≤ ‖1 - w‖ := by
    refine h3.trans ?_
    have := Complex.abs_im_le_norm (1 - w)
    simpa using this
  have hb2 : 1 / 4 ≤ ‖2 - w‖ := by
    refine h3.trans ?_
    have := Complex.abs_im_le_norm (2 - w)
    simpa using this
  have hre3 : (3 - w).re = 3 - w.re := by simp
  have hG3 : ‖Complex.Gamma (3 - w)‖ ≤ K :=
    (PI.EF.norm_Gamma_le (by rw [hre3]; linarith)).trans
      (hK _ (by rw [hre3]; linarith) (by rw [hre3]; linarith))
  have hG1 : ‖Complex.Gamma (1 - w)‖ ≤ 16 * K := by
    rw [hrec, norm_mul, norm_mul] at hG3
    have hp := norm_nonneg (Complex.Gamma (1 - w))
    have : (1 / 4) * ((1 / 4) * ‖Complex.Gamma (1 - w)‖) ≤
        ‖2 - w‖ * (‖1 - w‖ * ‖Complex.Gamma (1 - w)‖) := by gcongr
    linarith
  have hs : ‖Complex.sin (Real.pi * w)‖ ≤ Real.exp (Real.pi * |w.im|) := by
    refine (norm_sin_le_exp _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [div_le_iff₀ Real.pi_pos]
  have he := Real.exp_pos (Real.pi * |w.im|)
  calc ‖Complex.Gamma (1 - w)‖ * ‖Complex.sin (Real.pi * w)‖
      ≤ (16 * K) * Real.exp (Real.pi * |w.im|) := by gcongr
    _ = 16 * K * Real.exp (Real.pi * |w.im|) * 1 := by ring
    _ ≤ 16 * K * Real.exp (Real.pi * |w.im|) * Real.pi := by gcongr

theorem deriv_inv_Gamma_div {z : ℂ} (hz : 0 < z.re) :
    deriv (fun w => (Complex.Gamma w)⁻¹) z / (Complex.Gamma z)⁻¹ = -digamma z := by
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hd : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z (fun m h => by
    have := congrArg Complex.re h
    simp at this
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  have h7 : HasDerivAt (fun w => (Complex.Gamma w)⁻¹)
      (-deriv Complex.Gamma z / Complex.Gamma z ^ 2) z := hd.hasDerivAt.inv hG
  rw [h7.deriv, Complex.digamma_def, logDeriv_apply]
  field_simp

theorem norm_digamma_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 2 → 1 / 2 ≤ |z.im| →
      ‖digamma z‖ ≤ C * (1 + |z.im|) := by
  obtain ⟨C0, hC0, H⟩ := GlobalTheory.LWide.disc (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨K, hK0, hK⟩ := exists_Gamma_bound
  set L : ℝ := Real.log (16 * K ^ 2) with hL
  refine ⟨4 * C0 * (1 + |L| + 4 * Real.pi), by positivity, fun z hz1 hz2 hzi => ?_⟩
  set t : ℝ := |z.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  set F : ℂ → ℂ := fun w => (Complex.Gamma w)⁻¹ with hF
  have hFd : Differentiable ℂ F := by
    have h := Complex.differentiable_one_div_Gamma
    simpa [hF, one_div] using h
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hFz : F z ≠ 0 := inv_ne_zero hGz
  have hM : ∀ w, ‖w - z‖ ≤ 1 / 4 → ‖F w‖ ≤ 16 * K * Real.exp (Real.pi * (t + 1)) := by
    intro w hw
    have hre : |w.re - z.re| ≤ 1 / 4 := by
      have := (Complex.abs_re_le_norm (w - z)).trans hw
      simpa using this
    have him : |w.im - z.im| ≤ 1 / 4 := by
      have := (Complex.abs_im_le_norm (w - z)).trans hw
      simpa using this
    have hre' := abs_le.1 hre
    have h1 : t ≤ |w.im| + 1 / 4 := by
      have := abs_sub_abs_le_abs_sub z.im w.im
      rw [abs_sub_comm z.im w.im] at this
      linarith
    have h2 : |w.im| ≤ t + 1 / 4 := by
      have := abs_sub_abs_le_abs_sub w.im z.im
      linarith
    refine (norm_inv_Gamma_le hK0 hK (by linarith [hre'.1]) (by linarith [hre'.2])
      (by linarith)).trans ?_
    gcongr
    linarith
  obtain ⟨-, -, h3⟩ := H F z (1 / 4) (16 * K * Real.exp (Real.pi * (t + 1))) (by norm_num) hFd hFz hM
  have hempty : {w : ℂ | ‖w - z‖ ≤ 1 / 2 * (1 / 4) ∧ F w = 0} = ∅ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hw
    have hre : |w.re - z.re| ≤ 1 / 2 * (1 / 4) := by
      have := (Complex.abs_re_le_norm (w - z)).trans hw
      simpa using this
    have hre' := abs_le.1 hre
    exact inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by linarith [hre'.1]))
  have h4 := h3 z (by simp) hFz
  rw [hempty, finsum_mem_empty, sub_zero, deriv_inv_Gamma_div (by linarith), norm_neg] at h4
  have hnz : ‖Complex.Gamma z‖ ≤ K :=
    (PI.EF.norm_Gamma_le (by linarith)).trans (hK _ (by linarith) (by linarith))
  have hnz0 : 0 < ‖Complex.Gamma z‖ := norm_pos_iff.2 hGz
  have hlog : Real.log (16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖) ≤ L + Real.pi * (t + 1) := by
    have he : 16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖ =
        (16 * K * ‖Complex.Gamma z‖) * Real.exp (Real.pi * (t + 1)) := by
      simp only [hF, norm_inv]
      field_simp
    rw [he, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    have : Real.log (16 * K * ‖Complex.Gamma z‖) ≤ L := by
      apply Real.log_le_log (by positivity)
      nlinarith
    linarith
  have hL' : L ≤ |L| := le_abs_self L
  have hpi := Real.pi_pos
  have hfin : (1 / 4) * ‖digamma z‖ ≤ C0 * (1 + |L| + 4 * Real.pi) * (1 + t) := by
    refine h4.trans ?_
    have h5 : 1 + Real.log (16 * K * Real.exp (Real.pi * (t + 1)) / ‖F z‖) ≤
        (1 + |L| + 4 * Real.pi) * (1 + t) := by
      have h6 : 0 ≤ t * (1 + |L|) := by positivity
      nlinarith
    calc _ ≤ C0 * ((1 + |L| + 4 * Real.pi) * (1 + t)) := by gcongr
      _ = _ := by ring
  linarith

end GlobalTheory.CompanionTheory.DigammaStrip
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundLeftRegion
section
namespace GlobalTheory.CompanionTheory.DigammaLeft

theorem digamma_sub_digamma_one_sub (w : ℂ) (hw : ∀ n : ℤ, w ≠ n) :
    Complex.digamma w - Complex.digamma (1 - w) =
      -((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)) := by
  have hw1 : ∀ m : ℕ, w ≠ -(m : ℂ) := fun m h => hw (-(m : ℤ)) (by rw [h]; push_cast; rfl)
  have hw2 : ∀ m : ℕ, 1 - w ≠ -(m : ℂ) := fun m h => hw ((m : ℤ) + 1) (by
    push_cast
    linear_combination -h)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : Complex.sin (Real.pi * w) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    apply hw k
    apply mul_left_cancel₀ hpi
    rw [hk]; ring
  have ha : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw1
  have hb : Complex.Gamma (1 - w) ≠ 0 := Complex.Gamma_ne_zero hw2
  have hG1 : HasDerivAt Complex.Gamma (deriv Complex.Gamma w) w :=
    (Complex.differentiableAt_Gamma w hw1).hasDerivAt
  have hG2' : HasDerivAt Complex.Gamma (deriv Complex.Gamma (1 - w)) (1 - w) :=
    (Complex.differentiableAt_Gamma (1 - w) hw2).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => 1 - z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have hG2 : HasDerivAt (fun z : ℂ => Complex.Gamma (1 - z))
      (deriv Complex.Gamma (1 - w) * (-1)) w :=
    HasDerivAt.comp w hG2' hlin
  have hprod := hG1.mul hG2
  have hsin : HasDerivAt (fun z : ℂ => Complex.sin (Real.pi * z))
      (Complex.cos (Real.pi * w) * Real.pi) w := by
    have h1 : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) Real.pi w := by
      simpa using (hasDerivAt_id w).const_mul (Real.pi : ℂ)
    exact (Complex.hasDerivAt_sin _).comp w h1
  have hquot := (hasDerivAt_const w (Real.pi : ℂ)).div hsin hs
  have hfun : ((fun _ : ℂ => (Real.pi : ℂ)) / fun z : ℂ => Complex.sin (Real.pi * z)) =
      (Complex.Gamma * fun z : ℂ => Complex.Gamma (1 - z)) := by
    funext z
    simp only [Pi.mul_apply, Pi.div_apply]
    exact (Complex.Gamma_mul_Gamma_one_sub z).symm
  rw [hfun] at hquot
  have huniq := hprod.unique hquot
  have hab : Complex.Gamma w * Complex.Gamma (1 - w) = Real.pi / Complex.sin (Real.pi * w) :=
    Complex.Gamma_mul_Gamma_one_sub w
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply]
  have e1 : deriv Complex.Gamma w / Complex.Gamma w -
      deriv Complex.Gamma (1 - w) / Complex.Gamma (1 - w) =
      (deriv Complex.Gamma w * Complex.Gamma (1 - w) +
        Complex.Gamma w * (deriv Complex.Gamma (1 - w) * -1)) /
      (Complex.Gamma w * Complex.Gamma (1 - w)) := by
    field_simp
    ring
  rw [e1, huniq, hab]
  field_simp
  ring

theorem sq_norm_sin (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.sin_eq, Complex.normSq_apply]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_mul]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re]
  have h1 := Real.sin_sq_add_cos_sq z.re
  have h2 := Real.cosh_sq z.im
  linear_combination Real.sin z.re ^ 2 * h2 + Real.sinh z.im ^ 2 * h1

theorem sq_norm_cos (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.cos_eq, Complex.normSq_apply]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_mul]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re]
  have h1 := Real.sin_sq_add_cos_sq z.re
  have h2 := Real.cosh_sq z.im
  linear_combination Real.cos z.re ^ 2 * h2 + Real.sinh z.im ^ 2 * h1

theorem norm_cos_le_of_im (z : ℂ) (h : 1 ≤ |z.im|) : ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖ := by
  have h1 : 1 ≤ |Real.sinh z.im| := by
    rw [Real.abs_sinh]
    exact h.trans (Real.self_le_sinh_iff.mpr (abs_nonneg _))
  have h2 : 1 ≤ Real.sinh z.im ^ 2 := by
    rw [← sq_abs]; nlinarith
  have hc := sq_norm_cos z
  have hs := sq_norm_sin z
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, hc, hs]
  nlinarith [Real.cos_sq_le_one z.re, sq_nonneg (Real.sin z.re)]

theorem norm_cos_le_of_re (z : ℂ) (k : ℤ) (h : z.re = Real.pi * ((k : ℝ) / 2 + 1 / 4)) :
    ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖ := by
  have hc := sq_norm_cos z
  have hs := sq_norm_sin z
  have h2 : Real.cos (2 * z.re) = 0 := by
    have : 2 * z.re = (k : ℝ) * Real.pi + Real.pi / 2 := by rw [h]; ring
    rw [this, Real.cos_add_pi_div_two, Real.sin_int_mul_pi, neg_zero]
  have h3 : Real.cos z.re ^ 2 = Real.sin z.re ^ 2 := by
    have := Real.cos_sq' z.re
    rw [Real.cos_two_mul] at h2
    nlinarith
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, hc, hs, h3]
  nlinarith [sq_nonneg (Real.sin z.re), sq_nonneg (Real.sinh z.im)]

theorem norm_digamma_le_left :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re ≤ 1 / 4 →
      (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) →
      ‖Complex.digamma w‖ ≤ C * Real.log (‖w‖ + 2) := by
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.digamma_log_bound_right_half_plane
  refine ⟨2 * C + 10, by positivity, fun w hre halt => ?_⟩
  have hint : ∀ n : ℤ, w ≠ n := by
    intro n hn
    rcases halt with h | ⟨k, hk⟩
    · rw [hn] at h
      norm_num at h
    · have h1 : (n : ℝ) = (k : ℝ) / 2 + 1 / 4 := by
        rw [← hk, hn]; simp
      have h4 : (4 * n : ℝ) = 2 * k + 1 := by linarith
      have h5 : 4 * n = 2 * k + 1 := by exact_mod_cast h4
      omega
  have hcot : ‖Complex.cos (Real.pi * w)‖ ≤ 2 * ‖Complex.sin (Real.pi * w)‖ := by
    rcases halt with h | ⟨k, hk⟩
    · apply norm_cos_le_of_im
      have him : ((Real.pi : ℂ) * w).im = Real.pi * w.im := by simp
      rw [him, abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    · apply norm_cos_le_of_re _ k
      simp [hk]
  have hcotn : ‖(Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)‖ ≤
      2 * Real.pi := by
    rcases eq_or_ne (Complex.sin (Real.pi * w)) 0 with h0 | h0
    · rw [h0]
      simp [Real.pi_pos.le]
    · have hpos : 0 < ‖Complex.sin (Real.pi * w)‖ := norm_pos_iff.mpr h0
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        div_le_iff₀ hpos]
      nlinarith [Real.pi_pos]
  have hrefl := digamma_sub_digamma_one_sub w hint
  have hdecomp : Complex.digamma w = Complex.digamma (1 - w) +
      -((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)) := by
    rw [← hrefl]; ring
  have hbd := hb (1 - w) (by simp; linarith)
  have hw0 := norm_nonneg w
  have hL : Real.log 2 ≤ Real.log (‖w‖ + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h1w : ‖1 - w‖ ≤ 1 + ‖w‖ := by simpa using norm_sub_le 1 w
  have hl2 : Real.log (‖1 - w‖ + 2) ≤ 2 * Real.log (‖w‖ + 2) := by
    have h2 : Real.log (‖1 - w‖ + 2) ≤ Real.log ((‖w‖ + 2) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rwa [Real.log_pow, Nat.cast_ofNat] at h2
  have hpi : 2 * Real.pi ≤ 10 * Real.log (‖w‖ + 2) := by
    linarith [Real.pi_lt_d2, Real.log_two_gt_d9]
  have hmul : C * Real.log (‖1 - w‖ + 2) ≤ C * (2 * Real.log (‖w‖ + 2)) :=
    mul_le_mul_of_nonneg_left hl2 hC.le
  calc ‖Complex.digamma w‖
      ≤ ‖Complex.digamma (1 - w)‖ +
          ‖(Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)‖ := by
        rw [hdecomp]
        simpa using norm_add_le (Complex.digamma (1 - w))
          (-((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)))
    _ ≤ (2 * C + 10) * Real.log (‖w‖ + 2) := by nlinarith

end GlobalTheory.CompanionTheory.DigammaLeft
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisOnLocalizationAway
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.Glob.ResKCoords

theorem isCoords_basicOpen_of_away :
    ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ}
      (x : Fin n → Γ(Y, U.1)),
      (letI := secAlgebra g U.1;
        ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B]
          [IsLocalization.Away s B],
          LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧
            Submodule.span B (Set.range fun i =>
              KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) →
        IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  intro K _ Y g U s n x h
  letI aU : Algebra K Γ(Y, U.1) := secAlgebra g U.1
  letI aB : Algebra K Γ(Y, Y.basicOpen s) := secAlgebra g (Y.basicOpen s)
  letI aUB : Algebra Γ(Y, U.1) Γ(Y, Y.basicOpen s) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom.toAlgebra
  haveI tower : IsScalarTower K Γ(Y, U.1) Γ(Y, Y.basicOpen s) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial)).hom = _
    have e : g.appLE ⊤ U.1 (fun _ _ => trivial) ≫ Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op =
        g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial) := by
      exact Scheme.Hom.appLE_map _ _ _
    rw [← e]
    rfl
  haveI loc : IsLocalization.Away s Γ(Y, Y.basicOpen s) := U.2.isLocalization_basicOpen s
  exact h Γ(Y, Y.basicOpen s)

end GlobalTheory.CompanionTheory.Glob.ResKCoords
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisSpreadsToNeighbourhood
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.KaehlerSpread

open KaehlerDifferential

noncomputable abbrev diffMap (K : Type) {A : Type} [Field K] [CommRing A] [Algebra K A] {n : ℕ}
    (x : Fin n → A) : (Fin n →₀ A) →ₗ[A] Ω[A⁄K] :=
  Finsupp.linearCombination A fun i => D K A (x i)

theorem map_diffMap_eq (K : Type) {A : Type} [Field K] [CommRing A] [Algebra K A] {n : ℕ}
    (x : Fin n → A) (S : Submonoid A) (B : Type) [CommRing B] [Algebra A B] [Algebra K B]
    [IsScalarTower K A B] [IsLocalization S B] :
    (IsLocalizedModule.mapExtendScalars S
      (Finsupp.mapRange.linearMap (Algebra.linearMap A B) : (Fin n →₀ A) →ₗ[A] (Fin n →₀ B))
      (map K K A B) B (diffMap K x)) =
      Finsupp.linearCombination B fun i => D K B (algebraMap A B (x i)) := by
  refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have h1 : (Finsupp.single i (1 : B) : Fin n →₀ B) =
      Finsupp.mapRange.linearMap (Algebra.linearMap A B) (Finsupp.single i (1 : A)) := by
    simp
  rw [h1, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]
  simp [diffMap]

theorem bijective_linearCombination_iff {B M ι : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (v : ι → M) :
    Function.Bijective (Finsupp.linearCombination B v) ↔
      LinearIndependent B v ∧ Submodule.span B (Set.range v) = ⊤ := by
  rw [Function.Bijective, ← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  rfl

theorem spread : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A), (LinearIndependent (Localization.AtPrime P) (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧ Submodule.span (Localization.AtPrime P) (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) → ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := by
  intro K A _ _ _ _ P _ n x hP
  classical
  let l₁ : (Fin n →₀ A) →ₗ[A] (Fin n →₀ Localization.AtPrime P) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.AtPrime P))
  let l₂ : Ω[A⁄K] →ₗ[A] Ω[Localization.AtPrime P⁄K] :=
    KaehlerDifferential.map K K A (Localization.AtPrime P)
  have hP' : Function.Bijective (IsLocalizedModule.map P.primeCompl l₁ l₂ (diffMap K x)) := by
    have h := (bijective_linearCombination_iff _).mpr hP
    rw [← map_diffMap_eq K x P.primeCompl (Localization.AtPrime P)] at h
    exact h
  obtain ⟨s, hs, hbij⟩ :=
    Module.FinitePresentation.exists_notMem_bijective (diffMap K x) P l₁ l₂ hP'
  refine ⟨s, hs, ?_⟩
  intro B _ _ _ _ _
  rw [← bijective_linearCombination_iff, ← map_diffMap_eq K x (Submonoid.powers s) B]
  exact (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Finsupp.mapRange.linearMap (Algebra.linearMap A B)) (KaehlerDifferential.map K K A B)).mpr hbij

end GlobalTheory.CompanionTheory.KaehlerSpread
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDet
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QLDet

variable {F : Type} [Field F]

theorem det_mem_of_isInt (O : Subring F) {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsInt O M) :
    M.det ∈ O := by
  let M' : Matrix (Fin n) (Fin n) O := fun a b => ⟨M a b, h a b⟩
  have hM : M = O.subtype.mapMatrix M' := by
    ext a b
    rfl
  rw [hM, ← RingHom.map_det]
  exact (M'.det).2

theorem adjugate_isInt (O : Subring F) {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsInt O M) :
    IsInt O M.adjugate := by
  let M' : Matrix (Fin n) (Fin n) O := fun a b => ⟨M a b, h a b⟩
  have hM : M = O.subtype.mapMatrix M' := by
    ext a b
    rfl
  intro a b
  rw [hM, ← RingHom.map_adjugate]
  exact (M'.adjugate a b).2

theorem mem_GLint_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (hLF : LF O ϖ nrm q) (n : ℕ) (g : GL (Fin n) F) :
    g ∈ GLint O n ↔ (IsInt O (g : Matrix (Fin n) (Fin n) F) ∧
      nrm (g : Matrix (Fin n) (Fin n) F).det = 1) := by
  obtain ⟨-, -, hO, -, -, -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties hLF
  have hdet : (g : Matrix (Fin n) (Fin n) F).det * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ : IsInt O (g : Matrix (Fin n) (Fin n) F) ∧
        IsInt O ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := hg
    refine ⟨h1, ?_⟩
    have a1 := (hO _).2 (det_mem_of_isInt O h1)
    have a2 := (hO _).2 (det_mem_of_isInt O h2)
    have hm : nrm (g : Matrix (Fin n) (Fin n) F).det *
        nrm ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
      rw [← map_mul, hdet, map_one]
    have p1 := nrm.nonneg (g : Matrix (Fin n) (Fin n) F).det
    have p2 := nrm.nonneg ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det
    nlinarith
  · rintro ⟨h1, h2⟩
    show IsInt O (g : Matrix (Fin n) (Fin n) F) ∧ IsInt O ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    refine ⟨h1, ?_⟩
    intro a b
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    apply O.mul_mem
    · apply (hO _).1
      rw [map_inv₀, h2, inv_one]
    · exact adjugate_isInt O h1 a b

end GlobalTheory.CompanionTheory.QLDet
end

