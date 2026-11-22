import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0679
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0676
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0671
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0680
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveIntegralBoundOfParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParsevalBoundMax
section
noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.Parseval.Max

theorem fz_decay2 (Φ : Sw) (N : ℕ) : ∃ C : ℝ, ∀ (A : M22) (ξ : Fin 2 → ℝ),
    (1 + ‖A‖) ^ N * ((1 + ‖ξ‖) ^ 2 * ‖fz Φ A ξ‖) ≤ C := by
  classical
  have key : ∀ j : Fin 2, ∃ C : ℝ, ∀ (A : M22) (ξ : Fin 2 → ℝ),
      (1 + ‖A‖) ^ N * (|ξ j| ^ 2 * ‖fz Φ A ξ‖) ≤ C := by
    intro j
    obtain ⟨Ψ₁, h₁⟩ := GlobalTheory.CompanionTheory.Parseval.Ibp.main Φ j
    obtain ⟨Ψ₂, h₂⟩ := GlobalTheory.CompanionTheory.Parseval.Ibp.main Ψ₁ j
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Parseval.fz_decay_in_A Ψ₂ N
    refine ⟨C, fun A ξ => ?_⟩
    have e : ‖fz Ψ₂ A ξ‖ = (2 * Real.pi * |ξ j|) ^ 2 * ‖fz Φ A ξ‖ := by
      rw [h₂, h₁, norm_mul, norm_mul]
      have : ‖-(2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ))‖ = 2 * Real.pi * |ξ j| := by
        simp [abs_of_pos Real.pi_pos]
      rw [this]; ring
    have hp : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
      have := Real.pi_gt_three
      nlinarith
    have hA : 0 ≤ (1 + ‖A‖) ^ N := by positivity
    refine le_trans ?_ (hC A ξ)
    refine mul_le_mul_of_nonneg_left ?_ hA
    rw [e, mul_pow]
    have : 0 ≤ |ξ j| ^ 2 * ‖fz Φ A ξ‖ := by positivity
    nlinarith
  obtain ⟨C₀, h₀⟩ := GlobalTheory.CompanionTheory.Parseval.fz_decay_in_A Φ N
  obtain ⟨C₁, h₁⟩ := key 0
  obtain ⟨C₂, h₂⟩ := key 1
  refine ⟨2 * (C₀ + C₁ + C₂) + 0, fun A ξ => ?_⟩
  have hx : ‖ξ‖ ^ 2 ≤ |ξ 0| ^ 2 + |ξ 1| ^ 2 := by
    have hn : ‖ξ‖ ≤ max |ξ 0| |ξ 1| := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      fin_cases i
      · simpa using le_max_left _ _
      · simpa using le_max_right _ _
    have h2 : ‖ξ‖ ^ 2 ≤ (max |ξ 0| |ξ 1|) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    refine h2.trans ?_
    rcases max_cases |ξ 0| |ξ 1| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith [sq_nonneg |ξ 0|, sq_nonneg |ξ 1|]
  have hsq : (1 + ‖ξ‖) ^ 2 ≤ 2 * (1 + |ξ 0| ^ 2 + |ξ 1| ^ 2) := by
    nlinarith [sq_nonneg (‖ξ‖ - 1)]
  have hf : 0 ≤ ‖fz Φ A ξ‖ := norm_nonneg _
  have hA : 0 ≤ (1 + ‖A‖) ^ N := by positivity
  have s := h₀ A ξ
  have s1 := h₁ A ξ
  have s2 := h₂ A ξ
  calc (1 + ‖A‖) ^ N * ((1 + ‖ξ‖) ^ 2 * ‖fz Φ A ξ‖)
      ≤ (1 + ‖A‖) ^ N * ((2 * (1 + |ξ 0| ^ 2 + |ξ 1| ^ 2)) * ‖fz Φ A ξ‖) := by gcongr
    _ = 2 * ((1 + ‖A‖) ^ N * ‖fz Φ A ξ‖ + (1 + ‖A‖) ^ N * (|ξ 0| ^ 2 * ‖fz Φ A ξ‖)
          + (1 + ‖A‖) ^ N * (|ξ 1| ^ 2 * ‖fz Φ A ξ‖)) := by ring
    _ ≤ 2 * (C₀ + C₁ + C₂) + 0 := by linarith

theorem parseval_bound_max (Φ : Sw) (N : ℕ) : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (h : M22) (v : ℝ),
    (Matrix.of h).det ≠ 0 →
    ‖Ae Φ ε h v‖ ≤ C * ((max |(Matrix.of h).det|
      (|h 0 0 * h 0 1 + h 1 0 * h 1 1| / Real.sqrt (h 0 1 ^ 2 + h 1 1 ^ 2)))⁻¹ / (1 + ‖h‖) ^ N) := by
  obtain ⟨C₁, hC₁⟩ := fz_decay2 Φ N
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.CompanionTheory.Parseval.OneDim.wt_gau_bound
  have hC₁0 : 0 ≤ C₁ := le_trans (by positivity) (hC₁ 0 0)
  set K : ℝ := max C₂ 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  refine ⟨C₁ * (1 + 4 * K), fun ε hε _ h v hdet => ?_⟩
  set D : ℝ := |(Matrix.of h).det| with hD
  have hD0 : 0 < D := abs_pos.2 hdet
  set S : ℝ := h 0 0 * h 0 1 + h 1 0 * h 1 1 with hSdef
  set m : ℝ := h 0 1 ^ 2 + h 1 1 ^ 2 with hm
  have hm0 : 0 < m := by
    have : m ≠ 0 := by
      intro h0
      have a1 : h 0 1 = 0 := by nlinarith [sq_nonneg (h 0 1), sq_nonneg (h 1 1)]
      have a2 : h 1 1 = 0 := by nlinarith [sq_nonneg (h 0 1), sq_nonneg (h 1 1)]
      apply hdet
      simp [Matrix.det_fin_two, a1, a2]
    exact lt_of_le_of_ne (by positivity) this.symm
  set n : ℝ := Real.sqrt m with hn
  have hn0 : 0 < n := Real.sqrt_pos.2 hm0
  have hnn : n * n = m := Real.mul_self_sqrt hm0.le
  set P : ℝ := (1 + ‖h‖) ^ N with hP
  have hP0 : 0 < P := by positivity
  set a : ℝ := D / n with ha
  have ha0 : 0 < a := div_pos hD0 hn0
  set l : ℝ := S / m with hl
  have hg : ∀ ζ, ‖gz Φ h ζ‖ ≤ D⁻¹ * C₁ / P * ((1 + ‖dualF h ζ‖) ^ 2)⁻¹ := by
    intro ζ
    rw [GlobalTheory.CompanionTheory.Parseval.gz_eq_fz Φ h ζ hdet, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hD0.le)]
    have := hC₁ h (dualF h ζ)
    have hq : 0 < (1 + ‖dualF h ζ‖) ^ 2 := by positivity
    have h3 : ‖fz Φ h (dualF h ζ)‖ ≤ C₁ / P * ((1 + ‖dualF h ζ‖) ^ 2)⁻¹ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hP0, ← div_eq_mul_inv, le_div_iff₀ hq]
      calc _ = P * ((1 + ‖dualF h ζ‖) ^ 2 * ‖fz Φ h (dualF h ζ)‖) := by ring
        _ ≤ C₁ := this
    calc D⁻¹ * ‖fz Φ h (dualF h ζ)‖ ≤ D⁻¹ * (C₁ / P * ((1 + ‖dualF h ζ‖) ^ 2)⁻¹) := by gcongr
      _ = _ := by ring
  set B : ℝ := D⁻¹ * C₁ / P with hB
  have hB0 : 0 ≤ B := by positivity
  have hnormI : ∀ ζ, ‖(gau ε ζ : ℂ) * Ad3.psiR (ζ * v) * gz Φ h ζ‖ = gau ε ζ * ‖gz Φ h ζ‖ := by
    intro ζ
    have : ‖Ad3.psiR (ζ * v)‖ = 1 := by
      unfold Ad3.psiR
      have : (-2 * (Real.pi : ℂ) * Complex.I * ((ζ * v : ℝ) : ℂ)) = ((-2 * Real.pi * (ζ * v) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, norm_mul, this, Complex.norm_real, Real.norm_of_nonneg (gau_nonneg ε ζ hε)]
    ring
  have b1 : ‖Ae Φ ε h v‖ ≤ B := by
    rw [GlobalTheory.CompanionTheory.Parseval.GaussRep.Ae_eq_integral_gau Φ ε h v hε hdet]
    have : ∀ ζ, ‖(gau ε ζ : ℂ) * Ad3.psiR (ζ * v) * gz Φ h ζ‖ ≤ gau ε ζ * B := by
      intro ζ
      rw [hnormI]
      refine mul_le_mul_of_nonneg_left ((hg ζ).trans ?_) (gau_nonneg ε ζ hε)
      have hi : ((1 + ‖dualF h ζ‖) ^ 2)⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        have : 0 ≤ ‖dualF h ζ‖ := norm_nonneg _
        nlinarith
      nlinarith
    refine (norm_integral_le_of_norm_le ((gau_integrable ε hε).mul_const B) (Filter.Eventually.of_forall this)).trans ?_
    rw [integral_mul_const, gau_integral ε hε, one_mul]
  have b2 : S ≠ 0 → ‖Ae Φ ε h v‖ ≤ 4 * K * B * (a / |l|) := by
    intro hS
    have hl0 : l ≠ 0 := div_ne_zero hS hm0.ne'
    have hwm : Measurable (wt a l) := by
      unfold wt
      fun_prop
    have hwi : Integrable (fun ζ => wt a l ζ * gau ε ζ) := by
      refine (gau_integrable ε hε).bdd_mul (c := 1) hwm.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => ?_)
      rw [Real.norm_of_nonneg (wt_nonneg _ _ _)]
      apply inv_le_one_of_one_le₀
      have : 0 ≤ |ζ - l| / a := by positivity
      nlinarith
    rw [GlobalTheory.CompanionTheory.Parseval.GaussRep.Ae_eq_integral_gau Φ ε h v hε hdet]
    have : ∀ ζ, ‖(gau ε ζ : ℂ) * Ad3.psiR (ζ * v) * gz Φ h ζ‖ ≤ (4 * B) * (wt a l ζ * gau ε ζ) := by
      intro ζ
      rw [hnormI]
      have g1 := GlobalTheory.CompanionTheory.Parseval.dualF_weight_le h ζ hdet
      have g2 : ‖gz Φ h ζ‖ ≤ B * (4 * wt a l ζ) :=
        (hg ζ).trans (mul_le_mul_of_nonneg_left g1 hB0)
      calc gau ε ζ * ‖gz Φ h ζ‖ ≤ gau ε ζ * (B * (4 * wt a l ζ)) :=
            mul_le_mul_of_nonneg_left g2 (gau_nonneg ε ζ hε)
        _ = _ := by ring
    refine (norm_integral_le_of_norm_le (hwi.const_mul (4 * B)) (Filter.Eventually.of_forall this)).trans ?_
    rw [integral_const_mul]
    have o := hC₂ ε a l hε ha0 hl0
    have o2 : ∫ ζ, wt a l ζ * gau ε ζ ≤ K * (a / |l|) :=
      o.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    calc 4 * B * ∫ ζ, wt a l ζ * gau ε ζ ≤ 4 * B * (K * (a / |l|)) :=
          mul_le_mul_of_nonneg_left o2 (by positivity)
      _ = _ := by ring
  have e1 : B = C₁ / P * D⁻¹ := by rw [hB]; ring
  have goal2 : C₁ * (1 + 4 * K) * ((max D (|S| / n))⁻¹ / P) = (C₁ / P) * (1 + 4 * K) * (max D (|S| / n))⁻¹ := by
    ring
  rw [goal2]
  have hQ : 0 ≤ C₁ / P := by positivity
  rcases le_total (|S| / n) D with hle | hle
  · rw [max_eq_left hle]
    calc ‖Ae Φ ε h v‖ ≤ C₁ / P * D⁻¹ := by rw [← e1]; exact b1
      _ ≤ _ := by
        have : 0 ≤ C₁ / P * D⁻¹ * (4 * K) := by positivity
        nlinarith
  · rw [max_eq_right hle]
    have hSpos : 0 < |S| / n := lt_of_lt_of_le hD0 hle
    have hS : S ≠ 0 := by
      intro h0; rw [h0, abs_zero, zero_div] at hSpos; exact lt_irrefl _ hSpos
    have hS' : |S| ≠ 0 := abs_ne_zero.2 hS
    have hal : a / |l| = D * (n / |S|) := by
      rw [ha, hl, abs_div, abs_of_pos hm0, ← hnn]
      field_simp
    have e2 : 4 * K * B * (a / |l|) = 4 * K * (C₁ / P) * (n / |S|) := by
      rw [hal, hB]; field_simp
    rw [inv_div]
    calc ‖Ae Φ ε h v‖ ≤ 4 * K * (C₁ / P) * (n / |S|) := by rw [← e2]; exact b2 hS
      _ ≤ _ := by
        have : 0 ≤ C₁ / P * (n / |S|) := by positivity
        nlinarith

end GlobalTheory.CompanionTheory.Parseval.Max
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodIntegrandMajorant
section
noncomputable section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.PerUInt

theorem inv_pow_le_phi_prod (h : Ad3.LR.M22) (N : ℕ) (hN : 8 ≤ N) :
    1 / (1 + ‖h‖) ^ N ≤ phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)) := by
  have entry : ∀ i j, 1 + |h i j| ≤ 1 + ‖h‖ := by
    intro i j
    have h1 : ‖h i j‖ ≤ ‖h i‖ := norm_le_pi_norm (h i) j
    have h2 : ‖h i‖ ≤ ‖h‖ := norm_le_pi_norm h i
    have h3 : |h i j| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using h1.trans h2
    linarith
  have ht : 1 ≤ 1 + ‖h‖ := by linarith [norm_nonneg h]
  have sq : ∀ i j, (1 + |h i j|) ^ 2 ≤ (1 + ‖h‖) ^ 2 := fun i j =>
    pow_le_pow_left₀ (by positivity) (entry i j) 2
  have hP : (1 + |h 0 0|) ^ 2 * (1 + |h 1 0|) ^ 2 * ((1 + |h 0 1|) ^ 2 * (1 + |h 1 1|) ^ 2) ≤
      (1 + ‖h‖) ^ N := by
    calc (1 + |h 0 0|) ^ 2 * (1 + |h 1 0|) ^ 2 * ((1 + |h 0 1|) ^ 2 * (1 + |h 1 1|) ^ 2)
        ≤ (1 + ‖h‖) ^ 2 * (1 + ‖h‖) ^ 2 * ((1 + ‖h‖) ^ 2 * (1 + ‖h‖) ^ 2) := by
          have a := sq 0 0
          have b := sq 1 0
          have c := sq 0 1
          have d := sq 1 1
          gcongr
      _ = (1 + ‖h‖) ^ 8 := by ring
      _ ≤ (1 + ‖h‖) ^ N := pow_le_pow_right₀ ht hN
  have hphi : phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)) =
      ((1 + |h 0 0|) ^ 2 * (1 + |h 1 0|) ^ 2 * ((1 + |h 0 1|) ^ 2 * (1 + |h 1 1|) ^ 2))⁻¹ := by
    simp only [phi, mul_inv]
  rw [hphi, one_div]
  exact inv_anti₀ (by positivity) hP

theorem kernel_exponents (k : ℕ) (σ Y c E : ℝ) (hY : 0 < Y) (hc : 0 < c) :
    (Y ^ ((2 * (k : ℝ) - 1) / 2) * E) * (Y * c) ^ (-(3 : ℝ) / 2) *
        ((c / 2) ^ ((1 : ℝ) / 2) / (Y * c)) ^ (σ - 1) =
      2 ^ ((1 - σ) / 2) * (Y ^ ((k : ℝ) - 1 - σ) * E * c ^ (-1 - σ / 2)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hw : 0 < (c / 2) ^ ((1 : ℝ) / 2) / (Y * c) := by positivity
  have hlog : Real.log ((c / 2) ^ ((1 : ℝ) / 2) / (Y * c)) =
      (Real.log c - Real.log 2) / 2 - (Real.log Y + Real.log c) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_rpow (by positivity),
      Real.log_div hc.ne' h2.ne', Real.log_mul hY.ne' hc.ne']
    ring
  rw [Real.rpow_def_of_pos hY, Real.rpow_def_of_pos (mul_pos hY hc), Real.rpow_def_of_pos hw,
    Real.rpow_def_of_pos h2, Real.rpow_def_of_pos hY, Real.rpow_def_of_pos hc, hlog,
    Real.log_mul hY.ne' hc.ne']
  have e : ∀ a b c' : ℝ, Real.exp a * E * Real.exp b * Real.exp c' =
      Real.exp (a + b + c') * E := by
    intro a b c'
    rw [Real.exp_add, Real.exp_add]
    ring
  have e' : ∀ a b c' : ℝ, Real.exp a * (Real.exp b * E * Real.exp c') =
      Real.exp (a + b + c') * E := by
    intro a b c'
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [e, e']
  congr 2
  ring

theorem norm_Wm_inv (k : ℕ) (h : Ad3.LR.M22) (hD : 0 < (Matrix.of h).det)
    (hc : 0 < h 0 0 ^ 2 + h 1 0 ^ 2) :
    ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ =
      ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) ^ ((2 * (k : ℝ) - 1) / 2) *
        Real.exp (-(2 * Real.pi * ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)))) := by
  obtain ⟨e0, e1⟩ := GlobalTheory.CompanionTheory.PrimalInt.inv_row h hD.ne'
  have hdet : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hone : Ad3.LR.C.d2 1 = 1 := by
    simp [Ad3.LR.C.d2, Matrix.one_fin_two]
  have hW := GlobalTheory.CompanionTheory.AbsWm.norm_Wm k (Matrix.of h)⁻¹ 1 (by
    rw [one_mul, hdet]
    exact inv_pos.2 hD)
  rw [hone, one_mul, one_mul] at hW
  have hNR : Complex.normSq (GlobalTheory.CompanionTheory.WmFE.jj (Matrix.of h)⁻¹) =
      (h 0 0 ^ 2 + h 1 0 ^ 2) / (Matrix.of h).det ^ 2 := by
    have : Complex.normSq (GlobalTheory.CompanionTheory.WmFE.jj (Matrix.of h)⁻¹) =
        ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 +
          ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 := by
      simp [GlobalTheory.CompanionTheory.WmFE.jj, Complex.normSq_apply]
      ring
    rw [this, e0, e1]
    field_simp
    ring
  rw [hW, hNR, hdet]
  generalize (Matrix.of h).det = D at hD
  generalize h 0 0 ^ 2 + h 1 0 ^ 2 = c at hc
  have hY : D⁻¹ = D / c * (c / D ^ 2) := by
    field_simp
  have hE : 2 * Real.pi * D⁻¹ / (c / D ^ 2) = 2 * Real.pi * (D / c) := by
    field_simp
  have hYp : 0 < D / c := by positivity
  have hNp : 0 < c / D ^ 2 := by positivity
  rw [hE]
  congr 1
  rw [hY, Real.mul_rpow hYp.le hNp.le, mul_assoc, ← Real.rpow_add hNp]
  simp

theorem pointwise_gamma_bound : ∀ (k : ℕ), 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 8 ≤ N →
    ∃ C : ℝ, ∀ h : Ad3.LR.M22, (Matrix.of h).det ≠ 0 →
    ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) * ‖Ad3.LR.B.eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N ≤
      C * (GlobalTheory.CompanionTheory.PerUInt.gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ (-1 - σ / 2) *
        (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 0) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 0) * (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 1) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 1)))) := by
  intro k _ σ _ h1 N hN
  refine ⟨2 ^ ((1 - σ) / 2), fun h hd => ?_⟩
  have hC : (0 : ℝ) ≤ 2 ^ ((1 - σ) / 2) := by positivity
  have hΦ : 0 ≤ phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)) :=
    mul_nonneg (mul_nonneg (phi_nonneg _) (phi_nonneg _)) (mul_nonneg (phi_nonneg _) (phi_nonneg _))
  have hc0 : 0 ≤ h 0 0 ^ 2 + h 1 0 ^ 2 := by positivity
  rcases lt_or_gt_of_ne hd with hneg | hD
  · have hdet : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    have hW : Ad3.LR.Wm k (Matrix.of h)⁻¹ = 0 := by
      have : ¬ 0 < ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det := by
        rw [hdet]
        exact not_lt.2 (inv_lt_zero.2 hneg).le
      unfold Ad3.LR.Wm
      exact if_neg this
    rw [hW]
    simp only [norm_zero, zero_mul, zero_div]
    exact mul_nonneg hC (mul_nonneg (mul_nonneg (gk_nonneg _ _ _) (Real.rpow_nonneg hc0 _)) hΦ)
  · have hc : 0 < h 0 0 ^ 2 + h 1 0 ^ 2 := by
      rcases hc0.lt_or_eq with hp | hz
      · exact hp
      · exfalso
        have ha : h 0 0 = 0 := by nlinarith [sq_nonneg (h 0 0), sq_nonneg (h 1 0)]
        have hb : h 1 0 = 0 := by nlinarith [sq_nonneg (h 0 0), sq_nonneg (h 1 0)]
        apply hd
        simp [Matrix.det_fin_two, ha, hb]
    obtain ⟨e0, e1⟩ := GlobalTheory.CompanionTheory.PrimalInt.inv_row h hd
    have b0 : |((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0| ≤ ‖Ad3.LR.B.eta h‖ := by
      simpa [Ad3.LR.B.eta] using norm_le_pi_norm (Ad3.LR.B.eta h) 0
    have b1 : |((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1| ≤ ‖Ad3.LR.B.eta h‖ := by
      simpa [Ad3.LR.B.eta] using norm_le_pi_norm (Ad3.LR.B.eta h) 1
    rw [e0, abs_div, abs_neg, abs_of_pos hD, div_le_iff₀ hD] at b0
    rw [e1, abs_div, abs_of_pos hD, div_le_iff₀ hD] at b1
    have hw : ((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det ≤
        ‖Ad3.LR.B.eta h‖ := by
      rw [div_le_iff₀ hD, ← Real.sqrt_eq_rpow]
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      have s0 : h 1 0 ^ 2 ≤ (‖Ad3.LR.B.eta h‖ * (Matrix.of h).det) ^ 2 := by
        rw [← sq_abs (h 1 0)]
        exact pow_le_pow_left₀ (abs_nonneg _) b0 2
      have s1 : h 0 0 ^ 2 ≤ (‖Ad3.LR.B.eta h‖ * (Matrix.of h).det) ^ 2 := by
        rw [← sq_abs (h 0 0)]
        exact pow_le_pow_left₀ (abs_nonneg _) b1 2
      linarith
    have hwpos : 0 < ((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det := by
      positivity
    have hE : ‖Ad3.LR.B.eta h‖ ^ (σ - 1) ≤
        (((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det) ^ (σ - 1) :=
      Real.rpow_le_rpow_of_nonpos hwpos hw (by linarith)
    have hdec := inv_pow_le_phi_prod h N hN
    have hYp : 0 < (Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2) := div_pos hD hc
    have hDY : (Matrix.of h).det =
        (Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2) * (h 0 0 ^ 2 + h 1 0 ^ 2) := by
      field_simp
    have hker := kernel_exponents k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2))
      (h 0 0 ^ 2 + h 1 0 ^ 2)
      (Real.exp (-(2 * Real.pi * ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2))))) hYp hc
    rw [← hDY] at hker
    have hgk : gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) =
        ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) ^ ((k : ℝ) - 1 - σ) *
          Real.exp (-(2 * Real.pi * ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)))) := by
      simp [gk, hYp]
    rw [abs_of_pos hD]
    calc ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * (Matrix.of h).det ^ (-(3 : ℝ) / 2) *
          ‖Ad3.LR.B.eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N
        = (‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * (Matrix.of h).det ^ (-(3 : ℝ) / 2) *
            ‖Ad3.LR.B.eta h‖ ^ (σ - 1)) * (1 / (1 + ‖h‖) ^ N) := by ring
      _ ≤ (‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * (Matrix.of h).det ^ (-(3 : ℝ) / 2) *
            (((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det) ^ (σ - 1)) *
            (phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hE (by positivity)) hdec (by positivity)
            (by positivity)
      _ = _ := by
          rw [norm_Wm_inv k h hD hc, hker, hgk]
          ring

end GlobalTheory.CompanionTheory.PerUInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseCocycleBimultiplicative
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_sigR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (z : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ z) = Algebra.trace R (R ⊗[F] E) z := by
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  let e : (R ⊗[F] E) ≃ₐ[R] (R ⊗[F] E) := Algebra.TensorProduct.congr AlgEquiv.refl s
  have h : sigR R σ z = e z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [sigR, e, s]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [h]
  exact Algebra.trace_eq_of_algEquiv e z

theorem hR_add_left (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hR_add_right (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

end Gen

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem trace_gram2_swap (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j) (b : HermR (Af F) σ n)
    (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J Y X)) =
      Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y)) := by
  rw [← trace_sigR (Af F) σ hσ]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, gram2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  have hb : sigR (Af F) σ ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) c a) = (b : Matrix _ _ _) a c := b.2 a c
  rw [hb, GlobalTheory.CompanionTheory.SiegelND.Coef.sigR_hR (Af F) σ hσ hJ]

theorem gramR_add (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    gramR (Af F) σ J (X + Y) = gramR (Af F) σ J X + gramR (Af F) σ J Y + gram2 σ J X Y + gram2 σ J Y X := by
  funext a c
  simp only [gramR, gram2, Pi.add_apply, Matrix.add_apply, hR_add_left, hR_add_right]
  abel

end Fin

theorem psiFin_add {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (u v : Af F) :
    psiFin F ψ (u + v) = psiFin F ψ u * psiFin F ψ v := by
  have h : pairA F 0 (u + v) = pairA F 0 u + pairA F 0 v := by
    have h0 : (0 : Ainf F) = 0 + 0 := (add_zero 0).symm
    exact congrArg (fun t => pairA F t (u + v)) h0
  simp only [psiFin]
  rw [h, AddChar.map_add_eq_mul]

theorem phaseB_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n)
    (X Y : Fin n → Fin M → Af F ⊗[F] E),
    phaseB σ J (psiFin F ψ) b (X + Y) =
      phaseB σ J (psiFin F ψ) b X * phaseB σ J (psiFin F ψ) b Y * pairB σ J (psiFin F ψ) b X Y := by
  intro F E _ _ _ _ _ σ hCM M J hJ n ψ _ b X Y
  have hsw := trace_gram2_swap σ (GlobalTheory.CompanionTheory.SiegelND.Coef.sig_invol hCM) hJ.1 b X Y
  have h2 : algebraMap F (Af F) (1 / 2) + algebraMap F (Af F) (1 / 2) = 1 := by
    rw [← map_add]
    norm_num
  simp only [phaseB, pairB]
  rw [← psiFin_add, ← psiFin_add]
  congr 1
  rw [gramR_add, mul_add, mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    map_add, map_add, map_add, hsw]
  linear_combination (Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y))) * h2

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd
end
end

