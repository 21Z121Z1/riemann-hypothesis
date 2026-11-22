import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0319
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMeasureEqSmulAddHaarLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeYDerivativeTermIntegralPolynomialDecay
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.TermDecay

theorem intZ_ibp (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) (a : ℤ) (b m : ℕ) (hab : 2 ≤ a + 2 * b) {y : ℝ}
    (hy : y ≠ 0) :
    2 * (Real.pi : ℂ) * I * ν * intZ σ ν a b m y =
      -(a : ℂ) * intZ σ ν (a + 1) b m y
        + 2 * (-σ - (b : ℂ)) * (intZ σ ν (a - 1) (b + 1) m y - I * intZ σ ν a (b + 1) (m + 1) y) := by
  have i0 := GlobalTheory.T.integrable_heckeTermDecayIntegrand σ hσ a b m hab y hy
  have i1 := GlobalTheory.T.integrable_heckeTermDecayIntegrand σ hσ (a + 1) b m (by omega) y hy
  have i2 := GlobalTheory.T.integrable_heckeTermDecayIntegrand σ hσ (a - 1) (b + 1) m (by push_cast; omega) y hy
  have i3 := GlobalTheory.T.integrable_heckeTermDecayIntegrand σ hσ a (b + 1) (m + 1) (by push_cast; omega) y hy
  have hd : deriv (qZ σ a b m y) = fun t => -(a : ℂ) * qZ σ (a + 1) b m y t
      + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t) := by
    funext t; exact (GlobalTheory.T.hasDerivAt_heckeTermDecayIntegrand σ a b m y hy t).deriv
  have hdiff : Differentiable ℝ (qZ σ a b m y) := fun t => (GlobalTheory.T.hasDerivAt_heckeTermDecayIntegrand σ a b m y hy t).differentiableAt
  have hi : MeasureTheory.Integrable (deriv (qZ σ a b m y)) := by
    rw [hd]; exact (i1.const_mul _).add ((i2.sub (i3.const_mul _)).const_mul _)
  have key := congrFun (Real.fourier_deriv i0 hdiff hi) ν
  rw [← intZ_eq_fourier, smul_eq_mul] at key
  rw [← key, hd, Real.fourier_real_eq_integral_exp_smul]
  unfold intZ
  set E : ℝ → ℂ := fun t => Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) with hE
  have hEc : Continuous E := by rw [hE]; fun_prop
  have hEn : ∀ t, ‖E t‖ = 1 := by
    intro t; rw [hE, Complex.norm_exp]; simp
  have e : ∀ (f : ℝ → ℂ), MeasureTheory.Integrable f → MeasureTheory.Integrable (fun t : ℝ => f t * E t) := by
    intro f hf
    refine hf.norm.mono' (hf.aestronglyMeasurable.mul hEc.aestronglyMeasurable) (MeasureTheory.ae_of_all _ fun t => ?_)
    rw [norm_mul, hEn, mul_one]
  have hpt : ∀ t : ℝ, Complex.exp (((-2 * Real.pi * t * ν : ℝ) : ℂ) * I) •
      (-(a : ℂ) * qZ σ (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t))
      = -(a : ℂ) * (qZ σ (a + 1) b m y t * E t) + 2 * (-σ - (b : ℂ)) *
        (qZ σ (a - 1) (b + 1) m y t * E t - I * (qZ σ a (b + 1) (m + 1) y t * E t)) := by
    intro t
    rw [smul_eq_mul, hE]
    have : (((-2 * Real.pi * t * ν : ℝ) : ℂ) * I) = -(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)) := by push_cast; ring
    rw [this]; ring
  simp_rw [hpt]
  have j1 : MeasureTheory.Integrable (fun v => -(a : ℂ) * (qZ σ (a + 1) b m y v * E v)) := (e _ i1).const_mul _
  have j2 : MeasureTheory.Integrable (fun v => qZ σ (a - 1) (b + 1) m y v * E v) := e _ i2
  have j3 : MeasureTheory.Integrable (fun v => I * (qZ σ a (b + 1) (m + 1) y v * E v)) := (e _ i3).const_mul _
  have j23 : MeasureTheory.Integrable (fun v => 2 * (-σ - (b : ℂ)) *
      (qZ σ (a - 1) (b + 1) m y v * E v - I * (qZ σ a (b + 1) (m + 1) y v * E v))) := (j2.sub j3).const_mul _
  rw [MeasureTheory.integral_add j1 j23, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub j2 j3, MeasureTheory.integral_const_mul]

end GlobalTheory.HeckeTwo.TermDecay

namespace GlobalTheory.HeckeTwo.TermDecay

theorem le_div_one_add_pow_succ_of_mul_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) (A B Y : ℝ) (hY : 0 ≤ Y) (hA : 0 ≤ A) (hB : 0 ≤ B) (q : ℝ)
    (h0 : q ≤ A * Y) (h1 : x * q ≤ B * Y / (1 + x) ^ N) :
    q ≤ (2 ^ (N + 1) * A + 2 * B) * Y / (1 + x) ^ (N + 1) := by
  have hp : 0 < (1 + x) ^ (N + 1) := by positivity
  rw [le_div_iff₀ hp]
  rcases le_or_gt x 1 with h | h
  · have h2 : (1 + x) ^ (N + 1) ≤ 2 ^ (N + 1) := pow_le_pow_left₀ (by linarith) (by linarith) _
    rcases le_or_gt q 0 with hq | hq
    · have : 0 ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by positivity
      nlinarith [hp]
    · calc q * (1 + x) ^ (N + 1) ≤ A * Y * 2 ^ (N + 1) := mul_le_mul h0 h2 hp.le (by positivity)
        _ ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by nlinarith [mul_nonneg hB hY]
  · have hpN : 0 < (1 + x) ^ N := by positivity
    have h1' : x * q * (1 + x) ^ N ≤ B * Y := by rwa [le_div_iff₀ hpN] at h1
    have hx2 : 1 + x ≤ 2 * x := by linarith
    rcases le_or_gt q 0 with hq | hq
    · have : 0 ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by positivity
      nlinarith [hp]
    · calc q * (1 + x) ^ (N + 1) = q * (1 + x) ^ N * (1 + x) := by ring
        _ ≤ q * (1 + x) ^ N * (2 * x) := by gcongr
        _ = 2 * (x * q * (1 + x) ^ N) := by ring
        _ ≤ 2 * (B * Y) := by linarith
        _ ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by nlinarith [mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (N + 1)) hA) hY]

theorem intZ_decay (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ halfPlane) (N : ℕ) :
    ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∃ C : ℝ, ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖intZ σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  induction N with
  | zero =>
    intro a b m hab
    obtain ⟨C, hC⟩ := GlobalTheory.T.norm_heckeTermDecayFourierIntegral_le K hK hKH a b m hab
    exact ⟨C, fun σ hσ ν y _ hy => by simpa using hC σ hσ ν y hy⟩
  | succ N ih =>
    intro a b m hab
    obtain ⟨C0, hC0⟩ := GlobalTheory.T.norm_heckeTermDecayFourierIntegral_le K hK hKH a b m hab
    obtain ⟨C1, hC1⟩ := ih (a + 1) b m (by omega)
    obtain ⟨C2, hC2⟩ := ih (a - 1) (b + 1) m (by push_cast; omega)
    obtain ⟨C3, hC3⟩ := ih a (b + 1) (m + 1) (by push_cast; omega)
    set B : ℝ := (|(a : ℝ)| * |C1| + 2 * (|R| + b) * (|C2| + |C3|)) / (2 * Real.pi) with hB
    refine ⟨2 ^ (N + 1) * |C0| + 2 * B, fun σ hσ ν y hν hy => ?_⟩
    set E : ℝ := (m : ℝ) + 1 - a - 2 * b - 2 * σ.re with hE
    have hyp : 0 < |y| := abs_pos.2 hy
    have hnp : 0 < |ν| := abs_pos.2 hν
    have hx : |ν * y| = |ν| * |y| := abs_mul ν y
    have hpN : 0 < (1 + |ν * y|) ^ N := by positivity
    have hB0 : 0 ≤ B := by rw [hB]; have := Real.pi_pos; positivity
    refine le_trans ?_ (le_of_eq (by ring : (2 ^ (N + 1) * |C0| + 2 * B) * |y| ^ E / (1 + |ν * y|) ^ (N + 1) =
      (2 ^ (N + 1) * |C0| + 2 * B) * |y| ^ E / (1 + |ν * y|) ^ (N + 1)))
    apply le_div_one_add_pow_succ_of_mul_le |ν * y| (abs_nonneg _) N |C0| B (|y| ^ E) (by positivity) (abs_nonneg _) hB0
    · exact (hC0 σ hσ ν y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    ·
      have hibp := intZ_ibp σ (hKH hσ) ν a b m hab hy
      have e1 := hC1 σ hσ ν y hν hy
      have e2 := hC2 σ hσ ν y hν hy
      have e3 := hC3 σ hσ ν y hν hy
      have hE1 : ((m : ℝ) + 1 - ((a + 1 : ℤ) : ℝ) - 2 * b - 2 * σ.re) = E - 1 := by rw [hE]; push_cast; ring
      have hE2 : ((m : ℝ) + 1 - ((a - 1 : ℤ) : ℝ) - 2 * ((b + 1 : ℕ) : ℝ) - 2 * σ.re) = E - 1 := by rw [hE]; push_cast; ring
      have hE3 : (((m + 1 : ℕ) : ℝ) + 1 - (a : ℝ) - 2 * ((b + 1 : ℕ) : ℝ) - 2 * σ.re) = E - 1 := by rw [hE]; push_cast; ring
      rw [hE1] at e1; rw [hE2] at e2; rw [hE3] at e3
      set X : ℝ := |y| ^ (E - 1) / (1 + |ν * y|) ^ N with hX
      have hX0 : 0 ≤ X := by positivity
      have hσb : ‖-σ - (b : ℂ)‖ ≤ |R| + b := by
        calc ‖-σ - (b : ℂ)‖ ≤ ‖σ‖ + ‖(b : ℂ)‖ := by rw [← norm_neg σ]; exact norm_sub_le _ _
          _ ≤ |R| + b := by rw [Complex.norm_natCast]; gcongr; exact (hR σ hσ).trans (le_abs_self R)
      have key : 2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖ ≤ (|(a : ℝ)| * |C1| + 2 * (|R| + b) * (|C2| + |C3|)) * X := by
        have hn : ‖2 * (Real.pi : ℂ) * I * ν * intZ σ ν a b m y‖ = 2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖ := by
          simp [norm_mul, Complex.norm_real, abs_of_pos Real.pi_pos]
        rw [← hn, hibp]
        have f1 : ‖intZ σ ν (a + 1) b m y‖ ≤ |C1| * X := by
          rw [hX, ← mul_div_assoc]; exact e1.trans (by gcongr; exact le_abs_self _)
        have f2 : ‖intZ σ ν (a - 1) (b + 1) m y‖ ≤ |C2| * X := by
          rw [hX, ← mul_div_assoc]; exact e2.trans (by gcongr; exact le_abs_self _)
        have f3 : ‖intZ σ ν a (b + 1) (m + 1) y‖ ≤ |C3| * X := by
          rw [hX, ← mul_div_assoc]; exact e3.trans (by gcongr; exact le_abs_self _)
        calc _ ≤ ‖-(a : ℂ) * intZ σ ν (a + 1) b m y‖ + ‖2 * (-σ - (b : ℂ)) *
              (intZ σ ν (a - 1) (b + 1) m y - I * intZ σ ν a (b + 1) (m + 1) y)‖ := norm_add_le _ _
          _ ≤ |(a : ℝ)| * (|C1| * X) + 2 * (|R| + b) * (|C2| * X + |C3| * X) := by
            rw [norm_mul, norm_mul, norm_neg, norm_mul]
            have ha : ‖(a : ℂ)‖ = |(a : ℝ)| := by rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
            rw [ha]
            have hs : ‖intZ σ ν (a - 1) (b + 1) m y - I * intZ σ ν a (b + 1) (m + 1) y‖ ≤ |C2| * X + |C3| * X := by
              refine (norm_sub_le _ _).trans (add_le_add f2 ?_)
              rw [norm_mul, Complex.norm_I, one_mul]; exact f3
            gcongr
            · simp
          _ = _ := by ring

      have hyE : |y| ^ (E - 1) = |y| ^ E / |y| := by rw [Real.rpow_sub_one hyp.ne']
      have h2p : 0 < 2 * Real.pi * |ν| := by have := Real.pi_pos; positivity
      rw [hx]
      have : |ν| * |y| * ‖intZ σ ν a b m y‖ = |y| / (2 * Real.pi) * (2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖) := by
        field_simp
      rw [this]
      calc |y| / (2 * Real.pi) * (2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖)
          ≤ |y| / (2 * Real.pi) * ((|(a : ℝ)| * |C1| + 2 * (|R| + b) * (|C2| + |C3|)) * X) := by gcongr
        _ = B * |y| ^ E / (1 + |ν| * |y|) ^ N := by
          rw [hB, hX, hyE, ← hx]; field_simp

end GlobalTheory.HeckeTwo.TermDecay

open GlobalTheory.HeckeTwo.TermDecay in

theorem GlobalTheory.HeckeTwo.TermDecay.intT_bound : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N := by
  intro K hK hKH a b m hab N
  obtain ⟨C, hC⟩ := intZ_decay K hK hKH N (a : ℤ) b m (by exact_mod_cast hab)
  refine ⟨C, fun σ hσ ν y hν hy => ?_⟩
  rw [intT_eq_intZ]
  have := hC σ hσ ν y hν hy
  simpa using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicPropertiesStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q), ∃ β : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F, (∀ x y, β x y = pr c Q x y) ∧ (∀ x y, β x y = β y x) ∧ (∀ y, (∀ x, β x y = 0) → y = 0) ∧ (∀ (x y : Matrix α ν E) (a : Matrix ν ν E), β (x * a) y = β x (y * (a.map c)ᵀ)) ∧ ∀ x y, β x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  first | exact @GlobalTheory.KSp.pr_alg | exact GlobalTheory.KSp.pr_alg | (intros; apply GlobalTheory.KSp.pr_alg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingDiagonalNormStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMatrixColumnPairing_diagonal_norm : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (u : Matrix α α E) (D' : α → F) (a : Matrix ν ν E) (D : ν → F), Q = u * diagonal (fun i => algebraMap F E (D' i)) * (u.map c)ᵀ → ∀ x : Matrix α ν E, 2⁻¹ * pr c Q x (x * (a * diagonal (fun j => algebraMap F E (D j)) * (a.map c)ᵀ)) = ∑ i, ∑ j, (2⁻¹ * D' i * D j) * Algebra.norm F ((uᵀ * x * a) i j) := by
  first | exact @GlobalTheory.KSp.pr_diag_norm | exact GlobalTheory.KSp.pr_diag_norm | (intros; apply GlobalTheory.KSp.pr_diag_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinNonconstantTermsHasSumStatement
section
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisenstein_nonconstant_terms_hasSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
  ∀ (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k →
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z) ∧
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z c)
      ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) * ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z c) := by
  first | exact @GlobalTheory.EisNonConst.nonconst_terms | exact GlobalTheory.EisNonConst.nonconst_terms | (intros; apply GlobalTheory.EisNonConst.nonconst_terms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousClassSubstitution
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

namespace GlobalTheory.EZ

theorem fc_succ_eq_delta (n : ℕ) (i : Fin (n + 2)) : fc (n + 1) n i = SimplexCategory.δ i := by
  ext j
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [fc, clampHom, faceFun, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min (n + 1) (if (j : ℕ) < i then (j : ℕ) else j + 1) = ((Fin.succAbove i j : Fin (n+2)) : ℕ)
  rcases lt_or_ge (j : ℕ) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp [h] <;> omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]
    simp [show ¬ (j : ℕ) < i by omega] <;> omega

theorem ev_map_dD_eq_diagCx_d {C : Type u} [Category.{v} C] [Preadditive C]
    (Y : SimplicialObject (SimplicialObject C)) (n : ℕ) :
    (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := by
  refine Eq.trans ?_ (AlternatingFaceMapComplex.obj_d_eq (diag.obj Y) n).symm
  rw [dD, if_pos rfl, Functor.map_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Functor.map_zsmul, ev_map_bop, fc_succ_eq_delta]
  rfl

end GlobalTheory.EZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCochainsHomologyAddEquiv
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.HomogCochains

open GroundTheory.ProfCoh groupCohomology

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Rep.{0} k G} [IsDiscreteRep M] {C : CosimplicialObject AddCommGrpCat.{1}}
  {e : ∀ m : ℕ, C.obj ⦋m⦌ →+ ((Fin (m + 1) → G) → M)}

theorem neg_one_pow_smul_eq (m : ℕ) (x : M) : ((-1 : k) ^ m) • x = ((-1 : ℤ) ^ m) • x := by
  rw [← Int.cast_smul_eq_zsmul k]
  simp

section
variable (he : ∀ m, Function.Injective (e m))
  (hr : ∀ m (φ : (Fin (m + 1) → G) → M), (∃ c, e m c = φ) ↔
    IsLocallyConstant φ ∧ ∀ (τ : G) (σ : Fin (m + 1) → G), φ (fun i => τ * σ i) = M.ρ τ (φ σ))
  (hd : ∀ m (i : Fin (m + 2)) (c : C.obj ⦋m⦌) (σ : Fin (m + 2) → G),
    e (m + 1) (C.δ i c) σ = e m c (σ ∘ i.succAbove))

include hr in
theorem isLocallyConstant_e (m : ℕ) (c : C.obj ⦋m⦌) : IsLocallyConstant (e m c) :=
  ((hr m (e m c)).1 ⟨c, rfl⟩).1

include hr in
theorem e_mul (m : ℕ) (c : C.obj ⦋m⦌) (τ : G) (σ : Fin (m + 1) → G) :
    e m c (fun i => τ * σ i) = M.ρ τ (e m c σ) :=
  ((hr m (e m c)).1 ⟨c, rfl⟩).2 τ σ

def toInh (m : ℕ) : C.obj ⦋m⦌ →+ locallyConstantCochains M m where
  toFun c := ⟨fun g => e m c (Fin.partialProd g),
    (isLocallyConstant_e hr m c).comp_continuous (continuous_partialProd m)⟩
  map_zero' := by ext g; simp
  map_add' a b := by ext g; simp

theorem toInh_apply (m : ℕ) (c : C.obj ⦋m⦌) (g : Fin m → G) :
    ((toInh hr m c : locallyConstantCochains M m) : (Fin m → G) → M) g = e m c (Fin.partialProd g) :=
  rfl

include he in
theorem toInh_bijective (m : ℕ) : Function.Bijective (toInh hr m) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    apply he m
    rw [map_zero]
    funext σ
    have h0 : ∀ g, e m c (Fin.partialProd g) = 0 := fun g => by
      have := congrArg (fun f : locallyConstantCochains M m => (f : (Fin m → G) → M) g) hc
      simpa [toInh_apply] using this
    have hσ : σ = fun i => σ 0 * Fin.partialProd (fun j => (σ (Fin.castSucc j))⁻¹ * σ j.succ) i := by
      have := Fin.partialProd_left_inv σ
      funext i
      conv_lhs => rw [← this]
      rfl
    rw [hσ, e_mul hr, h0, map_zero]
    rfl
  · intro φ
    let F : (Fin (m + 1) → G) → M := fun x => M.ρ (x 0) (φ.1 fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)
    have hF : IsLocallyConstant F :=
      isLocallyConstant_ρ_apply M (continuous_apply 0)
        (φ.2.comp_continuous (continuous_pi fun _ =>
          ((continuous_apply _).inv).mul (continuous_apply _)))
    have hFm : ∀ (τ : G) (σ : Fin (m + 1) → G), F (fun i => τ * σ i) = M.ρ τ (F σ) := by
      intro τ σ
      simp only [F, mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul]
      rfl
    obtain ⟨c, hc⟩ := (hr m F).2 ⟨hF, hFm⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    funext g
    rw [toInh_apply, hc]
    simp only [F, Fin.partialProd_zero, Fin.partialProd_right_inv, map_one]
    rfl

theorem sum_hom_apply {X Y : AddCommGrpCat.{1}} {ι : Type} (s : Finset ι) (f : ι → (X ⟶ Y)) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]

theorem zsmul_hom_apply {X Y : AddCommGrpCat.{1}} (n : ℤ) (f : X ⟶ Y) (x : X) :
    (n • f) x = n • f x := by
  change (n • f).hom x = _
  rw [AddCommGrpCat.hom_zsmul]
  rfl

include hd hr in
theorem toInh_d (n : ℕ) (c : C.obj ⦋n⦌) :
    toInh hr (n + 1) ((AlgebraicTopology.AlternatingCofaceMapComplex.objD C n) c) =
      (dLocallyConstant M n).hom (toInh hr n c) := by
  apply Subtype.ext
  funext g
  rw [toInh_apply, dLocallyConstant_hom_apply, inhomogeneousCochains.d_hom_apply]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, sum_hom_apply, zsmul_hom_apply,
    map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply, hd]
  rw [Fin.sum_univ_succ]
  congr 1
  · have : (Fin.partialProd g ∘ (0 : Fin (n + 2)).succAbove) =
        fun j => g 0 * Fin.partialProd (Fin.tail g) j := by
      funext j
      simp only [Function.comp_apply, Fin.succAbove_zero]
      exact Fin.partialProd_succ' g j
    rw [this, e_mul hr, Fin.val_zero, pow_zero, one_smul, toInh_apply]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [toInh_apply, Fin.partialProd_contractNth, Fin.val_succ, neg_one_pow_smul_eq]

abbrev upF (k : Type) [CommRing k] : ModuleCat.{0} k ⥤ AddCommGrpCat.{1} :=
  forget₂ (ModuleCat.{0} k) AddCommGrpCat.{0} ⋙ AddCommGrpCat.uliftFunctor.{1, 0}

theorem alt_d (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD C n := by
  simp [AlgebraicTopology.alternatingCofaceMapComplex, AlgebraicTopology.AlternatingCofaceMapComplex.obj]

include he hr hd in

noncomputable def complexIso :
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C ≅
      ((upF k).mapHomologicalComplex _).obj (cochainsComplex M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (((AddEquiv.ofBijective (toInh hr n) (toInh_bijective he hr n)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso :
        (C.obj ⦋n⦌ : AddCommGrpCat.{1}) ≅ (upF k).obj (ModuleCat.of k (locallyConstantCochains M n))))
    (by
      rintro i j (rfl : i + 1 = j)
      rw [alt_d, Functor.mapHomologicalComplex_obj_d, cochainsComplex_d]
      ext c
      apply ULift.ext
      exact (toInh_d hr hd i c).symm)

end

end GlobalTheory.HomogCochains

open GlobalTheory.HomogCochains in
theorem GlobalTheory.homogeneousCochains_homology_addEquiv : ∀ (k : Type) [CommRing k] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Rep.{0} k G) [GroundTheory.ProfCoh.IsDiscreteRep M] (C : CosimplicialObject AddCommGrpCat.{1}) (e : ∀ m : ℕ, C.obj ⦋m⦌ →+ ((Fin (m + 1) → G) → M)), (∀ m, Function.Injective (e m)) → (∀ m (φ : (Fin (m + 1) → G) → M), (∃ c, e m c = φ) ↔ IsLocallyConstant φ ∧ ∀ (τ : G) (σ : Fin (m + 1) → G), φ (fun i => τ * σ i) = M.ρ τ (φ σ)) → (∀ m (i : Fin (m + 2)) (c : C.obj ⦋m⦌) (σ : Fin (m + 2) → G), e (m + 1) (C.δ i c) σ = e m c (σ ∘ i.succAbove)) → ∀ n : ℕ, Nonempty (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C).homology n ≃+ GroundTheory.ProfCoh.cohomology M n) := by
  intro k _ G _ _ _ M _ C e he hr hd n
  let i1 := (HomologicalComplex.homologyFunctor AddCommGrpCat.{1} _ n).mapIso (complexIso he hr hd)
  let i2 : (((upF k).mapHomologicalComplex _).obj (GroundTheory.ProfCoh.cochainsComplex M)).homology n ≅
      (upF k).obj ((GroundTheory.ProfCoh.cochainsComplex M).homology n) :=
    ((GroundTheory.ProfCoh.cochainsComplex M).sc n).mapHomologyIso (upF k)
  exact ⟨(i1 ≪≫ i2).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMeasureEqSmulAddHaarLocalFieldStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousMeasure_eq_smul_addHaar_localField : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [IsFiniteMeasureOnCompacts n], n {0} = 0 → (∀ u : Fˣ, n.map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n) → ∃ r : NNReal, n = r • lam := by
  first | exact @GlobalTheory.KSp.Homog.eq_smul_haar_of_homog | exact GlobalTheory.KSp.Homog.eq_smul_haar_of_homog | (intros; apply GlobalTheory.KSp.Homog.eq_smul_haar_of_homog <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfTermwiseBiject
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.LevelCx

open GlobalTheory.ColFilt

theorem zcomp_coe {C : Type*} [Category C] [Preadditive C] {K L M : CochainComplex C ℤ} {m n k : ℤ}
    (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) : (zcomp a b h).1 = a.1.comp b.1 h := rfl

theorem ofHom_coe {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (Cocycle.ofHom f).1 = Cochain.ofHom f := rfl

theorem main : ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ n, Injective (I.X n)) →
    ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
    (∀ p n, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I n)) →
    ∀ n, Function.Bijective (cpull g I n) := by
  intro R _ I _ _ K L _ _ g hg
  have hb1 : ∀ p n' m (h : 0 + n' = m), Function.Bijective
      (cpre (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p))) I n' m h) := by
    intro p n' m h
    obtain rfl : n' = m := by omega
    exact hg p n'
  let Φ : ∀ n, (∀ _ : Unit, Cochain L I (n - 0)) →+ Cochain K I n := fun n =>
    AddMonoidHom.mk' (fun α => (Cochain.ofHom g).comp (α ()) (by omega))
      (fun α β => Cochain.comp_add _ _ _ _)
  have hΦ0 : ∀ n (α : ∀ _ : Unit, Cochain L I (n - 0)), Φ n α = (Cochain.ofHom g).comp (α ()) (by omega) := fun _ _ => rfl
  have hΦ : ∀ n (α : ∀ _ : Unit, Cochain L I (n - 0)) (t q : ℤ) (hq : t + n = q),
      (Φ n α).v t q hq = g.f t ≫ (α ()).v t q (by omega) := by
    intro n α t q hq
    rw [hΦ0, Cochain.comp_v _ _ _ t t q (add_zero t) (by omega), Cochain.ofHom_v]
  have key : ∀ n' n (h : 0 + n' = n), Function.Bijective (cpre (Cocycle.ofHom g) I n' n h) := by
    intro n' n h
    obtain rfl : n' = n - 0 := by omega
    have := bijective_of_columns (isColumns_terms L) (isColumns_terms K) (fun _ : Unit => I) I (fun _ => 0) Φ
      (fun n m hnm α => by
        rw [hΦ0, hΦ0, δ_comp (Cochain.ofHom g) (α ()) _ 1 (m - 0) m hnm (zero_add 1) (by omega),
          δ_ofHom, Cochain.zero_comp, smul_zero, add_zero])
      (fun p n α hα => by
        show ∀ (c k t : ℤ) (h : c + k = t) (q : ℤ) (hq : t + n = q), p < c → ιTerm K c k t h ≫ (Φ n α).v t q hq = 0
        intro c k t h q hq hc
        by_cases hk : k = 0
        · subst hk
          obtain rfl : c = t := by omega
          have h0 := eq_zero_of_ιTerm (hα () c 0 c h q (by omega) hc)
          rw [hΦ, h0, comp_zero, comp_zero]
        · rw [ιTerm_ne _ _ _ _ _ hk, zero_comp])
      (fun p _ => ⟨fun m x => cpre (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p))) I (m - 0) m
          (by omega) (x ()),
        fun m => (hb1 p (m - 0) m (by omega)).comp (Equiv.funUnique Unit _).bijective,
        fun n m h α _ a b ha hb => by
          refine congrArg CohomologyClass.mk (Cocycle.ext (Cochain.ext _ _ fun k q hq => ?_))
          rw [zcomp_coe, ofHom_coe, Cochain.comp_v _ _ _ k k q (add_zero k) (by omega), Cochain.ofHom_v, ha (), hb]
          by_cases hk : k = 0
          · subst hk
            rw [restr_v _ _ p _ _ _ _ 0 p q (add_zero p) _ (by omega), restr_v _ _ p _ _ _ _ 0 p q (add_zero p) _ (by omega),
              hΦ, ιTerm_zero, ιTerm_zero,
              show ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)).f 0 =
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p)).hom ≫ g.f p ≫
                  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (L.X p)).inv from
                HomologicalComplex.single_map_f_self _ _ _]
            exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _))))
          · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X p) k hk).eq_of_src _ _⟩)
      n (fun x => cpre (Cocycle.ofHom g) I (n - 0) n h (x ()))
      (fun a b hb => congrArg CohomologyClass.mk (Cocycle.ext (by rw [zcomp_coe, hb]; rfl)))
    exact this.comp (Equiv.funUnique Unit _).symm.bijective
  intro n
  exact key n n (zero_add n)

end GlobalTheory.LevelCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InCellIffDetNeZeroStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inCell_iff_det_lower_left_block_ne_zero : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)), InCell c g ↔ ((mat c g).toBlocks₂₁).det ≠ 0 := by
  first | exact @GlobalTheory.KSp.inCell_iff_det_ne_zero | exact GlobalTheory.KSp.inCell_iff_det_ne_zero | (intros; apply GlobalTheory.KSp.inCell_iff_det_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducibleStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_scalar_irreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M := by
  first | exact @GlobalTheory.RankFibre.indScal_irreducible | exact GlobalTheory.RankFibre.indScal_irreducible | (intros; apply GlobalTheory.RankFibre.indScal_irreducible <;> assumption)
end

