import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def ConeIntegralMass.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      coneIntegral h W e (fun _ => 1) = δ

def ChowFormBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (σ : K →+* ℂ),
    IsProjPrime I → IsChowForm I k f →
      (∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, IsProjPrime W) ∧
        IsChowFormCycle (fundCycle (I.map (MvPolynomial.map σ))) k (MvPolynomial.map σ f)

def ChowHeightCharacterised.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (H : ArchData K n)
    (J : Ideal (MvPolynomial (Fin n) K) → ℝ),
    (∀ (e δ : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K)
        (u : Fin n → 𝓞 K),
      IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f →
      linForm (fun j => (u j : K)) ∉ I →
        J I = (∑ W ∈ (divCycle I fun j => (u j : K)).support,
                ((divCycle I fun j => (u j : K)) W : ℝ) * J W) +
          (1 / Module.finrank ℚ K : ℝ) *
            (vertTerm I (e + 1) u -
              ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
                (fsLog (H.normAt σ) fun j => σ (u j)))) →
    ∀ (e δ : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K),
      IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f → J I = chowHt H (e + 1) δ f

theorem ConeIntegralMass.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℂ) :=
  ⟨isProjPrime_point ℂ, isChowForm_point ℂ, isMultiHomog_point ℂ⟩

theorem ChowFormBaseChange.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 (X (0, 0)) :=
  ⟨isProjPrime_point ℚ, isChowForm_point ℚ⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramHess
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open scoped InnerProductSpace
open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem ChartGram.hasFDerivAt_re_inner {u w : E → F} {y : E} {u' w' : E →L[ℝ] F}
    (hu : HasFDerivAt u u' y) (hw : HasFDerivAt w w' y) :
    HasFDerivAt (fun y' => (⟪u y', w y'⟫_ℂ).re)
      (Complex.reCLM.comp ((fderivInnerCLM ℂ (u y, w y)).comp (u'.prod w'))) y :=
  Complex.reCLM.hasFDerivAt.comp y (HasFDerivAt.inner ℂ hu hw)

theorem ChartGram.re_inner_self_pos {x : F} (h0 : x ≠ 0) : 0 < (⟪x, x⟫_ℂ).re := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) x
  have h' : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := h
  rw [h']; positivity

theorem ChartGram.re_inner_comm (x z : F) : (⟪x, z⟫_ℂ).re = (⟪z, x⟫_ℂ).re := by
  rw [← inner_conj_symm x z, Complex.conj_re]

theorem ChartGram.fderiv_half_log_apply {u : E → F} {y : E}
    (hu : DifferentiableAt ℂ u y) (h0 : u y ≠ 0) (b : E) :
    fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y b =
      (⟪u y, fderiv ℂ u y b⟫_ℂ).re * ((⟪u y, u y⟫_ℂ).re)⁻¹ := by
  have h1 : HasFDerivAt u ((fderiv ℂ u y).restrictScalars ℝ) y := hu.hasFDerivAt.restrictScalars ℝ
  have h4 := HasFDerivAt.const_mul (HasFDerivAt.log (ChartGram.hasFDerivAt_re_inner h1 h1)
    (ChartGram.re_inner_self_pos h0).ne') 2⁻¹
  rw [h4.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, ContinuousLinearMap.coe_restrictScalars',
    Complex.reCLM_apply, Complex.add_re, smul_eq_mul]
  rw [ChartGram.re_inner_comm (fderiv ℂ u y b)]
  ring

theorem ChartGram.hessian_half_log_apply [CompleteSpace F] {u : E → F} {y : E}
    (hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y') (h0 : u y ≠ 0) (a b : E) :
    fderiv ℝ (fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re)) y a b =
      ((⟪u y, fderiv ℂ (fderiv ℂ u) y a b⟫_ℂ).re + (⟪fderiv ℂ u y a, fderiv ℂ u y b⟫_ℂ).re) *
          ((⟪u y, u y⟫_ℂ).re)⁻¹ -
        (⟪u y, fderiv ℂ u y b⟫_ℂ).re * (2 * (⟪u y, fderiv ℂ u y a⟫_ℂ).re) *
          (((⟪u y, u y⟫_ℂ).re) ^ 2)⁻¹ := by
  set ψ : E → ℝ := fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re with hψ
  have hy : AnalyticAt ℂ u y := hu.self_of_nhds
  have hN := ChartGram.re_inner_self_pos h0

  have hc : ContDiffAt ℝ 2 ψ y := by
    have hu2 : ContDiffAt ℝ 2 u y := (hy.contDiffAt (n := 2)).restrict_scalars ℝ
    have hi : ContDiffAt ℝ 2 (fun y' => (⟪u y', u y'⟫_ℂ).re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y (ContDiffAt.inner ℂ hu2 hu2)
    exact contDiffAt_const.mul (hi.log hN.ne')
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ ψ) y a b = fderiv ℝ (fun y' => fderiv ℝ ψ y' b) y a := by
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  rw [h2]

  have hev : (fun y' => fderiv ℝ ψ y' b) =ᶠ[𝓝 y]
      fun y' => (⟪u y', fderiv ℂ u y' b⟫_ℂ).re * ((⟪u y', u y'⟫_ℂ).re)⁻¹ := by
    filter_upwards [hu, hy.continuousAt.eventually_ne h0] with y' h1 h2
    exact ChartGram.fderiv_half_log_apply h1.differentiableAt h2 b
  rw [hev.fderiv_eq]
  have hu1 : HasFDerivAt u ((fderiv ℂ u y).restrictScalars ℝ) y :=
    hy.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hW : HasFDerivAt (fun y' => fderiv ℂ u y' b)
      (((fderiv ℂ u y).comp (0 : E →L[ℂ] E) + (fderiv ℂ (fderiv ℂ u) y).flip b).restrictScalars ℝ) y :=
    (hy.fderiv.differentiableAt.hasFDerivAt.clm_apply (hasFDerivAt_const b y)).restrictScalars ℝ
  have hI := (hasDerivAt_inv hN.ne').comp_hasFDerivAt y (ChartGram.hasFDerivAt_re_inner hu1 hu1)
  have hg := HasFDerivAt.mul (ChartGram.hasFDerivAt_re_inner hu1 hW) hI
  have hg' : HasFDerivAt (fun y' => (⟪u y', fderiv ℂ u y' b⟫_ℂ).re * ((⟪u y', u y'⟫_ℂ).re)⁻¹) _ y := hg
  rw [hg'.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', Complex.reCLM_apply, Complex.add_re, smul_eq_mul,
    zero_apply, map_zero, ContinuousLinearMap.flip_apply,
    zero_add, Function.comp_apply]
  rw [ChartGram.re_inner_comm (fderiv ℂ u y a) (u y)]
  ring

open ReciprocityTheory.ChartRestriction.G.Geo (cxHessian) in

theorem ChartGram.cxHessian_half_log [CompleteSpace F] {D : ℕ} {u : (Fin D → ℂ) → F}
    {y : Fin D → ℂ} (hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y') (h0 : u y ≠ 0) (i j : Fin D) :
    cxHessian (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y i j =
      (⟪u y, u y⟫_ℂ * ⟪fderiv ℂ u y (Pi.single j 1), fderiv ℂ u y (Pi.single i 1)⟫_ℂ -
          ⟪u y, fderiv ℂ u y (Pi.single i 1)⟫_ℂ * ⟪fderiv ℂ u y (Pi.single j 1), u y⟫_ℂ) /
        (2 * ⟪u y, u y⟫_ℂ ^ 2) := by
  have hN := ChartGram.re_inner_self_pos h0
  have hNc : ⟪u y, u y⟫_ℂ = ((⟪u y, u y⟫_ℂ).re : ℂ) := by
    rw [← inner_self_ofReal_re (𝕜 := ℂ)]; rfl
  unfold cxHessian
  simp only [ChartGram.hessian_half_log_apply hu h0, map_smul, smul_apply,
    inner_smul_right, inner_smul_left, Complex.conj_I]
  rw [← inner_conj_symm (fderiv ℂ u y (Pi.single j 1)) (u y),
    ← inner_conj_symm (fderiv ℂ u y (Pi.single j 1)) (fderiv ℂ u y (Pi.single i 1)), hNc]
  generalize ⟪u y, fderiv ℂ (fderiv ℂ u) y (Pi.single i 1) (Pi.single j 1)⟫_ℂ = Q
  generalize ⟪fderiv ℂ u y (Pi.single i 1), fderiv ℂ u y (Pi.single j 1)⟫_ℂ = P
  generalize ⟪u y, fderiv ℂ u y (Pi.single i 1)⟫_ℂ = p
  generalize ⟪u y, fderiv ℂ u y (Pi.single j 1)⟫_ℂ = q
  generalize (⟪u y, u y⟫_ℂ).re = N at hN ⊢
  have hN' : N ≠ 0 := hN.ne'
  apply Complex.ext <;>
    simp [sq, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    field_simp <;> ring

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramPolar
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Finset
open ReciprocityTheory.ChartRestriction.G.Geo (mixedDisc)

theorem ChartGram.sum_neg_one_pow_card_pow (D : ℕ) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D = D.factorial := by
  have h1 := fwdDiff_iter_eq_sum_shift (h := (1 : ℂ)) (fun r : ℂ => r ^ D) D 0
  rw [fwdDiff_iter_eq_factorial] at h1
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (f := fun m => (-1 : ℂ) ^ (D - m) * (m : ℂ) ^ D)]
  simp only [Finset.card_univ, Fintype.card_fin]
  have h2 : ((D.factorial : ℂ → ℂ) 0) = (D.factorial : ℂ) := rfl
  rw [← h2, h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [zsmul_eq_mul, nsmul_eq_mul]
  ring

theorem ChartGram.mixedDisc_const {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun _ => A) = A.det := by
  unfold mixedDisc
  have h : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ _k ∈ S, A).det =
      ((-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D) * A.det := by
    intro S
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, Matrix.det_smul, Fintype.card_fin]
    ring
  simp_rw [h, ← Finset.sum_mul, ChartGram.sum_neg_one_pow_card_pow]
  have : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  field_simp

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def BaseChangeAvoid.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (u : Fin n → K) (σ : K →+* ℂ), IsProjPrime I → linForm u ∉ I →
      ∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, linForm (fun j => σ (u j)) ∉ W

def coneBall {n : ℕ} (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {y | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0}

def ConeBallFinite.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) < ⊤

def ConeFsLogIntegrable.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      IntegrableOn (fun y => fsLog h u (h.pointOf y)) (coneBall h W)
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))

def ConeHyperplaneNull.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) = 0

def ConeLogBound.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f → linForm u ∉ W →
      coneIntegral h W e (fsLog h u) ≤ δ * Real.log (h.norm u)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjPrimeHasPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)), IsProjPrime W →
    ∃ x : Fin n → AlgebraicClosure F, x ≠ 0 ∧ ∀ q ∈ W, aeval x q = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace LineChowForm

variable {F : Type*} [Field F]

variable {F : Type*} [Field F]

def D2 : MvPolynomial (Fin 2 × Fin 2) F := X (0,0) * X (1,1) - X (0,1) * X (1,0)

def substZeroZeroZero : MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] MvPolynomial (Fin 2 × Fin 2) F :=
  aeval (fun ij => if ij = ((0 : Fin 2),(0 : Fin 2)) then 0 else X ij)

def substZeroOneOne : MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] MvPolynomial (Fin 2 × Fin 2) F :=
  aeval (fun ij => if ij = ((1 : Fin 2),(1 : Fin 2)) then 0 else X ij)

lemma X_dvd_of_substZeroZeroZero_eq_zero (q : MvPolynomial (Fin 2 × Fin 2) F) (h : substZeroZeroZero q = 0) : X (0,0) ∣ q := by
  have key : ∀ q : MvPolynomial (Fin 2 × Fin 2) F, X (0,0) ∣ q - substZeroZeroZero q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp [substZeroZeroZero]
    | add p q hp hq =>
      have e : p + q - substZeroZeroZero (p+q) = (p - substZeroZeroZero p) + (q - substZeroZeroZero q) := by
        simp only [map_add]; ring
      rw [e]; exact dvd_add hp hq
    | mul_X p i hp =>
      have e : p * X i - substZeroZeroZero (p * X i) =
          (p - substZeroZeroZero p) * X i + substZeroZeroZero p * (X i - substZeroZeroZero (X i)) := by
        simp only [map_mul]; ring
      rw [e]
      refine dvd_add (hp.mul_right _) (Dvd.dvd.mul_left ?_ _)
      by_cases hi : i = (0,0)
      · subst hi; simp [substZeroZeroZero]
      · simp [substZeroZeroZero, hi]
  simpa [h] using key q

lemma substZeroOneOne_X_zero_zero : substZeroOneOne (X (0,0) : MvPolynomial (Fin 2 × Fin 2) F) = X (0,0) := by
  simp [substZeroOneOne]

lemma substZeroOneOne_X_of_ne (i : Fin 2 × Fin 2) (hi : i ≠ (1,1)) :
    substZeroOneOne (X i : MvPolynomial (Fin 2 × Fin 2) F) = X i := by
  simp [substZeroOneOne, hi]

lemma pseudo (g : MvPolynomial (Fin 2 × Fin 2) F) :
    ∃ (N : ℕ) (q r : MvPolynomial (Fin 2 × Fin 2) F),
      X (0,0) ^ N * g = q * D2 + r ∧ substZeroOneOne r = r := by
  induction g using MvPolynomial.induction_on with
  | C a => exact ⟨0, 0, C a, by simp, by simp [substZeroOneOne]⟩
  | add p q hp hq =>
    obtain ⟨N, a, r, h1, h2⟩ := hp
    obtain ⟨M, b, s, h3, h4⟩ := hq
    refine ⟨N + M, X (0,0) ^ M * a + X (0,0) ^ N * b, X (0,0) ^ M * r + X (0,0) ^ N * s, ?_, ?_⟩
    · have : X (0,0) ^ (N + M) * (p + q) = X (0,0) ^ M * (X (0,0) ^ N * p) + X (0,0) ^ N * (X (0,0) ^ M * q) := by
        ring
      rw [this, h1, h3]; ring
    · simp only [map_add, map_mul, map_pow, substZeroOneOne_X_zero_zero, h2, h4]
  | mul_X p i hp =>
    obtain ⟨N, a, r, h1, h2⟩ := hp
    by_cases hi : i = (1,1)
    · subst hi
      refine ⟨N + 1, X (0,0) * X (1,1) * a + r, r * (X (0,1) * X (1,0)), ?_, ?_⟩
      · have : X (0,0) ^ (N + 1) * (p * X (1,1)) = (X (0,0) ^ N * p) * (X (0,0) * X (1,1)) := by ring
        rw [this, h1]; simp only [D2]; ring
      · rw [map_mul, map_mul, h2, substZeroOneOne_X_of_ne _ (by decide), substZeroOneOne_X_of_ne _ (by decide)]
    · refine ⟨N, a * X i, r * X i, ?_, ?_⟩
      · have : X (0,0) ^ N * (p * X i) = (X (0,0) ^ N * p) * X i := by ring
        rw [this, h1]; ring
      · rw [map_mul, h2, substZeroOneOne_X_of_ne _ hi]

lemma cancel1 (h q : MvPolynomial (Fin 2 × Fin 2) F) (e : X (0,0) * h = D2 * q) : D2 ∣ h := by
  have e0 := congrArg substZeroZeroZero e
  have hz : substZeroZeroZero (X (0,0) : MvPolynomial (Fin 2 × Fin 2) F) = 0 := by simp [substZeroZeroZero]
  have hD : substZeroZeroZero (D2 : MvPolynomial (Fin 2 × Fin 2) F) = -(X (0,1) * X (1,0)) := by
    simp [substZeroZeroZero, D2]
  rw [map_mul, map_mul, hz, hD, zero_mul] at e0
  have hne : -(X (0,1) * X (1,0)) ≠ (0 : MvPolynomial (Fin 2 × Fin 2) F) :=
    neg_ne_zero.mpr (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
  have hq : substZeroZeroZero q = 0 := by
    rcases mul_eq_zero.mp e0.symm with h' | h'
    · exact absurd h' hne
    · exact h'
  obtain ⟨q', rfl⟩ := X_dvd_of_substZeroZeroZero_eq_zero q hq
  refine ⟨q', mul_left_cancel₀ (X_ne_zero ((0 : Fin 2),(0 : Fin 2))) ?_⟩
  rw [e]; ring

lemma cancelN (N : ℕ) (g : MvPolynomial (Fin 2 × Fin 2) F) (h : D2 ∣ X (0,0) ^ N * g) : D2 ∣ g := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    obtain ⟨q, hq⟩ := h
    exact ih (cancel1 _ q (by rw [← hq]; ring))

lemma aeval_substZeroOneOne {A : Type*} [CommRing A] [Algebra F A] (w : Fin 2 × Fin 2 → A)
    (r : MvPolynomial (Fin 2 × Fin 2) F) :
    aeval w (substZeroOneOne r) = aeval (Function.update w (1,1) 0) r := by
  have : ((aeval w).comp substZeroOneOne : MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] A) =
      aeval (Function.update w (1,1) 0) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = (1,1)
    · subst hi; simp [substZeroOneOne]
    · simp [substZeroOneOne, hi, Function.update_of_ne hi]
  exact DFunLike.congr_fun this r

theorem det_two_ne_zero : (D2 : MvPolynomial (Fin 2 × Fin 2) F) ≠ 0 := by
  intro h
  have := congrArg (eval (fun ij : Fin 2 × Fin 2 => if ij.1 = ij.2 then (1 : F) else 0)) h
  simp [D2] at this

theorem isChowForm_line :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) F)) 2 (D2 : MvPolynomial (Fin 2 × Fin 2) F) := by
  refine ⟨det_two_ne_zero, fun g => ⟨fun hg => ?_, ?_⟩⟩
  ·
    obtain ⟨N, q, r, h1, h2⟩ := pseudo g
    have hr : r = 0 := by
      have hz : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) (X (0,0) * r) = 0 := by
        apply MvPolynomial.funext
        intro w
        have key : aeval w (X (0,0) * r) = 0 := by
          by_cases hw : w (0,0) = 0
          · simp [hw]
          · let u : Fin 2 × Fin 2 → AlgebraicClosure F :=
              Function.update w (1,1) (w (0,1) * w (1,0) / w (0,0))
            have u00 : u (0,0) = w (0,0) := Function.update_of_ne (by decide) _ _
            have u01 : u (0,1) = w (0,1) := Function.update_of_ne (by decide) _ _
            have u10 : u (1,0) = w (1,0) := Function.update_of_ne (by decide) _ _
            have u11 : u (1,1) = w (0,1) * w (1,0) / w (0,0) := Function.update_self _ _ _
            have hinc : u ∈ incidence (⊥ : Ideal (MvPolynomial (Fin 2) F)) 2 := by
              refine ⟨![w (0,1), -w (0,0)], fun h => ?_, fun g' hg' => ?_, fun i => ?_⟩
              · have := congrFun h 1
                simp at this
                exact hw this
              · rw [Ideal.mem_bot] at hg'
                simp [hg']
              · fin_cases i
                · simp [Fin.sum_univ_two, u00, u01]; ring
                · simp [Fin.sum_univ_two, u10, u11]; field_simp; ring
            have hg' := hg u hinc
            have hD : aeval u (D2 : MvPolynomial (Fin 2 × Fin 2) F) = 0 := by
              simp only [D2, map_sub, map_mul, aeval_X, u00, u01, u10, u11]
              field_simp
              ring
            have h3 := congrArg (aeval u) h1
            simp only [map_mul, map_add, map_pow, hg', hD, mul_zero, zero_add] at h3
            have hw' : aeval w r = aeval u r := by
              rw [← h2, aeval_substZeroOneOne, aeval_substZeroOneOne]
              congr 1
              simp only [u, Function.update_idem]
            rw [map_mul, hw', ← h3, mul_zero]
        rw [eval_map, map_zero]
        simpa [aeval_def] using key
      have hz' : (X (0,0) * r : MvPolynomial (Fin 2 × Fin 2) F) = 0 :=
        MvPolynomial.map_injective _ (algebraMap F (AlgebraicClosure F)).injective (by simpa using hz)
      exact (mul_eq_zero.mp hz').resolve_left (X_ne_zero _)
    rw [hr, add_zero] at h1
    exact cancelN N g ⟨q, by rw [h1]; ring⟩
  · rintro ⟨h, rfl⟩ u ⟨x, hx, -, hu⟩
    have E0 := hu 0
    have E1 := hu 1
    simp only [Fin.sum_univ_two] at E0 E1
    have hD : aeval u (D2 : MvPolynomial (Fin 2 × Fin 2) F) = 0 := by
      simp only [D2, map_sub, map_mul, aeval_X]
      by_cases h0 : x 0 = 0
      · have h1 : x 1 ≠ 0 := fun h1 => hx (funext fun j => by fin_cases j <;> simpa [*])
        apply mul_right_cancel₀ h1
        linear_combination (-(u (1,0))) * E0 + u (0,0) * E1
      · apply mul_right_cancel₀ h0
        linear_combination u (1,1) * E0 - u (0,1) * E1
    rw [map_mul, hD, zero_mul]

theorem isProjPrime_line : IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) F)) where
  isPrime := Ideal.isPrime_bot
  isHomog f hf d := by
    rw [Ideal.mem_bot] at hf ⊢
    simp [hf]
  isRelevant := ⟨0, by rw [Ideal.mem_bot]; exact X_ne_zero 0⟩

theorem isMultiHomog_line : IsMultiHomog 1 (D2 : MvPolynomial (Fin 2 × Fin 2) F) := by
  have hX : ∀ i j : Fin 2, IsWeightedHomogeneous (groupWeight 2 2)
      (X (i, j) : MvPolynomial (Fin 2 × Fin 2) F) (Pi.single i 1) :=
    fun i j => isWeightedHomogeneous_X F (groupWeight 2 2) (i, j)
  have hw : (Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℕ) = fun _ => 1 := by
    funext i; fin_cases i <;> simp
  have a := (hX 0 0).mul (hX 1 1)
  have b := (hX 0 1).mul (hX 1 0)
  rw [hw] at a b
  exact (weightedHomogeneousSubmodule F (groupWeight 2 2) (fun _ => 1)).sub_mem a b

theorem linForm_line : linForm (fun j : Fin 2 => if j = 0 then (1 : F) else 0) ∉
    (⊥ : Ideal (MvPolynomial (Fin 2) F)) := by
  rw [Ideal.mem_bot]
  intro h
  have := congrArg (eval (fun _ : Fin 2 => (1 : F))) h
  simp [linForm, Fin.sum_univ_two] at this

end LineChowForm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFundCycleBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def FundCycleBaseChange.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) K)),
      fundCycle (J.map (MvPolynomial.map σ)) =
        ∑ W ∈ (fundCycle J).support, fundCycle J W • fundCycle (W.map (MvPolynomial.map σ))

end GroundTheory.Heights₂.Heights
end

