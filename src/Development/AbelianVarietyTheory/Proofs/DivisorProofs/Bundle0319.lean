import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinWeightTwoQExpansion
section
noncomputable section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem hTrans_zero (ν y : ℝ) (hy : y ≠ 0) :
    hTrans 0 ν y = if 0 < ν * y then
      -4 * (Real.pi : ℂ) ^ 2 * ((|ν| : ℝ) : ℂ) * ((Real.exp (-(2 * Real.pi * (ν * y))) : ℝ) : ℂ) else 0 := by
  rcases hy.lt_or_gt with h | h
  · have e := hTrans_zero_neg (-ν) y
    rw [neg_neg] at e
    rw [← e, GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq _ _ (neg_pos.2 h)]
    by_cases hν : 0 < -ν
    · have h2 : 0 < ν * y := by nlinarith
      rw [if_pos hν, if_pos h2, abs_of_neg (by linarith : ν < 0),
        show -(2 * Real.pi * -ν * -y) = -(2 * Real.pi * (ν * y)) by ring]
    · have h2 : ¬ 0 < ν * y := by nlinarith
      rw [if_neg hν, if_neg h2]
  · rw [GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq _ _ h]
    by_cases hν : 0 < ν
    · have h2 : 0 < ν * y := mul_pos hν h
      rw [if_pos hν, if_pos h2, abs_of_pos hν, show 2 * Real.pi * ν * y = 2 * Real.pi * (ν * y) by ring]
    · have h2 : ¬ 0 < ν * y := by nlinarith
      rw [if_neg hν, if_neg h2]

theorem fTerm_zero [IsTotallyReal F] {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b ν : F} (hb : b ≠ 0) (hν : ν ≠ 0) :
    fTerm 0 z b ν = if ∀ τ : Emb F, 0 < τ (ν * b) then
      (-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) * ((|(Algebra.norm ℚ ν : ℝ)| : ℝ) : ℂ) * qPow (ν * b) z
      else 0 := by
  have hyτ : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  unfold fTerm
  simp only [hTrans_zero _ _ (hyτ _)]
  split_ifs with hc
  · have hc' : ∀ τ : Emb F, 0 < τ ν * (τ b * (z τ).im) := fun τ => by
      have := hc τ; rw [map_mul] at this; rw [← mul_assoc]; exact mul_pos this (hz τ)
    rw [Finset.prod_congr rfl fun τ _ => by rw [if_pos (hc' τ)]]
    rw [abs_norm_eq_prod, qPow, Finset.mul_sum, Complex.exp_sum]
    rw [show ((-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) * ∏ τ : Emb F, ((|τ ν| : ℝ) : ℂ)) *
        ∏ x : Emb F, Complex.exp (2 * (Real.pi : ℂ) * I * ((x (ν * b) : ℂ) * z x)) =
        ∏ τ : Emb F, ((-4 * (Real.pi : ℂ) ^ 2) * ((|τ ν| : ℝ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * I * ((τ (ν * b) : ℂ) * z τ))) by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_comm, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; congr 1
    conv_rhs => rw [← Complex.re_add_im (z τ)]
    simp only [map_mul]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * (τ ν : ℂ) * (τ b : ℂ) * ((z τ).im : ℂ)) * I_sq
  · push_neg at hc
    obtain ⟨τ, hτ⟩ := hc
    have : ¬ 0 < τ ν * (τ b * (z τ).im) := by
      rw [map_mul] at hτ; rw [← mul_assoc]; exact not_lt.2 (mul_nonpos_of_nonpos_of_nonneg hτ (hz τ).le)
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [if_neg this, mul_zero])

theorem bOne_zero_expansion [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) :
    Summable (qClass 𝔞 𝔟 2 z) ∧
      (cK F 2 : ℂ) * (kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z) / (omegaFactor 𝔞 : ℂ) ^ 2 =
        ∑' c, qClass 𝔞 𝔟 2 z c := by
  have hS := GlobalTheory.T.summable_hilbertEisensteinWeightTwoQSeries F 𝔞 𝔟 z hz
  refine ⟨hS, ?_⟩
  have hn : (nrm 𝔞 : ℂ) ≠ 0 := by exact_mod_cast nrm_ne_zero 𝔞
  have hs : ((dF F ^ ((1 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (dF_pos (F := F)) _).ne'
  have hcK : (cK F 2 : ℂ) = ((dF F ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
    unfold cK; norm_num
  have hL : (cK F 2 : ℂ) * (kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z) / (omegaFactor 𝔞 : ℂ) ^ 2 =
      (kFac F 0 / (nrm 𝔞 : ℂ)) * bOne 𝔞 𝔟 0 z := by
    rw [hcK, omegaFactor]; push_cast
    push_cast at hs
    field_simp
  rw [hL, bOne, ← tsum_mul_left, tsum_qClass_eq 𝔞 𝔟 z hS]
  refine tsum_congr fun c => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun ν => ?_
  rw [fTerm_zero hz c.out.2.2 ν.2.2]
  split_ifs with hc
  · have hk := kFac_zero_mul (F := F)
    unfold qTerm
    simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one, Complex.ofReal_div]
    linear_combination (((|(Algebra.norm ℚ ν.1 : ℝ)| : ℝ) : ℂ) / (nrm 𝔞 : ℂ) * qPow (ν.1 * c.out.1) z) * hk
  · rw [mul_zero]

theorem bOne_zero_qExpansion : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * (GlobalTheory.HeckeTwo.kFac F 0 *
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * GlobalTheory.HeckeTwo.bOne 𝔞 𝔟 0 z) / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 =
      ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c :=
  fun _ _ _ _ 𝔞 𝔟 z hz => bOne_zero_expansion 𝔞 𝔟 z hz

end GlobalTheory.HeckeTwoExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

namespace BZeroGood

theorem card_emb_totReal (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) ⟨fun τ τ' h => ?_, fun φ => ?_⟩
  · ext x
    exact Complex.ofReal_injective (RingHom.congr_fun h x)
  · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x =>
      (IsTotallyReal.complexEmbedding_isReal φ).coe_embedding_apply x⟩

theorem halfPlane_mem_nhds_zero : halfPlane ∈ nhds (0 : ℂ) := by
  refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
  show (-1 / 2 : ℝ) < (0 : ℂ).re
  norm_num

theorem _root_.GlobalTheory.HeckeTwo.bZero_isGood (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (hf : 2 ≤ Module.finrank ℚ F)
    (𝔞 𝔟 : Frac F) (Zb R : ℂ → ℂ) (hR : Differentiable ℂ R) (hZ : ∀ s : ℂ, s ≠ 1 → Zb s = R s / (s - 1)) :
    IsGood (bZero Zb 𝔞 𝔟) := by
  set f := Fintype.card (Emb F) with hfdef
  have hf2 : 2 ≤ f := by rw [hfdef, card_emb_totReal F]; exact hf
  set E : ℂ → ℂ := fun σ => if σ = 0 then 0 else
    kFac F σ * (omegaFactor 𝔞 : ℂ) * ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ) * Zb (1 + 2 * σ) * cConst σ ^ f with hE
  set G : ℂ → ℂ := fun σ =>
    kFac F σ * (omegaFactor 𝔞 : ℂ) * ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ) * (R (1 + 2 * σ) / 2) *
      dslope cConst 0 σ * cConst σ ^ (f - 1) with hG
  have hEG : E = G := by
    funext σ
    simp only [hE, hG]
    split_ifs with h0
    · subst h0
      rw [GlobalTheory.T.heckePhiFourierConstantAtZero_zero, zero_pow (by omega), mul_zero]
    · rw [dslope_of_ne _ h0, slope_def_field, GlobalTheory.T.heckePhiFourierConstantAtZero_zero, hZ _ (by
          intro h; apply h0; linear_combination h / 2)]
      have hf1 : f = (f - 1) + 1 := by omega
      rw [hf1, pow_succ]
      simp only [Nat.add_sub_cancel]
      field_simp
      ring
  have hGd : DifferentiableOn ℂ G halfPlane := by
    intro σ hσ
    have hσ' : -1 - 2 * σ ≠ 0 := by
      intro h
      have : σ.re = -1 / 2 := by
        have := congrArg Complex.re h
        simp at this
        linarith
      simp only [halfPlane, Set.mem_setOf_eq] at hσ
      linarith
    have h1 : DifferentiableAt ℂ (fun σ : ℂ => ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ)) σ :=
      DifferentiableAt.const_cpow ((differentiableAt_const _).sub (differentiableAt_id.const_mul _)) (Or.inr hσ')
    have h2 : DifferentiableAt ℂ (fun σ : ℂ => R (1 + 2 * σ)) σ :=
      (hR _).comp σ ((differentiableAt_const _).add (differentiableAt_id.const_mul _))
    have h3 : DifferentiableWithinAt ℂ (dslope cConst 0) halfPlane σ :=
      ((differentiableOn_dslope halfPlane_mem_nhds_zero).2 GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn) σ hσ
    have h4 : DifferentiableWithinAt ℂ cConst halfPlane σ := GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn σ hσ
    exact ((((kFac_differentiable σ).differentiableWithinAt.mul (differentiableWithinAt_const _)).mul
      h1.differentiableWithinAt).mul (h2.differentiableWithinAt.div_const _)).mul h3 |>.mul (h4.pow _)
  have hB : bZero Zb 𝔞 𝔟 = fun σ z => E σ * ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
    funext σ z
    simp only [bZero, hE]
    split_ifs
    · simp
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      ring
  rw [hB]
  exact GlobalTheory.HeckeTwoMul.isGood_mul F E _ (hEG ▸ hGd) ⟨fun σ _ => GlobalTheory.T.upperHalfPlaneProduct_prod_im_rpow_contDiffOn F σ, fun w z hz => GlobalTheory.T.prodIm_iteratedWirtingerDerivWord_differentiableOn F w z hz⟩

end BZeroGood

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicProperties
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section
namespace GlobalTheory.KSp

section PairAlg

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem pr_eq_trace (Q : Matrix α α E) (x y : Matrix α ν E) :
    pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  have h : fromCols x (0 : Matrix α ν E) * stdJ ν E * ((fromCols (0 : Matrix α ν E) y).map c)ᵀ = x * (y.map c)ᵀ := by
    ext i k
    simp [stdJ, mul_apply, Fintype.sum_sum_type, one_apply]
  rw [pr, form, hTens_eq, h]
  congr 2
  simp only [Matrix.trace, diag, mul_apply, transpose_apply]
  rw [Finset.sum_comm]

theorem trace_single_pair (Q : Matrix α α E) (y : Matrix α ν E) (i : α) (j : ν) (z : E) :
    Matrix.trace (Qᵀ * (Matrix.single i j z * (y.map c)ᵀ)) = z * (Q * y.map c) i j := by
  simp [Matrix.trace, mul_apply, Matrix.single_apply, Finset.mul_sum, ite_and]
  refine Finset.sum_congr rfl fun _ _ => by ring

def prLin (Q : Matrix α α E) : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))))
    (fun x x' y => by simp [Matrix.add_mul, Matrix.mul_add, mul_add])
    (fun t x y => by simp [Matrix.smul_mul, Matrix.mul_smul, mul_left_comm])
    (fun x y y' => by
      rw [show (y + y').map c = y.map c + y'.map c from Matrix.map_add _ (map_add c) _ _]
      simp [Matrix.add_mul, Matrix.mul_add, mul_add])
    (fun t x y => by
      rw [show (t • y).map c = t • y.map c from by ext i j; simp [map_smul]]
      simp [Matrix.smul_mul, Matrix.mul_smul, mul_left_comm])

end PairAlg

end GlobalTheory.KSp

namespace GlobalTheory.KSp

theorem pr_alg : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E)
    (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν]
    (Q : Matrix α α E) (_ : IsHerm c Q), ∃ β : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F,
      (∀ x y, β x y = pr c Q x y) ∧ (∀ x y, β x y = β y x) ∧ (∀ y, (∀ x, β x y = 0) → y = 0) ∧
      (∀ (x y : Matrix α ν E) (a : Matrix ν ν E), β (x * a) y = β x (y * (a.map c)ᵀ)) ∧
      ∀ x y, β x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q hQ
  have hc : ∀ z, c (c z) = z := hE.invol
  have ht : ∀ z, Algebra.trace F E (c z) = Algebra.trace F E z := fun z =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z
  have hap : ∀ x y : Matrix α ν E, prLin c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) :=
    fun _ _ => rfl
  refine ⟨prLin c Q, fun x y => by rw [hap, pr_eq_trace], fun x y => ?_, fun y hy => ?_, fun x y a => ?_, hap⟩
  ·
    have h : Matrix.trace (Qᵀ * (y * (x.map c)ᵀ)) = c (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
      simp only [Matrix.trace, diag, mul_apply, transpose_apply, map_apply, map_sum, map_mul, hc, hQ.1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)
    rw [hap, hap, h, ht]
  ·
    obtain ⟨bE, -, -⟩ := hE.basis
    haveI : Module.Finite F E := Module.Finite.of_basis bE
    have htr : Algebra.trace F E 1 ≠ 0 := by
      rw [← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
      exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have hw : Q * y.map c = 0 := by
      ext i j
      by_contra hij
      apply htr
      have := hy (Matrix.single i j ((Q * y.map c) i j)⁻¹)
      rw [hap, trace_single_pair, inv_mul_cancel₀ hij] at this
      simpa using this
    have hy0 : y.map c = 0 := by
      have := congrArg (fun m => Q⁻¹ * m) hw
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ.2] using this
    ext i j
    exact c.toRingHom.injective (by simpa using congrFun (congrFun hy0 i) j)
  ·
    have h : ((y * (a.map c)ᵀ).map c)ᵀ = a * (y.map c)ᵀ := by
      ext i j
      simp [mul_apply, map_sum, hc, mul_comm]
    rw [hap, hap, h, Matrix.mul_assoc]

end GlobalTheory.KSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingDiagonalNorm
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem pr_eq_half_trace_mat (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (x y : Matrix α ν E) :
  pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  simp only [pr, form, GlobalTheory.WeilM.hTens, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, stdJ, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Pi.zero_apply, Matrix.zero_apply, map_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, one_apply, Matrix.trace, mul_apply, transpose_apply, map_apply, diag_apply]
  congr 2
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pr_diag_norm : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (u : Matrix α α E) (D' : α → F) (a : Matrix ν ν E) (D : ν → F), Q = u * diagonal (fun i => algebraMap F E (D' i)) * (u.map c)ᵀ → ∀ x : Matrix α ν E, 2⁻¹ * pr c Q x (x * (a * diagonal (fun j => algebraMap F E (D j)) * (a.map c)ᵀ)) = ∑ i, ∑ j, (2⁻¹ * D' i * D j) * Algebra.norm F ((uᵀ * x * a) i j) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q _ u D' a D hQu x
  have hc : ∀ z, c (c z) = z := hE.invol
  have hmm : ∀ {m n : Type} (M : Matrix m n E), (M.map c).map c = M := fun M => by ext i j; simp [hc]
  have hd : ∀ {m : Type} [Fintype m] [DecidableEq m] (d : m → F),
      (diagonal (fun i => algebraMap F E (d i))).map c = diagonal (fun i => algebraMap F E (d i)) := by
    intro m _ _ d; ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
  set dD' := diagonal (fun i => algebraMap F E (D' i))
  set dD := diagonal (fun j => algebraMap F E (D j))
  set Y := uᵀ * x * a with hY
  have hQT : Qᵀ = u.map c * dD' * uᵀ := by
    rw [hQu, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  have hbs : ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ = a * dD * (a.map c)ᵀ * (x.map c)ᵀ := by
    rw [Matrix.map_mul (f := c), Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul, transpose_mul,
      transpose_mul, hd, diagonal_transpose, transpose_map, hmm, ← transpose_map, transpose_transpose]
    simp only [Matrix.mul_assoc]
    rfl
  have hYs : (Y.map c)ᵀ = (a.map c)ᵀ * (x.map c)ᵀ * u.map c := by
    rw [hY, Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul, transpose_mul, transpose_map,
      transpose_transpose]
    simp only [Matrix.mul_assoc]
  have htr : Matrix.trace (Qᵀ * (x * ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ)) = Matrix.trace (dD' * Y * dD * (Y.map c)ᵀ) := by
    rw [hQT, hbs, hYs, hY]
    rw [show u.map c * dD' * uᵀ * (x * (a * dD * (a.map c)ᵀ * (x.map c)ᵀ)) =
      u.map c * (dD' * uᵀ * x * a * dD * (a.map c)ᵀ * (x.map c)ᵀ) by simp only [Matrix.mul_assoc], trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hsum : Matrix.trace (dD' * Y * dD * (Y.map c)ᵀ) =
      algebraMap F E (∑ i, ∑ j, D' i * D j * Algebra.norm F (Y i j)) := by
    simp only [Matrix.trace, diag_apply, mul_apply, dD', dD, diagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, transpose_apply, map_apply,
      map_sum, map_mul, hE.algebraMap_norm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨b, -, -⟩ := hE.basis
  haveI : Module.Free F E := Module.Free.of_basis b
  haveI : Module.Finite F E := Module.Finite.of_basis b
  have hfin : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [pr_eq_half_trace_mat, htr, hsum, Algebra.trace_algebraMap, hfin, nsmul_eq_mul, Nat.cast_ofNat,
    inv_mul_cancel_left₀ (two_ne_zero : (2 : F) ≠ 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinNonconstantTermsHasSum
section
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.EisNonConst
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

theorem qTerm_norm {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (p : F × F) :
    ((‖qTerm 𝔞 k z p‖ : ℝ) : ℂ) = qTerm 𝔞 k (fun τ => Complex.I * ((z τ).im : ℂ)) p := by
  have hr : (0 : ℝ) ≤ (|(Algebra.norm ℚ p.1 : ℝ)| / nrm 𝔞) ^ (k - 1) := by
    apply pow_nonneg; apply div_nonneg (abs_nonneg _)
    unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  unfold qTerm qPow
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hr]
  push_cast
  congr 1
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

theorem nonconst_terms : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
  ∀ (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k →
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z) ∧
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z c)
      ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) * ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z c) := by
  intro F _ _ _ hL 𝔞 𝔟 k hk2 hke hsum z hz
  obtain ⟨e1, he1⟩ := GlobalTheory.T.exists_equiv_latticeClasses_fibre_summand F 𝔞 𝔟
  obtain ⟨e2, he2⟩ := GlobalTheory.T.exists_equiv_fourierClasses_posCone_summand F 𝔞 𝔟
  set C : ℂ := (omegaFactor 𝔞 : ℂ) ^ k / (cK F k : ℂ) with hC
  set y : Emb F → ℂ := fun τ => Complex.I * ((z τ).im : ℂ) with hy_def
  have hdF : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hN : 0 < nrm 𝔞 := by
    unfold nrm
    have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
    exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm
  have hCne : C ≠ 0 := by
    have h1 : 0 < omegaFactor 𝔞 := mul_pos (Real.rpow_pos_of_pos hdF _) hN
    have h2 : 0 < cK F k := mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos hdF _)
    rw [hC]
    exact div_ne_zero (pow_ne_zero _ (by exact_mod_cast h1.ne')) (by exact_mod_cast h2.ne')
  have hy : y ∈ upperHalf F := fun τ => by simpa [hy_def] using hz τ

  have hlat : ∀ w ∈ upperHalf F, Summable (fun x : (Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) =>
      eisTerm k 0 w ((x.2 : F), rep x.1)) := by
    intro w hw
    have h1 : Summable (fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 w c) :=
      (hsum w hw).subtype _
    have h2 := (e1.summable_iff (f := fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 w c)).2 h1
    refine h2.congr fun x => ?_
    simp only [Function.comp_apply]
    exact he1 k hke 0 w x

  have hqfib : ∀ β : NzCls 𝔟, Summable (fun ν : posCone 𝔞 (rep β) => ‖qTerm 𝔞 k z (ν.1, rep β)‖) := by
    intro β
    have := (GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) y hy).1
    rw [← Complex.summable_ofReal]
    refine this.congr fun ν => ?_
    exact (qTerm_norm 𝔞 k z _).symm
  have hqsig : Summable (fun x : (Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) => qTerm 𝔞 k z (x.2.1, rep x.1)) := by
    refine Summable.of_norm ?_
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨hqfib, ?_⟩
    have hmarg : Summable (fun β : NzCls 𝔟 => ∑' a : (latM 𝔞 : Set F), ‖eisTerm k 0 y ((a : F), rep β)‖) :=
      (summable_norm_iff.2 (hlat y hy)).sigma
    refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) (fun β => ?_) (hmarg.mul_left ‖C‖⁻¹)
    obtain ⟨-, hP⟩ := GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) y hy
    have hfib := hqfib β
    have hT : ((∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖ : ℝ) : ℂ) =
        ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k y (ν.1, rep β) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun ν => qTerm_norm 𝔞 k z _
    have hE : ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k y (ν.1, rep β) =
        C⁻¹ * ∑' a : (latM 𝔞 : Set F), eisTerm k 0 y ((a : F), rep β) := by
      rw [hP.tsum_eq, ← mul_assoc, inv_mul_cancel₀ hCne, one_mul]
    have hnn : 0 ≤ ∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖ := tsum_nonneg fun _ => norm_nonneg _
    calc ∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖
        = ‖((∑' ν : posCone 𝔞 (rep β), ‖qTerm 𝔞 k z (ν.1, rep β)‖ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ = ‖C‖⁻¹ * ‖∑' a : (latM 𝔞 : Set F), eisTerm k 0 y ((a : F), rep β)‖ := by
          rw [hT, hE, norm_mul, norm_inv]
      _ ≤ ‖C‖⁻¹ * ∑' a : (latM 𝔞 : Set F), ‖eisTerm k 0 y ((a : F), rep β)‖ := by
          gcongr
          exact norm_tsum_le_tsum_norm ((summable_norm_iff.2 (hlat y hy)).sigma_factor β)
  have hq : Summable (qClass 𝔞 𝔟 k z) := by
    have : Summable (qClass 𝔞 𝔟 k z ∘ e2) := hqsig.congr fun x => (he2 k z x).symm
    exact (e2.summable_iff).1 this
  refine ⟨hq, ?_⟩

  have hQ : HasSum (fun β : NzCls 𝔟 => ∑' ν : posCone 𝔞 (rep β), qTerm 𝔞 k z (ν.1, rep β)) (∑' c, qClass 𝔞 𝔟 k z c) := by
    have h1 : HasSum (fun x => qTerm 𝔞 k z (x.2.1, rep x.1) : (Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) → ℂ) (∑' c, qClass 𝔞 𝔟 k z c) := by
      have := (e2.hasSum_iff (f := qClass 𝔞 𝔟 k z)).2 hq.hasSum
      exact this.congr_fun fun x => (he2 k z x).symm
    exact h1.sigma fun β => (hqsig.sigma_factor β).hasSum
  have hL1 : HasSum (fun x : (Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) => eisTerm k 0 z ((x.2 : F), rep x.1))
      (C * ∑' c, qClass 𝔞 𝔟 k z c) := by
    have hs := (hlat z hz).hasSum
    have hg := hs.sigma fun β => (GlobalTheory.EisPerB.lattice_sum_eq_cone_sum F hL 𝔞 k hk2 hke (rep β) (rep_ne_zero β) z hz).2
    rw [(hQ.mul_left C).unique hg]
    exact hs
  have : HasSum (fun x => eisClass 𝔞 𝔟 k 0 z (e1 x).1) (C * ∑' c, qClass 𝔞 𝔟 k z c) :=
    hL1.congr_fun fun x => he1 k hke 0 z x
  exact (e1.hasSum_iff (f := fun c : {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => eisClass 𝔞 𝔟 k 0 z c)).1 this

end GlobalTheory.EisNonConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCurvatureDualMetricPointwiseBoundStatement
section
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCurvature_dual_metric_pointwise_bound : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K : ℝ), 0 < c → 0 ≤ K → Y.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, (Bs i).PosSemidef) → (∀ i, 0 < t i) → (∀ i x, t i * (x ⬝ᵥ Bs i *ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ j k, ‖Dm j k‖ ≤ K) → (Y.map Complex.ofReal).PosDef ∧ ∀ v, ‖form (Y.map Complex.ofReal)⁻¹ ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v) ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)‖ ≤ (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map Complex.ofReal) v ^ 2 := by
  first | exact @GlobalTheory.HodgeCurvPoint.dual_bound | exact GlobalTheory.HodgeCurvPoint.dual_bound | (intros; apply GlobalTheory.HodgeCurvPoint.dual_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricGramMatrixLocalHolomorphicImPartStatement
section
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart : ∀ (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), IsPeriodChart rk τ₀ B → ∀ z ∈ punctured ha 1, MContDiffAt ∞ (hodgeGram ha τ₀ B) z ∧ (∀ ξ, mdel (hodgeGram ha τ₀ B) z ξ = (1 / (2 * Complex.I)) • ((Matrix.of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ) + ∑ i, (ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))) • ((B i).map (Int.cast : ℤ → ℝ)).map Complex.ofReal)) ∧ ∀ ξ η, mddbar (hodgeGram ha τ₀ B) z ξ η = 0 := by
  first | exact @GlobalTheory.HodgeGramLocal.hodgeGram_local | exact GlobalTheory.HodgeGramLocal.hodgeGram_local | (intros; apply GlobalTheory.HodgeGramLocal.hodgeGram_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfacePartGeometricIrreducibleSpreadsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypersurface_part_geometric_irreducible_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (i : σ), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) → (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : σ → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i (MvPolynomial.map ψ f)) ≠ 0) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map φ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map φ g}) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map ψ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map ψ g}) := by
  first | exact @GlobalTheory.hypersurface_part_preirreducible_spreads | exact GlobalTheory.hypersurface_part_preirreducible_spreads | (intros; apply GlobalTheory.hypersurface_part_preirreducible_spreads <;> assumption)
end

