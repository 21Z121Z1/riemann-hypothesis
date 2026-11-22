import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0087

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardQuotSmulTopLePowFinrankStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_quot_smul_le_pow_finrank : ∀ (E : Type) [Field E] [NumberField E] (La : Type) [AddCommGroup La] [Module (𝓞 E) La], Module.Finite (𝓞 E) La → Module.Projective (𝓞 E) La → ∀ (I : Ideal (𝓞 E)) (g : ℕ), g.Prime → Ideal.absNorm I = g → Finite (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ∧ Nat.card (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ≤ g ^ Module.finrank (𝓞 E) La := by
  first | exact @GlobalTheory.natCard_quot_smul_top_le_pow_finrank | exact GlobalTheory.natCard_quot_smul_top_le_pow_finrank | (intros; apply GlobalTheory.natCard_quot_smul_top_le_pow_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentApproximationSurjective
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_approximation_surjective : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (I : Ideal B) (K : Ideal A) (N : ℕ), (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ I.map (algebraMap B A) ⊔ K) → (I ^ N).map (algebraMap B A) ≤ K → ∀ a : A, ∃ b : B, a - algebraMap B A b ∈ K := by
  first | (exact @GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le) | (exact GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le) | (intros; apply GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoCommonZeroSpreadsConstructibleNbhdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_common_zero_spreads_constructible_nbhd : ∀ (A : Type) [CommRing A] (τ J : Type) [Finite τ] (F : J → MvPolynomial τ A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), (¬ ∃ z : τ → Ω, ∀ j, MvPolynomial.eval₂ φ z (F j) = 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ ∃ z : τ → k, ∀ j, MvPolynomial.eval₂ ψ z (F j) = 0 := by
  first | exact @GlobalTheory.NoCommonZeroSpread.no_common_zero_spreads | exact GlobalTheory.NoCommonZeroSpread.no_common_zero_spreads | (intros; apply GlobalTheory.NoCommonZeroSpread.no_common_zero_spreads <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoSplittingFactorisationOfPderivNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_splitting_factorisation_of_pderiv_ne_zero : ∀ (Ω : Type) [Field Ω] (σ : Type) (f g : MvPolynomial σ Ω) (i : σ) (D : ℕ), (∀ Q : σ → Ω, MvPolynomial.eval Q f = 0 → MvPolynomial.eval Q g ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i f) ≠ 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) → ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) := by
  first | exact @GlobalTheory.hypersurface_part_no_splitting_factorisation | exact GlobalTheory.hypersurface_part_no_splitting_factorisation | (intros; apply GlobalTheory.hypersurface_part_no_splitting_factorisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherNormalizationFiniteAevalPowAddStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noether_normalization_finite_aeval_pow_add : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (t a : A), (Polynomial.aeval (R := k) t).Finite → ∃ M : ℕ, (Polynomial.aeval (R := k) (t ^ M + a)).Finite := by
  first | exact @GlobalTheory.noether_trick | exact GlobalTheory.noether_trick | (intros; apply GlobalTheory.noether_trick <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormClassFiniteOfReducedRatAlgebraStatement
section
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normClassFinite_of_reduced_rat_algebra : (∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e) →
  ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e := by
  first | (exact @GlobalTheory.normClassFinite_of_reduced) | (exact GlobalTheory.normClassFinite_of_reduced) | (intros; apply GlobalTheory.normClassFinite_of_reduced  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCompHomogeneousIsHomogeneousStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHomogeneous_eval_eq_norm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n d : ℕ) (f : MvPolynomial (Fin n) L), f.IsHomogeneous d → ∃ F : MvPolynomial (Fin n × Fin (Module.finrank K L)) K, F.IsHomogeneous (d * Module.finrank K L) ∧ ∀ y : Fin n × Fin (Module.finrank K L) → K, MvPolynomial.eval y F = Algebra.norm K (MvPolynomial.eval (fun i => ∑ j, algebraMap K L (y (i, j)) * Module.finBasis K L j) f) := by
  first | exact @GlobalTheory.norm_comp_homogeneous_isHomogeneous | exact GlobalTheory.norm_comp_homogeneous_isHomogeneous | (intros; apply GlobalTheory.norm_comp_homogeneous_isHomogeneous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEigenvalueLeOneOfIntegralMatrixUltrametricStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eigenvalue_le_one_of_integral_matrix_ultrametric : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] (emb : O →+* K), (∀ c, ‖emb c‖ ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K), c ≠ 0 → (M.map emb).mulVec c = μ • c → ‖μ‖ ≤ 1 := by
  first | exact @GlobalTheory.eigenvalue_integral_matrix_norm_le_one | exact GlobalTheory.eigenvalue_integral_matrix_norm_le_one | (intros; apply GlobalTheory.eigenvalue_integral_matrix_norm_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaussianConvolutionSeriesCoefficientLeIntegr
section
open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

namespace CoefNorm

theorem norm_innerC_apply_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a y : E) :
    ‖innerC a y‖ ≤ ‖a‖ * ‖y‖ := by
  simp only [innerC, ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.ofRealCLM_apply,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_real_inner_le_norm a y

theorem norm_powForm_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ) (a : E) :
    ‖powForm k a‖ ≤ ‖a‖ ^ k := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  simp only [powForm, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  rw [norm_prod]
  calc ∏ i, ‖innerC a (m i)‖ ≤ ∏ i, (‖a‖ * ‖m i‖) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_innerC_apply_le a (m i)
    _ = ‖a‖ ^ k * ∏ i, ‖m i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem norm_wt_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : E → ℂ) (a : E) : ‖wt b c h a‖ ≤ ‖h a‖ := by
  unfold wt
  rw [norm_mul, norm_mul, ← Complex.ofReal_neg, ← Complex.ofReal_neg, Complex.norm_exp_ofReal,
    Complex.norm_exp_ofReal]
  have e1 : Real.exp (-(b * ‖a‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖a‖])
  have e2 : Real.exp (-(c * ‖a‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖a‖])
  calc _ ≤ 1 * ‖h a‖ * 1 := by gcongr
    _ = _ := by ring

theorem continuous_wt {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (h : E → ℂ)
    (hh : Continuous h) : Continuous (wt b c h) := by
  unfold wt
  fun_prop

end CoefNorm

open CoefNorm in

theorem norm_coef_le_integral (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : SchwartzMap E ℂ) (j : ℕ) :
    ‖coef b c (⇑h) j‖ ≤ ∫ a, ‖wt b c (⇑h) a‖ * ‖a‖ ^ j := by
  unfold coef
  refine (norm_integral_le_integral_norm _).trans ?_
  have hw : Continuous (wt b c (⇑h)) := continuous_wt b c _ h.continuous
  have hint : Integrable (fun a : E => ‖a‖ ^ j * ‖h a‖) := h.integrable_pow_mul volume j
  have hint2 : Integrable (fun a : E => ‖wt b c (⇑h) a‖ * ‖a‖ ^ j) := by
    refine hint.mono' ((hw.norm.mul (continuous_norm.pow j)).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_wt_le b c hb hc _ a) (by positivity)
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => norm_nonneg _) hint2
    (Filter.Eventually.of_forall fun a => ?_)
  simp only [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_powForm_le j a) (norm_nonneg _)

end GlobalTheory.ConvSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormInvLePowCardOfNormProdEqOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_inv_le_pow_card_of_norm_prod_eq_one' : ∀ (B : Multiset ℂˣ) (M : ℝ), 1 ≤ M → (∀ b ∈ B, ‖(b : ℂ)‖ ≤ M) → ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 → ∀ b ∈ B, ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ M ^ B.card := by
  first | exact @GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one | exact GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one | (intros; apply GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivCexpPhaseLeStatement
section
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_cexp_phase_le' : ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h → (∀ y t, (B y t + h t).re = 0) → ∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t)) t‖ ≤ C * (1 + ‖y‖) ^ n := by
  first | exact @GlobalTheory.norm_iteratedFDeriv_cexp_phase_le | exact GlobalTheory.norm_iteratedFDeriv_cexp_phase_le | (intros; apply GlobalTheory.norm_iteratedFDeriv_cexp_phase_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivIteratedFDerivStatement
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_iteratedFDeriv' : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (n j : ℕ) (z : E), ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ n f) z‖ = ‖iteratedFDeriv ℝ (n + j) f z‖ := by
  first | exact @GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv | exact GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv | (intros; apply GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv <;> assumption)
end

