import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0003
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRing

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.ExistsExtensionEmbeddingAlgClosedStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_embedding_alg_closed : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (j : k →+* A), ∃ j' : k' →+* A, j'.comp f = j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.IdealNormPrincipalInExtensionStatement
section
open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_norm_principal_in_extension : ∀ (K : Type) [Field K] [NumberField K] (I : Ideal (𝓞 K)), I ≠ ⊥ → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (y : 𝓞 K'), y ≠ 0 ∧ y ∈ I.map (algebraMap (𝓞 K) (𝓞 K')) ∧ |((Algebra.norm ℚ (y : K') : ℚ) : ℝ)| = (I.absNorm : ℝ) ^ Module.finrank K K' := by
  first | exact @GlobalTheory.CompanionTheory.Lines.exists_principal_extension | exact GlobalTheory.CompanionTheory.Lines.exists_principal_extension | (intros; apply GlobalTheory.CompanionTheory.Lines.exists_principal_extension <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealMulSpanMap
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem logIdeal_mul_span_map : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]), Function.Injective j → (∀ I J : Ideal (𝓞 E), I ≠ ⊥ → J ≠ ⊥ → logIdeal j (I * J) = logIdeal j I + logIdeal j J) ∧ (∀ a : 𝓞 E, logIdeal j (Ideal.span {a}) = Real.log ‖j a‖) ∧ ∀ e : 𝓞 E ≃+* 𝓞 E, ∀ I : Ideal (𝓞 E), logIdeal j (I.map (e : 𝓞 E →+* 𝓞 E)) = logIdeal (j.comp (e : 𝓞 E →+* 𝓞 E)) I :=
  @PositivityTheory.Xgf.log_ideal_mul_span_map

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealSupportFinite
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem finite_logIdeal_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ →
    {p : Nat.Primes | ∃ j : 𝓞 E →+* ℂ_[p], logIdeal j I ≠ 0}.Finite :=
  @PositivityTheory.Xgf.logIdeal_support_finite

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelic
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem logNorms_ext_deg_isAdelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) :=
  @PositivityTheory.Xgf.logNorms_ext_degree_adelic

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsOfNonzeroAdelicStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norms_of_nonzero_adelic : ∀ (k : Type) [Field k] [NumberField k] (x : k), x ≠ 0 → (LogNorms.ofElt x).IsAdelic := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt | exact GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRingStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_embedding_discrete_valuation_ring : ∀ (K : Type) [Field K] [NumberField K] (p : Nat.Primes) (j : K →+* ℂ_[p]), ∃ (V : ValuationSubring K), IsDiscreteValuationRing V ∧ (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ V) ∧ (∀ a : 𝓞 K, (a : K) ∈ V) ∧ ∀ n : ℕ, ¬ (p : ℕ) ∣ n → ‖j (n : K)‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding | exact GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_logIdeal_attained : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]) (I : Ideal (𝓞 E)), Function.Injective j → I ≠ ⊥ → ∃ a ∈ I, a ≠ 0 ∧ (∀ b ∈ I, ‖j b‖ ≤ ‖j a‖) ∧ logIdeal j I = Real.log ‖j a‖ :=
  @PositivityTheory.Xgf.padic_logIdeal_max_element

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.RatProductFormula
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem rat_product_formula_complex : ∀ r : ℚ, r ≠ 0 → {p : Nat.Primes | Real.log ‖(r : ℂ_[p])‖ ≠ 0}.Finite ∧ Real.log ‖(r : ℂ)‖ + ∑ᶠ p : Nat.Primes, Real.log ‖(r : ℂ_[p])‖ = 0 :=
  PositivityTheory.Xgf.rat_product_formula

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumEmbeddingsBaseChange
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem finrank_mul_sum_comp_eq : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (F : (k →+* A) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ j : k' →+* A, F (j.comp f) = (Module.finrank ℚ k' : ℝ) * ∑ j : k →+* A, F j :=
  PositivityTheory.Xgf.sum_embeddings_base_change

end GlobalTheory.CompanionTheory.Ar.Fl
end

