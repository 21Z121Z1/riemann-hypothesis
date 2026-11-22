import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0004
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealMulSpanMapStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_ideal_mul_span_map : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]), Function.Injective j → (∀ I J : Ideal (𝓞 E), I ≠ ⊥ → J ≠ ⊥ → logIdeal j (I * J) = logIdeal j I + logIdeal j J) ∧ (∀ a : 𝓞 E, logIdeal j (Ideal.span {a}) = Real.log ‖j a‖) ∧ ∀ e : 𝓞 E ≃+* 𝓞 E, ∀ I : Ideal (𝓞 E), logIdeal j (I.map (e : 𝓞 E →+* 𝓞 E)) = logIdeal (j.comp (e : 𝓞 E →+* 𝓞 E)) I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.logIdeal_mul_span_map | exact GlobalTheory.CompanionTheory.Ar.Fl.logIdeal_mul_span_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.logIdeal_mul_span_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealSupportFiniteStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logIdeal_support_finite : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ → {p : Nat.Primes | ∃ j : 𝓞 E →+* ℂ_[p], logIdeal j I ≠ 0}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelicStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logNorms_ext_degree_adelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic | exact GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElementStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_logIdeal_max_element : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]) (I : Ideal (𝓞 E)), Function.Injective j → I ≠ ⊥ → ∃ a ∈ I, a ≠ 0 ∧ (∀ b ∈ I, ‖j b‖ ≤ ‖j a‖) ∧ logIdeal j I = Real.log ‖j a‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_logIdeal_attained | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_logIdeal_attained | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_logIdeal_attained <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.RatProductFormulaStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_product_formula : ∀ r : ℚ, r ≠ 0 → {p : Nat.Primes | Real.log ‖(r : ℂ_[p])‖ ≠ 0}.Finite ∧ Real.log ‖(r : ℂ)‖ + ∑ᶠ p : Nat.Primes, Real.log ‖(r : ℂ_[p])‖ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.rat_product_formula_complex | exact GlobalTheory.CompanionTheory.Ar.Fl.rat_product_formula_complex | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.rat_product_formula_complex <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumEmbeddingsBaseChangeStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_embeddings_base_change : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (F : (k →+* A) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ j : k' →+* A, F (j.comp f) = (Module.finrank ℚ k' : ℝ) * ∑ j : k →+* A, F j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq | exact GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq <;> assumption)
end

