import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0007
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.DifferentIdealLogSumRootDiscriminant
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem different_sum_eq_neg_finrank_mul_log_rootDiscr : ∀ (E : Type) [Field E] [NumberField E], {p : Nat.Primes | ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) ≠ 0}.Finite ∧ ∑ᶠ p : Nat.Primes, ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) = -(Module.finrank ℚ E : ℝ) * Real.log (rootDiscr E) := by
  intro E _ _
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (discr E).natAbs := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := hn ▸ Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hsum : ∀ p : Nat.Primes, ∑ j : E →+* ℂ_[p],
      GlobalTheory.CompanionTheory.Ar.Fl.logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
        Real.log ‖((n : ℚ) : ℂ_[p])‖ := by
    intro p
    rw [GlobalTheory.T.sum_logIdeal_eq_log_absNorm E _ hD p, absNorm_differentIdeal E (𝓞 E), ← hn,
      Rat.cast_natCast]
  have hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  obtain ⟨hfin, hprod⟩ := GlobalTheory.T.rat_product_formula (n : ℚ) hq
  have h1 : ‖((n : ℚ) : ℂ)‖ = (n : ℝ) := by rw [Rat.cast_natCast, Complex.norm_natCast]
  have hpos : (0 : ℝ) < ((|discr E| : ℤ) : ℝ) := Int.cast_pos.mpr (abs_pos.mpr (discr_ne_zero E))
  have h2 : Real.log (rootDiscr E) = (Module.finrank ℚ E : ℝ)⁻¹ * Real.log (n : ℝ) := by
    rw [rootDiscr_def, Real.log_rpow hpos, hn, Nat.cast_natAbs]
  have hk : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  simp only [hsum]
  refine ⟨hfin, ?_⟩
  rw [h1] at hprod
  rw [h2, ← mul_assoc, neg_mul, mul_inv_cancel₀ hk.ne', neg_one_mul]
  linarith

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMatrixPosDefConjugateStatement
section
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_pos_def_conjugate : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (i : ℕ) (f : Fin i → B.carrier), LinearIndependent (𝓞 L) f → (∀ σ, (gramMat B σ f).PosDef) ∧ ∀ σ, gramMat B (ComplexEmbedding.conjugate σ) f = (gramMat B σ f).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj | exact GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianLatticeDegreeEqBundleDegreeStatement
section
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_degree_eq_bundle_degree : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L)) (Fl : HermLattice L i), LinearIndependent (𝓞 L) f → i = B.rank F → Function.Injective c → (∀ j, c (f j) = Pi.single j 1) → Fl.lattice = LinearMap.range c → (∀ σ, Fl.metric σ = gramMat B σ (fun j => (f j : B.carrier))) → Fl.degree = B.degreeWith F f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith | exact GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LinearIndependentCoordinatesDenominatorStatement
section
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_independent_coordinates_denominator : ∀ (L : Type) [Field L] [NumberField L] (M : Type) [AddCommGroup M] [Module (𝓞 L) M] [Module.Finite (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M] (i : ℕ) (f : Fin i → M), LinearIndependent (𝓞 L) f → i = Module.finrank (𝓞 L) M → ∃ c : M →ₗ[𝓞 L] (Fin i → L), Function.Injective c ∧ (∀ j, c (f j) = Pi.single j 1) ∧ ∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧ ∀ j, (D : L) * c x j = a j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent | exact GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.SpanBaseChangeCoordinatesStatement
section
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_inner_self_eq_gramMat_form : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L)), (∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧ ∀ j, (D : L) * c x j = a j) → ∀ (K : Type) [Field K] [NumberField K] [Algebra L K] (x : Fin i → K), x ∈ Submodule.span (𝓞 K) ((fun (w : Fin i → L) j => algebraMap L K (w j)) '' (LinearMap.range c : Submodule (𝓞 L) (Fin i → L))) → ∃ X : (B.baseChange K).carrier, ∀ τ : K →+* ℂ, ((B.baseChange K).metric.form τ).inner ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) = star (fun j => τ (x j)) ⬝ᵥ (gramMat B (τ.comp (algebraMap L K)) (fun j => (f j : B.carrier)) *ᵥ fun j => τ (x j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.Lift.lift_length | exact GlobalTheory.CompanionTheory.Ar.Lines.Lift.lift_length | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.Lift.lift_length <;> assumption)
end

