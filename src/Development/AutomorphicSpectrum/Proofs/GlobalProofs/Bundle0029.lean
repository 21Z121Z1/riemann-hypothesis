import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitLogLatticeBoundedTranslate

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RealDifferenceConeBoundStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_continuation_from_strips : ∀ (S : ℂ → ℂ) (G : ℕ → ℂ → ℂ), (∀ k, DifferentiableOn ℂ (G k) {s | -(k : ℝ) < s.re}) →
  (∀ k s, 1 < s.re → G k s = S s) → ∃ T : ℂ → ℂ, Differentiable ℂ T ∧ ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → T s = G k s := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue.entire_of_halfPlane_continuations | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue.entire_of_halfPlane_continuations | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue.entire_of_halfPlane_continuations <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniConeDecompositionStatement
section
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_cone_decomposition : ∀ {F : Type} [Field F] [NumberField F] (P : Set F) (Q : Set F → Prop) (C : Set F), Tile P Q C → (0 : F) ∉ C →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), (∀ c, 0 < r c) ∧
      (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, v c i ∈ P) ∧ (∀ c, openCone (v c) ⊆ C) ∧
      ∀ x ∈ C, ∃! c, x ∈ openCone (v c) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.tile_family_closed | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.tile_family_closed | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.tile_family_closed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SizePowerLeInverseSquareProductStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_power_le_inverse_square_product : ∀ (r n B N : ℕ) (cs : List (Fin r)) (m : Fin r → ℕ), n * B + 2 ≤ N → (∀ i, cs.count i = N ∨ m i = 0) →
  sizeE (fun i => (m i : ℝ)) ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableInverseSquareProductStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_inverse_square_product : ∀ r : ℕ, Summable (fun m : Fin r → ℕ => ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyPositiveBasisRatioBoundStatement
section
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_positive_basis_ratio_bound : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) →
    ∃ R : ℝ, 0 < R ∧ ∀ x : F, (∀ i, 0 < b.repr x i) → ∀ σ τ : F →+* ℝ, σ x ≤ R * τ x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyRealFieldDenseEmbeddingsStatement
section
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_real_field_dense_embeddings : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (F →+* ℝ) → ℝ) (ε : ℝ), 0 < ε → ∃ x : F, ∀ σ : F →+* ℝ, |σ x - y σ| < ε := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitLogLatticeBoundedTranslateStatement
section
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_log_lattice_bounded_translate : ∀ (F : Type) [Field F] [NumberField F] (e : ℕ), 0 < e → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : logSpace F, ∃ u : (𝓞 F)ˣ,
    ∀ w, |y w + (e : ℝ) * logEmbedding F (Additive.ofMul u) w| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice.multiples_relativelyDense | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice.multiples_relativelyDense | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.UnitLattice.multiples_relativelyDense <;> assumption)
end

