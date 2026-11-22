import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0009
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationSheafGlueModulesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_sheaf_glue_modules : ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : {g : R // ∃ i, f i ∣ g} → Type) [∀ g, AddCommGroup (F g)] [∀ g, Module R (F g)]
    (res : ∀ g g' : {g : R // ∃ i, f i ∣ g}, g.1 ∣ g'.1 → (F g →ₗ[R] F g'))
    (ρ : ∀ g, E →ₗ[R] F g),
    (∀ g (h : g.1 ∣ g.1) y, res g g h y = y) →
    (∀ g g' g'' (h : g.1 ∣ g'.1) (h' : g'.1 ∣ g''.1) (h'' : g.1 ∣ g''.1) y, res g' g'' h' (res g g' h y) = res g g'' h'' y) →
    (∀ g g' (h : g.1 ∣ g'.1) e, res g g' h (ρ g e) = ρ g' e) →
    (∀ g (a : R), a ∣ g.1 → IsUnit (algebraMap R (Module.End R (F g)) a)) →
    (∀ g g' (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t → IsLocalizedModule (Submonoid.powers t) (res g g' h)) →
    (∀ e, (∀ i, ρ ⟨f i, i, dvd_rfl⟩ e = 0) → e = 0) →
    (∀ w : ∀ i, F ⟨f i, i, dvd_rfl⟩,
      (∀ i j, res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (w i) =
        res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (w j)) →
      ∃ e, ∀ i, ρ ⟨f i, i, dvd_rfl⟩ e = w i) →
    ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (ρ ⟨f i, i, dvd_rfl⟩) := by
  first | exact @GlobalTheory.CompanionTheory.BasicCover.isLocalizedModule_of_basic_cover | exact GlobalTheory.CompanionTheory.BasicCover.isLocalizedModule_of_basic_cover | (intros; apply GlobalTheory.CompanionTheory.BasicCover.isLocalizedModule_of_basic_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizedModuleBaseChangeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localized_module_base_change : ∀ (R P C C' : Type) [CommRing R] [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (f t : R) [AddCommGroup P] [Module R P]
  [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P] [Module.Finite (Localization.Away f) P]
  [Module.Projective (Localization.Away f) P], IsUnit (algebraMap R C f) → ∀ c : C →ₐ[R] C',
  IsLocalizedModule (Submonoid.powers t) c.toLinearMap →
  IsLocalizedModule (Submonoid.powers t) (LinearMap.compRight R c.toLinearMap : (P →ₗ[R] C) →ₗ[R] (P →ₗ[R] C')) := by
  first | exact @GlobalTheory.CompanionTheory.LocHom.isLocalizedModule_compRight_away | exact GlobalTheory.CompanionTheory.LocHom.isLocalizedModule_compRight_away | (intros; apply GlobalTheory.CompanionTheory.LocHom.isLocalizedModule_compRight_away <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuFactorsGenerateSameFieldStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lu_factors_generate_same_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (A : Matrix (Fin n) (Fin n) K) (u v w : Matrix (Fin n) (Fin n) L), A.det ≠ 0 → (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) → (∀ k, v k k = 1) → (∀ l k, l < k → v l k = 0) → (∀ l k, k < l → w l k = 0) → (∀ k, w k k ≠ 0) → A.map (algebraMap K L) * u = v * w → IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => u p.1 p.2) = IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => v p.1 p.2) := by
  first | exact @GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq | exact GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq | (intros; apply GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_ideal_membership_of_local : ∀ {K : Type} [Field K] (R : Subring K) [IsLocalRing R] (P : Ideal (integralClosure R K).toSubring), P.IsMaximal → ∀ (t : (integralClosure R K).toSubring), (t : K) ∈ R → (t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ R)) := by
  first | exact @GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem | exact GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem | (intros; apply GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemSpanOfIotaMultiProportionalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_of_iota_multi_proportional : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (b e : Fin n → V) (t : Ω), LinearIndependent Ω e → t ≠ 0 → exteriorPower.ιMulti Ω n b = t • exteriorPower.ιMulti Ω n e → ∀ i, b i ∈ Submodule.span Ω (Set.range e) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional | exact GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional | (intros; apply GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultiplicativeDerivationRankStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_derivation_rank : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R] (D : Derivation k R R) (ε : R →ₐ[k] k),
    (∀ a : R, (⇑D)^[p] a = D a) → ∀ z₀ : R, IsUnit z₀ → D z₀ = z₀ →
      Module.finrank k R = p * Module.finrank k (LinearMap.ker (D : R →ₗ[k] R)) ∧
      ∃ z : R, ε (D z) ≠ 0 ∧ ∀ u : R →ₗ[k] k, (∀ a b : R, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : R, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PowerDerivation.finrank_eq_and_derivation_eq_zero | exact GlobalTheory.CompanionTheory.PowerDerivation.finrank_eq_and_derivation_eq_zero | (intros; apply GlobalTheory.CompanionTheory.PowerDerivation.finrank_eq_and_derivation_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NilpotentDerivationRankStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_derivation_rank : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R] (D : Derivation k R R) (ε : R →ₐ[k] k),
    (∀ a : R, (⇑D)^[p] a = 0) → ∀ t : R, IsUnit ((⇑D)^[p - 1] t) →
      Module.finrank k R = p * Module.finrank k (LinearMap.ker (D : R →ₗ[k] R)) ∧
      ∃ z : R, ε (D z) ≠ 0 ∧ ∀ u : R →ₗ[k] k, (∀ a b : R, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : R, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.DerivFree.finrank_and_vanishing | exact GlobalTheory.CompanionTheory.Ggeo.DerivFree.finrank_and_vanishing | (intros; apply GlobalTheory.CompanionTheory.Ggeo.DerivFree.finrank_and_vanishing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonarchValuationOfPrimeStatement
section
open NumberField IsDedekindDomain UniqueFactorizationMonoid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonarch_valuation_of_prime : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (μ : R →*₀ ℝ) (a : R), a ≠ 0 → (∀ x, 0 ≤ μ x) → (∀ x, μ x ≤ 1) → (∀ x y, μ (x + y) ≤ max (μ x) (μ y)) → μ a < 1 → μ a ≠ 0 → ∃ (P : Ideal R) (c : ℝ), P.IsPrime ∧ P ≠ ⊥ ∧ a ∈ P ∧ 0 < c ∧ ∀ x : R, x ≠ 0 → μ x = c ^ (normalizedFactors (Ideal.span {x})).count P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.map_eq_pow_count_of_ultrametric | exact GlobalTheory.CompanionTheory.Ggeo.map_eq_pow_count_of_ultrametric | (intros; apply GlobalTheory.CompanionTheory.Ggeo.map_eq_pow_count_of_ultrametric <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldMapsLocalRingUniqueStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_maps_local_ring_unique : ∀ (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B] [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B), π.comp s = π.comp t → s = t := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | exact GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolynomialFieldExtensionDegree
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.polynomial_field_extension_degree : ∀ (κ K L I : Type) [Field κ] [Field K] [Field L] [Algebra K L] (ψ : κ ≃+* K) (T : I → L), AlgebraicIndependent K T → ∃ φ : FractionRing (MvPolynomial I κ) →+* L, (∀ a, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.C a)) = algebraMap K L (ψ a)) ∧ (∀ i, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.X i)) = T i) ∧ (letI := φ.toAlgebra; Module.finrank (FractionRing (MvPolynomial I κ)) L) = Module.finrank (IntermediateField.adjoin K (Set.range T)) L := by
  first | exact @ModelDimension.polynomial_fraction_field_degree | exact ModelDimension.polynomial_fraction_field_degree
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIdealExtensionLocalDomainStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_ideal_extension_local_domain : ∀ (R B : Type) [CommRing R] [IsDedekindDomain R] [CommRing B] [IsDomain B] [IsNoetherianRing B] (u : R →+* B), u.FiniteType → (∀ p : Ideal R, p.IsMaximal → ∀ a b : B, a * b ∈ p.map u → a ∈ p.map u ∨ b ∈ p.map u) → ∀ (f : B) (d : R), d ≠ 0 → (∀ m : Ideal B, m.IsMaximal → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (ψ : B →+* O), (∀ b, b ∉ m → IsUnit (ψ b)) ∧ (∀ b ∈ m, ¬ IsUnit (ψ b)) ∧ Function.Injective (ψ.comp u) ∧ ∃ c, ψ f = ψ (u d) * c) → ∃ a, f = u d * a := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local | exact GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local | (intros; apply GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalizationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_mem_iff_not_unit_localization : ∀ {K : Type} [Field K] (T : Subring K) (P : Ideal T) (_ : P.IsPrime) (t : T), t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ (LocalSubring.ofPrime T P).toSubring) := by
  first | exact @GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem | exact GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem | (intros; apply GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem <;> assumption)
end

