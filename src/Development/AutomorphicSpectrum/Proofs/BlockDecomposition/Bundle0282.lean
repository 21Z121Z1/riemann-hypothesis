import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesSubobject
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0267
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0268

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionLocalUnitsStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_quaternion_local_units : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (T : Finset (Pl F)) (y : (u : Pl F) → (Q d β (Kp u))ˣ),
  ∃ Y : (Q d β (AF F))ˣ, (∀ u ∈ T, qmap (proj u) (Y : Q d β (AF F)) = y u) ∧
    ∀ u, u ∉ T → qmap (proj u) (Y : Q d β (AF F)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.LocalUnit.exists_adelic_unit | exact GlobalTheory.CompanionTheory.PlaneSA.LocalUnit.exists_adelic_unit | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.LocalUnit.exists_adelic_unit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionNeighbourhoodStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_quaternion_neighbourhood : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (a : Q d β (AF F)), ∀ V ∈ 𝓝 a,
  ∃ T : Finset (Pl F), ∃ U : (u : Pl F) → Set (Q d β (Kp u)),
    (∀ u, U u ∈ 𝓝 (qmap (proj u) a)) ∧ (∀ w : InfinitePlace F, (Sum.inl w : Pl F) ∈ T) ∧
    ∀ b : Q d β (AF F), (∀ u ∈ T, qmap (proj u) b ∈ U u) →
      (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → IntQ v (qmap (proj (Sum.inr v)) b)) → b ∈ V := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.Box.basic_nhd | exact GlobalTheory.CompanionTheory.PlaneSA.Box.basic_nhd | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.Box.basic_nhd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineRestrictionFunctionsNaturalityStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_restriction_functions_naturality : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; (∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a)) → ∀ (G : Z.Modules) [G.IsQuasicoherent] (m : ℕ), ∃ g : (idealPow I G m).restrict (φ ⁻¹ᵁ V).ι ⟶ idealPow (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m, g ≫ idealPowι (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m = (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) := by
  first | exact @GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift | exact GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift | (intros; apply GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropicUnitaryGroupCompactStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropic_unitary_group_compact : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K], IsField (K ⊗[F] E) → ¬ IsoAt K σ J → IsCompact (Set.univ : Set (HA K σ J)) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.CompactField.isCompact_univ_HA | exact GlobalTheory.CompanionTheory.SaGen.CompactField.isCompact_univ_HA | (intros; apply GlobalTheory.CompanionTheory.SaGen.CompactField.isCompact_univ_HA <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesSubobjectStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_rees_subobject : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] {E : X.Modules}, IsCoherent E → ∀ D : Subobject E, (D : X.Modules).IsQuasicoherent → ∃ k : ℕ, ∀ n : ℕ, D ⊓ powSub I E (n + k) ≤ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n) := by
  first | exact @GlobalTheory.CompanionTheory.GE.artinRees_uniform | exact GlobalTheory.CompanionTheory.GE.artinRees_uniform | (intros; apply GlobalTheory.CompanionTheory.GE.artinRees_uniform <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartRestrictPullBijectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_restrict_pull_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty)
    (r r' : ℤ) (j : ℕ),
    ∃ h : capS (wK q i y s) S ≤ KS q s {⨅ k ∈ S, uy i y k},
      Function.Bijective ((resU (sq (thFil (smFun X q) r) (thFil (smFun X q) r')) h).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.ConeZarCap.main | exact GlobalTheory.CompanionTheory.ConeZarCap.main | (intros; apply GlobalTheory.CompanionTheory.ConeZarCap.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartTensorBaseCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_tensor_base_compat : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (eO (1 ⊗ₜ f))) →
      (∀ f, ev cA.D cA.inV f = Ideal.Quotient.mk _ (eA (1 ⊗ₜ f))) →
      ∃ e₀ : cO.D ⟶ ((nmO γ q).mor 0).obj cA.D, ∀ f, e₀.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := by
  first | exact @GlobalTheory.CompanionTheory.BcMor.chart_mor | exact GlobalTheory.CompanionTheory.BcMor.chart_mor | (intros; apply GlobalTheory.CompanionTheory.BcMor.chart_mor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemPullbackStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_system_pullback : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ClosedSys I ((Scheme.Modules.pullback φ).obj E) (pullSys I φ E S) := by
  first | exact @GlobalTheory.CompanionTheory.GE.closedSys_pullSys | exact GlobalTheory.CompanionTheory.GE.closedSys_pullSys | (intros; apply GlobalTheory.CompanionTheory.GE.closedSys_pullSys <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureConjugationInvariantStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_conjugation_invariant : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, ∀ a ∈ SuppAt d β {w}, ∀ c : (Q d β (AF F))ˣ,
    ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) →
    a ∈ closure (SAQ d β s) := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.MemConj.mem_closure_of_conj_mem | exact GlobalTheory.CompanionTheory.PlaneSA.MemConj.mem_closure_of_conj_mem | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.MemConj.mem_closure_of_conj_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmExtensionImaginaryGeneratorStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_extension_imaginary_generator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∃ d : F, (∀ r : F, r ^ 2 ≠ d) ∧ ∃ ξ : E, ξ ^ 2 = algebraMap F E d ∧ σ ξ = -ξ := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.cm_exists_sqrt_nonsquare | exact GlobalTheory.CompanionTheory.PlaneSA.cm_exists_sqrt_nonsquare | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.cm_exists_sqrt_nonsquare <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSectionIdealPowerStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_section_ideal_power : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) {E : X.Modules} (S : ℕ → Subobject E) (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (n : ℕ), B ⊔ powSub I _ (n + 1) = pullSys I φ E S n → ∀ (V : X.Opens), ∀ x ∈ secs (S n) V, (show Γ(cokernel B.arrow, φ ⁻¹ᵁ V) from (adjMap φ B).app V x) ∈ Set.range ((idealPowι I (cokernel B.arrow) (n + 1)).app (φ ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι | exact GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι | (intros; apply GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompleteModuleNoetherianRealizationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_module_noetherian_realization : ∀ {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B) {N : Type} [AddCommGroup N] [Module B N] [Module.Finite B N] (T : ℕ → Submodule B N), (∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n) → (∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) → ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : Algebra B R) (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module B M) (_ : IsScalarTower B R M) (_ : Module.Finite R M) (μ : N →ₗ[B] M), I.map (algebraMap B R) ≤ Ideal.jacobson ⊥ ∧ Submodule.span R (Set.range μ) = ⊤ ∧ ∀ n e, e ∈ T n ↔ μ e ∈ (I ^ (n + 1) • ⊤ : Submodule B M) := by
  first | exact @GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower | exact GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower | (intros; apply GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower <;> assumption)
end

