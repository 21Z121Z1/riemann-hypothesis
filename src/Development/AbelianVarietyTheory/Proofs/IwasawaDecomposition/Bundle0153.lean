import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Formalism.LocalToGlobal.HermitianForms.Bundle0003
import Formalism.LocalToGlobal.Columns.RecLevelLocT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorPrimeContractionMaximal
section
open IsLocalRing TensorProduct

namespace GlobalTheory.BaseChangeLoc

theorem localization_atPrime_tensor (A C R : Type) [CommRing A] [CommRing C] [CommRing R] [Algebra A C]
    [Algebra A R] (Q : Ideal (C ⊗[A] R)) [Q.IsPrime] :
    ∃ (Q' : Ideal (Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) ⊗[A] R))
      (_ : Q'.IsPrime),
      Q'.comap (Algebra.TensorProduct.includeLeft :
        Localization.AtPrime (Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R)) →ₐ[A] _ ⊗[A] R) =
          maximalIdeal _ ∧
      (IsDomain (Localization.AtPrime Q') → IsIntegrallyClosed (Localization.AtPrime Q') →
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) := by
  set P : Ideal C := Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) with hP
  let B := Localization.AtPrime P
  let φ : C ⊗[A] R →ₐ[A] B ⊗[A] R :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A C B) (AlgHom.id A R)
  letI : Algebra (C ⊗[A] R) (B ⊗[A] R) := φ.toRingHom.toAlgebra
  have hφ : ∀ x, algebraMap (C ⊗[A] R) (B ⊗[A] R) x = φ x := fun _ => rfl
  haveI : IsScalarTower C (C ⊗[A] R) (B ⊗[A] R) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [hφ]
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have H : (algebraMap (C ⊗[A] R) (B ⊗[A] R)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext r
    simp [hφ, φ]
  let M : Submonoid (C ⊗[A] R) := Algebra.algebraMapSubmonoid (C ⊗[A] R) P.primeCompl
  haveI hL : IsLocalization M (B ⊗[A] R) :=
    IsLocalization.tensorProduct_tensorProduct A R P.primeCompl B H
  have hdisj : Disjoint (M : Set (C ⊗[A] R)) (Q : Set (C ⊗[A] R)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ h
    exact hc h
  have hQ' := IsLocalization.isPrime_of_isPrime_disjoint M (B ⊗[A] R) Q inferInstance hdisj
  have hc := IsLocalization.comap_map_of_isPrime_disjoint M (B ⊗[A] R) (inferInstance : Q.IsPrime) hdisj
  refine ⟨Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)), hQ', ?_, ?_⟩
  · haveI := hQ'
    have hne : (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R))).comap
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) ≠ ⊤ :=
      Ideal.IsPrime.ne_top inferInstance
    symm
    refine (IsLocalRing.maximalIdeal.isMaximal B).eq_of_le hne ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro c hcP
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e1 : (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) (algebraMap C B c) =
        algebraMap (C ⊗[A] R) (B ⊗[A] R) ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) c) := by
      simp [hφ, φ]
    rw [e1]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp hcP)
  · intro h3 h4
    have h1 := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)))) (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)))
    have h2 : IsLocalization Q.primeCompl
        (Localization.AtPrime (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R)))) := by
      convert h1 using 1
      ext x
      simp [Ideal.primeCompl, hc]
    let e : Localization.AtPrime (Q.map (algebraMap (C ⊗[A] R) (B ⊗[A] R))) ≃ₐ[C ⊗[A] R]
        Localization.AtPrime Q :=
      IsLocalization.algEquiv Q.primeCompl _ _
    exact ⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

end GlobalTheory.BaseChangeLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryScalarEqOneModOfFixesSimpleModuleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryScalar_eq_one_mod_of_fixes_simple_module : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : Module.finrank F E = 2) (_ : ∀ x, σ (σ x) = x) (_ : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    (_ : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (_ : T.Prime)
    (_ : ∀ a : v.adicCompletionIntegers F, Valued.v (a : v.adicCompletion F) < 1 → ∃ b : v.adicCompletionIntegers F, a = (T : v.adicCompletionIntegers F) * b)
    (M : Type) [AddCommGroup M] [Module (intV E v) M] (_ : Nat.card M = T) (m : M) (_ : m ≠ 0) (d c : intV E v) (_ : (d - 1) • m = 0)
    (_ : sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F)),
    ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F) := by
  first | exact @GlobalTheory.UnitaryScalarModT.eq_one_add_of_fixes | exact GlobalTheory.UnitaryScalarModT.eq_one_add_of_fixes | (intros; apply GlobalTheory.UnitaryScalarModT.eq_one_add_of_fixes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiser
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeUnifVal

open Formalism.L2.Host

theorem localIdele_eq_locM {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) :
    localIdele E v x = Units.map (Formalism.L2.NC.locM v) x := by
  rfl

theorem at_val_and_unr_iff : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (h : Formalism.L2.NC.HC E), h.χ = (χ : Ideles E →* ℂˣ) → ∀ (v : HeightOneSpectrum (𝓞 E)), (χ.UnrAt v → h.At v (χ.val v)) ∧ (χ.UnrAt v ↔ h.Unr v) := by
  intro E _ _ χ h hχ v
  have hloc : ∀ x : (v.adicCompletion E)ˣ, χ.loc v x = h.χ (Units.map (Formalism.L2.NC.locM v) x) := by
    intro x
    rw [hχ, ← localIdele_eq_locM]
    rfl
  have hiff : χ.UnrAt v ↔ h.Unr v := by
    constructor
    · intro hu u hu1
      rw [← hloc]
      exact hu u hu1
    · intro hu u hu1
      rw [hloc]
      exact hu u hu1
  refine ⟨fun hu => ⟨hiff.1 hu, fun ϖ hϖ => ?_⟩, hiff⟩
  have hs := unif_spec v
  unfold IsUnifAt at hs
  have hq : IsUnitAt v (ϖ * (atFin v (unif v))⁻¹) := by
    unfold IsUnitAt
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hs, hϖ, mul_inv_cancel₀ (WithZero.exp_ne_zero)]
  have h1 := hu _ hq
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  rw [← hloc, h1]
  rfl

end GlobalTheory.HeckeUnifVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeIntegralColumnMinorExpansionStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylLattice_integral_columnMinor_expansion : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N), (∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) →
    ∀ f : MvPolynomial (Fin N × Fin N) ℤ, f ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r) →
    ∃ z : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ,
      (∀ J, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) =
        (z J : ℚ) * Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))) ∧
      ∑ J, z J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = f := by
  first | exact @GlobalTheory.WeylIntExpansion.weyl_int_expansion | exact GlobalTheory.WeylIntExpansion.weyl_int_expansion | (intros; apply GlobalTheory.WeylIntExpansion.weyl_int_expansion <;> assumption)
end

