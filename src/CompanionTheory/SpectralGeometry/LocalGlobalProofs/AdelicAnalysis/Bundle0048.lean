import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0047
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianDiagonalizeOverReducedTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0015
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductPushforwardStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_iterated_lintegral_eq_Mid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ S, ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) ∂(coordHerm R σ b lam (n + 1)) = Mid σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.Fold.fold | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.Fold.fold | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.Fold.fold <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRing
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.WittTuples

theorem exists_actW_eq_of_gramR_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = gramR R σ J Y → IsUnit (gramR R σ J X).det → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ n X Y hXY hdet
  have hσ := HermTop.sigma_sigma hCM
  have hS : cT (sigR R σ) (gramR R σ J X) = gramR R σ J X := by
    ext a b
    exact HermTop.gramR_mem (R := R) hσ hJ.1 X a b
  obtain ⟨g, D, hg⟩ := GlobalTheory.CompanionTheory.SW.exists_diagonal_congr F E σ hCM R n _ hS hdet
  have hgram : ∀ Z : Fin n → Fin M → R ⊗[F] E, gramR R σ J (rmul R Z (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * gramR R σ J Z * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    fun Z => (GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J Z g 1).1
  have hX' := (hgram X).trans hg
  have hY' : gramR R σ J (rmul R Y (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      gramR R σ J (rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    rw [hgram, hgram, hXY]
  obtain ⟨h, hh⟩ := GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag F E σ hCM R (GlobalTheory.CompanionTheory.SW.unitChoice_of_isArtinianRing_isReduced R) M J hJ n D _ _ hX' hY'
  refine ⟨h, ?_⟩
  have hk : actTup R (HA.mat R σ J h) (rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      rmul R (actTup R (HA.mat R σ J h) X) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    (GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J X g 1).2.2.2 _
  have he : rmul R (actW R σ J h X) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      rmul R Y (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := hk.symm.trans hh
  have hcancel : ∀ Z : Fin n → Fin M → R ⊗[F] E,
      rmul R (rmul R Z (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ((g⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = Z := by
    intro Z
    have h1 := GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J Z g ((g⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [h1.2.1, Units.mul_inv, h1.2.2.1]
  rw [← hcancel (actW R σ J h X), he, hcancel]

end GlobalTheory.CompanionTheory.SW.WittTuples
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionDiagonalGramTuplesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_extension_diagonal_gram_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R], PIW.AdelicOrbitU.UnitChoice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (D : Fin n → Rˣ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D i : R)) → gramR R σ J Y = gramR R σ J X → ∃ h : HA R σ J, actW R σ J h X = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag | exact GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag | (intros; apply GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag <;> assumption)
end

