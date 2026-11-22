import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneGramMeasurableSection
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle0002
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0050

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneGramMeasurableSectionStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_gram_measurable_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin 1 → Fin M → R ⊗[F] E, IsUnit (gramR R σ J x).det → ∃ s : (Fin 1 → Fin M → R ⊗[F] E) → HA R σ J, Measurable s ∧ (∀ y, gramR R σ J y = gramR R σ J x → actW R σ J (s y) x = y) ∧ ∀ C : Set (Fin 1 → Fin M → R ⊗[F] E), IsCompact C → ∃ C' : Set (HA R σ J), IsCompact C' ∧ ∀ y ∈ C, gramR R σ J y = gramR R σ J x → s y ∈ C' := by
  first | exact @GlobalTheory.CompanionTheory.SW.OrbitSection.orbit_section | exact GlobalTheory.CompanionTheory.SW.OrbitSection.orbit_section | (intros; apply GlobalTheory.CompanionTheory.SW.OrbitSection.orbit_section <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionRationalToAdelic
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TransA

theorem trans_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (X : Fin n → Fin M → E) (Y : Fin n → Fin M → AF F ⊗[F] E), (gramE σ J X).det ≠ 0 →
    gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) →
    ∃ h : HA (AF F) σ J, actW (AF F) σ J h (ratTup (AF F) X) = Y :=
  fun F E _ _ _ _ _ σ hcm M J hJ n =>
    GlobalTheory.T.adelic_orbit_of_rational_tuple F E σ hcm (AF F) (PIW.AdelicOrbitU.stP F) n M J hJ

end GlobalTheory.CompanionTheory.SW.TransA
end

