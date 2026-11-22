import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0067
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityNearOne

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingCocompactDiscreteNumberField
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.FieldCocompact

theorem discrete_cocompact : ∀ (F : Type) [Field F] [NumberField F],
    (∃ C : Set (AdeleRing (𝓞 F) F), IsCompact C ∧
      ∀ y, ∃ l : F, y - algebraMap F (AdeleRing (𝓞 F) F) l ∈ C) ∧
    (∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C →
      {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite) ∧
    NoncompactSpace (AdeleRing (𝓞 F) F) := by
  intro F _ _
  have hfin : ∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C →
      {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite := fun C hC =>
    GlobalTheory.Eis.Conv.Discr.finite_of_isCompact (algebraMap F (AdeleRing (𝓞 F) F))
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F) hC
  refine ⟨GlobalTheory.AdeleCocompact.exists_compact_adele F, hfin, ⟨fun h => ?_⟩⟩
  have h1 := hfin Set.univ h
  simp only [Set.mem_univ, Set.setOf_true] at h1
  exact Set.infinite_univ h1

end GlobalTheory.CompanionTheory.Adelic.FieldCocompact
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanSelfdualMeasurePiStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_selfdual_measure_pi : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ k : Measure (Ainf F), SelfDual k (fun s t => psiInf F ψ (s * t)) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => k) (fun x y => psiInf F ψ (x ⬝ᵥ y)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.selfDual_pi_inf | exact GlobalTheory.CompanionTheory.SW.selfDual_pi_inf | (intros; apply GlobalTheory.CompanionTheory.SW.selfDual_pi_inf <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanSelfdualSymmetricFormUniqueStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_selfdual_symmetric_form_unique : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ k : Measure (Ainf F), SelfDual k (fun s t => psiInf F ψ (s * t)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.IsSymm → A.det ≠ 0 → ∀ μ ν : Measure (ι → Ainf F), SelfDual μ (fun x y => psiInf F ψ (x ⬝ᵥ (A.map (algebraMap F (Ainf F)) *ᵥ y))) → SelfDual ν (fun x y => psiInf F ψ (x ⬝ᵥ (A.map (algebraMap F (Ainf F)) *ᵥ y))) → μ = ν := by
  first | exact @GlobalTheory.CompanionTheory.SW.selfDual_rationalForm_Ainf_unique | exact GlobalTheory.CompanionTheory.SW.selfDual_rationalForm_Ainf_unique | (intros; apply GlobalTheory.CompanionTheory.SW.selfDual_rationalForm_Ainf_unique <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityNearOneStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_quadratic_density_near_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ M : ℕ, Fintype.card ι = 2 * M → 1 ≤ M → ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) + 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) ∧ ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < 1} → (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  first | exact @GlobalTheory.CompanionTheory.SW.LGPrim.density_primitive | exact GlobalTheory.CompanionTheory.SW.LGPrim.density_primitive | (intros; apply GlobalTheory.CompanionTheory.SW.LGPrim.density_primitive <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.NonarchimedeanSelfdualSymmetricFormUniqueStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonarchimedean_selfdual_symmetric_form_unique : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Measure (Fv F v)), SelfDual k (fun s t => psiV F ψ v (s * t)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.IsSymm → A.det ≠ 0 → ∀ μ ν : Measure (ι → Fv F v), SelfDual μ (fun x y => psiV F ψ v (x ⬝ᵥ (A.map (algebraMap F (Fv F v)) *ᵥ y))) → SelfDual ν (fun x y => psiV F ψ v (x ⬝ᵥ (A.map (algebraMap F (Fv F v)) *ᵥ y))) → μ = ν := by
  first | exact @GlobalTheory.CompanionTheory.SW.SdUniq.selfDual_unique_coord | exact GlobalTheory.CompanionTheory.SW.SdUniq.selfDual_unique_coord | (intros; apply GlobalTheory.CompanionTheory.SW.SdUniq.selfDual_unique_coord <;> assumption)
end

