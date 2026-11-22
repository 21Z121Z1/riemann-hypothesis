import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0036
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0038
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductUnfold
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0039
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalFieldSelfdualMeasureExists
import GroundTheory.LocalFields.LocalFourier

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanLocalDensityFormulaStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_local_density_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Ainf F ⊗[F] E, Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) = cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → ∀ Dinf : (InfinitePlace F → ℝ) → ℝ, Continuous Dinf → (∀ y, 0 ≤ Dinf y) → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → Fin M × Fin d → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) → ∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X) ∂(coordW (Ainf F) b laminf 1 M) = ∫⁻ S in U, ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)))) ∂(coordHerm (Ainf F) σ b laminf 1) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens | exact GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens | (intros; apply GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDisintegrationStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_lintegral_eq_scale_mul_Pint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_fibS_of_mem | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_fibS_of_mem | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_fibS_of_mem <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductFoldStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_product_fold : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n, ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi_at_fibre | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi_at_fibre | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi_at_fibre <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductFubiniStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_Pint' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.measurable_Pint | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.measurable_Pint | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.measurable_Pint <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductNormalizationStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_concentrated_on_fiber : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibS σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))))ᶜ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductScalingStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_integrable_and_integral_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibS σ J t m₁ m' s B₀ a κ₁ cm S) ∧ ∫ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = ((κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) * cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n : ℝ≥0) : ℝ) * Preal σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.integrable_fibS_and_integral | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.integrable_fibS_and_integral | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.integrable_fibS_and_integral <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductUnfoldStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_product_unfold : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ y₀, chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) ∂(m₁ (hermScal R σ (algebraMap F R t))) ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1.first_step | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1.first_step | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1.first_step <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductUniquenessStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_preal_units_of_hasCompactSupport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → ContinuousOn (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Preal σ J t m₁ m' s φ z.1 z.2.1 z.2.2) ({α : R | IsUnit α} ×ˢ (Set.univ ×ˢ Unt σ R n)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo.cont_double | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo.cont_double | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo.cont_double <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureDisintegrationFormulaStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_measure_disintegration_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ S : HermR R σ n, IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ B : Set (HermR R σ n), IsOpen B ∧ S ∈ B ∧ (∀ S' ∈ B, IsUnit (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (gramR R σ J ⁻¹' (Subtype.val '' B)) ν B fib := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramNear.exists_fibre_near | exact GlobalTheory.CompanionTheory.SW.GramNear.exists_fibre_near | (intros; apply GlobalTheory.CompanionTheory.SW.GramNear.exists_fibre_near <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresIntegralFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ScaleCont

section Actions

variable {K : Type} [CommRing K] {n M : ℕ}

def tupR (X : Fin n → Fin M → K) (g : Matrix (Fin n) (Fin n) K) : Fin n → Fin M → K :=
  fun a i => ∑ c, X c i * g c a

theorem tupR_tupR (X : Fin n → Fin M → K) (g h : Matrix (Fin n) (Fin n) K) :
    tupR (tupR X g) h = tupR X (g * h) := by
  funext a i
  simp only [tupR, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

theorem tupR_one (X : Fin n → Fin M → K) : tupR X 1 = X := by
  funext a i
  simp [tupR, Matrix.one_apply]

def tupAction : DistribMulAction (GL (Fin n) K) (Fin n → Fin M → K) where
  smul q X := tupR X ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  one_smul X := by
    show tupR X (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = X
    simp [tupR_one]
  mul_smul q q' X := by
    show tupR X (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tupR (tupR X ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [tupR_tupR, mul_inv_rev, Units.val_mul]
  smul_zero q := by
    show tupR 0 _ = 0
    funext a i
    simp [tupR]
  smul_add q X Y := by
    show tupR (X + Y) _ = tupR X _ + tupR Y _
    funext a i
    simp [tupR, add_mul, Finset.sum_add_distrib]

theorem cT_one' (s : K →+* K) : cT s (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp [cT, Matrix.map_one]

theorem cT_mul' (s : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    cT s (A * B) = cT s B * cT s A := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

def hermAction (s : K →+* K) (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hmem : ∀ (S : H) (g : Matrix (Fin n) (Fin n) K),
      cT s g * (S : Matrix (Fin n) (Fin n) K) * g ∈ H) :
    DistribMulAction (GL (Fin n) K) H where
  smul q S := ⟨cT s ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (S : Matrix (Fin n) (Fin n) K) * ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hmem S _⟩
  one_smul S := by
    apply Subtype.ext
    show cT s (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (S : Matrix (Fin n) (Fin n) K) * (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = S
    simp [cT_one']
  mul_smul q q' S := by
    apply Subtype.ext
    show cT s (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (S : Matrix (Fin n) (Fin n) K) * (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      cT s ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (cT s ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (S : Matrix (Fin n) (Fin n) K) * ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [mul_inv_rev, Units.val_mul, cT_mul']
    simp only [Matrix.mul_assoc]
  smul_zero q := by
    apply Subtype.ext
    show cT s _ * ((0 : H) : Matrix (Fin n) (Fin n) K) * _ = 0
    simp
  smul_add q S T := by
    apply Subtype.ext
    show cT s _ * ((S + T : H) : Matrix (Fin n) (Fin n) K) * _ =
      cT s _ * (S : Matrix (Fin n) (Fin n) K) * _ + cT s _ * (T : Matrix (Fin n) (Fin n) K) * _
    simp [Matrix.mul_add, Matrix.add_mul]

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_inv_val :
    Continuous fun q : GL (Fin n) K => ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  Units.continuous_val.comp continuous_inv

theorem tup_continuousSMul :
    @ContinuousSMul (GL (Fin n) K) (Fin n → Fin M → K) (tupAction (K := K)).toSMul _ _ := by
  letI := tupAction (K := K) (n := n) (M := M)
  refine ⟨?_⟩
  show Continuous fun p : GL (Fin n) K × (Fin n → Fin M → K) =>
    tupR p.2 ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [tupR]
  refine continuous_finset_sum _ fun c _ => ?_
  refine Continuous.mul ?_ ?_
  · exact (continuous_apply i).comp ((continuous_apply c).comp continuous_snd)
  · exact (continuous_apply a).comp ((continuous_apply c).comp (continuous_inv_val.comp continuous_fst))

theorem herm_continuousSMul (s : K →+* K) (hs : Continuous s)
    (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hmem : ∀ (S : H) (g : Matrix (Fin n) (Fin n) K),
      cT s g * (S : Matrix (Fin n) (Fin n) K) * g ∈ H) :
    @ContinuousSMul (GL (Fin n) K) H (hermAction s H hmem).toSMul _ _ := by
  letI := hermAction s H hmem
  refine ⟨?_⟩
  have hq : Continuous fun p : GL (Fin n) K × H =>
      ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := continuous_inv_val.comp continuous_fst
  have hS : Continuous fun p : GL (Fin n) K × H => (p.2 : Matrix (Fin n) (Fin n) K) :=
    continuous_subtype_val.comp continuous_snd
  have hc : Continuous fun p : GL (Fin n) K × H =>
      cT s ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simp only [cT]
    exact (hq.matrix_map hs).matrix_transpose
  exact ((hc.matrix_mul hS).matrix_mul hq).subtype_mk _

end Actions

theorem fibre_scale_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∃ κ : GL (Fin n) (R ⊗[F] E) → ℝ≥0, Continuous κ ∧ (∀ g, κ g ≠ 0) ∧ κ 1 = 1 ∧ ∀ (g : GL (Fin n) (R ⊗[F] E)) (S S' : HermR R σ n), (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → m S' = κ g • (m S).map (fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm
  obtain ⟨r1, r2, r3, r4, -⟩ := id hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨k1, k2, k3, k4, k5, -, -, k8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := k1
  haveI := k2
  haveI := k3
  haveI := k4
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := k8 n M
  have hmem := (GlobalTheory.T.gram_right_action_identities F E σ hCM M J hJ R n).2.2.2.1
  letI a1 : DistribMulAction (GL (Fin n) (R ⊗[F] E)) (Fin n → Fin M → R ⊗[F] E) := tupAction
  haveI c1 : ContinuousSMul (GL (Fin n) (R ⊗[F] E)) (Fin n → Fin M → R ⊗[F] E) := tup_continuousSMul
  obtain ⟨χ₁, hχ₁c, hχ₁⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action (Fin n → Fin M → R ⊗[F] E) μ (GL (Fin n) (R ⊗[F] E))
  letI a2 : DistribMulAction (GL (Fin n) (R ⊗[F] E)) (HermR R σ n) :=
    hermAction (sigR R σ) (HermR R σ n) hmem
  haveI c2 : ContinuousSMul (GL (Fin n) (R ⊗[F] E)) (HermR R σ n) :=
    herm_continuousSMul (sigR R σ) k5 (HermR R σ n) hmem
  obtain ⟨χ₂, hχ₂c, hχ₂⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action (HermR R σ n) ν (GL (Fin n) (R ⊗[F] E))
  have hne : ∀ (χ : GL (Fin n) (R ⊗[F] E) →* ℝ≥0) (g), χ g ≠ 0 := by
    intro χ g h0
    have : χ (g * g⁻¹) = 1 := by simp
    rw [map_mul, h0, zero_mul] at this
    exact zero_ne_one this
  refine ⟨fun g => χ₁ g * χ₂ g⁻¹, hχ₁c.mul (hχ₂c.comp continuous_inv), ?_, ?_, ?_⟩
  · exact fun g => mul_ne_zero (hne χ₁ g) (hne χ₂ g⁻¹)
  · simp
  · intro g S S' hS'
    let τ : HermR R σ n → HermR R σ n := fun S => g⁻¹ • S
    have hτ : ∀ S : HermR R σ n, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * S *
          (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
      intro S
      show cT (sigR R σ) (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * S *
        (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = _
      rw [inv_inv]
    have hS'τ : S' = τ S := Subtype.ext (hS'.trans (hτ S).symm)
    have hmap₁ : μ.map (fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) = χ₁ g⁻¹ • μ := by
      have := hχ₁ g⁻¹
      have e : (fun v : Fin n → Fin M → R ⊗[F] E => g⁻¹ • v) =
          fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
        funext X
        show tupR X (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = _
        rw [inv_inv]
        rfl
      rwa [e] at this
    have hmap₂ : ν.map τ = χ₂ g⁻¹ • ν := hχ₂ g⁻¹
    have key := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hCM M J hJ R hR n μ ν m hμ hν hm
      (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (Matrix.isUnits_det_units g) τ hτ
      (χ₁ g⁻¹) (χ₂ g⁻¹) hmap₁ hmap₂ S
    rw [hS'τ]
    have hinv : χ₁ g * χ₁ g⁻¹ = 1 := by rw [← map_mul]; simp
    calc m (τ S) = (χ₁ g * χ₁ g⁻¹) • m (τ S) := by rw [hinv, one_smul]
      _ = χ₁ g • (χ₁ g⁻¹ • m (τ S)) := by rw [mul_smul]
      _ = χ₁ g • (χ₂ g⁻¹ • (m S).map fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
        rw [key]
      _ = _ := by rw [mul_smul]

end GlobalTheory.CompanionTheory.SW.ScaleCont
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianLocalContinuousCongruenceSectionStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_local_continuous_congruence_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (B : Set (HermR R σ n)) (g : HermR R σ n → GL (Fin n) (R ⊗[F] E)), IsOpen B ∧ S ∈ B ∧ ContinuousOn g B ∧ g S = 1 ∧ ∀ S' ∈ B, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_local_section | exact GlobalTheory.CompanionTheory.SW.exists_local_section | (intros; apply GlobalTheory.CompanionTheory.SW.exists_local_section <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalFieldSelfdualMeasureExistsStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_field_selfdual_measure_exists : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (ψ : AddChar K Circle), Continuous ψ → ψ ≠ 1 → SelfDual (GroundTheory.LocalField.selfDualMeasure ψ) (fun s t => ((ψ (s * t) : Circle) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure | exact GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure | (intros; apply GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure <;> assumption)
end

