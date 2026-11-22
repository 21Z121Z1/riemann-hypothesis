import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocallyFinite
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0055
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0054
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0056
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0057
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocallyFiniteStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_pure_tensor_eq_prod_of_isEulerProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → IsLocallyFiniteMeasure minf → (∀ v, IsLocallyFiniteMeasure (m v)) → ∀ (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf → Measurable Φ ∧ Integrable Φ I ∧ Multipliable (fun v => ∫ X, Φv v X ∂(m v)) ∧ ∫ X, Φ X ∂I = (∫ X, Φinf X ∂minf) * ∏' v, ∫ X, Φv v X ∂(m v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerInt.euler_int | exact GlobalTheory.CompanionTheory.SW.EulerInt.euler_int | (intros; apply GlobalTheory.CompanionTheory.SW.EulerInt.euler_int <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZeroStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_measure_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (IsEulerProd b I c minf m → I = 0 → c = 0 ∨ minf = 0 ∨ ∃ v, m v = 0) ∧ (IsEulerProd b I c minf m → (minf = 0 ∨ ∃ v, m v = 0) → I = 0) ∧ ((∀ v, m v (latV b v) < ⊤) → Summable (fun v => |(m v (latV b v)).toReal - 1|) → (minf = 0 ∨ ∃ v, m v = 0) → IsEulerProd b 0 c minf m) := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero | exact GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero | (intros; apply GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarEqProductLocalMeasures
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.WBox

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def cK (R : Type) [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E)
    (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

theorem cK_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (y : R ⊗[F] E) (k : Fin d) :
    cK R' b (Algebra.TensorProduct.map f (AlgHom.id F E) y) k = f (cK R b y k) := by
  induction y with
  | zero => simp [cK]
  | add x y hx hy =>
    simp only [cK] at hx hy ⊢
    simp [map_add, hx, hy]
  | tmul r e =>
    simp [cK, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R] {d : ℕ} {b : Module.Basis (Fin d) F E}

def eK (hK : IsHomeomorph (cK (F := F) (E := E) R b)) : (R ⊗[F] E) ≃ᵐ (Fin d → R) :=
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  (hK.homeomorph _).toMeasurableEquiv

def eW (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ᵐ (Fin n × Fin M × Fin d → R) where
  toFun X p := eK R hK (X p.1 p.2.1) p.2.2
  invFun Y a i := (eK R hK).symm fun k => Y (a, i, k)
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext p
    simp
  measurable_toFun := measurable_pi_lambda _ fun p =>
    (measurable_pi_apply p.2.2).comp ((eK R hK).measurable.comp
      ((measurable_pi_apply p.2.1).comp (measurable_pi_apply p.1)))
  measurable_invFun := measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun i =>
    (eK R hK).symm.measurable.comp (measurable_pi_lambda _ fun k => measurable_pi_apply (a, i, k))

theorem eW_apply (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (n M : ℕ)
    (X : Fin n → Fin M → R ⊗[F] E) (p : Fin n × Fin M × Fin d) :
    eW R hK n M X p = cK R b (X p.1 p.2.1) p.2.2 := rfl

theorem coordK_eq (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R) :
    coordK R b lam = (Measure.pi fun _ : Fin d => lam).map (eK R hK).symm := by
  rw [MeasurableEquiv.map_symm]
  rfl

theorem sigmaFinite_coordK (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R)
    [SigmaFinite lam] : SigmaFinite (coordK R b lam) := by
  rw [coordK_eq R hK lam]
  exact (eK R hK).symm.measurableEmbedding.sigmaFinite_map

theorem map_coordW (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R) [SigmaFinite lam]
    (n M : ℕ) :
    MeasurePreserving (eW R hK n M) (coordW R b lam n M)
      (Measure.pi fun _ : Fin n × Fin M × Fin d => lam) := by
  haveI := sigmaFinite_coordK R hK lam
  refine ⟨(eW R hK n M).measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (eW R hK n M).measurable (MeasurableSet.univ_pi hs)]
  have hset : (eW R hK n M) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun a => Set.pi Set.univ fun i =>
        (eK R hK) ⁻¹' Set.pi Set.univ fun k => s (a, i, k) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h a i k => h (a, i, k), fun h p => h p.1 p.2.1 p.2.2⟩
  have hK1 : ∀ t : Fin d → Set R, (∀ k, MeasurableSet (t k)) →
      coordK R b lam ((eK R hK) ⁻¹' Set.pi Set.univ t) = ∏ k, lam (t k) := by
    intro t ht
    rw [coordK_eq R hK lam, Measure.map_apply (eK R hK).symm.measurable
      ((eK R hK).measurable (MeasurableSet.univ_pi ht))]
    have : (eK R hK).symm ⁻¹' ((eK R hK) ⁻¹' Set.pi Set.univ t) = Set.pi Set.univ t := by
      ext x
      simp
    rw [this, Measure.pi_pi]
  rw [hset, coordW, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simp_rw [hK1 _ (fun k => hs _)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]

end Gen

theorem coordW_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → coordW (Af F) b lf n M {X | (∀ v ∈ S, projV v X ∈ A v) ∧ ∀ v, v ∉ S → projV v X ∈ latV b v} = ∏ v ∈ S, coordW (Fv F v) b (lam v) n M (A v) := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam lf hlf h1 n M S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hKf : IsHomeomorph (cK (F := F) (E := E) (Af F) b) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Af F)).2.2.2.2.2.2.1 d b
  have hKv : ∀ v, IsHomeomorph (cK (F := F) (E := E) (Fv F v) b) := fun v =>
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.1 d b
  have mf := map_coordW (Af F) hKf lf n M
  have mv := fun v => map_coordW (Fv F v) (hKv v) (lam v) n M
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n × Fin M × Fin d → Fv F v) := fun v =>
    (eW (Fv F v) (hKv v) n M).symm ⁻¹' A v
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => (eW (Fv F v) (hKv v) n M).symm.measurable (hA v)
  have hcomm : ∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → Af F ⊗[F] E)
      (p : Fin n × Fin M × Fin d),
      evalV F v (eW (Af F) hKf n M X p) = eW (Fv F v) (hKv v) n M (projV v X) p := by
    intro v X p
    rw [eW_apply, eW_apply, projV, cK_map]
  have hset : {X : Fin n → Fin M → Af F ⊗[F] E | (∀ v ∈ S, projV v X ∈ A v) ∧
      ∀ v, v ∉ S → projV v X ∈ latV b v} =
      (eW (Af F) hKf n M) ⁻¹' {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A' v) ∧
        ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hcomm]
    refine and_congr (forall₂_congr fun v _ => ?_) (forall₂_congr fun v _ => ?_)
    · simp [A']
    · exact ⟨fun h p => h p.1 p.2.1 p.2.2, fun h a i k => h (a, i, k)⟩
  rw [hset, mf.measure_preimage_equiv,
    GlobalTheory.CompanionTheory.SW.AfBox.pi_box F lam hlam lf hlf h1 (Fin n × Fin M × Fin d) S A' hA']
  exact Finset.prod_congr rfl fun v _ => (mv v).symm.measure_preimage_equiv (A v)

end GlobalTheory.CompanionTheory.SW.WBox
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarPiRestrictedProductStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_haar_pi_restricted_product : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (ι : Type) [Fintype ι] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (ι → Fv F v)), (∀ v, MeasurableSet (A v)) → (Measure.pi fun _ : ι => lf) {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} = ∏ v ∈ S, (Measure.pi fun _ : ι => lam v) (A v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.AfBox.pi_box | exact GlobalTheory.CompanionTheory.SW.AfBox.pi_box | (intros; apply GlobalTheory.CompanionTheory.SW.AfBox.pi_box <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties : ∀ (F : Type) [Field F] [NumberField F], LocallyCompactSpace (A F) ∧ SecondCountableTopology (A F) ∧ T2Space (A F) ∧ IsCompact (Oh F) ∧ IsOpen (Oh F) ∧ DenseRange (algebraMap F (A F)) ∧ (∀ b : F, algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b) ∧ (∀ U ∈ 𝓝 (0 : A F), ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, (N : A F) * x ∈ U) ∧ (∀ K : Set (A F), IsCompact K → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, (N : A F) * x ∈ Oh F) ∧ ∀ N : ℕ, 0 < N → IsOpen {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology | exact GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology | (intros; apply GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdelicTraceFormCoordinatesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_trace_form_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Af F ⊗[F] E, Algebra.trace (Af F) (Af F ⊗[F] E) (hR (Af F) σ J x y) = cv (Af F) b x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ cv (Af F) b y)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → ∀ (a : ℕ) (U : Set (Af F)), coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = (Measure.pi fun _ : Fin M × Fin d => lf) {x | (∀ i v, ((a : Af F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (Af F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ x)) ∈ U} := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.finDensity_coord | exact GlobalTheory.CompanionTheory.SW.BB.finDensity_coord | (intros; apply GlobalTheory.CompanionTheory.SW.BB.finDensity_coord <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarScalingUnderFlowStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_scaling_under_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ x : ℝ, μ.map (fun X => ((τ (Multiplicative.ofAdd (x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X) = ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * n * M * x))) • μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Flow.modulus_flow | exact GlobalTheory.CompanionTheory.SW.Flow.modulus_flow | (intros; apply GlobalTheory.CompanionTheory.SW.Flow.modulus_flow <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBlockOneAlmostAllStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_densities_block_one_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m₁ m', IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → m (hermOf (Fv F v) σ _ hT') (latV b v) = m₁ (hermScal (Fv F v) σ (algebraMap F _ t)) (latV b v) * m' (hermOf (Fv F v) σ T hT) (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodStep.blockFibre_mass | exact GlobalTheory.CompanionTheory.SW.GoodStep.blockFibre_mass | (intros; apply GlobalTheory.CompanionTheory.SW.GoodStep.blockFibre_mass <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesCongruentTargetAlmostAllStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_densities_congruent_target_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (g : Matrix (Fin n) (Fin n) E), g.det ≠ 0 → ∀ (T' : Matrix (Fin n) (Fin n) E) (hT' : ∀ a b, σ (T' b a) = T' a b), T' = cT (σ : E →+* E) g * T * g → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → m (hermOf (Fv F v) σ T' hT') (latV b v) = m (hermOf (Fv F v) σ T hT) (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodScale.mass_eq | exact GlobalTheory.CompanionTheory.SW.GoodScale.mass_eq | (intros; apply GlobalTheory.CompanionTheory.SW.GoodScale.mass_eq <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberMeasuresAgreeAlmostAllStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_gram_fiber_measures_agree_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ n : ℕ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m', IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → IsGramFib (Fv F v) σ J' n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ S, m S (latV b v) = m' S (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.lattice_mass_fibre_eq | exact GlobalTheory.CompanionTheory.SW.lattice_mass_fibre_eq | (intros; apply GlobalTheory.CompanionTheory.SW.lattice_mass_fibre_eq <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPowerStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_rank_one_density_uniformizer_power : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → 1 ≤ M → ∀ (a : ℕ) (e : ℕ), 0 < a → (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ e → ¬ (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ (e + 1) → ∀ (s : Fv F v) (A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet A → m (hermScal (Fv F v) σ s) {X | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ A} = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (e * (2 * M - 2)) * m (hermScal (Fv F v) σ ((a : Fv F v) ^ 2 * s)) A := by
  first | exact @GlobalTheory.CompanionTheory.SW.Dil.dilation | exact GlobalTheory.CompanionTheory.SW.Dil.dilation | (intros; apply GlobalTheory.CompanionTheory.SW.Dil.dilation <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasurableFiniteLevelLatticeSetStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_finite_level_lattice_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (N : Fv F v ⊗[F] E) * X p i) ∈ latV b v}} := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int | exact GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int | (intros; apply GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int <;> assumption)
end

