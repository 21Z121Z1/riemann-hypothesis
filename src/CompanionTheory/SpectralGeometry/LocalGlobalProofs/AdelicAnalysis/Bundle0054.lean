import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0027
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0011
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0002
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0036
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.SiegelWeilOfFormula

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeles_locally_compact_second_countable : ∀ (F : Type) [Field F] [NumberField F], (LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) ∧ T2Space (AF F)) ∧ (LocallyCompactSpace (Af F) ∧ SecondCountableTopology (Af F) ∧ T2Space (Af F)) := by
  first | exact @GlobalTheory.CompanionTheory.AdeleTop.adele_top | exact GlobalTheory.CompanionTheory.AdeleTop.adele_top | (intros; apply GlobalTheory.CompanionTheory.AdeleTop.adele_top <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarInvariantUnitaryAction
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HaarInv

def tupEquiv {K A : Type} [AddCommGroup K] [TopologicalSpace K] [AddCommGroup A] [TopologicalSpace A]
    {M d : ℕ} (Φ : K ≃ₜ (Fin d → A)) (hadd : ∀ x y, Φ (x + y) = Φ x + Φ y) :
    (Fin 1 → Fin M → K) ≃ₜ+ (Fin M × Fin d → A) where
  toFun X p := Φ (X 0 p.1) p.2
  invFun Y _ i := Φ.symm fun k => Y (i, k)
  left_inv X := by
    funext a i
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    simp
  right_inv Y := by
    funext p
    simp
  map_add' X Y := by
    funext p
    simp [hadd]
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2).comp
      (Φ.continuous.comp ((continuous_apply p.1).comp (continuous_apply 0)))
  continuous_invFun := by
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    exact Φ.symm.continuous.comp (continuous_pi fun k => continuous_apply (i, k))

theorem map_eq_of_conj {V W : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] (e : V ≃ₜ W) (μ : Measure V)
    (T : V → V) (G : W → W) (hG : Measurable G) (hc : ∀ x, e (T x) = G (e x))
    (hinv : (μ.map e).map G = μ.map e) : μ.map T = μ := by
  have he : Measurable e := e.continuous.measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  have hT : T = e.symm ∘ G ∘ e := by
    funext x
    simp [← hc x]
  calc μ.map T = ((μ.map e).map G).map e.symm := by
        rw [Measure.map_map hG he, Measure.map_map hes (hG.comp he), hT]
    _ = (μ.map e).map e.symm := by rw [hinv]
    _ = μ := by
        rw [Measure.map_map hes he]
        simp

end GlobalTheory.CompanionTheory.SW.HaarInv

open GlobalTheory.CompanionTheory.SW.HaarInv in
theorem GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ h : HA (AF F) σ J, μ.map (actW (AF F) σ J h) = μ := by
  intro F E _ _ _ _ _ σ hσ M J hJ μ _ h
  obtain ⟨⟨i3, i4, i5⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  letI : MeasurableSpace (AF F) := borel (AF F)
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨iR, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hBor 1 M
  let b := Module.finBasis F E
  obtain ⟨B, -, hBdet, hB⟩ := GlobalTheory.CompanionTheory.SW.CoordMat.coord_orthogonal F E σ hσ M J hJ _ b
  obtain ⟨g, hg, hconj⟩ := hB (AF F) h
  let Φ := GlobalTheory.CompanionTheory.SW.TopK.coordHomeo (AF F) b
  have hadd : ∀ x y, Φ (x + y) = Φ x + Φ y := fun x y => by
    funext k
    simp [Φ, GlobalTheory.CompanionTheory.SW.TopK.coordHomeo]
  let e := tupEquiv (M := M) Φ hadd
  have hcomm : ∀ X, e.toHomeomorph (actW (AF F) σ J h X) = (fun x => g *ᵥ x) (e.toHomeomorph X) := by
    intro X
    have := hconj X
    funext p
    have hp := congrFun this p
    simpa [e, tupEquiv, Φ, GlobalTheory.CompanionTheory.SW.TopK.coordHomeo] using hp
  have hdet : IsUnit (B.map (algebraMap F (AF F))).det := by
    have : (B.map (algebraMap F (AF F))).det = algebraMap F (AF F) B.det := by
      rw [RingHom.map_det]
      rfl
    rw [this]
    exact (Ne.isUnit hBdet).map _
  haveI : (μ.map e.toHomeomorph).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hinv : (μ.map e.toHomeomorph).map (fun x => g *ᵥ x) = μ.map e.toHomeomorph :=
    GlobalTheory.CompanionTheory.Adelic.OrthHaar.map_mulVec_eq_of_transpose_mul_mul_eq (AF F) (GlobalTheory.CompanionTheory.AdeleStableRange.adeleRing_stableRange_one F) _ (μ.map e.toHomeomorph) (B.map (algebraMap F (AF F))) g hdet hg
  exact map_eq_of_conj e.toHomeomorph μ (actW (AF F) σ J h) (fun x => g *ᵥ x)
    (continuous_const.matrix_mulVec continuous_id).measurable hcomm hinv
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarScalingByRealIdele
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdelicFlow

theorem map_eq_smul_of_scale {V W G : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [LocallyCompactSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G]
    (Φ : G ≃ₜ+ V × W) (φ : G → G) (t : ℝ) (ht : t ≠ 0)
    (h : ∀ x, Φ (φ x) = (t • (Φ x).1, (Φ x).2))
    (μ : Measure G) [μ.IsAddHaarMeasure] :
    μ.map φ = ENNReal.ofReal |(t ^ Module.finrank ℝ V)⁻¹| • μ := by
  set k := ENNReal.ofReal |(t ^ Module.finrank ℝ V)⁻¹| with hk
  have hΦ : Measurable Φ := Φ.continuous.measurable
  have hΦs : Measurable Φ.symm := Φ.symm.continuous.measurable
  let ν : Measure V := Measure.addHaar
  let ρ : Measure W := Measure.addHaar
  let ψ : V × W → V × W := Prod.map (fun v => t • v) id
  have hψ : Measurable ψ := (measurable_const_smul t).prodMap measurable_id
  haveI : (μ.map Φ).IsAddHaarMeasure := Φ.isAddHaarMeasure_map μ
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map Φ) (ν.prod ρ)
  set c := Measure.addHaarScalarFactor (μ.map Φ) (ν.prod ρ) with hcdef
  have hπ : (μ.map Φ).map ψ = k • μ.map Φ := by
    have h1 : (ν.prod ρ).map ψ = k • ν.prod ρ := by
      have := Measure.map_prod_map ν ρ (f := fun v : V => t • v) (g := (id : W → W))
        (measurable_const_smul t) measurable_id
      rw [show (ν.prod ρ).map ψ = (ν.map fun v => t • v).prod (ρ.map id) from this.symm,
        Measure.map_addHaar_smul ν ht, Measure.map_id, Measure.prod_smul_left]
    rw [hc, Measure.map_smul, h1, smul_comm]
  have hφ : φ = Φ.symm ∘ ψ ∘ Φ := by
    funext x
    apply Φ.injective
    simp [h]
    rfl
  have hμ : (μ.map Φ).map Φ.symm = μ := by
    rw [Measure.map_map hΦs hΦ]
    simp
  calc μ.map φ = ((μ.map Φ).map ψ).map Φ.symm := by
        rw [Measure.map_map hΦs hψ, Measure.map_map (hΦs.comp hψ) hΦ, hφ]; rfl
    _ = k • μ := by rw [hπ, Measure.map_smul, hμ]

section Adelic

variable (F : Type) [Field F] [NumberField F]

noncomputable def coords [IsTotallyReal F] (ι : Type) :
    (ι → AdeleRing (𝓞 F) F) ≃ₜ+
      (ι → InfinitePlace F → ℝ) × (ι → FiniteAdeleRing (𝓞 F) F) where
  toFun x := (fun i w => InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal w) ((x i).1 w), fun i => (x i).2)
  invFun p := fun i => (show AdeleRing (𝓞 F) F from
    (fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal w)).symm (p.1 i w), p.2 i))
  left_inv x := by
    funext i
    refine Prod.ext ?_ rfl
    funext w
    exact RingEquiv.symm_apply_apply _ _
  right_inv p := by
    refine Prod.ext ?_ rfl
    funext i w
    exact RingEquiv.apply_symm_apply _ _
  map_add' x y := by
    refine Prod.ext ?_ rfl
    funext i w
    exact map_add (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)) _ _
  continuous_toFun := by
    refine Continuous.prodMk (continuous_pi fun i => continuous_pi fun w => ?_)
      (continuous_pi fun i => ?_)
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (IsTotallyReal.isReal w)).continuous.comp
        ((continuous_apply w).comp (continuous_fst.comp (continuous_apply i)))
    · exact continuous_snd.comp (continuous_apply i)
  continuous_invFun := by
    refine continuous_pi fun i => Continuous.prodMk (continuous_pi fun w => ?_) ?_
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (IsTotallyReal.isReal w)).symm.continuous.comp
        ((continuous_apply w).comp ((continuous_apply i).comp continuous_fst))
    · exact (continuous_apply i).comp continuous_snd

theorem coord_theta [IsTotallyReal F] (θ : ℝ →+* InfiniteAdeleRing F) (t : ℝ)
    (w : InfinitePlace F) :
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) (θ t w) = t := by
  have h : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) :
      w.Completion →+* ℝ).comp ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ))
      = RingHom.id ℝ := Subsingleton.elim _ _
  exact DFunLike.congr_fun h t

theorem card_places [IsTotallyReal F] :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]

end Adelic

theorem map_scalar : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ →
    ∀ [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (ι : Type)
      [Fintype ι] (μ : Measure (ι → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (t : ℝ), 0 < t →
      μ.map (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) =
        ENNReal.ofReal ((t ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • μ := by
  intro F _ _ hF θ _ _ _ ι _ μ _ t ht
  haveI := hF
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have key := map_eq_smul_of_scale (coords F ι)
    (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) t ht.ne' ?_ μ
  · have hd : Module.finrank ℝ (ι → InfinitePlace F → ℝ) =
        Module.finrank ℚ F * Fintype.card ι := by
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_fintype_fun_eq_card, card_places F, mul_comm]
    rw [key, hd, abs_of_pos (inv_pos.2 (pow_pos ht _))]
  · intro x
    refine Prod.ext ?_ ?_
    · funext i w
      show InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
        (θ t w * (x i).1 w) = t * _
      rw [map_mul, coord_theta]
      rfl
    · funext i
      exact one_mul _

end GlobalTheory.CompanionTheory.AdelicFlow
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureIntegralStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_measure_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I c minf m → ∀ (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable φinf → (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) < ⊤) → (∀ᶠ v in Filter.cofinite, A v = latV b v) → Multipliable (fun v => (m v (A v)).toReal) ∧ ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, φinf (projInf X) ∂I = (c : ℝ≥0∞) * (∫⁻ X, φinf X ∂minf) * ENNReal.ofReal (∏' v, (m v (A v)).toReal) := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerBox.euler_box | exact GlobalTheory.CompanionTheory.SW.EulerBox.euler_box | (intros; apply GlobalTheory.CompanionTheory.SW.EulerBox.euler_box <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasuresStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standard_local_measures : ∀ (F : Type) [Field F] [NumberField F], (∃ laminf : Measure (Ainf F), IsStdInf laminf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∃ lam : Measure (Fv F v), IsStdV v lam := by
  first | exact @GlobalTheory.CompanionTheory.SW.StdEx.exists_std | exact GlobalTheory.CompanionTheory.SW.StdEx.exists_std | (intros; apply GlobalTheory.CompanionTheory.SW.StdEx.exists_std <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramCoordinatesMeasurable
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB

theorem continuous_gmat_entry {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (p q : Fin M × Fin d) :
    Continuous fun h : HA R σ J => gmat R σ J b h p q := by
  classical
  have hact := ((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ R).2.2.2.2.2 1).1
  have hco : IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k :=
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R).2.2.2.2.2.2.1 d b
  let X : Fin 1 → Fin M → R ⊗[F] E := fun _ => Pi.single q.1 (inclR R (b q.2))
  have h1 : Continuous fun h : HA R σ J => actW R σ J h X :=
    hact.comp (continuous_id.prodMk continuous_const)
  have h2 : Continuous fun h : HA R σ J => actW R σ J h X 0 p.1 :=
    (continuous_apply p.1).comp ((continuous_apply (0 : Fin 1)).comp h1)
  have h3 : Continuous fun h : HA R σ J =>
      (Algebra.TensorProduct.basis R b).repr (actW R σ J h X 0 p.1) p.2 :=
    (continuous_apply p.2).comp (hco.continuous.comp h2)
  refine h3.congr fun h => ?_
  simp [gmat, actW, actTup, X, Matrix.mulVec_single]

theorem ginf_gfin_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ w p q, Measurable fun ω => ginf e σ J b ω w p q) ∧ (∀ p q, Measurable fun ω => gfin σ J b ω p q) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b e he
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨htg, -, -, -, hbor, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  have hinv : ∀ p q, Continuous fun ω : HA (AF F) σ J => gmat (AF F) σ J b ω⁻¹ p q := fun p q =>
    (continuous_gmat_entry σ hσ J hJ b (AF F) p q).comp continuous_inv
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  refine ⟨fun w p q => ?_, fun p q => ?_⟩
  · have hf : Continuous fun t : AF F => e (fstA F t) w :=
      (continuous_apply w).comp (he.continuous.comp continuous_fst)
    exact (hf.comp (hinv p q)).measurable
  · have hf : Continuous fun t : AF F => sndA F t := continuous_snd
    exact (hf.comp (hinv p q)).measurable

end GlobalTheory.CompanionTheory.SW.BB
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainExistsUnitary
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem haar_fundamental_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∃ μ, IsHaarH F E σ M J μ) ∧ ∀ μ, IsHaarH F E σ M J μ → (∃ 𝓕, IsFDH F E σ M J μ 𝓕) ∧ (∃ 𝓕, MeasurableSet 𝓕 ∧ IsFDH F E σ M J μ 𝓕 ∧ ∀ h : HA (AF F) σ J, ∃ γ : HA (AF F) σ J, HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J ∧ γ * h ∈ 𝓕) ∧ ∀ 𝓕, IsFDH F E σ M J μ 𝓕 → μ 𝓕 ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  obtain ⟨htg, hlcH, hscH, ht2H, hbH, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := htg
  haveI := hlcH
  haveI := hscH
  haveI := ht2H
  haveI := hbH
  obtain ⟨hcount, U, hU, hUd⟩ := rational_countable_discrete F E σ hσ M J hJ
  haveI := hcount
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have hmem : ∀ γ : HA (AF F) σ J, γ ∈ Γ → HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J :=
    fun γ hγ => Subgroup.mem_subgroupOf.1 hγ
  obtain ⟨-, D, hD, hDs⟩ := GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete
    (HA (AF F) σ J) Γ ⟨U, hU, fun γ hγ hγU => hUd γ hγU (hmem γ hγ)⟩
  have hfd : ∀ μ : Measure (HA (AF F) σ J), IsFDH F E σ M J μ D := fun μ =>
    IsFundamentalDomain.mk' hD.nullMeasurableSet hDs
  refine ⟨⟨Measure.haar, inferInstanceAs (Measure.IsHaarMeasure _)⟩, fun μ hμ => ?_⟩
  haveI : μ.IsHaarMeasure := hμ
  refine ⟨⟨D, hfd μ⟩, ⟨D, hD, hfd μ, fun h => ?_⟩, fun 𝓕 h𝓕 => ?_⟩
  · obtain ⟨γ, hγ, -⟩ := hDs h
    exact ⟨γ, hmem _ γ.2, hγ⟩
  · haveI : MeasurableConstSMul (HFinIn (AF F) σ J) (HA (AF F) σ J) :=
      ⟨fun c => (continuous_const.mul continuous_id :
        Continuous fun x : HA (AF F) σ J => (show HA (AF F) σ J from c.1) * x).measurable⟩
    haveI : SMulInvariantMeasure (HFinIn (AF F) σ J) (HA (AF F) σ J) μ :=
      ⟨fun c s hs => measure_preimage_mul μ (show HA (AF F) σ J from c.1) s⟩
    have h𝓕' : IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ := h𝓕
    exact h𝓕'.measure_ne_zero (NeZero.ne μ)

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LinearChangeEulerProduct
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.ProdFormula

theorem modulus_matrix : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (ι → Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Ainf F)) *ᵥ x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (ι → Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Fv F v)) *ᵥ x) = c v • μ) := by
  intro F _ _ ι _ _ A hA
  obtain ⟨cinf, c, hU, hinf, hv⟩ := GlobalTheory.T.global_unit_scaling_haar_product_formula F A.det hA
  refine ⟨cinf, c, hU, ?_, ?_⟩
  · intro μ hμ
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    exact GlobalTheory.T.haar_map_linear_scaling_by_determinant F (Ainf F) ι A hA Measure.addHaar inferInstance cinf
      (hinf Measure.addHaar inferInstance) μ hμ
  · intro v μ hμ
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI : SecondCountableTopology (Fv F v) := (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v).2.2.1
    exact GlobalTheory.T.haar_map_linear_scaling_by_determinant F (Fv F v) ι A hA Measure.addHaar inferInstance (c v)
      (hv v Measure.addHaar inferInstance) μ hμ

end GlobalTheory.CompanionTheory.SW.ProdFormula
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneEventually
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GoodMass

theorem continuous_act_consTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (hring : IsTopologicalRing (R ⊗[F] E)) (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA R σ J) :
    Continuous fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J h (consTup X) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actW, actTup, Matrix.mulVec, dotProduct]
  refine continuous_finset_sum _ fun j _ => continuous_const.mul ?_
  refine Fin.cases ?_ (fun a' => ?_) a
  · refine Fin.cases ?_ (fun j' => ?_) j <;> simpa [consTup] using continuous_const
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simpa [consTup] using continuous_const
    · have hc : Continuous fun X : Fin n → Fin M → R ⊗[F] E => X a' j' :=
        (continuous_apply j').comp (continuous_apply a')
      simpa [consTup] using hc

theorem good_mass : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ c : ℝ≥0, (coordK (Fv F v) b lam).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) = c • coordK (Fv F v) b lam → m (hermOf (Fv F v) σ _ hT') (latV b v) = (c : ℝ≥0∞) ^ n * (m' (hermOf (Fv F v) σ T hT) (latV b v) * m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (latV b v)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hdetT hT' d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [StageGood.stage_good F E σ hCM M J hJ t ht n T hT hdetT d b] with v hv
  intro lam hlam m m₁ m' hm hm₁ hm' c hc
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have hH := coord_measures_haar F E σ hCM (Fv F v) d b lam hlam
  obtain ⟨hring, -, -, -, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have hlat : ∀ n' M' : ℕ, MeasurableSet (latV b v : Set (Fin n' → Fin M' → Fv F v ⊗[F] E)) := by
    intro n' M'
    haveI := hB n' M'
    exact ((MeasProj.proj_props F E σ hCM d b n' M').2.2.2.1 v).2.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdetT hT' (Fv F v) hLoc d b lam hlam
    m m₁ m' hm hm₁ hm' c hc ((latV b v).indicator 1) (measurable_one.indicator (hlat _ _))
  set A := m' (hermOf (Fv F v) σ T hT) (latV b v) with hA
  have hae : Ψ =ᵐ[m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))] (latV b v).indicator (fun _ => A) := by
    filter_upwards [mem_ae_iff.2 (hm₁.1 (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hg : gramR (Fv F v) σ (blockOne (algebraMap F E t) J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) =
        gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y :=
      (StageGood.gram_first (Fv F v) σ J t).trans hy1.symm
    obtain ⟨h, rfl⟩ := GlobalTheory.T.witt_extension_artinian_ring F E σ hCM (M + 1) _ hND (Fv F v) 1 _ y hg
      (by rw [hg]; exact hy2)
    rw [hΨ h]
    haveI := hB n M
    haveI := hB (n + 1) (M + 1)
    have hS : MeasurableSet {X : Fin n → Fin M → Fv F v ⊗[F] E |
        actW (Fv F v) σ _ h (consTup X) ∈ latV b v} :=
      (continuous_act_consTup (Fv F v) hring σ _ h).measurable (hlat _ _)
    have hfun : (fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
        (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ h (consTup X))) =
        {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v}.indicator 1 := by
      funext X
      rfl
    rw [hfun, lintegral_indicator_one hS, hv _ _ m' (hH.2.1 n M) (hH.2.2 n) hm' h]
  rw [← lintegral_indicator_one (hlat _ _), hint, lintegral_congr_ae hae,
    lintegral_indicator_const (hlat _ _)]

end GlobalTheory.CompanionTheory.SW.GoodMass
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_compact_open_unit_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV (M := M) (n := n) b v) ∧ IsOpen (latV (M := M) (n := n) b v) ∧ (0 : Fin n → Fin M → Fv F v ⊗[F] E) ∈ latV b v ∧ ∀ lam : Measure (Fv F v), IsStdV v lam → coordW (Fv F v) b lam n M (latV b v) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.latV_compact_open_mass | exact GlobalTheory.CompanionTheory.SW.latV_compact_open_mass | (intros; apply GlobalTheory.CompanionTheory.SW.latV_compact_open_mass <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem finVol_unitaryGroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J :=
  fun F E _ _ _ _ _ σ hσ M J hJ => CompanionTheory.SWFin.finVol F E σ hσ M J hJ

end GlobalTheory.CompanionTheory.SW
end

