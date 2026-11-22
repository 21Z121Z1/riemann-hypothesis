import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeGlue

theorem polishSpace_addCommGroup (G : Type) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] :
    PolishSpace G := by
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace G := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : (uniformity G).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem repr_map (φ : R →ₐ[F] R') (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem tens_ext {z z' : R ⊗[F] E} (h : ∀ k, (Algebra.TensorProduct.basis R b).repr z k =
    (Algebra.TensorProduct.basis R b).repr z' k) : z = z' :=
  (Algebra.TensorProduct.basis R b).ext_elem h

theorem exists_repr (c : Fin d → R) :
    ∃ z : R ⊗[F] E, ∀ k, (Algebra.TensorProduct.basis R b).repr z k = c k :=
  ⟨(Algebra.TensorProduct.basis R b).equivFun.symm c, fun k => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]⟩

include b in
theorem continuous_map [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace R']
    [IsTopologicalRing R'] (φ : R →ₐ[F] R') (hφ : Continuous φ) :
    Continuous (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have h1 : Continuous (Algebra.TensorProduct.basis R b).equivFun :=
    IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
  have h2 : Continuous (Algebra.TensorProduct.basis R' b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R' b).equivFun.symm.toLinearMap
  have h3 : Continuous fun z : R ⊗[F] E => fun k => φ ((Algebra.TensorProduct.basis R b).equivFun z k) :=
    continuous_pi fun k => hφ.comp ((continuous_apply k).comp h1)
  refine (h2.comp h3).congr fun z => ?_
  simp only [Function.comp_apply]
  rw [LinearEquiv.symm_apply_eq]
  funext k
  simp only [Module.Basis.equivFun_apply, repr_map]

end Coord

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) {n M : ℕ}

theorem repr_projInf (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).1 :=
  repr_map b (fstA F) _ k

theorem repr_projV (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n)
    (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 v :=
  (repr_map b (evalV F v) _ k).trans (congrArg (evalV F v) (repr_map b (sndA F) _ k))

theorem continuous_fstA : Continuous (fstA F) := continuous_fst

theorem continuous_sndA : Continuous (sndA F) := continuous_snd

theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval v

theorem adele_ext {x y : AF F} (h1 : x.1 = y.1) (h2 : ∀ v, x.2 v = y.2 v) : x = y :=
  Prod.ext h1 (RestrictedProduct.ext _ _ h2)

theorem exists_adele (x : Ainf F) (y : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (hy : ∀ᶠ v in Filter.cofinite, y v ∈ v.adicCompletionIntegers F) :
    ∃ z : AF F, z.1 = x ∧ ∀ v, z.2 v = y v :=
  ⟨pairA F x ⟨y, hy⟩, rfl, fun _ => rfl⟩

include b in
theorem continuous_projInf : Continuous (projInf (F := F) (E := E) (M := M) (n := n)) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_map b (fstA F) continuous_fstA).comp
      ((continuous_apply i).comp (continuous_apply a))

include b in
theorem continuous_projV (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_map b (evalV F v) (continuous_evalV v)).comp
      ((continuous_map b (sndA F) continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a)))

include b in
theorem injective_glue : Function.Injective (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) := by
  intro X X' h
  have h1 : projInf X = projInf X' := congrArg Prod.fst h
  have h2 : ∀ v, projV v (projFin X) = projV v (projFin X') := congrFun (congrArg Prod.snd h)
  funext a i
  refine tens_ext b fun k => adele_ext ?_ fun v => ?_
  · rw [← repr_projInf, ← repr_projInf, h1]
  · rw [← repr_projV, ← repr_projV, h2]

theorem range_glue : Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) =
    {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} := by
  ext Y
  constructor
  · rintro ⟨X, rfl⟩
    have : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ a i k,
        ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 v ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k =>
        ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2.2
    filter_upwards [this] with v hv a i k
    rw [repr_projV]
    exact hv a i k
  · intro hY
    choose c hc1 hc2 using fun (a : Fin n) (i : Fin M) (k : Fin d) =>
      exists_adele ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y.1 a i) k)
        (fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Y.2 v a i) k)
        (Filter.Eventually.mono hY fun v hv => hv a i k)
    choose X hX using fun a i => exists_repr b (c a i)
    have h1 : projInf X = Y.1 := by
      funext a i
      refine tens_ext b fun k => ?_
      rw [repr_projInf, hX, hc1]
    have h2 : ∀ v, projV v (projFin X) = Y.2 v := fun v => by
      funext a i
      refine tens_ext b fun k => ?_
      rw [repr_projV, hX, hc2]
    exact ⟨X, Prod.ext h1 (funext h2)⟩

end Adele

theorem adelicTuple_measurableEmbedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), MeasurableEmbedding (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) ∧ Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) = {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} ∧ Continuous (projInf (F := F) (E := E) (M := M) (n := n)) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) := by
  intro F E _ _ _ _ _ d b n M
  refine ⟨?_, range_glue b, continuous_projInf b, continuous_projV b⟩
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : PolishSpace (Fin n → Fin M → AF F ⊗[F] E) := polishSpace_addCommGroup _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (Fv F v ⊗[F] E) := fun v =>
    inferInstance
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v =>
    inferInstance
  haveI : BorelSpace (∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E) :=
    Pi.borelSpace
  haveI : BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := inferInstance
  exact ((continuous_projInf b).prodMk (continuous_pi (continuous_projV b))).measurableEmbedding
    (injective_glue b)

end GlobalTheory.GaugeGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableSetOrbitExistsMeasurableSection
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.OrbitSection

theorem exists_section_real {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (C : Set ℝ) [CompactSpace C] (c₀ : C) (f : C → X) (hf : Continuous f) :
    ∃ τ : X → C, Measurable τ ∧ ∀ y ∈ Set.range f, f (τ y) = y := by
  have h : ∀ y : X, ∃ c : C, (y ∈ Set.range f → f c = y ∧ ∀ c', f c' = y → (c : ℝ) ≤ c') ∧
      (y ∉ Set.range f → c = c₀) := by
    intro y
    by_cases hy : y ∈ Set.range f
    · have hc : IsCompact (f ⁻¹' {y}) := (isClosed_singleton.preimage hf).isCompact
      obtain ⟨c, hc1, hc2⟩ := hc.exists_isMinOn (f := fun c : C => (c : ℝ)) hy
        continuous_subtype_val.continuousOn
      exact ⟨c, fun _ => ⟨hc1, fun c' h' => hc2 h'⟩, fun h => absurd hy h⟩
    · exact ⟨c₀, fun h => absurd h hy, fun _ => rfl⟩
  choose τ h1 h2 using h
  refine ⟨τ, ?_, fun y hy => (h1 y hy).1⟩
  have hm : Measurable fun y => (τ y : ℝ) := by
    refine measurable_of_Iic fun a => ?_
    have he : (fun y => (τ y : ℝ)) ⁻¹' Set.Iic a =
        f '' {c : C | (c : ℝ) ≤ a} ∪ ((Set.range f)ᶜ ∩ {_y | (c₀ : ℝ) ≤ a}) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_setOf_eq]
      by_cases hy : y ∈ Set.range f
      · constructor
        · intro h
          exact Or.inl ⟨τ y, h, (h1 y hy).1⟩
        · rintro (⟨c, hc, hcy⟩ | h)
          · exact ((h1 y hy).2 c hcy).trans hc
          · exact absurd hy h.1
      · rw [h2 y hy]
        constructor
        · intro h
          exact Or.inr ⟨hy, h⟩
        · rintro (⟨c, -, hcy⟩ | h)
          · exact absurd ⟨c, hcy⟩ hy
          · exact h.2
    rw [he]
    refine MeasurableSet.union ?_ (MeasurableSet.inter ?_ (MeasurableSet.const _))
    · exact ((isClosed_le continuous_subtype_val continuous_const).isCompact.image
        hf).isClosed.measurableSet
    · exact (isCompact_range hf).isClosed.measurableSet.compl
  exact hm.subtype_mk (h := fun y => (τ y).2)

theorem exists_section_compact {K X : Type} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (f : K → X) (hf : Continuous f) :
    ∃ τ : X → K, Measurable τ ∧ ∀ y ∈ Set.range f, f (τ y) = y := by
  letI := TopologicalSpace.metrizableSpaceMetric K
  obtain ⟨p, hp, hps⟩ := exists_nat_bool_continuous_surjective_of_compact K
  have : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  let q : cantorSet → K := p ∘ cantorSetHomeomorphNatToBool
  have hq : Continuous q := hp.comp cantorSetHomeomorphNatToBool.continuous
  have hqs : Function.Surjective q := hps.comp cantorSetHomeomorphNatToBool.surjective
  obtain ⟨τ, h1, h2⟩ := exists_section_real cantorSet ⟨0, zero_mem_cantorSet⟩ (f ∘ q)
    (hf.comp hq)
  refine ⟨q ∘ τ, hq.measurable.comp h1, fun y hy => h2 y ?_⟩
  rwa [hqs.range_comp]

theorem measurableSet_orbit_and_exists_section : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), MeasurableSet {y : X | ∃ g : G, g • x₀ = y} ∧ ∃ s : X → G, Measurable s ∧ ∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x₀
  classical
  have hπ : Continuous fun g : G => g • x₀ := by fun_prop
  let K : ℕ → Set G := fun n => insert 1 (compactCovering G n)
  have hK : ∀ n, IsCompact (K n) := fun n => (isCompact_compactCovering G n).insert 1
  have hKU : ∀ g : G, ∃ n, g ∈ K n := fun g => by
    obtain ⟨n, hn⟩ := exists_mem_compactCovering g
    exact ⟨n, Or.inr hn⟩
  let A : ℕ → Set X := fun n => (fun g : G => g • x₀) '' K n
  have hA : ∀ n, MeasurableSet (A n) := fun n => ((hK n).image hπ).isClosed.measurableSet
  have hO : MeasurableSet {y : X | ∃ g : G, g • x₀ = y} := by
    have : {y : X | ∃ g : G, g • x₀ = y} = ⋃ n, A n := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨g, hg⟩
        obtain ⟨n, hn⟩ := hKU g
        exact ⟨n, g, hn, hg⟩
      · rintro ⟨n, g, -, hg⟩
        exact ⟨g, hg⟩
    rw [this]
    exact MeasurableSet.iUnion hA
  have hs : ∀ n, ∃ s : X → G, Measurable s ∧ ∀ y ∈ A n, s y • x₀ = y := by
    intro n
    have : CompactSpace (K n) := isCompact_iff_compactSpace.1 (hK n)
    have : Nonempty (K n) := ⟨⟨1, Or.inl rfl⟩⟩
    obtain ⟨τ, h1, h2⟩ := exists_section_compact (fun g : K n => (g : G) • x₀)
      (hπ.comp continuous_subtype_val)
    refine ⟨fun y => τ y, measurable_subtype_coe.comp h1, ?_⟩
    rintro y ⟨g, hg, hgy⟩
    exact h2 y ⟨⟨g, hg⟩, hgy⟩
  choose s hs1 hs2 using hs
  have hex : ∀ y : X, ∃ n, (y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y) := by
    intro y
    by_cases hy : ∃ g : G, g • x₀ = y
    · obtain ⟨g, hg⟩ := hy
      obtain ⟨n, hn⟩ := hKU g
      exact ⟨n, Or.inl ⟨g, hn, hg⟩⟩
    · exact ⟨0, Or.inr hy⟩
  refine ⟨hO, fun y => s (Nat.find (hex y)) y, ?_, fun y hy => ?_⟩
  · exact Measurable.find (p := fun n y => y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y) hs1 (fun n => (hA n).union hO.compl) hex
  · exact hs2 _ y ((Nat.find_spec (hex y)).resolve_right (not_not.2 hy))

end GlobalTheory.OrbitSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenNormCoeffOfFibre
section
open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem mem_basicOpen_normCoeff_of_fibre {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    {V : X.Opens} (hV : IsAffineOpen V) [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)]
    (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X) (hx : x ∈ V) (h : ∀ y : Y, f y = x → y ∈ Y.basicOpen τ) :
    ∃ k, 1 ≤ k ∧ x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := by
  have hV' := hV.preimage f
  have sq := hV.SpecMap_appLE_fromSpec f hV' le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at sq
  have pt : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V),
      hV.fromSpec (PrimeSpectrum.comap (f.app V).hom q) = f (hV'.fromSpec q) := fun q => congr($(sq) q)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have e₁ : ∀ c : Γ(X, V), hV.fromSpec p ∈ X.basicOpen c ↔ c ∉ p.asIdeal := fun c => by
    rw [← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen]; rfl
  have e₂ : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V), hV'.fromSpec q ∈ Y.basicOpen τ ↔ τ ∉ q.asIdeal :=
    fun q : Spec Γ(Y, f ⁻¹ᵁ V) => by rw [← Scheme.Hom.mem_preimage, hV'.fromSpec_preimage_basicOpen]; rfl
  have inj := hV.fromSpec.isOpenEmbedding.injective
  have h0 : ∃ Q : Ideal Γ(Y, f ⁻¹ᵁ V), Q.IsPrime ∧ Q.comap (f.app V).hom = ⊥ := by
    let P0 : PrimeSpectrum Γ(X, V) := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨y, hy⟩ := f.surjective (hV.fromSpec P0)
    have hyV : f y ∈ V := by
      have hr : hV.fromSpec P0 ∈ Set.range hV.fromSpec := ⟨P0, rfl⟩
      rw [hV.range_fromSpec] at hr
      rw [hy]; exact hr
    obtain ⟨q, rfl⟩ : y ∈ Set.range hV'.fromSpec := by rw [hV'.range_fromSpec]; exact hyV
    exact ⟨q.asIdeal, q.isPrime, congrArg PrimeSpectrum.asIdeal (inj ((pt q).trans hy))⟩
  obtain ⟨k, hk, hc⟩ := GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime (f.app V).hom (f.finite_app V hV) τ h0 p.asIdeal p.isPrime
    (fun Q hQ hQp => by
      let q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V) := ⟨Q, hQ⟩
      have e : PrimeSpectrum.comap (f.app V).hom q = p := PrimeSpectrum.ext hQp
      exact (e₂ q).1 (h _ ((pt q).symm.trans (congrArg hV.fromSpec e))))
  exact ⟨k, hk, (e₁ _).2 hc⟩

end GlobalTheory.NormalDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemInvMulDifferent
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped Pointwise nonZeroDivisors

namespace GlobalTheory.Mem.EigenLine

variable {R : Ranks} (H : Host R)

theorem half_ne_zero :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := by
  refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
  intro h0
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  apply hd
  have := H.𝔟_spec.1
  rw [h0, Ideal.bot_mul] at this
  exact this

theorem half_mul_inv :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) * H.AA0 = 1 :=
  mul_inv_cancel₀ (half_ne_zero H)

theorem inv_mul_different :
    H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) =
      ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  have h : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟) := H.𝔟_spec.1
  rw [h, FractionalIdeal.coeIdeal_mul, ← mul_assoc, mul_comm H.AA0, half_mul_inv, one_mul]

theorem mem_inv_mul_different (x : H.E) :
    x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∃ b ∈ H.𝔟, x = H.conj ((b : 𝓞 H.E) : H.E) := by
  rw [inv_mul_different, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Ideal.pointwise_smul_def] at hc
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (MulSemiringAction.toRingEquiv _ (𝓞 H.E) H.conj).surjective).1 hc
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨H.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, rfl⟩

theorem map_mem_ellLat {LL : Type} [Field LL] [NumberField LL] (embE : H.E →+* LL)
    (g : R.GG) (x : H.E)
    (hx : x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)) :
    embE (H.sigmaOf g x) ∈ ellLat H embE g := by
  refine FractionalIdeal.mul_induction_on hx ?_ ?_
  · intro i hi j hj
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    exact Submodule.subset_span ⟨i, hi, b, hb, rfl⟩
  · intro a b ha hb
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb

theorem ellT_eq_ellLat : ∀ (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] (embE : D.host.E →+* M),
    (∀ x, ((embE x : M) : ℂ) = D.host.φ₀ x) → ∀ τ : D.what₂.Tau,
      ellT D M τ = ellLat D.host embE (D.eTau τ).1 := by
  intro D M _ embE hE τ
  have hτ : ∀ (τ : D.what₂.Tau) x, embT D τ x = ((embE (D.host.sigmaOf (D.eTau τ).1 x) : M) : ℂ) := by
    intro τ x
    rw [hE]
    rfl
  have hM : ∀ τ x, embT D τ x ∈ M := fun τ x => by
    rw [hτ]
    exact Subtype.property _
  let φ : D.host.E →+* M := embE.comp (((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)).comp
    (D.host.conj : D.host.E →+* D.host.E))
  have hφ : ∀ y, φ y = embE (D.host.sigmaOf (D.eTau τ).1 (D.host.conj y)) := fun _ => rfl
  have hone := half_mul_inv D.host
  apply le_antisymm
  · intro x hx
    rw [GlobalTheory.Glob.mem_ellT_iff hM] at hx
    have key : ∀ z ∈ ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0,
        x * φ z ∈ ellLat D.host embE (D.eTau τ).1 := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz ?_ ?_
      · intro i hi j hj
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        have hint : IsIntegral ℤ (x * φ j) := by
          refine (isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective).1 ?_
          have := hx j hj
          rw [hτ] at this
          exact this
        let c : 𝓞 M := ⟨x * φ j, hint⟩
        have : c • φ (b : D.host.E) ∈ ellLat D.host embE (D.eTau τ).1 :=
          Submodule.smul_mem _ _ (map_mem_ellLat D.host embE _ _
            ((mem_inv_mul_different D.host _).2 ⟨b, hb, rfl⟩))
        convert this using 1
        change x * φ (b * j) = x * φ j * φ b
        rw [map_mul]; ring
      · intro a b ha hb
        rw [map_add, mul_add]
        exact Submodule.add_mem _ ha hb
    have := key 1 (hone ▸ FractionalIdeal.one_mem_one _)
    simpa using this
  · unfold ellLat
    rw [Submodule.span_le]
    rintro x ⟨a, ha, d, hd, rfl⟩
    obtain ⟨b, hb, hab⟩ := (mem_inv_mul_different D.host (a * (d : D.host.E))).1
      (FractionalIdeal.mul_mem_mul ha ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩))
    rw [SetLike.mem_coe, GlobalTheory.Glob.mem_ellT_iff hM]
    intro y hy
    have h1 : (b : D.host.E) * y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      hone ▸ FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩) hy
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [← hτ, hab, ← map_mul, ← map_mul, ← hr]
    exact map_isIntegral_int ((embT D τ).comp (D.host.conj : D.host.E →+* D.host.E)) r.isIntegral_coe

end GlobalTheory.Mem.EigenLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyNStageProvisional
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem nonempty_nStage_provisional :
    ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (χ : Chi B.toPre), ShaOK B.toPre W.shaLen →
      (∀ j w, 1 ≤ j → j ≤ B.R.m → W.etaJ j w = 0) →
      (GoodChi B.toPre χ ∨ ((∀ μ, W.eOp μ = 0) ∧ ∀ μ j, W.eMt μ j = 0)) → Nonempty (NStage B C W) := by
  intro B C W χ hsha heta hgood
  obtain ⟨L⟩ := GlobalTheory.T.local_stage_nonempty
  obtain ⟨nd, hE, hχ, -⟩ := GlobalTheory.T.exists_unramified_data_character B C W χ hsha
  obtain ⟨tw, hT⟩ := GlobalTheory.T.exists_twist_empty_local B C W nd hE
  obtain ⟨A, hlab, hine⟩ := GlobalTheory.T.exists_automorphic_unipotent_labels B C W nd hE
  obtain ⟨bc⟩ := GlobalTheory.T.base_change_nonempty B.R B.host W.what₂ nd A hE
  obtain ⟨T, hT0, hy⟩ := GlobalTheory.T.exists_types_idempotent_coefficients B C W χ nd A hE hχ hlab hine hgood
  choose e he using hy
  obtain ⟨Y, hY, ⟨th⟩⟩ := GlobalTheory.T.exists_exponent_theta_data B C W nd tw hT e
  refine ⟨{ toLocStage := L
            nd := nd
            ntw := tw
            naut := A
            nbc := bc
            nexp := Y
            ntypes := T
            nStage_trivialCharacter_compat := hT0
            nStage_trivialCharacter_coeff_eq := fun g => by rw [hY]; exact he g
            nth := th
            nbr := fun i => hE.elim i
            nbr_ind := fun i => hE.elim i
            self_good := fun i => hE.elim i
            ntwbr := fun i => hT.elim i
            ntwbr_ind := fun i => hT.elim i
            loc_tie := fun i => hE.elim i
            bc_tie := fun i => hE.elim i
            rbar_tie := fun i => hE.elim i
            mtpar_tie := fun i => hE.elim i
            Z_tie := fun i => hE.elim i
            Zgood_tie := fun i => hE.elim i
            etaJ_tie := fun j w h1 h2 => ?_ }⟩
  rw [heta j w h1 h2]
  exact (Finset.sum_eq_zero fun i _ => hE.elim i).symm

end GlobalTheory.MemN
end

