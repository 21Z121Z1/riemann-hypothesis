import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0405
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCmExtensionMixedSpaceRealCoords
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.ReCoords

theorem comap_bij (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2) :
    Function.Bijective fun w : InfinitePlace E => w.comap (algebraMap F E) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨InfinitePlace.comap_surjective (k := F) (K := E), ?_⟩
  have h1 := IsTotallyComplex.finrank E
  have h2' := IsTotallyReal.finrank F
  have h3 := Module.finrank_mul_finrank ℚ F E
  rw [h2] at h3
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, IsTotallyReal.nrComplexPlaces_eq_zero F]
  omega

theorem re_embedding_comap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace E) (y : F) :
    ((w.comap (algebraMap F E)).embedding y).re = (w.embedding (algebraMap F E y)).re := by
  have key : ∀ φ : E →+* ℂ, (((InfinitePlace.mk φ).comap (algebraMap F E)).embedding y).re = (φ (algebraMap F E y)).re := by
    intro φ
    rw [InfinitePlace.comap_mk]
    rcases InfinitePlace.embedding_mk_eq (φ.comp (algebraMap F E)) with h | h
    · rw [h]; rfl
    · rw [h]; simp [ComplexEmbedding.conjugate_coe_eq]
  have := key w.embedding
  rwa [InfinitePlace.mk_embedding] at this

theorem mixedSpace_reCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : mixedEmbedding.mixedSpace F ≃L[ℝ] (InfinitePlace E → ℝ), MeasurePreserving e volume volume ∧ ∀ y : F, e (mixedEmbedding F y) = reV (algebraMap F E y) := by
  intro F E _ _ _ _ _ σ h
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  haveI : IsEmpty {w : InfinitePlace F // InfinitePlace.IsComplex w} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  let g : InfinitePlace E ≃ {v : InfinitePlace F // InfinitePlace.IsReal v} :=
    (Equiv.ofBijective _ (comap_bij F E h.2.2.1)).trans
      (Equiv.subtypeUnivEquiv (fun v : InfinitePlace F => IsTotallyReal.isReal v)).symm
  have hg : ∀ w, (g w).1 = w.comap (algebraMap F E) := fun w => rfl
  let L : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace E → ℝ) :=
    { toFun := fun x w => x.1 (g w)
      invFun := fun f => (fun v => f (g.symm v), 0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun x => Prod.ext (funext fun v => by simp) (Subsingleton.elim _ _)
      right_inv := fun f => funext fun w => by simp }
  refine ⟨L.toContinuousLinearEquiv, ?_, ?_⟩
  · haveI : IsProbabilityMeasure (volume : Measure ({w : InfinitePlace F // InfinitePlace.IsComplex w} → ℂ)) := by
      rw [volume_pi, Measure.pi_of_empty]; infer_instance
    have h1 : MeasurePreserving (Prod.fst : mixedEmbedding.mixedSpace F → _) volume volume :=
      measurePreserving_fst
    have h2 := volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace E => ℝ) g.symm
    have heq : (L.toContinuousLinearEquiv : mixedEmbedding.mixedSpace F → InfinitePlace E → ℝ) =
        (MeasurableEquiv.piCongrLeft (fun _ : InfinitePlace E => ℝ) g.symm) ∘ Prod.fst := by
      funext x w
      simp [L, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    rw [heq]
    exact h2.comp h1
  · intro y
    funext w
    show (mixedEmbedding F y).1 (g w) = _
    rw [mixedEmbedding.mixedEmbedding_apply_isReal, reV]
    rw [← Complex.ofReal_re (InfinitePlace.embedding_of_isReal _ y), InfinitePlace.embedding_of_isReal_apply, hg]
    exact re_embedding_comap w y

end GlobalTheory.SnMass.ReCoords
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainSndOfTwoSmulMem
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem exists_fundamentalDomain_snd_of_two_smul_mem {ι : Type} [Fintype ι]
    (Λ : Submodule ℤ ((ι → ℝ) × (ι → ℝ))) [DiscreteTopology Λ] :
    Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) = ⊤ →
    (∀ a b, (a, b) ∈ Λ → ((0 : ι → ℝ), (2 : ℝ) • b) ∈ Λ) →
    ∃ D : Set (ι → ℝ), MeasurableSet D ∧
      ∀ y, ∃! l, l ∈ {b : ι → ℝ | ∃ a, (a, b) ∈ Λ} ∧ y + l ∈ D := by
  intro hspan h2
  let L₂ : Submodule ℤ (ι → ℝ) := Λ.map (LinearMap.snd ℤ (ι → ℝ) (ι → ℝ))
  have hmem : ∀ b, b ∈ L₂ ↔ ∃ a, (a, b) ∈ Λ := by
    intro b
    simp only [L₂, Submodule.mem_map, LinearMap.snd_apply]
    constructor
    · rintro ⟨⟨a, b'⟩, h, rfl⟩; exact ⟨a, h⟩
    · rintro ⟨a, h⟩; exact ⟨(a, b), h, rfl⟩
  have hin : ∀ x : L₂, ((0 : ι → ℝ), (2 : ℝ) • (x : ι → ℝ)) ∈ Λ := by
    intro x
    obtain ⟨a, ha⟩ := (hmem x).1 x.2
    exact h2 a x ha
  haveI : DiscreteTopology L₂ := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : L₂ => (⟨((0 : ι → ℝ), (2 : ℝ) • (x : ι → ℝ)), hin x⟩ : Λ)) ?_ ?_
    · exact Continuous.subtype_mk
        (by fun_prop) _
    · intro x y hxy
      have h := congrArg (fun z : Λ => (z : (ι → ℝ) × (ι → ℝ)).2) hxy
      simp only at h
      exact Subtype.ext (smul_right_injective _ (two_ne_zero) h)
  haveI : IsZLattice ℝ L₂ := by
    refine ⟨?_⟩
    rw [eq_top_iff]
    intro y _
    have hy : ((0 : ι → ℝ), y) ∈ Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) := by
      rw [hspan]; trivial
    have := Submodule.mem_map_of_mem (f := LinearMap.snd ℝ (ι → ℝ) (ι → ℝ)) hy
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨⟨a, b⟩, h, rfl⟩
    exact (hmem b).2 ⟨a, h⟩
  refine ⟨latticeDomain L₂, measurableSet_latticeDomain L₂, fun y => ?_⟩
  obtain ⟨⟨l, hl⟩, h1, h3⟩ := existsUnique_add_mem_latticeDomain L₂ y
  refine ⟨l, ⟨(hmem l).1 hl, h1⟩, ?_⟩
  rintro m ⟨hm, hm'⟩
  exact congrArg Subtype.val (h3 ⟨m, (hmem m).2 hm⟩ hm')

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsNonarchimedeanLocalField
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData GlobalTheory.NonGenericCompare
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.LocFieldOfDVR

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero

theorem exists_pow_lt_of_lt_one (a c : ℤᵐ⁰) (ha : a ≠ 0) (ha1 : a < 1) (hc : c ≠ 0) :
    ∃ n : ℕ, a ^ n < c := by
  obtain ⟨a', rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  obtain ⟨c', rfl⟩ := WithZero.ne_zero_iff_exists.mp hc
  refine ⟨(Multiplicative.toAdd c').natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  rw [← WithZero.coe_one, WithZero.coe_lt_coe] at ha1
  rw [← Multiplicative.toAdd_lt, toAdd_pow, nsmul_eq_mul]
  rw [← Multiplicative.toAdd_lt, toAdd_one] at ha1
  push_cast
  have ha2 : Multiplicative.toAdd a' ≤ -1 := by omega
  nlinarith [mul_le_mul_of_nonneg_left ha2 (by positivity : (0 : ℤ) ≤ |Multiplicative.toAdd c'| + 1),
    neg_abs_le (Multiplicative.toAdd c')]

variable (o F : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

abbrev val : Valuation F ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal o).valuation F

abbrev valued : Valued F ℤᵐ⁰ := Valued.mk' (val o F)

def equivInt : o ≃+* (val o F).integer :=
  RingEquiv.ofBijective
    ((algebraMap o F).codRestrict (val o F).integer (fun a => valuation_le_one _ a))
    ⟨fun a b h => IsFractionRing.injective o F (congrArg Subtype.val h),
     fun x => by
      obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one x.2
      exact ⟨a, Subtype.ext ha⟩⟩

@[simp] theorem equivInt_val (a : o) : ((equivInt o F a : (val o F).integer) : F) = algebraMap o F a := rfl

variable {o F}

theorem mem_pow_iff {ϖ : o} (hϖ : Irreducible ϖ) (n : ℕ) (x : (val o F).integer) :
    x ∈ ((IsLocalRing.maximalIdeal o).map (equivInt o F)) ^ n ↔
      val o F (x : F) ≤ val o F (algebraMap o F ϖ) ^ n := by
  rw [← Ideal.map_pow, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton, (Valuation.integer.integers _).dvd_iff_le]
  simp only [map_pow, equivInt_val]
  exact Iff.rfl

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero
variable {o F : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

theorem isAdic_map {ϖ : o} (hϖ : Irreducible ϖ) :
    letI := valued o F
    IsAdic ((IsLocalRing.maximalIdeal o).map (equivInt o F)) := by
  letI := valued o F
  set J := (IsLocalRing.maximalIdeal o).map (equivInt o F)
  set π := algebraMap o F ϖ
  have hπ0 : val o F π ≠ 0 := by
    simp only [π, ne_eq, map_eq_zero]
    exact (IsFractionRing.injective o F).ne_iff' (map_zero _) |>.mpr hϖ.ne_zero
  have hπ1 : val o F π < 1 := (valuation_lt_one_iff_mem _ ϖ).mpr
    (by simpa [IsDiscreteValuationRing.maximalIdeal] using hϖ.not_isUnit)
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds (J ^ n).toAddSubgroup (g := 0) ?_
    rw [mem_nhds_subtype]
    refine ⟨{y | val o F y < val o F π ^ n}, ?_, fun y hy => ?_⟩
    · change _ ∈ 𝓝 (0 : F)
      rw [Valued.mem_nhds_zero]
      have hπne : π ≠ 0 := by rintro h; simp [h] at hπ0
      refine ⟨Units.mk0 ((val o F).restrict (π ^ n)) (by simp [hπne]), fun y hy => ?_⟩
      simp only [Units.val_mk0, Set.mem_setOf_eq] at hy ⊢
      have hy' : (val o F).restrict y < (val o F).restrict (π ^ n) := hy
      rw [Valuation.restrict_lt_iff] at hy'
      simpa [map_pow] using hy'
    · exact (mem_pow_iff hϖ n y).mpr (le_of_lt hy)
  · obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ _ _).mp hs
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hu
    have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one _ _ hπ0 hπ1 hγ0
    refine ⟨n, fun y hy => hus (hγ ?_)⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact ((mem_pow_iff hϖ n y).mp hy).trans_lt hn

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero
variable {o F : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

theorem compactSpace_integer [IsAdicComplete (IsLocalRing.maximalIdeal o) o]
    [Finite (IsLocalRing.ResidueField o)] :
    letI := valued o F
    CompactSpace (Valued.integer F) := by
  letI := valued o F
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible o
  letI : (Valued.v : Valuation F ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne (val o F) (e := 2) one_lt_two
  have hI := isAdic_map (F := F) hϖ
  have hpre : IsPrecomplete ((IsLocalRing.maximalIdeal o).map (equivInt o F)) (val o F).integer :=
    (IsPrecomplete.congr_ringEquiv _ _).mpr inferInstance
  haveI : IsUniformAddGroup (val o F).integer :=
    inferInstanceAs (IsUniformAddGroup (val o F).integer.toAddSubgroup)
  have hcomp : CompleteSpace (val o F).integer := (IsAdic.isPrecomplete_iff hI).mp hpre
  have hdvr : IsDiscreteValuationRing (Valued.integer F) :=
    inferInstanceAs (IsDiscreteValuationRing (val o F).integer)
  have hfin : Finite (IsLocalRing.ResidueField (Valued.integer F)) :=
    Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv (equivInt o F)).toEquiv
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨hcomp, hdvr, hfin⟩

theorem locallyCompactSpace [IsAdicComplete (IsLocalRing.maximalIdeal o) o]
    [Finite (IsLocalRing.ResidueField o)] :
    letI := valued o F
    LocallyCompactSpace F := by
  letI := valued o F
  have := compactSpace_integer (o := o) (F := F)
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup
    (isCompact_iff_compactSpace.mpr this) ((Valued.isOpen_integer F).mem_nhds (zero_mem _))

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero

theorem exists_isNonarchimedeanLocalField : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [IsAdicComplete (IsLocalRing.maximalIdeal o) o] [Finite (IsLocalRing.ResidueField o)] [Field F] [Algebra o F] [IsFractionRing o F], ∃ (_ : ValuativeRel F) (_ : TopologicalSpace F), IsNonarchimedeanLocalField F ∧ ∀ x : F, x ∈ 𝒪[F] ↔ ∃ a : o, algebraMap o F a = x := by
  intro o F _ _ _ _ _ _ _ _
  letI := valued o F
  letI vr : ValuativeRel F := .ofValuation (val o F)
  haveI : (val o F).Compatible := .ofValuation _
  refine ⟨vr, inferInstance, ?_, fun x => ?_⟩
  · have h1 : IsValuativeTopology F :=
      IsValuativeTopology.of_mem_nhds_iff_vle (val o F) (fun {s x} => Valued.mem_nhds)
    have h2 : ValuativeRel.IsNontrivial F :=
      (ValuativeRel.isNontrivial_iff_isNontrivial (val o F)).mpr inferInstance
    have h3 : LocallyCompactSpace F := locallyCompactSpace (o := o) (F := F)
    exact {}
  · rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation F).vle_one_iff, (val o F).vle_one_iff]
    exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one,
      fun ⟨a, ha⟩ => ha ▸ valuation_le_one _ a⟩

end GlobalTheory.LocFieldOfDVR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsListProd
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ProdChar

theorem isChar_of_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem eq_zero_of_ip {G : Type} [Group G] [Fintype G] {f : G → ℂ} (hf : IsClass f)
    (h : ∀ ρ, IsIrr ρ → ip f ρ = 0) : f = 0 := by
  calc f = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, ip f ρ • ρ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G f).2.1 hf
    _ = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, (0 : G → ℂ) :=
        finsum_mem_congr rfl fun ρ hρ => by rw [h ρ hρ, zero_smul]
    _ = 0 := finsum_mem_zero _

theorem ip_prod {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ)
    (α : G₁ → ℂ) (β : G₂ → ℂ) :
    ip Φ (fun z => α z.1 * β z.2) = ip (fun y => ip (fun x => Φ (x, y)) α) β := by
  simp only [ip, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, Prod.fst_inv, Prod.snd_inv,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

theorem isIrr_prod {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    {α : G₁ → ℂ} {β : G₂ → ℂ} (hα : IsIrr α) (hβ : IsIrr β) :
    IsIrr (fun z : G₁ × G₂ => α z.1 * β z.2) := by
  have hA : IsChar (fun z : G₁ × G₂ => α z.1) :=
    (GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul).1 (G₁ × G₂) G₁ (MonoidHom.fst G₁ G₂) α (isChar_of_irr hα)
  have hB : IsChar (fun z : G₁ × G₂ => β z.2) :=
    (GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul).1 (G₁ × G₂) G₂ (MonoidHom.snd G₁ G₂) β (isChar_of_irr hβ)
  have hC : IsChar (fun z : G₁ × G₂ => α z.1 * β z.2) := (GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul).2 (G₁ × G₂) _ _ hA hB
  apply (GlobalTheory.T.character_decomposition_and_classFunction_expansion (G₁ × G₂) _).2.2.2.1 hC
  have h1 : ip α α = 1 := by simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G₁ α α hα hα).2.2
  have h2 : ip β β = 1 := by simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G₂ β β hβ hβ).2.2
  have key : ∀ y, ip (fun x => α x * β y) α = β y := by
    intro y
    have e : ip (fun x => α x * β y) α = β y * ip α α := by
      simp only [ip, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e, h1, mul_one]
  rw [ip_prod]
  simp only [key]
  exact h2

theorem exists_prod_of_isIrr {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    {ρ : G₁ × G₂ → ℂ} (hρ : IsIrr ρ) :
    ∃ p : (G₁ → ℂ) × (G₂ → ℂ), (IsIrr p.1 ∧ IsIrr p.2) ∧ ρ = fun z => p.1 z.1 * p.2 z.2 := by
  by_contra hne
  push_neg at hne
  have hcl : IsClass ρ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ ρ).2.2.1 (isChar_of_irr hρ)
  have hip : ∀ α β, IsIrr α → IsIrr β → ip ρ (fun z : G₁ × G₂ => α z.1 * β z.2) = 0 := by
    intro α β hα hβ
    rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ _ hρ (isIrr_prod hα hβ)).2.2, if_neg (by simpa using hne (α, β) ⟨hα, hβ⟩)]
  have hrow : ∀ y, (fun x => ρ (x, y)) = 0 := by
    intro y
    apply eq_zero_of_ip
    · intro x k
      simpa using hcl (x, y) (k, 1)
    · intro α hα
      have hF : (fun y' => ip (fun x => ρ (x, y')) α) = 0 := by
        apply eq_zero_of_ip
        · intro y' h
          have e : (fun x => ρ (x, h * y' * h⁻¹)) = fun x => ρ (x, y') := by
            funext x
            simpa using hcl (x, y') (1, h)
          exact congrArg (fun f => ip f α) e
        · intro β hβ
          exact (ip_prod ρ α β).symm.trans (hip α β hα hβ)
      exact congrFun hF y
  have hz : ρ = 0 := by
    funext z
    obtain ⟨x, y⟩ := z
    exact congrFun (hrow y) x
  have h1 := (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ ρ hρ hρ).2.2
  rw [if_pos rfl, hz] at h1
  simp [ip] at h1

private theorem sum_irr_prod_eq_sum_irr_mul {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    (L : List (G₁ × G₂ → ℂ)) (hL : ∀ ρ ∈ L, IsIrr ρ) :
    ∃ L' : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L', IsIrr p.1 ∧ IsIrr p.2) ∧
      ∀ x y, L.sum (x, y) = (L'.map fun p => p.1 x * p.2 y).sum := by
  induction L with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons ρ L ih =>
    obtain ⟨p, hp, rfl⟩ := exists_prod_of_isIrr (hL ρ (by simp))
    obtain ⟨L', hL', hsum⟩ := ih fun r hr => hL r (List.mem_cons_of_mem _ hr)
    refine ⟨p :: L', ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact hL' q hq
    · intro x y
      rw [List.sum_cons, Pi.add_apply, hsum]
      simp

theorem exists_list_prod : ∀ (G₁ G₂ : Type) [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ),
    IsChar Φ → ∃ L : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧
      ∀ x y, Φ (x, y) = (L.map fun p => p.1 x * p.2 y).sum := by
  intro G₁ G₂ _ _ _ _ Φ hΦ
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion (G₁ × G₂) Φ).1 hΦ
  exact sum_irr_prod_eq_sum_irr_mul L hL

end GlobalTheory.GLm.ProdChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMixedSpaceReImCoordsTotallyComplex
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.SnMass.SkewVol

open NumberField.InfinitePlace

def cxPlaceEquiv (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    {w : InfinitePlace E // IsComplex w} ≃ InfinitePlace E :=
  Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w

def mixedCoords (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    mixedEmbedding.mixedSpace E ≃ₗ[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)) where
  toFun x := (fun w => (x.2 ⟨w, IsTotallyComplex.isComplex w⟩).re,
    fun w => (x.2 ⟨w, IsTotallyComplex.isComplex w⟩).im)
  invFun y := (fun w => absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)),
    fun w => ⟨y.1 w.1, y.2 w.1⟩)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  left_inv x := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · exact absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1))
    · apply Complex.ext <;> rfl
  right_inv y := rfl

private theorem measurePreserving_mixedSpace_snd (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    MeasurePreserving (Prod.snd : mixedEmbedding.mixedSpace E → ({w : InfinitePlace E // IsComplex w} → ℂ))
      volume volume := by
  have : IsEmpty {w : InfinitePlace E // IsReal w} :=
    ⟨fun w => not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1) w.2⟩
  have h : (volume : Measure ({w : InfinitePlace E // IsReal w} → ℝ)) = Measure.dirac 0 := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨measurable_snd, ?_⟩
  show Measure.map Prod.snd ((volume : Measure ({w : InfinitePlace E // IsReal w} → ℝ)).prod volume) = volume
  rw [h, Measure.map_snd_prod]
  simp

theorem measurePreserving_mixedCoords (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    MeasurePreserving (mixedCoords E) volume volume := by
  have h2 := measurePreserving_piCongrLeft (fun _ : InfinitePlace E => (volume : Measure ℂ))
    (cxPlaceEquiv E)
  have h3 := measurePreserving_pi (fun _ : InfinitePlace E => (volume : Measure ℂ))
    (fun _ => (volume : Measure (ℝ × ℝ))) (fun _ => Complex.volume_preserving_equiv_real_prod)
  have h4 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (InfinitePlace E)
    (fun _ => (volume : Measure ℝ)) (fun _ => (volume : Measure ℝ))
  have key := h4.comp (h3.comp (h2.comp (measurePreserving_mixedSpace_snd E)))
  have e : (⇑(mixedCoords E)) = ⇑(MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (InfinitePlace E)) ∘
      (fun a i => Complex.measurableEquivRealProd (a i)) ∘
        ⇑(MeasurableEquiv.piCongrLeft (fun _ => ℂ) (cxPlaceEquiv E)) ∘ Prod.snd := by
    funext x
    ext w <;> rfl
  rw [e]
  exact key

theorem mixedCoords_mixedEmbedding (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (x : E) : mixedCoords E (mixedEmbedding E x) = (reV x, imV x) := by
  ext w <;> simp [mixedCoords, reV, imV, mixedEmbedding.mixedEmbedding_apply_isComplex]

theorem mixedSpace_reIm_coords : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E →
    ∃ e : mixedEmbedding.mixedSpace E ≃L[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)),
      MeasurePreserving e volume volume ∧ ∀ x : E, e (mixedEmbedding E x) = (reV x, imV x) := by
  intro E _ _ hE
  have := hE
  exact ⟨(mixedCoords E).toContinuousLinearEquiv, by
    simpa using measurePreserving_mixedCoords E, fun x => by
    simpa using mixedCoords_mixedEmbedding E x⟩

end GlobalTheory.SnMass.SkewVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueLayeredStrictFundamentalDomainStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_layered_strictFundamentalDomain : ∀ {G X B : Type} [Group G] [Finite B] {V : B → Type} [∀ β, AddCommGroup (V β)] (ρ : G → X → X) (NN : Set X) (o : X) (deg : B → ℕ) (c : ∀ β, X → V β) (L D : ∀ β, Set (V β)), o ∈ NN → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ β, (0 : V β) ∈ L β) → (∀ β v, ∃! l, l ∈ L β ∧ v + l ∈ D β) → (∀ β, c β o = 0) → (∀ (d : ℕ) (g : G), (∀ β, deg β < d → c β (ρ g o) = 0) → ∀ x ∈ NN, ∀ β, deg β ≤ d → c β (ρ g x) = c β x + c β (ρ g o)) → (∀ (g : G) (β : B), (∀ β', deg β' < deg β → c β' (ρ g o) = 0) → c β (ρ g o) ∈ L β) → (∀ β, ∀ l ∈ L β, ∃ g : G, c β (ρ g o) = l ∧ ∀ β', β' ≠ β → deg β' ≤ deg β → c β' (ρ g o) = 0) → (∀ g : G, (∀ β, c β (ρ g o) = 0) → g = 1) → ∀ x ∈ NN, ∃! g : G, ∀ β, c β (ρ g x) ∈ D β := by
  first | exact @GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain | exact GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain | (intros; apply GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagExplicitConstantLeExpNegHalfStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_explicit_constant_le_exp_neg_half : ConstantBound := by
  first | exact @GlobalTheory.FlagMeas.constantBound | exact GlobalTheory.FlagMeas.constantBound | (intros; apply GlobalTheory.FlagMeas.constantBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentBlockUpperUnitriangularStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotent_block_upper_unitriangular : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), x ∈ Nset k r → Dep k r 1 (x - 1) := by
  first | exact @GlobalTheory.SnMass.VolN.DepOne.dep_one | exact GlobalTheory.SnMass.VolN.DepOne.dep_one | (intros; apply GlobalTheory.SnMass.VolN.DepOne.dep_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNMKIntegrationPiProductStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawaNMKIntegration_pi_product : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul₂ (G i)] (μ μN μM μK : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μN i)] [∀ i, SigmaFinite (μM i)] [∀ i, SigmaFinite (μK i)] (C c : ι → ENNReal) (δ : ∀ i, G i → ENNReal), (∀ i, C i ≠ 0) → (∀ i, C i ≠ ⊤) → (∀ i, Measurable (δ i)) → (∀ i, ∀ φ : G i → ENNReal, Measurable φ → C i * ∫⁻ g, φ g ∂(μ i) = c i * ∫⁻ u, ∫⁻ m, δ i m * ∫⁻ k, φ (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i)) → ∀ φ : (∀ i, G i) → ENNReal, Measurable φ → (∏ i, C i) * ∫⁻ g, φ g ∂(Measure.pi μ) = (∏ i, c i) * ∫⁻ u, ∫⁻ m, (∏ i, δ i (m i)) * ∫⁻ k, φ (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) ∂(Measure.pi μN) := by
  first | exact @GlobalTheory.NMKProd.prod_formula | exact GlobalTheory.NMKProd.prod_formula | (intros; apply GlobalTheory.NMKProd.prod_formula <;> assumption)
end

