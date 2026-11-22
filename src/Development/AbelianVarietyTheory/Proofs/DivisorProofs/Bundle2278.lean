import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolume
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open MeasureTheory
open scoped Pointwise

theorem packing_set_covolume_le :
    ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) (Γ : Subgroup H), Countable Γ → ∃ F : Set H, MeasurableSet F ∧ covolume Γ H ν ≤ ν F ∧ ∀ γ ∈ Γ, ∀ y ∈ F, γ * y ∈ F → γ = 1 := by
  intro H _ _ _ ν Γ _
  classical
  by_cases hF : HasFundamentalDomain Γ H ν
  swap
  · refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
    · simp [covolume, hF]
    · intro γ _ y hy; exact absurd hy (Set.notMem_empty y)
  · set s := hF.ExistsIsFundamentalDomain.choose with hs_def
    have hs : IsFundamentalDomain Γ s ν := hF.ExistsIsFundamentalDomain.choose_spec
    have hcov : covolume Γ H ν = ν s := by simp [covolume, hF, hs_def]
    obtain ⟨t, hts, htm, hte⟩ := hs.nullMeasurableSet.exists_measurable_subset_ae_eq
    have hsmul : ∀ g : Γ, (g • t : Set H) = (fun y => (g : H)⁻¹ * y) ⁻¹' t := by
      intro g; ext y
      simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
    have hmeas : ∀ g : Γ, MeasurableSet (g • t : Set H) := by
      intro g; rw [hsmul g]; exact (measurable_const_mul _) htm
    let U : Set H := ⋃ g : {g : Γ // g ≠ 1}, (g.1 • t : Set H)
    have hUm : MeasurableSet U := MeasurableSet.iUnion (fun g => hmeas g.1)
    have hnull : ν (t ∩ U) = 0 := by
      rw [Set.inter_iUnion]
      refine measure_iUnion_null (fun g => ?_)
      have h1 := hs.aedisjoint (Ne.symm g.2 : (1 : Γ) ≠ g.1)
      have h2 : ν ((1 : Γ) • s ∩ g.1 • s) = 0 := h1
      rw [one_smul] at h2
      exact measure_mono_null (Set.inter_subset_inter hts (Set.smul_set_mono hts)) h2
    refine ⟨t \ U, htm.diff hUm, ?_, ?_⟩
    · rw [hcov, ← Set.sdiff_self_inter, measure_sdiff_null hnull]
      exact (measure_congr hte).ge
    · intro γ hγ y hy hγy
      by_contra hne
      have hne' : (⟨γ, hγ⟩ : Γ) ≠ 1 := fun h => hne (congrArg Subtype.val h)
      apply hγy.2
      refine Set.mem_iUnion.2 ⟨⟨⟨γ, hγ⟩, hne'⟩, ?_⟩
      exact ⟨y, hy.1, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntForm
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.ConeInterior

section Help

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem exists_nat_comb {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (h : toReal β = ∑ i, c i • toReal (γ i)) : ∃ n : Fin m → ℕ, β = ∑ i, n i • γ i := by
  classical
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  have hz : ∀ i, c i = (f i ⟨β, hβ⟩ : ℤ) := fun i => by
    have h0 : ∑ o : Option (Fin m), (Option.elim o (-1) c) • toReal ((balForms bar X).subtype
        (Option.elim o (⟨β, hβ⟩ : balForms bar X) fun k => ⟨γ k, hγ.mem k⟩)) = 0 := by
      rw [Fintype.sum_option]
      simp only [Option.elim_none, Option.elim_some, Submodule.subtype_apply, h, neg_one_smul, neg_add_cancel]
    have := sum_mul_eq_zero_of_sum_toReal Subtype.val_injective (f i) h0
    rw [Fintype.sum_option] at this
    simp only [Option.elim_none, Option.elim_some, hf] at this
    simp at this
    linarith
  have hn : ∀ i, ∃ n : ℕ, c i = n := fun i => by
    have h1 : (0 : ℤ) ≤ f i ⟨β, hβ⟩ := by exact_mod_cast (hz i ▸ hc i : (0 : ℝ) ≤ (f i ⟨β, hβ⟩ : ℤ))
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h1
    exact ⟨n, by rw [hz i, hn, Int.cast_natCast]⟩
  choose n hn using hn
  refine ⟨n, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ h a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hn, nsmul_eq_mul] at this ⊢
  exact_mod_cast this

theorem exists_pos_comb (hP : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : toReal β ∈ psdCone bar X) :
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (cf : Fin m → ℕ),
      IsCone bar φ γ ∧ (∀ j, 0 < cf j) ∧ β = ∑ j, cf j • γ j := by
  classical
  obtain ⟨m, γ, c, hγ, hc, h⟩ := hP.cover _ hp
  obtain ⟨n, hn⟩ := exists_nat_comb hγ hβ hc h
  let S : Finset (Fin m) := Finset.univ.filter fun i => 0 < n i
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Finset.univ.map s = S := Finset.map_orderEmbOfFin_univ S rfl
  refine ⟨S.card, fun i => γ (s i), fun i => n (s i), hP.face _ _ γ s hγ, fun j => ?_, ?_⟩
  · exact (Finset.mem_filter.1 (S.orderEmbOfFin_mem rfl j)).2
  · rw [hn, ← Finset.sum_map Finset.univ s fun i => n i • γ i, hs]
    refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_).symm
    have : n i = 0 := by simpa [S] using hi
    rw [this, zero_smul]

end Help

theorem exists_pos_comb_int : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → toReal b ∈ psdCone (id : ℤ → ℤ) (Fin r → ℤ) → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) (cf : Fin m → ℕ), IsCone id φ γ ∧ (∀ j, 0 < cf j) ∧ b = ∑ j, cf j • γ j := by
  intro g φ hφ r hr b hb hp
  exact exists_pos_comb (hφ (Fin r → ℤ) (by simpa using hr)) (mem_balForms_int.2 hb) hp

end GlobalTheory.ConeInterior
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleDiv

open IsLocalRing

theorem formallyEtale_of_bijective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) : f.FormallyEtale := by
  algebraize [f]
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)

theorem formallyEtale_of_comp_bijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hg : Function.Bijective g) (h : (g.comp f).FormallyEtale) :
    f.FormallyEtale := by
  let e := RingEquiv.ofBijective g hg
  have : f = (e.symm : T →+* S).comp (g.comp f) := by
    ext x
    exact (e.symm_apply_apply (f x)).symm
  rw [this]
  exact h.comp (formallyEtale_of_bijective _ e.symm.bijective)

theorem formallyEtale_stalkMap {M W : Scheme.{0}} (f : M ⟶ W) (U : M.Opens)
    [Etale (U.ι ≫ f)] (w : U.toScheme) : (f.stalkMap (U.ι w)).hom.FormallyEtale := by
  have hu := FormallyUnramified.stalkMap (U.ι ≫ f) w
  have hs : ((U.ι ≫ f).stalkMap w).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp ((U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ w))
  have h : ((U.ι ≫ f).stalkMap w).hom.FormallyEtale := by
    algebraize [((U.ι ≫ f).stalkMap w).hom]
    exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  have : IsIso (U.ι.stalkMap w) := inferInstance
  rw [Scheme.Hom.stalkMap_comp] at h
  exact formallyEtale_of_comp_bijective (f.stalkMap (U.ι w)).hom (U.ι.stalkMap w).hom
    (ConcreteCategory.bijective_of_isIso _) h

theorem strictMono_ι {M : Scheme.{0}} (U : M.Opens) : StrictMono U.ι := by
  have hi := U.ι.isOpenEmbedding.isInducing
  intro a b h
  refine lt_of_le_not_ge ?_ ?_
  · exact hi.specializes_iff.2 h.le
  · exact fun h' => h.not_ge (hi.specializes_iff.1 h')

theorem map_maximalIdeal_stalk {M W : Scheme.{0}} (f : M ⟶ W) [LocallyOfFiniteType f] (z : M)
    (h : (f.stalkMap z).hom.FormallyEtale) :
    (maximalIdeal (W.presheaf.stalk (f z))).map (f.stalkMap z).hom =
      maximalIdeal (M.presheaf.stalk z) := by
  have hft := LocallyOfFiniteType.stalkMap f z
  algebraize [(f.stalkMap z).hom]
  have : IsLocalHom (algebraMap (W.presheaf.stalk (f z)) (M.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
  exact Algebra.FormallyUnramified.map_maximalIdeal

theorem log_ordFrac_map {K L : Type} [Field K] [Field L] (V : ValuationSubring K)
    (V' : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing V']
    (ρ : K →+* L) (ψ : V →+* V') (hψ : ∀ a, (ψ a : L) = ρ a) {t : V} (ht : Irreducible t)
    (ht' : Irreducible (ψ t)) {g : K} (hg : g ≠ 0) :
    WithZero.log (Ring.ordFrac V' (ρ g)) = WithZero.log (Ring.ordFrac V g) := by
  obtain ⟨m, u, rfl⟩ := exists_eq_unit_mul_zpow (F := K) ht hg
  have h1 := ordTop_vw_unit_mul_zpow (F := K) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := L) ht' (Units.map ψ.toMonoidHom u) m
  have e : ρ (algebraMap V K u * algebraMap V K t ^ m) =
      algebraMap V' L (Units.map ψ.toMonoidHom u) * algebraMap V' L (ψ t) ^ m := by
    rw [map_mul, map_zpow₀]
    simp [hψ]
  rw [← e] at h2
  rw [ordTop_vw_of_ne_zero _ hg, WithTop.coe_inj] at h1
  rw [ordTop_vw_of_ne_zero _ ((map_ne_zero ρ).2 hg), WithTop.coe_inj] at h2
  rw [h1, h2]

theorem isFreeGen_formMap {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] {α : k →+* A}
    {β : k →+* B} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β) {D : ℕ}
    {ω : Forms α D} (hω : IsFreeGen A ω) : IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem maximalIdeal_eq_bot {X : Scheme.{0}} [IsIntegral X] {x : X} (h : Order.coheight x = 0) :
    maximalIdeal (X.presheaf.stalk x) = ⊥ := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h.le
  exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime ⊥).symm

theorem coheight_apply_eq_one {M W : Scheme.{0}} [IsIntegral W] (f : M ⟶ W) [LocallyOfFiniteType f]
    (U : M.Opens) [Etale (U.ι ≫ f)] (w : U.toScheme) (h1 : Order.coheight (U.ι w) = 1)
    (hB : maximalIdeal (M.presheaf.stalk (U.ι w)) ≠ ⊥) : Order.coheight (f (U.ι w)) = 1 := by
  have hle : Order.coheight w ≤ 1 :=
    h1 ▸ Order.coheight_le_coheight_apply_of_strictMono _ (strictMono_ι U) w
  have hle' := GlobalTheory.GenExtendNormal.coheight_apply_le_one (U.ι ≫ f) (Flat.generalizingMap _) w hle
  refine le_antisymm hle' ?_
  rw [Order.one_le_iff_ne_zero]
  intro h0
  apply hB
  rw [← map_maximalIdeal_stalk f _ (formallyEtale_stalkMap f U w), maximalIdeal_eq_bot h0,
    Ideal.map_bot]

theorem exists_isAt_ord_formOrd : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f]
    (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens),
    Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ E' : DivOver (f ≫ p), E'.IsAt z →
    ∃ E : DivOver p, E.IsAt (f z) ∧
      (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧
      ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  intro M W _ _ _ _ p f _ n _ _ U hU z hz E' hE'
  haveI := hU
  obtain ⟨w, rfl⟩ : ∃ w : U.toScheme, U.ι w = z := ⟨⟨z, hz⟩, rfl⟩
  haveI := SmoothOfRelativeDimension.smooth n p
  haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme W := GlobalTheory.ModifSections.isNormalScheme_of_smooth p
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f p
  haveI hB : IsDiscreteValuationRing (M.presheaf.stalk (U.ι w)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing hE'.equiv.symm
  have hφ := formallyEtale_stalkMap f U w
  have hmax := map_maximalIdeal_stalk f (U.ι w) hφ
  have hc := coheight_apply_eq_one f U w hE'.coheight_eq_one
    (IsDiscreteValuationRing.not_a_field _)
  obtain ⟨E, hE⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hc
  haveI hA : IsDiscreteValuationRing (W.presheaf.stalk (f (U.ι w))) :=
    GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hc
  let ψ : E.ring →+* E'.ring :=
    hE'.equiv.toRingHom.comp ((f.stalkMap (U.ι w)).hom.comp hE.equiv.symm.toRingHom)
  have hψ : ∀ a, (ψ a : M.functionField) = functionFieldMap f a := by
    intro a
    obtain ⟨b, rfl⟩ := hE.equiv.surjective a
    have e : ψ (hE.equiv b) = hE'.equiv (f.stalkMap (U.ι w) b) := by
      simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    rw [e]
    exact (functionFieldMap_algebraMap f (U.ι w) b).symm
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (W.presheaf.stalk (f (U.ι w)))
  have ht' : Irreducible (f.stalkMap (U.ι w) t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at ht ⊢
    rw [← hmax, ht, Ideal.map_span, Set.image_singleton]
  have htE : Irreducible (hE.equiv t) := ht.map hE.equiv
  have htE' : Irreducible (ψ (hE.equiv t)) := by
    have e : ψ (hE.equiv t) = hE'.equiv (f.stalkMap (U.ι w) t) := by
      simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    rw [e]
    exact ht'.map hE'.equiv
  have hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := fun g =>
    log_ordFrac_map E.ring E'.ring (functionFieldMap f) ψ hψ htE htE' g.ne_zero
  refine ⟨E, hE, hord, fun η hη => ?_⟩
  have hn : topologicalKrullDim W = n := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth W p n
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hn
  obtain ⟨c, rfl⟩ := (E.isFreeGen_toRat hω).2 η
  have hc0 : c ≠ 0 := fun h => hη (by rw [h]; exact zero_smul _ _)
  have hconst : ψ.comp E.const = E'.const := RingHom.ext fun a => Subtype.ext
    ((hψ _).trans (RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) a))
  have hψFE : ψ.FormallyEtale :=
    RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp
      (formallyEtale_of_bijective _ hE.equiv.symm.bijective) hφ)
      (formallyEtale_of_bijective _ hE'.equiv.bijective)
  have h3 : ((functionFieldMap f).comp E.ring.subtype).comp E.const = Cartier.constFn (f ≫ p) := by
    ext a
    exact RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) a
  have e1 : GlobalTheory.EtaleKlt.ratPull p f n (E.toRat n ω) =
      E'.toRat n (TopForm.formMap n ψ hconst ω) := by
    change TopForm.formMap n (functionFieldMap f) _ (TopForm.formMap n E.ring.subtype rfl ω) =
      TopForm.formMap n E'.ring.subtype rfl (TopForm.formMap n ψ hconst ω)
    exact (formMap_formMap E.ring.subtype (functionFieldMap f)
      ((functionFieldMap f).comp E.ring.subtype) rfl _ _ h3 ω).trans
      (formMap_formMap ψ E'.ring.subtype ((functionFieldMap f).comp E.ring.subtype)
        (RingHom.ext hψ) _ _ h3 ω).symm
  have h1 : E.formOrd (c • E.toRat n ω) = E.ord (Units.mk0 c hc0) :=
    DivOver.IsFormOrd.formOrd_eq hη ⟨ω, hω, Units.mk0 c hc0, rfl, rfl⟩
  have hη' : GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω) ≠ 0 := by
    have hfree := E'.isFreeGen_toRat (isFreeGen_formMap hψFE hconst hω)
    rw [map_smulₛₗ, e1]
    intro h0
    have := hfree.1 (a₁ := functionFieldMap f c) (a₂ := 0) (by simp only [h0, zero_smul])
    exact hc0 ((map_eq_zero _).1 this)
  have h2 : E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω)) =
      E'.ord (Units.map (functionFieldMap f).toMonoidHom (Units.mk0 c hc0)) :=
    DivOver.IsFormOrd.formOrd_eq hη' ⟨_, isFreeGen_formMap hψFE hconst hω, _,
      by rw [map_smulₛₗ, e1]; rfl, rfl⟩
  rw [h1, h2, hord]

end GlobalTheory.EtaleDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTangentLiftOfModelTangentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_tangent_lift_of_modelTangent : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), ∃ w : epsOver V V ⟶ G.G, IsTan w ∧ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ := by
  first | exact @GlobalTheory.TanLiftPull.exists_isTan_lift | exact GlobalTheory.TanLiftPull.exists_isTan_lift | (intros; apply GlobalTheory.TanLiftPull.exists_isTan_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPuncturedDiscInjectiveEvalAtPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_puncturedDisc_injective_evalAtPoint : ∀ (ε : ℝ) (S : Set (PowerSeries ℂ)), 0 < ε → S.Countable → (∀ Φ ∈ S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) → ∃ (u : ℂ) (i : Subring.closure S →+* ℂ), u ≠ 0 ∧ ‖u‖ < ε ∧ Function.Injective i ∧ ∀ Φ : Subring.closure S, i Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n := by
  first | exact @GlobalTheory.exists_injective_evalAt_closure | exact GlobalTheory.exists_injective_evalAt_closure | (intros; apply GlobalTheory.exists_injective_evalAt_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalCoordinates_extend_projectiveSpace : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (N : ℕ) (U : Y.Opens)
    (φ : U.toScheme ⟶ PSpace F N), φ ≫ PSpace.str F N = U.ι ≫ p → (U : Set Y).Nonempty →
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        (∀ y' : Y', ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
          (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k))) →
        ∃ g : Y' ⟶ PSpace F N, g ≫ PSpace.str F N = s ≫ p ∧ (s ⁻¹ᵁ U).ι ≫ g = (s ∣_ U) ≫ φ := by
  first | exact @GlobalTheory.ProjSpace.exists_ratCoords_extend | exact GlobalTheory.ProjSpace.exists_ratCoords_extend | (intros; apply GlobalTheory.ProjSpace.exists_ratCoords_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarCuspFormIntegralStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_cusp_form_integral : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n → ∀ f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n, ∃ s : Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  first | exact @GlobalTheory.LargeAll.exists_smul_nonneg_large | exact GlobalTheory.LargeAll.exists_smul_nonneg_large | (intros; apply GlobalTheory.LargeAll.exists_smul_nonneg_large <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarMatrixBetweenKeyDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_matrix_between_keyData : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (th th' : P.L.Sec) (v v' : Fin P.g → (epsR K ⟶ P.A)), (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th) → (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th') → IsLieBasis v → IsLieBasis v' → ∃ (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), a ≠ 0 ∧ (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) ∧ ∀ i, IsLieComb (M i) v (v' i) := by
  first | exact @GlobalTheory.MBLow.TwoData.exists_scalar_matrix | exact GlobalTheory.MBLow.TwoData.exists_scalar_matrix | (intros; apply GlobalTheory.MBLow.TwoData.exists_scalar_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingClosedPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_separating_closed_point : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB → ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U → (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) → ∃ s : L.Sec, x ∈ nonzeroLocus s ∧ ∀ y ∈ J.support, y ≠ x → y ∉ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated_zero_else | exact GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated_zero_else | (intros; apply GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated_zero_else <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianMapModelOfIntegralFramedPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianMap_model_of_integralFramedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y : FrPt Xo c T.Fr) (x : Sp T.V ⟶ Y.X), spMap (algebraMap T.V T.Fr) ≫ x = GlobalTheory.FlagMod.frX y ≫ Y.j → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∃ (ψ : SABMap G Y.t x) (ρ : t'.G.left ⟶ Y.oF.t.G.left), ρ ≫ Y.m0.toSABMap.φ = m1.φ ∧ ρ ≫ Y.oF.t.G.hom = t'.G.hom ≫ GlobalTheory.FlagMod.frX y ∧ ρ ≫ Y.m.φ = m2.φ ≫ ψ.φ := by
  first | exact @GlobalTheory.exists_sabMap_model_of_integral_frPt | exact GlobalTheory.exists_sabMap_model_of_integral_frPt | (intros; apply GlobalTheory.exists_sabMap_model_of_integral_frPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallScalarReflexIdealSelfDualLatticeStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_scalar_reflexIdeal_selfDualLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : Coeff l) (n : ℕ) (La : GenLat E n), La.Unimod → ∃ s : c.F, s ≠ 0 ∧ Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c La.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ ∧ ∀ σ : c.F →+* ℂ, ‖σ s‖ ^ 2 * ((La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index : ℝ) ^ (Dw.p + Dw.q) ≤ Real.exp (fieldSz c.F) ^ 2 := by
  first | exact @GlobalTheory.SmallScal.exists_small_scalar | exact GlobalTheory.SmallScal.exists_small_scalar | (intros; apply GlobalTheory.SmallScal.exists_small_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallTorsionSetForEndomorphismStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_torsion_set_for_endomorphism : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (α : G ⟶ G) (n m g r : ℕ) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom α → (∀ a, act.act a ≫ α = α ≫ act.act a) → 0 < n → (fun f : G ⟶ G => f ≫ α)^[n] (𝟙 G) = 𝟙 G → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → r + 1 < g → (∃ T : Finset (𝟙_ (Over (Sp k)) ⟶ G), T.card ≤ g ^ r ∧ ∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → x ∈ T) → (∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → (fun z : 𝟙_ (Over (Sp k)) ⟶ G => (z ≫ α) * z⁻¹)^[m] x = 1) → α = 𝟙 G := by
  first | exact @GlobalTheory.NeatUnip.finite_order_unipotent_eq_id | exact GlobalTheory.NeatUnip.finite_order_unipotent_eq_id | (intros; apply GlobalTheory.NeatUnip.finite_order_unipotent_eq_id <;> assumption)
end

