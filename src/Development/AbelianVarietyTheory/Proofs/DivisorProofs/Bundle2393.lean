import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalChartLiftsOfMorphism
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

section Chart

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

theorem chart_spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem chart_spMap_inj {A B : Type} [CommRing A] [CommRing B] {a b : A →+* B} (e : spMap a = spMap b) : a = b := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

variable (hI : I ^ 2 = 0) {X₀ Z₀ X Z : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {t₀ : Z₀ ⟶ Sp R₀} {s : X ⟶ Sp R}
  {t : Z ⟶ Sp R} {i : X₀ ⟶ X} {k : Z₀ ⟶ Z} {S : Sys I π s₀} {S' : Sys I π t₀} (P : S.Presents s i)
  (P' : S'.Presents t k) {f₀ : Z₀ ⟶ X₀} {f : Z ⟶ X} (hkf : k ≫ f = f₀ ≫ i)

include hkf in

theorem chart_red (p : Pair f₀) :
    spMap (S'.p (Opposite.op p.1.1)) ≫ P'.y (Opposite.op p.1.1) ≫ f =
      spMap (GlobalTheory.CechDR.secPull s₀ t₀ p) ≫ spMap (S.p (Opposite.op p.1.2)) ≫ P.y (Opposite.op p.1.2) := by
  rw [← Category.assoc, P'.red, P.red, Category.assoc, hkf, ← Category.assoc, ← Category.assoc,
    ← GlobalTheory.CechDR.secPull_affPt s₀ t₀ p, Category.assoc]

include hI hkf in

theorem chart_range (p : Pair f₀) :
    Set.range ⇑(P'.y (Opposite.op p.1.1) ≫ f) ⊆ Set.range ⇑(P.y (Opposite.op p.1.2)) := by
  rintro _ ⟨q, rfl⟩
  obtain ⟨q₀, rfl⟩ := (S'.surjective_spMap_p hI (Opposite.op p.1.1)).surj q
  have e := congrArg (fun g ↦ g q₀) (chart_red P P' hkf p)
  simp only [Scheme.Hom.comp_apply] at e
  rw [Scheme.Hom.comp_apply, e]
  exact ⟨_, rfl⟩

def chartMor (p : Pair f₀) : Sp (S'.F.obj (Opposite.op p.1.1)) ⟶ Sp (S.F.obj (Opposite.op p.1.2)) :=
  haveI := P.isOpen (Opposite.op p.1.2)
  IsOpenImmersion.lift _ _ (chart_range hI P P' hkf p)

theorem chartMor_fac (p : Pair f₀) :
    chartMor hI P P' hkf p ≫ P.y (Opposite.op p.1.2) = P'.y (Opposite.op p.1.1) ≫ f :=
  haveI := P.isOpen (Opposite.op p.1.2)
  IsOpenImmersion.lift_fac _ _ _

def chartRing (p : Pair f₀) : S.F.obj (Opposite.op p.1.2) →+* S'.F.obj (Opposite.op p.1.1) :=
  (Spec.preimage (chartMor hI P P' hkf p)).hom

theorem spMap_chartRing (p : Pair f₀) : spMap (chartRing hI P P' hkf p) = chartMor hI P P' hkf p := by
  simp only [spMap, chartRing, CommRingCat.ofHom_hom]
  exact Spec.map_preimage _

theorem chart_ext {A : Type} [CommRing A] (U : AffOp X₀) {a b : S.F.obj U →+* A}
    (e : spMap a ≫ P.y U = spMap b ≫ P.y U) : a = b :=
  haveI := P.isOpen U
  chart_spMap_inj ((cancel_mono (P.y U)).1 e)

include hkf in
theorem chartRing_fac (p : Pair f₀) :
    spMap (chartRing hI P P' hkf p) ≫ P.y (Opposite.op p.1.2) = P'.y (Opposite.op p.1.1) ≫ f := by
  rw [spMap_chartRing, chartMor_fac]

include hkf in

theorem chartRing_comp_algebraMap (hf : f ≫ s = t) (p : Pair f₀) :
    (chartRing hI P P' hkf p).comp (algebraMap R (S.F.obj (Opposite.op p.1.2))) =
      algebraMap R (S'.F.obj (Opposite.op p.1.1)) := by
  refine chart_spMap_inj ?_
  rw [chart_spMap_comp, ← P.base, ← Category.assoc, chartRing_fac, Category.assoc, hf, P'.base]

def chartAlg (hf : f ≫ s = t) (p : Pair f₀) : S.F.obj (Opposite.op p.1.2) →ₐ[R] S'.F.obj (Opposite.op p.1.1) :=
  { chartRing hI P P' hkf p with
    commutes' := fun r ↦ congrArg (fun g ↦ g r) (chartRing_comp_algebraMap hI P P' hkf hf p) }

include hkf in

theorem chartRing_red (p : Pair f₀) :
    (S'.p (Opposite.op p.1.1)).comp (chartRing hI P P' hkf p) =
      (GlobalTheory.CechDR.secPull s₀ t₀ p).comp (S.p (Opposite.op p.1.2)) := by
  refine chart_ext P _ ?_
  rw [chart_spMap_comp, chart_spMap_comp, Category.assoc, Category.assoc, chartRing_fac, chart_red P P' hkf p]

include hkf in

theorem chartRing_nat {p q : Pair f₀} (a : q ≤ p) (b : S.F.obj (Opposite.op p.1.2)) :
    mp S'.F (homOfLE (Pair.le_fst a)).op (chartRing hI P P' hkf p b) =
      chartRing hI P P' hkf q (mp S.F (homOfLE (Pair.le_snd a)).op b) := by
  have e : ((mp S'.F (homOfLE (Pair.le_fst a)).op : _ →+* _)).comp (chartRing hI P P' hkf p) =
      (chartRing hI P P' hkf q).comp (mp S.F (homOfLE (Pair.le_snd a)).op : _ →+* _) := by
    refine chart_ext P _ ?_
    rw [chart_spMap_comp, chart_spMap_comp, Category.assoc, Category.assoc, chartRing_fac, P.nat,
      chartRing_fac, ← Category.assoc, P'.nat]
  exact congrArg (fun g ↦ g b) e

end Chart

end GlobalTheory.Obs

namespace GlobalTheory.Obs

theorem exists_chart_lifts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (f : Z ⟶ X), f ≫ s = t → k ≫ f = f₀ ≫ i → ∃ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l ∧ (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l := by
  intro R R₀ _ _ I hI π _ _ X₀ Z₀ X Z s₀ t₀ s t i k _ _ S S' P P' f₀ h f hf hkf
  refine ⟨fun T ↦ chartAlg hI P P' hkf hf T.unop, fun T b ↦ ?_, fun T T' a b ↦ ?_⟩
  · exact congrArg (fun g ↦ g b) (chartRing_red hI P P' hkf T.unop)
  · exact chartRing_nat hI P P' hkf (leOfHom a.unop) b

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekind
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

set_option maxHeartbeats 1000000 in

theorem exists_ratModel_normalization : ∀ (A o Ω : Type) [CommRing A] [IsDedekindDomain A] [CommRing o] [Field Ω]
    [Algebra o Ω] [ArithBase o Ω] (κ : A →+* o), κ.Finite → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp A), LocallyOfFiniteType z →
    QuasiCompact z → IsSeparated z → ∀ p : Sp Ω ⟶ Z, p ≫ z = spMap ((algebraMap o Ω).comp κ) →
    (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ (M : RatModel o Ω) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z ∧
    IsFinite π ∧ M.pt ≫ π = p := by
  intro A o Ω _ _ _ _ _ _ κ hκ Z z _ _ _ p hp hfin
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : CharZero (Sp Ω).functionField :=
    charZero_of_injective_ringHom (((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫
      (Sp Ω).germToFunctionField ⊤).hom).injective
  haveI : IsFinite p.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_genericallyFinite (o := CommRingCat.of A) p z hfin
  haveI : GlobalTheory.IsNormalScheme p.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral p
  haveI : IsFinite (spMap κ) := by rw [IsFinite.SpecMap_iff]; exact hκ
  have hl : p ≫ z = spMap (algebraMap o Ω) ≫ spMap κ := by
    rw [hp, ← Spec.map_comp]; rfl
  let l : Sp Ω ⟶ pullback z (spMap κ) := pullback.lift p (spMap (algebraMap o Ω)) hl
  have hl1 : p = l ≫ pullback.fst z (spMap κ) := (pullback.lift_fst _ _ _).symm
  let d := p.normalizationDesc l (pullback.fst z (spMap κ)) hl1
  let s : p.normalization ⟶ Sp o := d ≫ pullback.snd z (spMap κ)
  have hs : s ≫ spMap κ = p.fromNormalization ≫ z := by
    simp only [s, d, Category.assoc, ← pullback.condition]
    rw [Scheme.Hom.normalizationDesc_comp_assoc]
  have hfz : LocallyOfFiniteType (s ≫ spMap κ) ∧ IsSeparated (s ≫ spMap κ) ∧ QuasiCompact (s ≫ spMap κ) := by
    rw [hs]; exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨h1, h2, h3⟩ := hfz
  have hpt_s : p.toNormalization ≫ s = spMap (algebraMap o Ω) := by
    simp only [s, d]
    rw [Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_snd]
  have hgen : Set.range p.toNormalization = {genericPoint p.normalization} := by
    have hr : ∀ w : Sp Ω, w = IsLocalRing.closedPoint Ω := fun w => Subsingleton.elim _ _
    have hrng : Set.range p.toNormalization = {p.toNormalization (IsLocalRing.closedPoint Ω)} :=
      Set.ext fun y => ⟨fun ⟨w, hw⟩ => hw ▸ congrArg p.toNormalization (hr w),
        fun hy => ⟨_, hy.symm⟩⟩
    have : IsGenericPoint (p.toNormalization (IsLocalRing.closedPoint Ω)) (⊤ : Set p.normalization) := by
      rw [isGenericPoint_def, ← hrng]
      exact p.toNormalization.denseRange.closure_range
    rw [hrng, this.eq (genericPoint_spec p.normalization)]
  have honto : ∀ x : Ω, ∃ (U : p.normalization.Opens) (f : Γ(p.normalization, U)), (U : Set p.normalization).Nonempty ∧
      valF p.toNormalization U f = x := by
    intro x
    set ξ : Sp Ω := genericPoint (Sp Ω) with hξ
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (x := p ξ) (U := ⊤) trivial
    have hsub : ∀ w : Sp Ω, w = ξ := fun w => Subsingleton.elim _ _
    have hpV : ⊤ ≤ p ⁻¹ᵁ V := fun w _ => by rw [hsub w]; exact hxV
    have hξB : ξ ∈ p ⁻¹ᵁ V := hxV
    letI := (p.app V).hom.toAlgebra

    let gB := (Sp Ω).presheaf.germ (p ⁻¹ᵁ V) ξ hξB
    let gR := Z.presheaf.germ V (p ξ) hxV
    have hsq : gR ≫ p.stalkMap ξ = p.app V ≫ gB := p.germ_stalkMap V ξ hxV
    letI alO : Algebra Γ(Z, V) (Z.presheaf.stalk (p ξ)) :=
      TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨p ξ, hxV⟩
    letI alS : Algebra (Z.presheaf.stalk (p ξ)) ((Sp Ω).presheaf.stalk ξ) := (p.stalkMap ξ).hom.toAlgebra
    letI alRS : Algebra Γ(Z, V) ((Sp Ω).presheaf.stalk ξ) := (gR ≫ p.stalkMap ξ).hom.toAlgebra
    haveI : IsScalarTower Γ(Z, V) (Z.presheaf.stalk (p ξ)) ((Sp Ω).presheaf.stalk ξ) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI hloc : IsLocalization.AtPrime (Z.presheaf.stalk (p ξ)) (hV.primeIdealOf ⟨p ξ, hxV⟩).asIdeal :=
      hV.isLocalization_stalk ⟨p ξ, hxV⟩

    have h1 : ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ (p ⁻¹ᵁ V) := hpV
    let E : Γ(Sp Ω, p ⁻¹ᵁ V) →+* Ω := (GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1).hom
    have hE : ∀ b, E b = valR (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) b := fun b => (GlobalTheory.Points.valR_eq _ _ h1 b).symm
    have hEinj : Function.Injective E := by
      have e1 : GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1 =
          (Sp Ω).presheaf.map (homOfLE h1).op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
        rw [GlobalTheory.Points.valMap, Scheme.Hom.appLE]
        simp
        rfl
      haveI : Nonempty (⊤ : (Sp Ω).Opens) := ⟨⟨ξ, trivial⟩⟩
      show Function.Injective (GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1).hom
      rw [e1]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).1.comp
        (map_injective_of_isIntegral (Sp Ω) (homOfLE h1))
    obtain ⟨y', hy'⟩ : ∃ y' : Γ(Sp Ω, p ⁻¹ᵁ V), E y' = x := by
      refine ⟨((Sp Ω).presheaf.map (homOfLE le_top).op).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom x), ?_⟩
      rw [hE, GlobalTheory.Points.valR_res (𝟙 (Sp Ω)) le_top h1]
      have := GlobalTheory.Points.valR_specMap (𝟙 (CommRingCat.of Ω)) x
      rw [Spec.map_id] at this
      exact this

    let y := gB.hom y'
    have hy : IsIntegral (Z.presheaf.stalk (p ξ)) y := hfin.to_isIntegral y
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (hV.primeIdealOf ⟨p ξ, hxV⟩).asIdeal.primeCompl y hy
    have hcomm : ∀ r : Γ(Z, V), gB.hom (algebraMap Γ(Z, V) Γ(Sp Ω, p ⁻¹ᵁ V) r) =
        algebraMap Γ(Z, V) ((Sp Ω).presheaf.stalk ξ) r := fun r => by
      show gB.hom ((p.app V).hom r) = (gR ≫ p.stalkMap ξ).hom r
      rw [hsq]; rfl
    let gB' : Γ(Sp Ω, p ⁻¹ᵁ V) →ₐ[Γ(Z, V)] (Sp Ω).presheaf.stalk ξ := { gB.hom with commutes' := hcomm }
    have hgB : Function.Injective gB' := germ_injective_of_isIntegral (Sp Ω) ξ hξB
    let c' : Γ(Sp Ω, p ⁻¹ᵁ V) := algebraMap Γ(Z, V) _ (m : Γ(Z, V))
    let d' : Γ(Sp Ω, p ⁻¹ᵁ V) := c' * y'
    have hc : IsIntegral Γ(Z, V) c' := isIntegral_algebraMap
    have hd : IsIntegral Γ(Z, V) d' := by
      rw [← isIntegral_algHom_iff gB' hgB]
      have : gB' d' = (m : Γ(Z, V)) • y := by
        rw [Algebra.smul_def, map_mul]
        exact congrArg (· * y) (hcomm _)
      rw [this]
      exact hm
    have hc0 : c' ≠ 0 := by
      intro h0
      have h2 : IsUnit (gB.hom c') := by
        rw [hcomm]
        exact ((IsLocalization.map_units (Z.presheaf.stalk (p ξ)) m).map (p.stalkMap ξ).hom)
      rw [h0, map_zero] at h2
      exact not_isUnit_zero h2
    have hEc : E c' ≠ 0 := fun h0 => hc0 (hEinj (h0.trans (map_zero E).symm))

    let iso := p.normalizationObjIso hV
    have key := p.normalizationObjIso_hom_val hV
    let ac : Γ(p.normalization, p.fromNormalization ⁻¹ᵁ V) := iso.inv.hom ⟨c', hc⟩
    let ad : Γ(p.normalization, p.fromNormalization ⁻¹ᵁ V) := iso.inv.hom ⟨d', hd⟩
    have hle : p ⁻¹ᵁ V ≤ p.toNormalization ⁻¹ᵁ (p.fromNormalization ⁻¹ᵁ V) := by
      simp [← Scheme.Hom.comp_preimage]
    have hval : ∀ e : integralClosure Γ(Z, V) Γ(Sp Ω, p ⁻¹ᵁ V),
        valR p.toNormalization (p.fromNormalization ⁻¹ᵁ V) (iso.inv.hom e) = E e.1 := by
      intro e
      have h3 := congrArg (fun φ => φ.hom (iso.inv.hom e)) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] at h3
      rw [hE, ← Category.id_comp p.toNormalization, ← GlobalTheory.Points.valR_appLE (𝟙 (Sp Ω)) p.toNormalization hle h1]
      congr 1
      exact h3.symm
    have hW : ⊤ ≤ p.toNormalization ⁻¹ᵁ (p.fromNormalization ⁻¹ᵁ V) := h1.trans hle
    have hU : ⊤ ≤ p.toNormalization ⁻¹ᵁ p.normalization.basicOpen ac := by
      rw [GlobalTheory.Points.le_preimage_basicOpen_iff _ hW ac]
      exact (show valR p.toNormalization _ ac ≠ 0 from (hval _).trans_ne hEc).isUnit
    have hu : IsUnit ((p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ac) :=
      p.normalization.toRingedSpace.isUnit_res_basicOpen ac
    refine ⟨p.normalization.basicOpen ac,
      (p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ad * ↑(hu.unit⁻¹),
      ⟨_, hU (x := ξ) trivial⟩, ?_⟩
    rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valR_mul _ _ hU, GlobalTheory.Points.valR_res _ _ hU, hval]
    have h4 : valR p.toNormalization _ ((p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ac) *
        valR p.toNormalization (p.normalization.basicOpen ac) ↑(hu.unit⁻¹) = 1 := by
      rw [← GlobalTheory.Points.valR_mul _ _ hU, ← GlobalTheory.Points.valR_one p.toNormalization _ hU]
      congr 1
      exact hu.mul_val_inv
    rw [GlobalTheory.Points.valR_res _ _ hU, hval] at h4
    rw [eq_inv_of_mul_eq_one_right h4]
    show E (c' * y') * (E c')⁻¹ = x
    rw [map_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hEc, one_mul, hy']
  haveI := IsSeparated.of_comp s (spMap κ)
  haveI := locallyOfFiniteType_of_comp s (spMap κ)
  haveI := QuasiCompact.of_comp s (spMap κ)
  let M : RatModel o Ω :=
    { Z := p.normalization
      s := s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := p.toNormalization
      pt_s := hpt_s
      gen := hgen
      onto := honto }
  exact ⟨M, p.fromNormalization, GlobalTheory.IsNormalScheme.pred _, inferInstance, p.toNormalization_fromNormalization⟩

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedMultiplicationPullbackFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.MulFrame

open GlobalTheory.ThetaFn GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter

theorem exists_two_mul_dot {g : ℕ} {a : Fin g → ℂ} (ha : Half a) (M : Fin g → ℤ) :
    ∃ n : ℤ, 2 * (a ⬝ᵥ cv M) = n := by
  have h : ∀ i, ∃ n : ℤ, 2 * a i = n := fun i => by
    rcases ha i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using h
  refine ⟨∑ i, n i * M i, ?_⟩
  simp only [dotProduct, cv, Finset.mul_sum, ← _root_.mul_assoc, hn]
  push_cast
  rfl

theorem cv_nsmul {g : ℕ} (m : ℕ) (M : Fin g → ℤ) : cv (m • M) = (m : ℂ) • cv M := by
  funext i
  simp [cv]

theorem perV_nsmul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (m : ℕ) (M N : Fin g → ℤ) :
    perV τ (m • M) (m • N) = (m : ℂ) • perV τ M N := by
  rw [perV, perV, cv_nsmul, cv_nsmul, Matrix.mulVec_smul, smul_add]

theorem autV_nsmul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) {a b : Fin g → ℂ} (ha : Half a) (hb : Half b) (m : ℕ)
    (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    autV τ a b (m • M) (m • N) ((m : ℂ) • z) = autV τ a b M N z ^ (m ^ 2) := by
  obtain ⟨p, hp⟩ := exists_two_mul_dot ha M
  obtain ⟨q, hq⟩ := exists_two_mul_dot hb N
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self (m : ℤ)
  have hk' : (m : ℂ) * (m - 1) = k + k := by exact_mod_cast hk
  rw [autV, autV, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(k * (p - q)), ?_⟩
  simp only [cv_nsmul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  push_cast
  rw [← hp, ← hq]
  linear_combination (-(2 * Real.pi * Complex.I * (a ⬝ᵥ cv M - b ⬝ᵥ cv N))) * hk'

section Origin

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T}

theorem val_origin {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig) {m : T ⊗ A ⟶ A} {ε : Fin 2 → ℤ} {c : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ε)}
    (hn : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L rig T c)) (i : L.ι)
    (hi : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] (fun _ => i)) :
    valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] (fun _ => i)) (α.s fun _ => i).val = u.fr i 0 ^ c := by
  have he := comp_ptSecT u p (comp_one_eq_ex_zero u p)
  have h1 : ⊤ ≤ p.left ⁻¹ᵁ LB.wchart L (fun k => (ptSecT A (1 : T ⟶ A)).left ≫ ![(snd T A).left, m.left] k)
      (fun _ => i) := by
    rw [← he] at hj
    exact fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hj hy) k
  have h2 := (mem_ptChart_iff (comp_one_eq_ex_zero u p) (fun _ => i)).2 hi
  have h12 := (le_preimage_inf p.left _ _).2 ⟨h1, h2⟩
  have e := congrArg (fun t => valAt' p.left _ (Units.val t))
    (hn (fun _ => i) (fun _ => i) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl))
  refine Eq.trans ?_ (((ThetaFn.valAt'_res p.left inf_le_left h12 _).symm.trans
    (e.trans (ThetaFn.valAt'_res p.left inf_le_right h12 _))).trans (valAt'_rigT p hrig c (fun _ => i) hi))
  rw [← he]
  exact (valAt'_appLE' p.left (ptSecT A (1 : T ⟶ A)).left _ h1 _).symm

end Origin

theorem fnT_iff {g : ℕ} {P : PolAV (Sp ℂ)} (u : HolUnif P.A P.L g) (k : ℕ)
    (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ) :
    FnT u k t f ↔ IsFnAt u basePt (k : ℤ) t f := by
  constructor
  · intro h j z hj
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    rw [zpow_natCast]
    exact h i z ((exAt_mem_chart_iff u basePt _ _ z).1 hj)
  · intro h i z hi
    rw [← zpow_natCast]
    exact h (fun _ => i) z ((exAt_mem_chart_iff u basePt _ _ z).2 hi)

end GlobalTheory.MBLow.Cl.MulFrame

namespace GlobalTheory.MBLow.Cl

open GlobalTheory.ThetaFn GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter MulFrame in

theorem exists_normalised_mulPull_fnT : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ (m : ℕ) (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ), FnT u 1 th f → ∃ (α : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![(snd (baseOver (Sp ℂ)) x.P.A).left, (snd (baseOver (Sp ℂ)) x.P.A ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (s₁ : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp ℂ)))), α.IsGen ∧ LB.Gen.Corr x.P.L _ _ _ _ (LB.pullGen x.P.L _ _ α (ptSecT x.P.A 1).left) (rigT x.P.A x.P.L x.rig (baseOver (Sp ℂ)) (((m ^ 2 : ℕ) : ℤ) - 1)) ∧ IsTwistPull x.P.A x.P.L (mulT x.P.A (baseOver (Sp ℂ)) m) (snd (baseOver (Sp ℂ)) x.P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧ FnT u (m ^ 2) s₁ fun z => f ((m : ℂ) • z) := by
  intro g x hg u τ a b c W hNF m th f hf
  have hfr := frame_eq_autV_mul g x hg u τ a b c W hNF
  obtain ⟨-, -, ha, hb, -, hΛ, hrig, -⟩ := hNF
  have hL := x.P.isLB
  have H := GlobalTheory.exists_mulPull_gen_over GlobalTheory.abelianSchemeLaws_all.1.mulPull x.P (baseOver (Sp ℂ)) m
  rw [← Nat.cast_pow] at H
  obtain ⟨α₀, hα₀⟩ := H
  obtain ⟨α, hα, hn⟩ := NormTheta.exists_normalised hL x.rig_gen m ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ)
    (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₀ hα₀
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT x.P.A (baseOver (Sp ℂ)) m)
    (snd (baseOver (Sp ℂ)) x.P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  refine ⟨α, s₁, hα, hn, hs₁, ?_⟩
  have hψ := exAt_mulT u basePt m
  have hΦ : ∀ z, exAt u basePt z ≫ (snd (baseOver (Sp ℂ)) x.P.A ^ m).left = (u.ex ((m : ℂ) • z)).left := fun z => by
    rw [← lift_snd (fst (baseOver (Sp ℂ)) x.P.A) (snd (baseOver (Sp ℂ)) x.P.A ^ m), Over.comp_left, ← Category.assoc]
    exact (congrArg (· ≫ _) (hψ z)).trans (exAt_snd _ _ _)
  obtain ⟨r, hr, hne, hrj⟩ := exists_fn_of_isGen (Φ := fun z => (m : ℂ) • z) hL (by fun_prop) hΦ hα
  haveI := u.discrete
  obtain ⟨-, -, k3⟩ := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 (fun _ => 1) r
    Matrix.isHermitian_zero (fun _ => norm_one) hr hne (fun l z => by
      obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
      obtain ⟨i', hi'⟩ := exists_chart u valueRules hL ((m : ℂ) • z)
      have hj := (exAt_mem_pairChart_iff (hΦ z) ![i, i']).2 ⟨hi, hi'⟩
      have hj' := hj
      rw [← exAt_add_period u basePt z l l.2] at hj'
      rw [hrj _ _ hj', hrj _ _ hj, exAt_add_period u basePt z l l.2]
      obtain ⟨M, N, hl⟩ := (hΛ l).1 l.2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hermForm, Matrix.zero_mulVec, dotProduct_zero]
      rw [hfr M N i z hi, hfr (m • M) (m • N) i' _ hi', autV_nsmul τ ha hb, perV_nsmul, hl, smul_add]
      have n1 : autV τ a b M N z ≠ 0 := Complex.exp_ne_zero _
      simp only [_root_.zpow_neg, zpow_natCast, mul_pow, pow_one, mul_zero, add_zero, Complex.exp_zero]
      field_simp)
  have h0 : r 0 = 1 := by
    obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
    have hj := (exAt_mem_pairChart_iff (hΦ 0) (fun _ => i)).2 ⟨hi, by rw [smul_zero]; exact hi⟩
    have n := u.fr_ne i 0 hi
    rw [hrj _ _ hj, val_origin hrig hn i hi hj, smul_zero, ← zpow_add₀ n, ← zpow_add₀ n]
    simp
  have hc : IsPullConst u basePt (fun z => (m : ℂ) • z) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α 1 := fun j z hj => by
    have n := zpow_ne_zero ((m ^ 2 : ℕ) : ℤ) (u.fr_ne _ _ ((exAt_mem_pairChart_iff (hΦ z) j).1 hj).1)
    rw [← h0, ← k3 z, hrj j z hj, _root_.zpow_neg, inv_mul_cancel_right₀ n]
  have h2 := isFnAt_fnAt u basePt hL _ s₁
  have e := funext (hc.fn_eq hL hψ hs₁ ((fnT_iff u 1 th f).1 hf) h2)
  rw [fnT_iff]
  simpa only [e, _root_.one_mul] using h2

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenOfSaturatedLocalSchemeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_open_of_saturated_stalkBaseChange : ∀ (S S₁ P : Scheme.{0}) (p : P ⟶ S) (x : S) (ξ' : S₁ ⟶ Spec (S.presheaf.stalk x)) (ξ : S₁ ⟶ S), ξ' ≫ S.fromSpecStalk x = ξ → Flat ξ' → Surjective ξ' → QuasiCompact ξ' → ∀ O : Set ↥(Limits.pullback p ξ), IsOpen O → (∀ w w' : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w = Limits.pullback.fst p ξ w' → w ∈ O → w' ∈ O) → ∃ V : P.Opens, ∀ w : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w ∈ V ↔ w ∈ O := by
  intro S S₁ P p x ξ' ξ hξ hfl hsu hqc O hO hsat
  subst hξ
  obtain ⟨π, hπ, hπ2⟩ : ∃ π : pullback p (ξ' ≫ S.fromSpecStalk x) ⟶ pullback p (S.fromSpecStalk x),
      π ≫ pullback.fst p (S.fromSpecStalk x) = pullback.fst p (ξ' ≫ S.fromSpecStalk x) ∧
      π ≫ pullback.snd p (S.fromSpecStalk x) = pullback.snd p (ξ' ≫ S.fromSpecStalk x) ≫ ξ' :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ξ') (by rw [Category.assoc]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsq : IsPullback π (pullback.snd p (ξ' ≫ S.fromSpecStalk x)) (pullback.snd p (S.fromSpecStalk x)) ξ' := by
    refine IsPullback.of_right ?_ hπ2 (IsPullback.of_hasPullback p (S.fromSpecStalk x))
    rw [hπ]
    exact IsPullback.of_hasPullback p (ξ' ≫ S.fromSpecStalk x)
  have : Flat π := MorphismProperty.of_isPullback (P := @Flat) hsq.flip hfl
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hsu
  have : QuasiCompact π := MorphismProperty.of_isPullback (P := @QuasiCompact) hsq.flip hqc
  have hq := Flat.isQuotientMap_of_surjective π
  have hc : ∀ w, pullback.fst p (S.fromSpecStalk x) (π w) = pullback.fst p (ξ' ≫ S.fromSpecStalk x) w := by
    intro w; rw [← Scheme.Hom.comp_apply, hπ]
  have hpre : π ⁻¹' (π '' O) = O := by
    ext w; constructor
    · rintro ⟨w', hw', he⟩
      exact hsat w' w (by rw [← hc, ← hc, he]) hw'
    · intro hw; exact ⟨w, hw, rfl⟩
  have hopen : IsOpen (π '' O) := by
    rw [← hq.isOpen_preimage, hpre]; exact hO
  have hemb := IsPreimmersion.isEmbedding (pullback.fst p (S.fromSpecStalk x))
  obtain ⟨t, ht, hte⟩ := hemb.isInducing.isOpen_iff.1 hopen
  refine ⟨⟨t, ht⟩, fun w => ?_⟩
  change _ ∈ t ↔ _
  rw [← hc, ← Set.mem_preimage, hte, ← Set.mem_preimage, hpre]

end GlobalTheory.Desc
end

