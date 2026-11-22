import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteModelOfExtension
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BplusDescent

section Field

variable {X : Scheme.{0}} [IsIntegral X] {L : Type} [Field L] (φ : X.presheaf.stalk (genericPoint X) ⟶ .of L)

abbrev fieldPt : Spec (.of L) ⟶ X := Spec.map φ ≫ X.fromSpecStalk (genericPoint X)

theorem fieldPt_apply (x : Spec (.of L)) : fieldPt φ x = genericPoint X := by
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  have : Spec.map φ x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
  change X.fromSpecStalk _ (Spec.map φ x) = _
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

theorem top_le_fieldPt {U : X.Opens} (hU : genericPoint X ∈ U) : ⊤ ≤ fieldPt φ ⁻¹ᵁ U := fun x _ => by
  change fieldPt φ x ∈ U
  rwa [fieldPt_apply]

theorem fieldPt_appLE {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) ≫ (Scheme.ΓSpecIso (.of L)).hom = X.presheaf.germ U _ hU ≫ φ := by
  have h1 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U := fun x _ => by
    letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
    have : x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
      Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
    change X.fromSpecStalk _ x ∈ U
    rw [this, Scheme.fromSpecStalk_closedPoint]
    exact hU
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) (X.fromSpecStalk (genericPoint X)) U ⊤ ⊤ h1 le_rfl]
  have h2 : (Spec.map φ).appLE ⊤ ⊤ le_rfl = (Spec.map φ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  rw [h2, Category.assoc, Scheme.ΓSpecIso_naturality, Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  have h3 : ∀ i : (Opposite.op ⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opensᵒᵖ) ⟶ Opposite.op ⊤,
      (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map i = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _
  rw [h3]
  simp

def normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    Γ((fieldPt φ).normalization, (fieldPt φ).fromNormalization ⁻¹ᵁ U) ⟶ .of L :=
  (fieldPt φ).toNormalization.appLE _ ⊤ (by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU) ≫
    (Scheme.ΓSpecIso (.of L)).hom

theorem app_normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).fromNormalization.app U ≫ normFun φ hU = X.presheaf.germ U _ hU ≫ φ := by
  have key : ∀ (g : Spec (.of L) ⟶ X) (_ : g = fieldPt φ) (e : ⊤ ≤ g ⁻¹ᵁ U),
      g.appLE U ⊤ e = (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) := by
    rintro _ rfl _
    rfl
  rw [normFun, ← fieldPt_appLE, ← Category.assoc]
  congr 1
  exact (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans (key _ (fieldPt φ).toNormalization_fromNormalization (by
    rw [Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU))

theorem map_normFun {U U' : X.Opens} (hU : genericPoint X ∈ U) (hU' : genericPoint X ∈ U') (h : U' ≤ U) :
    (fieldPt φ).normalization.presheaf.map (homOfLE ((fieldPt φ).fromNormalization.preimage_mono h)).op ≫
      normFun φ hU' = normFun φ hU := by
  rw [normFun, normFun, Scheme.Hom.map_appLE_assoc]

theorem normFun_spec {U : X.Opens} (hU : genericPoint X ∈ U) (hA : IsAffineOpen U) :
    Function.Injective (normFun φ hU).hom ∧
      ∀ x : L, x ∈ (normFun φ hU).hom.range ↔ (X.presheaf.germ U _ hU ≫ φ).hom.IsIntegralElem x := by
  let u := fieldPt φ
  letI := (u.app U).hom.toAlgebra
  let ε : Γ(Spec (.of L), u ⁻¹ᵁ U) ⟶ .of L :=
    (Spec (.of L)).presheaf.map (homOfLE (top_le_fieldPt φ hU)).op ≫ (Scheme.ΓSpecIso (.of L)).hom
  have hε : Function.Bijective ε.hom := by
    have : homOfLE (top_le_fieldPt φ hU) = eqToHom (top_le_iff.1 (top_le_fieldPt φ hU)).symm := Subsingleton.elim _ _
    haveI : IsIso ε := by
      simp only [ε, this]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso ε
  have h1 : normFun φ hU = (u.normalizationObjIso hA).hom ≫
      CommRingCat.ofHom (integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U)).val.toRingHom ≫ ε := by
    rw [← Category.assoc, u.normalizationObjIso_hom_val hA, normFun]
    simp only [ε]
    rw [Scheme.Hom.appLE_map_assoc]
  have h2 : X.presheaf.germ U _ hU ≫ φ = u.app U ≫ ε := by
    rw [← fieldPt_appLE, Scheme.Hom.appLE, Category.assoc]
  have hb := ConcreteCategory.bijective_of_isIso (u.normalizationObjIso hA).hom
  rw [h1, h2]
  refine ⟨hε.1.comp (Subtype.val_injective.comp hb.1), fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨p, hp, hp0⟩ := ((u.normalizationObjIso hA).hom y).2
    refine ⟨p, hp, ?_⟩
    have := congrArg ε.hom hp0
    rw [Polynomial.hom_eval₂, map_zero] at this
    exact this
  · rintro ⟨p, hp, hp0⟩
    obtain ⟨y, rfl⟩ := hε.2 x
    have hy : IsIntegral Γ(X, U) y := ⟨p, hp, hε.1 (by rw [Polynomial.hom_eval₂, map_zero]; exact hp0)⟩
    obtain ⟨z, hz⟩ := hb.2 ⟨y, hy⟩
    exact ⟨z, congrArg (fun w : integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U) => ε.hom w.1) hz⟩

end Field

theorem exists_normalization_in (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (B : GlobalTheory.Vert.Model O) (_ : GlobalTheory.IsNormalScheme B.X) (K' : IntermediateField B.X.functionField (Kbar B.X))
    (hK : FiniteDimensional B.X.functionField K') :
    ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (γ : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp),
      GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ IsFinite f.f ∧ (∀ U, Function.Injective (γ U)) ∧
      (∀ (U : AffOp B.X) (a : Γ(B.X, U.1)), γ U ((f.f.app U.1).hom a) = algebraMap Γ(B.X, U.1) U.Bp a) ∧
      (∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1) (a : Γ(B'.X, f.f ⁻¹ᵁ U.1)),
        γ U' ((B'.X.presheaf.map (homOfLE (f.f.preimage_mono hle)).op).hom a) = AffOp.res hle (γ U a)) ∧
      ∀ U, (γ U).range = ringOver K' U := by
  set η := genericPoint B.X
  let ψ : B.X.presheaf.stalk (genericPoint B.X) ⟶ .of K' := CommRingCat.ofHom (algebraMap B.X.functionField K')
  let u : Spec (.of K') ⟶ B.X := fieldPt ψ
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ B.str)
  have hu : u (IsLocalRing.closedPoint K') = η := fieldPt_apply ψ _
  have hφinj : Function.Injective φ.hom := by
    have hη : (B.str η).asIdeal = ⊥ := Model.mem_gen_iff_eq_bot.1 B.genericPoint_mem_gen
    have e : Spec.map φ (IsLocalRing.closedPoint K') = B.str η := by
      rw [hφ]
      exact congrArg B.str hu
    rw [RingHom.injective_iff_ker_eq_bot]
    have e' := congrArg PrimeSpectrum.asIdeal e
    rw [hη] at e'
    rw [← e']
    ext a
    change _ ↔ φ.hom a ∈ IsLocalRing.maximalIdeal K'
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
    rfl
  haveI : CharZero K' := charZero_of_injective_ringHom hφinj
  haveI : LocallyOfFiniteType B.str := inferInstance
  have hfin : IsFinite u.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk (o := .of O) B.str η ψ
      (RingHom.finite_algebraMap.2 hK).finiteType.essFiniteType
  let ν := u.fromNormalization
  haveI : Flat (u.fromNormalization ≫ B.str) := by
    have : Flat (u.toNormalization ≫ u.fromNormalization ≫ B.str) := by
      rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, ← hφ]
      exact Flat.SpecMap_iff.mpr (flat_of_dedekind_of_injective φ.hom hφinj)
    exact flat_normalization u _
  let B' : Model O :=
    { X := u.normalization
      str := ν ≫ B.str
      isIntegral := inferInstance
      isProjOver := isProjOver_comp_of_isFinite ν B.isProjOver
      flat := ‹_› }
  have hrange : Set.range ν = Set.univ := by
    have hcl : IsClosed (Set.range ν) := ν.isClosedMap.isClosed_range
    have hmem : η ∈ Set.range ν :=
      ⟨u.toNormalization (IsLocalRing.closedPoint K'), by
        change (u.toNormalization ≫ u.fromNormalization) _ = η
        rw [Scheme.Hom.toNormalization_fromNormalization]
        exact hu⟩
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec B.X).def]
    exact hcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)
  haveI : Surjective ν := ⟨fun x => hrange.ge (Set.mem_univ x)⟩
  let n : Model.Hom B' B := ⟨ν, rfl⟩
  have hx : ∀ U : AffOp B.X, genericPoint B.X ∈ U.1 := fun U =>
    ((genericPoint_spec B.X).mem_open_set_iff U.1.isOpen).2 (by simpa using U.2.2)
  have hint : ∀ (U : AffOp B.X) (x : K'), (B.X.presheaf.germ U.1 _ (hx U) ≫ ψ).hom.IsIntegralElem x ↔
      IsIntegral Γ(B.X, U.1) (x : Kbar B.X) := fun U x => by
    refine exists_congr fun p => and_congr_right fun _ => ?_
    rw [← (map_eq_zero_iff K'.val.toRingHom Subtype.val_injective), Polynomial.hom_eval₂]
    rfl
  let γ : ∀ U : AffOp B.X, Γ(B'.X, n.f ⁻¹ᵁ U.1) →+* U.Bp := fun U =>
    (K'.val.toRingHom.comp (normFun ψ (hx U)).hom).codRestrict (integralClosure Γ(B.X, U.1) (Kbar B.X)) fun a =>
      (hint U _).1 (((normFun_spec ψ (hx U) U.2.1).2 _).1 ⟨a, rfl⟩)
  refine ⟨B', n, γ, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u, ?_, hfin, fun U a b h => ?_, fun U a => ?_,
    fun U U' hle a => ?_, fun U => ?_⟩
  · have hdim := Model.topologicalKrullDim_genFibre O B B' n
    haveI : Subsingleton n.genFibre := by
      constructor
      intro a b
      have key : ∀ c : n.genFibre, (ν.fiberι η) c = genericPoint B'.X := fun c => by
        have hc : (ν.fiberι η) c ∈ ν ⁻¹' {η} := by
          rw [← Scheme.Hom.range_fiberι]; exact ⟨c, rfl⟩
        exact Model.eq_genericPoint_of_isFinite ν hc
      exact (ν.fiberι η).isEmbedding.injective ((key a).trans (key b).symm)
    have h0 := topologicalKrullDim_zero_of_discreteTopology n.genFibre
    rw [hdim] at h0
    have h1 : n.relDim ≤ 0 := by exact_mod_cast h0
    omega
  · exact (normFun_spec ψ (hx U) U.2.1).1 (Subtype.ext (congrArg (fun z : U.Bp => (z : Kbar B.X)) h))
  · exact Subtype.ext (congrArg (fun g : Γ(B.X, U.1) ⟶ .of K' => (g.hom a : Kbar B.X)) (app_normFun ψ (hx U)))
  · exact Subtype.ext (congrArg (fun g : Γ(B'.X, n.f ⁻¹ᵁ U.1) ⟶ .of K' => (g.hom a : Kbar B.X))
      (map_normFun ψ (hx U) (hx U') hle))
  · ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ((normFun ψ (hx U)).hom a).2
    · intro h
      obtain ⟨a, ha⟩ := ((normFun_spec ψ (hx U) U.2.1).2 ⟨x.1, h⟩).2 ((hint U _).2 x.2)
      exact ⟨a, Subtype.ext (congrArg (fun z : K' => (z : Kbar B.X)) ha)⟩

end GlobalTheory.BplusDescent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenComplexPointsCoveringGenericDegree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace GlobalTheory.CoverDegProj

theorem etale_morphismRestrict {X Y : Scheme.{0}} (π : Y ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (hπU : IsAffineOpen (π ⁻¹ᵁ U)) (hét : (π.app U).hom.Etale) : Etale (π ∣_ U) := by
  haveI : IsAffine U := hU
  haveI : IsAffine (π ⁻¹ᵁ U) := hπU
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    morphismRestrict_appLE]
  refine (Scheme.Hom.appLE_congr π _ (Scheme.Opens.ι_image_top U) (V' := π ⁻¹ᵁ U) ?_
    (fun φ => RingHom.Etale φ.hom)).2 ?_
  · rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top]
  · rw [← Scheme.Hom.app_eq_appLE]; exact hét

theorem etale_pullback_coords_of_etale {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    (π : Y ⟶ X) (hπ : π ≫ p = q) (D : ℕ) (U : X.Opens) (hU : IsAffineOpen U)
    (hπU : IsAffineOpen (π ⁻¹ᵁ U)) (hét : (π.app U).hom.Etale) (W : X.Opens) (x : Fin D → Γ(X, W))
    (hW : IsAffineOpen W) (hx : (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x).Etale)
    (z : Y) (hzU : π z ∈ U) (hzW : π z ∈ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ z ∈ V ∧ ∃ h : V ≤ π ⁻¹ᵁ W,
      (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V) (fun a => (π.appLE W V h).hom (x a))).Etale := by
  subst hπ
  have hE := etale_morphismRestrict π U hU hπU hét
  obtain ⟨f, g, hfg, hz⟩ := exists_basicOpen_le_affine_inter hU hW (π z) ⟨hzU, hzW⟩
  have hW'U : X.basicOpen f ≤ U := X.basicOpen_le f
  have hW'W : X.basicOpen f ≤ W := hfg ▸ X.basicOpen_le g
  have hW' : IsAffineOpen (X.basicOpen f) := hU.basicOpen f
  have hV : IsAffineOpen (π ⁻¹ᵁ X.basicOpen f) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact hπU.basicOpen _
  have hVU : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ U := fun y hy => hW'U hy
  have h : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ W := fun y hy => hW'W hy
  refine ⟨π ⁻¹ᵁ X.basicOpen f, hV, hz, h, ?_⟩

  have e1 : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (π ≫ p) (π ⁻¹ᵁ X.basicOpen f))
      (fun a => (π.appLE W _ h).hom (x a)) =
      (π.appLE W _ h).hom.comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x) := by
    rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.CoverDeg.algX_comp p π W _ h]
  rw [e1]
  refine RingHom.Etale.stableUnderComposition _ _ hx ?_

  have e2 : π.appLE W (π ⁻¹ᵁ X.basicOpen f) h =
      X.presheaf.map (homOfLE hW'W).op ≫ π.appLE (X.basicOpen f) (π ⁻¹ᵁ X.basicOpen f) le_rfl := by
    rw [Scheme.Hom.map_appLE]
  rw [e2, CommRingCat.hom_comp]
  refine RingHom.Etale.stableUnderComposition _ _ (GlobalTheory.CoverDeg.etale_map_basicOpen hW g _ hfg hW'W) ?_

  have ha : IsAffineOpen (U.ι ⁻¹ᵁ X.basicOpen f) :=
    hW'.preimage_of_isOpenImmersion U.ι (by rw [Scheme.Opens.opensRange_ι]; exact hW'U)
  have hb : IsAffineOpen ((π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f)) :=
    hV.preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact hVU)
  have e3 : (π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f) ≤ (π ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ X.basicOpen f) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
  have := HasRingHomProperty.appLE @Etale (π ∣_ U) hE ⟨_, ha⟩ ⟨_, hb⟩ e3
  rw [morphismRestrict_appLE] at this
  refine (Scheme.Hom.appLE_congr π _ ?_ ?_ (fun φ => RingHom.Etale φ.hom)).1 this
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hW'U
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hVU

theorem exists_open_covering_charts : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (ptMap π hπ σ ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ z : CxPts q σ, ptMap π hπ σ z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, ptMap π hπ σ z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w)) := by
  intro k _ X Y _ _ p q σ D hpP hqP π hπ hη hδ
  haveI : CharZero k := RingHom.charZero σ
  obtain ⟨U, hU, hxU, hV, he, hf, hr⟩ :=
    GlobalTheory.GenFinEtField.exists_affine_finite_etale_free k X Y p q hpP hqP π hπ hη hδ
  refine ⟨U, hxU, fun y hy => ?_, fun z hz c hc => ?_⟩
  · rw [GlobalTheory.encard_fibre_eq_encard_ringHom π hπ U hU hV σ y hy]
    exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank (π.app U).hom _ he hf hr _
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hVa, hzV, h, hVe⟩ := etale_pullback_coords_of_etale π hπ D U hU hV he c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hVa _ hVe (mem_ptsIn.2 hzV)
    have key : ∀ w ∈ c''.e.source, w ∈ ptsIn q σ V ∧
        ∀ a, c''.e w a = ev q σ V ((π.appLE c.U V h).hom (c.x a)) w := by
      rcases c'' with ⟨e, U', aff, x', et, ss, ae, ho⟩
      dsimp only at hU'' hx'' ⊢
      subst hU''
      have hx : x' = fun a => (π.appLE c.U U' h).hom (c.x a) := hx''
      subst hx
      exact fun w hw => ⟨ss hw, ae w hw⟩
    have hS : IsOpen (c''.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source) :=
      (PtsOver.continuous_map π hπ (spMap σ)).continuousOn.isOpen_inter_preimage c''.e.open_source
        c.e.open_source
    refine ⟨c''.restr _ hS, ⟨hc'', hc'', hc⟩, fun w hw => ⟨hw.2.2, ?_⟩⟩
    have hw' : w ∈ c''.e.source := hw.1
    obtain ⟨hwV, hwe⟩ := key w hw'
    ext a
    change c''.e w a = c.e (PtsOver.map π hπ (spMap σ) w) a
    rw [hwe a, c.apply_eq _ hw.2.2 a]
    exact valR_appLE w.1 π h hwV _

end GlobalTheory.CoverDegProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionBigCellBaseAffineCoords
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

noncomputable section

namespace GlobalTheory.LogPole.CellBir

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem isIso_spMap_of_inverse {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (h₁ : f.comp g = RingHom.id B) (h₂ : g.comp f = RingHom.id A) : IsIso (spMap f) :=
  inferInstanceAs (IsIso (Spec.map (RingEquiv.toCommRingCatIso (RingEquiv.ofRingHom f g h₁ h₂)).hom))

theorem isOpenImmersion_spMap_away {R : Type} [CommRing R] (g : R) :
    IsOpenImmersion (spMap (algebraMap R (Localization.Away g))) := IsOpenImmersion.of_isLocalization g

set_option maxHeartbeats 3000000 in

theorem exists_isOpenImmersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), Nonempty W → ∃ V : (Spec (CommRingCat.of Γ(Y₀ TF.X Z, W))).Opens, Nonempty V ∧ IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by

  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h hW
  obtain ⟨g, hnil, hU0, z, hz, hzU, hC, hX⟩ := GlobalTheory.T.exists_bigCell_point_basicOpen_affineSpace_coords E H Dw l Xo c TF Z hF U n e v hv W k L N h hW
  obtain ⟨φ, hφ⟩ : ∃ φ : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1) →+* Γ(Y₀ TF.X Z, W),
    φ = MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) := ⟨_, rfl⟩
  rw [← hφ] at hnil hU0 ⊢
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = ev z W hz := ⟨_, rfl⟩
  have hψφ : ψ.comp φ = algebraMap _ (Localization.Away g) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, hφ, MvPolynomial.eval₂Hom_C, hψ]
      exact hC r
    · intro i
      simp only [RingHom.comp_apply, hφ, MvPolynomial.eval₂Hom_X', hψ]
      exact hX i
  have hψu : IsUnit (ψ (φ g)) := by
    rw [← RingHom.comp_apply, hψφ]
    exact IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨ψ', hψ'c⟩ : ∃ ψ' : Localization.Away (φ g) →+* Localization.Away g, ψ'.comp (algebraMap _ _) = ψ :=
    ⟨_, IsLocalization.Away.lift_comp (φ g) hψu⟩
  obtain ⟨θ, hθc⟩ : ∃ θ : Localization.Away g →+* Localization.Away (φ g),
      θ.comp (algebraMap _ _) = (algebraMap _ (Localization.Away (φ g))).comp φ :=
    ⟨Localization.awayMap φ g, IsLocalization.map_comp _⟩

  have hz₀ : ⊤ ≤ (spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) ≫ GlobalTheory.FlagMod.tau h.1) ⁻¹ᵁ W :=
    GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le h.1 le_rfl)
  have ev₀ := GlobalTheory.FlagMod.ev_spMap_tau h.1 (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) hz₀
  have hz' : ⊤ ≤ (spMap θ ≫ z) ⁻¹ᵁ W := GlobalTheory.FlagMod.le_preimage_comp _ hz
  have ev' : ev (spMap θ ≫ z) W hz' = θ.comp ψ := by rw [hψ]; exact GlobalTheory.FlagMod.ev_spMap θ z W hz hz'
  have hcomp : ∀ p, θ (ψ (φ p)) = algebraMap _ (Localization.Away (φ g)) (φ p) := fun p => by
    rw [← RingHom.comp_apply ψ φ, hψφ, ← RingHom.comp_apply θ, hθc, RingHom.comp_apply]
  have heq : spMap θ ≫ z = spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) ≫ GlobalTheory.FlagMod.tau h.1 := by
    refine GlobalTheory.T.bigCell_point_eq_of_base_and_cellCoordinates_eq E H Dw l Xo c TF Z hF U n e v hv W k L N h _ _ _ hz' hz₀
      (GlobalTheory.FlagMod.le_preimage_comp _ hzU) (hU0 _ _ hz₀ (by
        rw [ev₀]; exact IsLocalization.Away.algebraMap_isUnit _)) (fun r => ?_) (fun i => ?_)
    · have := hcomp (MvPolynomial.C r)
      simp only [hφ, MvPolynomial.eval₂Hom_C] at this
      rw [ev', ev₀, RingHom.comp_apply]
      exact this
    · have := hcomp (MvPolynomial.X i)
      simp only [hφ, MvPolynomial.eval₂Hom_X'] at this
      rw [ev', ev₀, RingHom.comp_apply]
      exact this
  have hθψ : θ.comp ψ = algebraMap _ (Localization.Away (φ g)) := by
    exact ev'.symm.trans ((GlobalTheory.FlagMod.ev_congr heq W hz' hz₀).trans ev₀)
  have h1 : ψ'.comp θ = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers g)
      ((congrArg (ψ'.comp ·) hθc).trans ((congrArg (·.comp φ) hψ'c).trans hψφ))
  have h2 : θ.comp ψ' = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (φ g)) ((congrArg (θ.comp ·) hψ'c).trans hθψ)
  haveI : Nontrivial (Localization.Away (φ g)) := OreLocalization.nontrivial_iff.mpr hnil
  haveI : IsOpenImmersion (spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))))))
  refine ⟨(spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).opensRange, ?_, ?_⟩
  · have x : Sp (Localization.Away (φ g)) :=
      (inferInstance : Nonempty (PrimeSpectrum (Localization.Away (φ g)))).some
    exact ⟨⟨_, Set.mem_range_self x⟩⟩
  · have key : ((spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).opensRange).ι =
        (spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).isoOpensRange.inv ≫
          spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) := by
      exact (Iso.eq_inv_comp _).2 (Scheme.Hom.isoOpensRange_hom_ι _)
    have hfac : spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) ≫ spMap φ =
        spMap θ ≫ spMap (algebraMap _ (Localization.Away g)) :=
      (spMap_comp_ringHom φ _).trans ((congrArg spMap hθc.symm).trans (spMap_comp_ringHom _ θ).symm)
    haveI : IsIso (spMap θ) := isIso_spMap_of_inverse θ ψ' h2 h1
    haveI := isOpenImmersion_spMap_away g
    have hoi : IsOpenImmersion ((spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).isoOpensRange.inv ≫
        spMap θ ≫ spMap (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g))) := inferInstance
    rw [← hfac, ← Category.assoc, ← key] at hoi
    exact hoi

end GlobalTheory.LogPole.CellBir
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projSpace_map_of_tuple_hasDivisor : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (β : o →+* k) (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace o n, h ≫ PSpace.str o n = M.s ≫ spMap β ∧ PCrd (M.pt ≫ h) c := by
  first | exact @GlobalTheory.SiegTh.CrdMapBC.exists_map_of_hasDiv | exact GlobalTheory.SiegTh.CrdMapBC.exists_map_of_hasDiv | (intros; apply GlobalTheory.SiegTh.CrdMapBC.exists_map_of_hasDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveAlgebraisationFormalEmbeddingComStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projective_algebraisation_formalEmbedding_complete : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j)) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ e, F ∈ vanIdeal ((Y e).hom ≫ thick R I e) (s e)) → F ∈ vanIdeal B.hom s' := by
  first | exact @GlobalTheory.FormalAlg.exists_projective_of_formal_embedding | exact GlobalTheory.FormalAlg.exists_projective_of_formal_embedding | (intros; apply GlobalTheory.FormalAlg.exists_projective_of_formal_embedding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackSectionZerosNormMultiplicities
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

theorem exists_secPull_props : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (M : MLine p σ) (s : M.B.Sec), ∃ s' : (M.pull π hπ).B.Sec, nonzeroLocus s' = π ⁻¹ᵁ nonzeroLocus s ∧ (∀ y, (M.pull π hπ).φ.nsq (secVal q σ s') y = M.φ.nsq (secVal p σ s) (ptMap π hπ σ y)) ∧ ∀ [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (hη : π (genericPoint Y) ⤳ genericPoint X) (hs : genericPoint X ∈ nonzeroLocus s) (hs' : genericPoint Y ∈ nonzeroLocus s') (w : Y) (i : M.B.ι), π w ∈ M.B.U i → (divOfSec (M.pull π hπ).φ.isLB s' hs').mult w = Scheme.ord (TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField)) w := by
  intro k _ X Y p q σ π hπ M s
  refine ⟨GlobalTheory.Cartier.secPull s π, GlobalTheory.Cartier.nonzeroLocus_secPull s π, fun y =>
    Weight.nsq_pull_secPull M.φ π hπ s y, ?_⟩
  intro _ _ _ hη hs hs' w i hw
  have hc : w ∈ (M.B.pull π).U (fun _ => i) := by
    rw [GlobalTheory.Cartier.pull_U]; exact hw
  have hg : genericPoint Y ∈ (M.B.pull π).U (fun _ => i) := gen_mem hc
  have hg' : genericPoint Y ∈ π ⁻¹ᵁ M.B.U i := by
    have h := hg
    rw [GlobalTheory.Cartier.pull_U] at h
    exact h
  have h0 : genericPoint X ∈ M.B.U i := gen_mem hw
  have e : ((ratOfSec (L := (M.pull π hπ).B) (GlobalTheory.Cartier.secPull s π) hs' fun _ => i : Y.functionFieldˣ) :
      Y.functionField) = TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField) := by
    rw [val_ratOfSec h0, TrueGeo.SmallSec.fnMap_fnOf π hη h0 hg']
    exact (val_ratOfSec (L := M.B.pull π) (s := GlobalTheory.Cartier.secPull s π) (hs := hs') hg).trans
      (fnOf_resG (GlobalTheory.Cartier.pull_U M.B π fun _ => i).le hg _)
  exact ((presents_divOfRatSec _ _).isEqn (fun _ => i) w hc).mult_eq.trans (congrArg (Scheme.ord · w) e)

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnectedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpace_component_smooth_projective_connected : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → IsVariety₀ T.X Z := by
  first | exact @GlobalTheory.VarFlag.isVariety₀_flag | exact GlobalTheory.VarFlag.isVariety₀_flag | (intros; apply GlobalTheory.VarFlag.isVariety₀_flag <;> assumption)
end

