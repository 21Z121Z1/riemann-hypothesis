import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionMemComponentGenericOfClosedValuation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem separated_of_isOpen_component_subtype {X : Type*} [TopologicalSpace X] (F : Set X) (a : X)
    (ha : a ∈ F) (ho : IsOpen (connectedComponent (⟨a, ha⟩ : F))) :
    Disjoint (connectedComponentIn F a) (closure (F \ connectedComponentIn F a)) ∧
      Disjoint (closure (connectedComponentIn F a)) (F \ connectedComponentIn F a) := by
  have hC : connectedComponentIn F a = Subtype.val '' connectedComponent (⟨a, ha⟩ : F) :=
    connectedComponentIn_eq_image ha
  have hmem : ∀ y : F, (y : X) ∈ connectedComponentIn F a ↔ y ∈ connectedComponent (⟨a, ha⟩ : F) := by
    intro y
    rw [hC]
    exact Subtype.val_injective.mem_set_image
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 ho
  obtain ⟨Z, hZ, hZe⟩ := isClosed_induced_iff.1
    (isClosed_connectedComponent : IsClosed (connectedComponent (⟨a, ha⟩ : F)))
  constructor
  · have h1 : closure (F \ connectedComponentIn F a) ⊆ Uᶜ := by
      refine closure_minimal ?_ hU.isClosed_compl
      rintro y ⟨hyF, hy⟩ hyU
      apply hy
      refine (hmem ⟨y, hyF⟩).2 ?_
      rw [← hUe]
      exact hyU
    refine Set.disjoint_left.2 fun y hy hy' => h1 hy' ?_
    have := (hmem ⟨y, connectedComponentIn_subset F a hy⟩).1 hy
    rw [← hUe] at this
    exact this
  · have h1 : closure (connectedComponentIn F a) ⊆ Z := by
      refine closure_minimal ?_ hZ
      intro y hy
      have := (hmem ⟨y, connectedComponentIn_subset F a hy⟩).1 hy
      rw [← hZe] at this
      exact this
    refine Set.disjoint_left.2 fun y hy hy' => hy'.2 ?_
    refine (hmem ⟨y, hy'.1⟩).2 ?_
    rw [← hZe]
    exact h1 hy

theorem isOpen_component_fibre_subtype {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (a : (f ⁻¹' {s} : Set X)) : IsOpen (connectedComponent a) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s)))
  have hn : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have ho := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' _ hn ((f.fiberHomeo s).symm a)
  have h := (f.fiberHomeo s).isOpenMap _ ho
  have h2 : (f.fiberHomeo s) '' connectedComponent ((f.fiberHomeo s).symm a)
      = connectedComponent a := by
    have := (f.fiberHomeo s).image_connectedComponentIn (s := Set.univ)
      (x := (f.fiberHomeo s).symm a) (Set.mem_univ _)
    simpa [connectedComponentIn_univ, (f.fiberHomeo s).surjective.range_eq] using this
  rwa [h2] at h

theorem section_mem_component_generic_of_closed :
    ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (e σ : Spec (CommRingCat.of V) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → σ ≫ f = 𝟙 _ → σ (IsLocalRing.closedPoint V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → σ (⊥ : PrimeSpectrum V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  intro V _ _ _ X f e σ hf he hσ hm
  have hfe : ∀ p : (Spec (CommRingCat.of V) : Scheme.{0}), f (e p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hfσ : ∀ p : (Spec (CommRingCat.of V) : Scheme.{0}), f (σ p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, hσ]; rfl
  let g₀ : (Spec (CommRingCat.of V) : Scheme.{0}) := (⊥ : PrimeSpectrum V)
  let m : (Spec (CommRingCat.of V) : Scheme.{0}) := IsLocalRing.closedPoint V
  change σ m ∈ connectedComponentIn (f ⁻¹' {f (σ m)}) (e (f (σ m))) at hm
  change σ g₀ ∈ connectedComponentIn (f ⁻¹' {f (σ g₀)}) (e (f (σ g₀)))
  rw [hfσ] at hm ⊢
  have hsp : g₀ ⤳ m := IsLocalRing.specializes_closedPoint (R := V) ⊥
  have ha : e g₀ ∈ f ⁻¹' {g₀} := hfe g₀
  obtain ⟨h1, h2⟩ := separated_of_isOpen_component_subtype (f ⁻¹' {g₀}) (e g₀) ha
    (isOpen_component_fibre_subtype f g₀ ⟨e g₀, ha⟩)
  obtain ⟨hd, hu⟩ := GlobalTheory.T.disjoint_closure_and_union_eq_univ_of_genericFibre_partition V X f hf (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
    (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
    (Set.union_diff_cancel (connectedComponentIn_subset _ _)) h1 h2
  by_contra hne
  have hσ' : σ m ∈ closure (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀)) :=
    (hsp.map σ.continuous).mem_closed isClosed_closure (subset_closure ⟨hfσ g₀, hne⟩)
  have he' : e m ∈ closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀)) :=
    (hsp.map e.continuous).mem_closed isClosed_closure
      (subset_closure (mem_connectedComponentIn ha))
  have hclopen : IsClopen (closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))) := by
    refine ⟨isClosed_closure, ?_⟩
    have : closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
        = (closure (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀)))ᶜ :=
      (IsCompl.eq_compl ⟨hd, codisjoint_iff.2 hu⟩)
    rw [this]
    exact isClosed_closure.isOpen_compl
  have hsub := (isPreconnected_connectedComponentIn (x := e m) (F := f ⁻¹' {m})).subset_isClopen
    hclopen ⟨e m, mem_connectedComponentIn (hfe m), he'⟩
  exact Set.disjoint_left.1 hd (hsub hm) hσ'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafSectionEqZeroAtStageOfFilteredColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FilteredSections

variable {R : Type} [CommRing R]

lemma etale_of_isPushout {A B C P : CommRingCat.{0}} {g : A ⟶ B} {f : A ⟶ C} {inl : B ⟶ P}
    {inr : C ⟶ P} (sq : IsPushout g f inl inr) (hg : g.hom.Etale) : inr.hom.Etale := by
  have : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty @RingHom.Etale) sq.flip hg

lemma cover_of_isPushout {ι : Type} {A C : CommRingCat.{0}} {B P : ι → CommRingCat.{0}}
    (g : ∀ i, A ⟶ B i) (f : A ⟶ C) (inl : ∀ i, B i ⟶ P i) (inr : ∀ i, C ⟶ P i)
    (sq : ∀ i, IsPushout (g i) f (inl i) (inr i))
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) :
    ∀ p : Spec C, ∃ i v, Spec.map (inr i) v = p := by
  intro p
  obtain ⟨i, v, hv⟩ := hcov (Spec.map f p)
  obtain ⟨z, hz⟩ := GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (sq i).flip p v hv.symm
  exact ⟨i, z, hz⟩

lemma eq_zero_of_cover (F : Shv R) {ι : Type} {A : CommRingCat.{0}} {B : ι → CommRingCat.{0}}
    (g : ∀ i, A ⟶ B i) (hg : ∀ i, (g i).hom.Etale)
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) (y : (onRings F).obj A)
    (hy : ∀ i, ((onRings F).map (g i)).hom y = 0) : y = 0 :=
  (GlobalTheory.EtC.sec_sep_glue_of_points R F (Spec A) ι (fun i => Spec (B i)) (fun i => Spec.map (g i))
    (fun i => (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (hg i)) hcov).1 y hy

lemma map_eta {M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)} {F : Shv R}
    (η : M ⟶ onRings F) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : M.obj A) :
    ((onRings F).map f).hom ((η.app A).hom x) = (η.app B).hom ((M.map f).hom x) := by
  change (η.app A ≫ (onRings F).map f).hom x = (M.map f ≫ η.app B).hom x
  rw [η.naturality]

lemma stage_of_pieces (F : Shv R) {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (j : J) (y : (onRings F).obj (D.obj j)) {ι : Type} [Finite ι]
    (B : ι → CommRingCat.{0}) (g : ∀ i, D.obj j ⟶ B i) (hg : ∀ i, (g i).hom.Etale)
    (hcov : ∀ p : Spec (D.obj j), ∃ i v, Spec.map (g i) v = p)
    (D' : ι → (Under j ⥤ CommRingCat.{0})) (u : ∀ i, Under.forget j ⋙ D ⟶ D' i)
    (v : ∀ i, (Functor.const _).obj (B i) ⟶ D' i)
    (sq : ∀ i (k : Under j), IsPushout (g i) (D.map k.hom) ((v i).app k) ((u i).app k))
    (hk : ∀ i, ∃ k : Under j,
      ((onRings F).map ((v i).app k)).hom (((onRings F).map (g i)).hom y) = 0) :
    ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0 := by
  classical
  choose k hk using hk
  letI := Fintype.ofFinite ι
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (Finset.univ.image k)
  have e : ∀ i, k i ⟶ K := fun i => (hK (Finset.mem_image_of_mem _ (Finset.mem_univ i))).some
  refine ⟨K.right, K.hom, ?_⟩
  apply eq_zero_of_cover F (fun i => (u i).app K) (fun i => etale_of_isPushout (sq i K) (hg i))
    (cover_of_isPushout g (D.map K.hom) (fun i => (v i).app K) (fun i => (u i).app K)
      (fun i => sq i K) hcov)
  intro i
  have h1 : (v i).app (k i) ≫ (D' i).map (e i) = (v i).app K := by
    simpa using ((v i).naturality (e i)).symm
  have h2 : D.map K.hom ≫ (u i).app K = g i ≫ (v i).app K := (sq i K).w.symm
  have h3 : ((onRings F).map ((u i).app K)).hom (((onRings F).map (D.map K.hom)).hom y) =
      ((onRings F).map ((D' i).map (e i))).hom
        (((onRings F).map ((v i).app (k i))).hom (((onRings F).map (g i)).hom y)) := by
    have := congrArg (fun φ => ((onRings F).map φ).hom y) h2
    rw [← h1] at this
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
    erw [Functor.map_comp (onRings F) (D.map K.hom) ((u i).app K)] at this
    exact this
  rw [h3, hk i, map_zero]

lemma stage_of_eta (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R)
    (η : M ⟶ onRings F) (hM : PreservesFilteredColimitsOfSize.{0, 0} M)
    (hker : ∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι)
      (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧
      (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0)
    (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (j : J) (m : M.obj (D.obj j))
    (hm : ((onRings F).map (c.ι.app j)).hom ((η.app _).hom m) = 0) :
    ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom ((η.app _).hom m) = 0 := by
  have hMel := (GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements _ M).2.1 hM
  rw [map_eta] at hm
  obtain ⟨ι, _, B, g, hg, hcov, hz⟩ := hker _ _ hm
  obtain ⟨j', f0, B', g', h, hsq, hcov'⟩ :=
    GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit J D c hc ι B g hg hcov j
  choose D' ιB u v hcol hpush using fun i =>
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc j' (B' i) (B i) (g' i) (h i) (g i)
      (hsq i).2
  have hk : ∀ i, ∃ k : Under j', ((onRings F).map ((v i).app k)).hom
      (((onRings F).map (g' i)).hom ((η.app _).hom ((M.map (D.map f0)).hom m))) = 0 := by
    intro i
    let k0 : Under j' := Under.mk (𝟙 j')
    have e1 : D.map f0 ≫ g' i ≫ (v i).app k0 ≫ (ιB i).app k0 = c.ι.app j ≫ g i := by
      rw [(hpush i k0).2.1, (hsq i).2.w, ← Category.assoc, c.w]
    have hdie : (M.map ((ιB i).app k0)).hom ((M.map ((v i).app k0)).hom
        ((M.map (g' i)).hom ((M.map (D.map f0)).hom m))) = 0 := by
      have := congrArg (fun φ => (M.map φ).hom m) e1
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [this]
      exact hz i
    obtain ⟨k, f, hf⟩ := (hMel (Under j') (D' i) _ (hcol i).some).2 k0 _ hdie
    refine ⟨k, ?_⟩
    have e2 : (v i).app k0 ≫ (D' i).map f = (v i).app k := by
      simpa using ((v i).naturality f).symm
    rw [map_eta]
    erw [map_eta]
    rw [← e2, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hf,
      map_zero]
  obtain ⟨k, f, hf⟩ := stage_of_pieces F D j' ((η.app _).hom ((M.map (D.map f0)).hom m)) B' g'
    (fun i => (hsq i).1) hcov' D' u v (fun i k => (hpush i k).1) hk
  refine ⟨k, f0 ≫ f, ?_⟩
  rw [map_eta] at hf ⊢
  rw [Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact hf

theorem eq_zero_at_stage_of_map_colimit_eq_zero : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0 := by
  intro R _ M F η hM hloc hker J _ _ D c hc j y hy
  obtain ⟨ι, _, B, g, m, hg, hcov, hm⟩ := hloc _ y
  have hP : ∀ i, IsPushout (g i) (c.ι.app j) (pushout.inl (g i) (c.ι.app j))
      (pushout.inr (g i) (c.ι.app j)) := fun i => IsPushout.of_hasPushout _ _
  choose D' ιB u v hcol hpush using fun i =>
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc j (B i)
      (pushout (g i) (c.ι.app j)) (g i) (pushout.inl (g i) (c.ι.app j))
      (pushout.inr (g i) (c.ι.app j)) (hP i)
  have hk : ∀ i, ∃ k : Under j,
      ((onRings F).map ((v i).app k)).hom (((onRings F).map (g i)).hom y) = 0 := by
    intro i
    let k0 : Under j := Under.mk (𝟙 j)
    have h0 : ((onRings F).map ((ιB i).app k0)).hom
        ((η.app _).hom ((M.map ((v i).app k0)).hom (m i))) = 0 := by
      calc ((onRings F).map ((ιB i).app k0)).hom ((η.app _).hom ((M.map ((v i).app k0)).hom (m i)))
          = (η.app _).hom ((M.map ((v i).app k0 ≫ (ιB i).app k0)).hom (m i)) := by
            rw [map_eta, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
        _ = ((onRings F).map (pushout.inl (g i) (c.ι.app j))).hom ((η.app _).hom (m i)) := by
            rw [(hpush i k0).2.1, map_eta]
            rfl
        _ = ((onRings F).map (g i ≫ pushout.inl (g i) (c.ι.app j))).hom y := by
            rw [hm i, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
        _ = 0 := by
            rw [pushout.condition, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hy,
              map_zero]
    obtain ⟨k, f, hf⟩ := stage_of_eta M F η hM hker (Under j) (D' i) _ (hcol i).some k0 _ h0
    refine ⟨k, ?_⟩
    have e2 : (v i).app k0 ≫ (D' i).map f = (v i).app k := by
      simpa using ((v i).naturality f).symm
    rw [← hm i]
    erw [map_eta]
    rw [← e2, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
      ← map_eta]
    exact hf
  exact stage_of_pieces F D j y B g hg hcov D' u v (fun i k => (hpush i k).1) hk

end GlobalTheory.EtC.FilteredSections
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfStableOfIsFractionRing
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in

theorem _root_.GlobalTheory.span_eq_top_of_stable_of_isFractionRing :
    ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k K] [Algebra F K] [FiniteDimensional F K] (B : Subalgebra k K) [IsFractionRing B K] (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Submodule.span K S = ⊤ → Submodule.span F S = ⊤ := by
  intro k F K _ _ _ _ _ _ B _ W _ _ _ _ S hS hspan
  set M := Submodule.span F S with hM
  let T : Subalgebra F K :=
    { carrier := {y | ∀ m ∈ M, y • m ∈ M}
      mul_mem' := fun {a b} ha hb m hm => by rw [mul_smul]; exact ha _ (hb m hm)
      one_mem' := fun m hm => by rwa [one_smul]
      add_mem' := fun {a b} ha hb m hm => by rw [add_smul]; exact M.add_mem (ha m hm) (hb m hm)
      zero_mem' := fun m _ => by rw [zero_smul]; exact M.zero_mem
      algebraMap_mem' := fun f m hm => by rw [algebraMap_smul]; exact M.smul_mem f hm }
  have hmemT : ∀ y : K, y ∈ T ↔ ∀ m ∈ M, y • m ∈ M := fun y => Iff.rfl
  have hB : ∀ c ∈ B, (c : K) ∈ T := by
    intro c hc m hm
    induction hm using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span (hS c hc s hs)
    | zero => rw [smul_zero]; exact M.zero_mem
    | add v w _ _ hv hw => rw [smul_add]; exact M.add_mem hv hw
    | smul f v _ hv => rw [smul_comm]; exact M.smul_mem f hv
  have hinv : ∀ y : K, y ∈ T → y⁻¹ ∈ T := by
    intro y hy
    exact T.inv_mem_of_algebraic (x := ⟨y, hy⟩) (Algebra.IsAlgebraic.isAlgebraic y)
  have hall : ∀ y : K, y ∈ T := by
    intro y
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    rw [div_eq_mul_inv]
    exact T.mul_mem (hB _ a.2) (hinv _ (hB _ b.2))
  let MK : Submodule K W :=
    { carrier := M
      add_mem' := M.add_mem
      zero_mem' := M.zero_mem
      smul_mem' := fun c m hm => hall c m hm }
  have hle : Submodule.span K S ≤ MK := Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
  rw [hspan] at hle
  exact eq_top_iff.mpr fun w _ => hle Submodule.mem_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapSmoothSurjectiveOfIsSeparable
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC
namespace GlobalTheory

theorem spec_map_smooth_surjective_of_isSeparable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have hfp : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.Etale K L := ⟨inferInstance, inferInstance⟩
  have hs : Algebra.Smooth K L := inferInstance
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    rw [RingHom.Smooth]
    simp only [CommRingCat.hom_ofHom]
    exact RingHom.smooth_algebraMap.mpr hs
  · constructor
    intro x
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    exact ⟨y, Subsingleton.elim _ _⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiCofanIsColimitOfRingEquivStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_pi_cofan_isColimit_of_ringEquiv : ∀ (ι : Type) [Finite ι] (T : ι → Type) [∀ i, CommRing (T i)] (B : Type) [CommRing B] (e : B ≃+* (∀ i, T i)), Nonempty (IsColimit (Cofan.mk (Spec (CommRingCat.of B)) (fun i ↦ Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))))) := by
  first | exact @GlobalTheory.EtC.spec_pi_cofan_isColimit | exact GlobalTheory.EtC.spec_pi_cofan_isColimit | (intros; apply GlobalTheory.EtC.spec_pi_cofan_isColimit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsLimitWidePullback
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem specAdj_symm_comp_specMap (T : Scheme.{0}) {R S : CommRingCat.{0}}
    (f : T ⟶ Spec S) (φ : R ⟶ S) :
    ((ΓSpec.adjunction.homEquiv T (op R)).symm (f ≫ Spec.map φ)).unop =
      φ ≫ ((ΓSpec.adjunction.homEquiv T (op S)).symm f).unop := by
  have h := ΓSpec.adjunction.homEquiv_naturality_right_symm (X := T) (Y := op S) (Y' := op R)
    f φ.op
  exact congrArg Quiver.Hom.unop h

theorem spec_widePushout_isLimit : ∀ (n : ℕ) (C D A : Type) [CommRing C] [CommRing D] [CommRing A] (a : C →+* D) (b : C →+* A) (l : Fin n → (D →+* A)) (hl : ∀ i, (l i).comp a = b), (∀ (B : Type) [CommRing B] (g : Fin n → (D →+* B)) (c : C →+* B), (∀ i, (g i).comp a = c) → ∃! u : A →+* B, u.comp b = c ∧ ∀ i, u.comp (l i) = g i) → Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) (fun i => Spec.map (CommRingCat.ofHom (l i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i]))) := by
  intro n C D A _ _ _ a b l hl H
  classical
  let adj := ΓSpec.adjunction
  let e : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}), (op Γ(T, ⊤) ⟶ op R) ≃ (T ⟶ Spec R) :=
    fun T R => adj.homEquiv T (op R)
  have hcomp : ∀ (T : Scheme.{0}) {R S : CommRingCat.{0}} (f : T ⟶ Spec S) (φ : R ⟶ S),
      ((e T R).symm (f ≫ Spec.map φ)).unop = φ ≫ ((e T S).symm f).unop :=
    fun T R S f φ => specAdj_symm_comp_specMap T f φ
  have hse : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}) (ψ : R ⟶ Γ(T, ⊤)),
      ((e T R).symm (e T R ψ.op)).unop = ψ := fun T R ψ => by
    rw [Equiv.symm_apply_apply]; rfl
  have hinj : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}) (f g : T ⟶ Spec R),
      ((e T R).symm f).unop = ((e T R).symm g).unop → f = g :=
    fun T R f g h => (e T R).symm.injective (Quiver.Hom.unop_inj h)

  let gOf : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))),
      Fin n → (D →+* Γ(t.pt, ⊤)) :=
    fun t i => ((e t.pt (CommRingCat.of D)).symm (t.π i)).unop.hom
  let cOf : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))),
      C →+* Γ(t.pt, ⊤) :=
    fun t => ((e t.pt (CommRingCat.of C)).symm t.base).unop.hom
  have hgc : ∀ t i, (gOf t i).comp a = cOf t := by
    intro t i
    have h1 := hcomp t.pt (t.π i) (CommRingCat.ofHom a)
    rw [t.condition i] at h1
    have h2 := congrArg CommRingCat.Hom.hom h1
    simpa [gOf, cOf] using h2.symm
  let uOf : ∀ t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a)), A →+* Γ(t.pt, ⊤) := fun t => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose
  have huOf : ∀ t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a)), (uOf t).comp b = cOf t ∧ ∀ i, (uOf t).comp (l i) = gOf t i :=
    fun t => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose_spec.1
  have huniq : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))) (u : A →+* Γ(t.pt, ⊤)), u.comp b = cOf t → (∀ i, u.comp (l i) = gOf t i) →
      u = uOf t :=
    fun t u h1 h2 => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose_spec.2 u ⟨h1, h2⟩
  refine ⟨WidePullbackCone.IsLimit.mk _
    (fun t => e t.pt (CommRingCat.of A) (CommRingCat.ofHom (uOf t)).op) ?_ ?_ ?_⟩
  · intro t
    rw [WidePullbackCone.mk_base]
    apply hinj
    erw [hcomp, hse]
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    exact (huOf t).1
  · intro t i
    rw [WidePullbackCone.mk_π]
    apply hinj
    erw [hcomp, hse]
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    exact (huOf t).2 i
  · intro t m hb hπ
    rw [WidePullbackCone.mk_base] at hb
    simp only [WidePullbackCone.mk_π] at hπ
    have hu : ((e t.pt (CommRingCat.of A)).symm m).unop.hom = uOf t := by
      apply huniq
      · have hb' : m ≫ Spec.map (CommRingCat.ofHom b) = t.base := hb
        have h1 : ((e t.pt (CommRingCat.of C)).symm t.base).unop =
            CommRingCat.ofHom b ≫ ((e t.pt (CommRingCat.of A)).symm m).unop := by
          rw [← hb']; exact hcomp t.pt m (CommRingCat.ofHom b)
        have h2 := congrArg CommRingCat.Hom.hom h1
        rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
        exact h2.symm
      · intro i
        have hπ' : m ≫ Spec.map (CommRingCat.ofHom (l i)) = t.π i := hπ i
        have h1 : ((e t.pt (CommRingCat.of D)).symm (t.π i)).unop =
            CommRingCat.ofHom (l i) ≫ ((e t.pt (CommRingCat.of A)).symm m).unop := by
          rw [← hπ']; exact hcomp t.pt m (CommRingCat.ofHom (l i))
        have h2 := congrArg CommRingCat.Hom.hom h1
        rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
        exact h2.symm
    apply hinj
    rw [hse, ← hu]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneAdicCompletionNumberFieldStatement
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  first | exact @GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion | exact GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion | (intros; apply GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoethe
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

open KaehlerDifferential in

theorem _root_.GlobalTheory.PD.rA_isFractionRing_isNoetherianRing : ∀ (k : Type) [Field k]
    (F : Type) [Field F] [Algebra k F] (d : ℕ)
    (x : Fin (d + 1) → F), _root_.GlobalTheory.PD.IsPd k x → ∀ I : Finset (Fin (d + 1)),
      I.Nonempty →
      IsFractionRing (_root_.GlobalTheory.PD.rA k x I) F ∧
        IsNoetherianRing (_root_.GlobalTheory.PD.rA k x I) := by
  intro k _ F _ _ d x hx I hI
  set S : Set F := {y | ∃ i ∈ I, ∃ j, y = x j / x i} with hS
  have hA : _root_.GlobalTheory.PD.rA k x I = Algebra.adjoin k S := rfl
  refine ⟨?_, ?_⟩
  · refine IsFractionRing.of_field _ F fun z => ?_
    obtain ⟨i, hi⟩ := hI
    have hle : IntermediateField.adjoin k (Set.range fun j : Fin d => x j.succ / x 0) ≤
        IntermediateField.adjoin k S := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_adjoin_iff_div]
      refine ⟨x j.succ / x i, Algebra.subset_adjoin ⟨i, hi, j.succ, rfl⟩,
        x 0 / x i, Algebra.subset_adjoin ⟨i, hi, 0, rfl⟩, ?_⟩
      have h0 := hx.ne 0
      have hi0 := hx.ne i
      field_simp
    have hz : z ∈ IntermediateField.adjoin k S := by
      apply hle
      rw [hx.gen]
      trivial
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩
  · have hfin : S.Finite :=
      (Set.finite_range fun q : Fin (d + 1) × Fin (d + 1) => x q.2 / x q.1).subset
        (by rintro _ ⟨i, -, j, rfl⟩; exact ⟨(i, j), rfl⟩)
    have hfg : (_root_.GlobalTheory.PD.rA k x I).FG := by
      rw [hA, ← hfin.coe_toFinset]
      exact Subalgebra.fg_adjoin_finset _
    haveI := (Subalgebra.fg_iff_finiteType _).mp hfg
    exact Algebra.FiniteType.isNoetherianRing k _

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSimplexFacePairsAcyclicPositiveDegreeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardSimplexFacePairs_acyclic_positive_degree : ∀ N k (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 → ∃ e, Pr.Deg (k + 2) e ∧ Pr.d N e = c := by
  first | (exact @GlobalTheory.PrAcyc.pr_acyclic) | (exact GlobalTheory.PrAcyc.pr_acyclic) | (intros; apply GlobalTheory.PrAcyc.pr_acyclic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonEtaleHypercohomologyOfRetractStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_etaleHypercohomology_of_retract : ∀ (R : Type) [CommRing R] (M M' : Shv R) (i : M ⟶ M') (r : M' ⟶ M), i ≫ r = 𝟙 M → ∀ (K : Cx R) (n : ℤ), Subsingleton (HK R K M' n) → Subsingleton (HK R K M n) := by
  first | exact @GlobalTheory.EtC.RetractAcyc.subsingleton_of_retract | exact GlobalTheory.EtC.RetractAcyc.subsingleton_of_retract | (intros; apply GlobalTheory.EtC.RetractAcyc.subsingleton_of_retract <;> assumption)
end

