import Development.EtaleCohomology.EtaleSheaves.Bundle0073
import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafShIsoOf
import Development.EtaleCohomology.EtaleSheaves.Bundle0072
import Development.EtaleCohomology.EtaleSheaves.Bundle0011
import Development.EtaleCohomology.EtaleSheaves.Bundle0049
import Development.EtaleCohomology.EtaleSheaves.Bundle0050
import Development.EtaleCohomology.EtaleSheaves.PullMonoPf
import Development.EtaleCohomology.EtaleSheaves.Bundle0070
import Development.EtaleCohomology.EtaleSheaves.TwPairExists

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSHNbSys
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf

namespace LateralTheory.E.StrictHenselianNeighbourhood

def IsPtNb {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ U.left)
    {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U)
    (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j)) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left) : Prop :=
  s default = x ∧ (∀ j, IsIso (e j)) ∧ (∀ j, l j ≫ e j ≫ (a j).left = s) ∧
  (∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left) ∧
  (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) ∧
  (∀ (j k : J) (f : j ⟶ k), l k ≫ Spec.map (CommRingCat.ofHom (D.map f).hom) = l j) ∧
  (∀ (U' : B.Etale) (b : U' ⟶ U) (l' : Spec (CommRingCat.of Ω) ⟶ U'.left), l' ≫ b.left = s →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left ∧ l j ≫ e j ≫ g = l') ∧
  (∀ (U' : B.Etale) (b : U' ⟶ U) (j : J) (g g' : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left →
      g' ≫ b.left = (a j).left → l j ≫ e j ≫ g = l j ≫ e j ≫ g' →
      ∃ (k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ g =
        Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ g')

def LeafSHNbSys : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left),
  ∃ (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (CommRingCat.of Ω) ⟶ U.left)
    (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t

def LeafSHLoc : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (c : Cocone D), IsColimit c → ∀ (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
  (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t → IsLocalRing c.pt

def LeafSHHens : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (c : Cocone D), IsColimit c → ∀ (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
  (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t → IsLocalRing c.pt →
  SH c.pt

theorem LeafSHNb_of (hS : LeafSHNbSys) (hL : LeafSHLoc) (hH : LeafSHHens) : LeafSHNb := by
  intro _ q _ k _ hq B U s0 x
  obtain ⟨Ω, _, _, s, J, _, _, D, c, hc, V, a, l, e, t, hP⟩ := hS U x
  obtain ⟨hs, he, hl, hcomp, ht, -, hcof, -⟩ := id hP
  refine ⟨J, inferInstance, inferInstance, D, c, hc, V, a, fun j => (l j ≫ e j) default, e, t, he, ?_, ?_, hcomp, ht,
    hH U x Ω s D c hc V a l e t hP (hL U x Ω s D c hc V a l e t hP), ?_⟩
  · intro j
    rw [← hs, ← hl j]
    rfl
  · intro j
    have := hq.map (Spec.preimage (e j ≫ (a j).left ≫ s0)).hom
    simpa using this
  · intro U' b y' hy'
    obtain ⟨l', hl', -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed b.left s y' (hy'.trans hs.symm)
    obtain ⟨j, g, hg, -⟩ := hcof U' b l' hl'
    exact ⟨j, g, hg⟩

end LateralTheory.E.StrictHenselianNeighbourhood
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSHPtOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StrictHenselianPoint
open LateralTheory.E.E4 LateralTheory.E.LeafDegCut LateralTheory.E.LeafSHPtPf

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem leafSHTop : LeafSHTop := by
  intro B U x J _ _ D c V a e t ht hcof
  obtain ⟨j0⟩ := (inferInstance : Nonempty J)
  constructor
  · intro O hxO
    have hU : Etale U.hom := U.prop
    let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (by
      change Etale (O.ι ≫ U.hom); infer_instance)
    let b : U' ⟶ U := MorphismProperty.Over.homMk (A := U') (B := U) O.ι rfl
    obtain ⟨j, g, hg⟩ := hcof U' b ⟨x, hxO⟩ rfl
    rintro _ ⟨z, rfl⟩
    rw [← ht j, ← hg]
    have : Set.range (O.ι) ⊆ (O : Set U.left) := by rw [Scheme.Opens.range_ι]
    apply this
    exact ⟨(Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g) z, by
      rfl⟩
  · intro S hS
    obtain ⟨𝒰, _, h, hU⟩ := (Scheme.mem_smallGrothendieckTopology _ _).1 hS
    obtain ⟨i, ⟨u, hu⟩⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀).1 x
    let fi : (𝒰.X i).asOverProp B (h i) ⟶ U := (𝒰.f i).asOverProp B
    refine ⟨_, fi, hU _ _ ⟨i⟩, ?_⟩
    obtain ⟨j, g, hg⟩ := hcof _ fi u hu
    exact ⟨Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g, by
      rw [Category.assoc, Category.assoc, hg, ht j]⟩

theorem LeafSHPt_of (hN : LateralTheory.E.LeafSHPtPf.LeafSHNb) : LateralTheory.E.LeafInj0VPf.LeafSHPt :=
  LateralTheory.E.LeafSHPtPf.LeafSHPt_of hN leafSHTop

end LateralTheory.E.StrictHenselianPoint
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSecRepPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafSecRepPf
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf LateralTheory.E.LeafShIsoPf.Sh

section General
universe u
variable {C : Type u} [Category.{0} C] (R : Type 1) [Ring R]

def FP : C ⥤ (Cᵒᵖ ⥤ ModuleCat.{1} R) :=
  yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type 0) (ModuleCat.{1} R)).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free R)

def gen {U V : C} (a : V ⟶ U) : ((FP R).obj U).obj (op V) :=
  ModuleCat.freeMk (R := R) (X := ULift.{1} (V ⟶ U)) (ULift.up a)

theorem map_gen {U V W : C} (a : V ⟶ U) (b : W ⟶ V) :
    ((FP R).obj U).map b.op (gen R a) = gen R (b ≫ a) :=
  ModuleCat.free_map_apply (R := R) _ _

theorem app_gen {U U' V : C} (a : V ⟶ U') (b : U' ⟶ U) :
    ((FP R).map b).app (op V) (gen R a) = gen R (a ≫ b) :=
  ModuleCat.free_map_apply (R := R) _ _

theorem freePresheaf_hom_ext {U V : C} {M : ModuleCat.{1} R} {f g : ((FP R).obj U).obj (op V) ⟶ M}
    (h : ∀ a : V ⟶ U, f (gen R a) = g (gen R a)) : f = g :=
  ModuleCat.free_hom_ext (R := R) (X := ULift.{1} (V ⟶ U)) (fun x => h x.down)

def desc (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) (s : G.obj (op U)) (V : C) :
    ((FP R).obj U).obj (op V) ⟶ G.obj (op V) :=
  ModuleCat.freeDesc (R := R) (X := ULift.{1} (V ⟶ U)) (↾fun x => G.map x.down.op s)

theorem desc_gen (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) (s : G.obj (op U)) {V : C} (a : V ⟶ U) :
    desc R G U s V (gen R a) = G.map a.op s :=
  ModuleCat.freeDesc_apply (R := R) _ _

theorem nat_gen {G : Cᵒᵖ ⥤ ModuleCat.{1} R} {U V : C} (η : (FP R).obj U ⟶ G) (a : V ⟶ U) :
    η.app (op V) (gen R a) = G.map a.op (η.app (op U) (gen R (𝟙 U))) := by
  have h := ConcreteCategory.congr_hom (η.naturality a.op) (gen R (𝟙 U))
  simp only [ConcreteCategory.comp_apply] at h
  rw [map_gen, Category.comp_id] at h
  exact h

def yE (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) : ((FP R).obj U ⟶ G) ≃ G.obj (op U) where
  toFun η := η.app (op U) (gen R (𝟙 U))
  invFun s :=
    { app := fun V => desc R G U s V.unop
      naturality := by
        rintro ⟨V⟩ ⟨W⟩ ⟨b⟩
        apply freePresheaf_hom_ext
        intro a
        simp only [ConcreteCategory.comp_apply]
        have h := map_gen R a b
        erw [h, desc_gen, desc_gen]
        rw [op_comp, G.map_comp, ConcreteCategory.comp_apply]
        rfl }
  left_inv η := by
    ext1
    funext ⟨V⟩
    apply freePresheaf_hom_ext
    intro a
    exact (desc_gen R G U _ a).trans (nat_gen R η a).symm
  right_inv s := by
    refine (desc_gen R G U s (𝟙 U)).trans ?_
    simp

theorem yE_res {G : Cᵒᵖ ⥤ ModuleCat.{1} R} {U U' : C} (a : U' ⟶ U) (η : (FP R).obj U ⟶ G) :
    yE R G U' ((FP R).map a ≫ η) = G.map a.op (yE R G U η) := by
  change η.app (op U') (((FP R).map a).app (op U') (gen R (𝟙 U'))) = _
  rw [app_gen, Category.id_comp]
  exact nat_gen R η a

theorem yE_sub {G : Cᵒᵖ ⥤ ModuleCat.{1} R} (U : C) (η η' : (FP R).obj U ⟶ G) :
    yE R G U (η - η') = yE R G U η - yE R G U η' := rfl

variable (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{1} R)]

theorem general (T : C ⥤ Sheaf J (ModuleCat.{1} R)) (i : FP R ⋙ presheafToSheaf J _ ≅ T) :
    ∃ e : ∀ (F : Sheaf J (ModuleCat.{1} R)) (U : C), (T.obj U ⟶ F) ≃ F.obj.obj (op U),
  (∀ (F G : Sheaf J (ModuleCat.{1} R)) (g : F ⟶ G) (U : C) (t : T.obj U ⟶ F),
    e G U (t ≫ g) = g.hom.app (op U) (e F U t)) ∧
  (∀ (F : Sheaf J (ModuleCat.{1} R)) (U U' : C) (a : U' ⟶ U) (t : T.obj U ⟶ F),
    e F U' (T.map a ≫ t) = F.obj.map a.op (e F U t)) ∧
  (∀ (F : Sheaf J (ModuleCat.{1} R)) (U : C) (t t' : T.obj U ⟶ F), e F U (t - t') = e F U t - e F U t') := by
  let adj := sheafificationAdjunction J (ModuleCat.{1} R)
  refine ⟨fun F U => ((Iso.homCongr (i.app U).symm (Iso.refl F)).trans
    (adj.homEquiv ((FP R).obj U) F)).trans (yE R F.obj U), ?_, ?_, ?_⟩
  · intro F G g U t
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    rfl
  · intro F U U' a t
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    have h : (i.app U').hom ≫ T.map a ≫ t =
        (presheafToSheaf J _).map ((FP R).map a) ≫ (i.app U).hom ≫ t := by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      exact (i.hom.naturality a).symm
    rw [h]
    erw [Adjunction.homEquiv_naturality_left]
    exact yE_res R a _
  · intro F U t t'
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [Preadditive.comp_sub, ← yE_sub]
    congr 1

end General

theorem LeafSecRep_of : LeafSecRep := by
  intro B q
  let i : FP (C := B.Etale) (ULift.{1} (ZMod q)) ⋙ presheafToSheaf (EtTop B) _ ≅ OU B q ⋙ H0 B q :=
    (Functor.isoWhiskerLeft (FP (C := B.Etale) (ULift.{1} (ZMod q)) ⋙ presheafToSheaf (EtTop B) _)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0)).symm
  exact general (ULift.{1} (ZMod q)) (EtTop B) (OU B q ⋙ H0 B q) i

end LateralTheory.E.LeafSecRepPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpecGenClosed
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

set_option backward.isDefEq.respectTransparency false in
theorem sep_of_cover {X S : Scheme.{0}} (f : X ⟶ S) (U : X.OpenCover)
    (H : ∀ i j, IsClosedImmersion (pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f
      (by simp) (by simp))) : IsSeparated f := by
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight U U f f)
  rintro ⟨i, j⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv]
  have e : (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv ≫
      (Scheme.Pullback.openCoverOfLeftRight U U f f).pullbackHom (pullback.diagonal f) (i, j) =
      pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp only [Scheme.Cover.pullbackHom, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
    · exact pullbackDiagonalMapIdIso_inv_snd_fst (U.f i) (U.f j) f
    · exact pullbackDiagonalMapIdIso_inv_snd_snd (U.f i) (U.f j) f
  rw [e]; exact H i j

theorem closed_of_pb {X S W P Q : Scheme.{0}} (f : X ⟶ S) (ia : P ⟶ X) (ib : Q ⟶ X) (pa : W ⟶ P)
    (pb : W ⟶ Q) (hp : IsPullback pa pb ia ib) (ga : P ⟶ S) (gb : Q ⟶ S) (hga : ia ≫ f = ga)
    (hgb : ib ≫ f = gb) (w : pa ≫ ga = pb ≫ gb)
    (hc : IsClosedImmersion (pullback.lift pa pb w)) :
    IsClosedImmersion (pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp)) := by
  subst hga hgb
  have e : pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) =
      hp.isoPullback.inv ≫ pullback.lift pa pb w := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.comp_id, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_inv_fst]
    · rw [pullback.lift_snd, Category.comp_id, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_inv_snd]
  rw [e]; infer_instance

def LeafGluePullback : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsPullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)).toRingHom))
    G.iA G.iB

theorem spec_w {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L) (hA : A ≤ D) (hB : B ≤ D) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hA).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω A)) =
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hB).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]; congr 1

def LeafSpecGenClosed : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
  (hA : A ≤ D) (hB : B ≤ D), D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) →
  IsClosedImmersion (pullback.lift _ _ (spec_w A B D hA hB))

theorem dr_le {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L) (hu : u⁻¹ ∈ B) :
    Dr Ω A u ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) :=
  Algebra.adjoin_mono (Set.union_subset_union_right _ (Set.singleton_subset_iff.mpr hu))

theorem LeafGlueSep_of (hP : LeafGluePullback) (hC : LeafSpecGenClosed) :
    LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hD := dr_le A B u h.2.2.1
  apply sep_of_cover G.c0 (LateralTheory.E.LeafGlueIsProperPf.cov G)
  intro i j
  cases i <;> cases j
  · exact closed_of_pb G.c0 G.iB G.iB (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iB) _ _ G.hcB G.hcB (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω B))))))
  · exact closed_of_pb G.c0 G.iB G.iA _ _ (hP Ω L A B u h G).flip _ _ G.hcB G.hcA _
      (hC Ω L B A _ _ _ (by rw [Set.union_comm]; exact hD))
  · exact closed_of_pb G.c0 G.iA G.iB _ _ (hP Ω L A B u h G) _ _ G.hcA G.hcB _ (hC Ω L A B _ _ _ hD)
  · exact closed_of_pb G.c0 G.iA G.iA (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iA) _ _ G.hcA G.hcA (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω A))))))

end LateralTheory.E.GluedCurveChartOverlaps
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTensMonoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensMonoPf
open LateralTheory.E.LeafTwPairExistsPf LateralTheory.E.LeafPairExtPf2

section
variable {R : Type} [CommRing R]

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
  simp [Sec.res]

theorem loc_trans {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let T : ∀ ⦃V : Scheme.{0}⦄ ⦃f : V ⟶ U⦄, S.arrows f → Sieve V := fun V f hf =>
    Classical.choose (hPQ V f (hP V f hf))
  refine ⟨Sieve.bind S.arrows T, (Scheme.etaleTopology.{0}).bind_covering hS
    (fun V f hf => (Classical.choose_spec (hPQ V f (hP V f hf))).1), ?_⟩
  rintro W _ ⟨V, k, f, hf, hk, rfl⟩
  exact (Classical.choose_spec (hPQ V f (hP V f hf))).2 W k hk

theorem eq_zero_of_loc {F : Shv R} {U : Scheme.{0}} (y : Sec F U) (h : Loc U fun _ g => Sec.res g y = 0) : y = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  let e : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have := F.property.hom_ext ⟨S, hS⟩ e 0 (fun I => by
    ext1; apply LinearMap.ext_ring
    have := hP _ I.f I.hf
    simpa [e] using this)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) 1
  simpa [e] using h2

theorem mono_of_loc {F G : Shv R} (f : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map f y = 0 → Loc U fun _ g => Sec.res g y = 0) : Mono f := by
  have : Mono ((sheafToPresheaf _ _).map f) := by
    have hm : ∀ U, Mono (((sheafToPresheaf Scheme.etaleTopology (ModuleCat (ULift.{1, 0} R))).map f).app U) := by
      intro U
      rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
      intro y hy
      exact eq_zero_of_loc y (h U.unop y hy)
    exact NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

theorem lift_res {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) := by
  have : (μ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (μ.lift U w) := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Pair.lift, Tens.res]
    exact (μ.nat g _ _ _ p.2 a b).symm
  exact LinearMap.congr_fun this x

theorem lift_compat {I J K K' : Cx R} (σ : Pair I J K) (ν : Pair I J K') (ι : K ⟶ K')
    (h : ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (ι.f w) (σ.mul U s t w hw a b) = ν.mul U s t w hw a b) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map (ι.f w) (σ.lift U w x) = ν.lift U w x := by
  have : ((ι.f w).hom.app (op U)).hom.comp (σ.lift U w) = ν.lift U w := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Pair.lift]
    exact h U _ _ _ p.2 a b
  exact LinearMap.congr_fun this x
end

def LeafTw0LocSplit : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (n : ℕ) (a : Fin n → Sec ((sgl (tw q 0)).X 0) U),
  Loc U fun V g => ∃ (e : Sec ((sgl (tw q 0)).X 0) V) (c : Fin n → ULift.{1} (ZMod q)),
    (∀ k, Sec.res g (a k) = c k • e) ∧
    (e = 0 ∨ ∃ r : Sec ((res _ (tw q 0)).X 0) V →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q),
      r (Sec.map ((resAug (tw q 0)).f 0) e) = 1)

def LeafPreTensLocInj : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {T : Cx (ZMod q)} (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T),
  τ.IsTensor → ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens (sgl (tw q 0)) (res _ (tw q i)) U w),
  (pre τ (resAug (tw q 0))).lift U w x = 0 → Loc U fun _ g => Tens.res g w x = 0

theorem LeafTensMono_of (hL : LeafPreTensLocInj) : LateralTheory.E.LeafExtTensPf.LeafTensMono := by
  intro q _ i S T σ τ hσ hτ ι hι n
  apply mono_of_loc
  intro U y hy
  have hc := lift_compat σ (pre τ (resAug (tw q 0))) ι (fun U s t w hw a b => hι U s t w hw a b)
  refine loc_trans (hσ.1 U n y) ?_
  rintro V g ⟨x, hx⟩
  have h0 : (pre τ (resAug (tw q 0))).lift V n x = 0 := by
    rw [← hc, hx, ← res_map, hy]; simp
  obtain ⟨S', hS', hP'⟩ := hL q i τ hτ V n x h0
  exact ⟨S', hS', fun W k hk => by
    show Sec.res (k ≫ g) y = 0
    have hk' : Tens.res k n x = 0 := hP' W k hk
    rw [res_comp, ← hx, ← lift_res, hk', map_zero]⟩

end LateralTheory.E.LeafTensMonoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensQIsoPf

def LeafSecInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), Injective F → ∀ U : Scheme.{0},
  Module.Injective (ULift.{1} R) (Sec F U)

def LeafZModInjFlat : Prop := ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M],
  Module.Injective (ULift.{1} (ZMod q)) M → Module.Flat (ULift.{1} (ZMod q)) M

def LeafTensQIsoGen : Prop := ∀ (R : Type) [CommRing R] {I I' J S T : Cx R} (f : I ⟶ I'), QuasiIso f →
  I.IsStrictlyGE 0 → I'.IsStrictlyGE 0 → J.IsStrictlyGE 0 →
  (∀ (n : ℤ) (U : Scheme.{0}), Module.Flat (ULift.{1} R) (Sec (J.X n) U)) →
  ∀ (σ : Pair I J S) (τ : Pair I' J T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map (f.f s) a) b) →
  QuasiIso ι

theorem resAug_quasiIso (R : Type) [CommRing R] (F : Shv R) : QuasiIso (resAug F) := by
  unfold resAug; exact @InjectiveResolution.instQuasiIsoIntι' _ _ _ _ _

theorem res_strictlyGE (R : Type) [CommRing R] (F : Shv R) : (res R F).IsStrictlyGE 0 := by
  unfold res; infer_instance

theorem sgl_strictlyGE (R : Type) [CommRing R] (F : Shv R) : (sgl F).IsStrictlyGE 0 := by
  infer_instance

theorem LeafTensQIso_of (hgen : LeafTensQIsoGen) (hinj : LeafSecInj) (hflat : LeafZModInjFlat) :
    LateralTheory.E.LeafExtTensPf.LeafTensQIso := by
  intro q _ i S T σ τ hσ hτ ι hι
  exact hgen (ZMod q) (resAug (tw q 0)) (resAug_quasiIso _ _) (sgl_strictlyGE _ _) (res_strictlyGE _ _)
    (res_strictlyGE _ _) (fun n U => hflat q _ (hinj _ _ (LateralTheory.E.LeafExtTensPf.res_injective _ _ n) U)) σ τ hσ hτ ι hι

end LateralTheory.E.LeafTensQIsoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwistIsoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTwistIsoPf

theorem leafLoc : LateralTheory.E.LeafTwistPf.LeafLoc :=
  LateralTheory.E.LeafLocPf.LeafLoc_of' (LateralTheory.E.LocSecPfC.LocSec_of LateralTheory.E.ClassSecPf.ClassSec_of)
    (LateralTheory.E.LocSlicePf.LocSlice_of' LateralTheory.E.PullMonoPf.PullMono_of)

theorem leafTwSec : LateralTheory.E.LeafTwistPf.LeafTwSec :=
  LateralTheory.E.LeafTwSecPf.LeafTwSec_of' LateralTheory.E.LeafTwInjPf.LeafTwInj_of LateralTheory.E.LeafTwSecPf.LeafTwSurj_of

end LateralTheory.E.LeafTwistIsoPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RingCommutativity
section
namespace LateralTheory.E.RingCommutativity

theorem goal_of : LateralTheory.E.CupProductRingLaws.LeafRingComm := LateralTheory.Fix.CupProductTensor.ringComm'

end LateralTheory.E.RingCommutativity
end

