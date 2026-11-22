import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0002
import Development.EtaleCohomology.TateTwists.Bundle0004
import Development.EtaleCohomology.TateTwists.Bundle0005

-- bundled from Development.EtaleCohomology.TateTwists.EtaleFreeSheafHomUniversalPropertyHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.FreeHomPf

variable (R : Type) [CommRing R]

noncomputable def desc (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun x : uliftFunctor.{1}.obj (P.obj U) => a U.unop x.down)
  naturality U W g := by
    apply ModuleCat.free_hom_ext
    intro x
    have := ha W.unop U.unop g.unop x.down
    simp only [Sec.res] at this
    simp only [freeP] at *
    simp only [Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map, Functor.whiskeringRight_obj_map,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact this.symm

lemma freePresheaf_map_generator {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) =
      (ModuleCat.freeMk (ULift.up (f.app (op U) x)) : ((freeP R).obj Q).obj (op U)) :=
  ModuleCat.free_map_apply _ _

lemma freePresheaf_obj_map_generator (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) =
      (ModuleCat.freeMk (ULift.up (P.map g.op x)) : ((freeP R).obj P).obj (op V)) :=
  ModuleCat.free_map_apply _ _

lemma gen_eq (P : PSh) (F : Shv R) (φ : (free R).obj P ⟶ F) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map φ (freeGen R P U x) =
      ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ φ.hom).app (op U)).hom
        (ModuleCat.freeMk (ULift.up x)) := rfl

end LateralTheory.EtaleFoundations.FreeHomPf

open LateralTheory.EtaleFoundations.FreeHomPf in
theorem LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  intro R _ P F
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    refine ⟨⟨sheafifyLift Scheme.etaleTopology (desc R P F a ha) F.property⟩, fun U x => ?_⟩
    refine (gen_eq R P F _ U x).trans ?_
    rw [toSheafify_sheafifyLift]
    exact ModuleCat.freeDesc_apply _ _
  · intro φ ψ h
    apply Sheaf.hom_ext
    apply sheafify_hom_ext Scheme.etaleTopology _ _ F.property
    ext U : 2
    apply ModuleCat.free_hom_ext
    intro x
    have := h U.unop x.down
    rw [gen_eq, gen_eq] at this
    exact this
  · intro V U g x
    have hn := (toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op
    calc _ = (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
          (sheafify Scheme.etaleTopology ((freeP R).obj P)).map g.op)).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := rfl
      _ = ((((freeP R).obj P).map g.op ≫
          (toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := by rw [hn]
      _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
            ((((freeP R).obj P).map g.op).hom
              (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U))) := rfl
      _ = _ := by rw [freePresheaf_obj_map_generator]; rfl
  · intro Q f U x
    have hn := congrArg (fun η => η.app (op U))
      (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f))
    calc _ = (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
          (sheafifyMap Scheme.etaleTopology ((freeP R).map f)).app (op U))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := rfl
      _ = ((((freeP R).map f).app (op U) ≫
          (toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := by
              simp only [NatTrans.comp_app] at hn; rw [hn]
      _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom
            ((((freeP R).map f).app (op U)).hom
              (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U))) := rfl
      _ = _ := by rw [freePresheaf_map_generator]; rfl
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε],
    (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m')

def LateralTheory.EtaleFoundations.EtaleSheafInjectiveResolutionProperties : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧
    (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F

def LateralTheory.EtaleFoundations.EtaleTateTwistHomDeterminedByGenerators : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) (M : Shv (ZMod q)) (φ ψ : tw q i ⟶ M),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen i ζ) = Sec.map ψ (twGen i ζ)) → φ = ψ

def LateralTheory.EtaleFoundations.EtaleZModInjectiveSheafFlat : Prop :=
  ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M], FlatS M

def LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective : Prop :=
  ∀ (R : Type) [CommRing R] (M : Shv R) [Injective M] (U : Scheme.{0}), Module.Injective (ULift.{1} R) (Sec M U)

def LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat : Prop :=
  ∀ (q : ℕ) [NeZero q] (N : Type 1) [AddCommGroup N] [Module (ULift.{1} (ZMod q)) N],
    Module.Injective (ULift.{1} (ZMod q)) N → Module.Flat (ULift.{1} (ZMod q)) N

theorem LateralTheory.EtaleFoundations.etale_zmod_injective_sheaf_flat_of_sections_injective_and_zmod_flat (hS : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective)
    (hQ : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat) : LateralTheory.EtaleFoundations.EtaleZModInjectiveSheafFlat := by
  intro q _ M _
  refine ⟨M.obj, 𝟙 _, fun U y => ?_, fun U x hx => ?_, fun U _ => hQ q _ (hS _ M U)⟩
  · exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g y, rfl⟩⟩
  · refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ?_⟩
    have hx0 : x = 0 := hx
    subst hx0
    exact map_zero _

namespace LateralTheory.EtaleFoundations.TwResExt

variable {C : Type*} [Category C] [Abelian C]

attribute [local instance] HasDerivedCategory.standard in
theorem qh_iso {S T : CochainComplex C ℤ} (ε : S ⟶ T) [QuasiIso ε] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ε)) := by
  have : IsIso (DerivedCategory.Q.map ε) := inferInstance
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) ε).2 this

attribute [local instance] HasDerivedCategory.standard in
theorem kinj_lift {S T I : CochainComplex C ℤ} [I.IsKInjective] (ε : S ⟶ T) [QuasiIso ε] (a : S ⟶ I) :
    ∃ m : T ⟶ I, Nonempty (Homotopy (ε ≫ m) a) := by
  have := qh_iso ε
  set qt := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) I).2
    (inv (DerivedCategory.Qh.map (qt.map ε)) ≫ DerivedCategory.Qh.map (qt.map a))
  obtain ⟨m, rfl⟩ := qt.map_surjective g
  refine ⟨m, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj S) I).1
  rw [Functor.map_comp, Functor.map_comp]
  erw [hg]
  exact IsIso.hom_inv_id_assoc _ _

attribute [local instance] HasDerivedCategory.standard in
theorem kinj_uniq {S T I : CochainComplex C ℤ} [I.IsKInjective] (ε : S ⟶ T) [QuasiIso ε] (m m' : T ⟶ I)
    (h : ε ≫ m = ε ≫ m') : Nonempty (Homotopy m m') := by
  have := qh_iso ε
  set qt := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) I).1
  rw [← cancel_epi (DerivedCategory.Qh.map (qt.map ε)), ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp, h]

theorem homotopy_single_eq {F : C} {I : CochainComplex C ℤ} [I.IsStrictlyGE 0]
    (f g : (CochainComplex.singleFunctor C 0).obj F ⟶ I) (h : Homotopy f g) : f = g := by
  have hz : ∀ i j, h.hom i j = 0 := by
    intro i j
    by_cases hi : i = 0
    · subst hi
      by_cases hr : (ComplexShape.up ℤ).Rel j 0
      · have hj : j < 0 := by simp [ComplexShape.up_Rel] at hr; omega
        exact (I.isZero_of_isStrictlyGE 0 j hj).eq_of_tgt _ _
      · exact h.zero _ _ hr
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _
  ext n
  rw [h.comm n]
  have : h.hom = 0 := by funext i j; exact hz i j
  simp [this]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem ext_hom_pf : LateralTheory.EtaleFoundations.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle := by
  intro R _ F T I _ _ ε _
  refine ⟨fun a => ?_, fun m m' h => kinj_uniq ε m m' h⟩
  obtain ⟨m, ⟨hm⟩⟩ := kinj_lift ε a
  exact ⟨m, homotopy_single_eq _ _ hm⟩

theorem res_pf : LateralTheory.EtaleFoundations.EtaleSheafInjectiveResolutionProperties := by
  intro R _ F
  refine ⟨?_, fun n => ?_, ?_, ?_, rfl⟩
  · exact inferInstanceAs ((injectiveResolution F).cochainComplex.IsKInjective)
  · exact inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  · exact inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  · exact inferInstanceAs (QuasiIso (injectiveResolution F).ι')

end LateralTheory.EtaleFoundations.TwResExt

theorem LateralTheory.EtaleFoundations.TwResExt.linearMap_comp_eq_on_smul_of_eq {S A B C : Type*} [Ring S] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module S A] [Module S B] [Module S C] (t : A →ₗ[S] B) (f g : B →ₗ[S] C) (x : A) (b : S)
    (h : f (t x) = g (t x)) : f (t (b • x)) = g (t (b • x)) := by
  rw [map_smul, map_smul, map_smul, h]

theorem LateralTheory.EtaleFoundations.TwResExt.twuniq_pf : LateralTheory.EtaleFoundations.EtaleTateTwistHomDeterminedByGenerators := by
  intro q _ i M φ ψ h
  apply Sheaf.hom_ext
  refine CategoryTheory.sheafify_hom_ext (J := Scheme.etaleTopology) (P := Scheme.Γ ⋙ twF q i) φ.hom ψ.hom M.cond ?_
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ b => ?_)))
  have h1 := h (unop U) ζ
  change (φ.hom.app U).hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i) |>.app U).hom
      (Submodule.Quotient.mk (Finsupp.single ζ b))) = (ψ.hom.app U).hom ((toSheafify Scheme.etaleTopology
      (Scheme.Γ ⋙ twF q i) |>.app U).hom (Submodule.Quotient.mk (Finsupp.single ζ b)))
  rw [← Finsupp.smul_single_one, Submodule.Quotient.mk_smul]
  exact LateralTheory.EtaleFoundations.TwResExt.linearMap_comp_eq_on_smul_of_eq _ _ _ _ b h1

open LateralTheory.EtaleFoundations.TwResExt in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_resolution_universal_of_injective_sections_and_zmod_f (hS : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective) (hQ : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat) :
    LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := by
  have hF := LateralTheory.EtaleFoundations.etale_zmod_injective_sheaf_flat_of_sections_injective_and_zmod_flat hS hQ
  have hE := ext_hom_pf
  have hR := res_pf
  have hU := twuniq_pf
  intro q _ i
  obtain ⟨hK, hInj, hGE, hQ, hι⟩ := hR (ZMod q) (tw q i)
  have hgen : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map ((resAug (tw q i)).f 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) = resGen i ζ := by
    intro U ζ
    rw [← sec_map_comp, hι]
    rfl
  refine ⟨⟨hGE, resAug _, hQ, hgen⟩, fun t => ?_, ?_⟩
  · haveI := hInj t
    exact hF q _
  · intro T e hT
    obtain ⟨_, ε, hε, he⟩ := hT
    have := hε
    have := hK
    have := hGE
    obtain ⟨hex, huniq⟩ := hE (ZMod q) (tw q i) T (res _ (tw q i)) ε
    refine ⟨?_, ?_⟩
    · obtain ⟨m, hm⟩ := hex (resAug _)
      refine ⟨m, fun U ζ => ?_⟩
      rw [← he, ← sec_map_comp, ← HomologicalComplex.comp_f, hm]
      exact hgen U ζ
    · intro u u' h
      apply huniq
      apply HomologicalComplex.from_single_hom_ext
      have hφ : sglι (tw q i) ≫ (ε ≫ u).f 0 = sglι (tw q i) ≫ (ε ≫ u').f 0 := by
        apply hU q i
        intro U ζ
        simp only [sec_map_comp, HomologicalComplex.comp_f]
        have h1 := h U ζ
        rw [← he] at h1
        exact h1
      have hiso : IsIso (sglι (tw q i)) := Iso.isIso_inv _
      exact (cancel_epi (sglι (tw q i))).1 hφ
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleKummerClassSpecificationOfExistenceNaturali
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def kum_exists : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def kum_nat : Prop :=
  ∀ (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)

def kum_add : Prop :=
  ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0

theorem kum_spec_of_exists (he : kum_exists) (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ)
    (hq : IsUnit (q : Γ(X, ⊤))) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1, CohomologyClass.mk γ = kum q u ∧
      (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v) := by
  obtain ⟨γ, h1, h2⟩ := he q X u hq
  unfold kum
  exact pick_spec (P := fun c => ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      CohomologyClass.mk γ = c ∧ (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    ⟨CohomologyClass.mk γ, γ, rfl, h1, h2⟩

theorem etale_kummer_class_specification_of_existence_naturality_additivity (he : kum_exists) (hn : kum_nat) (ha : kum_add) : EtaleKummerClassExplicitCocycle := by
  intro q _
  exact ⟨fun X u hq => kum_spec_of_exists he q X u hq, fun f u hq => hn q f u hq, fun u v hq => ha q u v hq⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosureProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.LocBasicPf

theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

theorem loc_and (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT,
    fun V g hg => ⟨hSP V g hg.1, hTQ V g hg.2⟩⟩

theorem loc_pull (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : Loc U P) : Loc W fun V g => P V (g ≫ k) := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S.pullback k, (Scheme.etaleTopology).pullback_stable k hS,
    fun V g hg => hSP V (g ≫ k) hg⟩

theorem loc_trans (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U (fun V g => Loc V fun W k => P W (k ≫ g))) : Loc U P := by
  obtain ⟨S, hS, hSP⟩ := h
  let R : Sieve U :=
    { arrows := fun W h => ∀ (W' : Scheme.{0}) (k : W' ⟶ W), P W' (k ≫ h)
      downward_closed := by
        intro Y Z f hf g W' k
        simpa [Category.assoc] using hf W' (k ≫ g) }
  refine ⟨R, ?_, fun W h hR => by simpa using hR W (𝟙 W)⟩
  refine (Scheme.etaleTopology).transitive hS R ?_
  intro Y f hf
  obtain ⟨T, hT, hTP⟩ := hSP Y f hf
  refine (Scheme.etaleTopology).superset_covering ?_ hT
  intro Z k hk W' k'
  have := hTP W' (k' ≫ k) (T.downward_closed hk k')
  simpa [Category.assoc] using this

theorem loc_finset (U : Scheme.{0}) (ι : Type) (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) (s : Finset ι) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_top U _ (fun V g i hi => by simp at hi)
  | insert a s ha ih =>
    refine loc_mono U _ _ (loc_and U _ _ (h a) ih) ?_
    intro V g hg i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hg.1
    · exact hg.2 i hi

theorem loc_finite (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g := by
  haveI := Fintype.ofFinite ι
  exact loc_mono U _ _ (loc_finset U ι P h Finset.univ) (fun V g hg i => hg i (Finset.mem_univ i))

theorem loc_empty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun V g hg => hg.elim⟩

end LateralTheory.EtaleFoundations.LocBasicPf

open LateralTheory.EtaleFoundations.LocBasicPf in
theorem LateralTheory.EtaleFoundations.etale_local_property_basic_closure_properties : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure :=
  ⟨loc_top, loc_mono, loc_and, loc_pull, loc_trans, fun U ι _ P h => loc_finite U ι P h,
    fun U _ P => loc_empty U P⟩
end

-- bundled from Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

def leaf_acyc : Prop := ∀ (N k : ℕ) (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 →
  ∃ b : Pr N →₀ ℤ, Pr.Deg (k + 2) b ∧ Pr.d N b = c

def leaf_dbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c)

def leaf_bdbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.bd (Pr.bd c) = 0

def leaf_aw : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N)

def leaf_wa : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N)

lemma deg_zero {N k : ℕ} : Pr.Deg k (0 : Pr N →₀ ℤ) := by
  intro z hz; simp at hz

lemma deg_sub {N k : ℕ} {a b : Pr N →₀ ℤ} (ha : Pr.Deg k a) (hb : Pr.Deg k b) : Pr.Deg k (a - b) := by
  intro z hz
  rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
  · exact ha z h
  · exact hb z h

lemma deg_bd {N k : ℕ} {c : Pr N →₀ ℤ} (hc : Pr.Deg k c) : Pr.Deg k (Pr.bd c) := by
  intro z hz
  unfold Pr.bd at hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have h2 := Finsupp.support_smul hi
  unfold Pr.push at h2
  simp only [Finsupp.lmapDomain_apply] at h2
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h2)
  exact hc w hw

lemma deg_aw (N : ℕ) : Pr.Deg N (Pr.aw N) := by
  intro z hz
  unfold Pr.aw at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (p : ℕ) + (N - p) = N
  omega

lemma deg_wa (N : ℕ) : Pr.Deg N (Pr.wa N) := by
  intro z hz
  unfold Pr.wa at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (N - p) + (p : ℕ) = N
  omega

lemma bd_sub {N : ℕ} (a b : Pr N →₀ ℤ) : Pr.bd (a - b) = Pr.bd a - Pr.bd b := by
  unfold Pr.bd
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, smul_sub]

lemma bd_zero {N : ℕ} : Pr.bd (0 : Pr N →₀ ℤ) = 0 := by
  simpa using bd_sub (0 : Pr N →₀ ℤ) 0

lemma aw_zero_eq : Pr.aw 0 = Pr.wa 0 := by
  simp [Pr.aw, Pr.wa]

def Good (N : ℕ) (x : Pr N →₀ ℤ) : Prop :=
  Pr.Deg (N + 1) x ∧ Pr.bd (Pr.aw N - Pr.wa N - Pr.d N x) = 0

lemma step (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd) (hAW : leaf_aw) (hWA : leaf_wa)
    (N : ℕ) (x : Pr N →₀ ℤ) (hx : Good N x) :
    ∃ y : Pr (N + 1) →₀ ℤ, Good (N + 1) y ∧ Pr.d (N + 1) y + Pr.bd x = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  set c := Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd x with hcdef
  have hcdeg : Pr.Deg (N + 1) c := deg_sub (deg_sub (deg_aw _) (deg_wa _)) (deg_bd hx.1)
  have hcyc : Pr.d (N + 1) c = 0 := by
    rw [hcdef, map_sub, map_sub, hAW, hWA, hD, ← bd_sub, ← bd_sub]
    exact hx.2
  obtain ⟨b, hbdeg, hb⟩ := hA (N + 1) N c hcdeg hcyc
  refine ⟨b, ⟨hbdeg, ?_⟩, ?_⟩
  · have : Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.d (N + 1) b = Pr.bd x := by
      rw [hb, hcdef]; abel
    rw [this]; exact hB N x
  · rw [hb, hcdef]; abel

lemma good_zero : Good 0 0 := by
  refine ⟨deg_zero, ?_⟩
  rw [aw_zero_eq, map_zero, sub_self, sub_zero, bd_zero]

end LateralTheory.EtaleFoundations.SteenPf

open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd)
    (hAW : leaf_aw) (hWA : leaf_wa) : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := by
  classical
  let seq : ∀ N, {x : Pr N →₀ ℤ // Good N x} := fun N =>
    Nat.rec (motive := fun N => {x : Pr N →₀ ℤ // Good N x}) ⟨0, good_zero⟩
      (fun N x => ⟨Classical.choose (step hA hD hB hAW hWA N x.1 x.2),
        (Classical.choose_spec (step hA hD hB hAW hWA N x.1 x.2)).1⟩) N
  refine ⟨fun N => (seq N).1, fun N => (seq N).2.1, ?_, fun N => ?_⟩
  · show Pr.d 0 0 = _
    rw [map_zero, aw_zero_eq, sub_self]
  · exact (Classical.choose_spec (step hA hD hB hAW hWA N (seq N).1 (seq N).2)).2
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleShortComplexExactIffLocallySurjectiveOnKern
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleShortComplexExactIffLocallySurjectiveOnKernel : Prop :=
  ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔
    ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b

def EtaleTensorComplexLocallyExactOfFlatBounded : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (T.sc w).X₂ U), Sec.map (T.sc w).g y = 0 →
      Loc U fun V g => ∃ x : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f x = Sec.res g y

theorem etale_tensor_complex_acyclic_of_locally_exact_flat (hE : EtaleShortComplexExactIffLocallySurjectiveOnKernel) (hS : EtaleTensorComplexLocallyExactOfFlatBounded) :
    EtaleTensorAcyclicOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC w
  have hCl := fun s => (hE R (C.sc s)).1 (hC s)
  exact (hE R (T.sc w)).2 (hS R a b τ hτ hJ hCl w)

end LateralTheory.EtaleFoundations
end

