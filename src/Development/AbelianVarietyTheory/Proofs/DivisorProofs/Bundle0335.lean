import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.CechRep

variable {V W : Scheme.{0}} (f : V ⟶ W)

def IsPow (n : ℕ) (Z : Scheme.{0}) (p : Fin (n + 1) → (Z ⟶ V)) : Prop :=
  (∀ i, p i ≫ f = p 0 ≫ f) ∧ ∀ (U : Scheme.{0}) (y : Fin (n + 1) → (U ⟶ V)), (∀ i, y i ≫ f = y 0 ≫ f) →
    ∃! g : U ⟶ Z, ∀ i, g ≫ p i = y i

theorem exists_pow (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    (hf : P f) (n : ℕ) : ∃ (Z : Scheme.{0}) (p : Fin (n + 1) → (Z ⟶ V)), IsPow f n Z p ∧ P (p 0) := by
  induction n with
  | zero =>
    refine ⟨V, fun _ => 𝟙 V, ⟨fun _ => rfl, fun U y _ => ⟨y 0, fun i => ?_, fun g hg => ?_⟩⟩, P.id_mem V⟩
    · rw [Fin.fin_one_eq_zero i]; simp
    · simpa using hg 0
  | succ n ih =>
    obtain ⟨Z, p, ⟨hc, hu⟩, hP⟩ := ih
    let q : Fin (n + 2) → (pullback (p 0 ≫ f) f ⟶ V) :=
      Fin.snoc (α := fun _ => pullback (p 0 ≫ f) f ⟶ V) (fun j => pullback.fst _ _ ≫ p j) (pullback.snd _ _)
    have qc : ∀ j : Fin (n + 1), q j.castSucc = pullback.fst _ _ ≫ p j := fun j => by simp [q]
    have ql : q (Fin.last _) = pullback.snd _ _ := by simp [q]
    have hz : (Fin.castSucc (0 : Fin (n + 1)) : Fin (n + 2)) = 0 := rfl
    have q0 : q 0 = pullback.fst _ _ ≫ p 0 := qc 0
    refine ⟨pullback (p 0 ≫ f) f, q, ⟨fun i => ?_, fun U y hy => ?_⟩, ?_⟩
    · rw [q0]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [ql, ← pullback.condition, Category.assoc]
      · rw [qc, Category.assoc, Category.assoc, hc j]
    · have h' : ∀ j : Fin (n + 1), y j.castSucc ≫ f = y (Fin.castSucc 0) ≫ f := fun j => by
        rw [hy, hz, hy]
      obtain ⟨g0, hg0, hg0u⟩ := hu U (fun j => y j.castSucc) h'
      have hw : g0 ≫ p 0 ≫ f = y (Fin.last _) ≫ f := by
        rw [← Category.assoc, hg0 0, hy (Fin.last _), hz]
      refine ⟨pullback.lift g0 (y (Fin.last _)) hw, fun i => ?_, fun g hg => ?_⟩
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [ql, pullback.lift_snd]
        · rw [qc, pullback.lift_fst_assoc, hg0 j]
      · apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine hg0u _ (fun j => ?_)
          rw [Category.assoc, ← qc, hg]
        · rw [pullback.lift_snd, ← ql, hg]
    · rw [q0]
      exact P.comp_mem _ _ (P.pullback_fst _ _ hf) hP

end GlobalTheory.EtC.CechRep

namespace GlobalTheory.EtC.CechRep

variable {V W : Scheme.{0}} (f : V ⟶ W)

noncomputable section

def isLimitPow {n : ℕ} {Z : Scheme.{0}} {p : Fin (n + 1) → (Z ⟶ V)} (h : IsPow f n Z p) :
    IsLimit (WidePullbackShape.mkCone (F := WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f))
      (p 0 ≫ f) p (fun j => h.1 j)) := by
  have hs : ∀ s : Cone (WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f)),
      ∀ j, s.π.app (some j) ≫ f = s.π.app (some 0) ≫ f := fun s j => by
    have a : s.π.app (some j) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term j)
    have b : s.π.app (some 0) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term 0)
    rw [a, b]
  refine IsLimit.mk (fun s => (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose) (fun s j => ?_)
    (fun s m hm => ?_)
  · have hl := (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose_spec
    cases j with
    | none =>
      have b : s.π.app (some 0) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term 0)
      change (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose ≫ (p 0 ≫ f) = s.π.app none
      rw [← Category.assoc, hl 0]
      exact b
    | some j =>
      exact hl j
  · exact (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).unique (fun j => hm (some j))
      (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose_spec

end

end GlobalTheory.EtC.CechRep

theorem GlobalTheory.EtC.cech_level_representable : ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative] (V W : Scheme.{0}) (f : V ⟶ W), P f → ∀ k : SimplexCategoryᵒᵖ, ∃ (Z : Scheme.{0}) (π : Z ⟶ V) (e : yoneda.obj Z ≅ (cech f).obj k), P π ∧ e.hom ≫ (cechAug f).app k = yoneda.map (π ≫ f) := by
  intro P _ _ V W f hf k
  obtain ⟨Z, p, h, hP⟩ := GlobalTheory.EtC.CechRep.exists_pow f P hf k.unop.len
  have hY := isLimitOfPreserves yoneda (GlobalTheory.EtC.CechRep.isLimitPow f h)
  let D := WidePullbackShape.wideCospan (yoneda.obj W) (fun _ : Fin (k.unop.len + 1) => yoneda.obj V)
    (fun _ => yoneda.map f)
  let iso : WidePullbackShape.wideCospan W (fun _ : Fin (k.unop.len + 1) => V) (fun _ => f) ⋙ yoneda ≅ D :=
    WidePullbackShape.diagramIsoWideCospan _
  have hL := (IsLimit.postcomposeHomEquiv iso _).symm hY
  refine ⟨Z, p 0, IsLimit.conePointUniqueUpToIso hL (limit.isLimit D), hP, ?_⟩
  have := IsLimit.conePointUniqueUpToIso_hom_comp hL (limit.isLimit D) none
  change _ ≫ limit.π D none = _
  refine this.trans ?_
  change yoneda.map (p 0 ≫ f) ≫ iso.hom.app none = _
  simp [iso, WidePullbackShape.diagramIsoWideCospan]
  first | exact Category.comp_id _ | rfl | (erw [eqToHom_refl, Category.comp_id])
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsIsoOfFreeIso
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.isIso_chains_map_of_isIso_free (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E')
    (h : ∀ n, IsIso ((free R).map (f.app n))) : IsIso ((chains R).map f) := by
  have hw : IsIso (((SimplicialObject.whiskering _ _).obj (free R)).map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    exact h n
  have : IsIso ((chainsN R).map f) := by
    unfold chainsN
    rw [Functor.comp_map]
    infer_instance
  unfold chains
  rw [Functor.comp_map]
  infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsQuasiIsoOfSections
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem chains_quasiIso_of_sections : ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E'), (∀ U : Scheme.{0}, QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map (((SimplicialObject.whiskering _ _).obj ((evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R))).map f))) → QuasiIso ((chains R).map f) := by
  intro R _ E E' f hf
  let g := ((SimplicialObject.whiskering _ _).obj (freeP R)).map f
  let φ := (AlgebraicTopology.alternatingFaceMapComplex _).map g
  have hφ : QuasiIso φ := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro t
    have e := Arrow.isoOfNatIso (eqToIso (AlgebraicTopology.map_alternatingFaceMapComplex ((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj t))) (Arrow.mk g)
    exact (quasiIso_iff_of_arrow_mk_iso _ _ e).2 (hf t.unop)
  have e := Arrow.isoOfNatIso (eqToIso (AlgebraicTopology.map_alternatingFaceMapComplex (presheafToSheaf (Scheme.etaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))))) (Arrow.mk g)
  have h2 : QuasiIso ((chainsN R).map f) := by
    have : QuasiIso (((presheafToSheaf (Scheme.etaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex _).map φ) := inferInstance
    exact (quasiIso_iff_of_arrow_mk_iso _ _ e).1 this
  change QuasiIso (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat)
  infer_instance

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicProperti
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ResBasic

variable {C : Type*} [Category C] [Abelian C] {X : C} (I : InjectiveResolution X)

theorem aug_comm : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
    (I.cochainComplexXIso 0 0 rfl).hom =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X).inv ≫ I.ι.f 0 := by
  rw [InjectiveResolution.ι'_f_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  erw [Category.id_comp]

end GlobalTheory.EtC.ResBasic

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private theorem injectiveResolution_cochainComplex_exact_and_exactAt {C : Type*} [Category C] [Abelian C]
    {X : C} (I : InjectiveResolution X) :
    (∀ n : ℤ, Injective (I.cochainComplex.X n)) ∧
    (∀ n : ℤ, n < 0 → IsZero (I.cochainComplex.X n)) ∧
    Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ∧
    (∃ w : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
        I.cochainComplex.d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧
    (∀ n : ℤ, n ≠ 0 → I.cochainComplex.ExactAt n) := by
  refine ⟨fun n => inferInstance, fun n hn => ?_, ?_, ?_, fun n hn => ?_⟩
  · exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
      have h : (ComplexShape.embeddingUpNat.f i : ℤ) = i := rfl
      omega)
  · rw [I.ι'_f_zero]
    erw [Iso.inv_hom_id_assoc]
    exact mono_comp (I.ι.f 0) _
  · have hw : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
        I.cochainComplex.d 0 1 = 0 := by
      rw [I.ι'_f_zero, I.cochainComplex_d 0 1 0 1 rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      erw [Category.assoc, Iso.inv_hom_id_assoc, I.ι_f_zero_comp_complex_d_assoc, zero_comp]
      rfl
    refine ⟨hw, ?_⟩
    refine (ShortComplex.exact_iff_of_iso ?_).mpr I.exact₀
    refine ShortComplex.isoMk (Iso.refl _) (I.cochainComplexXIso 0 0 rfl)
      (I.cochainComplexXIso 1 1 rfl) ?_ ?_
    · dsimp only
      rw [I.ι'_f_zero]
      erw [Category.id_comp, Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, Iso.inv_hom_id_assoc]
    · dsimp only
      rw [I.cochainComplex_d 0 1 0 1 rfl rfl]
      simp
  · exact (quasiIsoAt_iff_exactAt I.ι' n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn)).mp
      inferInstance

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in

theorem _root_.GlobalTheory.EtC.res_basic : ∀ (R : Type) [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R), (∀ n : ℤ, Injective ((_root_.GlobalTheory.EtC.res R F).X n)) ∧
    (∀ n : ℤ, n < 0 → IsZero ((_root_.GlobalTheory.EtC.res R F).X n)) ∧ Mono (_root_.GlobalTheory.EtC.resι R F) ∧
    (∃ w : _root_.GlobalTheory.EtC.resι R F ≫ (_root_.GlobalTheory.EtC.res R F).d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧
    (∀ n : ℤ, n ≠ 0 → (_root_.GlobalTheory.EtC.res R F).ExactAt n) ∧
    ∀ (E : _root_.GlobalTheory.EtC.Spc) (n : ℤ), 0 < n → IsZero (((_root_.GlobalTheory.EtC.chains R).obj E).X n) := by
  intro R _ F
  unfold _root_.GlobalTheory.EtC.res _root_.GlobalTheory.EtC.resι _root_.GlobalTheory.EtC.chains
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := injectiveResolution_cochainComplex_exact_and_exactAt (injectiveResolution F)
  refine ⟨h₁, h₂, h₃, h₄, h₅, fun E n hn => ?_⟩
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
    have h : (ComplexShape.embeddingDownNat.f i : ℤ) = -i := rfl
    omega)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ResBasic

variable (R : Type) [CommRing R]

def resHom {F G : Shv R} (φ : F ⟶ G) :
    InjectiveResolution.Hom (injectiveResolution F) (injectiveResolution G) φ :=
  ⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
    congrArg (fun f => HomologicalComplex.Hom.f f 0)
      (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F))⟩

theorem mono_ι_f_zero (F : Shv R) : Mono ((injectiveResolution F).ι.f 0) :=
  mono_of_isLimit_fork (injectiveResolution F).isLimitKernelFork

theorem mono_resι (F : Shv R) : Mono (resι R F) := by
  have h1 := mono_ι_f_zero R F
  change Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0)
  rw [InjectiveResolution.ι'_f_zero, Iso.inv_hom_id_assoc]
  exact @mono_comp _ _ _ _ _ _ h1 _ inferInstance

theorem sglι_comp_single_map {F G : Shv R} (φ : F ⟶ G) :
    sglι F ≫ ((CochainComplex.singleFunctor (Shv R) 0).map φ).f 0 = φ ≫ sglι G := by
  have := HomologicalComplex.single_map_f_self (V := Shv R) (ComplexShape.up ℤ) 0 φ
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map φ).f 0 = _
  rw [this, Iso.inv_hom_id_assoc]
  rfl

theorem res_basic : ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧
    (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F ∧ Mono (resι R F) ∧
    resι R F ≫ (res R F).d 0 1 = 0 ∧ ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G ∧
      resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  intro R _ F
  have hinj : ∀ n, Injective ((res R F).X n) := fun n =>
    inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  have hge : (res R F).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  have hq : QuasiIso (resAug F) := inferInstanceAs (QuasiIso (injectiveResolution F).ι')
  have hι : ∀ F : Shv R, sglι F ≫ (resAug F).f 0 = resι R F := fun _ => rfl
  have hcomm : ∀ (G : Shv R) (φ : F ⟶ G),
      resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G :=
    fun G φ => (resHom R φ).ι'_comp_hom'
  refine ⟨CochainComplex.isKInjective_of_injective _ 0, hinj, hge, hq, hι F, mono_resι R F, ?_,
    fun G φ => ⟨hcomm G φ, ?_⟩⟩
  · rw [← hι F, Category.assoc, (resAug F).comm 0 1]
    simp
  · rw [← hι F, Category.assoc, ← HomologicalComplex.comp_f, hcomm G φ, HomologicalComplex.comp_f, ← hι G,
      ← Category.assoc, sglι_comp_single_map, Category.assoc]

end GlobalTheory.EtC.ResBasic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCompHomComplexAssocOnCohomologyClasses
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem cocycle_comp_assoc_classes : ∀ (R : Type) [CommRing R] {K L M N : Cx R} {a b c ab bc abc : ℤ} (h1 : a + b = ab) (h2 : b + c = bc) (h3 : ab + c = abc) (h4 : a + bc = abc), (∀ (x : Cocycle K L a) (y : Cocycle L M b) (z : CohomologyClass M N c), cpre (zcomp x y h1) N c abc h3 z = cpre x N bc abc h4 (cpre y N c bc h2 z)) ∧ (∀ (x : Cocycle K L a) (y : CohomologyClass L M b) (z : Cocycle M N c), cpost K z ab abc h3 (cpre x M b ab h1 y) = cpre x N bc abc h4 (cpost L z b bc h2 y)) ∧ (∀ (x : CohomologyClass K L a) (y : Cocycle L M b) (z : Cocycle M N c), cpost K (zcomp y z h2) a abc h4 x = cpost K z ab abc h3 (cpost K y a ab h1 x)) := by
  intro R _ K L M N a b c ab bc abc h1 h2 h3 h4
  have hA : a + b + c = abc := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro x y z
    obtain ⟨z, rfl⟩ := z.mk_surjective
    rw [cpre_mk, cpre_mk, cpre_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA))
  · intro x y z
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [cpre_mk, cpost_mk, cpost_mk, cpre_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA))
  · intro x y z
    obtain ⟨x, rfl⟩ := x.mk_surjective
    rw [cpost_mk, cpost_mk, cpost_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleEqChainMapShiftCompatClasses
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ShiftCocycle

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

def rsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) :
    CohomologyClass K L n →+ CohomologyClass K (L⟦a⟧) n' :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K (L⟦a⟧) n').comp (Cocycle.rightShiftAddEquiv n a n' h).toAddMonoidHom)
    (by
      rintro α ⟨m, hm, β, hβ⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        CohomologyClass.mkAddMonoidHom_apply]
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m + -a, by omega, a.negOnePow • β.rightShift a (m + -a) (by omega), ?_⟩
      rw [δ_units_smul, Cochain.δ_rightShift β a (m + -a) n' (by omega) n h, smul_smul,
        Int.units_mul_self, one_smul]
      simp [hβ])

def runsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) :
    CohomologyClass K (L⟦a⟧) n' →+ CohomologyClass K L n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K L n).comp (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).symm.toAddMonoidHom)
    (by
      rintro α ⟨m, hm, β, hβ⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        CohomologyClass.mkAddMonoidHom_apply]
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m + a, by omega, a.negOnePow • β.rightUnshift (m + a) (by omega), ?_⟩
      rw [δ_units_smul, Cochain.δ_rightUnshift β (m + a) (by omega) n n' h, smul_smul,
        Int.units_mul_self, one_smul]
      simp [hβ])

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC.ShiftCocycle
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem runsh_rsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) (x) :
    runsh K L a n n' h (rsh K L a n n' h x) = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  show CohomologyClass.mk _ = _
  congr 1
  exact (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).symm_apply_apply x

theorem rsh_runsh (K L : CochainComplex C ℤ) (a n n' : ℤ) (h : n' + a = n) (x) :
    rsh K L a n n' h (runsh K L a n n' h x) = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  show CohomologyClass.mk _ = _
  congr 1
  exact (Cocycle.rightShiftAddEquiv (K := K) (L := L) n a n' h).apply_symm_apply x

def sgn (d : ℤ) : ℤˣ := ((-d) * 0 + ((-d) * (-d - 1)) / 2).negOnePow

theorem zcomp_rightShift_homOf_leftShift {K L M : CochainComplex C ℤ} (d n : ℤ) (α : Cocycle K L (n - d)) (ψ : Cocycle L M d) :
    zcomp (sgn d • α.rightShift (-d) n (by omega)) (Cocycle.ofHom (Cocycle.homOf (ψ.leftShift (-d) 0 (by omega))))
      (add_zero n) = zcomp α ψ (by omega) := by
  ext p q hpq
  have e1 : (↑(Cocycle.ofHom (Cocycle.homOf (ψ.leftShift (-d) 0 (by omega)))) : Cochain (L⟦-d⟧) M 0) =
      (ψ.leftShift (-d) 0 (by omega) : Cochain _ _ 0) := by
    rw [Cocycle.ofHom_coe, Cocycle.cochain_ofHom_homOf_eq_coe]
  simp only [zcomp, Cocycle.mk_coe, e1, Cocycle.coe_units_smul, Cochain.units_smul_comp,
    Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q),
    Cochain.comp_v _ _ (show n - d + d = n by omega) p (p + (n - d)) q rfl (by omega),
    Cochain.units_smul_v, Cocycle.rightShift_coe, Cocycle.leftShift_coe,
    Cochain.rightShift_v _ (-d) n (show n + -d = n - d by omega) p q hpq (p + (n - d)) rfl,
    Cochain.leftShift_v _ (-d) 0 (show d + -d = 0 by omega) q q (add_zero q) (p + (n - d)) (by omega)]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul, Category.assoc, Iso.inv_hom_id_assoc]
  have hs : sgn d * (-d * 0 + -d * (-d - 1) / 2).negOnePow = 1 := Int.units_mul_self _
  rw [hs, one_smul]

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC.ShiftCocycle
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem smul_mk {K L : CochainComplex C ℤ} {n : ℤ} (u : ℤˣ) (z : Cocycle K L n) :
    CohomologyClass.mk (u • z) = u • CohomologyClass.mk z := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul, Units.neg_smul, one_smul, CohomologyClass.mk_neg]

theorem smul_smul_self {G : Type*} [AddCommGroup G] (u : ℤˣ) (x : G) : u • u • x = x := by
  rw [smul_smul, Int.units_mul_self, one_smul]

theorem map_units_smul' {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (u : ℤˣ) (x : G) :
    f (u • x) = u • f x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul, Units.neg_smul, one_smul, map_neg]

end GlobalTheory.EtC.ShiftCocycle

namespace GlobalTheory.EtC
open ShiftCocycle in

theorem cocycle_as_chainMap_of_shift : ∀ (R : Type) [CommRing R] (L C : Cx R) (d : ℤ) (ψ : Cocycle L C d),
    ∃ (L' : Cx R) (g : L' ⟶ C), (∀ m, L.IsStrictlyGE m → L'.IsStrictlyGE (m + d)) ∧
      ((∀ n, CategoryTheory.Injective (L.X n)) → ∀ n, CategoryTheory.Injective (L'.X n)) ∧
      ∀ (K : Cx R) (n : ℤ), ∃ e : CohomologyClass K L (n - d) ≃ CohomologyClass K L' n,
        ∀ a, cpush K g n (e a) = cpost K ψ (n - d) n (by omega) a := by
  intro R _ L C d ψ
  refine ⟨L⟦-d⟧, Cocycle.homOf (ψ.leftShift (-d) 0 (by omega)), ?_, ?_, ?_⟩
  · intro m hm
    exact L.isStrictlyGE_shift m (-d) (m + d) (by omega)
  · intro hI n
    exact Injective.of_iso (L.shiftFunctorObjXIso (-d) n (n + -d) rfl).symm (hI _)
  · intro K n
    refine ⟨{ toFun := fun x => sgn d • rsh K L (-d) (n - d) n (by omega) x
              invFun := fun y => sgn d • runsh K L (-d) (n - d) n (by omega) y
              left_inv := fun x => by
                simp only [map_units_smul', runsh_rsh, smul_smul_self]
              right_inv := fun y => by
                simp only [map_units_smul', rsh_runsh, smul_smul_self] }, ?_⟩
    intro a
    obtain ⟨α, rfl⟩ := a.mk_surjective
    show cpush K _ n (sgn d • CohomologyClass.mk (α.rightShift (-d) n (by omega))) = _
    rw [← smul_mk, cpost_mk]
    exact congrArg CohomologyClass.mk (zcomp_rightShift_homOf_leftShift d n α ψ)

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAddPPowMulLt
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.LemY

theorem digits (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p]
    [PerfectRing S p] [Field K] [Algebra S K] [IsFractionRing S K] [CharP K p] [PerfectRing K p] (d : ℕ)
    (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Y : Fin d → WittVector p K)
    (hY : ∀ i, WittVector.frobenius (Y i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y) i) (n : ℕ) :
    ∃ (B Z : Fin d → WittVector p S) (Yn : Fin d → WittVector p K),
      (∀ i, Y i = WittVector.map (algebraMap S K) (B i) + (p : WittVector p K) ^ n * Yn i) ∧
      ∀ i, WittVector.frobenius (Yn i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Yn) i
        + WittVector.map (algebraMap S K) (Z i) := by
  induction n with
  | zero =>
    exact ⟨0, 0, Y, fun i => by simp, fun i => by simpa using hY i⟩
  | succ n ih =>
    obtain ⟨B, Z, Yn, h1, h2⟩ := ih
    obtain ⟨B', Z', Y', h3, h4⟩ := GlobalTheory.LemY.step p S K d U Z Yn h2
    refine ⟨fun i => B i + (p : WittVector p S) ^ n * B' i, Z', Y', fun i => ?_, h4⟩
    rw [h1 i, h3 i, map_add, map_mul, map_pow, map_natCast]
    ring

theorem coeff_add_p_pow_mul_lt (p : ℕ) [Fact p.Prime] {K : Type} [CommRing K] [CharP K p] (n k : ℕ)
    (hk : k < n) (a y : WittVector p K) : (a + (p : WittVector p K) ^ n * y).coeff k = a.coeff k := by
  have h := (WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero (x := a + (p : WittVector p K) ^ n * y)
    (y := a) (n := n)).2 (fun m hm => by
      rw [add_sub_cancel_left, mul_comm]
      exact WittVector.mul_pow_charP_coeff_zero _ hm)
  exact h k hk

theorem range_of_frobenius_eq : ∀ (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p] [PerfectRing S p] [Field K] [Algebra S K] [IsFractionRing S K] [CharP K p] [PerfectRing K p] (d : ℕ) (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Y : Fin d → WittVector p K), (∀ i, WittVector.frobenius (Y i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y) i) → ∀ i, Y i ∈ (WittVector.map (p := p) (algebraMap S K)).range := by
  intro p _ S K _ _ _ _ _ _ _ _ _ _ d U Y hY i
  have hc : ∀ k, ∃ s : S, algebraMap S K s = (Y i).coeff k := by
    intro k
    obtain ⟨B, Z, Yn, h1, -⟩ := digits p S K d U Y hY (k + 1)
    refine ⟨(B i).coeff k, ?_⟩
    rw [h1 i, coeff_add_p_pow_mul_lt p (k + 1) k (Nat.lt_succ_self k), WittVector.map_coeff]
  choose c hc using hc
  refine ⟨WittVector.mk p c, ?_⟩
  ext k
  rw [WittVector.map_coeff]
  exact hc k

end GlobalTheory.LemY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjOfCharpolyEqOfCharpolySeparableStatement
section
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_of_charpoly_eq_of_charpoly_separable : ∀ (R : Type) [Field R] (m : ℕ) (N U : Matrix (Fin m) (Fin m) R), N.charpoly = U.charpoly → N.charpoly.Separable → ∃ P : GL (Fin m) R, N * P.val = P.val * U := by
  first | exact @GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable | exact GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable | (intros; apply GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjOfCharpolyLocalStatement
section
open Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_of_charpoly_eq_of_separable_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y Y' : Matrix (Fin n) (Fin n) R), Y.charpoly = Y'.charpoly → Y.charpoly.Separable → ∃ g : GL (Fin n) R, Y' = (g⁻¹ : GL (Fin n) R).val * Y * g.val := by
  first | exact @GlobalTheory.ConjLocal.conj_of_charpoly_local | exact GlobalTheory.ConjLocal.conj_of_charpoly_local | (intros; apply GlobalTheory.ConjLocal.conj_of_charpoly_local <;> assumption)
end

