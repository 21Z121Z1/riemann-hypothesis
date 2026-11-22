import Development.EtaleCohomology.CohomologicalPurity.Bundle0027
import Development.EtaleCohomology.CohomologicalPurity.OffChaseGeoOf

-- bundled from Development.EtaleCohomology.CohomologicalPurity.FinLeafAW
section
namespace LateralTheory.Fin.LeafAW
theorem etale_purity_aw : LateralTheory.CohomologicalPurity.LeafAW := by
  apply LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafAW := etale_purity_aw
end LateralTheory.Fin.LeafAW
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.IsPullbackOfApp
section
noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem fin_pb {α β γ δ M : Type*} [AddCommMonoid M] (t : α → β) (l : α → γ) (r : β → δ) (b : γ → δ)
    (w : ∀ a, r (t a) = b (l a)) (hpb : ∀ x y, r x = b y → ∃ a, t a = x ∧ l a = y)
    (ht : Function.Injective t) (hr : Function.Injective r) (hb : Function.Injective b)
    (x : β →₀ M) (y : γ →₀ M) (h : Finsupp.mapDomain r x = Finsupp.mapDomain b y) :
    ∃ z : α →₀ M, Finsupp.mapDomain t z = x ∧ Finsupp.mapDomain l z = y := by
  classical
  have hsupp : ∀ s ∈ x.support, s ∈ Set.range t := by
    intro s hs
    have h1 : (Finsupp.mapDomain r x) (r s) ≠ 0 := by
      rw [Finsupp.mapDomain_apply hr]; exact Finsupp.mem_support_iff.1 hs
    rw [h] at h1
    have h2 : r s ∈ (Finsupp.mapDomain b y).support := Finsupp.mem_support_iff.2 h1
    have h3 := Finsupp.mapDomain_support h2
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 h3
    obtain ⟨a, ha, -⟩ := hpb s c hc.symm
    exact ⟨a, ha⟩
  refine ⟨x.comapDomain t ht.injOn, ?_, ?_⟩
  · exact Finsupp.mapDomain_comapDomain t ht x hsupp
  · apply Finsupp.mapDomain_injective hb
    rw [← Finsupp.mapDomain_comp]
    have : b ∘ l = r ∘ t := funext fun a => (w a).symm
    rw [this, Finsupp.mapDomain_comp, Finsupp.mapDomain_comapDomain t ht x hsupp, h]

theorem isPullback_of_app {J C : Type*} [Category J] [Category C] {A B X Y : J ⥤ C}
    {t : A ⟶ B} {l : A ⟶ X} {r : B ⟶ Y} {b : X ⟶ Y} (w : t ≫ r = l ≫ b)
    (h : ∀ j, IsPullback (t.app j) (l.app j) (r.app j) (b.app j)) : IsPullback t l r b :=
  IsPullback.of_isLimit' ⟨w⟩ (evaluationJointlyReflectsLimits _ fun j =>
    (isLimitMapConePullbackConeEquiv ((evaluation J C).obj j) w).symm (h j).isLimit)

theorem modfree_pb (R : Type) [CommRing R] {A' A B' B : Type} (t : A' ⟶ B') (l : A' ⟶ A) (r : B' ⟶ B)
    (b : A ⟶ B) (hpb : IsPullback t l r b) (hr : Function.Injective r) (hb : Function.Injective b) :
    IsPullback ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map t))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map l))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map r))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map b)) := by
  obtain ⟨w, hinj, hex⟩ := (Types.isPullback_iff _ _ _ _).1 hpb
  have ht : Function.Injective t := fun x y h => hinj x y ⟨h, hb (by
    have := ConcreteCategory.congr_hom w x; have h2 := ConcreteCategory.congr_hom w y; simp only [ConcreteCategory.comp_apply, types_comp_apply] at this h2
    rw [← this, ← h2, h])⟩
  have hw : ∀ a : ULift.{1} A', ULift.up (r (t a.down)) = ULift.up (b (l a.down)) := fun a => by
    have := ConcreteCategory.congr_hom w a.down; simp only [ConcreteCategory.comp_apply, types_comp_apply] at this; rw [this]
  have sq : (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map t) ≫
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map r) =
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map l) ≫
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map b) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, w]
  refine IsPullback.of_map (forget (ModuleCat (ULift.{1} R))) sq ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (forget _).map sq, ?_, ?_⟩
  · rintro x y ⟨h1, -⟩
    have hu : Function.Injective (uliftFunctor.{1}.map t) := fun a c h =>
      ULift.ext _ _ (ht (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu h1
  · intro x y h
    exact fin_pb (uliftFunctor.{1}.map t) (uliftFunctor.{1}.map l) (uliftFunctor.{1}.map r)
      (uliftFunctor.{1}.map b) hw
      (fun x y h => by
        obtain ⟨a, ha1, ha2⟩ := hex x.down y.down (congrArg ULift.down h)
        exact ⟨ULift.up a, ULift.ext _ _ ha1, ULift.ext _ _ ha2⟩)
      (fun a c h => ULift.ext _ _ (ht (congrArg ULift.down h)))
      (fun a c h => ULift.ext _ _ (hr (congrArg ULift.down h)))
      (fun a c h => ULift.ext _ _ (hb (congrArg ULift.down h))) x y h

theorem leafFreePb : LeafFreePb := by
  intro R _ A' A B' B t l r b hpb hr hb
  have hP : IsPullback ((freeP R).map t) ((freeP R).map l) ((freeP R).map r) ((freeP R).map b) := by
    refine isPullback_of_app (by rw [← Functor.map_comp, ← Functor.map_comp, hpb.w]) fun U => ?_
    have hrU : Mono (r.app U) := by rw [NatTrans.mono_iff_mono_app] at hr; exact hr U
    have hbU : Mono (b.app U) := by rw [NatTrans.mono_iff_mono_app] at hb; exact hb U
    exact modfree_pb R _ _ _ _ (hpb.map ((evaluation _ _).obj U))
      ((mono_iff_injective _).1 hrU) ((mono_iff_injective _).1 hbU)
  exact hP.map (presheafToSheaf _ _)

theorem LeafCokIso_of : LeafCokIso := leafCokIso_of leafFreePb

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafChiSqProof
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem dblPO (A : Arrow Spc) : IsPushout A.hom A.hom (dbl.inl A) (dbl.inr A) :=
  IsPushout.of_hasPushout A.hom A.hom

theorem mmPO {P' P : Arrow Spc} (φ : P' ⟶ P) : IsPushout P'.hom (P'.hom ≫ φ.right) (ii φ) (jj φ) :=
  IsPushout.of_hasPushout _ _

theorem LeafChiSq_of : LeafChiSq := by
  intro P' P φ
  have s2 : IsPushout ((P'.hom ≫ φ.right) ≫ jj φ) P'.hom (dbl.inr (QQ φ)) (ii φ ≫ dbl.inl (QQ φ)) :=
    IsPushout.paste_horiz (mmPO φ).flip (dblPO (QQ φ)).flip
  have c : IsPushout P'.hom (P'.hom ≫ (chi φ).right) (dbl.inl P' ≫ dbl.map (chi φ)) (dbl.inr (QQ φ)) := by
    have e1 : P'.hom ≫ (chi φ).right = (P'.hom ≫ φ.right) ≫ jj φ := ij_cond φ
    have e2 : dbl.inl P' ≫ dbl.map (chi φ) = ii φ ≫ dbl.inl (QQ φ) := dinl_map (chi φ)
    rw [e1, e2]; exact s2.flip
  exact IsPushout.of_top c (dbl.inr_map (chi φ)) (dblPO P')
end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafHsRelPfSplit
section
noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex Pretriangulated

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem toHom_pull (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n) :
    CohomologyClass.toHom (HK.pull R f F n x) =
      (HomotopyCategory.quotient _ _).map f ≫ CohomologyClass.toHom x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.toHom (CohomologyClass.mk (zcomp (Cocycle.ofHom f) x (zero_add n))) = _
  rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, ← Functor.map_comp]
  congr 1
  ext p : 1
  simp [zcomp, Cocycle.equivHomShift_symm_apply, Cochain.rightShift_v _ n 0 (zero_add n) p p (add_zero p) (p + n) rfl]
  rfl

theorem leafConeSplit : LeafConeSplit := by
  intro R _ K L g r hgr F n
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished g
  let Q := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)
  have z12 : Q.map g ≫ Q.map (mappingCone.inr g) = 0 := comp_distTriang_mor_zero₁₂ _ hT
  let m3 : Q.obj (mappingCone g) ⟶ (Q.obj K)⟦(1 : ℤ)⟧ := (mappingCone.triangleh g).mor₃
  have z31 : m3 ≫ (Q.map g)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have ex2 : ∀ {X} (f : Q.obj L ⟶ X), Q.map g ≫ f = 0 → ∃ w : Q.obj (mappingCone g) ⟶ X,
      f = Q.map (mappingCone.inr g) ≫ w := fun f hf => Triangle.yoneda_exact₂ _ hT f hf
  have ex3 : ∀ {X} (f : Q.obj (mappingCone g) ⟶ X), Q.map (mappingCone.inr g) ≫ f = 0 →
      ∃ w : (Q.obj K)⟦(1 : ℤ)⟧ ⟶ X, f = m3 ≫ w :=
    fun f hf => Triangle.yoneda_exact₃ _ hT f hf
  have hinj : ∀ {M : Cx R} (a b : HK R M F n), CohomologyClass.toHom a = CohomologyClass.toHom b → a = b :=
    fun a b h => (CohomologyClass.toHom_bijective _ _ _).1 h
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · apply hinj
    have h0 : Q.map (mappingCone.inr g) ≫ CohomologyClass.toHom x = 0 := by
      rw [← toHom_pull, hx, map_zero]
    obtain ⟨w, hw⟩ := ex3 _ h0
    rw [hw, map_zero]
    have : w = (Q.map g)⟦(1 : ℤ)⟧' ≫ (Q.map r)⟦(1 : ℤ)⟧' ≫ w := by
      rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hgr, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    rw [this, ← Category.assoc, z31, zero_comp]
  · have h0 : Q.map g ≫ CohomologyClass.toHom y = 0 := by
      rw [← toHom_pull, hy, map_zero]
    obtain ⟨w, hw⟩ := ex2 _ h0
    obtain ⟨x, hx⟩ := (CohomologyClass.toHom_bijective (mappingCone g) _ _).2 w
    refine ⟨x, hinj _ _ ?_⟩
    rw [toHom_pull, hx, hw]
  · rintro ⟨x, rfl⟩
    apply hinj
    rw [toHom_pull, toHom_pull, map_zero, ← Category.assoc, z12, zero_comp]

def LeafDblCok : Prop := ∀ (R : Type) [CommRing R] (P : Arrow Spc), Mono P.hom → ∀ n : ℤ,
  IsIso (cokernel.map _ _ _ _ (sqw (dbl_sq R P) n))

theorem leafDblConeQI_of (hC : LeafConeCok) (hK : LeafDblCok) : LeafDblConeQI := by
  intro R _ P h
  have hi : Mono (dbl.inr P) := ⟨fun a b e => by
    have := congrArg (· ≫ dbl.fold P) e
    simpa [Category.assoc, dbl.inr_fold] using this⟩
  exact hC R _ _ _ _ (dbl_sq R P) (leafChainsMono R _ h) (leafChainsMono R _ hi) (hK R P h)

theorem etale_relative_cohomology_iso_of_cone_and_double_cokernel_isos (hC : LeafConeCok) (hK : LeafDblCok) : LeafHsRel :=
  leafHsRel_of (leafDblConeQI_of hC hK) leafConeSplit

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

section gen
variable {C : Type*} [Category C] {S : Type*} [Ring S] {F G : Cᵒᵖ ⥤ ModuleCat.{1} S} (φ : F ⟶ G) {X : C}

theorem pl_imageSieve_add (s s' : G.obj (op X)) :
    Presheaf.imageSieve φ s ⊓ Presheaf.imageSieve φ s' ≤ Presheaf.imageSieve φ (s + s') := by
  rintro Y i ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
  exact ⟨t + t', by rw [map_add, map_add, ht, ht']⟩

theorem pl_imageSieve_smul (r : S) (s : G.obj (op X)) :
    Presheaf.imageSieve φ s ≤ Presheaf.imageSieve φ (r • s) := by
  rintro Y i ⟨t, ht⟩
  exact ⟨r • t, by rw [map_smul, map_smul, ht]⟩

theorem pl_imageSieve_zero : Presheaf.imageSieve φ (0 : G.obj (op X)) = ⊤ := by
  ext Y i
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩
end gen

theorem pl_hit (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (n : SimplexCategoryᵒᵖ)
    {X Z : Scheme.{0}} (x : (E.obj n).obj (op X)) (h : Z ⟶ X)
    (H : (∃ y, (f.app n).app (op Z) y = (E.obj n).map h.op x) ∨ (∃ y, (g.app n).app (op Z) y = (E.obj n).map h.op x)) :
    Presheaf.imageSieve (biprod.desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)) h := by
  rcases H with ⟨y, hy⟩ | ⟨y, hy⟩
  · refine ⟨NatTrans.app (biprod.inl : (freeP R).obj (U.obj n) ⟶ (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)) _
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)), ?_⟩
    have key := congrArg (fun (k : (freeP R).obj (U.obj n) ⟶ (freeP R).obj (E.obj n)) => ConcreteCategory.hom (NatTrans.app k (op Z))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)))
      (biprod.inl_desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
    refine Eq.trans key ?_
    change (ModuleCat.free _).map _ (ModuleCat.freeMk _) = (ModuleCat.free _).map _ (ModuleCat.freeMk _)
    refine (ModuleCat.free_map_apply _ _).trans (Eq.trans ?_ (ModuleCat.free_map_apply _ _).symm)
    exact congrArg ModuleCat.freeMk (congrArg ULift.up hy)
  · refine ⟨NatTrans.app (biprod.inr : (freeP R).obj (V.obj n) ⟶ (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)) _
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)), ?_⟩
    have key := congrArg (fun (k : (freeP R).obj (V.obj n) ⟶ (freeP R).obj (E.obj n)) => ConcreteCategory.hom (NatTrans.app k (op Z))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} y)))
      (biprod.inr_desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
    refine Eq.trans key ?_
    change (ModuleCat.free _).map _ (ModuleCat.freeMk _) = (ModuleCat.free _).map _ (ModuleCat.freeMk _)
    refine (ModuleCat.free_map_apply _ _).trans (Eq.trans ?_ (ModuleCat.free_map_apply _ _).symm)
    exact congrArg ModuleCat.freeMk (congrArg ULift.up hy)

theorem pl_gen (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hL : LocCov f g) (n : SimplexCategoryᵒᵖ)
    (X : Scheme.{0}) (x : (E.obj n).obj (op X)) :
    Presheaf.imageSieve (biprod.desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))
      (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)) ∈ Scheme.etaleTopology.{0} X := by
  obtain ⟨ι, O, hO, hi⟩ := hL n X x
  have hO' : TopologicalSpace.IsOpenCover O := hO
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_ (X.openCoverOfIsOpenCover O hO').mem_grothendieckTopology
  refine (Sieve.generate_le_iff _ _).2 ?_
  rintro Y _ ⟨i⟩
  exact pl_hit R f g n x (O i).ι (hi i)

theorem LeafPLoc_of : LeafPLoc := by
  intro R _ U V E f g hL n
  constructor
  intro X s
  change (ULift.{1} ((E.obj n).obj (op X)) →₀ ULift.{1} R) at s
  induction s using Finsupp.induction_linear with
  | zero =>
    exact GrothendieckTopology.superset_covering _ (pl_imageSieve_zero _).ge (GrothendieckTopology.top_mem _ _)
  | add a b ha hb =>
    exact GrothendieckTopology.superset_covering _ (pl_imageSieve_add _ _ _)
      (GrothendieckTopology.intersection_covering _ ha hb)
  | single a r =>
    have e : (Finsupp.single a r : ULift.{1} ((E.obj n).obj (op X)) →₀ ULift.{1} R) =
        r • ModuleCat.freeMk (R := ULift.{1} R) a := by
      exact (Finsupp.smul_single_one a r).symm
    have h := GrothendieckTopology.superset_covering _ (pl_imageSieve_smul _ r _) (pl_gen R f g hL n X a.down)
    convert h using 2
    exact congrArg (Presheaf.imageSieve _) e

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafWCechRec
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem psh_limit_ext {J : Type} [SmallCategory J] (F : J ⥤ PSh) (U : Scheme.{0}ᵒᵖ) (w w' : (limit F).obj U)
    (h : ∀ j, (limit.π F j).app U w = (limit.π F j).app U w') : w = w' := by
  apply (mono_iff_injective (limitObjIsoLimitCompEvaluation F U).hom).1 inferInstance
  apply Types.limit_ext
  intro j
  have e := limitObjIsoLimitCompEvaluation_hom_π F j (k := U)
  have e1 := congrArg (fun f => f w) (congrArg ConcreteCategory.hom e)
  have e2 := congrArg (fun f => f w') (congrArg ConcreteCategory.hom e)
  simp only [types_comp_apply] at e1 e2
  rw [e1, e2]; exact h j

theorem wpb_ext {B : PSh} {n : ℕ} {P : PSh} (φ : P ⟶ B) (U : Scheme.{0}ᵒᵖ)
    (w w' : (widePullback B (fun _ : Fin (n + 1) => P) fun _ => φ).obj U)
    (h : ∀ i, NatTrans.app (WidePullback.π (fun _ : Fin (n + 1) => φ) i) U w =
      NatTrans.app (WidePullback.π (fun _ : Fin (n + 1) => φ) i) U w') : w = w' := by
  apply psh_limit_ext _ U
  rintro (_ | i)
  · have e := WidePullback.π_arrow (fun _ : Fin (n + 1) => φ) 0
    have e1 := congrArg (fun f => (f.app U) w) e
    have e2 := congrArg (fun f => (f.app U) w') e
    simp only [NatTrans.comp_app, types_comp_apply] at e1 e2
    change NatTrans.app (WidePullback.base (fun _ : Fin (n + 1) => φ)) U w =
      NatTrans.app (WidePullback.base (fun _ : Fin (n + 1) => φ)) U w'
    rw [← e1, ← e2, h 0]
  · exact h i

theorem leafCechRec : LeafCechRec := by
  intro X P Z φ r g hg hinj hsurj
  let Xa : SimplicialObject.Augmented PSh := { left := X, right := Z, hom := r }
  let G : SimplicialObject.Augmented.toArrow.obj Xa ⟶ Arrow.mk φ :=
    Arrow.homMk g (𝟙 Z) (by change g ≫ φ = r.app _ ≫ 𝟙 Z; exact hg.trans (Category.comp_id _).symm)
  let Ψ := SimplicialObject.equivalenceLeftToRight Xa (Arrow.mk φ) G
  have hπ : ∀ (m : ℕ) (U : Scheme.{0}ᵒᵖ) x (i : Fin (m + 1)),
      NatTrans.app (WidePullback.π (fun _ : Fin (m + 1) => φ) i) U
        (NatTrans.app (Ψ.left.app (op (SimplexCategory.mk m))) U x) = g.app U ((X.map (vtx m i).op).app U x) := by
    intro m U x i
    have e : Ψ.left.app (op (SimplexCategory.mk m)) ≫ WidePullback.π (fun _ : Fin (m + 1) => φ) i =
        X.map (vtx m i).op ≫ g := WidePullback.lift_π _ _ _ _ _
    have := ConcreteCategory.congr_hom (NatTrans.congr_app e U) x
    exact this
  refine ⟨Ψ.left, ?_, ?_⟩
  · have : ∀ n, IsIso (Ψ.left.app n) := by
      intro n
      induction n using Opposite.rec with | op n => ?_
      induction n using SimplexCategory.rec with | _ m => ?_
      have : ∀ U, IsIso ((Ψ.left.app (op (SimplexCategory.mk m))).app U) := by
        intro U
        rw [isIso_iff_bijective]
        constructor
        · intro x x' hx
          apply hinj m U x x'
          intro i
          rw [← hπ, ← hπ]
          exact congrArg _ hx
        · intro w
          obtain ⟨x, hx⟩ := hsurj m U (fun i => NatTrans.app (WidePullback.π (fun _ : Fin (m + 1) => φ) i) U w)
            (NatTrans.app (WidePullback.base (fun _ : Fin (m + 1) => φ)) U w) (fun i => by
              have e := WidePullback.π_arrow (fun _ : Fin (m + 1) => φ) i
              have := ConcreteCategory.congr_hom (NatTrans.congr_app e U) w
              exact this)
          refine ⟨x, wpb_ext φ U _ _ fun i => ?_⟩
          rw [hπ]; exact hx i
      exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ Ψ.left this
  · refine (Ψ.w : _).trans ?_
    change r ≫ (SimplicialObject.const PSh).map (𝟙 Z) = r
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

theorem LeafWCech_of_data (hD : LeafWData) : LeafWCech := LeafWCech_of leafCechRec hD

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.ResLECompIsoOpenInfPreimageHomNaturality
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem ht_transport (q : ℕ) {J : Type} [SmallCategory J] (X Y : J → Spc) (X0 Y0 : Spc) (a : ∀ j, X0 ⟶ X j)
    (b : ∀ j, Y0 ⟶ Y j) (ma : ∀ {j k : J} (_ : j ⟶ k), X k ⟶ X j) (mb : ∀ {j k : J} (_ : j ⟶ k), Y k ⟶ Y j)
    (α : ∀ j, X j ≅ Y j) (α0 : X0 ≅ Y0) (hab : ∀ j, a j ≫ (α j).hom = α0.hom ≫ b j)
    (hm : ∀ j k (f : j ⟶ k), ma f ≫ (α j).hom = (α k).hom ≫ mb f) (n i : ℤ)
    (H : (∀ x : Ht q X0 n i, ∃ j, ∃ y, pull _ (a j) (tw q i) n y = x) ∧
      ∀ j y, pull _ (a j) (tw q i) n y = 0 → ∃ (k : J) (f : j ⟶ k), pull _ (ma f) (tw q i) n y = 0) :
    (∀ x : Ht q Y0 n i, ∃ j, ∃ y, pull _ (b j) (tw q i) n y = x) ∧
      ∀ j y, pull _ (b j) (tw q i) n y = 0 → ∃ (k : J) (f : j ⟶ k), pull _ (mb f) (tw q i) n y = 0 := by
  have hba : ∀ j, b j ≫ (α j).inv = α0.inv ≫ a j := fun j => by
    rw [Iso.comp_inv_eq, Category.assoc, hab, Iso.inv_hom_id_assoc]
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := H.1 (pull _ α0.hom (tw q i) n x)
    refine ⟨j, pull _ (α j).inv (tw q i) n y, ?_⟩
    rw [← pull_comp, hba, pull_comp, hy, ← pull_comp, Iso.inv_hom_id, pull_id]
  · have h0 : pull _ (a j) (tw q i) n (pull _ (α j).hom (tw q i) n y) = 0 := by
      rw [← pull_comp, hab, pull_comp, hy, map_zero]
    obtain ⟨k, f, hk⟩ := H.2 j _ h0
    refine ⟨k, f, ?_⟩
    have : pull _ (mb f) (tw q i) n y = pull _ (α k).inv (tw q i) n (pull _ (ma f) (tw q i) n (pull _ (α j).hom (tw q i) n y)) := by
      rw [← pull_comp, ← pull_comp, Category.assoc, hm, Iso.inv_hom_id_assoc]
    rw [this, hk, map_zero]

theorem oj_sup_eq {A : Type} [CommRing A] {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0})
    (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (I1 I2 : Ideal A) (j : J) :
    oj D s I1 j ⊔ oj D s I2 j = oj D s (I1 ⊔ I2) j := by
  unfold oj; rw [Ideal.map_sup, off_sup]

theorem sq_iso {X' X : Scheme.{0}} (f : X' ⟶ X) (V W : X.Opens) (V' W' : X'.Opens) (e : V = W) (e' : V' = W')
    (h1 : V' ≤ f ⁻¹ᵁ V) (h2 : W' ≤ f ⁻¹ᵁ W) :
    sch.map (f.resLE V V' h1) ≫ sch.map (X.isoOfEq e).hom = sch.map (X'.isoOfEq e').hom ≫ sch.map (f.resLE W W' h2) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [← cancel_mono W.ι]
  simp only [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.resLE_comp_ι, Scheme.isoOfEq_hom_ι_assoc]

theorem ocg_BR : OCG_BR := by
  intro q A B _ _ φ I1 I2 J _ _ D s t hc he n i H
  have T := ht_transport q (fun j => sch.obj (oj D s I1 j ⊔ oj D s I2 j).toScheme)
    (fun j => sch.obj (oj D s (I1 ⊔ I2) j).toScheme)
    (sch.obj (off B (I1.map φ) ⊔ off B (I2.map φ)).toScheme) (sch.obj (off B ((I1 ⊔ I2).map φ)).toScheme)
    (fun j => (conB φ I1 I2 D s t he j).right)
    (fun j => (opnMap (Spec.map (t.app j)) _ _ (oinf_pre φ D s t (I1 ⊔ I2) he j).le).left)
    (fun f => ((sysB I1 I2 D s).map f.op).right)
    (fun f => (opnMap (Spec.map (D.map f)) _ _ (oj_pre D s (I1 ⊔ I2) f).le).left)
    (fun j => sch.mapIso (Scheme.isoOfEq _ (oj_sup_eq D s I1 I2 j)))
    (sch.mapIso (Scheme.isoOfEq _ (by rw [Ideal.map_sup, off_sup])))
    (fun j => sq_iso _ _ _ _ _ _ _ _ _) (fun j k f => sq_iso _ _ _ _ _ _ _ _ _) n i H
  refine ⟨fun x => ?_, fun j h y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := T.1 x
    exact ⟨j, (oinf_pre φ D s t (I1 ⊔ I2) he j).le, y, hy⟩
  · obtain ⟨k, f, hk⟩ := T.2 j y hy
    exact ⟨k, f, (oj_pre D s (I1 ⊔ I2) f).le, hk⟩

theorem sq_le {X' X : Scheme.{0}} (f : X' ⟶ X) (U V : X.Opens) (U' V' : X'.Opens) (hUV : U ≤ V) (hUV' : U' ≤ V')
    (h1 : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V) (h3 : V'.ι ⁻¹ᵁ U' ≤ (f.resLE V V' hV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)) :
    sch.map (f.resLE U U' h1) ≫ sch.map (Scheme.Opens.isoOfLE hUV).inv =
      sch.map (Scheme.Opens.isoOfLE hUV').inv ≫ sch.map ((f.resLE V V' hV).resLE (V.ι ⁻¹ᵁ U) (V'.ι ⁻¹ᵁ U') h3) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [← cancel_mono (Scheme.Opens.ι _), ← cancel_mono (Scheme.Opens.ι _)]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, Scheme.Opens.isoOfLE_inv_ι,
    Scheme.Opens.isoOfLE_inv_ι_assoc]

theorem ocg_BL : OCG_BL := by
  intro q A B _ _ φ I1 I2 J _ _ D s t hc he m i H
  have T := ht_transport q (fun j => sch.obj (oj D s I1 j).toScheme)
    (fun j => ((sysB I1 I2 D s).obj (op j)).left)
    (sch.obj (off B (I1.map φ)).toScheme) (limB φ I1 I2).left
    (fun j => (opnMap (Spec.map (t.app j)) _ _ (oinf_pre φ D s t I1 he j).le).left)
    (fun j => (conB φ I1 I2 D s t he j).left)
    (fun f => (opnMap (Spec.map (D.map f)) _ _ (oj_pre D s I1 f).le).left)
    (fun f => ((sysB I1 I2 D s).map f.op).left)
    (fun j => sch.mapIso (Scheme.Opens.isoOfLE (le_sup_left : oj D s I1 j ≤ oj D s I1 j ⊔ oj D s I2 j)).symm)
    (sch.mapIso (Scheme.Opens.isoOfLE (le_sup_left : off B (I1.map φ) ≤ off B (I1.map φ) ⊔ off B (I2.map φ))).symm)
    (fun j => sq_le _ _ _ _ _ le_sup_left le_sup_left _ _ _) (fun j k f => sq_le _ _ _ _ _ le_sup_left le_sup_left _ _ _) m i
    ⟨fun x => let ⟨j, _, y, hy⟩ := H.1 x; ⟨j, y, hy⟩, fun j y hy => let ⟨k, f, _, hk⟩ := H.2 j _ y hy; ⟨k, f, hk⟩⟩
  exact T

theorem pre_inf {X : Scheme.{0}} (U V : X.Opens) : V.ι ⁻¹ᵁ (U ⊓ V) = V.ι ⁻¹ᵁ U := by
  apply le_antisymm
  · intro x hx; exact hx.1
  · intro x hx
    refine ⟨hx, ?_⟩
    change V.ι x ∈ (V : Set X)
    rw [← Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩

theorem oj_mul_eq {A : Type} [CommRing A] {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0})
    (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (I1 I2 : Ideal A) (j : J) :
    oj D s (I1 * I2) j = oj D s I1 j ⊓ oj D s I2 j := by
  unfold oj; rw [Ideal.map_mul, off_mul]

def isoW {X : Scheme.{0}} (U V W : X.Opens) (e : W = U ⊓ V) : W.toScheme ≅ (V.ι ⁻¹ᵁ U).toScheme :=
  X.isoOfEq e ≪≫ (Scheme.Opens.isoOfLE (inf_le_right : U ⊓ V ≤ V)).symm ≪≫ Scheme.isoOfEq _ (pre_inf U V)

theorem isoW_ι {X : Scheme.{0}} (U V W : X.Opens) (e : W = U ⊓ V) :
    (isoW U V W e).hom ≫ (V.ι ⁻¹ᵁ U).ι ≫ V.ι = W.ι := by
  simp [isoW]

theorem resLE_comp_isoOpenInfPreimage_hom_naturality {X' X : Scheme.{0}} (f : X' ⟶ X) (U V W : X.Opens) (U' V' W' : X'.Opens) (e : W = U ⊓ V)
    (e' : W' = U' ⊓ V') (h1 : W' ≤ f ⁻¹ᵁ W) (hV : V' ≤ f ⁻¹ᵁ V) (h3 : V'.ι ⁻¹ᵁ U' ≤ (f.resLE V V' hV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)) :
    sch.map (f.resLE W W' h1) ≫ sch.map (isoW U V W e).hom =
      sch.map (isoW U' V' W' e').hom ≫ sch.map ((f.resLE V V' hV).resLE (V.ι ⁻¹ᵁ U) (V'.ι ⁻¹ᵁ U') h3) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [← cancel_mono (Scheme.Opens.ι _), ← cancel_mono (Scheme.Opens.ι _)]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, isoW_ι]
  rw [← Category.assoc (isoW U' V' W' e').hom, ← Category.assoc ((isoW U' V' W' e').hom ≫ _), Category.assoc (isoW U' V' W' e').hom, isoW_ι]

theorem ocg_AL : OCG_AL := by
  intro q A B _ _ φ I1 I2 J _ _ D s t hc he m i H
  have T := ht_transport q (fun j => sch.obj (oj D s (I1 * I2) j).toScheme)
    (fun j => ((sysA I1 I2 D s).obj (op j)).left)
    (sch.obj (off B ((I1 * I2).map φ)).toScheme) (limA φ I1 I2).left
    (fun j => (opnMap (Spec.map (t.app j)) _ _ (oinf_pre φ D s t (I1 * I2) he j).le).left)
    (fun j => (conA φ I1 I2 D s t he j).left)
    (fun f => (opnMap (Spec.map (D.map f)) _ _ (oj_pre D s (I1 * I2) f).le).left)
    (fun f => ((sysA I1 I2 D s).map f.op).left)
    (fun j => sch.mapIso (isoW _ _ _ (oj_mul_eq D s I1 I2 j)))
    (sch.mapIso (isoW _ _ _ (by rw [Ideal.map_mul, off_mul])))
    (fun j => resLE_comp_isoOpenInfPreimage_hom_naturality _ _ _ _ _ _ _ _ _ _ _ _) (fun j k f => resLE_comp_isoOpenInfPreimage_hom_naturality _ _ _ _ _ _ _ _ _ _ _ _) m i
    ⟨fun x => let ⟨j, _, y, hy⟩ := H.1 x; ⟨j, y, hy⟩, fun j y hy => let ⟨k, f, _, hk⟩ := H.2 j _ y hy; ⟨k, f, hk⟩⟩
  exact T

theorem OffChaseGeo_full : OffChaseGeo := OffChaseGeo_of ocg_AL ocg_BL ocg_BR

end LateralTheory.CohomologicalPurity
end
end

