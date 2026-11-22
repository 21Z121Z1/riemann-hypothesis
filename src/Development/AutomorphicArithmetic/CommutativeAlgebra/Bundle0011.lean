import Mathlib
import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.EtaleCohomology.EtaleSheaves.Bundle0004
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.A6supp
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0010
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0005

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CechNerveRepresentableDisjoint
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem comp_ap {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C) (x : A) :
    (u ≫ v) x = v (u x) := by simp

private def lvlIso {V Y : Scheme.{0}} (f : V ⟶ Y) (p : ℕ) :
    yoneda.obj (widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f)) ≅
      widePullback (yoneda.obj Y) (fun _ : Fin (p + 1) => yoneda.obj V)
        (fun _ => yoneda.map f) :=
  preservesLimitIso yoneda (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f)) ≪≫
    HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan
      (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f) ⋙ yoneda))

private theorem lvlIso_base {V Y : Scheme.{0}} (f : V ⟶ Y) (p : ℕ) :
    (lvlIso f p).hom ≫ WidePullback.base (fun _ : Fin (p + 1) => yoneda.map f) =
      yoneda.map (WidePullback.base (fun _ : Fin (p + 1) => f)) := by
  have h := HasLimit.isoOfNatIso_hom_π (WidePullbackShape.diagramIsoWideCospan
    (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f) ⋙ yoneda)) none
  have h2 := preservesLimitIso_hom_π yoneda
    (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f)) none
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (h.trans (Category.comp_id _))).trans h2)

private theorem piece_open {V Y : Scheme.{0}} (f : V ⟶ Y) (p : ℕ) {T : Fin (p + 1) → Scheme.{0}}
    (j : ∀ i, T i ⟶ V) (h1 : ∀ i, IsOpenImmersion (j i)) (h2 : ∀ i, IsOpenImmersion (j i ≫ f))
    (O : (widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f)).Opens)
    (hO : (O : Set _) = ⋂ i, (WidePullback.π (fun _ : Fin (p + 1) => f) i) ⁻¹' Set.range (j i)) :
    IsOpenImmersion (O.ι ≫ WidePullback.base (fun _ : Fin (p + 1) => f)) := by
  have hb : ∀ (i : Fin (p + 1)) z, (WidePullback.base (fun _ : Fin (p + 1) => f)) z =
      f ((WidePullback.π (fun _ : Fin (p + 1) => f) i) z) := by
    intro i z
    rw [← comp_ap, WidePullback.π_arrow]
  have hxO : ∀ (x : O.toScheme) (i : Fin (p + 1)),
      (WidePullback.π (fun _ : Fin (p + 1) => f) i) (O.ι x) ∈ Set.range (j i) := by
    intro x i
    have hx : O.ι x ∈ (O : Set _) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
    rw [hO] at hx
    exact Set.mem_iInter.1 hx i
  let W : Y.Opens := ⟨⋂ i, Set.range (j i ≫ f),
    isOpen_iInter_of_finite fun i => (j i ≫ f).opensRange.2⟩
  have hW : ∀ (w : W.toScheme) (i : Fin (p + 1)), W.ι w ∈ Set.range (j i ≫ f) := by
    intro w i
    have hw : W.ι w ∈ (W : Set _) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨w, rfl⟩
    exact Set.mem_iInter.1 hw i
  have hr : Set.range (O.ι ≫ WidePullback.base (fun _ : Fin (p + 1) => f)) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine Set.mem_iInter.2 fun i => ?_
    obtain ⟨y, hy⟩ := hxO x i
    exact ⟨y, by rw [comp_ap, hy, comp_ap, hb i]⟩
  let r := IsOpenImmersion.lift W.ι _ hr
  have hl : ∀ i, Set.range W.ι ⊆ Set.range (j i ≫ f) := by
    rintro i _ ⟨w, rfl⟩
    exact hW w i
  let l : ∀ i, W.toScheme ⟶ T i := fun i => IsOpenImmersion.lift (j i ≫ f) W.ι (hl i)
  have hlf : ∀ i, l i ≫ j i ≫ f = W.ι := fun i => IsOpenImmersion.lift_fac _ _ _
  let L : W.toScheme ⟶ widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f) :=
    WidePullback.lift W.ι (fun i => l i ≫ j i) (fun i => by simpa using hlf i)
  have hLπ : ∀ i, L ≫ WidePullback.π (fun _ : Fin (p + 1) => f) i = l i ≫ j i :=
    fun i => WidePullback.lift_π _ _ _ _ i
  have hLb : L ≫ WidePullback.base (fun _ : Fin (p + 1) => f) = W.ι :=
    WidePullback.lift_base _ _ _ _
  have hs : Set.range L ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι, hO]
    rintro _ ⟨w, rfl⟩
    refine Set.mem_iInter.2 fun i => ?_
    refine ⟨l i w, ?_⟩
    have := congr($(hLπ i) w)
    rw [comp_ap, comp_ap] at this
    exact this.symm
  let s := IsOpenImmersion.lift O.ι L hs
  have hsO : s ≫ O.ι = L := IsOpenImmersion.lift_fac _ _ _
  have hrW : r ≫ W.ι = O.ι ≫ WidePullback.base (fun _ : Fin (p + 1) => f) :=
    IsOpenImmersion.lift_fac _ _ _
  have hm : ∀ i, Set.range (O.ι ≫ WidePullback.π (fun _ : Fin (p + 1) => f) i) ⊆
      Set.range (j i) := by
    rintro i _ ⟨x, rfl⟩
    rw [comp_ap]
    exact hxO x i
  have hrs : r ≫ s = 𝟙 _ := by
    rw [← cancel_mono O.ι, Category.assoc, hsO, Category.id_comp]
    apply WidePullback.hom_ext
    · intro i
      rw [Category.assoc, hLπ, ← IsOpenImmersion.lift_fac (j i) _ (hm i), ← Category.assoc]
      congr 1
      rw [← cancel_mono (j i ≫ f), Category.assoc, hlf, hrW,
        IsOpenImmersion.lift_fac_assoc, Category.assoc, WidePullback.π_arrow]
    · rw [Category.assoc, hLb, hrW]
  have hsr : s ≫ r = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, hrW, ← Category.assoc, hsO, hLb, Category.id_comp]
  have : IsIso r := ⟨s, hrs, hsr⟩
  rw [← hrW]
  infer_instance

theorem UpperTheory.cech_nerve_representable_disjoint :
    ∀ {V Y : Scheme.{0}} (f : V ⟶ Y), (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ V), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : V, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ f)) → ∀ p : ℕ, ∃ (Z : Scheme.{0}) (g : Z ⟶ Y) (e : yoneda.obj Z ≅ (cech f).obj (op (SimplexCategory.mk p))),
      e.hom ≫ (cechAug f).app (op (SimplexCategory.mk p)) = yoneda.map g ∧ (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ Z), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : Z, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ g)) := by
  rintro V Y f ⟨ι, O, j, hj, hd, hc, hf⟩ p
  let π := fun i => WidePullback.π (fun _ : Fin (p + 1) => f) i
  let U : (Fin (p + 1) → ι) → (widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f)).Opens :=
    fun a => ⟨⋂ i, (π i) ⁻¹' Set.range (j (a i)),
      isOpen_iInter_of_finite fun i => (j (a i)).opensRange.2.preimage (π i).continuous⟩
  have hU : ∀ a z, z ∈ Set.range (U a).ι ↔ ∀ i, (π i) z ∈ Set.range (j (a i)) := by
    intro a z
    rw [Scheme.Opens.range_ι]
    exact Set.mem_iInter
  refine ⟨widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f),
    WidePullback.base (fun _ : Fin (p + 1) => f), lvlIso f p,
    lvlIso_base f p, Fin (p + 1) → ι, fun a => (U a).toScheme, fun a => (U a).ι,
    fun a => inferInstance, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hab
    refine Set.disjoint_left.2 fun z hza hzb => ?_
    exact Set.disjoint_left.1 (hd _ _ hi) ((hU a z).1 hza i) ((hU b z).1 hzb i)
  · intro z
    choose a ha using fun i => hc ((π i) z)
    exact ⟨a, (hU a z).2 ha⟩
  · intro a
    exact piece_open f p (fun i => j (a i)) (fun i => hj _) (fun i => hf _) (U a) rfl

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CechNerveRestrictOpen
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

private theorem cechNerve_level_isPullback {C : Type*} [Category C] {a b : Arrow C}
    [∀ n : ℕ, HasWidePullback a.right (fun _ : Fin (n + 1) => a.left) fun _ => a.hom]
    [∀ n : ℕ, HasWidePullback b.right (fun _ : Fin (n + 1) => b.left) fun _ => b.hom]
    (F : a ⟶ b) (h : IsPullback F.left a.hom b.hom F.right) (n : SimplexCategoryᵒᵖ) :
    IsPullback ((Arrow.mapCechNerve F).app n) (WidePullback.base _) (WidePullback.base _) F.right := by
  have hc : (Arrow.mapCechNerve F).app n ≫ WidePullback.base _ = WidePullback.base _ ≫ F.right := by
    simp [Arrow.mapCechNerve]
  refine ⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk hc
    (fun s => WidePullback.lift s.snd
      (fun i => h.lift (s.fst ≫ WidePullback.π _ i) s.snd (by
        simp only [Category.assoc, WidePullback.π_arrow]
        simpa using s.condition)) (by simp)) ?_ ?_ ?_⟩⟩
  · intro s
    refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · simp [Arrow.mapCechNerve]
    · simpa [Arrow.mapCechNerve] using s.condition.symm
  · intro s
    simp
  · intro s m h1 h2
    refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · simp only [WidePullback.lift_π]
      refine h.hom_ext ?_ ?_
      · rw [h.lift_fst, ← h1]
        simp [Arrow.mapCechNerve]
      · rw [h.lift_snd, ← h2, Category.assoc]
        simp
    · simpa using h2

private theorem comp_eq_of_comp_inv {C : Type*} [Category C] {A B D E : C} {i : A ⟶ B} {ψ : B ⟶ D} {t : A ⟶ E}
    (e : E ≅ D) (h : i ≫ ψ ≫ e.inv = t) : i ≫ ψ = t ≫ e.hom := by
  rw [← h]
  simp

theorem UpperTheory.cech_nerve_restrict_open :
    ∀ {V Y : Scheme.{0}} (f : V ⟶ Y) (W : Y.Opens), ∃ ψ : cech (f ∣_ W) ⟶ cech f, ψ ≫ cechAug f = cechAug (f ∣_ W) ≫ sch.map W.ι ∧
      ∀ (p : ℕ) (Z : Scheme.{0}) (g : Z ⟶ Y) (e : yoneda.obj Z ≅ (cech f).obj (op (SimplexCategory.mk p))), e.hom ≫ (cechAug f).app (op (SimplexCategory.mk p)) = yoneda.map g →
        ∃ e' : yoneda.obj (g ⁻¹ᵁ W : Scheme.{0}) ≅ (cech (f ∣_ W)).obj (op (SimplexCategory.mk p)), e'.hom ≫ ψ.app (op (SimplexCategory.mk p)) = yoneda.map (g ⁻¹ᵁ W).ι ≫ e.hom := by
  intro V Y f W
  have hP0 := isPullback_morphismRestrict f W
  have hP1 := hP0.map yoneda
  let F : Arrow.mk (yoneda.map (f ∣_ W)) ⟶ Arrow.mk (yoneda.map f) :=
    Arrow.homMk (yoneda.map (f ⁻¹ᵁ W).ι) (yoneda.map W.ι) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, morphismRestrict_ι])
  have hF : IsPullback F.left (Arrow.mk (yoneda.map (f ∣_ W))).hom (Arrow.mk (yoneda.map f)).hom F.right :=
    hP1.flip
  have hL := cechNerve_level_isPullback F hF
  refine ⟨Arrow.mapCechNerve F, ?_, ?_⟩
  · exact NatTrans.ext (funext fun n => (hL n).w)
  · intro p Z g e he
    have hA := ((isPullback_morphismRestrict g W).map yoneda).flip
    have hL' : IsPullback ((Arrow.mapCechNerve F).app (op (SimplexCategory.mk p)) ≫ e.inv)
        ((cechAug (f ∣_ W)).app (op (SimplexCategory.mk p))) (yoneda.map g) (yoneda.map W.ι) :=
      IsPullback.of_iso (hL (op (SimplexCategory.mk p))) (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
        (by simp) (by simp; rfl) (by
          simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
          exact (Iso.eq_inv_comp e).2 he) (by simp; rfl)
    refine ⟨hA.isoIsPullback _ _ hL', ?_⟩
    have h1 := hA.isoIsPullback_hom_fst _ _ hL'
    exact comp_eq_of_comp_inv e h1

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyContinuityFilteredColimitRings
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace UpperTheory.DirectSumIndependence

private abbrev P (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    Ht q (sch.obj (Spec A)) n i →+ Ht q (sch.obj (Spec B)) n i :=
  pull _ (sch.map (Spec.map f)) (tw q i) n

private theorem pullback_comp₂ (q : ℕ) (i n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (x : Ht q (sch.obj (Spec A)) n i) : P q i n (f ≫ g) x = P q i n g (P q i n f x) := by
  show pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n x = _
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

private theorem isUnit_of_hom {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (h : IsUnit (q : A)) :
    IsUnit (q : B) := by
  simpa using h.map f.hom

private theorem chase (b1 : B1) (q : ℕ) (i : ℤ) {J : Type} [SmallCategory J] [IsFiltered J]
    (D D' : J ⥤ CommRingCat.{0}) (α : D ⟶ D') (c : Cocone D) (hc : IsColimit c)
    (c' : Cocone D') (hc' : IsColimit c') (g : c.pt ⟶ c'.pt)
    (hg : ∀ j, c.ι.app j ≫ g = α.app j ≫ c'.ι.app j)
    (hα : ∀ j, RE q i (α.app j)) (hq : ∀ j, IsUnit (q : D.obj j)) : RE q i g := by
  intro n
  change Function.Bijective (P q i n g)
  have hqc : IsUnit (q : c.pt) := by
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    exact isUnit_of_hom (c.ι.app j) (hq j)
  have hqc' : IsUnit (q : c'.pt) := isUnit_of_hom g hqc
  have hqD' : ∀ j, IsUnit (q : D'.obj j) := fun j => isUnit_of_hom (α.app j) (hq j)
  have comm : ∀ j y, P q i n g (P q i n (c.ι.app j) y) =
      P q i n (c'.ι.app j) (P q i n (α.app j) y) := by
    intro j y
    rw [← pullback_comp₂, ← pullback_comp₂, hg]
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, hy⟩ := (b1 q D c hc n i).1 x hqc
    change P q i n (c.ι.app j) y = x at hy
    subst hy
    rw [comm] at hx
    obtain ⟨k, f, hf⟩ := (b1 q D' c' hc' n i).2 j (P q i n (α.app j) y) (hqD' j) hx
    change P q i n (D'.map f) (P q i n (α.app j) y) = 0 at hf
    rw [← pullback_comp₂, ← α.naturality f, pullback_comp₂] at hf
    have h0 : P q i n (D.map f) y = 0 := by
      apply (hα k n).1
      show P q i n (α.app k) (P q i n (D.map f) y) = P q i n (α.app k) 0
      rw [hf, map_zero]
    rw [← c.w f, pullback_comp₂, h0, map_zero]
  · intro z
    obtain ⟨j, y', hy'⟩ := (b1 q D' c' hc' n i).1 z hqc'
    change P q i n (c'.ι.app j) y' = z at hy'
    obtain ⟨y, rfl⟩ := (hα j n).2 y'
    refine ⟨P q i n (c.ι.app j) y, ?_⟩
    rw [← hy']
    exact comm j y

variable {J : Type} [SmallCategory J] {A Y : CommRingCat.{0}} (φ : A ⟶ Y) (D : J ⥤ CommRingCat.{0})
  (t : ∀ j, A ⟶ D.obj j) (ht : ∀ {j k : J} (f : j ⟶ k), t j ≫ D.map f = t k)

private def Dp : J ⥤ CommRingCat.{0} where
  obj j := pushout φ (t j)
  map {j k} f := pushout.desc (pushout.inl φ (t k)) (D.map f ≫ pushout.inr φ (t k)) (by
    rw [← Category.assoc, ht f, pushout.condition])
  map_id j := by
    apply pushout.hom_ext <;> simp
  map_comp {j k l} f g := by
    apply pushout.hom_ext
    · erw [pushout.inl_desc, ← Category.assoc, pushout.inl_desc, pushout.inl_desc]
    · erw [pushout.inr_desc, ← Category.assoc, pushout.inr_desc, Category.assoc, pushout.inr_desc,
        D.map_comp, Category.assoc]

private theorem inl_Dp {j k : J} (f : j ⟶ k) :
    pushout.inl φ (t j) ≫ (Dp φ D t ht).map f = pushout.inl φ (t k) :=
  pushout.inl_desc _ _ _

private theorem inr_Dp {j k : J} (f : j ⟶ k) :
    pushout.inr φ (t j) ≫ (Dp φ D t ht).map f = D.map f ≫ pushout.inr φ (t k) :=
  pushout.inr_desc _ _ _

private def toDp : D ⟶ Dp φ D t ht where
  app j := pushout.inr φ (t j)
  naturality j k f := (inr_Dp φ D t ht f).symm

variable (c : Cocone D) (hc : IsColimit c) {Y' : CommRingCat.{0}} (w : Y ⟶ Y') (φ' : c.pt ⟶ Y')
  (cc : A ⟶ c.pt) (hcc : ∀ j, t j ≫ c.ι.app j = cc) (hp : IsPushout φ cc w φ')

private def cocDp : Cocone (Dp φ D t ht) where
  pt := Y'
  ι :=
    { app j := pushout.desc w (c.ι.app j ≫ φ') (by
        rw [← Category.assoc, hcc, hp.w])
      naturality j k f := by
        refine pushout.hom_ext ?_ ?_
        · erw [← Category.assoc, inl_Dp, pushout.inl_desc, ← Category.assoc, pushout.inl_desc,
            Category.comp_id]
        · erw [← Category.assoc, inr_Dp, Category.assoc, pushout.inr_desc, ← Category.assoc, c.w f,
            ← Category.assoc, pushout.inr_desc, Category.comp_id] }

private theorem inl_coc (j : J) :
    pushout.inl φ (t j) ≫ (cocDp φ D t ht c w φ' cc hcc hp).ι.app j = w :=
  pushout.inl_desc _ _ _

private theorem inr_coc (j : J) :
    pushout.inr φ (t j) ≫ (cocDp φ D t ht c w φ' cc hcc hp).ι.app j = c.ι.app j ≫ φ' :=
  pushout.inr_desc _ _ _

private theorem inl_indep [IsFiltered J] (e : Cocone (Dp φ D t ht)) (j k : J) :
    pushout.inl φ (t j) ≫ e.ι.app j = pushout.inl φ (t k) ≫ e.ι.app k := by
  rw [← e.w (IsFiltered.leftToMax j k), ← e.w (IsFiltered.rightToMax j k)]
  erw [← Category.assoc, inl_Dp, ← Category.assoc, inl_Dp]

private def resCoc (e : Cocone (Dp φ D t ht)) : Cocone D where
  pt := e.pt
  ι :=
    { app j := pushout.inr φ (t j) ≫ e.ι.app j
      naturality j k f := by
        erw [Category.comp_id, ← e.w f, ← Category.assoc, ← Category.assoc, inr_Dp]
        simp
        rfl }

private def isColDp [IsFiltered J] : IsColimit (cocDp φ D t ht c w φ' cc hcc hp) :=
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  { desc := fun e => hp.desc (pushout.inl φ (t j0) ≫ e.ι.app j0)
      (hc.desc (resCoc φ D t ht e)) (by
        erw [← hcc j0, Category.assoc, hc.fac, ← Category.assoc, pushout.condition, Category.assoc])
    fac := fun e j => by
      refine pushout.hom_ext ?_ ?_
      · erw [← Category.assoc, inl_coc, hp.inl_desc]
        exact inl_indep φ D t ht e j0 j
      · erw [← Category.assoc, inr_coc, Category.assoc, hp.inr_desc, hc.fac]
        rfl
    uniq := fun e m hm => by
      refine hp.hom_ext ?_ ?_
      · erw [hp.inl_desc, ← hm j0, ← Category.assoc, inl_coc]
        rfl
      · erw [hp.inr_desc]
        refine hc.hom_ext fun j => ?_
        erw [hc.fac, ← Category.assoc, ← inr_coc φ D t ht c w φ' cc hcc hp j, Category.assoc, hm j]
        rfl }

end UpperTheory.DirectSumIndependence

theorem UpperTheory.cohomology_continuity_filtered_colimit_rings :
    LateralTheory.E.t_E3Cut.Limit := by
  intro hyp q _ i A Y φ hq hEt C c hc Y' w φ' hp
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hc
  have ht : ∀ {j k : J} (f : j ⟶ k), t.app j ≫ D.map f = t.app k := by
    intro j k f
    rw [← t.naturality f]
    simp
  exact UpperTheory.DirectSumIndependence.chase hyp.2.2.2.2.2.2.1 q i D
    (UpperTheory.DirectSumIndependence.Dp φ D (fun j => t.app j) ht)
    (UpperTheory.DirectSumIndependence.toDp φ D (fun j => t.app j) ht) (Cocone.mk C s) hs
    (UpperTheory.DirectSumIndependence.cocDp φ D (fun j => t.app j) ht (Cocone.mk C s) w φ' c
      (fun j => (hts j).2) hp)
    (UpperTheory.DirectSumIndependence.isColDp φ D (fun j => t.app j) ht (Cocone.mk C s) hs w φ' c
      (fun j => (hts j).2) hp)
    φ'
    (fun j => (UpperTheory.DirectSumIndependence.inr_coc φ D (fun j => t.app j) ht (Cocone.mk C s) w φ' c
      (fun j => (hts j).2) hp j).symm)
    (fun j => hEt _ _ (hts j).1 _ _ _ (IsPushout.of_hasPushout _ _))
    (fun j => UpperTheory.DirectSumIndependence.isUnit_of_hom (t.app j) hq)
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectivityOfDisjointOpenCover
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

theorem UpperTheory.connectivity_of_disjoint_open_cover :
    LeafProd → A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {Z : Scheme.{0}} {ι : Type} (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ Z) [∀ a, IsOpenImmersion (j a)],
      (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) → (∀ y : Z, ∃ a, y ∈ Set.range (j a)) → ∀ W : Z.Opens,
      (∀ a, Conn R F c (sch.map (j a ⁻¹ᵁ W).ι)) → Conn R F c (sch.map W.ι) := by
  intro hP a1 R _ F c Z ι O j _ disj cov W h
  have hsq : ∀ a, sch.map (j a ∣_ W) ≫ sch.map W.ι = sch.map (j a ⁻¹ᵁ W).ι ≫ sch.map (j a) := fun a => by
    rw [← Functor.map_comp, ← Functor.map_comp, morphismRestrict_ι]
  have hval : ∀ a (y : (j a ⁻¹ᵁ W).toScheme), W.ι ((j a ∣_ W) y) = j a ((j a ⁻¹ᵁ W).ι y) := fun a y => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
  have disjW : ∀ a b, a ≠ b → Disjoint (Set.range (j a ∣_ W)) (Set.range (j b ∣_ W)) := by
    intro a b hab
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    refine Set.disjoint_left.1 (disj a b hab) ⟨(j a ⁻¹ᵁ W).ι x, (hval a x).symm⟩ ⟨(j b ⁻¹ᵁ W).ι y, ?_⟩
    rw [← hval b y, hy]
  have covW : ∀ y : W.toScheme, ∃ a, y ∈ Set.range (j a ∣_ W) := by
    intro y
    obtain ⟨a, x, hx⟩ := cov (W.ι y)
    have hxW : x ∈ j a ⁻¹ᵁ W := by
      change j a x ∈ W
      rw [hx]
      exact y.2
    obtain ⟨x', rfl⟩ : x ∈ Set.range (j a ⁻¹ᵁ W).ι := by
      rw [Scheme.Opens.range_ι]
      exact hxW
    exact ⟨a, x', W.ι.isOpenEmbedding.injective ((hval a x').trans hx)⟩
  have key : ∀ (n : ℤ) (x : H R (sch.obj Z) F n) (a : ι),
      pull R (sch.map (j a ∣_ W)) F n (pull R (sch.map W.ι) F n x) =
        pull R (sch.map (j a ⁻¹ᵁ W).ι) F n (pull R (sch.map (j a)) F n x) := by
    intro n x a
    rw [← pull_comp, ← pull_comp, hsq]
  intro n
  have PZ := hP a1 R F O j disj cov n
  have PW := hP a1 R F (fun a => (j a ⁻¹ᵁ W).toScheme) (fun a => j a ∣_ W) disjW covW n
  have hinj : n < c → Function.Injective (pull R (sch.map W.ι) F n) := by
    intro hn x y hxy
    apply PZ.1
    funext a
    have ha : Function.Injective (pull R (sch.map (j a ⁻¹ᵁ W).ι) F n) := (h a n).2 hn
    apply ha
    rw [← key, ← key, hxy]
  refine ⟨fun hn => ⟨hinj (by omega), ?_⟩, hinj⟩
  intro y
  have hs : ∀ a, ∃ z, pull R (sch.map (j a ⁻¹ᵁ W).ι) F n z = pull R (sch.map (j a ∣_ W)) F n y := by
    intro a
    have ha : Function.Bijective (pull R (sch.map (j a ⁻¹ᵁ W).ι) F n) := (h a n).1 hn
    exact ha.2 _
  choose z hz using hs
  obtain ⟨x, hx⟩ := PZ.2 z
  refine ⟨x, ?_⟩
  apply PW.1
  funext a
  have hxa : pull R (sch.map (j a)) F n x = z a := congrFun hx a
  change pull R (sch.map (j a ∣_ W)) F n (pull R (sch.map W.ι) F n x) = pull R (sch.map (j a ∣_ W)) F n y
  rw [key, hxa, hz]

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ConstantSheafCyclicGeneratorOfOrder
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

private theorem UpperTheory.continuousSection_nsmul (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T]
    [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (U : Scheme.{0})
    (a : C(U, T)) (c : ℕ) : cSec R T (c • a) = c • cSec R T a := by
  exact map_nsmul (AddMonoidHom.mk' (cSec R T (U := U)) (UpperTheory.continuousSections_bijective_additive_natural R T U).2.1) c a

private theorem UpperTheory.restriction_comp {R : Type} [CommRing R] (M : PMod R) {W' W V : Scheme.{0}}
    (l : W' ⟶ W) (h : W ⟶ V) (z : sec M V) : rs M (l ≫ h) z = rs M l (rs M h z) := by
  simp only [rs, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem UpperTheory.constantSheaf_cyclic_generator_of_order :
    ∀ (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T] [DiscreteTopology T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (q : ℕ) (t : T), q • t = 0 → (∀ c : ℕ, c • t = 0 → q ∣ c) → (∀ x : T, ∃ c : ℕ, x = c • t) → ∀ U : Scheme.{0}, Gen Scheme.etaleTopology q (cSh R T).obj (cSec R T (ContinuousMap.const U t)) := by
  intro R _ T _ _ _ _ _ _ q t hq hmin hgen U
  have hsm : ∀ (W : Scheme.{0}) (a : C(W, T)) (c : ℕ), cSec R T (c • a) = c • cSec R T a :=
    fun W a c => UpperTheory.continuousSection_nsmul R T W a c
  have h0 : ∀ W : Scheme.{0}, cSec R T (0 : C(W, T)) = 0 := fun W =>
    map_zero (AddMonoidHom.mk' (cSec R T (U := W)) (UpperTheory.continuousSections_bijective_additive_natural R T W).2.1)
  have hrs : ∀ (V : Scheme.{0}) (k : V ⟶ U),
      rs (cSh R T).obj k (cSec R T (ContinuousMap.const U t)) =
        cSec R T (ContinuousMap.const V t) := by
    intro V k
    rw [(UpperTheory.continuousSections_bijective_additive_natural R T U).2.2.1]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsm, show q • ContinuousMap.const U t = 0 by ext; simp [hq], h0]
  · intro V k c hV hc
    obtain ⟨v⟩ := hV
    rw [hrs, ← hsm, ← h0 V] at hc
    have he := (UpperTheory.continuousSections_bijective_additive_natural R T V).1.1 hc
    have hv : c • t = 0 := by simpa using congrArg (fun f : C(V, T) => f v) he
    exact hmin c hv
  · intro V k y
    obtain ⟨b, rfl⟩ := (UpperTheory.continuousSections_bijective_additive_natural R T V).1.2 y
    refine (UpperTheory.etaleLocallyHolds_of_pointwise_cover_or_affine_local V _ ?_).1 ?_
    · rintro W W' g' k' ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [UpperTheory.restriction_comp _ k' g', hc, Category.assoc, UpperTheory.restriction_comp _ k' (g' ≫ k)]
      exact map_nsmul ((cSh R T).obj.map k'.op).hom c _
    · intro x
      obtain ⟨c, hc⟩ := hgen (b x)
      let O : V.Opens := ⟨b ⁻¹' {b x}, (isOpen_discrete _).preimage b.continuous⟩
      refine ⟨O, O.ι, inferInstance, ?_, c, ?_⟩
      · rw [Scheme.Opens.range_ι]
        show b x ∈ ({b x} : Set T)
        exact Set.mem_singleton _
      · rw [(UpperTheory.continuousSections_bijective_additive_natural R T V).2.2.1, hrs, ← hsm]
        congr 1
        ext w
        have hw : O.ι w ∈ (O : Set V) := Scheme.Opens.range_ι O ▸ Set.mem_range_self w
        have hw' : b (O.ι w) = b x := hw
        simp [hw', hc]
end

