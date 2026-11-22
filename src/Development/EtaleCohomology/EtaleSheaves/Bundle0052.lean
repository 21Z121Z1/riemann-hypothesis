import Development.EtaleCohomology.EtaleSheaves.Bundle0035
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration.LevelsOfGen
import Development.EtaleCohomology.EtaleSheaves.Bundle0039
import Development.EtaleCohomology.EtaleSheaves.Bundle0033
import Development.EtaleCohomology.EtaleSheaves.Bundle0041
import Development.EtaleCohomology.EtaleSheaves.Bundle0017
import Development.EtaleCohomology.EtaleSheaves.Bundle0032
import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf
import Development.EtaleCohomology.EtaleSheaves.Bundle0034
import Development.EtaleCohomology.EtaleSheaves.Bundle0010

-- bundled from Development.EtaleCohomology.EtaleSheaves.RestrPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.ContStepPf LateralTheory.E.StepKPf

namespace LateralTheory.E.RestrPf

theorem pull_zero {q : ℕ} {n i : ℤ} {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (y : Ht q (sch.obj C) n i)
    (h : pull _ (sch.map b) _ _ y = 0) : pull _ (sch.map (a ≫ b)) _ _ y = 0 := by
  rw [Functor.map_comp, pull_comp, h, map_zero]

theorem Restr_of : Restr := by
  intro h q J _ _ D c hc ha hcs hqs hu j0 X e U hU pU
  have : ∀ {a b : J} (g : a ⟶ b), IsAffineHom (D.map g) := ha
  let W : (D.obj j0).Opens := e.hom ⁻¹ᵁ U
  have haff : ∀ {a b : Over j0} (g : a ⟶ b), IsAffineHom ((opensDiagram D j0 W).map g) := fun g => inferInstance
  have hcpt : ∀ a : Over j0, CompactSpace ((opensDiagram D j0 W).obj a) := fun a =>
    isCompact_iff_compactSpace.mp ((D.map a.hom).isCompact_preimage hU)
  have hqs' : ∀ a : Over j0, QuasiSeparatedSpace ((opensDiagram D j0 W).obj a) := fun a => by
    have := hqs a.left
    exact (D.map a.hom ⁻¹ᵁ W).isOpen.isOpenEmbedding_subtypeVal.quasiSeparatedSpace
  have hu' : ∀ a : Over j0, IsUnit (q : Γ((opensDiagram D j0 W).obj a, ⊤)) := fun a => by
    show IsUnit (q : Γ((D.map a.hom ⁻¹ᵁ W).toScheme, ⊤))
    simpa using (hu a.left).map (Scheme.Hom.appTop (Scheme.Opens.ι (D.map a.hom ⁻¹ᵁ W))).hom
  have hiso : Nonempty ((opensDiagram D j0 W).obj (Over.mk (𝟙 j0)) ≅ U.toScheme) := by
    refine ⟨(D.obj j0).isoOfEq ?_ ≪≫ asIso (e.hom ∣_ U)⟩
    simp [W]
  have P := pU q (opensDiagram D j0 W) (opensCone D c j0 W) (isLimitOpensCone D c hc j0 W) haff hcpt hqs' hu'
    (Over.mk (𝟙 j0)) hiso
  intro n i
  obtain ⟨P1, P2⟩ := P n i
  refine ⟨fun x => ?_, fun k f y hy => ?_⟩
  · obtain ⟨j', y, hy⟩ := P1 x
    exact ⟨j'.left, j'.hom, y, hy⟩
  · obtain ⟨k', g', hg'⟩ := P2 (Over.mk f) y hy
    refine ⟨k'.left, g'.left, ?_⟩
    have hle : lv D e U (g'.left ≫ f) ≤ D.map k'.hom ⁻¹ᵁ W := by
      rw [← Over.w g']; exact le_rfl
    let ι0 : (lv D e U (g'.left ≫ f)).toScheme ⟶ (opensDiagram D j0 W).obj k' := (D.obj k'.left).homOfLE hle
    have heq : rD D e U f g'.left = ι0 ≫ (opensDiagram D j0 W).map g' := by
      apply (cancel_mono (lv D e U f).ι).mp
      have e1 : (opensDiagram D j0 W).map g' ≫ (D.map (Over.mk f).hom ⁻¹ᵁ W).ι =
          (D.map k'.hom ⁻¹ᵁ W).ι ≫ D.map g'.left := Scheme.Hom.resLE_comp_ι _ _
      have e2 : ι0 ≫ (D.map k'.hom ⁻¹ᵁ W).ι = (lv D e U (g'.left ≫ f)).ι := Scheme.homOfLE_ι _ _
      calc rD D e U f g'.left ≫ (lv D e U f).ι = (lv D e U (g'.left ≫ f)).ι ≫ D.map g'.left :=
            Scheme.Hom.resLE_comp_ι _ _
        _ = (ι0 ≫ (D.map k'.hom ⁻¹ᵁ W).ι) ≫ D.map g'.left := by rw [e2]
        _ = ι0 ≫ ((D.map k'.hom ⁻¹ᵁ W).ι ≫ D.map g'.left) := Category.assoc _ _ _
        _ = ι0 ≫ ((opensDiagram D j0 W).map g' ≫ (D.map (Over.mk f).hom ⁻¹ᵁ W).ι) :=
            congrArg (fun t => ι0 ≫ t) e1.symm
        _ = (ι0 ≫ (opensDiagram D j0 W).map g') ≫ (lv D e U f).ι := (Category.assoc _ _ _).symm
    rw [heq]; exact pull_zero ι0 ((opensDiagram D j0 W).map g') y hg'

end LateralTheory.E.RestrPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpectrumLimits
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

def IsCop {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) : Prop :=
  ∀ (R : Type) [CommRing R] (g : ι → (A' →+* R)) (c : A →+* R), (∀ i, (g i).comp φ = c) →
    ∃! h : B →+* R, (∀ i, h.comp (l i) = g i) ∧ h.comp χ = c

theorem le_l {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B)
    (f : A' →+* B) (hf : f.comp φ = χ) (I : Ideal A) : I.map φ ≤ (I.map χ).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hf]

abbrev lq {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B)
    (f : A' →+* B) (hf : f.comp φ = χ) (I : Ideal A) : A' ⧸ I.map φ →+* B ⧸ I.map χ :=
  Ideal.quotientMap (I.map χ) f (le_l φ χ f hf I)

def coneOf {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) :
    Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : ι => yoneda.obj (Spec (CommRingCat.of A'))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom φ)))) :=
  WidePullbackShape.mkCone (yoneda.map (Spec.map (CommRingCat.ofHom χ))) (fun i => yoneda.map (Spec.map (CommRingCat.ofHom (l i))))
    (fun i => by
      change yoneda.map _ ≫ yoneda.map (Spec.map (CommRingCat.ofHom φ)) = _
      rw [← yoneda.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i])

def SpecLim : Prop := ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) (n : ℕ)
  (l : Fin (n + 1) → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ), IsCop φ χ l → Nonempty (IsLimit (coneOf φ χ l hl))

def TensCop : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (n : ℕ),
  ∃ (B : Type) (_ : CommRing B) (χ : A →+* B) (l : Fin (n + 1) → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ),
    Subring.closure (⋃ i, Set.range (l i)) = ⊤ ∧ IsCop φ χ l

def QuotCop : Prop := ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
  (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (I : Ideal A), IsCop φ χ l →
    IsCop (qm φ I) (qm χ I) (fun i => lq φ χ (l i) (hl i) I)

theorem lq_hl {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
  (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (I : Ideal A) (i : ι) :
    (lq φ χ (l i) (hl i) I).comp (qm φ I) = qm χ I := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp [qm, lq, ← hl i]

theorem ysq {R S S' T : Type} [CommRing R] [CommRing S] [CommRing S'] [CommRing T] (f : R →+* S) (g : S →+* T)
    (f' : R →+* S') (g' : S' →+* T) (h : g.comp f = g'.comp f') :
    yoneda.map (Spec.map (CommRingCat.ofHom g)) ≫ yoneda.map (Spec.map (CommRingCat.ofHom f)) =
      yoneda.map (Spec.map (CommRingCat.ofHom g')) ≫ yoneda.map (Spec.map (CommRingCat.ofHom f')) := by
  rw [← yoneda.map_comp, ← yoneda.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, h]

theorem LevelsGen_of (hT : TensCop) (hQ : QuotCop) (hS : SpecLim) : LevelsGen := by
  intro A A' _ _ φ I p
  obtain ⟨B, _, χ, l, hl, hc, hcop⟩ := hT A A' φ (p.unop.len)
  refine ⟨B, inferInstance, χ, _, l, hl, hc, ?_⟩
  obtain ⟨L⟩ := hS A A' B φ χ _ l hl hcop
  obtain ⟨Lr⟩ := hS _ _ _ (qm φ I) (qm χ I) _ _ (lq_hl φ χ l hl I) (hQ A A' B φ χ l hl I hcop)
  let e : (cech (Spec.map (CommRingCat.ofHom φ))).obj p ≅
      yoneda.obj (Spec (CommRingCat.of B)) := (limit.isLimit _).conePointUniqueUpToIso L
  let er : (cech (Spec.map (CommRingCat.ofHom (qm φ I)))).obj p ≅
      yoneda.obj (Spec (CommRingCat.of (B ⧸ I.map χ))) := (limit.isLimit _).conePointUniqueUpToIso Lr
  refine ⟨Arrow.isoMk er e ?_⟩
  simp only [Arrow.mk_hom]
  apply L.hom_ext
  rintro (_|i)
  · have h1 : er.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (qm χ I))) = (WidePullback.base _ : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp Lr none
    have h2 : e.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ)) = (WidePullback.base _ : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp L none
    change (er.hom ≫ _) ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ)) =
      ((psi φ I).app p ≫ e.hom) ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ))
    rw [Category.assoc, Category.assoc, h2, ysq χ (Ideal.Quotient.mk (I.map χ)) (Ideal.Quotient.mk I) (qm χ I) (qm_comp χ I).symm,
      ← Category.assoc, h1]
    simp only [psi, Arrow.mapCechNerve_app, sqA, Arrow.homMk_right]
    erw [WidePullback.lift_base]
    all_goals rfl
  · have h1 : er.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (lq φ χ (l i) (hl i) I))) = (WidePullback.π _ i : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp Lr (some i)
    have h2 : e.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i))) = (WidePullback.π _ i : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp L (some i)
    change (er.hom ≫ _) ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i))) =
      ((psi φ I).app p ≫ e.hom) ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i)))
    rw [Category.assoc, Category.assoc, h2, ysq (l i) (Ideal.Quotient.mk (I.map χ)) (Ideal.Quotient.mk (I.map φ))
      (lq φ χ (l i) (hl i) I) (Ideal.quotientMap_comp_mk _).symm, ← Category.assoc, h1]
    simp only [psi, Arrow.mapCechNerve_app, sqA, Arrow.homMk_left]
    erw [WidePullback.lift_π]
    all_goals rfl

end LateralTheory.E.LevelsGenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StageBPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.ProEqvPf

namespace LateralTheory.E.StageBPf

theorem pp {q : ℕ} {i n : ℤ} {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : Ht q (sch.obj Z) n i) :
    pull _ (sch.map a) _ _ (pull _ (sch.map b) _ _ x) = pull _ (sch.map (a ≫ b)) (tw q i) n x := by
  rw [Functor.map_comp, pull_comp]

theorem indep {Y : Scheme.{0}} {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D)
    (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j j' : J) :
    c.π.app j ≫ ι j = c.π.app j' ≫ ι j' := by
  rw [← c.w (IsCofiltered.minToLeft j j'), ← c.w (IsCofiltered.minToRight j j'), Category.assoc, Category.assoc, hι, hι]

theorem qc_of {X Y : Scheme.{0}} (f : X ⟶ Y) (h : IsAffineHom f) (hY : CompactSpace Y) : CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace f
theorem qs_of {X Y : Scheme.{0}} (f : X ⟶ Y) (h : IsAffineHom f) (hY : QuasiSeparatedSpace Y) : QuasiSeparatedSpace X :=
  quasiSeparatedSpace_of_quasiSeparated f
theorem aff_canc {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h1 : IsAffineHom (f ≫ g)) (h2 : IsAffineHom g) : IsAffineHom f := by
  have := IsSeparated.of_isAffineHom g; exact IsAffineHom.of_comp f g
theorem aff_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h1 : IsAffineHom f) (h2 : IsAffineHom g) : IsAffineHom (f ≫ g) :=
  inferInstance

variable {A : Type} [CommRing A] [IsLocalRing A]

@[simps]
def DO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0})
    (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) : J ⥤ Over (Spec (CommRingCat.of A)) where
  obj j := Over.mk (ι j ≫ g)
  map f := Over.homMk (D.map f) (by dsimp; rw [← Category.assoc, hι])
  map_id := by intros; ext; simp
  map_comp := by intros; ext; simp

@[simps]
def CO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0})
    (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J) :
    Cone (DO g D ι hι) where
  pt := Over.mk ((c.π.app j0 ≫ ι j0) ≫ g)
  π := { app := fun j => Over.homMk (c.π.app j) (by show c.π.app j ≫ ι j ≫ g = _; rw [← Category.assoc, indep D c ι hι j j0]; rfl)
         naturality := by intro j k f; ext; exact (c.w f).symm }

def isLimit_CO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J)
    (hl : IsLimit c) : IsLimit (CO g D c ι hι j0) := by
  haveI := IsCofiltered.isConnected J
  exact isLimitOfReflects (Over.forget _) hl

def isLimit_fib {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J)
    (hl : IsLimit c) :
    IsLimit ((Over.forget _).mapCone ((Over.pullback (cpt A)).mapCone (CO g D c ι hι j0))) := by
  haveI := IsCofiltered.isConnected J
  haveI := (Over.mapPullbackAdj (cpt A)).rightAdjoint_preservesLimits
  exact isLimitOfPreserves _ (isLimitOfPreserves _ (isLimit_CO g D c ι hι j0 hl))

theorem fm_comp {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {U V : Scheme.{0}} (u : U ⟶ Y) (v : V ⟶ Y) (d : U ⟶ V)
    (hd : d ≫ v = u) (h : pullback (u ≫ g) (cpt A) ⟶ pullback (v ≫ g) (cpt A))
    (h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d) (h2 : h ≫ pullback.snd _ _ = pullback.snd _ _) :
    h ≫ fm v g = fm u g := by
  apply pullback.hom_ext
  · simp only [fm, pullback.map, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, ← Category.assoc, h1, Category.assoc, hd]
  · simp only [fm, pullback.map, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd, Category.comp_id, Category.comp_id, h2]

end LateralTheory.E.StageBPf

namespace LateralTheory.E.StageBPf

theorem StageB_of : StageB := by
  intro hC H q i A _ _ hq Y _ _ g y J _ _ D c ι hc hp n z
  obtain ⟨⟨hl⟩, hι, hD⟩ := hc
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have hcs : ∀ j, CompactSpace (D.obj j) := fun j => by
    have := (hι j).2.1; exact QuasiCompact.compactSpace_of_compactSpace (ι j)
  have hqs : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j => by
    have := (hι j).1; exact quasiSeparatedSpace_of_quasiSeparated (ι j)
  have hι' : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j := fun f => (hD f).1
  obtain ⟨w, hw⟩ := (hp j0 n).2 (pull _ (sch.map (fm (c.π.app j0 ≫ ι j0) g)) _ _ z)
  obtain ⟨j1, u, hu⟩ := (hC H q D c hl (fun f => (hD f).2) hcs hqs (fun j => unit_of hq (ι j ≫ g)) n i).1 w
  have hfa : ∀ j, IsAffineHom (pullback.fst (ι j ≫ g) (cpt A)) := fun j =>
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have hκ : IsUnit (q : IsLocalRing.ResidueField A) := by simpa using hq.map (IsLocalRing.residue A)
  let Cg := (Over.forget _).mapCone ((Over.pullback (cpt A)).mapCone (CO g D c ι hι' j0))
  have hlim : IsLimit Cg := isLimit_fib g D c ι hι' j0 hl
  have hEaff : ∀ {j k : J} (f : j ⟶ k), IsAffineHom (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f) := by
    intro j k f
    have e : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.fst (ι k ≫ g) (cpt A) =
        pullback.fst (ι j ≫ g) (cpt A) ≫ D.map f := pullback.lift_fst _ _ _
    refine aff_canc _ (pullback.fst (ι k ≫ g) (cpt A)) ?_ (hfa k)
    rw [e]; exact aff_comp _ _ (hfa j) (hD f).2
  have hEc : ∀ j, CompactSpace (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j) := fun j =>
    qc_of (pullback.fst (ι j ≫ g) (cpt A)) (hfa j) (hcs j)
  have hEq : ∀ j, QuasiSeparatedSpace (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j) := fun j =>
    qs_of (pullback.fst (ι j ≫ g) (cpt A)) (hfa j) (hqs j)
  have hEu : ∀ j, IsUnit (q : Γ((((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j), ⊤)) := fun j =>
    unit_of hκ (pullback.snd (ι j ≫ g) (cpt A))
  have key1 : Cg.π.app j1 ≫ pullback.fst (ι j1 ≫ g) (cpt A) = pullback.fst _ _ ≫ c.π.app j1 := pullback.lift_fst _ _ _
  have key1s : Cg.π.app j1 ≫ pullback.snd (ι j1 ≫ g) (cpt A) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have key2 : Cg.π.app j1 ≫ fm (ι j1) g = fm (c.π.app j0 ≫ ι j0) g :=
    fm_comp g (c.π.app j0 ≫ ι j0) (ι j1) (c.π.app j1) (indep D c ι hι' j1 j0) _ key1 key1s
  have hv : pull _ (sch.map (Cg.π.app j1)) _ _ (pull _ (sch.map (pullback.fst (ι j1 ≫ g) (cpt A))) _ _ u -
      pull _ (sch.map (fm (ι j1) g)) (tw q i) n z) = 0 := by
    erw [map_sub, pp, pp, key1, key2, ← pp, hu, hw, sub_self]
  obtain ⟨k, f, hk⟩ := (hC H q _ Cg hlim hEaff hEc hEq hEu n i).2 j1 _ hv
  refine ⟨k, pull _ (sch.map (D.map f)) _ _ u, ?_⟩
  have key3 : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.fst (ι j1 ≫ g) (cpt A) =
      pullback.fst (ι k ≫ g) (cpt A) ≫ D.map f := pullback.lift_fst _ _ _
  have key5 : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.snd (ι j1 ≫ g) (cpt A) =
      pullback.snd (ι k ≫ g) (cpt A) := pullback.lift_snd _ _ _
  have key4 := fm_comp g (ι k) (ι j1) (D.map f) (hι' f) _ key3 key5
  erw [map_sub, pp, pp, key3, key4, ← pp, sub_eq_zero] at hk
  exact hk

end LateralTheory.E.StageBPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkSHSPf
section
noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial LateralTheory.E.t_E2Cut LateralTheory.E.FibStalkPf

namespace LateralTheory.E.StalkSHSPf

theorem germs (S : Scheme.{0}) (x : S) (c : ℕ → S.presheaf.stalk x) (s : Finset ℕ) :
    ∃ (U : S.Opens) (_ : IsAffineOpen U) (hx : x ∈ U) (f : ℕ → Γ(S, U)),
      ∀ i ∈ s, (S.presheaf.germ U x hx).hom (f i) = c i := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨U, hU, hx, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show x ∈ (⊤ : S.Opens) from trivial)
    exact ⟨U, hU, hx, fun _ => 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨U, hU, hx, f, hf⟩ := ih
    obtain ⟨V, hxV, g, hg⟩ := S.presheaf.exists_germ_eq (c a)
    obtain ⟨W, hW, hxW, hWUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show x ∈ U ⊓ V from ⟨hx, hxV⟩)
    refine ⟨W, hW, hxW, fun i => if i = a then (S.presheaf.map (homOfLE (hWUV.trans inf_le_right)).op).hom g
       else (S.presheaf.map (homOfLE (hWUV.trans inf_le_left)).op).hom (f i), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp only [if_true]
      rw [← hg, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    · have : i ≠ a := fun h => ha (h ▸ hi)
      simp only [this, if_false]
      rw [← hf i hi, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]

theorem stalkAIC : StalkAIC := by
  intro S hS x p hm hd
  obtain ⟨U, hU, hx, f, hf⟩ := germs S x (fun i => p.coeff i) (Finset.range (p.natDegree + 1))
  have hl : p ∈ Polynomial.lifts (S.presheaf.germ U x hx).hom := by
    refine (lifts_iff_coeff_lifts p).2 fun i => ?_
    by_cases hi : i < p.natDegree + 1
    · exact ⟨f i, hf i (Finset.mem_range.2 hi)⟩
    · exact ⟨0, by rw [map_zero, coeff_eq_zero_of_natDegree_lt (by omega)]⟩
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  obtain ⟨r, hr⟩ := hS.2 U hU ⟨x, hx⟩ P hPm (by omega)
  exact ⟨(S.presheaf.germ U x hx).hom r, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hr, map_zero]⟩

end LateralTheory.E.StalkSHSPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StdChartsOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StdChartsProof₂

theorem StdCharts_of : LateralTheory.E.StandardEtaleChartsMultivariableHensel.StdCharts := by
  intro A _ _ Z p hp
  obtain ⟨L, u, l, hu, ⟨hl, f, hf⟩, hul⟩ := hp
  have hf' : IsAffineHom f := MorphismProperty.of_isPullback hf.flip inferInstance
  let g : Z ⟶ P1 := u ≫ f
  have hU : ∀ i, IsAffineOpen (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D i) := fun i => (LateralTheory.E.ChartsPf.D_affine i).preimage g
  refine ⟨g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 0, g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 1, (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 0).ι,
    (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 1).ι, inferInstance, inferInstance, hU 0, hU 1, ?_, ?_⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    have hx : g x ∈ (⨆ i, LateralTheory.E.ChartsPf.D i : P1.Opens) := by rw [LateralTheory.E.ChartsPf.D_cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · refine ⟨L, u, l, f, hu, hl, hf, hul, ?_, ?_⟩
    · rw [Scheme.Opens.range_ι]; rfl
    · rw [Scheme.Opens.range_ι]; rfl

end LateralTheory.E.StdChartsProof₂
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SysOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut LateralTheory.E.CompCut

namespace LateralTheory.E.SysPf

def HasLim : Prop := ∀ {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}),
  (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → ∃ c : Cone D, Nonempty (IsLimit c)

def NbIso : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ∀ c : Cone D, IsLimit c →
        Nonempty (c.pt ≅ (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization)

theorem Sys_of (hH : HasLim) (hN : NbIso) : Sys := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, h3⟩ := hN W w hW y
  obtain ⟨c, ⟨hc⟩⟩ := hH D (fun f => (h2 f).2)
  exact ⟨q, J, inferInstance, inferInstance, D, c, ι, ⟨⟨hc⟩, h1, fun f => h2 f⟩, h3 c hc⟩

end LateralTheory.E.SysPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TruncCokPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf Opposite

namespace LateralTheory.E.TruncCokPf

def sq {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y') (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'') (h : φ' ≫ u = e ≫ φ'') :
    Arrow.mk (yoneda.map (Spec.map u)) ⟶ Arrow.mk (yoneda.map (Spec.map e)) :=
  Arrow.homMk (yoneda.map (Spec.map φ'')) (yoneda.map (Spec.map φ')) (by
    simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp, h])

def LevelLow (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y')
    (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'') (h : φ' ≫ u = e ≫ φ'') : Prop :=
  ∀ (p : ℕ) (m : ℤ), m < n →
    (∀ k : ℤ, k + 1 = m → Function.Surjective (pull R (disc.map ((Arrow.mapCechNerve (sq e φ' u φ'' h)).app (op (SimplexCategory.mk p)))) F k)) ∧
    Function.Injective (pull R (disc.map ((Arrow.mapCechNerve (sq e φ' u φ'' h)).app (op (SimplexCategory.mk p)))) F m)

def Desc : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y')
    (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'') (hpo : IsPushout φ' e u φ''), Et e → SpS e →
    LevelLow R F n e φ' u φ'' hpo.w →
    ∀ m : ℤ, m + 1 = n → ∀ y : H R (sch.obj (Spec Y')) F m,
      pull R (sch.map (Spec.map u)) F m y ∈ Set.range (pull R (sch.map (Spec.map φ'')) F m) →
      y ∈ Set.range (pull R (sch.map (Spec.map φ')) F m)

def Levels : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (hpo : IsPushout φ' e u φ''), Et e → SpS e → P E (d ≫ e) →
    LevelLow (ZMod q) (tw q i) n e φ' u φ'' hpo.w

theorem TruncCok_of (hD : Desc) (hL : Levels) : LateralTheory.E.DescLocPf.Fine.TruncCok := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD' Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' m hm y hy
  exact hD hH (ZMod q) (tw q i) n e φ' u φ'' hpo' he hs
    (hL hH q i n φ hq P hpush het hlow D d hD' Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE) m hm y hy

end LateralTheory.E.TruncCokPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TruncKerPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.TruncationKernel

def RelExact : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (x : H R E F n),
  pull R f F n x = 0 → ∃ y : Hrel R f F n, fgt R f F n y = x

def RelNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (y : Hrel R f F n),
  fgt R f' F n (rpull R f f' u e comm F n y) = pull R e F n (fgt R f F n y)

def FgtInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R f F m)) → Function.Injective (fgt R f F n)

def RelDesc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → ∀ hpo' : IsPushout φ' e u φ'',
  Function.Injective (rpl q i (Spec.map φ') (Spec.map φ'') (Spec.map u) (Spec.map e)
    (by rw [← Spec.map_comp, ← Spec.map_comp, hpo'.w]) n)

theorem exists_fgt_eq_of_pull_eq_zero : ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (x : H R E F n),
  pull R f F n x = 0 → ∃ y : Hrel R f F n, fgt R f F n y = x := by
  intro R _ F U E f n x hx
  obtain ⟨z, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)) = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff] at hx
  obtain ⟨m, hm, β, hβ⟩ := hx
  refine ⟨CohomologyClass.mk (mappingCone.descCocycle _ (n.negOnePow • β) z hm ?_), ?_⟩
  · rw [δ_units_smul, hβ]
    rfl
  · refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
    exact mappingCone.inr_descCochain _ _ _ hm

theorem fgt_injective_of_pull_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R f F m)) → Function.Injective (fgt R f F n) := by
  intro R _ F U E f n hs
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) c (zero_add n)) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m, hm, γ, hγ⟩ := hy
  change δ m n γ = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp c.1 (zero_add n) at hγ
  have hdec : c.1 = mappingCone.descCochain _ ((mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia))
      (δ m n γ) hm := by
    rw [mappingCone.ext_cochain_from_iff _ m n hm, hγ]
    simp
  have hc : δ n (n + 1) c.1 = 0 := Cocycle.δ_eq_zero c (n + 1)
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ rfl] at hc
  have hc' := congrArg (fun z => (mappingCone.inl ((chains R).map f)).comp z (show -1 + (n + 1) = n by lia)) hc
  simp at hc'
  set a := (mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia) with ha
  have hz : δ m n (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) = 0 := by
    rw [δ_sub, δ_units_smul, δ_ofHom_comp]
    rw [Int.negOnePow_succ, Units.neg_smul, ← sub_eq_add_neg] at hc'
    exact hc'
  obtain ⟨w, hw⟩ := hs m hm (CohomologyClass.mk (Cocycle.mk _ n hm hz))
  obtain ⟨w', rfl⟩ := w.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) w' (zero_add m)) = _ at hw
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff] at hw
  obtain ⟨k, hk, α0, hα0⟩ := hw
  change δ k m α0 = (Cochain.ofHom ((chains R).map f)).comp w'.1 (zero_add m) -
    (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) at hα0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, hm, mappingCone.descCochain _ (-α0) (γ + n.negOnePow • w'.1) hk, ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ _ hm, δ_add, δ_units_smul, Cocycle.δ_eq_zero, smul_zero, add_zero]
  conv_rhs => rw [hdec]
  rw [mappingCone.ext_cochain_from_iff _ m n hm]
  refine ⟨?_, ?_⟩
  · simp only [mappingCone.inl_descCochain, Cochain.comp_add, mappingCone.inl_fst_assoc]
    simp only [δ_neg, hα0, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul, mappingCone.inl_snd_assoc, zero_comp, Cochain.zero_comp, add_zero]
    abel
  · simp

theorem relExact : RelExact := exists_fgt_eq_of_pull_eq_zero
theorem fgtInj : FgtInj := fgt_injective_of_pull_surjective

end LateralTheory.E.TruncationKernel
end
end

