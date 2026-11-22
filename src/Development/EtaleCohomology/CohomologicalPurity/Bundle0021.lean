import Development.EtaleCohomology.CohomologicalPurity.Bundle0015
import Development.EtaleCohomology.CohomologicalPurity.Bundle0016
import Development.EtaleCohomology.CohomologicalPurity.Bundle0008
import Development.EtaleCohomology.CohomologicalPurity.Bundle0011

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafLocBasePf
section
set_option linter.unusedSimpArgs false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.LocBasePf

theorem isPullback_of_app {K C : Type*} [Category K] [Category C] [HasPullbacks C] {P X Y Z : K ⥤ C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (h : ∀ k, IsPullback (fst.app k) (snd.app k) (f.app k) (g.app k)) : IsPullback fst snd f g :=
  IsPullback.of_isLimit (c := PullbackCone.mk fst snd w)
    (evaluationJointlyReflectsLimits _ fun k =>
      (isLimitMapConePullbackConeEquiv ((evaluation K C).obj k) w).symm (h k).isLimit)

section
variable {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
  (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {Y : Scheme.{0}} (g : Y ⟶ X)

include hc in
theorem cw {j k : J} (f : j ⟶ k) : D.map f ≫ c k = c j :=
  yoneda.map_injective (by simpa using hc j k f)

def D' : J ⥤ Scheme.{0} where
  obj j := pullback (c j) g
  map {j k} f := pullback.map (c j) g (c k) g (D.map f) (𝟙 Y) (𝟙 X) (by simp [cw D c hc f]) (by simp)
  map_id j := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id]
    exact (congrArg (pullback.fst (c j) g ≫ ·) (D.map_id j)).trans (Category.comp_id _)
  map_comp f f' := by apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id]

def c' (j : J) : (D' D c hc g).obj j ⟶ Y := pullback.snd (c j) g

theorem hc' : Coc (D' D c hc g ⋙ yoneda) fun j => yoneda.map (c' D c hc g j) := by
  intro j k f
  rw [Functor.comp_map, ← yoneda.map_comp]
  congr 1
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

def α : D' D c hc g ⋙ yoneda ⟶ D ⋙ yoneda where
  app j := yoneda.map (pullback.fst (c j) g)
  naturality j k f := by
    have e : (D' D c hc g).map f ≫ pullback.fst (c k) g = pullback.fst (c j) g ≫ D.map f := pullback.lift_fst _ _ _
    exact (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map e).trans (yoneda.map_comp _ _))

theorem sq : (hocF J).map (α D c hc g) ≫ aug _ hc = aug _ (hc' D c hc g) ≫ sch.map g := by
  ext n U x
  have key : ∀ j (a : unop U ⟶ pullback (c j) g), (a ≫ pullback.fst (c j) g) ≫ c j = (a ≫ pullback.snd (c j) g) ≫ g :=
    fun j a => by rw [Category.assoc, Category.assoc, pullback.condition]
  exact key _ _

theorem snd_map {j k : J} (f : j ⟶ k) {V : Scheme.{0}} (a : V ⟶ (D' D c hc g).obj j) :
    (a ≫ (D' D c hc g).map f) ≫ c' D c hc g k = a ≫ c' D c hc g j := by
  rw [Category.assoc]
  congr 1
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem snd_chain {n : ℕ} {U : Scheme.{0}ᵒᵖ} (z : Fin (n + 1) ⥤ ((D' D c hc g ⋙ yoneda).flip.obj U).Elements)
    (i : Fin (n + 1)) : (z.obj i).2 ≫ c' D c hc g (z.obj i).1 = (z.obj 0).2 ≫ c' D c hc g (z.obj 0).1 := by
  have m := (z.map (homOfLE (Fin.zero_le i))).2
  rw [← m]
  exact snd_map D c hc g _ _

include hc in
theorem c_chain {n : ℕ} {U : Scheme.{0}ᵒᵖ} (z : Fin (n + 1) ⥤ ((D ⋙ yoneda).flip.obj U).Elements)
    (i : Fin (n + 1)) : (z.obj i).2 ≫ c (z.obj i).1 = (z.obj 0).2 ≫ c (z.obj 0).1 := by
  have m := (z.map (homOfLE (Fin.zero_le i))).2
  rw [← m]
  change ((z.obj 0).2 ≫ D.map _) ≫ _ = _
  rw [Category.assoc, cw D c hc]

theorem pt_ext {U : Scheme.{0}ᵒᵖ} (p q : Σ j, unop U ⟶ pullback (c j) g)
    (h1 : (⟨p.1, p.2 ≫ pullback.fst (c p.1) g⟩ : Σ j, unop U ⟶ D.obj j) = ⟨q.1, q.2 ≫ pullback.fst (c q.1) g⟩)
    (h2 : p.2 ≫ pullback.snd (c p.1) g = q.2 ≫ pullback.snd (c q.1) g) : p = q := by
  obtain ⟨j, a⟩ := p
  obtain ⟨k, b⟩ := q
  simp only [Sigma.mk.injEq] at h1
  obtain ⟨rfl, h⟩ := h1
  have h' := eq_of_heq h
  congr 1
  exact pullback.hom_ext h' h2

include hc in
theorem lift_map {j k : J} (f : j ⟶ k) {V : Scheme.{0}} (a : V ⟶ D.obj j) (b : V ⟶ D.obj k) (y : V ⟶ Y)
    (ha : a ≫ c j = y ≫ g) (hb : b ≫ c k = y ≫ g) (hab : a ≫ D.map f = b) :
    (pullback.lift a y ha : V ⟶ (D' D c hc g).obj j) ≫ (D' D c hc g).map f = pullback.lift b y hb := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id, D', hab]

theorem pb : IsPullback ((hocF J).map (α D c hc g)) (aug _ (hc' D c hc g)) (aug _ hc) (sch.map g) := by
  refine isPullback_of_app (sq D c hc g) fun n => isPullback_of_app ?_ fun U => ?_
  · exact NatTrans.congr_app (sq D c hc g) n
  refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · exact NatTrans.congr_app (NatTrans.congr_app (sq D c hc g) n) U
  · rintro x y ⟨h1, h2⟩
    change chn x = chn y
    refine CategoryTheory.Functor.ext ?_ (fun _ _ _ => Subtype.ext (Subsingleton.elim _ _))
    intro i
    refine pt_ext D c g _ _ ?_ ?_
    · exact congrArg (fun z => (chn z).obj i) h1
    · exact (snd_chain D c hc g (chn x) i).trans (h2.trans (snd_chain D c hc g (chn y) i).symm)
  · intro x₂ x₃ h
    have e : ∀ i, ((chn x₂).obj i).2 ≫ c ((chn x₂).obj i).1 = x₃ ≫ g := fun i =>
      (c_chain D c hc (chn x₂) i).trans h
    refine ⟨mkChn (F := (D' D c hc g ⋙ yoneda).flip.obj U) (chn x₂ ⋙ CategoryOfElements.π _)
      (fun i => pullback.lift ((chn x₂).obj i).2 x₃ (e i)) (fun i k f => ?_), ?_, ?_⟩
    · exact lift_map D c hc g _ _ _ x₃ _ _ ((chn x₂).map f).2
    · change chn _ = chn x₂
      refine CategoryTheory.Functor.ext ?_ (fun _ _ _ => Subtype.ext (Subsingleton.elim _ _))
      intro i
      refine Sigma.ext rfl (heq_of_eq ?_)
      change pullback.lift _ _ _ ≫ pullback.fst (c ((chn x₂).obj i).1) g = _
      exact pullback.lift_fst _ _ _
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ = x₃
      exact pullback.lift_snd _ _ _

end

theorem hr {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
    (ho : ∀ j, IsOpenImmersion (c j)) (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {Y : Scheme.{0}} (g : Y ⟶ X)
    (j : J) (y : Y) : y ∈ Set.range (c' D c hc g j) ↔ g y ∈ Set.range (c j) := by
  have := ho j
  change y ∈ Set.range (pullback.snd (c j) g) ↔ _
  rw [IsOpenImmersion.range_pullbackSnd]
  rfl

end LateralTheory.CohomologicalPurity.TubeCut.LocBasePf

namespace LateralTheory.CohomologicalPurity.TubeCut
open LocBasePf

theorem LeafLocBase_of : EtaleLocBase := by
  intro J _ D X c ho hcov hdir hc Y g
  refine ⟨D' D c hc g, c' D c hc g, ?_, ?_, ?_, hc' D c hc g, ⟨?_⟩⟩
  · intro j
    have := ho j
    change IsOpenImmersion (pullback.snd (c j) g)
    infer_instance
  · intro y
    obtain ⟨j, hj⟩ := hcov (g y)
    exact ⟨j, (hr D c ho hc g j y).2 hj⟩
  · intro y j k h1 h2
    obtain ⟨l, hl1, hl2, hl⟩ := hdir (g y) j k ((hr D c ho hc g j y).1 h1) ((hr D c ho hc g k y).1 h2)
    exact ⟨l, hl1, hl2, (hr D c ho hc g l y).2 hl⟩
  · exact Arrow.isoMk (pb D c hc g).isoPullback.symm (Iso.refl _)
      ((IsPullback.isoPullback_inv_snd _).trans (Category.comp_id _).symm)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPBMapPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

abbrev evNU (n : ℕ) (U : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation _ _).obj (op (SimplexCategory.mk n)) ⋙ (evaluation _ _).obj (op U)

theorem pb_ext {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) {n : ℕ} {U : Scheme.{0}} (x y : Sx (pullback f g) n U)
    (h1 : ((pullback.fst f g).app _).app _ x = ((pullback.fst f g).app _).app _ y)
    (h2 : ((pullback.snd f g).app _).app _ x = ((pullback.snd f g).app _).app _ y) : x = y := by
  let G := evNU n U
  let I := PreservesPullback.iso G f g ≪≫ Types.pullbackIsoPullback (G.map f) (G.map g)
  have hi : Function.Injective I.hom := (isIso_iff_bijective I.hom).1 inferInstance |>.1
  apply hi
  apply Subtype.ext
  have a1 := (ConcreteCategory.congr_hom (PreservesPullback.iso_hom_fst G f g))
  have a2 := (ConcreteCategory.congr_hom (PreservesPullback.iso_hom_snd G f g))
  refine Prod.ext ?_ ?_
  · simp only [I, Iso.trans_hom]
    rw [types_comp_apply, types_comp_apply, Types.pullbackIsoPullback_hom_fst, Types.pullbackIsoPullback_hom_fst]
    exact (a1 x).trans (h1.trans (a1 y).symm)
  · simp only [I, Iso.trans_hom]
    rw [types_comp_apply, types_comp_apply, Types.pullbackIsoPullback_hom_snd, Types.pullbackIsoPullback_hom_snd]
    exact (a2 x).trans (h2.trans (a2 y).symm)

theorem pb_mk {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) {n : ℕ} {U : Scheme.{0}} (a : Sx X n U) (b : Sx Y n U)
    (h : (f.app _).app _ a = (g.app _).app _ b) : ∃ x : Sx (pullback f g) n U,
    ((pullback.fst f g).app _).app _ x = a ∧ ((pullback.snd f g).app _).app _ x = b := by
  let G := evNU n U
  let z : Types.PullbackObj (G.map f) (G.map g) := ⟨(a, b), h⟩
  refine ⟨(PreservesPullback.iso G f g).inv ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z), ?_, ?_⟩
  · have := (ConcreteCategory.congr_hom (PreservesPullback.iso_inv_fst G f g))
      ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z)
    refine this.trans ?_
    exact (ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_fst (G.map f) (G.map g))) z
  · have := (ConcreteCategory.congr_hom (PreservesPullback.iso_inv_snd G f g))
      ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z)
    refine this.trans ?_
    exact (ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_snd (G.map f) (G.map g))) z

theorem pr_ext {X Y : Spc} {n : ℕ} {U : Scheme.{0}} (x y : Sx (X ⨯ Y) n U)
    (h1 : ((prod.fst : X ⨯ Y ⟶ X).app _).app _ x = ((prod.fst : X ⨯ Y ⟶ X).app _).app _ y)
    (h2 : ((prod.snd : X ⨯ Y ⟶ Y).app _).app _ x = ((prod.snd : X ⨯ Y ⟶ Y).app _).app _ y) : x = y := by
  let G := evNU n U
  let I := PreservesLimitPair.iso G X Y ≪≫ Types.binaryProductIso (G.obj X) (G.obj Y)
  have hi : Function.Injective I.hom := (isIso_iff_bijective I.hom).1 inferInstance |>.1
  apply hi
  have a1 := (ConcreteCategory.congr_hom (prodComparison_fst G X Y))
  have a2 := (ConcreteCategory.congr_hom (prodComparison_snd G X Y))
  have b1 := (ConcreteCategory.congr_hom (Types.binaryProductIso_hom_comp_fst (G.obj X) (G.obj Y)))
  have b2 := (ConcreteCategory.congr_hom (Types.binaryProductIso_hom_comp_snd (G.obj X) (G.obj Y)))
  refine Prod.ext ?_ ?_
  · simp only [I, Iso.trans_hom, types_comp_apply, PreservesLimitPair.iso_hom]
    exact (b1 _).trans ((a1 x).trans (h1.trans ((a1 y).symm.trans (b1 _).symm)))
  · simp only [I, Iso.trans_hom, types_comp_apply, PreservesLimitPair.iso_hom]
    exact (b2 _).trans ((a2 x).trans (h2.trans ((a2 y).symm.trans (b2 _).symm)))

theorem um_basic {U : Scheme.{0}} {N : ℕ} (v : Fin N → Γ(U, ⊤)) (hv : Ideal.span (Set.range v) = ⊤) (p : U) :
    ∃ i : Fin N, 0 ≤ i.val ∧ p ∈ U.basicOpen (v i) := by
  have h := iSup_basicOpen_of_span_eq_top (X := U) ⊤ (Set.range v) hv
  have hp : p ∈ (⊤ : U.Opens) := trivial
  rw [← h] at hp
  obtain ⟨_, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  obtain ⟨⟨i, rfl⟩, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  exact ⟨i, Nat.zero_le _, hi⟩

theorem basic_um {A : Type} [CommRing A] {N : ℕ} (v : Fin N → Γ(Spec (CommRingCat.of A), ⊤))
    (hv : ∀ p, ∃ i : Fin N, 0 ≤ i.val ∧ p ∈ (Spec (CommRingCat.of A)).basicOpen (v i)) :
    Ideal.span (Set.range v) = ⊤ := by
  rw [← (isAffineOpen_top (Spec (CommRingCat.of A))).iSup_basicOpen_eq_self_iff]
  apply le_antisymm le_top
  intro p _
  obtain ⟨i, -, hi⟩ := hv p
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨v i, i, rfl⟩, hi⟩

def cstV (N : ℕ) (E : Spc) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (Functor.const (Fin (n.unop.len + 1))).obj (SingleObj.star (GL (Fin N) Γ(U.unop, ⊤)))
      naturality := fun U U' g => by
        ext x
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq ?_)
        exact (map_one (Matrix.GeneralLinearGroup.map _)).symm }
  naturality n m f := rfl

def conv {N n : ℕ} {U : Scheme.{0}} (c : ComposableArrows (Um N Γ(U, ⊤)) n)
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1) : ComposableArrows (Vec N 0 U) n where
  obj i := ⟨(c.obj i).1, um_basic _ (c.obj i).2⟩
  map {i j} h := ⟨(c.map h).1.2, fun k => by
    have := congrFun (c.map h).2 k
    rw [hc h] at this
    simpa using this⟩
  map_id i := Subtype.ext (congrArg (fun p => (Subtype.val p).2) (c.map_id i))
  map_comp f g := Subtype.ext (congrArg (fun p => (Subtype.val p).2) (c.map_comp f g))

theorem conv_congr {N n : ℕ} {U : Scheme.{0}} {c c' : ComposableArrows (Um N Γ(U, ⊤)) n} (e : c = c')
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1)
    (hc' : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c'.map h).1.1 = 1) : conv c hc = conv c' hc' := by
  subst e; rfl

theorem pb_gl {N : ℕ} {E : Spc} {n : SimplexCategoryᵒᵖ} {U : Scheme.{0}ᵒᵖ}
    (x : ((pullback (cstV N E) (PGL.pr N)).obj n).obj U) {i j : Fin (n.unop.len + 1)} (h : i ⟶ j) :
    ((((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x : ComposableArrows (Um N Γ(U.unop, ⊤)) n.unop.len).map h).1.1
      = 1 := by
  have e0 := ConcreteCategory.congr_hom
    (congrArg (fun φ : pullback (cstV N E) (PGL.pr N) ⟶ ofCat (glCat N) => (φ.app n).app U) (pullback.condition (f := cstV N E) (g := PGL.pr N))) x
  have e : ((Functor.const (Fin (n.unop.len + 1))).obj (SingleObj.star (GL (Fin N) Γ(U.unop, ⊤))) :
      ComposableArrows (SingleObj (GL (Fin N) Γ(U.unop, ⊤))) n.unop.len) =
      (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x : ComposableArrows (Um N Γ(U.unop, ⊤)) n.unop.len) ⋙
        Um.toGL N Γ(U.unop, ⊤) := e0
  have := Functor.congr_hom e.symm h
  exact this.trans ((Category.id_comp _).trans (Category.comp_id _))

def fMap (N : ℕ) (E : Spc) : pullback (cstV N E) (PGL.pr N) ⟶ Pj N 0 where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        (conv (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) (pb_gl x) : ComposableArrows (Vec N 0 U.unop) n.unop.len)
      naturality := fun U U' g => by
        ext x
        have e1 : (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U' (((pullback (cstV N E) (PGL.pr N)).obj n).map g x) :
            ComposableArrows (Um N Γ(U'.unop, ⊤)) n.unop.len) =
            ((PGL N).obj n).map g (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) :=
          ConcreteCategory.congr_hom (((pullback.snd (cstV N E) (PGL.pr N)).app n).naturality g) x
        refine (conv_congr e1 (pb_gl _) (by intro i j h; rw [← e1]; exact pb_gl _ h)).trans ?_
        exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl)) }
  naturality n m f := by
    ext U x
    have e1 : (((pullback.snd (cstV N E) (PGL.pr N)).app m).app U (((pullback (cstV N E) (PGL.pr N)).map f).app U x) :
        ComposableArrows (Um N Γ(U.unop, ⊤)) m.unop.len) =
        ((PGL N).map f).app U (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) :=
      ConcreteCategory.congr_hom (congrArg (fun φ : (pullback (cstV N E) (PGL.pr N)).obj n ⟶ (PGL N).obj m => φ.app U) ((pullback.snd (cstV N E) (PGL.pr N)).naturality f)) x
    refine (conv_congr e1 (pb_gl _) (by intro i j h; rw [← e1]; exact pb_gl _ h)).trans ?_
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl))

def back {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n where
  obj i := ⟨(w.obj i).1, basic_um _ (w.obj i).2⟩
  map h := ⟨(1, (w.map h).1), by funext k; simpa using (w.map h).2 k⟩
  map_id i := Subtype.ext (Prod.ext rfl (congrArg Subtype.val (w.map_id i)))
  map_comp f g := Subtype.ext (Prod.ext (one_mul 1).symm (congrArg Subtype.val (w.map_comp f g)))

theorem back_conv {A : Type} [CommRing A] {N n : ℕ} (c : ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n)
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1) : back (conv c hc) = c :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ h => heq_of_eq (Subtype.ext (Prod.ext (hc h).symm rfl)))

theorem conv_back {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    conv (back w) (fun _ => rfl) = w :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl))

theorem back_gl {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    ((Functor.const (Fin (n + 1))).obj (SingleObj.star (GL (Fin N) Γ(Spec (CommRingCat.of A), ⊤))) :
      ComposableArrows (SingleObj (GL (Fin N) Γ(Spec (CommRingCat.of A), ⊤))) n) = back w ⋙ Um.toGL N _ :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

theorem conv_inj {A : Type} [CommRing A] {N n : ℕ} {c c' : ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n}
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1)
    (hc' : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c'.map h).1.1 = 1) (e : conv c hc = conv c' hc') : c = c' :=
  (back_conv c hc).symm.trans ((congrArg back e).trans (back_conv c' hc'))

theorem fMap_line (N : ℕ) (E : Spc) : fMap N E ≫ Pj.line N 0 = pullback.snd (cstV N E) (PGL.pr N) ≫ PGL.line N := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

theorem eMap_bij (N : ℕ) (R : Type) [CommRing R] (n : ℕ) (A : Type) [CommRing A] : Function.Bijective
      (fun x : Sx (pullback (cstV N (sp R)) (PGL.pr N)) n (Spec (CommRingCat.of A)) =>
        ((prod.lift (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)) : _ ⟶ PR N 0 R).app
          (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x) := by
  have k1 := fun z => ConcreteCategory.congr_hom (congrArg (fun φ : pullback (cstV N (sp R)) (PGL.pr N) ⟶ Pj N 0 =>
        (φ.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A)))) (prod.lift_fst (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)))) z
  have k2 := fun z => ConcreteCategory.congr_hom (congrArg (fun φ : pullback (cstV N (sp R)) (PGL.pr N) ⟶ sp R =>
        (φ.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A)))) (prod.lift_snd (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)))) z
  constructor
  · intro x y hxy
    apply pb_ext
    · exact (k2 x).symm.trans ((congrArg _ hxy).trans (k2 y))
    · exact conv_inj (pb_gl x) (pb_gl y) ((k1 x).symm.trans ((congrArg _ hxy).trans (k1 y)))
  · intro z
    obtain ⟨x, hx1, hx2⟩ := pb_mk (cstV N (sp R)) (PGL.pr N) (n := n) (U := Spec (CommRingCat.of A))
      (((prod.snd : PR N 0 R ⟶ _).app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) z)
      (back (((prod.fst : PR N 0 R ⟶ _).app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) z))
      (back_gl _)
    refine ⟨x, pr_ext _ _ ?_ ?_⟩
    · exact (k1 x).trans ((conv_congr hx2 (pb_gl x) (fun _ => rfl)).trans (conv_back _))
    · exact (k2 x).trans hx1

theorem LeafPBMap_of : LeafPBMap := fun N R _ =>
  ⟨cstV N (sp R), prod.lift (fMap N (sp R)) (pullback.fst _ _), prod.lift_snd _ _,
    by rw [prod.lift_fst_assoc]; exact fMap_line N (sp R), fun n A _ => eMap_bij N R n A⟩

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPfQuot
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem quotC_bij (d : ℕ) (R : Type) [CommRing R] :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)))).comp
      MvPolynomial.C) := by
  have hJ : Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R) = MvPolynomial.X '' Set.univ := Set.image_univ.symm
  constructor
  · rw [injective_iff_map_eq_zero]
    intro r hr
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hJ, MvPolynomial.mem_ideal_span_X_image] at hr
    by_contra h
    obtain ⟨i, -, hi⟩ := hr 0 (by rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C, if_pos rfl]; exact h)
    exact hi rfl
  · intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPolynomial.constantCoeff p, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq, hJ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push_neg at hcon
    have : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ i)
    subst this
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl,
      ← MvPolynomial.constantCoeff_eq, sub_self] at hm
    exact hm rfl

theorem leafAffQuot_pf : LeafAffQuot := by
  intro hQ d R B C _ _ _ ψ η hψ I K hη hK hI
  subst hK
  have hJI : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ = I := by
    rw [Ideal.map_span, ← Set.range_comp]; exact hI
  subst hJI
  have b2 := hψ.2
  have b3 := hQ B C η _ hη
  have e : (Ideal.Quotient.mk _).comp (η.comp (ψ.comp MvPolynomial.C)) =
      ((Ideal.quotientMap _ η Ideal.le_comap_map).comp (Ideal.quotientMap _ ψ Ideal.le_comap_map)).comp
        ((Ideal.Quotient.mk (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)))).comp
          MvPolynomial.C) := by
    ext r; simp [Ideal.quotientMap_mk]
  rw [e]
  exact (b3.comp b2).comp (quotC_bij d R)

theorem LeafPrdAff_of' (hT : LeafThom) (hA : LeafActNat) (h1 : LeafHensH) (h3 : LeafExcAff)
    (hQ : LeafQuot) (hI : LeafIndExc) : LeafPrdAff :=
  LeafPrdAff_of hT hA h1 leafAffQuot_pf h3 hQ hI

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPurProjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurProjPf

open PurPf

def HsCast {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) : Hs q P N' I' := by
  subst hN; subst hI; exact x

theorem HsCast_val {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) :
    (HsCast hN hI x).1 = Ht.cast hN hI x.1 := by
  subst hN; subst hI; rfl

theorem HsCast_pull {q : ℕ} {P' P : Arrow Spc} (φ : P' ⟶ P) {N N' I I' : ℤ} (hN : N = N') (hI : I = I')
    (x : Hs q P N I) : Hs.pull q φ N' I' (HsCast hN hI x) = HsCast hN hI (Hs.pull q φ N I x) := by
  subst hN; subst hI; rfl

theorem HsCast_fgt {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) :
    Hs.fgt q P N' I' (HsCast hN hI x) = Ht.cast hN hI (Hs.fgt q P N I x) := by
  subst hN; subst hI; rfl

theorem act_val (hA : DivisorNaturality) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m i j : ℤ} (a : Ht q P.right n i)
    (b : Hs q P m j) : (Hs.act q a b).1 = cup q (pull _ (dbl.fold P) _ n a) b.1 := by
  have hb : pull _ (dbl.inr P) (tw q j) m b.1 = 0 := b.2
  change cup q (pull _ (dbl.fold P) _ n a) b.1 -
    pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1)) = _
  rw [(hA q).1, hb]
  simp only [map_zero, sub_zero]

theorem act_cup (hA : DivisorNaturality) (hR : DivisorRingCompatibility) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m k i j l : ℤ}
    (x : Ht q P.right n i) (y : Ht q P.right m j) (c : Hs q P k l) :
    Hs.act q (cup q x y) c = HsCast (by ring) (by ring) (Hs.act q x (Hs.act q y c)) := by
  apply Subtype.ext
  rw [HsCast_val, act_val hA, act_val hA, act_val hA, (hA q).1, (hR q _).2.1]

theorem fgt_act (hA : DivisorNaturality) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m i j : ℤ} (a : Ht q P.right n i)
    (s : Hs q P m j) : Hs.fgt q P _ _ (Hs.act q a s) = cup q a (Hs.fgt q P m j s) := by
  change pull _ (dbl.inl P) _ _ (Hs.act q a s).1 = cup q a (pull _ (dbl.inl P) _ _ s.1)
  rw [act_val hA, (hA q).1, ← pull_comp, show dbl.inl P ≫ dbl.fold P = 𝟙 _ from pushout.inl_desc _ _ _, pull_id]

theorem purT_char {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (x : Ht q (sch.obj P.Z) n i) : ∃ e : Ht q (T P).E n i,
      pull _ (pullback.fst (T P).π (sch.map P.ι)) _ _ e = pull _ (pullback.snd (T P).π (sch.map P.ι)) _ _ x ∧
      Hs.pull q (abvMap P.U (T P).π) _ _ (purT T q P n i x) =
        Hs.act q (P := abv P.U (T P).π) e (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P)) := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  refine ⟨(AddEquiv.ofBijective _ (((T P).ok q hq).1 i n)).symm
    (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n x), ?_, ?_⟩
  · exact AddEquiv.ofBijective_apply_symm_apply _ (((T P).ok q hq).1 i n)
  · unfold purT
    rw [dif_pos h]
    exact AddEquiv.ofBijective_apply_symm_apply _ (((T P).ok q hq).2.2.1 (n + 2 * d) (i + d))

end PurProjPf

open PurPf PurProjPf

theorem LeafPurProj_of : EtalePurityProjection := by
  intro hH d T q _ P hq n m i j a b
  have hA : DivisorNaturality := hH.2.2.2.2.1
  have hR : DivisorRingCompatibility := hH.2.2.2.2.2.1
  obtain ⟨eb, heb1, heb2⟩ := purT_char T q P hq m j b
  obtain ⟨ex, hex1, hex2⟩ := purT_char T q P hq (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)
  have hex : ex = cup q (pull (ZMod q) (T P).π (tw q i) n a) eb := by
    apply (((T P).ok q hq).1 (i + j) (n + m)).1
    rw [hex1, (hA q).1, (hA q).1, heb1, ← pull_comp, ← pull_comp, pullback.condition]
  have hN : n + (m + 2 * (d : ℤ)) = n + m + 2 * d := by ring
  have hI : i + (j + (d : ℤ)) = i + j + d := by ring
  have key : purT T q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b) =
      HsCast hN hI (Hs.act q (P := opn P.U) (n := n) (i := i) a (purT T q P m j b)) := by
    apply (((T P).ok q hq).2.2.1 (n + m + 2 * d) (i + j + d)).1
    rw [hex2, hex, HsCast_pull]
    refine (act_cup hA hR q (P := abv P.U (T P).π) (pull (ZMod q) (T P).π (tw q i) n a) eb
      (Hs.pull q (abvMap P.U (T P).π) (2 * d) d (fcl d q P))).trans ?_
    rw [TubeCut.LeafActNat_of hA q _ _ (abvMap P.U (T P).π) n (m + 2 * d) i (j + d) a (purT T q P m j b), heb2]
    rfl
  rw [key, HsCast_fgt]
  exact congrArg (Ht.cast hN hI) (fgt_act hA q (P := opn P.U) a (purT T q P m j b))

end LateralTheory.CohomologicalPurity
end
end

