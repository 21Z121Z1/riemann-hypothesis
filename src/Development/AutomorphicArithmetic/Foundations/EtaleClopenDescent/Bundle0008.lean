import Mathlib
import Development.EtaleCohomology.EtaleSheaves.Bundle0082

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NeighbourhoodShrinkingOfObstructionExactNatural
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.MorphismProjectionLaws
open LateralTheory.E.E4 LateralTheory.E.EtaleTopologySheaves LateralTheory.E.SecondDegreeKilling LateralTheory.E.Bridge_yfiPf

variable {B W Y S T T' T'' : Scheme.{0}}

private def mY (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    pullback p u ⟶ pullback p u' :=
  pullback.map p u p u' (𝟙 Y) f (𝟙 B) (by simp) (by simp [h])

private lemma mY_snd (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mY p u u' f h ≫ pullback.snd p u' = pullback.snd p u ≫ f :=
  pullback.lift_snd _ _ _

private lemma mY_fst (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mY p u u' f h ≫ pullback.fst p u' = pullback.fst p u := by
  unfold mY pullback.map
  erw [pullback.lift_fst]
  exact Category.comp_id _

private lemma mY_comp (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (u'' : T'' ⟶ B) (f : T ⟶ T') (g : T' ⟶ T'')
    (k : T ⟶ T'') (h : f ≫ u' = u) (h' : g ≫ u'' = u') (hk : k ≫ u'' = u) (e : f ≫ g = k) :
    mY p u u' f h ≫ mY p u' u'' g h' = mY p u u'' k hk := by
  apply pullback.hom_ext
  · rw [Category.assoc, mY_fst, mY_fst, mY_fst]
  · rw [Category.assoc, mY_snd, reassoc_of% mY_snd, mY_snd, e]

private lemma mY_id (p : Y ⟶ B) (u : T ⟶ B) (h : 𝟙 T ≫ u = u) : mY p u u (𝟙 T) h = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mY_fst, Category.id_comp]
  · rw [mY_snd, Category.comp_id, Category.id_comp]

private def mW (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    pullback (pullback.snd p u ≫ u) ι ⟶ pullback (pullback.snd p u' ≫ u') ι :=
  pullback.map _ _ _ _ (mY p u u' f h) (𝟙 W) (𝟙 B)
    (by rw [Category.comp_id, reassoc_of% (mY_snd p u u' f h), h]) (by simp)

private lemma mW_fst (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mW p ι u u' f h ≫ pullback.fst _ ι = pullback.fst _ ι ≫ mY p u u' f h :=
  pullback.lift_fst _ _ _

private lemma mW_snd (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mW p ι u u' f h ≫ pullback.snd _ ι = pullback.snd _ ι :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private lemma mW_comp (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (u'' : T'' ⟶ B) (f : T ⟶ T')
    (g : T' ⟶ T'') (k : T ⟶ T'') (h : f ≫ u' = u) (h' : g ≫ u'' = u') (hk : k ≫ u'' = u) (e : f ≫ g = k) :
    mW p ι u u' f h ≫ mW p ι u' u'' g h' = mW p ι u u'' k hk := by
  apply pullback.hom_ext
  · simp only [Category.assoc, mW_fst, reassoc_of% mW_fst]
    rw [mY_comp p u u' u'' f g k h h' hk e]
  · simp only [Category.assoc, mW_snd]

private lemma mW_id (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (h : 𝟙 T ≫ u = u) : mW p ι u u (𝟙 T) h = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mW_fst, mY_id, Category.id_comp, Category.comp_id]
  · rw [mW_snd, Category.id_comp]

private lemma a_w {U U' : B.Etale} (a : U' ⟶ U) : a.left ≫ U.hom = U'.hom := by
  simpa using a.w

private lemma resY_comp (p : Y ⟶ B) {U U' U'' : B.Etale} (b : U'' ⟶ U') (a : U' ⟶ U) :
    resY p (b ≫ a) = resY p b ≫ resY p a := by
  have hY : ∀ {V V' : B.Etale} (c : V' ⟶ V), resY p c = mY p _ _ c.left (a_w c) := fun _ => rfl
  rw [hY (b ≫ a), hY b, hY a]
  exact (mY_comp p _ _ _ _ _ _ _ _ _ rfl).symm

private lemma resYW_comp (p : Y ⟶ B) (ι : W ⟶ B) {U U' U'' : B.Etale} (b : U'' ⟶ U') (a : U' ⟶ U) :
    resYW p ι (b ≫ a) = resYW p ι b ≫ resYW p ι a := by
  have hW : ∀ {V V' : B.Etale} (c : V' ⟶ V), resYW p ι c = mW p ι _ _ c.left (a_w c) := fun _ => rfl
  rw [hW (b ≫ a), hW b, hW a]
  exact (mW_comp p ι _ _ _ _ _ _ _ _ _ rfl).symm

private lemma tY_res (p : Y ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (t : S ⟶ U'.left)
    (h : 𝟙 S ≫ t ≫ U'.hom = (t ≫ a.left) ≫ U.hom) :
    mY p _ _ (𝟙 S) h ≫ tY p U' t ≫ resY p a = tY p U (t ≫ a.left) := by
  have hY : resY p a = mY p _ _ a.left (a_w a) := rfl
  have hT : ∀ {V : B.Etale} (s : S ⟶ V.left), tY p V s = mY p _ _ s rfl := fun _ => rfl
  have h1 : (t ≫ a.left) ≫ U.hom = t ≫ U'.hom := by rw [Category.assoc, a_w]
  rw [hY, hT, hT, mY_comp p _ _ _ t a.left (t ≫ a.left) _ _ h1 rfl,
    mY_comp p _ _ _ (𝟙 S) (t ≫ a.left) (t ≫ a.left) _ _ rfl (Category.id_comp _)]

private lemma tW_res (p : Y ⟶ B) (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (t : S ⟶ U'.left)
    (h : 𝟙 S ≫ t ≫ U'.hom = (t ≫ a.left) ≫ U.hom) :
    mW p ι _ _ (𝟙 S) h ≫ tW p ι U' t ≫ resYW p ι a = tW p ι U (t ≫ a.left) := by
  have hW : resYW p ι a = mW p ι _ _ a.left (a_w a) := rfl
  have hT : ∀ {V : B.Etale} (s : S ⟶ V.left), tW p ι V s = mW p ι _ _ s rfl := fun _ => rfl
  have h1 : (t ≫ a.left) ≫ U.hom = t ≫ U'.hom := by rw [Category.assoc, a_w]
  rw [hW, hT, hT, mW_comp p ι _ _ _ t a.left (t ≫ a.left) _ _ h1 rfl,
    mW_comp p ι _ _ _ (𝟙 S) (t ≫ a.left) (t ≫ a.left) _ _ rfl (Category.id_comp _)]

private lemma pull_left (q : ℕ) (i n : ℤ) {X Z : Scheme.{0}} (f : X ⟶ Z) (g : Z ⟶ X) (h : f ≫ g = 𝟙 X)
    (y : Ht q (sch.obj X) n i) :
    pull (ZMod q) (sch.map f) (tw q i) n (pull (ZMod q) (sch.map g) (tw q i) n y) = y := by
  rw [← pull_comp, ← sch.map_comp, h, sch.map_id, pull_id]

private lemma pull_zero (q : ℕ) (i n : ℤ) {X Z : Scheme.{0}} (f : X ⟶ Z) (g : Z ⟶ X) (h : g ≫ f = 𝟙 Z)
    (y : Ht q (sch.obj Z) n i) (hy : pull (ZMod q) (sch.map f) (tw q i) n y = 0) : y = 0 := by
  rw [← pull_left q i n g f h y, hy, map_zero]

private lemma shrink (q : ℕ) (i : ℤ) (p : Y ⟶ B) (ι : W ⟶ B) (U U' : B.Etale) (a : U' ⟶ U) (m : ℤ)
    (u' : U'.left) (S : Sys q i p ι U' m u') : Nonempty (Sys q i p ι U m (a.left u')) := by
  have hu : 𝟙 _ ≫ S.t ≫ U'.hom = (S.t ≫ a.left) ≫ U.hom := by
    rw [Category.id_comp, Category.assoc, a_w]
  have hu' : 𝟙 _ ≫ (S.t ≫ a.left) ≫ U.hom = S.t ≫ U'.hom := by
    rw [Category.id_comp, Category.assoc, a_w]
  have eY1 : mY p _ _ (𝟙 _) hu ≫ mY p _ _ (𝟙 _) hu' = 𝟙 _ := by
    rw [mY_comp p _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mY_id]
  have eY2 : mY p _ _ (𝟙 _) hu' ≫ mY p _ _ (𝟙 _) hu = 𝟙 _ := by
    rw [mY_comp p _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mY_id]
  have eW1 : mW p ι _ _ (𝟙 _) hu ≫ mW p ι _ _ (𝟙 _) hu' = 𝟙 _ := by
    rw [mW_comp p ι _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mW_id]
  have eW2 : mW p ι _ _ (𝟙 _) hu' ≫ mW p ι _ _ (𝟙 _) hu = 𝟙 _ := by
    rw [mW_comp p ι _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mW_id]
  have pc : ∀ {X1 X2 X3 : Scheme.{0}} (f : X1 ⟶ X2) (g : X2 ⟶ X3) (n : ℤ) (y : Ht q (sch.obj X3) n i),
      pull (ZMod q) (sch.map (f ≫ g)) (tw q i) n y =
        pull (ZMod q) (sch.map f) (tw q i) n (pull (ZMod q) (sch.map g) (tw q i) n y) := by
    intro X1 X2 X3 f g n y
    rw [CategoryTheory.Functor.map_comp, pull_comp]
  letI := S.cat
  letI := S.ring
  haveI := S.filt
  refine ⟨Sys.mk S.J S.V (fun j => S.a j ≫ a) ?_ S.tr S.tr_id S.tr_comp ?_ S.A S.sh
    (S.t ≫ a.left) (fun j => mY p _ _ (𝟙 _) hu ≫ S.gY j) (fun j => mW p ι _ _ (𝟙 _) hu ≫ S.gW j)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro j
    obtain ⟨v, hv⟩ := S.mem j
    exact ⟨v, congrArg (fun z => a.left z) hv⟩
  · intro j k f
    rw [← Category.assoc, S.tr_a]
  · intro j
    show pullback.fst _ ι ≫ mY p _ _ (𝟙 _) hu ≫ S.gY j = (mW p ι _ _ (𝟙 _) hu ≫ S.gW j) ≫ _
    rw [← reassoc_of% (mW_fst p ι _ _ (𝟙 _) hu)]
    exact (congrArg (fun z => mW p ι _ _ (𝟙 _) hu ≫ z) (S.sq j)).trans (Category.assoc _ _ _).symm
  · intro j
    rw [resY_comp]
    refine (Category.assoc _ _ _).trans ?_
    rw [reassoc_of% (S.gY_a j)]
    exact tY_res p a S.t hu
  · intro j
    rw [resYW_comp]
    refine (Category.assoc _ _ _).trans ?_
    rw [reassoc_of% (S.gW_a j)]
    exact tW_res p ι a S.t hu
  · intro j k f
    refine (Category.assoc _ _ _).trans ?_
    rw [S.gY_tr]
  · intro j k f
    refine (Category.assoc _ _ _).trans ?_
    rw [S.gW_tr]
  · intro j y hy
    apply S.injY j y
    exact pull_zero q i m (mY p _ _ (𝟙 _) hu) (mY p _ _ (𝟙 _) hu') eY2 _ (by rw [← pc]; exact hy)
  · intro y
    obtain ⟨j, y', hy'⟩ := S.surY (pull (ZMod q) (sch.map (mY p _ _ (𝟙 _) hu')) (tw q i) (m - 1) y)
    refine ⟨j, y', ?_⟩
    rw [pc, hy', pull_left q i (m - 1) _ _ eY1 y]
  · intro j w hw
    apply S.injW j w
    exact pull_zero q i (m - 1) (mW p ι _ _ (𝟙 _) hu) (mW p ι _ _ (𝟙 _) hu') eW2 _
      (by rw [← pc]; exact hw)

end UpperTheory.Cb.MorphismProjectionLaws

theorem UpperTheory.Cb.neighbourhoodShrinking_of_obstructionExact_natural :
    LateralTheory.E.NeighbourhoodKilling.ObsExact → LateralTheory.E.NeighbourhoodKilling.ObsNat → LateralTheory.E.GeoProof.Shrink := by
  intro _ _ q _ i B W Y p ι U U' a m u' S
  exact UpperTheory.Cb.MorphismProjectionLaws.shrink q i p ι U U' a m u' S
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PullbackIsLimitOverFgSubalgebras
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf LateralTheory.E.LeafInclDescendPf
  LateralTheory.E.LeafInclPiecePf

namespace UpperTheory.Cb.PiLocalization₂

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)

private abbrev Lev : Type := {S : Subalgebra k Ω // R ≤ S ∧ S.FG}

private theorem lev_directed : IsDirected (Lev R) (· ≤ ·) :=
  ⟨fun a b ↦ ⟨⟨a.1 ⊔ b.1, a.2.1.trans le_sup_left, a.2.2.sup b.2.2⟩,
    (le_sup_left : a.1 ≤ a.1 ⊔ b.1), (le_sup_right : b.1 ≤ a.1 ⊔ b.1)⟩⟩

private def rings : Lev R ⥤ CommRingCat.{0} where
  obj s := .of s.1
  map {s t} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h : s.1 ≤ t.1)).toRingHom

private def ringsCocone : Cocone (rings R) where
  pt := .of Ω
  ι := { app s := CommRingCat.ofHom (algebraMap s.1 Ω) }

private def ringsIsColimit (hR : R.FG) : IsColimit (ringsCocone R) := by
  classical
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have : Nonempty (Lev R) := ⟨⟨R, le_rfl, hR⟩⟩
  have := lev_directed R
  refine isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun s a b hab ↦ ?_))
  · let x' : Ω := x
    have hx : (Algebra.adjoin k {x'}).FG := ⟨{x'}, by simp⟩
    refine ⟨⟨R ⊔ Algebra.adjoin k {x'}, le_sup_left, hR.sup hx⟩,
      (⟨x', (le_sup_right : Algebra.adjoin k {x'} ≤ R ⊔ Algebra.adjoin k {x'})
        (Algebra.subset_adjoin rfl)⟩ : (R ⊔ Algebra.adjoin k {x'} : Subalgebra k Ω)), rfl⟩
  · exact ⟨s, 𝟙 s, congrArg _ (Subtype.ext hab)⟩

variable {R} in
private theorem lvl_fst {R1 R2 : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R2) (h' : R1 ≤ R2)
    {D : Scheme.{0}} (q : D ⟶ Sp R) : lvl h1 h h' q ≫ pullback.fst q (incl h1) = pullback.fst q (incl h) :=
  pullback.lift_fst _ _ _

variable {R} in
private theorem lvl_snd {R1 R2 : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R2) (h' : R1 ≤ R2)
    {D : Scheme.{0}} (q : D ⟶ Sp R) :
    lvl h1 h h' q ≫ pullback.snd q (incl h1) = pullback.snd q (incl h) ≫ incl h' :=
  pullback.lift_snd _ _ _

variable {R} in
private theorem lvl_isPullback {R1 R2 : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R2) (h' : R1 ≤ R2)
    {D : Scheme.{0}} (q : D ⟶ Sp R) :
    IsPullback (lvl h1 h h' q) (pullback.snd q (incl h)) (pullback.snd q (incl h1)) (incl h') := by
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h1)) (v₁₃ := q) (h₂₂ := incl h1) ?_
    (lvl_snd h1 h h' q) (IsPullback.of_hasPullback q (incl h1))
  rw [lvl_fst, incl_comp h1 h h']
  exact IsPullback.of_hasPullback q (incl h)

variable {D : Scheme.{0}} (q : D ⟶ Sp R)

private def stages : (Lev R)ᵒᵖ ⥤ Scheme.{0} where
  obj s := pullback q (incl s.unop.2.1)
  map {s t} h := lvl t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q
  map_id s := by
    apply pullback.hom_ext
    · rw [lvl_fst, Category.id_comp]
    · rw [lvl_snd, Category.id_comp]
      exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)
  map_comp {s t u} f g := by
    apply pullback.hom_ext
    · rw [lvl_fst, Category.assoc, lvl_fst, lvl_fst]
    · rw [lvl_snd, Category.assoc, lvl_snd, ← Category.assoc, lvl_snd, Category.assoc,
        incl_comp (leOfHom g.unop : u.unop.1 ≤ t.unop.1) (leOfHom (f ≫ g).unop : u.unop.1 ≤ s.unop.1)
          (leOfHom f.unop : t.unop.1 ≤ s.unop.1)]

private def toBase : stages R q ⟶ (rings R).op ⋙ Scheme.Spec where
  app s := pullback.snd q (incl s.unop.2.1)
  naturality s t h := lvl_snd t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q

variable {R q} in

private def stagesCone {Y : Scheme.{0}} {g : Y ⟶ Sp Ω} {v : Y ⟶ D} (w : v ≫ q = g ≫ toR R) :
    Cone (stages R q) where
  pt := Y
  π :=
    { app s := bcLift s.unop.2.1 w
      naturality s t h := (Category.id_comp _).trans
        (bcLift_lvl t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) w).symm }

variable {R q} in

private def stagesIsLimit (hR : R.FG) {Y : Scheme.{0}} {g : Y ⟶ Sp Ω} {v : Y ⟶ D}
    (hp : IsPullback v g q (toR R)) : IsLimit (stagesCone hp.w) := by
  classical
  have : Nonempty (Lev R) := ⟨⟨R, le_rfl, hR⟩⟩
  have := lev_directed R
  have : IsFiltered (Lev R) := isFiltered_of_directed_le_nonempty _
  have : IsConnected (Lev R)ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfIsPullbackOfIsConnected (toBase R q) (stagesCone hp.w)
    (Scheme.Spec.mapCone (ringsCocone R).op)
    { hom := g
      w s := (pullback.lift_snd _ _ _).symm }
    (fun s ↦ bcLift_isPullback s.unop.2.1 hp)
    (isLimitOfPreserves Scheme.Spec (ringsIsColimit R hR).op)

private def stagesToConstantSpec : stages R q ⟶ (Functor.const _).obj (Sp R) where
  app s := pullback.fst q (incl s.unop.2.1) ≫ q
  naturality s t h := by
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact (lvl_fst t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q) =≫ q |>.trans rfl |> fun e ↦ by
      simpa [stages] using e

variable {R q} in

private theorem factor (hR : R.FG) (hq : FP q) {Y Z : Scheme.{0}} {g : Y ⟶ Sp Ω} {v : Y ⟶ D}
    (hp : IsPullback v g q (toR R)) (qZ : Z ⟶ Sp R) (hZ : LocallyOfFinitePresentation qZ)
    (a : Y ⟶ Z) (ha : a ≫ qZ = v ≫ q) :
    ∃ (R1 : Subalgebra k Ω) (h1 : R ≤ R1), R1.FG ∧ ∃ u : pullback q (incl h1) ⟶ Z,
      bcLift h1 hp.w ≫ u = a ∧ u ≫ qZ = pullback.fst q (incl h1) ≫ q := by
  classical
  have : Nonempty (Lev R) := ⟨⟨R, le_rfl, hR⟩⟩
  have := lev_directed R
  have : IsFiltered (Lev R) := isFiltered_of_directed_le_nonempty _
  have i1 : ∀ {s t : (Lev R)ᵒᵖ} (h : s ⟶ t), IsAffineHom ((stages R q).map h) := fun {s t} h ↦
    MorphismProperty.of_isPullback
      (lvl_isPullback t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q).flip inferInstance
  have i2 : ∀ s : (Lev R)ᵒᵖ, CompactSpace ((stages R q).obj s) := fun s ↦ by
    have h : QuasiCompact (pullback.snd q (incl s.unop.2.1)) := (fp_snd q (incl s.unop.2.1) hq).2.1
    change CompactSpace ↥(pullback q (incl s.unop.2.1))
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd q (incl s.unop.2.1))
  have i3 : ∀ s : (Lev R)ᵒᵖ, QuasiSeparatedSpace ((stages R q).obj s) := fun s ↦
    (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd q (incl s.unop.2.1))).mp
      (fp_snd q (incl s.unop.2.1) hq).2.2
  obtain ⟨s, u, h₁, h₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (stages R q) (stagesToConstantSpec R q) qZ (stagesCone hp.w) (stagesIsLimit hR hp) a (by
      refine NatTrans.ext (funext fun s ↦ ?_)
      change bcLift s.unop.2.1 hp.w ≫ pullback.fst q (incl s.unop.2.1) ≫ q = a ≫ qZ
      rw [ha]
      exact pullback.lift_fst_assoc _ _ _ _)
  exact ⟨s.unop.1, s.unop.2.1, s.unop.2.2, u, h₁, h₂⟩

end UpperTheory.Cb.PiLocalization₂

theorem UpperTheory.Cb.pullback_isLimit_over_fg_subalgebras :
    LateralTheory.E.LeafInclPiecePf.LeafInclMap := by
  intro k _ Ω _ _ X f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW
  obtain ⟨R1, h1, hR1, u, hu, hu'⟩ := UpperTheory.Cb.PiLocalization₂.factor hR hqW hW qU hqU.1 (X.homOfLE hWU ≫ vU) (by
    rw [Category.assoc, hU.w, hW.w]
    simp only [Category.assoc, Scheme.homOfLE_ι_assoc])
  refine ⟨R1, h1, hR1, pullback.lift u (pullback.snd qW (incl h1)) ?_, pullback.lift_snd _ _ _, ?_⟩
  · rw [hu', pullback.condition]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hu, Category.assoc]
      unfold bcLift
      rw [pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc]
      unfold bcLift
      rw [pullback.lift_snd, pullback.lift_snd]
      simp only [Category.assoc, Scheme.homOfLE_ι_assoc]

end
end

