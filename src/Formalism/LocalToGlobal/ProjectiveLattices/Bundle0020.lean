import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.GenSpecRel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace Formalism.L2.Pj.GSR

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Corr

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : IsGrpPullback G' G f F) {k : Type} [CommRing k] (tk : Spec (CommRingCat.of k) ⟶ S') (g : Spec (CommRingCat.of k) ⟶ S)
  (hg : tk ≫ f = g)

abbrev viaT (X : Over (Spec (CommRingCat.of k))) : Over S' := Over.mk (X.hom ≫ tk)

def Rel {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) : Prop :=
  w.left ≫ F = v.left ≫ pullback.fst G.hom g

def liftT {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) : viaT tk Y ⟶ viaT tk X :=
  Over.homMk φ.left (by
    show φ.left ≫ X.hom ≫ tk = Y.hom ≫ tk
    rw [← Category.assoc, Over.w φ])

variable {tk g}

theorem one_left' {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  exact ReciprocityTheory.ChartRestriction.G.Chart.one_left'

theorem comp_one'' {T : Scheme.{0}} {X Y M : Over T} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  ext
  rw [Over.comp_left, Formalism.L2.Pj.GSR.one_left', Formalism.L2.Pj.GSR.one_left', ← Category.assoc, Over.w u]

include hc in
theorem rel_uniq_w {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v) : w = w' := by
  have e : w.left ≫ F = w'.left ≫ F :=
    (h : w.left ≫ F = _).trans (h' : w'.left ≫ F = _).symm
  exact Over.OverMorphism.ext (hc.1.hom_ext e (by rw [Over.w w, Over.w w']))

theorem rel_uniq_v {X : Over (Spec (CommRingCat.of k))} {w : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w v') : v = v' := by
  have e : v.left ≫ pullback.fst G.hom g = v'.left ≫ pullback.fst G.hom g :=
    (h : _ = v.left ≫ pullback.fst G.hom g).symm.trans (h' : _ = v'.left ≫ pullback.fst G.hom g)
  refine Over.OverMorphism.ext (pullback.hom_ext e ?_)
  have hv : v.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v
  have hv' : v'.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v'
  rw [hv, hv']

include hc hg in
theorem rel_exists_w {X : Over (Spec (CommRingCat.of k))} (v : X ⟶ (Over.pullback g).obj G) :
    ∃ w : viaT tk X ⟶ G', Rel (F := F) tk g w v := by
  have hv : v.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v
  have cond : (v.left ≫ pullback.fst G.hom g) ≫ G.hom = (X.hom ≫ tk) ≫ f := by
    rw [Category.assoc, pullback.condition, reassoc_of% hv, Category.assoc, hg]
  exact ⟨Over.homMk (hc.1.lift _ _ cond) (hc.1.lift_snd _ _ cond), hc.1.lift_fst _ _ cond⟩

include hc hg in
theorem rel_exists_v {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') :
    ∃ v : X ⟶ (Over.pullback g).obj G, Rel (F := F) tk g w v := by
  have hw : w.left ≫ G'.hom = X.hom ≫ tk := Over.w w
  have cond : (w.left ≫ F) ≫ G.hom = X.hom ≫ g := by
    rw [Category.assoc, hc.1.w, reassoc_of% hw, hg]
  exact ⟨Over.homMk (pullback.lift _ _ cond) (pullback.lift_snd _ _ cond), (pullback.lift_fst _ _ cond).symm⟩

def iota2 (hg : tk ≫ f = g) (X : Over (Spec (CommRingCat.of k))) :
    Over.mk (X.hom ≫ g) ⟶ Over.mk ((viaT tk X).hom ≫ f) :=
  Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (X.hom ≫ tk) ≫ f = X.hom ≫ g
    rw [Category.id_comp, Category.assoc, hg])

theorem rel_iff {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) :
    Rel (F := F) tk g w v ↔
      pushPt (isGrpPullback_pullback G g).1.w v = iota2 hg X ≫ pushPt hc.1.w w := by
  constructor
  · intro h
    ext
    simp only [pushPt, iota2, Over.comp_left, Over.homMk_left, Category.id_comp]
    exact (h : w.left ≫ F = _).symm
  · intro h
    have e : (pushPt (isGrpPullback_pullback G g).1.w v).left = (iota2 hg X ≫ pushPt hc.1.w w).left := by
      rw [h]
    simp only [pushPt, iota2, Over.comp_left, Over.homMk_left, Category.id_comp] at e
    exact e.symm

include hc hg in
theorem rel_mul {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v') : Rel (F := F) tk g (w * w') (v * v') := by
  rw [Formalism.L2.Pj.GSR.rel_iff hc hg] at h h' ⊢
  have e1 := map_mul (pushHom (isGrpPullback_pullback G g) X) v v'
  have e2 := map_mul ((preHom (iota2 hg X)).comp (pushHom hc (viaT tk X))) w w'
  exact e1.trans ((congrArg₂ (· * ·) h h').trans e2.symm)

include hc hg in
theorem rel_one {X : Over (Spec (CommRingCat.of k))} : Rel (F := F) tk g (1 : viaT tk X ⟶ G') (1 : X ⟶ (Over.pullback g).obj G) := by
  rw [Formalism.L2.Pj.GSR.rel_iff hc hg]
  exact (map_one (pushHom (isGrpPullback_pullback G g) X)).trans
    (map_one ((preHom (iota2 hg X)).comp (pushHom hc (viaT tk X)))).symm

include hc hg in
theorem rel_prod : ∀ {N : ℕ} {X : Over (Spec (CommRingCat.of k))} (u : Fin N → (viaT tk X ⟶ G'))
    (u' : Fin N → (X ⟶ (Over.pullback g).obj G)), (∀ i, Rel (F := F) tk g (u i) (u' i)) →
    Rel (F := F) tk g (List.ofFn u).prod (List.ofFn u').prod
  | 0, X, u, u', _ => by simpa using rel_one hc hg (X := X)
  | N + 1, X, u, u', h => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    exact rel_mul hc hg (h 0) (rel_prod (fun i => u i.succ) (fun i => u' i.succ) fun i => h i.succ)

theorem rel_pre {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) {w : viaT tk X ⟶ G'}
    {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) : Rel (F := F) tk g (liftT tk φ ≫ w) (φ ≫ v) := by
  show (φ.left ≫ w.left) ≫ F = (φ.left ≫ v.left) ≫ pullback.fst G.hom g
  rw [Category.assoc, Category.assoc, (h : w.left ≫ F = _)]

theorem rel_act (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) {X : Over (Spec (CommRingCat.of k))}
    {w : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) :
    Rel (F := F) tk g (w ≫ a) (v ≫ (Over.pullback g).map b) := by
  have h' : w.left ≫ F = v.left ≫ pullback.fst G.hom g := h
  show (w ≫ a).left ≫ F = (v ≫ (Over.pullback g).map b).left ≫ pullback.fst G.hom g
  first
  | (simp [hab, reassoc_of% h']; erw [pullback.lift_fst])
  | exact ReciprocityTheory.ChartRestriction.G.Chart.rel_act (F := F) a b hab (show ReciprocityTheory.ChartRestriction.G.Chart.Rel (F := F) tk g w v from h)

end Corr

section Count

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f F) {k : Type} [CommRing k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)

include hc in
theorem rel_eq_iff {X : Over (Spec (CommRingCat.of k))} {w₁ w₂ : viaT tk X ⟶ G'} {v₁ v₂ : X ⟶ (Over.pullback g).obj G}
    (h₁ : Rel (F := F) tk g w₁ v₁) (h₂ : Rel (F := F) tk g w₂ v₂) : w₁ = w₂ ↔ v₁ = v₂ := by
  constructor
  · rintro rfl
    exact Formalism.L2.Pj.GSR.rel_uniq_v h₁ h₂
  · rintro rfl
    exact Formalism.L2.Pj.GSR.rel_uniq_w hc h₁ h₂

include hc hg in
theorem tan_iff {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk tk ⟶ G').left ↔ ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := by
  have h1 := rel_pre (spMap (fstD k)) h
  have h2 := rel_one hc hg (X := sp (R₀ := k) k)
  have hid : (sp (R₀ := k) k).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have e1 : (1 : viaT tk (sp (R₀ := k) k) ⟶ G').left = (1 : Over.mk tk ⟶ G').left := by
    rw [one_left', one_left']
    show ((sp (R₀ := k) k).hom ≫ tk) ≫ _ = tk ≫ _
    rw [hid, Category.id_comp]
  rw [ReciprocityTheory.ChartRestriction.G.Chart.IsTan, ← rel_eq_iff hc h1 h2]
  constructor
  · intro e
    apply Over.OverMorphism.ext
    exact e.trans e1.symm
  · intro e
    exact (congrArg (fun q => q.left) e).trans e1

include hc in
theorem eig_iff (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) (s : k)
    {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    (w ≫ a).left = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ w.left ↔ v ≫ (Over.pullback g).map b = spMap (scaleD s) ≫ v := by
  rw [← rel_eq_iff hc (rel_act a b hab h) (rel_pre (spMap (scaleD s)) h)]
  constructor
  · intro e
    exact Over.OverMorphism.ext e
  · intro e
    exact congrArg (fun q => q.left) e

end Count

end Formalism.L2.Pj.GSR
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LieRel
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj.LieRel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tcoord tmap IsUnivChart tvec_tmap tcoord_spec tvec_inj list_prod_tan' tcoord_scale
  tcoord_tvec isTan_tvec isTan_scale tvec_eig_iff scaleD fB Rel liftT viaT rel_exists_w rel_exists_v rel_eq_iff
  rel_prod rel_pre tan_iff eig_iff one_left' sp JetR)

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Vside

variable {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := V) (JetR V (Fin n) m) ⟶ G} (hx : IsUnivChart G n xc)

theorem epsOver_hom : (epsOver V V).hom = (sp (R₀ := V) (DualNumber V)).hom := rfl

def eV : epsOver V V ⟶ sp (R₀ := V) (DualNumber V) :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans epsOver_hom.symm)

def cvV (y : sp (R₀ := V) (DualNumber V) ⟶ G) : epsOver V V ⟶ G := eV ≫ y

theorem cvV_left (y : sp (R₀ := V) (DualNumber V) ⟶ G) : (cvV y).left = y.left := by
  simp [cvV, eV]

theorem cvV_inj {y y' : sp (R₀ := V) (DualNumber V) ⟶ G} (h : cvV y = cvV y') : y = y' :=
  Over.OverMorphism.ext (by rw [← cvV_left y, ← cvV_left y', h])

theorem cvV_prod {m : ℕ} (y : Fin m → (sp (R₀ := V) (DualNumber V) ⟶ G)) :
    (List.ofFn fun i => cvV (y i)).prod = cvV (List.ofFn y).prod := by
  show (List.ofFn fun i => preHom eV (y i)).prod = preHom eV (List.ofFn y).prod
  rw [map_list_prod, List.map_ofFn]
  rfl

theorem isTan_cvV {y : sp (R₀ := V) (DualNumber V) ⟶ G} (h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y) : IsTan (cvV y) := by
  have h' : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD V) ≫ y = 1 := h
  have e : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD V) ≫ y).left =
      (1 : sp (R₀ := V) V ⟶ G).left := by rw [h']
  show spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ (cvV y).left = (1 : ptOver V V ⟶ G).left
  rw [cvV_left]
  exact e

include hx in
theorem tan_eq_cvV {w : epsOver V V ⟶ G} (h : IsTan w) : ∃ c : Fin n → V, w = cvV (tvec (x := xc) c) := by
  let y : sp (R₀ := V) (DualNumber V) ⟶ G := Over.homMk w.left ((Over.w w).trans epsOver_hom)
  have hy : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y := Over.OverMorphism.ext h
  refine ⟨tcoord hx y hy, ?_⟩
  have e : y = tvec (x := xc) (tcoord hx y hy) := by
    first
    | exact tcoord_spec hx y hy
    | exact tcoord_spec y hy
  rw [← e]
  exact Over.OverMorphism.ext (by rw [cvV_left]; rfl)

theorem eigV_iff (e : G ⟶ G) [IsMonHom e] (c : Fin n → V) (z : V) :
    (cvV (tvec (x := xc) c) ≫ e).left = spMap (epsMul z) ≫ (cvV (tvec (x := xc) c)).left ↔ tmap hx e c = z • c := by
  have key : ∀ y : sp (R₀ := V) (DualNumber V) ⟶ G, (cvV y ≫ e).left = (y ≫ e).left := fun y => by
    rw [Over.comp_left, cvV_left, Over.comp_left]
  rw [key, cvV_left, ← tvec_eig_iff hx e c z]
  constructor
  · intro h
    exact Over.OverMorphism.ext h
  · intro h
    rw [h]
    rfl

include hx in
theorem prod_tvec {m : ℕ} (r : Fin m → V) (b : Fin m → Fin n → V) :
    (List.ofFn fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (r i)) ≫ tvec (x := xc) (b i)).prod =
      tvec (x := xc) (∑ i, r i • b i) := by
  have h0 : tvec (x := xc) (0 : Fin n → V) = 1 := by
    have e := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → V) 0
    rw [add_zero] at e
    simpa using e.symm
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx]

include hx in
theorem comb_iff {m : ℕ} (b : Fin m → Fin n → V) (r : Fin m → V) (e : Fin n → V) :
    IsComb (fun i => cvV (tvec (x := xc) (b i))) r (cvV (tvec (x := xc) e)) ↔ e = ∑ i, r i • b i := by
  have hprod : (List.ofFn fun i => cvV (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (r i)) ≫ tvec (x := xc) (b i))).prod =
      cvV (tvec (x := xc) (∑ i, r i • b i)) := by
    rw [cvV_prod, prod_tvec hx]
  constructor
  · rintro ⟨u, hu1, hw⟩
    have hu' : u = fun i => cvV (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (r i)) ≫ tvec (x := xc) (b i)) :=
      funext fun i => Over.OverMorphism.ext (by rw [hu1, cvV_left, cvV_left] <;> rfl)
    rw [hu', hprod] at hw
    first
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (cvV_inj hw)
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj (cvV_inj hw)
  · intro he
    refine ⟨fun i => cvV (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (r i)) ≫ tvec (x := xc) (b i)), fun i => ?_, ?_⟩
    · rw [cvV_left, cvV_left] <;> rfl
    · rw [hprod, he]

end Vside

section Kside

variable {K : Type} [Field K] {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : Sp K ⟶ S) {G' : Over (Sp K)} [GrpObj G']
  {F1 : G'.left ⟶ A.left} (h1 : IsGrpPullback G' A x F1) {V : Type} [CommRing V] [Algebra V K] {G : Over (Sp V)}
  [GrpObj G] {F2 : G'.left ⟶ G.left} (h2 : IsGrpPullback G' G (fB V K) F2)

abbrev epsAt : Over S := Over.mk (spMap (algebraMap K (DualNumber K)) ≫ x)

theorem epsMul_alg (s : K) :
    spMap (epsMul s) ≫ spMap (algebraMap K (DualNumber K)) = spMap (algebraMap K (DualNumber K)) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun a => by simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_alg : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 (Sp K) := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hid : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K :=
    RingHom.ext fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hid, CommRingCat.ofHom_id, Spec.map_id]

def iotaX : epsAt x ⟶ Over.mk ((viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K))).hom ≫ x) :=
  Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ ((sp (R₀ := K) (DualNumber K)).hom ≫ 𝟙 _) ≫ x = spMap (algebraMap K (DualNumber K)) ≫ x
    rw [Category.id_comp, Category.comp_id]; rfl)

def phiX : (viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K)) ⟶ G') →* (epsAt x ⟶ A) :=
  (preHom (iotaX x)).comp (pushHom h1 _)

theorem phiX_left (w : viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K)) ⟶ G') : (phiX x h1 w).left = w.left ≫ F1 := by
  show (iotaX x ≫ pushPt h1.1.w w).left = w.left ≫ F1
  simp [iotaX, pushPt]

def RelA (F1 : G'.left ⟶ A.left) (F2 : G'.left ⟶ G.left) (v : epsAt x ⟶ A)
    (y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G) : Prop :=
  ∃ w : viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K)) ⟶ G', Rel (F := F2) (𝟙 _) (fB V K) w y ∧ v.left = w.left ≫ F1

include h1 h2 in
theorem relA_exists_v (y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G) :
    ∃ v : epsAt x ⟶ A, RelA x F1 F2 v y := by
  obtain ⟨w, hw⟩ := rel_exists_w h2 (Category.id_comp _) y
  exact ⟨phiX x h1 w, w, hw, phiX_left x h1 w⟩

include h1 h2 in
theorem relA_exists_y (v : epsAt x ⟶ A) :
    ∃ y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G, RelA x F1 F2 v y := by
  obtain ⟨w, hw⟩ : ∃ w : viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K)) ⟶ G', v.left = w.left ≫ F1 :=
    ⟨Over.homMk (h1.1.lift v.left (spMap (algebraMap K (DualNumber K))) (by simpa using Over.w v)) (by simp),
      (h1.1.lift_fst _ _ _).symm⟩
  obtain ⟨y, hy⟩ := rel_exists_v h2 (Category.id_comp _) w
  exact ⟨y, w, hy, hw⟩

include h1 h2 in
theorem relA_uniq {v v' : epsAt x ⟶ A} {y y' : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G}
    (h : RelA x F1 F2 v y) (h' : RelA x F1 F2 v' y') : v = v' ↔ y = y' := by
  obtain ⟨w, hwy, hwv⟩ := h
  obtain ⟨w', hwy', hwv'⟩ := h'
  rw [← rel_eq_iff h2 hwy hwy']
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (h1.1.hom_ext (hwv.symm.trans hwv') (by rw [Over.w w, Over.w w']))
  · rintro rfl
    exact Over.OverMorphism.ext (by rw [hwv, hwv'])

include h1 h2 in
theorem relA_prod {N : ℕ} (v : Fin N → (epsAt x ⟶ A)) (y : Fin N → (sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G))
    (h : ∀ i, RelA x F1 F2 (v i) (y i)) : RelA x F1 F2 (List.ofFn v).prod (List.ofFn y).prod := by
  choose w hw hwv using h
  have hv : ∀ i, v i = phiX x h1 (w i) := fun i => Over.OverMorphism.ext (by rw [phiX_left, hwv])
  refine ⟨(List.ofFn w).prod, rel_prod h2 (Category.id_comp _) w y hw, ?_⟩
  rw [← phiX_left x h1, map_list_prod, List.map_ofFn]
  exact congrArg (fun l => (List.prod l).left) (congrArg List.ofFn (funext hv))

def sclA (s : K) : epsAt x ⟶ epsAt x := Over.homMk (spMap (epsMul s)) (by
  show spMap (epsMul s) ≫ spMap (algebraMap K (DualNumber K)) ≫ x = spMap (algebraMap K (DualNumber K)) ≫ x
  rw [← Category.assoc, epsMul_alg])

theorem relA_scl {v : epsAt x ⟶ A} {y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G}
    (h : RelA x F1 F2 v y) (s : K) :
    RelA x F1 F2 (sclA x s ≫ v) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD s) ≫ y) := by
  obtain ⟨w, hwy, hwv⟩ := h
  refine ⟨liftT (𝟙 (Sp K)) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD s)) ≫ w, rel_pre _ hwy, ?_⟩
  show spMap (epsMul s) ≫ v.left = ((ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD s)).left ≫ w.left) ≫ F1
  rw [Category.assoc, ← hwv]
  rfl

include h1 h2 in
theorem relA_tan {v : epsAt x ⟶ A} {y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G}
    (h : RelA x F1 F2 v y) :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left ↔
      ReciprocityTheory.ChartRestriction.G.Chart.IsTan y := by
  have hb : (1 : Over.mk (𝟙 (Sp K)) ⟶ G').left ≫ F1 = (1 : Over.mk x ⟶ A).left := by
    have e : (pushHom h1 (Over.mk (𝟙 (Sp K))) 1).left =
        (1 : Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x) ⟶ A).left := by
      rw [map_one]
    change (1 : Over.mk (𝟙 (Sp K)) ⟶ G').left ≫ F1 = _ at e
    rw [e, one_left', one_left']
    simp
  obtain ⟨w, hwy, hwv⟩ := h
  rw [← tan_iff h2 (Category.id_comp _) hwy, hwv, ← hb]
  constructor
  · intro e
    apply h1.1.hom_ext
    · rw [Category.assoc]
      exact e
    · rw [Category.assoc, Over.w w, Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ G')]
      simpa using fst_alg
  · intro e
    rw [← Category.assoc, e]

include h1 h2 in
theorem relA_eig {v : epsAt x ⟶ A} {y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G}
    (h : RelA x F1 F2 v y) (a : G' ⟶ G') (aA : A ⟶ A) (b : G ⟶ G) (h1a : a.left ≫ F1 = F1 ≫ aA.left)
    (h2a : a.left ≫ F2 = F2 ≫ b.left) (s : K) :
    v.left ≫ aA.left = spMap (epsMul s) ≫ v.left ↔
      y ≫ (Over.pullback (fB V K)).map b = ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD s) ≫ y := by
  obtain ⟨w, hwy, hwv⟩ := h
  rw [← eig_iff h2 a b h2a s hwy, hwv]
  constructor
  · intro e
    apply h1.1.hom_ext
    · simp only [Over.comp_left, Category.assoc, h1a]
      rw [Category.assoc] at e
      exact e
    · rw [Over.comp_left, Category.assoc, Over.w a, Category.assoc, Over.w w]
      show (sp (R₀ := K) (DualNumber K)).hom ≫ 𝟙 _ =
        spMap (epsScale s) ≫ (sp (R₀ := K) (DualNumber K)).hom ≫ 𝟙 _
      simp only [Category.comp_id]
      exact (epsMul_alg s).symm
  · intro e
    rw [Category.assoc, ← h1a, ← Category.assoc, ← Over.comp_left, e, Category.assoc]
    rfl

end Kside

end Formalism.L2.Pj.LieRel
end
end

