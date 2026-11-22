import Development.EtaleCohomology.CohomologicalPurity.Bundle0008
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
import Development.EtaleCohomology.CohomologicalPurity.Bundle0006

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPurRedPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurRedPf

open PurPf

theorem inv_red (q r : ℕ) {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (hq : Function.Bijective (pull (ZMod q) f (tw q i) n)) (hr : Function.Bijective (pull (ZMod r) f (tw r i) n))
    (y : Ht q E n i) :
    (AddEquiv.ofBijective _ hr).symm (red q r E n i y) = red q r E' n i ((AddEquiv.ofBijective _ hq).symm y) := by
  apply hr.1
  rw [AddEquiv.ofBijective_apply_symm_apply]
  rw [GlobalTheory.EtC.pull_red]
  congr 1
  exact ((AddEquiv.ofBijective _ hq).apply_symm_apply y).symm

def redS (q r : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs r P n i :=
  ⟨red q r _ n i x.1, by
    change pull _ (dbl.inr P) (tw r i) n (red q r _ n i x.1) = 0
    have hx : pull _ (dbl.inr P) (tw q i) n x.1 = 0 := x.2
    rw [GlobalTheory.EtC.pull_red, hx, map_zero]⟩

theorem redS_coe (q r : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : (redS q r P n i x).1 = red q r _ n i x.1 := rfl

theorem Hs.pullS_red (q r : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull r φ n i (redS q r P n i x) = redS q r P' n i (Hs.pull q φ n i x) := by
  apply Subtype.ext
  change pull _ (dbl.map φ) (tw r i) n (red q r _ n i x.1) = red q r _ n i (pull _ (dbl.map φ) (tw q i) n x.1)
  rw [GlobalTheory.EtC.pull_red]

theorem Hs.inv_red (q r : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ)
    (hq : Function.Bijective (Hs.pull q φ n i)) (hr : Function.Bijective (Hs.pull r φ n i)) (y : Hs q P' n i) :
    (AddEquiv.ofBijective _ hr).symm (redS q r P' n i y) = redS q r P n i ((AddEquiv.ofBijective _ hq).symm y) := by
  apply hr.1
  rw [AddEquiv.ofBijective_apply_symm_apply, Hs.pullS_red]
  congr 1
  exact ((AddEquiv.ofBijective _ hq).apply_symm_apply y).symm

theorem Hs.act_red (hA : A11) (q r : ℕ) [NeZero q] (hrq : r ∣ q) {P : Arrow Spc} {n m i j : ℤ}
    (a : Ht q P.right n i) (b : Hs q P m j) :
    Hs.act r (red q r _ n i a) (redS q r P m j b) = redS q r P _ _ (Hs.act q a b) := by
  apply Subtype.ext
  have hc : cup r (pull _ (dbl.fold P) (tw r i) n (red q r _ n i a)) (red q r _ m j b.1) =
      red q r _ _ _ (cup q (pull _ (dbl.fold P) (tw q i) n a) b.1) := by
    rw [(hA q r hrq (dbl P)).1, GlobalTheory.EtC.pull_red]
  simp only [Hs.act, Hs.proj, redS_coe]
  rw [hc, map_sub, GlobalTheory.EtC.pull_red, GlobalTheory.EtC.pull_red]

theorem fcl_isCl (hH : Hyp) (hCl : LeafCl) (d : ℕ) : IsCl d (fcl d) := by
  unfold fcl
  exact pick_spec (hCl hH d)

theorem purT_eq {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (a : Ht q (sch.obj P.Z) n i) :
    purT T q P n i a = (AddEquiv.ofBijective _ (((T P).ok q hq).2.2.1 (n + 2 * d) (i + d))).symm
      (Hs.act q (P := abv P.U (T P).π) ((AddEquiv.ofBijective _ (((T P).ok q hq).1 i n)).symm
        (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n a))
        (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P))) := by
  unfold purT
  rw [dif_pos ⟨NeZero.ne q, hq⟩]
  rfl

theorem act_fcl (hH : Hyp) (hCl : LeafCl) {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d)
    (hq : IsUnit (q : Γ(P.X, ⊤))) (r : ℕ) (hrq : r ∣ q) (n i : ℤ) (x : Ht q (T P).E n i) :
    Hs.act r (P := abv P.U (T P).π) (red q r (T P).E n i x) (Hs.pull r (abvMap P.U (T P).π) _ _ (fcl d r P)) =
      redS q r _ _ _ (Hs.act q (P := abv P.U (T P).π) x (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P))) := by
  have hfr : fcl d r P = redS q r _ _ _ (fcl d q P) := Subtype.ext (((fcl_isCl hH hCl d) q).2.2 r hrq P hq)
  rw [hfr, Hs.pullS_red]
  exact Hs.act_red hH.2.2.2.2.2.2.2.1 q r hrq _ _

end PurRedPf

open PurPf PurRedPf

theorem LeafPurRed_of : EtalePurityReduction := by
  intro hH hCl d T q _ P hq r hrq n i a
  have hq0 : q ≠ 0 := NeZero.ne q
  have hr0 : r ≠ 0 := by rintro rfl; exact hq0 (zero_dvd_iff.mp hrq)
  have : NeZero r := ⟨hr0⟩
  have hru : IsUnit (r : Γ(P.X, ⊤)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hrq) hq
  rw [purT_eq T r P hru, purT_eq T q P hq, GlobalTheory.EtC.pull_red, inv_red q r _ n i (((T P).ok q hq).1 i n) (((T P).ok r hru).1 i n), act_fcl hH hCl T q P hq r hrq, Hs.inv_red q r _ _ _, redS_coe]

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPushPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut
namespace PushPf

variable {J' J : Type} [SmallCategory J'] [SmallCategory J] {D' : J' ⥤ PSh} {D : J ⥤ PSh} {G : J' ⥤ J}

def phi (α : D' ⟶ G ⋙ D) (U : Scheme.{0}ᵒᵖ) : (D'.flip.obj U).Elements ⥤ (D.flip.obj U).Elements where
  obj e := ⟨G.obj e.1, (α.app e.1).app U e.2⟩
  map {e e'} g := ⟨G.map g.1, by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality g.1) U) e.2
    have h2 : (D'.map g.1).app U e.2 = e'.2 := g.2
    exact h.symm.trans (congrArg (fun y => (α.app e'.1).app U y) h2)⟩
  map_id e := Subtype.ext (G.map_id e.1)
  map_comp g g' := Subtype.ext (G.map_comp g.1 g'.1)

theorem elem_ext {X : Type} [Category X] {F : J ⥤ Type} (A B : X ⥤ F.Elements) (ho : ∀ x, A.obj x = B.obj x)
    (hm : A ⋙ CategoryOfElements.π F = B ⋙ CategoryOfElements.π F) : A = B := by
  refine CategoryTheory.Functor.ext ho (fun x y g => ?_)
  apply (CategoryOfElements.π F).map_injective
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hm g

theorem phi_nat (α : D' ⟶ G ⋙ D) {U U' : Scheme.{0}ᵒᵖ} (f : U ⟶ U') :
    phi α U ⋙ CategoryOfElements.map (D.flip.map f) = CategoryOfElements.map (D'.flip.map f) ⋙ phi α U' :=
  elem_ext _ _ (fun e => by
    have h := ConcreteCategory.congr_hom ((α.app e.1).naturality f) e.2
    exact Sigma.ext rfl (heq_of_eq h.symm)) rfl

def bmap (α : D' ⟶ G ⋙ D) : hoc D' ⟶ hoc D where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => (chn x ⋙ phi α U : Fin (n.unop.len + 1) ⥤ _)
      naturality := fun U U' f => by
        ext x
        change (chn x ⋙ CategoryOfElements.map (D'.flip.map f)) ⋙ phi α U' = (chn x ⋙ phi α U) ⋙ CategoryOfElements.map (D.flip.map f)
        rw [Functor.assoc, Functor.assoc, phi_nat] }
  naturality n m θ := by
    ext U x
    rfl

theorem goal (α : D' ⟶ G ⋙ D) {Y' Y : PSh} (f : Y' ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y') (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, α.app j ≫ c (G.obj j) = c' j ≫ f) : bmap α ≫ aug c hc = aug c' hc' ≫ disc.map f := by
  ext n U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h ((chn x).obj 0).1) U) ((chn x).obj 0).2

end PushPf

theorem LeafPush_of : LeafPush := fun _ _ _ _ _ _ _ α _ _ f c' c hc' hc h => ⟨PushPf.bmap α, PushPf.goal α f c' c hc' hc h⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafQuotPf
section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem LeafQuot_of : LeafQuot := by
  intro A B _ _ φ I h
  obtain ⟨J, _, _, D, s, t, ⟨hc⟩, hj⟩ := h
  have hst : ∀ j (a : A), (t.app j).hom ((s.app j).hom a) = φ a := fun j a =>
    congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom a) (hj j).2
  have sn : ∀ {j k : J} (f : j ⟶ k), (D.map f).hom.comp (s.app j).hom = (s.app k).hom := by
    intro j k f
    have := s.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    rw [this]; rfl
  have tn : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), (t.app k).hom ((D.map f).hom y) = (t.app j).hom y := by
    intro j k f y
    have := t.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
    exact congrArg (fun g : D.obj j ⟶ CommRingCat.of B => g.hom y) this
  have mv : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), y ∈ I.map (s.app j).hom →
      (D.map f).hom y ∈ I.map (s.app k).hom := by
    intro j k f y hy
    have := Ideal.mem_map_of_mem (D.map f).hom hy
    rwa [Ideal.map_map, sn f] at this
  have rep : ∀ b : B, ∃ j, ∃ y : D.obj j, (t.app j).hom y = b := fun b =>
    Concrete.isColimit_exists_rep D hc b
  have mem : ∀ x ∈ I.map φ, ∃ j, ∃ y : D.obj j, y ∈ I.map (s.app j).hom ∧ (t.app j).hom y = x := by
    intro x hx
    obtain ⟨j0⟩ := IsFiltered.nonempty (C := J)
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, ha, rfl⟩ := h
      exact ⟨j0, (s.app j0).hom a, Ideal.mem_map_of_mem _ ha, hst j0 a⟩
    | zero => exact ⟨j0, 0, zero_mem _, map_zero _⟩
    | add x x' _ _ h h' =>
      obtain ⟨j, y, hy, rfl⟩ := h
      obtain ⟨k, y', hy', rfl⟩ := h'
      refine ⟨IsFiltered.max j k, (D.map (IsFiltered.leftToMax j k)).hom y + (D.map (IsFiltered.rightToMax j k)).hom y',
        add_mem (mv _ _ hy) (mv _ _ hy'), ?_⟩
      rw [map_add, tn, tn]
    | smul b x _ h =>
      obtain ⟨j, y, hy, rfl⟩ := h
      obtain ⟨k, c, rfl⟩ := rep b
      refine ⟨IsFiltered.max k j, (D.map (IsFiltered.leftToMax k j)).hom c * (D.map (IsFiltered.rightToMax k j)).hom y,
        Ideal.mul_mem_left _ _ (mv _ _ hy), ?_⟩
      rw [map_mul, tn, tn]; rfl
  constructor
  · intro u v huv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.eq] at huv
    rw [Ideal.Quotient.eq]
    rw [← map_sub] at huv
    obtain ⟨j, y, hy, hy'⟩ := mem _ huv
    rw [← hst j] at hy'
    obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc y ((s.app j).hom (a - a')) hy'
    have h1 : (s.app k).hom (a - a') ∈ I.map (s.app k).hom := by
      have e : (D.map g).hom ((s.app j).hom (a - a')) = (D.map f).hom y := hfg.symm
      have e2 : ((D.map g).hom.comp (s.app j).hom) (a - a') = (s.app k).hom (a - a') :=
        congrArg (fun r : A →+* D.obj k => r (a - a')) (sn g)
      rw [← e2]
      have := mv f y hy
      rw [← e] at this
      exact this
    have h2 := (hj k).1.2.1 (a₁ := Ideal.Quotient.mk I (a - a')) (a₂ := 0) (by
      rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]; exact h1)
    exact (Ideal.Quotient.eq_zero_iff_mem).1 h2
  · intro w
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨j, y, rfl⟩ := rep b
    obtain ⟨u, hu⟩ := (hj j).1.2.2 (Ideal.Quotient.mk _ y)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hu
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    have hc' : (t.app j).hom.comp (s.app j).hom = φ :=
      congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom) (hj j).2
    have := Ideal.mem_map_of_mem (t.app j).hom hu
    rw [Ideal.map_map, hc', map_sub, hst] at this
    exact this

end LateralTheory.CohomologicalPurity.TubeCut
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafRefinePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex
namespace LateralTheory.CohomologicalPurity.TubeCut

variable {d : ℕ}

theorem hmap_congr (H : Hens) {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B} {φ ψ : A →+* B}
    (e : φ = ψ) (h : I ≤ J.comap φ) (h' : I ≤ J.comap ψ) : H.map φ h = H.map ψ h' := by subst e; rfl

theorem hmap_sq (H : Hens) {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    {I : Ideal A} {J : Ideal B} {K : Ideal C} {L : Ideal D} (a : A →+* B) (b : B →+* D) (c : A →+* C) (e : C →+* D)
    (ha : I ≤ J.comap a) (hb : J ≤ L.comap b) (hc : I ≤ K.comap c) (he : K ≤ L.comap e) (e0 : b.comp a = e.comp c) :
    (H.map b hb).comp (H.map a ha) = (H.map e he).comp (H.map c hc) := by
  rw [← H.map_comp a b ha hb (fun x hx => hb (ha hx)), ← H.map_comp c e hc he (fun x hx => he (hc hx))]
  exact hmap_congr H e0 _ _

theorem appLE_congr {X Y : Scheme.{0}} {u v : X ⟶ Y} (e : u = v) (U : Y.Opens) (W : X.Opens) (h : W ≤ u ⁻¹ᵁ U) :
    u.appLE U W h = v.appLE U W (e ▸ h) := by subst e; rfl

theorem idl {P' P : SP d} (φ : P'.Hom P) (V : P.X.affineOpens) (V' : P'.X.affineOpens) (h : V'.1 ≤ φ.f ⁻¹ᵁ V.1) :
    P.ι.ker.ideal V ≤ (P'.ι.ker.ideal V').comap (φ.f.appLE V.1 V'.1 h).hom := by
  have := P.cl; have := P'.cl
  intro a ha
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at ha
  rw [Ideal.mem_comap, Scheme.Hom.ker_apply, RingHom.mem_ker]
  rw [← CommRingCat.comp_apply, P'.ι.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr φ.cart.w,
    Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ha, map_zero]

theorem cotangentAtUnit_tangentBijection_naturality (H : Hens) {P' P : SP d} (φ : P'.Hom P) (V1 V2 : P.X.affineOpens) (V1' V2' : P'.X.affineOpens)
    (h1 : V1'.1 ≤ φ.f ⁻¹ᵁ V1.1) (h2 : V2'.1 ≤ φ.f ⁻¹ᵁ V2.1) (hV : V1 ≤ V2) (hV' : V1' ≤ V2') :
    Spec.map (CommRingCat.ofHom (H.map _ (P'.ι.ker.ideal_le_comap_ideal hV'))) ≫
      Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V2.1 V2'.1 h2).hom (idl φ V2 V2' h2))) =
    Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V1.1 V1'.1 h1).hom (idl φ V1 V1' h1))) ≫
      Spec.map (CommRingCat.ofHom (H.map _ (P.ι.ker.ideal_le_comap_ideal hV))) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact hmap_sq H _ _ _ _ _ _ _ _ (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE])

theorem henselization_spec_map_commutes_with_smooth_pair_hom (H : Hens) {P' P : SP d} (φ : P'.Hom P) (V : P.X.affineOpens) (V' : P'.X.affineOpens)
    (h : V'.1 ≤ φ.f ⁻¹ᵁ V.1) :
    Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V.1 V'.1 h).hom (idl φ V V' h))) ≫ hensTo H P V =
      hensTo H P' V' ≫ φ.f := by
  dsimp only [hensTo, eta]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, H.map_η, CommRingCat.ofHom_comp, Spec.map_comp_assoc]
  exact (congrArg (_ ≫ ·) (IsAffineOpen.SpecMap_appLE_fromSpec φ.f V.2 V'.2 h)).trans (Category.assoc _ _ _).symm

abbrev RJ {P' P : SP d} (φ : P'.Hom P) : Type :=
  {p : P'.X.affineOpens × P.X.affineOpens // Good P' p.1 ∧ Good P p.2 ∧ p.1.1 ≤ φ.f ⁻¹ᵁ p.2.1}

def Sys.ref (hC : LateralTheory.CohomologicalPurity.LeafChart) {P' P : SP d} (φ : P'.Hom P) : Sys P' where
  J := RJ φ
  V j := j.1.1
  mono h := (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1
  good j := j.2.1
  cov x := by
    obtain ⟨V, hV, -, g⟩ := hC d P (φ.f x) ⊤ trivial
    obtain ⟨V', hV', l, g'⟩ := hC d P' x (φ.f ⁻¹ᵁ V.1) hV
    exact ⟨⟨(V', V), g', g, l⟩, hV'⟩
  dir x j k hj hk := by
    have hj2 : φ.f x ∈ j.1.2.1 := j.2.2.2 hj
    have hk2 : φ.f x ∈ k.1.2.1 := k.2.2.2 hk
    obtain ⟨V, hV, l, g⟩ := hC d P (φ.f x) (j.1.2.1 ⊓ k.1.2.1) ⟨hj2, hk2⟩
    obtain ⟨V', hV', l', g'⟩ := hC d P' x (j.1.1.1 ⊓ k.1.1.1 ⊓ φ.f ⁻¹ᵁ V.1) ⟨⟨hj, hk⟩, hV⟩
    exact ⟨⟨(V', V), g', g, l'.trans inf_le_right⟩, ⟨l'.trans (inf_le_left.trans inf_le_left), l.trans inf_le_left⟩,
      ⟨l'.trans (inf_le_left.trans inf_le_right), l.trans inf_le_right⟩, hV'⟩

theorem EtaleRefine_of_push (hP : LeafPush) : LeafRefine := by
  intro hC H d P' P φ
  let S' := Sys.ref hC φ
  let G1 : S'.J ⥤ (Sys.all hC P').J := Monotone.functor (f := fun j => (⟨j.1.1, j.2.1⟩ : {V : P'.X.affineOpens // Good P' V}))
    (fun _ _ h => (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1)
  let G2 : S'.J ⥤ (Sys.all hC P).J := Monotone.functor (f := fun j => (⟨j.1.2, j.2.2.1⟩ : {V : P.X.affineOpens // Good P V}))
    (fun _ _ h => (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2)
  let α1 : S'.hen H ⋙ yoneda ⟶ G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda :=
    { app := fun j => (𝟙 ((S'.hen H ⋙ yoneda).obj j) : _ ⟶ (G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda).obj j)
      naturality := fun j k f => (Category.comp_id _).trans (Category.id_comp ((G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda).map f)).symm }
  obtain ⟨a, ha⟩ := hP _ _ _ _ G1 α1 _ _ (𝟙 (yoneda.obj P'.X)) _ _ (S'.cocHen H) ((Sys.all hC P').cocHen H)
    (fun j => (Category.id_comp _).trans (Category.comp_id _).symm)
  have ea : a ≫ (Sys.all hC P').π H = S'.π H := by
    have := ha; rw [disc.map_id, Category.comp_id] at this; exact this
  let α2 : S'.hen H ⋙ yoneda ⟶ G2 ⋙ (Sys.all hC P).hen H ⋙ yoneda :=
    { app := fun j => yoneda.map (Spec.map (CommRingCat.ofHom
        (H.map (φ.f.appLE (j.1.2).1 (j.1.1).1 j.2.2.2).hom (idl φ j.1.2 j.1.1 j.2.2.2))))
      naturality := fun j k f => (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map
        (cotangentAtUnit_tangentBijection_naturality H φ j.1.2 k.1.2 j.1.1 k.1.1 j.2.2.2 k.2.2.2 (Prod.le_def.1 (Subtype.coe_le_coe.2 f.le)).2
          (Prod.le_def.1 (Subtype.coe_le_coe.2 f.le)).1)).trans (yoneda.map_comp _ _)) }
  obtain ⟨b, hb⟩ := hP _ _ _ _ G2 α2 _ _ (yoneda.map φ.f) _ _ (S'.cocHen H) ((Sys.all hC P).cocHen H)
    (fun j => (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map (henselization_spec_map_commutes_with_smooth_pair_hom H φ j.1.2 j.1.1 j.2.2.2)).trans
      (yoneda.map_comp _ _)))
  exact ⟨S', a, b, ea, hb⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafRelHocPfX
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem pull_iso_bij (R : Type) [CommRing R] {E E' : Spc} (i : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R i.hom F n) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R i.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, i.inv_hom_id, pull_id]
  · rw [← pull_comp, i.hom_inv_id, pull_id]

theorem eqv_of_arrowIso (R : Type) [CommRing R] {E' E G' G : Spc} {f : E' ⟶ E} {g : G' ⟶ G} (F : Shv R)
    (e : Arrow.mk f ≅ Arrow.mk g) (hf : Eqv R f F) : Eqv R g F := by
  intro n
  have w : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
  have k : (pull R e.hom.left F n) ∘ (pull R g F n) = (pull R f F n) ∘ (pull R e.hom.right F n) := by
    funext x
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, w]
  have hl : Function.Bijective (pull R e.hom.left F n) :=
    pull_iso_bij R ((Arrow.leftFunc).mapIso e) F n
  have hr : Function.Bijective (pull R e.hom.right F n) :=
    pull_iso_bij R ((Arrow.rightFunc).mapIso e) F n
  have hc : Function.Bijective ((pull R e.hom.left F n) ∘ (pull R g F n)) := by
    rw [k]; exact (hf n).comp hr
  exact (Function.Bijective.of_comp_iff' hl _).mp hc

theorem eqv_sum_RRelH (hS : LeafSum) (R : Type) [CommRing R] (F : Shv R) {A : Type} {E' E : A → Spc} (c' : Cofan E') (c : Cofan E)
    (hc' : Nonempty (IsColimit c')) (hc : Nonempty (IsColimit c)) (f : ∀ a, E' a ⟶ E a) (φ : c'.pt ⟶ c.pt)
    (hφ : ∀ a, c'.inj a ≫ φ = f a ≫ c.inj a) (hf : ∀ a, Eqv R (f a) F) : Eqv R φ F := by
  intro n
  have k : (fun (y : H R c'.pt F n) (a : A) => pull R (c'.inj a) F n y) ∘ (pull R φ F n) =
      (fun (z : ∀ a, H R (E a) F n) (a : A) => pull R (f a) F n (z a)) ∘
        (fun (x : H R c.pt F n) (a : A) => pull R (c.inj a) F n x) := by
    funext x a
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, hφ]
  have h1 := hS R F A E' c' hc' n
  have h2 := hS R F A E c hc n
  have hc3 : Function.Bijective ((fun (y : H R c'.pt F n) (a : A) => pull R (c'.inj a) F n y) ∘ (pull R φ F n)) := by
    rw [k]
    exact (Function.Bijective.piMap (fun a => hf a n)).comp h2
  exact (Function.Bijective.of_comp_iff' h1 _).mp hc3

def LeafRelLev : Prop := LeafLevel → ∀ (J : Type) [SmallCategory J] (D' D : J ⥤ PSh) (α : D' ⟶ D)
  (Y G : PSh) (g : G ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j)) (h' : (hocF J).map α ≫ aug c hc = aug c' hc')
  (n : SimplexCategoryᵒᵖ),
  ∃ (A : Type) (ι : A → J) (E' E : A → Spc) (k' : Cofan E') (k : Cofan E) (f : ∀ a, E' a ⟶ E a) (φ : k'.pt ⟶ k.pt),
    Nonempty (IsColimit k') ∧ Nonempty (IsColimit k) ∧ (∀ a, k'.inj a ≫ φ = f a ≫ k.inj a) ∧
    (∀ a, Nonempty (Arrow.mk (pbRel (disc.map g) (disc.map (α.app (ι a))) (disc.map (c' (ι a))) (disc.map (c (ι a)))
      (h (ι a))) ≅ Arrow.mk (f a))) ∧
    Nonempty (Arrow.mk φ ≅ Arrow.mk (disc.map ((pbRel (disc.map g) ((hocF J).map α) (aug c' hc') (aug c hc) h').app n)))

theorem LeafRelHoc_of (hL : LeafLevel) (hS : LeafSum) (hB : LeafRelLev) : LeafRelHoc := by
  intro hA3 R _ F J _ D' D α Y G g c' c hc' hc h h' hE
  apply hA3
  intro n
  obtain ⟨A, ι, E', E, k', k, f, φ, h1, h2, h3, h4, ⟨e⟩⟩ := hB hL J D' D α Y G g c' c hc' hc h h' n
  refine eqv_of_arrowIso R F e ?_
  exact eqv_sum_RRelH hS R F k' k h1 h2 f φ h3 fun a => eqv_of_arrowIso R F (h4 a).some (hE (ι a))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafRelPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafChPush : Prop := ∀ (q : ℕ) (P : Arrow Spc),
  IsPushout ((chains (ZMod q)).map P.hom) ((chains (ZMod q)).map P.hom) ((chains (ZMod q)).map (dbl.inl P))
    ((chains (ZMod q)).map (dbl.inr P))

def LeafHKSplit : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B D : Cx R} (f : A ⟶ B) (l r : B ⟶ D)
  (s : D ⟶ B), IsPushout f f l r → r ≫ s = 𝟙 _ → ∀ p : D ⟶ cokernel f, l ≫ p = cokernel.π f → r ≫ p = 0 →
  Function.Injective (HK.pull R p F n) ∧ ∀ x, HK.pull R r F n x = 0 → ∃ y, HK.pull R p F n y = x

theorem hk_pull_pull {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R f F n (HK.pull R g F n x) = HK.pull R (f ≫ g) F n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem hk_pull_zero {R : Type} [CommRing R] {K L : Cx R} (F : Shv R) (n : ℤ) (x : HK R L F n) :
    HK.pull R (0 : K ⟶ L) F n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [← CohomologyClass.mk_zero]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem LeafRel_of (h1 : LeafChPush) (h2 : LeafHKSplit) : LeafRel := by
  intro q i
  have ex : ∀ P : Arrow Spc, ∃ p : (chains (ZMod q)).obj (dbl P) ⟶ cokernel ((chains (ZMod q)).map P.hom),
      (chains _).map (dbl.inl P) ≫ p = cokernel.π _ ∧ (chains _).map (dbl.inr P) ≫ p = 0 := fun P =>
    ⟨(h1 q P).desc (cokernel.π _) 0 (by simp), (h1 q P).inl_desc _ _ _, (h1 q P).inr_desc _ _ _⟩
  choose p hl hr using ex
  have hs : ∀ P : Arrow Spc, (chains (ZMod q)).map (dbl.inr P) ≫ (chains _).map (dbl.fold P) = 𝟙 _ := fun P => by
    rw [← Functor.map_comp, dbl.inr_fold, CategoryTheory.Functor.map_id]
  have mem : ∀ (P : Arrow Spc) (n : ℤ) x, HK.pull _ (p P) (tw q i) n x ∈ Hs q P n i := fun P n x => by
    change HK.pull _ ((chains _).map (dbl.inr P)) (tw q i) n (HK.pull _ (p P) (tw q i) n x) = 0
    rw [hk_pull_pull, hr, hk_pull_zero]
  refine ⟨fun P n => AddEquiv.ofBijective ((HK.pull _ (p P) (tw q i) n).codRestrict _ (mem P n)) ⟨fun x y h => ?_, fun x => ?_⟩,
    fun P n p' hl' hr' x => ?_⟩
  · exact (h2 _ (tw q i) n _ _ _ _ (h1 q P) (hs P) (p P) (hl P) (hr P)).1 (congrArg Subtype.val h)
  · obtain ⟨y, hy⟩ := (h2 _ (tw q i) n _ _ _ _ (h1 q P) (hs P) (p P) (hl P) (hr P)).2 x.1 x.2
    exact ⟨y, Subtype.ext hy⟩
  · have e : p' = p P := (h1 q P).hom_ext (hl'.trans (hl P).symm) (hr'.trans (hr P).symm)
    subst e; rfl

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafSurjGeoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity

theorem LeafSurjGeo_of : LeafSurjGeo := by
  intro X' X Z f _ ι' ι _ hp U hU T t
  let F : Bool → Scheme.{0} := fun b => Bool.rec (pullback t f) (t ⁻¹ᵁ U).toScheme b
  let m : ∀ b, F b ⟶ T := fun b => Bool.rec (pullback.fst t f) (t ⁻¹ᵁ U).ι b
  have hR : Presieve.ofArrows F m ∈ Scheme.precoverage @Etale T := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : t.base x ∈ (U : Set X)
      · refine ⟨true, ?_⟩
        show x ∈ Set.range (t ⁻¹ᵁ U).ι.base
        rw [Scheme.Opens.range_ι]; exact hx
      · rw [hU, Set.notMem_compl_iff] at hx
        obtain ⟨z, hz⟩ := hx
        have hw : f.base (ι'.base z) = ι.base z := by
          rw [← Scheme.Hom.comp_apply, hp.w]; simp
        obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := f) x (ι'.base z)
          (by rw [hw, hz])
        exact ⟨false, p, hp1⟩
    · cases b <;> dsimp [m] <;> infer_instance
  refine ⟨Sieve.generate (Presieve.ofArrows F m),
    Precoverage.generate_mem_toGrothendieck hR, ?_⟩
  intro V g hg
  obtain ⟨W, h, k, hk, rfl⟩ := hg
  obtain ⟨b⟩ := hk
  cases b
  · right
    refine ⟨h ≫ pullback.snd t f, ?_⟩
    simp only [m, Category.assoc, ← pullback.condition]
  · left
    refine ⟨h ≫ (t ∣_ U), ?_⟩
    simp only [m, Category.assoc, morphismRestrict_ι]

end LateralTheory.CohomologicalPurity
end
end

