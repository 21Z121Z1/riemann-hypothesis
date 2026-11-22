import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Sector
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.BaseChange

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {A' : Over S'} [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem ext' (hφ : IsGrpPullback A' A f φ) {X Z : Scheme.{0}} {s : X ⟶ S'} {u v : Z ⟶ (A' ⊗ Over.mk s).left}
    (h₁ : u ≫ (fst A' (Over.mk s)).left ≫ φ = v ≫ (fst A' (Over.mk s)).left ≫ φ)
    (h₂ : u ≫ (snd A' (Over.mk s)).left = v ≫ (snd A' (Over.mk s)).left) : u = v := by
  refine left_ext (hφ.1.hom_ext (by simpa only [Category.assoc] using h₁) ?_) h₂
  rw [Category.assoc, Category.assoc, Over.w (fst A' _), ← Over.w (snd A' (Over.mk s)), ← Category.assoc, h₂,
    Category.assoc]

theorem toBase_w {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    (snd A' (Over.mk s)).left ≫ s₀ = (A' ⊗ Over.mk s).hom ≫ f := by
  rw [← hs, ← Category.assoc]
  exact congrArg (· ≫ f) (Over.w (snd A' (Over.mk s)))

def toBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    (A' ⊗ Over.mk s).left ⟶ (A ⊗ Over.mk s₀).left :=
  (lift (pushP hφ (s := (A' ⊗ Over.mk s).hom) rfl (fst A' (Over.mk s)))
    (Over.homMk (snd A' (Over.mk s)).left (toBase_w hs) : Over.mk ((A' ⊗ Over.mk s).hom ≫ f) ⟶ Over.mk s₀)).left

@[reassoc]
theorem toBase_fst (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    toBase hφ hs ≫ (fst A (Over.mk s₀)).left = (fst A' (Over.mk s)).left ≫ φ :=
  lift_left_fst _ _

@[reassoc]
theorem toBase_snd (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    toBase hφ hs ≫ (snd A (Over.mk s₀)).left = (snd A' (Over.mk s)).left :=
  lift_left_snd _ _

theorem ofBase_w {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    (fst A (Over.mk s₀)).left ≫ A.hom = ((snd A (Over.mk s₀)).left ≫ s) ≫ f := by
  rw [Over.w (fst A _), Category.assoc, hs]
  exact (Over.w (snd A (Over.mk s₀))).symm

def ofBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    (A ⊗ Over.mk s₀).left ⟶ (A' ⊗ Over.mk s).left :=
  (lift (liftPt hφ _ (fst A (Over.mk s₀)).left (ofBase_w hs))
    (Over.homMk (snd A (Over.mk s₀)).left rfl : Over.mk ((snd A (Over.mk s₀)).left ≫ s) ⟶ Over.mk s)).left

@[reassoc]
theorem ofBase_fst (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    ofBase hφ hs ≫ (fst A' (Over.mk s)).left ≫ φ = (fst A (Over.mk s₀)).left := by
  rw [← Category.assoc]
  exact (congrArg (· ≫ φ) (lift_left_fst _ _)).trans (liftPt_left _ _ _ _)

@[reassoc]
theorem ofBase_snd (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀) :
    ofBase hφ hs ≫ (snd A' (Over.mk s)).left = (snd A (Over.mk s₀)).left :=
  lift_left_snd _ _

theorem ofBase_toBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (hs : s ≫ f = s₀) : ofBase hφ hs ≫ toBase hφ hs = 𝟙 _ := by
  apply left_ext
  · rw [Category.assoc, toBase_fst, ofBase_fst, Category.id_comp]
  · rw [Category.assoc, toBase_snd, ofBase_snd, Category.id_comp]

theorem toBase_ofBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (hs : s ≫ f = s₀) : toBase hφ hs ≫ ofBase hφ hs = 𝟙 _ := by
  apply ext' hφ
  · rw [Category.assoc, ofBase_fst, toBase_fst, Category.id_comp]
  · rw [Category.assoc, ofBase_snd, toBase_snd, Category.id_comp]

end GlobalTheory.DualCon.BaseChange

namespace GlobalTheory.DualCon.BaseChange

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {A' : Over S'} [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem lift_ofBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀)
    {Y : Over S} (a₀ : Y ⟶ A) (t₀ : Y ⟶ Over.mk s₀) :
    (lift a₀ t₀).left ≫ ofBase hφ hs = (lift (liftPt hφ (t₀.left ≫ s) a₀.left
      (by rw [Over.w a₀, Category.assoc, hs]; exact (Over.w t₀).symm))
      (Over.homMk t₀.left rfl : Over.mk (t₀.left ≫ s) ⟶ Over.mk s)).left := by
  apply ext' hφ
  · rw [Category.assoc, ofBase_fst, lift_left_fst, lift_left_fst_assoc, liftPt_left]
  · rw [Category.assoc, ofBase_snd, lift_left_snd, lift_left_snd]
    rfl

theorem lift_toBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀)
    {Y : Over S'} (a : Y ⟶ A') (t : Y ⟶ Over.mk s) :
    (lift a t).left ≫ toBase hφ hs = (lift (pushP hφ (s := Y.hom) rfl a)
      (Over.homMk t.left (by show t.left ≫ s₀ = Y.hom ≫ f; rw [← hs, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w t)) :
        Over.mk (Y.hom ≫ f) ⟶ Over.mk s₀)).left := by
  apply left_ext
  · rw [Category.assoc, toBase_fst, lift_left_fst_assoc, lift_left_fst]
    rfl
  · rw [Category.assoc, toBase_snd, lift_left_snd, lift_left_snd]
    rfl

theorem fam_ofBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀)
    {M : LB (A' ⊗ Over.mk s).left} (hM : Fam A' M) : Fam A (M.pull (ofBase hφ hs)) := by
  have hM₀ : (M.pull (ofBase hφ hs)).IsLB := pull_isLB hM.isLB _
  refine ⟨hM₀, (isAdditive_iff hM₀).2 fun Y a₀ a₀' t₀ ↦ ?_⟩
  have ev₀ : ∀ (a : Y ⟶ A), evc hM₀ a t₀ = evc hM.isLB
      (liftPt hφ (t₀.left ≫ s) a.left (by rw [Over.w a, Category.assoc, hs]; exact (Over.w t₀).symm))
      (Over.homMk t₀.left rfl : Over.mk (t₀.left ≫ s) ⟶ Over.mk s) := fun a ↦ by
    rw [evc, evc, cls_pull hM.isLB, ← pull_comp, lift_ofBase]
  have hs' : (t₀.left ≫ s) ≫ f = Y.hom := by rw [Category.assoc, hs]; exact Over.w t₀
  have hmul : liftPt hφ (t₀.left ≫ s) (a₀ * a₀').left
      (by rw [Over.w (a₀ * a₀'), Category.assoc, hs]; exact (Over.w t₀).symm) =
      liftPt hφ _ a₀.left (by rw [Over.w a₀, Category.assoc, hs]; exact (Over.w t₀).symm) *
        liftPt hφ _ a₀'.left (by rw [Over.w a₀', Category.assoc, hs]; exact (Over.w t₀).symm) :=
    pt_ext hφ (by
      rw [liftPt_left]
      exact (mul_left_comp hφ hs' (x₀ := a₀) (y₀ := a₀') (liftPt_left _ _ _ _) (liftPt_left _ _ _ _)).symm)
  rw [ev₀, ev₀, ev₀, hmul]
  exact (isAdditive_iff hM.isLB).1 hM.add _ _ _ _

theorem fam_toBase (hφ : IsGrpPullback A' A f φ) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ f = s₀)
    {N : LB (A ⊗ Over.mk s₀).left} (hN : Fam A N) : Fam A' (N.pull (toBase hφ hs)) := by
  have hN' : (N.pull (toBase hφ hs)).IsLB := pull_isLB hN.isLB _
  refine ⟨hN', (isAdditive_iff hN').2 fun Y a a' t ↦ ?_⟩
  have ev₀ : ∀ (c : Y ⟶ A'), evc hN' c t = evc hN.isLB (pushP hφ (s := Y.hom) rfl c)
      (Over.homMk t.left (by show t.left ≫ s₀ = Y.hom ≫ f; rw [← hs, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w t)) : Over.mk (Y.hom ≫ f) ⟶ Over.mk s₀) :=
    fun c ↦ by rw [evc, evc, cls_pull hN.isLB, ← pull_comp, lift_toBase]
  have hmul : pushP hφ (s := Y.hom) rfl (a * a') = pushP hφ (s := Y.hom) rfl a * pushP hφ (s := Y.hom) rfl a' :=
    Over.OverMorphism.ext (mul_left_comp hφ rfl rfl rfl)
  rw [ev₀, ev₀, ev₀, hmul]
  exact (isAdditive_iff hN.isLB).1 hN.add _ _ _ _

theorem pull_inj_iff {X Y : Scheme.{0}} (u : Y ⟶ X) (v : X ⟶ Y) (h : v ≫ u = 𝟙 X) (c d : Pic X) :
    c = d ↔ CechPic.pull u c = CechPic.pull u d :=
  ⟨congrArg _, fun e ↦ by
    have k := congrArg (CechPic.pull v) e
    rwa [← pull_comp, ← pull_comp, h, pull_id, pull_id] at k⟩

theorem toBase_lift_ofBase (hφ : IsGrpPullback A' A f φ) {X Z : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (hs : s ≫ f = s₀) {sZ : Z ⟶ S'} {sZ₀ : Z ⟶ S} (hsZ : sZ ≫ f = sZ₀) (x : Over.mk s₀ ⟶ Over.mk sZ₀)
    (x' : Over.mk s ⟶ Over.mk sZ) (hx : x.left = x'.left) :
    toBase hφ hs ≫ (lift (fst A (Over.mk s₀)) (snd A (Over.mk s₀) ≫ x)).left ≫ ofBase hφ hsZ =
      (lift (fst A' (Over.mk s)) (snd A' (Over.mk s) ≫ x')).left := by
  apply ext' hφ
  · rw [Category.assoc, Category.assoc, ofBase_fst, lift_left_fst, toBase_fst, lift_left_fst_assoc]
  · rw [Category.assoc, Category.assoc, ofBase_snd, lift_left_snd, Over.comp_left, toBase_snd_assoc,
      lift_left_snd, Over.comp_left, hx]

theorem ofBase_lift_toBase (hφ : IsGrpPullback A' A f φ) {X Z : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S}
    (hs : s ≫ f = s₀) {sZ : Z ⟶ S'} {sZ₀ : Z ⟶ S} (hsZ : sZ ≫ f = sZ₀) (x : Over.mk s₀ ⟶ Over.mk sZ₀)
    (x' : Over.mk s ⟶ Over.mk sZ) (hx : x.left = x'.left) :
    ofBase hφ hs ≫ (lift (fst A' (Over.mk s)) (snd A' (Over.mk s) ≫ x')).left ≫ toBase hφ hsZ =
      (lift (fst A (Over.mk s₀)) (snd A (Over.mk s₀) ≫ x)).left := by
  apply left_ext
  · rw [Category.assoc, Category.assoc, toBase_fst, lift_left_fst_assoc, ofBase_fst, lift_left_fst]
  · rw [Category.assoc, Category.assoc, toBase_snd, lift_left_snd, Over.comp_left, ofBase_snd_assoc,
      lift_left_snd, Over.comp_left, hx]

end GlobalTheory.DualCon.BaseChange

namespace GlobalTheory.DualCon.BaseChange

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {A' : Over S'} [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem rep_down (hφ : IsGrpPullback A' A f φ) {T B' : Over S'} (b' : B' ⟶ T) {P' : LB (A' ⊗ B').left}
    (h : Rep A' b' P') :
    Rep A (Over.homMk b'.left (by show b'.left ≫ T.hom ≫ f = B'.hom ≫ f; rw [← Category.assoc, Over.w b']) :
      Over.mk (B'.hom ≫ f) ⟶ Over.mk (T.hom ≫ f)) (P'.pull (ofBase hφ (s := B'.hom) rfl)) where
  fam := fam_ofBase hφ rfl h.fam
  univ T₁ t N hN := by
    have hs : (t.left ≫ T.hom) ≫ f = T₁.hom := by rw [Category.assoc]; exact Over.w t
    obtain ⟨x', ⟨hxb, hxN⟩, hu⟩ := h.univ (Over.mk (t.left ≫ T.hom)) (Over.homMk t.left rfl)
      (N.pull (toBase hφ hs)) (fam_toBase hφ hs hN)
    have key : ∀ (x : T₁ ⟶ Over.mk (B'.hom ≫ f)) (x' : Over.mk (t.left ≫ T.hom) ⟶ B'), x.left = x'.left →
        (LBIso N (ev (P'.pull (ofBase hφ (s := B'.hom) rfl)) (fst A T₁) (snd A T₁ ≫ x)) ↔
          LBIso (N.pull (toBase hφ hs)) (ev P' (fst A' _) (snd A' _ ≫ x'))) := fun x x' hx ↦ by
      have hQ := pull_isLB (pull_isLB h.fam.isLB (ofBase hφ (s := B'.hom) rfl))
        (lift (fst A T₁) (snd A T₁ ≫ x)).left
      rw [← cls_eq_iff hN.isLB hQ, ← cls_eq_iff (pull_isLB hN.isLB _) (pull_isLB h.fam.isLB _)]
      refine (pull_inj_iff _ _ (ofBase_toBase hφ hs) _ _).trans (Eq.congr_right ?_)
      show CechPic.pull (toBase hφ hs) (CechPic.pull (lift (fst A T₁) (snd A T₁ ≫ x)).left
        (CechPic.pull (ofBase hφ (s := B'.hom) rfl) (cls P' h.fam.isLB))) = _
      rw [← pull_comp, ← pull_comp, Category.assoc]
      exact congrArg (fun m ↦ CechPic.pull m (cls P' h.fam.isLB)) (toBase_lift_ofBase hφ hs rfl x x' hx)
    have hxl : x'.left ≫ b'.left = t.left := congrArg (fun z ↦ z.left) hxb
    refine ⟨Over.homMk x'.left (by show x'.left ≫ B'.hom ≫ f = T₁.hom; rw [← Category.assoc, Over.w x']; exact hs),
      ⟨Over.OverMorphism.ext hxl, (key _ x' rfl).2 hxN⟩, fun y ⟨hyb, hyN⟩ ↦ ?_⟩
    have hyl : y.left ≫ b'.left = t.left := congrArg (fun z ↦ z.left) hyb
    let y' : Over.mk (t.left ≫ T.hom) ⟶ B' := Over.homMk y.left
      (by
        show y.left ≫ B'.hom = t.left ≫ T.hom
        rw [← hyl, Category.assoc]
        exact congrArg (y.left ≫ ·) (Over.w b').symm)
    have e := hu y' ⟨Over.OverMorphism.ext hyl, (key y y' rfl).1 hyN⟩
    exact Over.OverMorphism.ext (congrArg (fun z ↦ z.left) e)

theorem rep_up (hφ : IsGrpPullback A' A f φ) {T : Over S'} {B : Over S} (b : B ⟶ Over.mk (T.hom ≫ f))
    {P : LB (A ⊗ B).left} (h : Rep A b P) :
    Rep A' (Over.homMk b.left rfl : Over.mk (b.left ≫ T.hom) ⟶ T)
      (P.pull (toBase hφ (s := b.left ≫ T.hom) (s₀ := B.hom) (by rw [Category.assoc]; exact Over.w b))) where
  fam := fam_toBase hφ _ h.fam
  univ T₁ t' N' hN' := by
    have hsB : (b.left ≫ T.hom) ≫ f = B.hom := by rw [Category.assoc]; exact Over.w b
    let t : Over.mk (T₁.hom ≫ f) ⟶ Over.mk (T.hom ≫ f) := Over.homMk t'.left
      (by show t'.left ≫ T.hom ≫ f = T₁.hom ≫ f; rw [← Category.assoc, Over.w t'])
    obtain ⟨x, ⟨hxb, hxN⟩, hu⟩ := h.univ (Over.mk (T₁.hom ≫ f)) t (N'.pull (ofBase hφ (s := T₁.hom) rfl))
      (fam_ofBase hφ rfl hN')
    have key : ∀ (x : Over.mk (T₁.hom ≫ f) ⟶ B) (x' : T₁ ⟶ Over.mk (b.left ≫ T.hom)), x.left = x'.left →
        (LBIso N' (ev (P.pull (toBase hφ hsB)) (fst A' T₁) (snd A' T₁ ≫ x')) ↔
          LBIso (N'.pull (ofBase hφ (s := T₁.hom) rfl)) (ev P (fst A _) (snd A _ ≫ x))) := fun x x' hx ↦ by
      have hQ := pull_isLB (pull_isLB h.fam.isLB (toBase hφ hsB)) (lift (fst A' T₁) (snd A' T₁ ≫ x')).left
      rw [← cls_eq_iff hN'.isLB hQ, ← cls_eq_iff (pull_isLB hN'.isLB _) (pull_isLB h.fam.isLB _)]
      refine (pull_inj_iff _ _ (toBase_ofBase hφ (s := T₁.hom) rfl) _ _).trans (Eq.congr_right ?_)
      show CechPic.pull (ofBase hφ (s := T₁.hom) rfl) (CechPic.pull (lift (fst A' T₁) (snd A' T₁ ≫ x')).left
        (CechPic.pull (toBase hφ hsB) (cls P h.fam.isLB))) = _
      rw [← pull_comp, ← pull_comp, Category.assoc]
      exact congrArg (fun m ↦ CechPic.pull m (cls P h.fam.isLB)) (ofBase_lift_toBase hφ rfl hsB x x' hx)
    have hxl : x.left ≫ b.left = t'.left := congrArg (fun z ↦ z.left) hxb
    refine ⟨Over.homMk x.left (by show x.left ≫ b.left ≫ T.hom = T₁.hom; rw [← Category.assoc, hxl, Over.w t']),
      ⟨Over.OverMorphism.ext hxl, (key x _ rfl).2 hxN⟩, fun y' ⟨hyb, hyN⟩ ↦ ?_⟩
    have hyl : y'.left ≫ b.left = t'.left := congrArg (fun z ↦ z.left) hyb
    let y : Over.mk (T₁.hom ≫ f) ⟶ B := Over.homMk y'.left (by
      show y'.left ≫ B.hom = T₁.hom ≫ f
      rw [← hsB, ← Category.assoc, ← Category.assoc, hyl, Over.w t'])
    have e := hu y ⟨Over.OverMorphism.ext hyl, (key y y' rfl).1 hyN⟩
    exact Over.OverMorphism.ext (congrArg (fun z ↦ z.left) e)

end GlobalTheory.DualCon.BaseChange

namespace GlobalTheory.DualCon

theorem hasRep_baseChange_iff : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A']
    (φ : A'.left ⟶ A.left), IsGrpPullback A' A f φ → ∀ (g : ℕ) (T : Over S'),
    (HasRep A' g T ↔ HasRep A g (Over.mk (T.hom ≫ f))) ∧
      (HasRepAF A' g T ↔ HasRepAF A g (Over.mk (T.hom ≫ f))) := by
  intro S S' f A _ A' _ φ hφ g T
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨B', b', P', hR, hG⟩
    exact ⟨_, _, _, BaseChange.rep_down hφ b' hR, hG⟩
  · rintro ⟨B, b, P, hR, hG⟩
    exact ⟨_, _, _, BaseChange.rep_up hφ b hR, hG⟩
  · rintro ⟨B', b', P', hR, hG, hF⟩
    exact ⟨_, _, _, BaseChange.rep_down hφ b' hR, hG, hF⟩
  · rintro ⟨B, b, P, hR, hG, hF⟩
    exact ⟨_, _, _, BaseChange.rep_up hφ b hR, hG, hF⟩

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqSpanOnBasicOpensOfStalkPrincipal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.IdealSpread

theorem exists_of_map_eq_span {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (M : Submonoid A)
    [IsLocalization M R] {J : Ideal A} (hJ : J.FG) (d : A)
    (h : J.map (algebraMap A R) = Ideal.span {algebraMap A R d}) :
    ∃ s ∈ M, s * d ∈ J ∧ ∀ j ∈ J, ∃ c, s * j = c * d := by

  obtain ⟨s₁, hs₁M, hs₁⟩ : ∃ s₁ ∈ M, s₁ * d ∈ J := by
    have hd : algebraMap A R d ∈ J.map (algebraMap A R) := h ▸ Ideal.subset_span rfl
    obtain ⟨⟨⟨a, ha⟩, m⟩, hm⟩ := (IsLocalization.mem_map_algebraMap_iff M R).1 hd
    simp only at hm
    rw [← map_mul] at hm
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) hm
    refine ⟨c * m, M.mul_mem c.2 m.2, ?_⟩
    have : (c : A) * (d * m) = c * a := hc
    rw [show (c : A) * m * d = c * (d * m) by ring, this]
    exact J.mul_mem_left _ ha

  have hone : ∀ g ∈ J, ∃ t ∈ M, ∃ c, t * g = c * d := by
    intro g hg
    have hg' : algebraMap A R g ∈ Ideal.span {algebraMap A R d} := h ▸ Ideal.mem_map_of_mem _ hg
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hg'
    obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj M r
    simp only at ham
    have : algebraMap A R (m * g) = algebraMap A R (a * d) := by
      rw [map_mul, map_mul, ← ham, ← hr]; ring
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) this
    exact ⟨c * m, M.mul_mem c.2 m.2, c * a, by linear_combination hc⟩
  have key : ∀ T : Finset A, (∀ g ∈ T, ∃ t ∈ M, ∃ c, t * g = c * d) → ∃ t ∈ M, ∀ g ∈ T, ∃ c, t * g = c * d := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, M.one_mem, by simp⟩
    | insert a S haS ih =>
      intro hT
      obtain ⟨t, htM, ht⟩ := ih (fun g hg => hT g (Finset.mem_insert_of_mem hg))
      obtain ⟨t', ht'M, c', hc'⟩ := hT a (Finset.mem_insert_self a S)
      refine ⟨t * t', M.mul_mem htM ht'M, fun g hg => ?_⟩
      rcases Finset.mem_insert.1 hg with rfl | hg
      · exact ⟨t * c', by rw [mul_assoc, hc', mul_assoc]⟩
      · obtain ⟨c, hc⟩ := ht g hg
        exact ⟨t' * c, by rw [mul_comm t t', mul_assoc, hc, mul_assoc]⟩
  obtain ⟨S, rfl⟩ := hJ
  obtain ⟨t, htM, ht⟩ := key S fun g hg => hone g (Ideal.subset_span hg)
  have hall : ∀ j ∈ Ideal.span (S : Set A), ∃ c, t * j = c * d := by
    intro j hj
    induction hj using Submodule.span_induction with
    | mem x hx => exact ht x hx
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [mul_add, ha, hb, add_mul]⟩
    | smul a x _ hx =>
      obtain ⟨b, hb⟩ := hx
      exact ⟨a * b, by rw [smul_eq_mul, mul_left_comm, hb, mul_assoc]⟩
  refine ⟨s₁ * t, M.mul_mem hs₁M htM, ?_, fun j hj => ?_⟩
  · rw [mul_comm s₁ t, mul_assoc]
    exact Ideal.mul_mem_left _ _ hs₁
  · obtain ⟨c, hc⟩ := hall j hj
    exact ⟨s₁ * c, by rw [mul_assoc, hc, mul_assoc]⟩

end GlobalTheory.IdealSpread

namespace GlobalTheory.IdealSpread

theorem ideal_eq_span_of_germ (X : Scheme.{0}) (I : X.IdealSheafData) (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1)
    (d : Γ(X, U.1)) (hN : IsNoetherianRing Γ(X, U.1))
    (h : (I.ideal U).map (X.presheaf.germ U.1 x₀ hx).hom = Ideal.span {(X.presheaf.germ U.1 x₀ hx).hom d}) :
    ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ ∀ t : Γ(X, U.1), X.basicOpen t ≤ X.basicOpen s →
      I.ideal (X.affineBasicOpen t) = Ideal.span {resG X (X.basicOpen_le t) d} := by
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x₀) := (X.presheaf.germ U.1 x₀ hx).hom.toAlgebra
  haveI hL : IsLocalization.AtPrime (X.presheaf.stalk x₀) (U.2.primeIdealOf ⟨x₀, hx⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x₀, hx⟩
  obtain ⟨s, hsM, hsd, hsJ⟩ := exists_of_map_eq_span (R := X.presheaf.stalk x₀)
    (U.2.primeIdealOf ⟨x₀, hx⟩).asIdeal.primeCompl (IsNoetherian.noetherian (I.ideal U)) d h
  refine ⟨s, (X.mem_basicOpen s x₀ hx).2 (IsLocalization.map_units (X.presheaf.stalk x₀) ⟨s, hsM⟩), fun t ht => ?_⟩
  have hu : IsUnit (resG X (X.basicOpen_le t) s) := by
    have h0 : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
    have h1 := h0.map (resG X ht)
    have e : resG X ht (resG X (X.basicOpen_le s) s) = resG X (X.basicOpen_le t) s := by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
      rfl
    rwa [e] at h1
  rw [← I.map_ideal_basicOpen U t]
  change (I.ideal U).map (resG X (X.basicOpen_le t)) = _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro j hj
    obtain ⟨c, hc⟩ := hsJ j hj
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨↑hu.unit⁻¹ * resG X (X.basicOpen_le t) c, ?_⟩
    have := congrArg (resG X (X.basicOpen_le t)) hc
    rw [map_mul, map_mul] at this
    rw [mul_assoc, ← this, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hm := Ideal.mem_map_of_mem (resG X (X.basicOpen_le t)) hsd
    rw [map_mul] at hm
    have := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : Γ(X, X.basicOpen t)) hm
    rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this

end GlobalTheory.IdealSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteFrameRealSpecialUnitaryStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_frame_real_special_unitary : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (Ψ : Finset (D.host.E →+* ℂ)) (Gm : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (x₀ : Frame Ψ V.rank) (σ : D.what₂.Tau ≃ Ψ) (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank) (π : (∀ ρ, Upq V ρ) → realSU Ψ Gm) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (J : Type) (s : J → Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → GA D V) (F : J → Set (realSU Ψ Gm)) (ρ₀ : D.what₂.Tau), Gm = -(V.gram)ᵀ → IsInfFam θ → IsRealPart V θ A rp → IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) Ψ Gm x₀ σ A e → (∀ ρ, (σ ρ).1 = tauE D ρ) → (∀ (s' : realSU Ψ Gm) (b₀ : ∀ ρ, Upq V ρ), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s'.1 (σ ρ) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) → ∀ b, π (b₀ * b) = s' * π b) → (∀ j, ∀ γ ∈ inReal Ψ Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)), ∀ y ∈ F j, γ * y ∈ F j → γ = 1) → (∀ (j j' : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E), g ∈ GQ V → matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → finE V ((h j')⁻¹ * g * h j) ∈ K → IsIntegral ℤ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det ∧ ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 → j = j')) → (∀ (j : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E), g ∈ GQ V → matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 → finE V ((h j)⁻¹ * g * h j) ∈ K → γ ∈ ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)) → ∀ g ∈ GQ V, ∀ (j j' : J) (y : GA D V), (finE V ((h j)⁻¹ * y) ∈ K ∧ π (rp y) ∈ F j ∧ 0 < (UpqT.mat (rp y ρ₀)).det.im) → (finE V ((h j')⁻¹ * (g * y)) ∈ K ∧ π (rp (g * y)) ∈ F j' ∧ 0 < (UpqT.mat (rp (g * y) ρ₀)).det.im) → UpperTheory.Ram.Sector.sec (NumberField.Units.torsionOrder D.host.E) (UpqT.mat (rp y ρ₀)).det = UpperTheory.Ram.Sector.sec (NumberField.Units.torsionOrder D.host.E) (UpqT.mat (rp (g * y) ρ₀)).det → g = 1 ∧ j = j' := by
  first | exact @GlobalTheory.TubePack.tube_disjoint | exact GlobalTheory.TubePack.tube_disjoint | (intros; apply GlobalTheory.TubePack.tube_disjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerFixesVacuumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeStabilizer_fixes_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @GlobalTheory.InertSph.vac_fixed' | exact GlobalTheory.InertSph.vac_fixed' | (intros; apply GlobalTheory.InertSph.vac_fixed' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerVacuumScalarEqOneStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeStabilizer_vacuumScalar_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @GlobalTheory.InertScalarLeft.scalar_eq_one | exact GlobalTheory.InertScalarLeft.scalar_eq_one | (intros; apply GlobalTheory.InertScalarLeft.scalar_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InhabitedAndRefines
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PolDeg
variable {R : Type} [CommRing R] [IsDomain R]

def ofDeg (D : DegPre R) (hB : D.TauBimult) : Data R := Wit.ofDeg D hB

theorem ofDeg_X (D : DegPre R) (hB : D.TauBimult) : (ofDeg D hB).X = D.X := rfl

theorem ofDeg_c (D : DegPre R) (hB : D.TauBimult) (a : D.X) : (ofDeg D hB).c a = D.c a := rfl

theorem exists_nontrivial (k : Type) [Field k] : ∃ Q : Data (PowerSeries k), Nontrivial Q.X :=
  ⟨ofDeg (GlobalTheory.ToricData.arcDataInt k).toPre (GlobalTheory.ToricData.arcDataInt k).tau_bimult, inferInstanceAs (Nontrivial ℤ)⟩

theorem refines_ofDeg (D : DegPre R) (hB : D.TauBimult) :
    Refines (ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) :=
  Wit.refines_ofDeg D hB

theorem inhabited_and_refines :
    (∀ (k : Type) [Field k], ∃ Q : Data (PowerSeries k), Nontrivial Q.X) ∧
    ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult),
      Refines (ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) :=
  ⟨fun k _ => exists_nontrivial k, fun _ _ _ D hB => refines_ofDeg D hB⟩

open GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.InhTate in

theorem isMonomialTau_arcData (k : Type) [Field k] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y) (hp : ∀ y, y ≠ 0 → 0 < be y y)
    (he : ∀ y, (2 : ℤ) ∣ be y y) :
    (ofDeg (arcData k be hs hp he).toPre (arcData k be hs hp he).tau_bimult).IsMonomialTau
      ![PowerSeries.X] ![be] := fun (a b : X) => by
  refine ⟨arcVar k ^ (be a b), ?_, cg _ _ 1, cg_isGen _ _ _, fun z J hJ => ?_⟩
  · rw [Fin.prod_univ_one]
    exact Units.val_zpow_eq_zpow_val _ _
  have e1 := (Wit.exists_tau (arcData k be hs hp he).toPre a b).choose_spec.2 _ (𝟙 _) z J hJ
  refine e1.trans ?_
  have e2 : val ((arcData k be hs hp he).toPre.tau a b) (𝟙 _) z J = gm (𝟙 _) z ⊤ (unitOn (arcVar k ^ (be a b))) := by
    exact (congrArg (gm _ z _) (arcData_tau_isConst k be hs hp he a b _)).trans (gm_res _ z _ (hJ.mem _ _) _)
  rw [e2]
  refine Eq.trans ?_ (congrArg (_ * ·) ((gm_res _ z _ (hJ.mem _ _) _).trans (map_one _))).symm
  exact (_root_.mul_one _).symm

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimEqLocalDomain
section
open IsLocalRing

namespace GlobalTheory

open IsLocalRing in

theorem _root_.GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain :
    ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R]
      [IsLocalRing R] (ψ : B →+* R), ψ.Finite → ringKrullDim R = ringKrullDim B →
      Function.Injective ψ := by
  intro B R _ _ _ _ _ _ ψ hψ hdim
  letI : Algebra B R := ψ.toAlgebra
  haveI : Module.Finite B R := hψ
  have hlt : ringKrullDim B < ⊤ := ringKrullDim_lt_top
  have hne : ringKrullDim B ≠ ⊥ := fun h =>
    (WithBot.bot_lt_coe (0 : ℕ∞)).not_ge (h ▸ (ringKrullDim_nonneg_of_nontrivial (R := B)))
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℕ∞) = m := by
    refine ENat.ne_top_iff_exists.mp ?_
    rintro rfl
    exact hlt.ne hm.symm
  exact _root_.GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq (A := B) (S := R) hm.symm
    (hdim.trans hm.symm)

end GlobalTheory
end

