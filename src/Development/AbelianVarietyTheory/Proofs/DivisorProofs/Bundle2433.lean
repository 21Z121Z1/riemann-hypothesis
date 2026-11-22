import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareActionBundleIso
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.PullPol

theorem swap_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hs : IsSquare φ φ₂) :
    (lift (snd G' G') (fst G' G')).left ≫ φ₂ = φ₂ ≫ (lift (snd G G) (fst G G)).left := by
  apply pullback.hom_ext
  · change _ ≫ φ₂ ≫ (fst G G).left = φ₂ ≫ (lift (snd G G) (fst G G)).left ≫ (fst G G).left
    rw [hs.1, ← Over.comp_left, lift_fst, hs.2, ← Category.assoc, ← Over.comp_left, lift_fst]
  · change _ ≫ φ₂ ≫ (snd G G).left = φ₂ ≫ (lift (snd G G) (fst G G)).left ≫ (snd G G).left
    rw [hs.2, ← Over.comp_left, lift_snd, hs.1, ← Category.assoc, ← Over.comp_left, lift_snd]

theorem act_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hs : IsSquare φ φ₂) (u' : G' ⟶ G') (u : G ⟶ G)
    (hu : u'.left ≫ φ = φ ≫ u.left) :
    (lift (fst G' G') (snd G' G' ≫ u')).left ≫ φ₂ = φ₂ ≫ (lift (fst G G) (snd G G ≫ u)).left := by
  apply pullback.hom_ext
  · change _ ≫ φ₂ ≫ (fst G G).left = φ₂ ≫ (lift (fst G G) (snd G G ≫ u)).left ≫ (fst G G).left
    rw [hs.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst, hs.1]
  · change _ ≫ φ₂ ≫ (snd G G).left = φ₂ ≫ (lift (fst G G) (snd G G ≫ u)).left ≫ (snd G G).left
    rw [hs.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd, Over.comp_left,
      Over.comp_left, Category.assoc, hu, ← Category.assoc, ← hs.2, Category.assoc]

end GlobalTheory.RealMult.PullPol

namespace GlobalTheory.RealMult.PullPol

open GlobalTheory.CechPic in

theorem pol_pull : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (rm' : OAct (𝓞 F) A'),
    (∀ a, (rm'.act a).left ≫ φ = φ ≫ (X.rm.act a).left) → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ (c c' : 𝔠.elt) (a : 𝓞 F),
      LBIso ((X.P c).pull φ₂) (((X.P c).pull φ₂).pull (lift (snd A' A') (fst A' A')).left) ∧
      LBIso ((X.P c').pull φ₂) (LB.div ((X.P (c + c')).pull φ₂) ((X.P c).pull φ₂)) ∧
      LBIso ((X.P (a • c)).pull φ₂) (((X.P c).pull φ₂).pull (lift (fst A' A') (snd A' A' ≫ rm'.act a)).left) := by
  intro F _ _ 𝔠 S S' X b A' _ _ φ _ rm' hact φ₂ hs c c' a
  have hP := X.isLB
  refine ⟨(cls_eq_iff (pull_isLB (hP c) φ₂) (pull_isLB (pull_isLB (hP c) φ₂) _)).1 ?_,
    (cls_eq_iff (pull_isLB (hP c') φ₂) (LB.isLB_div (pull_isLB (hP _) φ₂) (pull_isLB (hP c) φ₂))).1 ?_,
    (cls_eq_iff (pull_isLB (hP _) φ₂) (pull_isLB (pull_isLB (hP c) φ₂) _)).1 ?_⟩
  · have h := (cls_eq_iff (hP c) (pull_isLB (hP c) _)).2 (X.symm c)
    rw [cls_pull (hP c)] at h
    rw [cls_pull (pull_isLB (hP c) φ₂), cls_pull (hP c), ← GlobalTheory.CechPic.pull_comp, swap_comp hs,
      GlobalTheory.CechPic.pull_comp, ← h]
  · have h := (cls_eq_iff (hP c') (LB.isLB_div (hP _) (hP c))).2 (X.add c c')
    rw [cls_div (pull_isLB (hP _) φ₂) (pull_isLB (hP c) φ₂), cls_pull (hP c'), cls_pull (hP _), cls_pull (hP c), h,
      cls_div (hP _) (hP c), map_sub]
  · have h := (cls_eq_iff (hP _) (pull_isLB (hP c) _)).2 (X.smul a c)
    rw [cls_pull (hP c)] at h
    rw [cls_pull (pull_isLB (hP c) φ₂), cls_pull (hP c), ← GlobalTheory.CechPic.pull_comp, act_comp hs _ _ (hact a),
      GlobalTheory.CechPic.pull_comp, ← h, cls_pull (hP _)]

end GlobalTheory.RealMult.PullPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareActionSectionsGenerated
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolKerPull

theorem hasGen_pull_pull_comp {X Y Z W : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (ℓ : Z ⟶ Y)
    (g : W ⟶ Z) (m : W ⟶ X) (hm : g ≫ ℓ ≫ f = m) (h : HasGen ((L.pull f).pull ℓ)) : HasGen (L.pull m) := by
  obtain ⟨t, ht⟩ := h
  have h₁ : HasGen ((L.pull f).pull (g ≫ ℓ)) :=
    ⟨LB.pullGen (L.pull f) (fun _ : PUnit => ℓ) (fun _ => 1) t g,
      DVR.pullGen_isGen (L.pull f) (fun _ : PUnit => ℓ) (fun _ => 1) t ht g⟩
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨u, hu⟩ := RigidTranslate.gen_of_lbIso (pull_isLB (pull_isLB hL f) _) (pull_isLB hL _)
    (FamRep.lbIso_pull_pull hL f (g ≫ ℓ)) s hs
  have e : (g ≫ ℓ) ≫ f = m := by rw [Category.assoc, hm]
  subst e
  exact ⟨u, hu⟩

theorem ker_pull : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (rm' : OAct (𝓞 F) A'),
    (∀ a, (rm'.act a).left ≫ φ = φ ≫ (X.rm.act a).left) → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ (c : 𝔠.elt) (T : Over S') (x : T ⟶ A'),
      HasGen (((X.P c).pull φ₂).pull (lift (fst A' T) (snd A' T ≫ x)).left) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → x ≫ rm'.act a = 1 := by
  intro F _ _ 𝔠 S S' X b A' _ _ φ hφ rm' hact φ₂ hsq c T x hgen a ha
  let T₀ : Over S := Over.mk (T.hom ≫ b)
  let x₀ : T₀ ⟶ X.A := pushPt hφ.1.w x

  let Z' : Over S' := Over.mk ((snd X.A T₀).left ≫ T.hom)
  have w₁ : (fst X.A T₀).left ≫ X.A.hom = ((snd X.A T₀).left ≫ T.hom) ≫ b := by
    rw [Over.w (fst X.A T₀), Category.assoc]
    exact (Over.w (snd X.A T₀)).symm
  let p₁ : Z' ⟶ A' := Over.homMk (hφ.1.lift (fst X.A T₀).left ((snd X.A T₀).left ≫ T.hom) w₁)
    (hφ.1.lift_snd _ _ _)
  let p₂ : Z' ⟶ T := Over.homMk (snd X.A T₀).left rfl
  have hp₁ : p₁.left ≫ φ = (fst X.A T₀).left := hφ.1.lift_fst _ _ _
  have key : (lift p₁ p₂).left ≫ (lift (fst A' T) (snd A' T ≫ x)).left ≫ φ₂ =
      (lift (fst X.A T₀) (snd X.A T₀ ≫ x₀)).left := by
    have e : (lift p₁ p₂).left ≫ (lift (fst A' T) (snd A' T ≫ x)).left = (lift p₁ (p₂ ≫ x)).left := by
      rw [← Over.comp_left]; congr 1; simp
    rw [← Category.assoc, e]
    apply pullback.hom_ext
    · have h1 := hsq.1
      rw [Over.fst_left] at h1
      rw [Category.assoc, h1, ← Category.assoc, ← Over.comp_left, lift_fst, hp₁, ← Over.fst_left,
        ← Over.comp_left, lift_fst]
    · have h2 := hsq.2
      rw [Over.snd_left] at h2
      rw [Category.assoc, h2, ← Category.assoc, ← Over.comp_left, lift_snd, ← Over.snd_left,
        ← Over.comp_left, lift_snd, Over.comp_left, Over.comp_left, Category.assoc]
      rfl
  have hgen₀ : HasGen ((X.P c).pull (lift (fst X.A T₀) (snd X.A T₀ ≫ x₀)).left) :=
    hasGen_pull_pull_comp (X.isLB c) φ₂ _ (lift p₁ p₂).left _ key hgen
  have h₀ : x₀ ≫ X.rm.act a = 1 := X.ker c T₀ x₀ hgen₀ a ha
  have inj : ∀ {y z : T ⟶ A'}, pushPt hφ.1.w y = pushPt hφ.1.w z → y = z := fun {y z} h =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  apply inj
  have hpa : pushPt hφ.1.w (x ≫ rm'.act a) = x₀ ≫ X.rm.act a :=
    Over.OverMorphism.ext (by
      show (x.left ≫ (rm'.act a).left) ≫ φ = (x.left ≫ φ) ≫ (X.rm.act a).left
      rw [Category.assoc, hact, Category.assoc])
  rw [hpa, h₀]
  exact (map_one (pushHom hφ T)).symm

end GlobalTheory.PolKerPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareDiagonalRelAmple
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.Obj

theorem relAmple_diag_of_isGrpPullback : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A' (((X.P c).pull φ₂).pull (lift (𝟙 A') (𝟙 A')).left) := by
  intro F _ _ 𝔠 S S' X b A' _ _ φ hg φ₂ hsq c hc
  haveI : IsProper X.A.hom := X.ab.proper
  have hP : IsPullback φ A'.hom X.A.hom b := hg.1
  haveI : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) hP inferInstance
  have hM := pull_isLB (X.isLB c) (lift (𝟙 X.A) (𝟙 X.A)).left
  have h1 : Out.RelAmple A' (((X.P c).pull (lift (𝟙 X.A) (𝟙 X.A)).left).pull φ) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hM (X.pos c hc) hP
  have hL := pull_isLB (pull_isLB (X.isLB c) φ₂) (lift (𝟙 A') (𝟙 A')).left
  have hM' := pull_isLB hM φ
  have key : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · show ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂) ≫ (fst X.A X.A).left =
        (φ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left) ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
        ← Over.comp_left, lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
    · show ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂) ≫ (snd X.A X.A).left =
        (φ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left) ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
        ← Over.comp_left, lift_snd, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hL hM' (N := 1) le_rfl ?_ h1
  rw [one_smul]
  show GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.cls _ (X.isLB c))) =
    GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.cls _ (X.isLB c)))
  rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, key]

end GlobalTheory.RealMult.Obj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareDiagonalSectionsGenerated
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RigPull

theorem hasGen_pull_of_comm {X₀ X Y Y₀ : Scheme.{0}} {L : LB X₀} (hL : L.IsLB) (F : X ⟶ X₀) {a : Y₀ ⟶ X₀}
    {a' : Y ⟶ X} {ψ : Y ⟶ Y₀} (e : a' ≫ F = ψ ≫ a) (h : HasGen (L.pull a)) : HasGen ((L.pull F).pull a') := by
  refine (CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hL F) a')).1 ?_
  have h0 : CechPic.cls _ (pull_isLB hL a) = 0 := (CechPic.cls_eq_zero_iff (pull_isLB hL a)).2 h
  rw [CechPic.cls_pull (pull_isLB hL F) a', CechPic.cls_pull hL F, ← CechPic.pull_comp, e, CechPic.pull_comp,
    ← CechPic.cls_pull hL a (pull_isLB hL a), h0, map_zero]

end GlobalTheory.RigPull

namespace GlobalTheory

open RigPull SiegelDescent

theorem hasGen_pull_rig_of_isGrpPullback : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ c : 𝔠.elt, HasGen (((X.P c).pull φ₂).pull (lift (1 : A' ⟶ A') (𝟙 A')).left) ∧
      HasGen (((X.P c).pull φ₂).pull (lift (𝟙 A') (1 : A' ⟶ A')).left) := by
  intro F _ _ 𝔠 S S' X b A' _ _ φ hp φ₂ sq c
  have hφ : φ ≫ X.A.hom = A'.hom ≫ b := hp.1.w
  have one := one_comp hp A' X.A φ hφ
  have idφ : (𝟙 A' : A' ⟶ A').left ≫ φ = φ ≫ (𝟙 X.A : X.A ⟶ X.A).left := by simp
  exact ⟨hasGen_pull_of_comm (X.isLB c) φ₂ (lift_square sq one idφ) (X.rig₁ c),
    hasGen_pull_of_comm (X.isLB c) φ₂ (lift_square sq idφ one) (X.rig₂ c)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushSecOfLeft
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelPull

theorem push_sec_of_left {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hpb : IsGrpPullback A' A f φ) {x : 𝟙_ (Over S) ⟶ A} {x' : 𝟙_ (Over S') ⟶ A'}
    (hx : x'.left ≫ φ = f ≫ x.left) (T : Over S') :
    pushHom hpb T (toUnit T ≫ x') = toUnit (Over.mk (T.hom ≫ f)) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ x'.left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ x.left
  rw [Category.assoc, hx, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem isSympLev_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A]
    [IsCommMonObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left}
    (hpb : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (G2 A).left} {P' : LB (G2 A').left}
    (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) {h M : ℕ} {B : Type} [CommRing B] {ζ : B}
    {s : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)}
    {lev' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A')} (hl : ∀ a, (lev' a).left ≫ φ = f ≫ (lev a).left)
    (hS : IsSympLev P h M ζ s lev) : IsSympLev P' h M ζ (f ≫ s) lev' := by
  have hp' : ∀ a, pushHom hpb _ (lev' a) = toUnit _ ≫ lev a := fun a => by
    have e := push_sec_of_left hpb (hl a) (𝟙_ (Over S'))
    rwa [toUnit_unit, Category.id_comp] at e
  refine ⟨fun a b => push_injective hpb _ ?_, fun a => push_injective hpb _ ?_, ?_⟩
  · rw [map_mul, hp', hp', hp', hS.1, MonObj.comp_mul]
  · rw [map_pow, map_one, hp', ← MonObj.comp_pow, hS.2.1, MonObj.comp_one]
  intro k _ _ x β z hx hz
  obtain ⟨g₁, g₂, g₃⟩ := hS.2.2 k (x ≫ f) β z (by rw [Category.assoc, hx]) hz
  refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
  · rw [← (push_injective hpb (Over.mk x)).eq_iff, push_sec_of_left hpb (hl a), map_one]
    rfl
  · obtain ⟨a, ha⟩ := g₂ (pushHom hpb (Over.mk x) g) (by
      have := congrArg (pushHom hpb (Over.mk x)) hg
      rw [map_pow, map_one] at this
      exact this)
    exact ⟨a, push_injective hpb _ ((push_sec_of_left hpb (hl a) _).trans ha)⟩
  · exact (weilIs_grpPullback_of_comm S S' A A' f φ _ _ (pull_isLB hP _) (pull_isLB hP' _) hpb
      (diag_iso sq H) (Over.mk x) M _ _ _ _ _
      (congrArg (fun q => q.left) (push_sec_of_left hpb (hl a) (Over.mk x)).symm)
      (congrArg (fun q => q.left) (push_sec_of_left hpb (hl b) (Over.mk x)).symm)).2 (g₃ a b)

theorem kerBy_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂)
    {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) (d : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ d = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x ^ d = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine push_injective h T ?_
  rw [map_pow, map_one]
  refine hn _ (pushHom h T x) ?_
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

theorem siegKerBy_pull {S S' : Scheme.{0}} {h M : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c : SiegPre h M ζ s} {c' : SiegPre h M ζ' s'} {f : S' ⟶ S}
    (m : SiegPB c' c f) {d : ℕ} (hc : SiegKerBy c d) : SiegKerBy c' d := by
  obtain ⟨φ, φ₂, pb, sq, iso, -⟩ := m
  exact ⟨(GlobalTheory.pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
    (diag_iso sq iso)).2.1 hc.1, kerBy_pull pb sq c.isLB c'.isLB iso d hc.2⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushoutQuotientSurjectiveKerEqMap
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pushout_quotient_map_eq_quotient_map_ideal : ∀ (R C E : Type) [CommRing R] [CommRing C] [CommRing E] (c : Ideal R) (f : R →+* C) (π : C →+* E) (χ : R ⧸ c →+* E), IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom χ) → Function.Surjective π ∧ RingHom.ker π = c.map f := by
  intro R C E _ _ _ c f π χ h
  have hw' : ∀ r, π (f r) = χ (Ideal.Quotient.mk c r) := fun r => by
    have := congrArg (fun g => g.hom r) h.w
    simpa using this
  have hle : c.map f ≤ RingHom.ker π := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp [RingHom.mem_ker, hw', Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  let q : C →+* C ⧸ c.map f := Ideal.Quotient.mk _
  let qm : R ⧸ c →+* C ⧸ c.map f := Ideal.quotientMap (c.map f) f Ideal.le_comap_map
  let φ : C ⧸ c.map f →+* E := Ideal.Quotient.lift _ π (fun x hx => hle hx)
  have hcomm : CommRingCat.ofHom f ≫ CommRingCat.ofHom q =
      CommRingCat.ofHom (Ideal.Quotient.mk c) ≫ CommRingCat.ofHom qm := by
    ext r; rfl
  let ψ := h.desc (CommRingCat.ofHom q) (CommRingCat.ofHom qm) hcomm
  have h1 : CommRingCat.ofHom π ≫ ψ = CommRingCat.ofHom q := h.inl_desc _ _ _
  have h2 : CommRingCat.ofHom χ ≫ ψ = CommRingCat.ofHom qm := h.inr_desc _ _ _
  have hid : ψ ≫ CommRingCat.ofHom φ = 𝟙 _ := by
    apply h.hom_ext
    · rw [← Category.assoc, h1, Category.comp_id]
      ext x; rfl
    · rw [← Category.assoc, h2, Category.comp_id]
      ext r
      change φ (qm (Ideal.Quotient.mk c r)) = χ (Ideal.Quotient.mk c r)
      rw [← hw']
      rfl
  have hφsurj : Function.Surjective φ := fun e =>
    ⟨ψ e, by
      have := congrArg (fun g => g.hom e) hid
      simpa using this⟩
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨y, hy⟩ := hφsurj e
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, hy⟩
  · refine le_antisymm ?_ hle
    intro x hx
    have hx1 : ψ.hom (π x) = q x := by
      rw [← CommRingCat.hom_ofHom q, ← h1]; rfl
    rw [RingHom.mem_ker] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q x = 0
    rw [← hx1, hx, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoTorsion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RankTwoTorsion

theorem ptorsion_sub (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M]
    (N : ℕ) (𝔭 : Ideal (𝓞 F)) (hN𝔭 : (N : 𝓞 F) ∈ 𝔭) (n : ℕ) (x : M) (hx : ∀ a ∈ 𝔭 ^ n, a • x = 0) :
    (N ^ n) • x = 0 := by
  have := hx _ (Ideal.pow_mem_pow hN𝔭 n)
  rwa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this

theorem rank_two_torsion (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M]
    (N : ℕ) (hN : 1 ≤ N)
    (h2 : ∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F))
    (h3 : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 → ∃ C : ℕ, ∀ n : ℕ,
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0} ≤ C * Ideal.absNorm 𝔭 ^ (2 * n)) :
    ∃ p : Fin 2 → M, (∀ i, N • p i = 0) ∧
      (∀ a b : 𝓞 F, a • p 0 + b • p 1 = 0 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1 := by
  have hfin : ∀ j : ℕ, Finite {x : M // (N ^ j) • x = 0} := fun j => by
    apply Nat.finite_of_card_ne_zero
    rw [h2 j]; positivity
  have hdiv := GlobalTheory.T.torsion_lift_number_field_module F M N hN h2
  have hfin1 : Finite {x : M // N • x = 0} := by simpa using hfin 1
  have hp : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
      Nat.card {x : M // ∀ a ∈ 𝔭, a • x = 0} ≤ Ideal.absNorm 𝔭 ^ 2 := by
    intro 𝔭 h𝔭 hN𝔭
    obtain ⟨C, hC⟩ := h3 𝔭 h𝔭 hN𝔭
    obtain ⟨e, he, hblk⟩ := GlobalTheory.T.torsion_count_multiplicative_prime_powers F M N hN hfin hdiv 𝔭 h𝔭 hN𝔭
    have hfinp : ∀ n, Finite {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0} := fun n =>
      Finite.of_injective (fun x => (⟨x.1, ptorsion_sub F M N 𝔭 hN𝔭 n x.1 x.2⟩ :
        {x : M // (N ^ n) • x = 0})) (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
    have h0 : Nat.card {x : M // ∀ a ∈ 𝔭 ^ 0, a • x = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨0, fun a _ => smul_zero a⟩⟩⟩
      have hx := x.2 1 (by simp); have hy := y.2 1 (by simp)
      simp only [one_smul] at hx hy; rw [hx, hy]
    have := GlobalTheory.T.log_concave_multiplicative_growth_bound (fun n => Nat.card {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0}) e C
      (Ideal.absNorm 𝔭 ^ 2) he h0
      (fun n => by
        haveI := hfinp n
        haveI : Nonempty {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0} := ⟨⟨0, fun a _ => smul_zero a⟩⟩
        exact Nat.card_pos (α := {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0}))
      (fun k => GlobalTheory.T.torsion_count_log_concave_prime_powers F M 𝔭 h𝔭 k (hfinp (k + 2))) hblk
      (fun n => by rw [← pow_mul]; exact hC n)
    simpa using this
  obtain ⟨p, hpN, hgen⟩ := GlobalTheory.T.torsion_two_generators_global F M N hN hfin1
    (fun 𝔭 h𝔭 hN𝔭 => GlobalTheory.T.torsion_two_generators_mod_prime F M N hN hfin1 𝔭 h𝔭 hN𝔭 (hp 𝔭 h𝔭 hN𝔭))
  exact ⟨p, hpN, GlobalTheory.T.torsion_basis_relations_divisible F M N hN (by simpa using h2 1) p hpN hgen, hgen⟩

end GlobalTheory.RankTwoTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionAppOfPreservesGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc

theorem fnOf_app_of_pff : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (m : Y ⟶ X) (φ : X.functionField →+* Y.functionField), PFF (𝟙 _) m φ → ∀ (V : X.Opens) (hV : genericPoint X ∈ V) (hV' : genericPoint Y ∈ m ⁻¹ᵁ V) (a : Γ(X, V)), fnOf (m ⁻¹ᵁ V) hV' ((m.app V).hom a) = φ (fnOf V hV a) := by
  intro X Y _ _ m φ hφ V hV hV' a
  have h : gp Y ≫ m = spMap φ ≫ gp X := by
    obtain ⟨l, h1, h2⟩ := hφ
    rw [Category.comp_id] at h1
    rw [← h1, h2]
  have hloc : IsLocalHom φ := inferInstance
  have e1 : Spec.map (m.stalkMap (genericPoint Y)) ≫ X.fromSpecStalk (m (genericPoint Y)) =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X) := by
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk]; exact h
  have e2 := (SpecToEquivOfLocalRing X (CommRingCat.of Y.functionField)).symm.injective
    (a₁ := ⟨m (genericPoint Y), m.stalkMap (genericPoint Y), inferInstance⟩)
    (a₂ := ⟨genericPoint X, CommRingCat.ofHom φ, hloc⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]; exact e1)
  obtain ⟨h₁, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simp only at e3
  have key : X.presheaf.germ V _ hV' ≫ m.stalkMap (genericPoint Y) =
      X.presheaf.germ V _ hV ≫ CommRingCat.ofHom φ := by
    rw [e3, TopCat.Presheaf.stalkCongr_hom]
    exact X.presheaf.germ_stalkSpecializes_assoc hV' _ _
  have key' : m.app V ≫ Y.presheaf.germ (m ⁻¹ᵁ V) (genericPoint Y) hV' =
      X.presheaf.germ V _ hV ≫ CommRingCat.ofHom φ :=
    (Scheme.Hom.germ_stalkMap m V (genericPoint Y) hV').symm.trans key
  exact congrArg (fun q => CommRingCat.Hom.hom q a) key'

end GlobalTheory.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedFiniteTypeIntFiniteIndexProdNormalDomainsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_finiteType_int_exists_finite_prod_normalDomains_nonzero_conductor : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] [Nontrivial R], ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, Algebra R (D i)), (∀ i, IsDomain (D i) ∧ IsIntegrallyClosed (D i) ∧ Module.Finite R (D i)) ∧ Function.Injective (algebraMap R (∀ i, D i)) ∧ ∃ a : R, a ≠ 0 ∧ ∀ r : (∀ i, D i), ∃ y : R, algebraMap R (∀ i, D i) y = algebraMap R (∀ i, D i) a * r := by
  first | exact @GlobalTheory.ReducedNormalisation.exists_finiteIndex_prod_normalDomains | exact GlobalTheory.ReducedNormalisation.exists_finiteIndex_prod_normalDomains | (intros; apply GlobalTheory.ReducedNormalisation.exists_finiteIndex_prod_normalDomains <;> assumption)
end

