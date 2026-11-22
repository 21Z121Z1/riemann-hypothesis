import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2340
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftHomomorphismOfSquareZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift.Hom

theorem one_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  let x : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
  have e : x * x = x := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 x x rfl rfl, _root_.mul_one]; rfl)
  have e' : x = 1 := by simpa using e
  have := congrArg (fun z ↦ z.left) e'
  refine this.trans ?_
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] (T : Over S) :
    (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem liftHom_sq : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftHom (divided₂ hI) π := by
  intro P R R₀ _ _ I hI π hπ hk H g A₀ _ A _ i h hA hg g' B₀ _ B _ j k hB hg' f₀ _ hf
  have pA := (P.1 R A g hA hg).1
  have pB := (P.1 R B g' hB hg').1
  obtain ⟨l, l₁, l₂⟩ : ∃ l : (A₀ ⊗ B₀).left ⟶ (A ⊗ B).left, l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i ∧
      l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j :=
    ⟨Limits.pullback.lift ((fst A₀ B₀).left ≫ i) ((snd A₀ B₀).left ≫ j) (by
      rw [Category.assoc, Category.assoc, h.1.w, k.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_lift_shearMap_squareZero_abelianSchemes R R₀ I hI π hπ hk H g g' A₀ B₀ A B i j h k hA hB hg hg' A B i j h.1 k.1
    hA.smooth hB.smooth η[A].left η[B].left (Over.w η[A]) (Over.w η[B])
    ((one_left_comp h _).trans (Category.id_comp _)) ((one_left_comp k _).trans (Category.id_comp _)) l l₁ l₂ f₀
    (by rw [schemeFil_eq_liftFil _ h pA, schemeFil_eq_liftFil _ k pB]; exact hf)
  refine GlobalTheory.T.existsUnique_isMonHom_lift_of_grpPullback_abelian R R₀ π hπ ⟨2, hk ▸ hI⟩ A₀ B₀ A B i j h k hA hB f₀ (lift (𝟙 A) 1 ≫ φ) ?_
  have e : i ≫ (lift (𝟙 A) (1 : A ⟶ B)).left = (lift (𝟙 A₀) (1 : A₀ ⟶ B₀)).left ≫ l := by
    refine Limits.pullback.hom_ext ?_ ?_
    · change (i ≫ _) ≫ (fst A B).left = (_ ≫ l) ≫ (fst A B).left
      rw [Category.assoc, Category.assoc, l₁, ← Over.comp_left, ← Category.assoc, ← Over.comp_left, lift_fst, lift_fst,
        Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
    · change (i ≫ _) ≫ (snd A B).left = (_ ≫ l) ≫ (snd A B).left
      rw [Category.assoc, Category.assoc, l₂, ← Over.comp_left, ← Category.assoc, ← Over.comp_left, lift_snd, lift_snd,
        one_left_comp k, one_left, ← Category.assoc, h.1.w, Category.assoc]
  rw [Over.comp_left, ← Category.assoc, e, Category.assoc, hφ, ← Category.assoc, ← Over.comp_left, comp_mul,
    lift_fst_assoc, lift_snd, _root_.mul_one, Category.id_comp]

end GlobalTheory.SqLift.Hom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawGlueOverCoprodBase
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdGlue

variable {T T₁ : Scheme.{0}}

theorem isPb (Y : Over T) : IsPullback (fst Y Y).left (snd Y Y).left Y.hom Y.hom :=
  IsPullback.of_hasPullback Y.hom Y.hom

theorem tens_hom (Y : Over T) : (Y ⊗ Y).hom = (fst Y Y).left ≫ Y.hom := (Over.w (fst Y Y)).symm

noncomputable def incl (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : (Y₁ ⊗ Y₁).left ⟶ (Y ⊗ Y).left :=
  (isPb Y).lift ((fst Y₁ Y₁).left ≫ j) ((snd Y₁ Y₁).left ≫ j) (by
    rw [Category.assoc, Category.assoc, w, ← Category.assoc, ← Category.assoc, (isPb Y₁).w])

@[reassoc (attr := simp)] theorem incl_fst (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : incl v Y Y₁ j w ≫ (fst Y Y).left = (fst Y₁ Y₁).left ≫ j :=
  (isPb Y).lift_fst _ _ _

@[reassoc (attr := simp)] theorem incl_snd (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : incl v Y Y₁ j w ≫ (snd Y Y).left = (snd Y₁ Y₁).left ≫ j :=
  (isPb Y).lift_snd _ _ _

theorem incl_pullback (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (h : IsPullback j Y₁.hom Y.hom v) :
    IsPullback (incl v Y Y₁ j h.w) (Y₁ ⊗ Y₁).hom (Y ⊗ Y).hom v := by
  have w : incl v Y Y₁ j h.w ≫ (Y ⊗ Y).hom = (Y₁ ⊗ Y₁).hom ≫ v := by
    rw [tens_hom, tens_hom, incl_fst_assoc, h.w, Category.assoc]
  have e1 : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, (s.fst ≫ (fst Y Y).left) ≫ Y.hom = s.snd ≫ v := fun s => by
    rw [Category.assoc, ← tens_hom, s.condition]
  have e2 : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, (s.fst ≫ (snd Y Y).left) ≫ Y.hom = s.snd ≫ v := fun s => by
    rw [Category.assoc, ← (isPb Y).w, ← tens_hom, s.condition]
  let lf : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, s.pt ⟶ (Y₁ ⊗ Y₁).left := fun s =>
    (isPb Y₁).lift (h.lift (s.fst ≫ (fst Y Y).left) s.snd (e1 s)) (h.lift (s.fst ≫ (snd Y Y).left) s.snd (e2 s))
      (by rw [h.lift_snd, h.lift_snd])
  have lf1 : ∀ s, lf s ≫ (fst Y₁ Y₁).left = h.lift (s.fst ≫ (fst Y Y).left) s.snd (e1 s) :=
    fun s => (isPb Y₁).lift_fst _ _ _
  have lf2 : ∀ s, lf s ≫ (snd Y₁ Y₁).left = h.lift (s.fst ≫ (snd Y Y).left) s.snd (e2 s) :=
    fun s => (isPb Y₁).lift_snd _ _ _
  refine ⟨⟨w⟩, ⟨Limits.PullbackCone.IsLimit.mk w lf ?_ ?_ ?_⟩⟩
  · intro s
    apply (isPb Y).hom_ext
    · rw [Category.assoc, incl_fst, reassoc_of% (lf1 s), h.lift_fst]
    · rw [Category.assoc, incl_snd, reassoc_of% (lf2 s), h.lift_fst]
  · intro s
    rw [tens_hom Y₁, reassoc_of% (lf1 s), h.lift_snd]
  · intro s m hm1 hm2
    rw [tens_hom Y₁] at hm2
    apply (isPb Y₁).hom_ext
    · rw [lf1]
      apply h.hom_ext
      · rw [h.lift_fst, Category.assoc, ← incl_fst v Y Y₁ j h.w, reassoc_of% hm1]
      · rw [h.lift_snd]; simpa only [Category.assoc] using hm2
    · rw [lf2]
      apply h.hom_ext
      · rw [h.lift_fst, Category.assoc, ← incl_snd v Y Y₁ j h.w, reassoc_of% hm1]
      · rw [h.lift_snd, ← hm2, Category.assoc, (isPb Y₁).w]

theorem incl_mul (f : T₁ ⟶ T) (A : Over T) [GrpObj A] (B : Over T₁) [GrpObj B] (φ : B.left ⟶ A.left)
    (h : IsGrpPullback B A f φ) : incl f A B φ h.1.w ≫ (μ[A]).left = (μ[B]).left ≫ φ := by
  let x₀ : Over.mk ((B ⊗ B).hom ≫ f) ⟶ A := Over.homMk ((fst B B).left ≫ φ) (by
    show _ = (B ⊗ B).hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  let y₀ : Over.mk ((B ⊗ B).hom ≫ f) ⟶ A := Over.homMk ((snd B B).left ≫ φ) (by
    show _ = (B ⊗ B).hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, ← (isPb B).w, Over.w])
  have hm := h.2 (B ⊗ B) (fst B B) (snd B B) x₀ y₀ rfl rfl
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at hm
  have e : incl f A B φ h.1.w = (lift x₀ y₀).left := by
    apply (isPb A).hom_ext
    · rw [incl_fst, ← Over.comp_left, lift_fst]; rfl
    · rw [incl_snd, ← Over.comp_left, lift_snd]; rfl
  rw [e]; exact hm

theorem colim_of_pullbacks {T T₁ T₂ : Scheme.{0}} (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T)
    (hT : Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) (Y : Over T) (Y₁ : Over T₁) (Y₂ : Over T₂)
    (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left)
    (h₁ : IsPullback j₁ Y₁.hom Y.hom v₁) (h₂ : IsPullback j₂ Y₂.hom Y.hom v₂) :
    Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (incl v₁ Y Y₁ j₁ h₁.w) (incl v₂ Y Y₂ j₂ h₂.w))) := by
  refine (((BinaryCofan.isVanKampen_iff _).1 (FinitaryExtensive.vanKampen _ hT)
    (Limits.BinaryCofan.mk (incl v₁ Y Y₁ j₁ h₁.w) (incl v₂ Y Y₂ j₂ h₂.w)) (Y₁ ⊗ Y₁).hom (Y₂ ⊗ Y₂).hom (Y ⊗ Y).hom
    ?_ ?_).2 ⟨incl_pullback v₁ Y Y₁ j₁ h₁, incl_pullback v₂ Y Y₂ j₂ h₂⟩)
  · exact (incl_pullback v₁ Y Y₁ j₁ h₁).w.symm
  · exact (incl_pullback v₂ Y Y₂ j₂ h₂).w.symm

end GlobalTheory.ProdGlue

open GlobalTheory.ProdGlue in
theorem GlobalTheory.ProdGlue.mul_glue : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂) (A₁ : Over S₁) [GrpObj A₁] (A₂ : Over S₂) [GrpObj A₂] (B₁ : Over T₁) [GrpObj B₁] (B₂ : Over T₂) [GrpObj B₂] (A₀ : Over T) [GrpObj A₀] (i₁ : B₁.left ⟶ A₁.left) (i₂ : B₂.left ⟶ A₂.left) (j₁ : B₁.left ⟶ A₀.left) (j₂ : B₂.left ⟶ A₀.left), IsGrpPullback B₁ A₁ f₁ i₁ → IsGrpPullback B₂ A₂ f₂ i₂ → IsGrpPullback B₁ A₀ v₁ j₁ → IsGrpPullback B₂ A₀ v₂ j₂ → ∀ (i : A₀.left ⟶ A₁.left ⨿ A₂.left), j₁ ≫ i = i₁ ≫ Limits.coprod.inl → j₂ ≫ i = i₂ ≫ Limits.coprod.inr → ∃ m : Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⟶ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)), ∀ l : (A₀ ⊗ A₀).left ⟶ (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))).left, l ≫ (fst (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (fst A₀ A₀).left ≫ i → l ≫ (snd (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (snd A₀ A₀).left ≫ i → l ≫ m.left = (μ[A₀]).left ≫ i := by

  intro S S₁ S₂ T T₁ T₂ u₁ u₂ ⟨hS⟩ v₁ v₂ ⟨hT⟩ f₁ f₂ A₁ _ A₂ _ B₁ _ B₂ _ A₀ _ i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ i ei₁ ei₂
  set X := Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) with hX
  have hV := (BinaryCofan.isVanKampen_iff _).1 (FinitaryExtensive.vanKampen _ hS)
    (Limits.BinaryCofan.mk (Limits.coprod.inl : A₁.left ⟶ A₁.left ⨿ A₂.left) Limits.coprod.inr) A₁.hom A₂.hom X.hom
    (Limits.coprod.inl_desc _ _).symm (Limits.coprod.inr_desc _ _).symm
  have pX : _ := hV.1 ⟨Limits.coprodIsCoprod _ _⟩
  have pX₁ : IsPullback (Limits.coprod.inl : A₁.left ⟶ A₁.left ⨿ A₂.left) A₁.hom X.hom u₁ := pX.1
  have pX₂ : IsPullback (Limits.coprod.inr : A₂.left ⟶ A₁.left ⨿ A₂.left) A₂.hom X.hom u₂ := pX.2
  obtain ⟨cX⟩ := colim_of_pullbacks u₁ u₂ hS X A₁ A₂ _ _ pX₁ pX₂
  obtain ⟨c0⟩ := colim_of_pullbacks v₁ v₂ hT A₀ B₁ B₂ _ _ hj₁.1 hj₂.1
  have D := Limits.BinaryCofan.IsColimit.desc' cX
    ((μ[A₁]).left ≫ Limits.coprod.inl) ((μ[A₂]).left ≫ Limits.coprod.inr)
  let ml : (X ⊗ X).left ⟶ X.left := D.1
  have hm₁ : incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ ml = (μ[A₁]).left ≫ Limits.coprod.inl := D.2.1
  have hm₂ : incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ ml = (μ[A₂]).left ≫ Limits.coprod.inr := D.2.2
  have hw : ml ≫ X.hom = (X ⊗ X).hom := by
    apply Limits.BinaryCofan.IsColimit.hom_ext cX
    · change incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ ml ≫ X.hom = incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ (X ⊗ X).hom
      rw [← Category.assoc, hm₁, Category.assoc, tens_hom, incl_fst_assoc]
      simp only [X, Over.mk_hom, Limits.coprod.inl_desc]
      rw [← Category.assoc, Over.w, ← Category.assoc, Over.w]
    · change incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ ml ≫ X.hom = incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ (X ⊗ X).hom
      rw [← Category.assoc, hm₂, Category.assoc, tens_hom, incl_fst_assoc]
      simp only [X, Over.mk_hom, Limits.coprod.inr_desc]
      rw [← Category.assoc, Over.w, ← Category.assoc, Over.w]
  refine ⟨Over.homMk ml hw, fun l hl₁ hl₂ => ?_⟩
  change l ≫ ml = _
  have key : ∀ {Tk Sk : Scheme.{0}} (vk : Tk ⟶ T) (uk : Sk ⟶ S) (fk : Tk ⟶ Sk) (Ak : Over Sk) [GrpObj Ak]
      (Bk : Over Tk) [GrpObj Bk] (ik : Bk.left ⟶ Ak.left) (jk : Bk.left ⟶ A₀.left) (ink : Ak.left ⟶ X.left)
      (hik : IsGrpPullback Bk Ak fk ik) (hjk : IsGrpPullback Bk A₀ vk jk) (eik : jk ≫ i = ik ≫ ink)
      (κ : (Ak ⊗ Ak).left ⟶ (X ⊗ X).left)
      (κf : κ ≫ (fst X X).left = (fst Ak Ak).left ≫ ink) (κs : κ ≫ (snd X X).left = (snd Ak Ak).left ≫ ink)
      (hmk : κ ≫ ml = (μ[Ak]).left ≫ ink),
      incl vk A₀ Bk jk hjk.1.w ≫ l ≫ ml = incl vk A₀ Bk jk hjk.1.w ≫ (μ[A₀]).left ≫ i := by
    intro Tk Sk vk uk fk Ak _ Bk _ ik jk ink hik hjk eik κ κf κs hmk
    have e : incl vk A₀ Bk jk hjk.1.w ≫ l = incl fk Ak Bk ik hik.1.w ≫ κ := by
      apply (isPb X).hom_ext
      · rw [Category.assoc, hl₁, incl_fst_assoc, eik, Category.assoc, κf, incl_fst_assoc]
      · rw [Category.assoc, hl₂, incl_snd_assoc, eik, Category.assoc, κs, incl_snd_assoc]
    rw [reassoc_of% e, hmk, reassoc_of% (incl_mul fk Ak Bk ik hik), reassoc_of% (incl_mul vk A₀ Bk jk hjk), eik]
  apply Limits.BinaryCofan.IsColimit.hom_ext c0
  · exact key v₁ u₁ f₁ A₁ B₁ i₁ j₁ _ hi₁ hj₁ ei₁ _ (incl_fst _ _ _ _ _) (incl_snd _ _ _ _ _) hm₁
  · exact key v₂ u₂ f₂ A₂ B₂ i₂ j₂ _ hi₂ hj₂ ei₂ _ (incl_fst _ _ _ _ _) (incl_snd _ _ _ _ _) hm₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentUniquenessStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_lift_tangent_uniqueness : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  first | exact @GlobalTheory.ConstDeform.objMap_const | exact GlobalTheory.ConstDeform.objMap_const | (intros; apply GlobalTheory.ConstDeform.objMap_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpLawAndUnitAgreeOfOpenInDescentModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc.UAgree

theorem ext_of_schDom {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated s›
  let U' : Over Z := Over.mk (d ≫ f ≫ s)
  let d' : U' ⟶ X' := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := by
    ext1
    exact hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  have hfg : f' = g' := (cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')
  exact congrArg CommaMorphism.left hfg

theorem schDom_away {R : Type} [CommRing R] [IsDomain R] {f : R} (hf : f ≠ 0) {T : Scheme.{0}} (q : T ⟶ Sp R)
    [Flat q] : IsSchemeTheoreticallyDominant (pullback.fst q (awayMap f)) := by
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsDominant (awayMap f) :=
    ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
  have : IsSchemeTheoreticallyDominant (awayMap f) := .of_isDominant _
  infer_instance

theorem ext_generic {R : Type} [CommRing R] [IsDomain R] {f : R} (hf : f ≠ 0) {T P : Scheme.{0}}
    (q : T ⟶ Sp R) [Flat q] (p : P ⟶ Sp R) [IsSeparated p] (u v : T ⟶ P) (hu : u ≫ p = q) (hv : v ≫ p = q)
    (h : pullback.fst q (awayMap f) ≫ u = pullback.fst q (awayMap f) ≫ v) : u = v := by
  haveI := schDom_away hf q
  exact ext_of_schDom p (hu.trans hv.symm) _ h

theorem flat_of_openIn {S S₁ P Y : Scheme.{0}} {h : Y ⟶ P} {q : Y ⟶ S₁} {p : P ⟶ S} {s : S₁ ⟶ S}
    (ho : OpenIn h q p s) [Flat s] : Flat h := by
  obtain ⟨w, hw⟩ := ho
  haveI := hw
  rw [← pullback.lift_fst h q w]
  infer_instance

variable {σ : Setup} (E : Emb σ)

def toA {T : Scheme.{0}} (x : T ⟶ E.P) (k : T ⟶ Sp (Localization.Away σ.f)) (w : x ≫ E.p = k ≫ awayMap σ.f) :
    Over.mk k ⟶ σ.A :=
  Over.homMk (E.cartA.lift x k w) (E.cartA.lift_snd _ _ _)

theorem toA_left {T : Scheme.{0}} (x : T ⟶ E.P) (k : T ⟶ Sp (Localization.Away σ.f))
    (w : x ≫ E.p = k ≫ awayMap σ.f) : (toA E x k w).left ≫ E.ιA = x :=
  E.cartA.lift_fst _ _ _

theorem gen_mul {S₁ S₂ : Scheme.{0}} {s₁ : S₁ ⟶ Sp σ.R} (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂]
    (h₁ : H₁.left ⟶ E.P) (h₂ : H₂.left ⟶ E.P) (w₁ : h₁ ≫ E.p = H₁.hom ≫ s₁)
    (m₁ : MulAgree H₁ σ.A h₁ E.ιA) (m₂ : MulAgree H₂ σ.A h₂ E.ιA) {T : Scheme.{0}} (t : T ⟶ S₁) (t' : T ⟶ S₂)
    (k : T ⟶ Sp (Localization.Away σ.f)) (hk : t ≫ s₁ = k ≫ awayMap σ.f) (a b : Over.mk t ⟶ H₁)
    (a' b' : Over.mk t' ⟶ H₂) (ha : a.left ≫ h₁ = a'.left ≫ h₂) (hb : b.left ≫ h₁ = b'.left ≫ h₂) :
    (a * b).left ≫ h₁ = (a' * b').left ≫ h₂ := by
  have pa : (a.left ≫ h₁) ≫ E.p = k ≫ awayMap σ.f := by
    rw [Category.assoc, w₁, ← Category.assoc, Over.w a]; exact hk
  have pb : (b.left ≫ h₁) ≫ E.p = k ≫ awayMap σ.f := by
    rw [Category.assoc, w₁, ← Category.assoc, Over.w b]; exact hk
  exact (m₁ T t k a b (toA E _ k pa) (toA E _ k pb) (toA_left E _ _ _).symm (toA_left E _ _ _).symm).trans
    (m₂ T t' k a' b' (toA E _ k pa) (toA E _ k pb) ((toA_left E _ _ _).trans ha).symm
      ((toA_left E _ _ _).trans hb).symm).symm

theorem gen_one {S : Scheme.{0}} {s : S ⟶ Sp σ.R} (H : Over S) [GrpObj H] (h : H.left ⟶ E.P)
    (w : h ≫ E.p = H.hom ≫ s) (m : MulAgree H σ.A h E.ιA) {T : Scheme.{0}} (t : T ⟶ S)
    (k : T ⟶ Sp (Localization.Away σ.f)) (hk : t ≫ s = k ≫ awayMap σ.f) :
    (1 : Over.mk t ⟶ H).left ≫ h = (1 : Over.mk k ⟶ σ.A).left ≫ E.ιA := by
  have pe : ((1 : Over.mk t ⟶ H).left ≫ h) ≫ E.p = k ≫ awayMap σ.f := by
    rw [Category.assoc, w, ← Category.assoc, Over.w]; exact hk
  have hm := m T t k 1 1 (toA E _ k pe) (toA E _ k pe) (toA_left E _ _ _).symm (toA_left E _ _ _).symm
  rw [_root_.mul_one] at hm
  have hee : toA E _ k pe * toA E _ k pe = toA E _ k pe := by
    apply Over.OverMorphism.ext
    apply E.cartA.hom_ext
    · rw [← hm, toA_left]
    · exact (Over.w _).trans (Over.w _).symm
  have h1 : toA E _ k pe = 1 := mul_eq_left.1 hee
  rw [← h1, toA_left]

theorem mul_agree {S₁ S₂ : Scheme.{0}} (s₁ : S₁ ⟶ Sp σ.R) (s₂ : S₂ ⟶ Sp σ.R)
    (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂] (h₁ : H₁.left ⟶ E.P) (h₂ : H₂.left ⟶ E.P)
    [Flat s₁] [Flat H₁.hom] [Flat h₂] (w₁ : h₁ ≫ E.p = H₁.hom ≫ s₁) (w₂ : h₂ ≫ E.p = H₂.hom ≫ s₂)
    [IsOpenImmersion (pullback.lift h₂ H₂.hom w₂)]
    (m₁ : MulAgree H₁ σ.A h₁ E.ιA) (m₂ : MulAgree H₂ σ.A h₂ E.ιA) : MulAgree H₁ H₂ h₁ h₂ := by
  haveI := E.sep
  obtain ⟨X₁, fa, fb, hX, _⟩ : ∃ (X₁ : Scheme.{0}) (fa fb : X₁ ⟶ H₁.left),
      IsPullback fa fb H₁.hom H₁.hom ∧ Flat fa :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _, inferInstance⟩
  obtain ⟨Y, ya, ya', hY, _⟩ : ∃ (Y : Scheme.{0}) (ya : Y ⟶ X₁) (ya' : Y ⟶ H₂.left),
      IsPullback ya ya' (fa ≫ h₁) h₂ ∧ Flat ya :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _, inferInstance⟩
  have cX : fa ≫ H₁.hom = fb ≫ H₁.hom := hX.w
  have cY : ya ≫ fa ≫ h₁ = ya' ≫ h₂ := hY.w
  have wY : (ya ≫ fb ≫ h₁) ≫ E.p = (ya' ≫ H₂.hom) ≫ s₂ := by
    simp only [Category.assoc]
    rw [w₁, ← reassoc_of% cX, ← w₁, reassoc_of% cY, w₂]
  obtain ⟨Tu, π, ρ, hT, _⟩ : ∃ (Tu : Scheme.{0}) (π : Tu ⟶ Y) (ρ : Tu ⟶ H₂.left),
      IsPullback π ρ (pullback.lift (ya ≫ fb ≫ h₁) (ya' ≫ H₂.hom) wY) (pullback.lift h₂ H₂.hom w₂) ∧ Flat π :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _, inferInstance⟩
  have eT₁ : π ≫ ya ≫ fb ≫ h₁ = ρ ≫ h₂ := by
    have := hT.w =≫ pullback.fst E.p s₂
    simp only [Category.assoc] at this
    rw [pullback.lift_fst, pullback.lift_fst] at this
    exact this
  have eT₂ : π ≫ ya' ≫ H₂.hom = ρ ≫ H₂.hom := by
    have := hT.w =≫ pullback.snd E.p s₂
    simp only [Category.assoc] at this
    rw [pullback.lift_snd, pullback.lift_snd] at this
    simpa only [Category.assoc] using this
  let Au : Over.mk (π ≫ ya ≫ fa ≫ H₁.hom) ⟶ H₁ := Over.homMk (π ≫ ya ≫ fa) (by simp)
  let Bu : Over.mk (π ≫ ya ≫ fa ≫ H₁.hom) ⟶ H₁ := Over.homMk (π ≫ ya ≫ fb) (by simp [cX])
  let A'u : Over.mk (π ≫ ya' ≫ H₂.hom) ⟶ H₂ := Over.homMk (π ≫ ya') (by simp)
  let B'u : Over.mk (π ≫ ya' ≫ H₂.hom) ⟶ H₂ := Over.homMk ρ (by simp [eT₂])
  have key : (Au * Bu).left ≫ h₁ = (A'u * B'u).left ≫ h₂ := by
    haveI : Flat (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) := inferInstance
    refine ext_generic σ.hf (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) E.p _ _ ?_ ?_ ?_
    · rw [Category.assoc, w₁, ← Category.assoc, Over.w (Au * Bu)]; simp
    · rw [Category.assoc, w₂, ← Category.assoc, Over.w (A'u * B'u)]
      simp only [Over.mk_hom, Category.assoc]
      rw [← w₂, ← reassoc_of% cY, w₁]
    · have hk : (pullback.fst (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ π ≫ ya ≫ fa ≫ H₁.hom) ≫ s₁ =
          pullback.snd (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ awayMap σ.f := by
        simp only [Category.assoc]; exact pullback.condition
      let J₁ : Over.mk (pullback.fst (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ π ≫ ya ≫ fa ≫ H₁.hom) ⟶
          Over.mk (π ≫ ya ≫ fa ≫ H₁.hom) := Over.homMk (pullback.fst _ _) (by simp)
      let J₂ : Over.mk (pullback.fst (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ π ≫ ya' ≫ H₂.hom) ⟶
          Over.mk (π ≫ ya' ≫ H₂.hom) := Over.homMk (pullback.fst _ _) (by simp)
      have e1 : pullback.fst (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ (Au * Bu).left =
          ((J₁ ≫ Au) * (J₁ ≫ Bu)).left := by
        rw [← MonObj.comp_mul, Over.comp_left]; rfl
      have e2 : pullback.fst (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ (A'u * B'u).left =
          ((J₂ ≫ A'u) * (J₂ ≫ B'u)).left := by
        rw [← MonObj.comp_mul, Over.comp_left]; rfl
      have ha : (J₁ ≫ Au).left ≫ h₁ = (J₂ ≫ A'u).left ≫ h₂ := by
        simp [J₁, J₂, Au, A'u, cY]
      have hb : (J₁ ≫ Bu).left ≫ h₁ = (J₂ ≫ B'u).left ≫ h₂ := by
        simp [J₁, J₂, Bu, B'u, eT₁]
      calc _ = ((J₁ ≫ Au) * (J₁ ≫ Bu)).left ≫ h₁ := by rw [← e1, Category.assoc]
        _ = ((J₂ ≫ A'u) * (J₂ ≫ B'u)).left ≫ h₂ := gen_mul E H₁ H₂ h₁ h₂ w₁ m₁ m₂ _ _ _ hk _ _ _ _ ha hb
        _ = _ := by rw [← e2, Category.assoc]
  intro T t₁ t₂ a b a' b' ha hb
  obtain ⟨x, hx1, hx2⟩ : ∃ x, x ≫ fa = a.left ∧ x ≫ fb = b.left :=
    ⟨hX.lift a.left b.left ((Over.w a).trans (Over.w b).symm), hX.lift_fst _ _ _, hX.lift_snd _ _ _⟩
  have gY : x ≫ fa ≫ h₁ = a'.left ≫ h₂ := by rw [reassoc_of% hx1]; exact ha
  obtain ⟨y, hy1, hy2⟩ : ∃ y, y ≫ ya = x ∧ y ≫ ya' = a'.left :=
    ⟨hY.lift x a'.left gY, hY.lift_fst _ _ _, hY.lift_snd _ _ _⟩
  have gT : y ≫ pullback.lift (ya ≫ fb ≫ h₁) (ya' ≫ H₂.hom) wY = b'.left ≫ pullback.lift h₂ H₂.hom w₂ := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · rw [reassoc_of% hy1, reassoc_of% hx2]; exact hb
    · rw [reassoc_of% hy2]; exact (Over.w a').trans (Over.w b').symm
  obtain ⟨g, hg1, hg2⟩ : ∃ g, g ≫ π = y ∧ g ≫ ρ = b'.left :=
    ⟨hT.lift y b'.left gT, hT.lift_fst _ _ _, hT.lift_snd _ _ _⟩
  let G : Over.mk t₁ ⟶ Over.mk (π ≫ ya ≫ fa ≫ H₁.hom) := Over.homMk g (by
    simp only [Over.mk_hom]; rw [reassoc_of% hg1, reassoc_of% hy1, reassoc_of% hx1]; exact Over.w a)
  let G' : Over.mk t₂ ⟶ Over.mk (π ≫ ya' ≫ H₂.hom) := Over.homMk g (by
    simp only [Over.mk_hom]; rw [reassoc_of% hg1, reassoc_of% hy2]; exact Over.w a')
  have hA : G ≫ Au = a := Over.OverMorphism.ext (by
    simp only [G, Au, Over.comp_left, Over.homMk_left]; rw [reassoc_of% hg1, reassoc_of% hy1, hx1])
  have hB : G ≫ Bu = b := Over.OverMorphism.ext (by
    simp only [G, Bu, Over.comp_left, Over.homMk_left]; rw [reassoc_of% hg1, reassoc_of% hy1, hx2])
  have hA' : G' ≫ A'u = a' := Over.OverMorphism.ext (by
    simp only [G', A'u, Over.comp_left, Over.homMk_left]; rw [reassoc_of% hg1, hy2])
  have hB' : G' ≫ B'u = b' := Over.OverMorphism.ext (by
    simp only [G', B'u, Over.comp_left, Over.homMk_left]; exact hg2)
  calc (a * b).left ≫ h₁ = g ≫ (Au * Bu).left ≫ h₁ := by
        rw [← hA, ← hB, ← MonObj.comp_mul, Over.comp_left, Category.assoc]; rfl
    _ = g ≫ (A'u * B'u).left ≫ h₂ := by rw [key]
    _ = (a' * b').left ≫ h₂ := by
        rw [← hA', ← hB', ← MonObj.comp_mul, Over.comp_left, Category.assoc]; rfl

theorem one_agree {S₁ S₂ : Scheme.{0}} (s₁ : S₁ ⟶ Sp σ.R) (s₂ : S₂ ⟶ Sp σ.R)
    (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂] (h₁ : H₁.left ⟶ E.P) (h₂ : H₂.left ⟶ E.P)
    [Flat s₁] [Flat s₂] (w₁ : h₁ ≫ E.p = H₁.hom ≫ s₁) (w₂ : h₂ ≫ E.p = H₂.hom ≫ s₂)
    (m₁ : MulAgree H₁ σ.A h₁ E.ιA) (m₂ : MulAgree H₂ σ.A h₂ E.ιA) : OneAgree s₁ s₂ H₁ H₂ h₁ h₂ := by
  haveI := E.sep
  obtain ⟨Z, u₁, u₂, hP, _⟩ : ∃ (Z : Scheme.{0}) (u₁ : Z ⟶ S₁) (u₂ : Z ⟶ S₂), IsPullback u₁ u₂ s₁ s₂ ∧ Flat u₁ :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _, inferInstance⟩
  have key : (1 : Over.mk u₁ ⟶ H₁).left ≫ h₁ = (1 : Over.mk u₂ ⟶ H₂).left ≫ h₂ := by
    haveI : Flat (u₁ ≫ s₁) := inferInstance
    refine ext_generic σ.hf (u₁ ≫ s₁) E.p _ _ ?_ ?_ ?_
    · rw [Category.assoc, w₁, ← Category.assoc, Over.w]; rfl
    · rw [Category.assoc, w₂, ← Category.assoc, Over.w]; exact hP.w.symm
    · have hk : (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₁) ≫ s₁ =
          pullback.snd (u₁ ≫ s₁) (awayMap σ.f) ≫ awayMap σ.f := by
        rw [Category.assoc]; exact pullback.condition
      have hk' : (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₂) ≫ s₂ =
          pullback.snd (u₁ ≫ s₁) (awayMap σ.f) ≫ awayMap σ.f := by
        rw [Category.assoc, ← hP.w]; exact pullback.condition
      let J₁ : Over.mk (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₁) ⟶ Over.mk u₁ :=
        Over.homMk (pullback.fst _ _) rfl
      let J₂ : Over.mk (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₂) ⟶ Over.mk u₂ :=
        Over.homMk (pullback.fst _ _) rfl
      calc pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ (1 : Over.mk u₁ ⟶ H₁).left ≫ h₁
            = (J₁ ≫ (1 : Over.mk u₁ ⟶ H₁)).left ≫ h₁ := by rw [Over.comp_left, Category.assoc]; rfl
        _ = (1 : Over.mk (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₁) ⟶ H₁).left ≫ h₁ := by
            rw [MonObj.comp_one]
        _ = (1 : Over.mk (pullback.snd (u₁ ≫ s₁) (awayMap σ.f)) ⟶ σ.A).left ≫ E.ιA :=
            gen_one E H₁ h₁ w₁ m₁ _ _ hk
        _ = (1 : Over.mk (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₂) ⟶ H₂).left ≫ h₂ :=
            (gen_one E H₂ h₂ w₂ m₂ _ _ hk').symm
        _ = (J₂ ≫ (1 : Over.mk u₂ ⟶ H₂)).left ≫ h₂ := by rw [MonObj.comp_one]
        _ = pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ (1 : Over.mk u₂ ⟶ H₂).left ≫ h₂ := by
            rw [Over.comp_left, Category.assoc]; rfl
  intro T t₁ t₂ hw
  obtain ⟨g, hg1, hg2⟩ : ∃ g, g ≫ u₁ = t₁ ∧ g ≫ u₂ = t₂ :=
    ⟨hP.lift t₁ t₂ hw, hP.lift_fst _ _ _, hP.lift_snd _ _ _⟩
  let G : Over.mk t₁ ⟶ Over.mk u₁ := Over.homMk g hg1
  let G' : Over.mk t₂ ⟶ Over.mk u₂ := Over.homMk g hg2
  calc (1 : Over.mk t₁ ⟶ H₁).left ≫ h₁ = (G ≫ (1 : Over.mk u₁ ⟶ H₁)).left ≫ h₁ := by rw [MonObj.comp_one]
    _ = g ≫ (1 : Over.mk u₁ ⟶ H₁).left ≫ h₁ := by rw [Over.comp_left, Category.assoc]; rfl
    _ = g ≫ (1 : Over.mk u₂ ⟶ H₂).left ≫ h₂ := by rw [key]
    _ = (G' ≫ (1 : Over.mk u₂ ⟶ H₂)).left ≫ h₂ := by rw [Over.comp_left, Category.assoc]; rfl
    _ = (1 : Over.mk t₂ ⟶ H₂).left ≫ h₂ := by rw [MonObj.comp_one]

end GlobalTheory.Desc.UAgree

open GlobalTheory.Desc.UAgree in

theorem GlobalTheory.Desc.mulAgree_oneAgree_of_openIn : ∀ (σ : Setup) (E : Emb σ) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp σ.R) (s₂ : S₂ ⟶ Sp σ.R) (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂] (h₁ : H₁.left ⟶ E.P) (h₂ : H₂.left ⟶ E.P), Flat s₁ → Flat s₂ → Flat H₁.hom → Flat H₂.hom → OpenIn h₁ H₁.hom E.p s₁ → OpenIn h₂ H₂.hom E.p s₂ → MulAgree H₁ σ.A h₁ E.ιA → MulAgree H₂ σ.A h₂ E.ιA → MulAgree H₁ H₂ h₁ h₂ ∧ OneAgree s₁ s₂ H₁ H₂ h₁ h₂ := by
  intro σ E S₁ S₂ s₁ s₂ H₁ _ H₂ _ h₁ h₂ fs₁ fs₂ fH₁ fH₂ o₁ o₂ m₁ m₂
  haveI := fs₁; haveI := fs₂; haveI := fH₁; haveI := fH₂
  haveI : Flat h₂ := flat_of_openIn o₂
  obtain ⟨w₁, -⟩ := o₁
  obtain ⟨w₂, hw₂⟩ := o₂
  haveI := hw₂
  exact ⟨mul_agree E s₁ s₂ H₁ H₂ h₁ h₂ w₁ w₂ m₁ m₂, one_agree E s₁ s₂ H₁ H₂ h₁ h₂ w₁ w₂ m₁ m₂⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charP : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [CharP k p] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  first | (exact @GlobalTheory.UPel.HT.Datum.charP_tensor_matrix) | (exact GlobalTheory.UPel.HT.Datum.charP_tensor_matrix) | (intros; apply GlobalTheory.UPel.HT.Datum.charP_tensor_matrix  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  first | (exact @GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix) | (exact GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix) | (intros; apply GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimEqLocalDomainStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_finite_of_ringKrullDim_eq_localDomain : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] (ψ : B →+* R), ψ.Finite → ringKrullDim R = ringKrullDim B → Function.Injective ψ := by
  first | exact @GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain | exact GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain | (intros; apply GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain <;> assumption)
end

