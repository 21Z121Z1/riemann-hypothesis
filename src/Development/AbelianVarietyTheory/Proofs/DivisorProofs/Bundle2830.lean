import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfBaseChangesArtinFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PinchHom

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {β : G'.left ⟶ G.left}

theorem sq_fst (hp : IsPullback β G'.hom G.hom f) :
    (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left ≫ (fst G G).left = (fst G' G').left ≫ β := by
  rw [← Over.comp_left, lift_fst]; rfl

theorem sq_snd (hp : IsPullback β G'.hom G.hom f) :
    (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left ≫ (snd G G).left = (snd G' G').left ≫ β := by
  rw [← Over.comp_left, lift_snd]; rfl

theorem sq_hom_ext (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G ⊗ G).left}
    (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left) (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  GlobalTheory.Mum.PowCart.square_over_hom_ext G fun i => by fin_cases i; exacts [h₁, h₂]

theorem sq_mul [GrpObj G] [GrpObj G'] (hp : IsGrpPullback G' G f β) :
    (lift (pushPt hp.1.w (fst G' G')) (pushPt hp.1.w (snd G' G'))).left ≫ (MonObj.mul : G ⊗ G ⟶ G).left =
      (MonObj.mul : G' ⊗ G' ⟶ G').left ≫ β := by
  have h := hp.2 (G' ⊗ G') (fst G' G') (snd G' G') (pushPt hp.1.w (fst G' G')) (pushPt hp.1.w (snd G' G')) rfl rfl
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at h
  exact h

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A' A : Over (Spec P)) [GrpObj A'] [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (A₀ : Over (Spec R₀)) [GrpObj A₁] [GrpObj A₂] [GrpObj A₀] (j₁ : A₁.left ⟶ A'.left) (j₂ : A₂.left ⟶ A'.left) (k₁ : A₁.left ⟶ A.left) (k₂ : A₂.left ⟶ A.left) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (φ : A'.left ⟶ A.left), Flat A'.hom → IsGrpPullback A₁ A' (Spec.map f₁) j₁ → IsGrpPullback A₂ A' (Spec.map f₂) j₂ → IsGrpPullback A₁ A (Spec.map f₁) k₁ → IsGrpPullback A₂ A (Spec.map f₂) k₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) i₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) i₂ → i₁ ≫ j₁ = i₂ ≫ j₂ → IsPullback φ A'.hom A.hom (𝟙 _) → j₁ ≫ φ = k₁ → j₂ ≫ φ = k₂ → IsGrpPullback A' A (𝟙 _) φ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ A' A _ _ A₁ A₂ A₀ _ _ _ j₁ j₂ k₁ k₂ i₁ i₂ φ hfl hj₁ hj₂ hk₁ hk₂
    hi₁ hi₂ hij hφ hjk₁ hjk₂
  have hY : Flat (A' ⊗ A').hom := by
    haveI := hfl
    exact GlobalTheory.ExtUnique.flat_tensorObj A' A'
  have hw : φ ≫ A.hom = A'.hom := by simpa using hφ.w
  let Φ : A' ⟶ A := Over.homMk φ hw
  let L : A' ⊗ A' ⟶ A ⊗ A := lift (fst A' A' ≫ Φ) (snd A' A' ≫ Φ)

  have hcomp : (lift (pushPt hi₁.1.w (fst A₀ A₀)) (pushPt hi₁.1.w (snd A₀ A₀))).left ≫
      (lift (pushPt hj₁.1.w (fst A₁ A₁)) (pushPt hj₁.1.w (snd A₁ A₁))).left =
      (lift (pushPt hi₂.1.w (fst A₀ A₀)) (pushPt hi₂.1.w (snd A₀ A₀))).left ≫
      (lift (pushPt hj₂.1.w (fst A₂ A₂)) (pushPt hj₂.1.w (snd A₂ A₂))).left := by
    apply sq_hom_ext A'
    · rw [Category.assoc, sq_fst hj₁.1, reassoc_of% (sq_fst hi₁.1), Category.assoc, sq_fst hj₂.1,
        reassoc_of% (sq_fst hi₂.1), hij]
    · rw [Category.assoc, sq_snd hj₁.1, reassoc_of% (sq_snd hi₁.1), Category.assoc, sq_snd hj₂.1,
        reassoc_of% (sq_snd hi₂.1), hij]
  have po := GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ (A' ⊗ A') (A₁ ⊗ A₁) (A₂ ⊗ A₂) (A₀ ⊗ A₀) _ _ _ _
    hY (GlobalTheory.Mum.PowCart.isPullback_two hj₁.1) (GlobalTheory.Mum.PowCart.isPullback_two hj₂.1)
    (GlobalTheory.Mum.PowCart.isPullback_two hi₁.1) hcomp (GlobalTheory.Mum.PowCart.isPullback_two hi₂.1).w

  have hL : ∀ {R : CommRingCat.{0}} {g : P ⟶ R} {B : Over (Spec R)} [GrpObj B] {j k : B.left ⟶ _}
      (hj : IsGrpPullback B A' (Spec.map g) j) (hk : IsGrpPullback B A (Spec.map g) k), j ≫ φ = k →
      (lift (pushPt hj.1.w (fst B B)) (pushPt hj.1.w (snd B B))).left ≫ (MonObj.mul : A' ⊗ A' ⟶ A').left ≫ φ =
      (lift (pushPt hj.1.w (fst B B)) (pushPt hj.1.w (snd B B))).left ≫ L.left ≫ (MonObj.mul : A ⊗ A ⟶ A).left := by
    intro R g B _ j k hj hk hjk
    have e : (lift (pushPt hj.1.w (fst B B)) (pushPt hj.1.w (snd B B))).left ≫ L.left =
        (lift (pushPt hk.1.w (fst B B)) (pushPt hk.1.w (snd B B))).left := by
      apply sq_hom_ext A
      · rw [Category.assoc, ← Over.comp_left _ _ _ L, lift_fst, sq_fst hk.1, Over.comp_left, ← Category.assoc,
          sq_fst hj.1, Category.assoc, ← hjk]
        rfl
      · rw [Category.assoc, ← Over.comp_left _ _ _ L, lift_snd, sq_snd hk.1, Over.comp_left, ← Category.assoc,
          sq_snd hj.1, Category.assoc, ← hjk]
        rfl
    rw [← Category.assoc, sq_mul hj, ← Category.assoc, e, sq_mul hk, Category.assoc, hjk]
  have hE : (MonObj.mul : A' ⊗ A' ⟶ A').left ≫ φ = L.left ≫ (MonObj.mul : A ⊗ A ⟶ A).left :=
    po.hom_ext (hL hj₁ hk₁ hjk₁) (hL hj₂ hk₂ hjk₂)
  have hE' : (MonObj.mul : A' ⊗ A' ⟶ A') ≫ Φ = L ≫ MonObj.mul := Over.OverMorphism.ext hE
  have hxy : ∀ (T : Over (Spec P)) (x y : T ⟶ A'), (x * y) ≫ Φ = (x ≫ Φ) * (y ≫ Φ) := by
    intro T x y
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, hE', ← Category.assoc]
    congr 1
    simp [L]
  refine ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩
  let k : Over.mk (T.hom ≫ 𝟙 (Spec P)) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = k ≫ x ≫ Φ := Over.OverMorphism.ext (by simp [k, Φ, hx])
  have ey : y₀ = k ≫ y ≫ Φ := Over.OverMorphism.ext (by simp [k, Φ, hy])
  rw [ex, ey, ← MonObj.comp_mul, ← hxy]
  simp [k, Φ]

end GlobalTheory.PinchHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionToGradedModelFlatBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.OpenImmersionDescent

theorem openImm_of_isIso_appTop {X Y : Scheme.{0}} [IsAffine Y] [X.IsQuasiAffine] (g : X ⟶ Y) [IsIso g.appTop] :
    IsOpenImmersion g := by
  have e : g = X.toSpecΓ ≫ Spec.map g.appTop ≫ Y.isoSpec.inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  rw [e]; infer_instance

theorem bij_congr {X Y : Scheme.{0}} (f : X ⟶ Y) (V W : Y.Opens) (h : V = W) (hb : Function.Bijective (f.app W)) :
    Function.Bijective (f.app V) := by subst h; exact hb

end GlobalTheory.Desc.OpenImmersionDescent

open GlobalTheory.Desc.OpenImmersionDescent in

theorem GlobalTheory.Desc.openIn_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ → PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → OpenIn m q p (spMap ρ) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hP R₁ _ _ ρ hρ hc₀ Y _ _ _ q θ D₁ hθ hLD hamp hSec m hm hPFF hloc
  refine ⟨hm, ?_⟩
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsOpenImmersion) fun z => ?_
  obtain ⟨k, hk, b, hb, hz⟩ := hP.cover (pullback.fst p (spMap ρ) z)
  refine ⟨(pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b, hz, ?_⟩
  haveI : IsAffineHom (pullback.fst p (spMap ρ)) := by first | infer_instance | exact MorphismProperty.pullback_fst (P := @IsAffineHom) p (spMap ρ) inferInstance | exact (isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback p (spMap ρ)).flip inferInstance)
  have hA : IsAffineOpen ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) := (hP.affine k hk b hb).preimage _
  haveI : IsAffine ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b).toScheme := hA
  have hpre : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) : Set Y) = locus D₁ k (θ b) := by
    ext y
    change pullback.fst p (spMap ρ) (pullback.lift m q hm y) ∈ Dp k b ↔ _
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hloc k hk b hb y
  haveI : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).toScheme.IsQuasiAffine :=
    GlobalTheory.T.isQuasiAffine_cartierSectionGeneratingLocus_ample Y D₁ hamp k hk (θ b) (by rw [hSec]; exact subset_spanBy _ _ ⟨b, hb, rfl⟩) _ hpre
  haveI : IsIso (pullback.lift m q hm ∣_ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).appTop := by
    rw [morphismRestrict_appTop]
    have h1 := bij_congr (pullback.lift m q hm) _ _ (Scheme.Opens.ι_image_top _)
      ⟨GlobalTheory.T.proj_model_baseChange_standard_open_app_injective R F c₀ N hN P p ψ Dp hP R₁ ρ hρ hc₀ Y q θ D₁ hθ hLD hamp hSec m hPFF hloc hm k hk b hb,
       GlobalTheory.T.proj_model_baseChange_standard_open_app_surjective R F c₀ N hN P p ψ Dp hP R₁ ρ hρ hc₀ Y q θ D₁ hθ hLD hamp hSec m hPFF hloc hm k hk b hb⟩
    have h2 : IsIso (Scheme.Hom.app (pullback.lift m q hm) ((pullback.fst p (spMap ρ) ⁻¹ᵁ Dp k b).ι ''ᵁ ⊤)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 h1
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 (Functor.map_isIso _ _)
  exact openImm_of_isIso_appTop _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic

namespace GlobalTheory.Mum.PowData

def AdjCls {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] [GrpObj G₀] (c : Pic G.left) (c₀ : Pic G₀.left) (q : G ⟶ G₀)
    (j : G₀ ⟶ G) : Prop :=
  ∀ (T : Over S) (x : T ⟶ G) (z : T ⟶ G₀), lam c x (z ≫ j) = lam c₀ (x ≫ q) z

variable {R : Type} [CommRing R] [IsDomain R]

def PrimVal (D : DegPre R) (f : D.P.A ⟶ D.P.A) (m : D.X → D.X) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(padd D.P.A (𝟙 _) f).left, 𝟙 D.P.A.left, f.left, (toUnit D.P.A ≫ η[D.P.A]).left] ![1, -2, -1, 2]),
    u.IsGen ∧ ∀ y, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau y (m y)) (LB.pullGen D.P.L _ _ u (D.xK y))) (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK)

theorem isPrimitiveValue_of_ringElement_psiRelation {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X] {o : D.OAct O} {w : O}
    (h : TraceFormTwistIso D o w) : PrimVal D (o.onB.act w) (fun y => w • y) :=
  h.imp fun _ h => ⟨h.1, h.2.2⟩

def Expand (D : DegPre R) {K : Type} [Fintype K] (n : K → ℤ) {T : Over (Sp R)} (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A)) : Prop :=
  ∃ κ : LB.Gen (LB.LinComb D.P.L (Sum.elim (lamPts x (∏ i, y i ^ n i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
      (Sum.elim Oε (fun k : K × Fin 4 => -(n k.1 * Oε k.2)))),
    κ.IsGen ∧ ∀ (p : TK R ⟶ T) (a : D.X) (b : K → D.X), p ≫ x = toUnit _ ≫ D.c a → (∀ i, p ≫ y i = toUnit _ ≫ D.c (b i)) →
      ∀ z J, Good D.P.L z J →
        val (D.tau a (∑ i, n i • b i)) (𝟙 _) z J * val κ p.left z J = ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ n i

def CmpTwo (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A) : Prop :=
  ∃ Γ : LB.Gen (LB.LinComb (JN D D₀)
      (Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j) k ≫ coprod.inl)
        (fun k => lamPts (fst D.P.A D₀.P.A ≫ q) (snd D.P.A D₀.P.A) k ≫ coprod.inr)) (Sum.elim Oε Oinvε)),
    Γ.IsGen ∧ ∀ (χ' : D.X) (χ : D₀.X), D.c χ' = D₀.c χ ≫ j → ∀ u : LB.Gen (CmpLB D D₀ q χ' χ), Nrm u →
      ∀ (T : Over (Sp R)) (x : T ⟶ D.P.A) (z : T.left) (J), Good (JN D D₀) z J →
        val u x.left z J = val Γ (lift x (toUnit T ≫ D₀.c χ)).left z J

def PeriodRel (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (h : D₀.X → D.X) (k : D.X → D₀.X) : Prop :=
  ∀ χ, ∃ u : LB.Gen (CmpLB D D₀ q (h χ) χ), Nrm u ∧ ∀ y z J, Good (JN D D₀) z J →
    val (D₀.tau (k y) χ) (𝟙 _) z (rr J) = val (D.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D.c y)) z J

section Points

variable {S : Scheme.{0}} {T T' G G' : Over S} [GrpObj G] [IsCommMonObj G] {K : Type} [Fintype K]

theorem comp_prod_zpow (p : T' ⟶ T) (y : K → (T ⟶ G)) (n : K → ℤ) : p ≫ ∏ i, y i ^ n i = ∏ i, (p ≫ y i) ^ n i := by
  let f : (T ⟶ G) →* (T' ⟶ G) := MonoidHom.mk' (fun a => p ≫ a) fun a b => MonObj.comp_mul p a b
  exact (map_prod f _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow f _ _)

theorem prod_zpow_comp [GrpObj G'] [IsCommMonObj G'] (y : K → (T ⟶ G)) (n : K → ℤ) (g : G ⟶ G') [IsMonHom g] :
    (∏ i, y i ^ n i) ≫ g = ∏ i, (y i ≫ g) ^ n i := by
  let f : (T ⟶ G) →* (T ⟶ G') := MonoidHom.mk' (fun a => a ≫ g) fun a b => MonObj.mul_comp a b g
  exact (map_prod f _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow f _ _)

end Points

end GlobalTheory.Mum.PowData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrincipalOfSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section
namespace GlobalTheory.PrincSubring

theorem isPrincipal_of_subring : ∀ (h : ℕ) (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsSymmetricPair h A₁ P₁ → Out.RelAmple A₁ (diagPull A₁ P₁) → IsGrpPullback A A₁ (spMap R₁.subtype) φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → IsPrincipal A P → IsPrincipal A₁ P₁ := by
  intro h R _ R₁ _ A _ P A₁ _ P₁ φ φ₂ hS hamp hpb hsq hiso hpr
  haveI : IsAbelianScheme A₁ := hS.1
  haveI : IsCommMonObj A₁ := IsAbelianScheme.comm
  obtain ⟨hG, hL, hLa, hrig, hsym⟩ := GlobalTheory.T.eighth_power_symmetric_ample h A₁ P₁ hS hamp
  have hf : KerAlong A₁ P₁ (spMap R₁.subtype) := GlobalTheory.T.kernel_condition_along_baseChange_of_pullback _ A P A₁ P₁ φ φ₂ hS.2.2.1 hpb hsq hiso hpr.2
  have hfT := (GlobalTheory.T.kernel_condition_iff_e8Bundle_kGroup_trivial h A₁ P₁ hS hamp _).1 hf
  have hK : Out.KTriv (Out.powObj A₁ 8) (powLB A₁ P₁) := by
    refine GlobalTheory.KTrivSpread.kTriv_of_primes GlobalTheory.abelianSchemeLaws_all.1.globalFns R₁ _ hG _ hL hLa fun p => ?_
    rcases GlobalTheory.T.noetherian_subring_prime_contraction_or_dvr R R₁ p with hp | ⟨Q, k, _, i, j, V, _, _, _, ρ, e, h1, h2, hp⟩
    · exact ⟨R, inferInstance, R₁.subtype, hp, hfT⟩
    · refine ⟨V, inferInstance, ρ, hp, ?_⟩
      refine GlobalTheory.T.kGroup_trivial_spreads_from_dvr_generic_point _ _ hG hL hLa hrig hsym V (spMap ρ) ?_
      have t1 := hfT.comp (spMap (algebraMap R Q.asIdeal.ResidueField))
      have e1 : spMap (algebraMap R Q.asIdeal.ResidueField) ≫ spMap R₁.subtype = spMap j ≫ spMap i := by
        rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, h1]
      rw [e1] at t1
      have t2 := (GlobalTheory.T.kGroup_trivial_descends_flat_surjective _ _ (spMap i) (spMap j) hL t1).comp (spMap e)
      have e2 : spMap e ≫ spMap i = spMap (algebraMap V (FractionRing V)) ≫ spMap ρ := by
        rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, h2]
      rwa [e2] at t2
  have hT : GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A₁ 8) (powLB A₁ P₁) (𝟙 _) :=
    fun T a ha x hx => GlobalTheory.UU.kTriv_iff_forall.1 hK T x hx
  exact ⟨hamp, fun T x hx => (GlobalTheory.T.kernel_condition_iff_e8Bundle_kGroup_trivial h A₁ P₁ hS hamp (𝟙 _)).2 hT T T.hom (Category.comp_id _) x hx⟩

end GlobalTheory.PrincSubring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProdUnif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D : DegData R I}
  {A₁ A₂ A : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

structure IsProdUnif (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (U : UnifPre I D A (G₁ ⊗ G₂))
    (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X)
    (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A) : Prop where
  gen_pr₁ : U.gen.hom ≫ a₁ = (Over.pullback (jK R)).map (fst G₁ G₂) ≫ U₁.gen.hom
  gen_pr₂ : U.gen.hom ≫ a₂ = (Over.pullback (jK R)).map (snd G₁ G₂) ≫ U₂.gen.hom
  wL : ∃ w : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left), w.IsGen
  q_pr₁ : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map p₁ =
    (Over.pullback (thick R I e)).map (fst G₁ G₂) ≫ (U₁.gt e).q
  q_pr₂ : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map p₂ =
    (Over.pullback (thick R I e)).map (snd G₁ G₂) ≫ (U₂.gt e).q
  i_pr₁ : ∀ (e : ℕ) (h : D₁.toPre.X → D.toPre.X), (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) →
    ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X,
      TorusHomOf h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂) = t ≫ (U₁.gt e).i
  i_pr₂ : ∀ (e : ℕ) (h : D₂.toPre.X → D.toPre.X), (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) →
    ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
      TorusHomOf h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂) = t ≫ (U₂.gt e).i

variable {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U : UnifPre I D A (G₁ ⊗ G₂)}
  {p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A} {p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A} {q₁ : D.toPre.X →+ D₁.toPre.X}
  {q₂ : D.toPre.X →+ D₂.toPre.X} {a₁ : A.A ⟶ A₁.A} {a₂ : A.A ⟶ A₂.A}

theorem IsProdUnif.linHom_fst (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂) (j₁ : D₁.toPre.X →+ D.toPre.X)
    (h₁ : ∀ y, q₁ (j₁ y) = y) (h₂ : ∀ y, q₂ (j₁ y) = 0) : LinHom U U₁ p₁ j₁ (fst G₁ G₂) :=
  ⟨inferInstance, fun e => (hU.q_pr₁ e).symm, fun e => hU.i_pr₁ e j₁ h₁ h₂⟩

theorem IsProdUnif.linHom_snd (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂) (j₂ : D₂.toPre.X →+ D.toPre.X)
    (h₁ : ∀ y, q₁ (j₂ y) = 0) (h₂ : ∀ y, q₂ (j₂ y) = y) : LinHom U U₂ p₂ j₂ (snd G₁ G₂) :=
  ⟨inferInstance, fun e => (hU.q_pr₂ e).symm, fun e => hU.i_pr₂ e j₂ h₁ h₂⟩

end GlobalTheory.MumProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ProjOverBase

theorem isProjOver_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (κ : C.o →+* X.o₁), X.uΩ ≫ C.i ≫ C.z = spMap ((algebraMap X.o₁ X.Ω₁).comp κ) → IsProjOver X.M.s := by
  intro E _ _ _ H Dw l Xo cf C X κ h
  have hs : X.M.s ≫ spMap κ = X.π ≫ C.z := by
    refine ext_of_isDominant X.M.pt ?_
    rw [← Category.assoc, X.M.pt_s, ← Category.assoc, X.comp]
    simp only [USetup.uΩ, UCompact.i, Category.assoc] at h ⊢
    rw [h]
    exact (Spec.map_comp (CommRingCat.ofHom κ) (CommRingCat.ofHom (algebraMap X.o₁ X.Ω₁))).symm
  haveI := C.ded
  exact GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over C.o X.o₁ κ X.M.Z C.Z C.z X.π X.M.s C.proj X.fin inferInstance hs

end GlobalTheory.UPoinc.ProjOverBase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegSquareFourthSide
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullSquare

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_of_eq {θ θ' : R →+* R'} (e : θ = θ') {D : DegPre R} {D' : DegPre R'} (r : IsPullDeg θ D D') :
    ∃ r' : IsPullDeg θ' D D', (∀ x, r'.xe x = r.xe x) ∧
      ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (g : GtPtF D F)
        (g' : GtPtF D' F), IsPullGtF θ r F g g' → IsPullGtF θ' r' F g g' := by
  subst e
  exact ⟨r, fun _ => rfl, fun _ _ _ _ _ _ h => h⟩

end GlobalTheory.PullSquare

theorem GlobalTheory.Mum.isPullDeg_square : ∀ (R R₁ W W₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [CommRing W₁] [IsDomain W₁] (I : Ideal R) (I₁ : Ideal R₁) (J : Ideal W) (J₁ : Ideal W₁), AdmBase R I → AdmBase R₁ I₁ → AdmBase W J → AdmBase W₁ J₁ → ∀ (ρ : R →+* R₁) (φ : R →+* W) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁), φ₁.comp ρ = iw.comp φ → Function.Injective φ₁ → Function.Injective ρ → Function.Injective φ → Function.Injective iw → ∀ (D : DegData R I) (D₁ : DegData R₁ I₁) (D' : DegData W J) (D'₁ : DegData W₁ J₁) (hρ : IsPullDeg ρ D.toPre D₁.toPre) (hD : IsPullDeg φ D.toPre D'.toPre) (hX : IsPullDeg iw D'.toPre D'₁.toPre), ∃ h : IsPullDeg φ₁ D₁.toPre D'₁.toPre, (∀ x, hρ.xe (h.xe x) = hD.xe (hX.xe x)) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R₁) F] [Algebra (FractionRing W) F] [Algebra (FractionRing W₁) F], GlobalTheory.ArcPull.Compat ρ F → GlobalTheory.ArcPull.Compat φ F → GlobalTheory.ArcPull.Compat iw F → GlobalTheory.ArcPull.Compat φ₁ F → ∀ (g : GtPtF D.toPre F) (g₁ : GtPtF D₁.toPre F) (g' : GtPtF D'.toPre F) (g'₁ : GtPtF D'₁.toPre F), IsPullGtF ρ hρ F g g₁ → IsPullGtF φ hD F g g' → IsPullGtF iw hX F g' g'₁ → IsPullGtF φ₁ h F g₁ g'₁ := by
  intro R R₁ W W₁ _ _ _ _ _ _ _ _ I I₁ J J₁ _ _ _ _ ρ φ iw φ₁ hsq hφ₁ hρi hφi hiw D D₁ D' D'₁ hρ hD hX
  obtain ⟨r, Tr⟩ := GlobalTheory.LabTrans.exists_comp hφi hiw hD hX
  obtain ⟨r', hx', hg'⟩ := GlobalTheory.PullSquare.exists_of_eq hsq.symm r
  obtain ⟨h, Th⟩ := GlobalTheory.LabTrans.exists_cancel hρi hφ₁ hρ r'
  refine ⟨h, fun x => ?_, ?_⟩
  · rw [Th.xe_eq, hx', ← Tr.xe_eq]
  · intro F _ _ _ _ _ cρ cφ ci c₁ g g₁ g' g'₁ Hρ HD HX
    have cθ : GlobalTheory.ArcPull.Compat (iw.comp φ) F := fun a => (cφ a).trans (ci (φ a))
    have cθ' : GlobalTheory.ArcPull.Compat (φ₁.comp ρ) F := fun a => (cρ a).trans (c₁ (ρ a))
    have H : IsPullGtF (φ₁.comp ρ) r' F g g'₁ := hg' F g g'₁ (Tr.isPullGtF cθ HD HX)
    obtain ⟨g'', H''⟩ := GlobalTheory.ArcPull.exists_pullGt h GlobalTheory.ExpansionTotal.globalFns c₁ g₁
    have H2 := Th.isPullGtF cθ' Hρ H''
    rwa [GlobalTheory.ArcPull.pullGt_unique r' cθ' H2 H] at H''
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackDescentSquarePairToOpenSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

abbrev prU (N : Near π G) : (Desc.UT N).left ⟶ N.U.left := pullback.fst _ _

def liftU (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : Y ⟶ (Desc.UT N).left :=
  pullback.lift x t h

theorem liftU_prU (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : liftU N x t h ≫ prU N = x :=
  pullback.lift_fst _ _ _

theorem liftU_hom (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : liftU N x t h ≫ (Desc.UT N).hom = t :=
  pullback.lift_snd _ _ _

theorem UT_ext (N : Near π G) {Y : Scheme.{0}} (f g : Y ⟶ (Desc.UT N).left) (h1 : f ≫ prU N = g ≫ prU N)
    (h2 : f ≫ (Desc.UT N).hom = g ≫ (Desc.UT N).hom) : f = g :=
  pullback.hom_ext h1 h2

theorem pairU_fst (N : Near π G) :
    pairU N ≫ (fst N.U N.U).left = (fst (Desc.UT N) (Desc.UT N)).left ≫ prU N :=
  congrArg Over.Hom.left (lift_fst (fstU N) (sndU N))

theorem pairU_snd (N : Near π G) :
    pairU N ≫ (snd N.U N.U).left = (snd (Desc.UT N) (Desc.UT N)).left ≫ prU N :=
  congrArg Over.Hom.left (lift_snd (fstU N) (sndU N))

theorem pairU_isPullback (N : Near π G) :
    IsPullback (pairU N) (Desc.UT N ⊗ Desc.UT N).hom (N.U ⊗ N.U).hom (pullback.fst π π ≫ π) := by
  have hUU : (N.U ⊗ N.U).hom = (fst N.U N.U).left ≫ N.U.hom := rfl
  have cUU : (fst N.U N.U).left ≫ N.U.hom = (snd N.U N.U).left ≫ N.U.hom := pullback.condition
  have hTT : (Desc.UT N ⊗ Desc.UT N).hom = (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom := rfl
  have cTT : (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom := pullback.condition
  have extUU : ∀ {Y : Scheme.{0}} (f g : Y ⟶ (N.U ⊗ N.U).left), f ≫ (fst N.U N.U).left = g ≫ (fst N.U N.U).left →
      f ≫ (snd N.U N.U).left = g ≫ (snd N.U N.U).left → f = g := fun f g h1 h2 => pullback.hom_ext h1 h2
  have extTT : ∀ {Y : Scheme.{0}} (f g : Y ⟶ (Desc.UT N ⊗ Desc.UT N).left),
      f ≫ (fst (Desc.UT N) (Desc.UT N)).left = g ≫ (fst (Desc.UT N) (Desc.UT N)).left →
      f ≫ (snd (Desc.UT N) (Desc.UT N)).left = g ≫ (snd (Desc.UT N) (Desc.UT N)).left → f = g :=
    fun f g h1 h2 => pullback.hom_ext h1 h2
  have liftTT : ∀ {Y : Scheme.{0}} (a b : Y ⟶ (Desc.UT N).left), a ≫ (Desc.UT N).hom = b ≫ (Desc.UT N).hom →
      ∃ f : Y ⟶ (Desc.UT N ⊗ Desc.UT N).left,
        f ≫ (fst (Desc.UT N) (Desc.UT N)).left = a ∧ f ≫ (snd (Desc.UT N) (Desc.UT N)).left = b :=
    fun a b h => ⟨pullback.lift a b h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have ha : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      (s.fst ≫ (fst N.U N.U).left) ≫ N.U.hom = s.snd ≫ pullback.fst π π ≫ π := fun s => by
    rw [Category.assoc, ← hUU]; exact s.condition
  have hb : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      (s.fst ≫ (snd N.U N.U).left) ≫ N.U.hom = s.snd ≫ pullback.fst π π ≫ π := fun s => by
    rw [Category.assoc, ← cUU, ← hUU]; exact s.condition
  have hab : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      liftU N _ _ (ha s) ≫ (Desc.UT N).hom = liftU N _ _ (hb s) ≫ (Desc.UT N).hom := fun s => by
    rw [liftU_hom, liftU_hom]
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ (pairU_over N)) ?_
  refine PullbackCone.IsLimit.mk (pairU_over N) (fun s => (liftTT _ _ (hab s)).choose) ?_ ?_ ?_
  · intro s
    obtain ⟨h1, h2⟩ := (liftTT _ _ (hab s)).choose_spec
    apply extUU
    · rw [Category.assoc, pairU_fst, ← Category.assoc, h1, liftU_prU]
    · rw [Category.assoc, pairU_snd, ← Category.assoc, h2, liftU_prU]
  · intro s
    obtain ⟨h1, _⟩ := (liftTT _ _ (hab s)).choose_spec
    show _ ≫ (Desc.UT N ⊗ Desc.UT N).hom = _
    rw [hTT, ← Category.assoc, h1, liftU_hom]
  · intro s m m1 m2
    obtain ⟨h1, h2⟩ := (liftTT _ _ (hab s)).choose_spec
    have m2' : m ≫ (Desc.UT N ⊗ Desc.UT N).hom = s.snd := m2
    rw [hTT] at m2'
    apply extTT
    · rw [h1]
      apply UT_ext
      · rw [liftU_prU, Category.assoc, ← pairU_fst, ← Category.assoc, m1]
      · rw [liftU_hom, Category.assoc, m2']
    · rw [h2]
      apply UT_ext
      · rw [liftU_prU, Category.assoc, ← pairU_snd, ← Category.assoc, m1]
      · rw [liftU_hom, Category.assoc, ← cTT, m2']

end GlobalTheory.Mum.DescKP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfIsPullbackOnOpenCoverTargetStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_of_isPullback_on_openCover_target : ∀ (X G S B : Scheme.{0}) (β : X ⟶ G) (f : X ⟶ S) (g : G ⟶ B) (π : S ⟶ B), β ≫ g = f ≫ π → ∀ (J : Type) (Y P : J → Scheme.{0}) (ψ : ∀ j, Y j ⟶ G) (e : ∀ j, P j ⟶ X) (p : ∀ j, P j ⟶ Y j) (q : ∀ j, P j ⟶ S), (∀ j, IsOpenImmersion (ψ j)) → (∀ y : G, ∃ j, y ∈ Set.range (ψ j)) → (∀ j, IsOpenImmersion (e j)) → (∀ j, IsPullback (p j) (q j) (ψ j ≫ g) π) → (∀ j, e j ≫ β = p j ≫ ψ j) → (∀ j, e j ≫ f = q j) → (∀ (j : J) (x : X), β x ∈ Set.range (ψ j) → x ∈ Set.range (e j)) → IsPullback β f g π := by
  first | exact @GlobalTheory.Mum.isPullback_of_openCover_target | exact GlobalTheory.Mum.isPullback_of_openCover_target | (intros; apply GlobalTheory.Mum.isPullback_of_openCover_target <;> assumption)
end

