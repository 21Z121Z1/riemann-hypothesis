import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFramesDoublingPolynomialExists
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRiemannRochAsymptotic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfLevelSubmodulePermutation
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramBoundStatementStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_bound_statement : Hypotheses2 → Gram := by
  first | exact @GlobalTheory.CovTop.gram_of_hypotheses | exact GlobalTheory.CovTop.gram_of_hypotheses | (intros; apply GlobalTheory.CovTop.gram_of_hypotheses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFramesDoublingPolynomialExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grid_frames_doubling_polynomial_exists : GlobalTheory.FunPr.Hypotheses₂ →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ (σ : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank)
      (σ' : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank), ∀ t : T,
      IsFinF W.ψ W.θ true A (frSum AV AV₁) (X.f t) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) ∧
      (∀ P g h, X.ker W.ψ W.θ t P h g = thetaKO (X.ω t) g h (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) (σ P))) ∧
      ∀ P g h, X.ker' W.ψ W.θ t P h g = thetaKO (X.ω' t) g h (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P)) := by
  first | exact @GlobalTheory.TopDict.top_dictionary | exact GlobalTheory.TopDict.top_dictionary | (intros; apply GlobalTheory.TopDict.top_dictionary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftAbelianSchemeOfSquareZeroStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieckMessingLiftAbelianScheme_of_squareZero : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftObj (divided₂ hI) π := by
  first | exact @GlobalTheory.SqLift.liftObj_sq | exact GlobalTheory.SqLift.liftObj_sq | (intros; apply GlobalTheory.SqLift.liftObj_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftHomomorphismOfSquareZeroStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieckMessingLiftHomomorphism_of_squareZero : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftHom (divided₂ hI) π := by
  first | exact @GlobalTheory.SqLift.Hom.liftHom_sq | exact GlobalTheory.SqLift.Hom.liftHom_sq | (intros; apply GlobalTheory.SqLift.Hom.liftHom_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawGlueOverCoprodBaseStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupLaw_glue_over_coprod_base : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂) (A₁ : Over S₁) [GrpObj A₁] (A₂ : Over S₂) [GrpObj A₂] (B₁ : Over T₁) [GrpObj B₁] (B₂ : Over T₂) [GrpObj B₂] (A₀ : Over T) [GrpObj A₀] (i₁ : B₁.left ⟶ A₁.left) (i₂ : B₂.left ⟶ A₂.left) (j₁ : B₁.left ⟶ A₀.left) (j₂ : B₂.left ⟶ A₀.left), IsGrpPullback B₁ A₁ f₁ i₁ → IsGrpPullback B₂ A₂ f₂ i₂ → IsGrpPullback B₁ A₀ v₁ j₁ → IsGrpPullback B₂ A₀ v₂ j₂ → ∀ (i : A₀.left ⟶ A₁.left ⨿ A₂.left), j₁ ≫ i = i₁ ≫ Limits.coprod.inl → j₂ ≫ i = i₂ ≫ Limits.coprod.inr → ∃ m : Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⟶ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)), ∀ l : (A₀ ⊗ A₀).left ⟶ (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))).left, l ≫ (fst (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (fst A₀ A₀).left ≫ i → l ≫ (snd (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (snd A₀ A₀).left ≫ i → l ≫ m.left = (μ[A₀]).left ≫ i := by
  first | exact @GlobalTheory.ProdGlue.mul_glue | exact GlobalTheory.ProdGlue.mul_glue | (intros; apply GlobalTheory.ProdGlue.mul_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalOrigin

theorem evO_constO (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (r : R) :
    evO G (constO G r) = r := by
  have hw : (η[G]).left ≫ G.hom = 𝟙 _ := by simpa using Over.w (η[G])
  have h1 := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left ⊤ trivial
  have h2 := congrArg (fun q => q.hom ((G.hom.appLE ⊤ ⊤ (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) h1
  refine h2.trans ?_
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appLE ⊤ ⊤ (by simp) ≫
      (η[G]).left.app ⊤ ≫ (Functor.mapIso (Spec (CommRingCat.of R)).presheaf
        (eqToIso (show (η[G]).left ⁻¹ᵁ ⊤ = ⊤ by simp)).op ≪≫ Scheme.ΓSpecIso (CommRingCat.of R)).hom = 𝟙 _ := by
    rw [Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_comp_appLE_assoc]
    simp [hw]
    rw [show Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ (by simp) = 𝟙 _ from
      (Scheme.Hom.appLE_eq_app (𝟙 (Sp R))).trans (Scheme.Hom.id_app ⊤)]
    simp
  exact congrArg (fun q => q.hom r) key

end GlobalTheory.FormalOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpLawAndUnitAgreeOfOpenInDescentModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel : ∀ (σ : Setup) (E : Emb σ) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp σ.R) (s₂ : S₂ ⟶ Sp σ.R) (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂] (h₁ : H₁.left ⟶ E.P) (h₂ : H₂.left ⟶ E.P), Flat s₁ → Flat s₂ → Flat H₁.hom → Flat H₂.hom → OpenIn h₁ H₁.hom E.p s₁ → OpenIn h₂ H₂.hom E.p s₂ → MulAgree H₁ σ.A h₁ E.ιA → MulAgree H₂ σ.A h₂ E.ιA → MulAgree H₁ H₂ h₁ h₂ ∧ OneAgree s₁ s₂ H₁ H₂ h₁ h₂ := by
  first | exact @GlobalTheory.Desc.mulAgree_oneAgree_of_openIn | exact GlobalTheory.Desc.mulAgree_oneAgree_of_openIn | (intros; apply GlobalTheory.Desc.mulAgree_oneAgree_of_openIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjOfLawUnitInverseAgreeAwayStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpObj_of_law_unit_inverse_agree_away : ∀ (R : Type) [CommRing R] [IsDomain R] (f g : R), f ≠ 0 → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), Flat q → IsSeparated q → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsCommMonObj A → ∀ i : A.left ⟶ X, IsPullback i A.hom q (awayMap f) → ∀ (H : Over (Sp (Localization.Away g))) (h : H.left ⟶ X), IsPullback h H.hom q (awayMap g) → ∀ (m : H ⊗ H ⟶ H) (n : H ⟶ H) (o : 𝟙_ (Over (Sp (Localization.Away g))) ⟶ H), (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a b : Over.mk t₁ ⟶ H) (a' b' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → b.left ≫ h = b'.left ≫ i → (lift a b ≫ m).left ≫ h = (a' * b').left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a : Over.mk t₁ ⟶ H) (a' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → (a ≫ n).left ≫ h = (a'⁻¹).left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)), t₁ ≫ awayMap g = t₀ ≫ awayMap f → t₁ ≫ o.left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i) → ∃ _ : GrpObj H, MulAgree H A h i := by
  first | exact @GlobalTheory.Desc.SpreadGrp.grpObj_of_agree | exact GlobalTheory.Desc.SpreadGrp.grpObj_of_agree | (intros; apply GlobalTheory.Desc.SpreadGrp.grpObj_of_agree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolRoot

def Root {S T : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (G2 A).left) (t : T ⟶ S) : Prop :=
  ∃ (B : Over T) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left),
    IsGrpPullback B A t β ∧ IsSquare β β₂ ∧ ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) (P.pull β₂)

theorem Root.comp {S T T' : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {P : LB (G2 A).left}
    {t : T ⟶ S} (h : Root A P t) (σ : T' ⟶ T) : Root A P (σ ≫ t) := by
  obtain ⟨A', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := h
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hβ
  obtain ⟨B', _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' σ
  have hB' : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA' hφ
  haveI : IsCommMonObj B' := hB'.comm
  let V := lift (pushPt hφ.1.w (fst B' B')) (pushPt hφ.1.w (snd B' B'))
  have hV : IsSquare φ V.left := GlobalTheory.LamPull.exists_isSquare hφ.1.w
  refine ⟨B', inferInstance, inferInstance, φ ≫ β, V.left ≫ β₂, hφ.comp hβ,
    GlobalTheory.ZM.SiegPull.isSquare_comp hV hsq, L.pull φ, pull_isLB hL φ, ?_⟩
  refine LBIso.chartPull
    (chartPullLinComb L φ _ _ _ V.left fun I => psum_push hφ _ _ V (fun i => ?_) I.down)
    (chartPullSame P (fun _ : PUnit => V.left ≫ β₂) (fun _ => β₂) (fun _ => 1) V.left fun _ => rfl) H
  fin_cases i <;> simp [V, x2]

def tri {X Y T : Scheme.{0}} (f : X ⟶ Y) (a b c : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f) :
    T ⟶ GlobalTheory.LBDescent.Triple f :=
  pullback.lift (pullback.lift a b h₁) (pullback.lift b c h₂) (by rw [pullback.lift_snd, pullback.lift_fst])

def TriCocycle {X Y : Scheme.{0}} (f : X ⟶ Y) (D : Γ(GlobalTheory.LBDescent.Triple f, ⊤)ˣ) : Prop :=
  ∀ (T : Scheme.{0}) (a b c d : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f) (h₃ : c ≫ f = d ≫ f),
    GlobalTheory.CharKer.pullTop (tri f a b c h₁ h₂) D * GlobalTheory.CharKer.pullTop (tri f a c d (h₁.trans h₂) h₃) D =
      GlobalTheory.CharKer.pullTop (tri f b c d h₂ h₃) D * GlobalTheory.CharKer.pullTop (tri f a b d h₁ (h₂.trans h₃)) D

def KillsSq {X Y : Scheme.{0}} (f : X ⟶ Y) (D : Γ(GlobalTheory.LBDescent.Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ) : Prop :=
  D ^ 2 * GlobalTheory.CharKer.pullTop (pullback.fst (pullback.snd f f) (pullback.fst f f)) u *
      GlobalTheory.CharKer.pullTop (pullback.snd (pullback.snd f f) (pullback.fst f f)) u =
    GlobalTheory.CharKer.pullTop (GlobalTheory.LBDescent.pr13 f) u

end GlobalTheory.PolRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpUnitsAndInversesAgreeOfLawsAgreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpUnits_and_inverses_agree_of_laws_agree : ∀ (S S₀ S₁ X : Scheme.{0}) (q : X ⟶ S) (s₀ : S₀ ⟶ S) (s₁ : S₁ ⟶ S) (A : Over S₀) [GrpObj A] (G : Over S₁) [GrpObj G] (i : A.left ⟶ X) (e : G.left ⟶ X), IsPullback i A.hom q s₀ → e ≫ q = G.hom ≫ s₁ → MulAgree G A e i → OneAgree s₁ s₀ G A e i ∧ ∀ (T : Scheme.{0}) (t₁ : T ⟶ S₁) (t₀ : T ⟶ S₀) (a : Over.mk t₁ ⟶ G) (a' : Over.mk t₀ ⟶ A), a.left ≫ e = a'.left ≫ i → (a⁻¹).left ≫ e = (a'⁻¹).left ≫ i := by
  first | exact @GlobalTheory.Desc.oneAgree_invAgree_of_mulAgree | exact GlobalTheory.Desc.oneAgree_invAgree_of_mulAgree | (intros; apply GlobalTheory.Desc.oneAgree_invAgree_of_mulAgree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H0LowerBoundIntersectionNumberClosure
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClosureRR

theorem eventually_le_of_abs_sub_le (k C : ℕ) (T : ℤ) (q : ℚ) (hq : q < T) (h : ℕ → ℕ)
    (hC : ∀ m : ℕ, |(k.factorial : ℤ) * (h m : ℤ) - T * (m : ℤ) ^ k| ≤
      C * ((k : ℤ) * ((m : ℤ) + 1) ^ (k - 1))) :
    ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤ (h l : ℚ) := by
  have hf : (0 : ℚ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hε : (0 : ℚ) < (T : ℚ) - q := sub_pos.2 hq
  obtain ⟨N, hN⟩ := exists_nat_ge ((C : ℚ) * k * 2 ^ (k - 1) / ((T : ℚ) - q))
  refine ⟨N + 1, fun l hl => ?_⟩
  have hm : (1 : ℚ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have hNl : (N : ℚ) ≤ l := by exact_mod_cast (show N ≤ l by omega)
  have hB : (C : ℚ) * k * 2 ^ (k - 1) ≤ ((T : ℚ) - q) * l := by
    have := (div_le_iff₀ hε).1 (hN.trans hNl)
    linarith
  have a := hC l
  rw [abs_le] at a
  have a' : (T : ℚ) * (l : ℚ) ^ k - (C : ℚ) * ((k : ℚ) * ((l : ℚ) + 1) ^ (k - 1)) ≤
      (k.factorial : ℚ) * (h l : ℚ) := by
    have := a.1
    have e : ((T * (l : ℤ) ^ k - C * ((k : ℤ) * ((l : ℤ) + 1) ^ (k - 1)) : ℤ) : ℚ) ≤
        (((k.factorial : ℤ) * (h l : ℤ) : ℤ) : ℚ) := Int.cast_le.2 (by linarith)
    push_cast at e
    exact e
  rw [div_le_iff₀ hf]
  rcases k with _ | j
  · simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, CharP.cast_eq_zero, zero_mul,
      mul_zero, sub_zero, one_mul] at a' ⊢
    linarith
  · simp only [Nat.add_sub_cancel] at a' hB
    have h2 : ((l : ℚ) + 1) ^ j ≤ 2 ^ j * (l : ℚ) ^ j := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) j
    have hl0 : (0 : ℚ) ≤ (l : ℚ) ^ j := by positivity
    have hCk : (0 : ℚ) ≤ (C : ℚ) * ((j + 1 : ℕ) : ℚ) := by positivity
    have e1 : (C : ℚ) * (((j + 1 : ℕ) : ℚ) * ((l : ℚ) + 1) ^ j) ≤
        (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j := by
      have := mul_le_mul_of_nonneg_left h2 hCk
      nlinarith
    have e2 : (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j ≤ ((T : ℚ) - q) * l * (l : ℚ) ^ j :=
      mul_le_mul_of_nonneg_right hB hl0
    rw [pow_succ] at a' ⊢
    nlinarith

end GlobalTheory.ClosureRR

namespace GlobalTheory.ClosureRR

theorem h0_ge_of_lt_interNumRed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X) (k : ℕ) (q : ℚ),
  IsAmpleLB (toLB A) → letI := algebraΓOfHom p; topologicalKrullDim (closure ({z} : Set X)) = k →
  q < (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤
    (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) : ℚ) := by
  intro X _ _ p hp A z k q hA
  letI := algebraΓOfHom p
  intro hdim hq
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p)
  have hi : ∀ r : ℂ, (redι (Closeds.closure ({z} : Set X))).appTop (algebraMap ℂ Γ(X, ⊤) r) =
      algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) r :=
    fun r => rfl
  have hpq : IsProjOver (redι (Closeds.closure ({z} : Set X)) ≫ p) := by
    obtain ⟨n, f, hf, hs⟩ := hp
    exact ⟨n, redι (Closeds.closure ({z} : Set X)) ≫ f, inferInstance, by rw [Category.assoc, hs]⟩
  have hstr : strHom ℂ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme =
      redι (Closeds.closure ({z} : Set X)) ≫ p := strHom_eq fun _ => rfl
  have hD : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme = k :=
    (topologicalKrullDim_red _).trans hdim
  have hNef : IsNef ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) :=
    (IsAmpleLB.isNef (k := ℂ) hA).pull_of_isClosedImmersion _ hi
  obtain ⟨C, hC⟩ := NefRiemannRoch.abs_factorial_mul_sections_sub_top_le ℂ _ (hstr ▸ hpq) k hD.le _ hNef
  have heq : interNumRed ℂ (Closeds.closure ({z} : Set X)) (fun _ : Fin k => toLB A) =
      topSelfIntersection ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) k :=
    interNumOn_const_eq_topSelf hi (isLB_toLB A) k
  have hH : ∀ l : ℕ, lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) =
      lbH0 ℂ (lbPow ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) l) := fun l =>
    lineBundleGlobalSectionsDim_congr_picardClass (pull_isLB (isLB_toLB _) _) (isLB_lbPow (pull_isLB (isLB_toLB A) _) l)
      (by rw [cls_lbPow (pull_isLB (isLB_toLB A) _), cls_pull (isLB_toLB _), cls_pull (isLB_toLB A),
        ← toPic_apply, ← toPic_apply, map_nsmul, map_nsmul])
  rw [heq] at hq
  obtain ⟨l₁, hl₁⟩ := eventually_le_of_abs_sub_le k C _ q hq _ hC
  exact ⟨l₁, fun l hl => by rw [hH l]; exact hl₁ l hl⟩

end GlobalTheory.ClosureRR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfLevelSubmodulePermutationStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.half_level_submodule_permutation : Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ (hp : RowsT p) (Hg : Type) [Group Hg] [Finite Hg] (φ : Hg →* p.P.Gp),
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun h => (p.O i).lev2 (φ h)) →
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction Hg X) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.CF p i))),
      (∀ (h : Hg) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : Hg) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.actC p i hp.1 (φ h)) v ∈ A (h • y) := by
  first | exact @GlobalTheory.DefSplit.split_lift | exact GlobalTheory.DefSplit.split_lift | (intros; apply GlobalTheory.DefSplit.split_lift <;> assumption)
end

