import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueEqRootMulThetaOperatorValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2866
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedUniformizationPullbackStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_uniformization_pullback : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L₀ : LB A.left) (g : ℕ) (u : HolUnif A L₀ g)
    (L : LB (A ⊗ A).left) (U : HolUnif (A ⊗ A) L (g + g)),
    (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → ∀ x₀ : Fin g → ℂ,
    ∃ u' : HolUnif A (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left) g, u'.ex = u.ex ∧
      (∀ j z, (⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left).U j ↔
        ⊤ ≤ (U.ex (Fin.append z x₀)).left ⁻¹ᵁ L.U (j PUnit.unit))) ∧
      ∀ j z, u'.fr j z = U.fr (j PUnit.unit) (Fin.append z x₀) := by
  first | exact @GlobalTheory.TorusPullFrame.exists_holUnif_pull_right | exact GlobalTheory.TorusPullFrame.exists_holUnif_pull_right | (intros; apply GlobalTheory.TorusPullFrame.exists_holUnif_pull_right <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsosCommuteOfCommutatorPairingOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translation_isos_commute_of_commutatorPairing_one : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (L : LB G.left), L.IsLB → ∀ (x y : 𝟙_ (Over S) ⟶ G) (φx : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl x).left] ![1, -1])) (φy : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl y).left] ![1, -1])), φx.IsGen → φy.IsGen → Out.WeilIs G L 1 x y 1 → LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ φx (LB.pullGen L _ _ φy (GlobalTheory.UPel.HT.Hecke.transl x).left)) (LB.mulGen L _ _ _ _ φy (LB.pullGen L _ _ φx (GlobalTheory.UPel.HT.Hecke.transl y).left)) := by
  first | exact @GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs | exact GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs | (intros; apply GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwicePicardClassEqZeroOfTranslatesMemOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twice_picardClass_eq_zero_of_translates_mem_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), A.hom ⁻¹ᵁ U ≤ W → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A), (∀ y, Y.hom y ∈ U) → (∀ y, v.left y ∈ V) → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → ∀ l : Y.left ⟶ W.toScheme, l ≫ W.ι = x.left → GlobalTheory.CechPic.pull l (2 • c) = 0 := by
  first | exact @GlobalTheory.twice_cls_eq_zero_of_translates_mem | exact GlobalTheory.twice_cls_eq_zero_of_translates_mem | (intros; apply GlobalTheory.twice_cls_eq_zero_of_translates_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioEqOneUnitSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.twistRatio_eq_one_at_unit : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X) (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) ae) (LB.pullGen D.P.L _ _ (gp.s χ) (thick R I e))) → ∀ (z : Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (J : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D.P.A.left) → D.P.L.ι) (J' : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val (g.t χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ h) z J * ((∏ k, gv w ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J (((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J' * val (gp.s χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = 1 := by
  intro R _ _ I D D₂ e G _ _ g g₂ β gp w χ₂ χ a h hh hf hcorr z J J' hJ hJ'
  set o := (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G) with ho
  have hom1 : o.left ≫ (thickObj R I e G).hom = 𝟙 _ := Over.w o
  have e1 : o.left ≫ h ≫ (thickObj R I e G).hom = 𝟙 _ := by rw [hh, hom1]
  have f1 : (Over.map (thick R I e)).map o ≫ fstG I e G = 1 := by
    have := GlobalTheory.FormalPoint.map_mul_fstG (R := R) (I := I) (e := e) (G := G) o o
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  let T := (Over.map (thick R I e)).obj (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))))
  have tu : (toUnit T).left = thick R I e := by
    have := Over.w (toUnit T)
    simpa [T] using this
  have e2 : o.left ≫ h ≫ (fstG I e G).left = thick R I e ≫ a.left := by
    rw [hf]
    show ((Over.map (thick R I e)).map o ≫ fstG I e G ≫ ((toUnit G ≫ a) * 𝟙 G)).left = _
    rw [← Category.assoc, f1, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, _root_.mul_one,
      Over.comp_left, tu]
  have hc := hcorr (o.left ≫ h) (by simpa [Category.assoc] using e1) (by simpa [Category.assoc] using e2)
  have va := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at va
  have vb : val (g₂.t χ₂) o.left z J' = 1 := GlobalTheory.TorusCoord.val_unit g₂ χ₂ hJ'
  let f : (_ ⟶ D₂.P.A.left) → _ := fun ψ => gv w ψ z (fun i => J (ψ ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' ψ)
  have e0 : ∀ k, o.left ≫ D₂.Oφ g₂.pG χ₂ k = D₂.Oφ (1 : T ⟶ D₂.P.A) χ₂ k :=
    fun k => (WeightPf.Oφ_comp ((Over.map (thick R I e)).map o) g₂.pG χ₂ k).trans
      (congrArg (D₂.Oφ · χ₂ k) (GlobalTheory.TorusCoord.im_one g₂))
  have vc : (∏ k, f (o.left ≫ D₂.Oφ g₂.pG χ₂ k) ^ Oinvε k) = 1 := by
    refine (Finset.prod_congr rfl fun k _ => congrArg (fun ψ => f ψ ^ Oinvε k) (e0 k)).trans ?_
    rw [Fin.prod_univ_four]
    show f ((1 : T ⟶ D₂.P.A) * (toUnit T ≫ D₂.c χ₂)).left ^ (-1 : ℤ) * f (toUnit T ≫ D₂.c χ₂).left ^ (1 : ℤ) *
      f (1 : T ⟶ D₂.P.A).left ^ (1 : ℤ) * f (1 : T ⟶ D₂.P.A).left ^ (-1 : ℤ) = 1
    rw [_root_.one_mul]
    simp
  have vc' : (∏ k, gv w (o.left ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((o.left ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (o.left ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) = 1 := vc
  rw [vc', vb, ← Category.assoc, hom1, Category.id_comp, va, _root_.one_mul, _root_.one_mul, mul_inv_cancel]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioFibreInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwCoordInv

open GlobalTheory.CoordCompare TorusCoord

theorem ratio_translate_invariant : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] [Mono β.left], g₂.pG ≫ β = g.pG → ∀ (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A → r ≫ g₂.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D₂.P.A → val (g.t χ) r z J = val (g₂.t χ₂) r z J') → ∀ (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.q.left = r' ≫ g.q.left → val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = val (g.t χ) (r' ≫ h) z J * ((∏ k, gv w (r' ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r' ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r' ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r' z J' * val (gp.s χ) (r' ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  intro R _ _ I D D₂ e G _ _ g g₂ β _ _ hβ gp w χ₂ χ hker a₀ h hh hf Z r r' z J J' hJ hJ' hq
  obtain ⟨h₁, h₂⟩ := ratio_invariant g g₂ β hβ χ χ₂ hker r r' z J J' hJ hJ' hq
  have hw : r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom := by
    rw [← Over.w g.q, reassoc_of% hq]
  have hprod : ∀ k, r ≫ D₂.Oφ g₂.pG χ₂ k = r' ≫ D₂.Oφ g₂.pG χ₂ k := fun k =>
    Oφ_congr χ₂ g₂.pG r r' h₁ k
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G).hom)
  let b : Z' ⟶ thickObj R I e G := Over.homMk r hw
  let b' : Z' ⟶ thickObj R I e G := Over.homMk r' rfl
  obtain ⟨τ, hτ⟩ := exists_torus g b b' (Over.OverMorphism.ext hq)
  let hO : thickObj R I e G ⟶ thickObj R I e G := Over.homMk h hh
  have hfO : (Over.map (thick R I e)).map hO ≫ fstG I e G =
      fstG I e G ≫ ((toUnit G ≫ a₀) * 𝟙 G) := Over.OverMorphism.ext hf
  have hsh : ∀ x : Z' ⟶ thickObj R I e G, (Over.map (thick R I e)).map (x ≫ hO) ≫ fstG I e G =
      (toUnit _ ≫ a₀) * ((Over.map (thick R I e)).map x ≫ fstG I e G) := fun x => by
    rw [Functor.map_comp, Category.assoc, hfO, ← Category.assoc, MonObj.comp_mul, comp_toUnit_assoc,
      Category.comp_id]
  have hkey : b ≫ hO = (τ ≫ g.i) * (b' ≫ hO) := by
    apply FormalPoint.eq_of_map_fstG
    rw [hsh, FormalPoint.map_mul_fstG, hsh, hτ, FormalPoint.map_mul_fstG, mul_left_comm]
  have v₁ := val_torus_mul g χ (Z := Z') hJ τ _ (b ≫ hO) (b' ≫ hO) rfl hkey
  have v₂ := val_torus_mul g χ (Z := Z') hJ τ _ b b' rfl hτ
  let k : Z ⟶ (thickObj R I e G).left := (τ ≫ g.i).left
  have v₁' : val (g.t χ) (r ≫ h) z J = val (g.t χ) k z J * val (g.t χ) (r' ≫ h) z J := v₁
  have v₂' : val (g.t χ) r z J = val (g.t χ) k z J * val (g.t χ) r' z J := v₂
  have hB : val (g₂.t χ₂) r z J' = val (g.t χ) k z J * val (g₂.t χ₂) r' z J' := by
    rw [v₂'] at h₂
    rw [mul_inv_eq_iff_eq_mul.1 h₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hP : (∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z
        (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i))
        (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) =
      ∏ k, gv w (r' ≫ D₂.Oφ g₂.pG χ₂ k) z
        (fun i => J ((r' ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i))
        (J' (r' ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k :=
    Finset.prod_congr rfl fun k _ => by rw [hprod k]
  have hS : val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J =
      val (gp.s χ) (r' ≫ (thickObj R I e G).hom ≫ thick R I e) z J := by
    rw [reassoc_of% hw]
  rw [hP, hS, v₁', hB]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TwCoordInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_of_isSum {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {n j : ℤ} (τ : SecE U b n j)
    {Ix : Type} {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β)
    (hs : Small I s) (hF : IsSum I s F) (hτ : TExp U τ s) : TExp U τ (w := id) F := by
  classical
  intro S hS Z x z J J' hJ hJ'
  have h0 : ∀ i ∉ (hs e).toFinset, Van I (s i) e := fun i hi => by
    by_contra h
    exact hi ((hs e).mem_toFinset.2 h)
  have hx : x ≫ (U.gt e).pG.left =
      (x ≫ (U.gt e).q.left) ≫ pullback.fst D.toPre.P.A.hom (thick R I e) := (Category.assoc _ _ _).symm
  rw [hτ _ h0 Z x z J J' hJ hJ']
  have hsum : ∀ δ, sval (F δ) (x ≫ (U.gt e).pG.left) z J =
      ∑ i ∈ (hs e).toFinset.filter (fun i => w i = δ), sval (s i) (x ≫ (U.gt e).pG.left) z J := fun δ => by
    rw [hx]
    convert hF e _ h0 δ Z (x ≫ (U.gt e).q.left) z J hJ
  have hvan : ∀ δ ∉ S, sval (F δ) (x ≫ (U.gt e).pG.left) z J = 0 := fun δ hδ => by
    rw [hx]
    exact hS δ hδ Z (x ≫ (U.gt e).q.left) z J hJ
  have key : ∀ T : Finset D.toPre.X, (hs e).toFinset.image w ⊆ T →
      ∑ i ∈ (hs e).toFinset, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val =
      ∑ δ ∈ T, sval (F δ) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t δ) x z J).val := fun T hT => by
    rw [← Finset.sum_fiberwise_of_maps_to (g := w) (t := T) (fun i hi => hT (Finset.mem_image_of_mem w hi))]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain rfl := (Finset.mem_filter.1 hi).2
    rfl
  rw [key _ (Finset.subset_union_left (s₂ := S))]
  refine (Finset.sum_subset Finset.subset_union_right fun δ _ hδ => ?_).symm
  exact (congrArg (· * _) (hvan δ hδ)).trans (zero_mul _)

theorem texp_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j : ℤ) (τ : SecE U.toUnifPre b n j) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → TExp U.toUnifPre τ s → TExp U.toUnifPre τ (w := id) F :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U _ _ _ _ τ _ _ s F hs hF hτ => texp_of_isSum U.toUnifPre τ s F hs hF hτ

end GlobalTheory.TwFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionMulOfMemberProducts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_mul_of_prod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β) (p : ∀ q : D.toPre.X × D.toPre.X, SecT D.toPre a n'' j'' (q.1 + q.2)) (τ : SecE U.toUnifPre b n j) (τ' : SecE U.toUnifPre b n' j') (τ'' : SecE U.toUnifPre b n'' j''), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → (∀ q : D.toPre.X × D.toPre.X, IsProdT (f q.1) (g q.2) (p q)) → TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') → TExp U.toUnifPre τ'' (w := fun q : D.toPre.X × D.toPre.X => q.1 + q.2) p := by
  intro R _ _ _ _ D a A G _ _ _ U e b n j n' j' n'' j'' hn hj f g p τ τ' τ'' hf hg hp hτ hτ' hτ''
  classical
  subst hn hj
  intro S hS Z x z J J' hJ hJ'
  have hy : x ≫ (U.gt e).pG.left = (x ≫ (U.gt e).q.left) ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) := by
    simp [GtCoord.pG, DegPre.prBe, Over.comp_left, Over.map_map_left, Over.homMk_left]
  have vanAt : ∀ {n j : ℤ} {β : D.toPre.X} (s : SecT D.toPre a n j β), Van (maximalIdeal R) s e →
      sval s (x ≫ (U.gt e).pG.left) z J = 0 := fun s hs => by rw [hy]; exact hs Z _ z J hJ
  have h1 : evalE U.toUnifPre τ'' x z J J' = evalE U.toUnifPre τ x z J J' * evalE U.toUnifPre τ' x z J J' := by
    simp only [evalE, zpow_add, Units.val_mul]; rw [hτ'' Z x z J' hJ']; ring
  have hL : ∀ χ χ' : D.toPre.X, x ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (U.gt e).pG)).left =
      (x ≫ (U.gt e).pG.left) ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (𝟙 D.toPre.P.A)) :
        D.toPre.P.A ⟶ G3 D.toPre.P.A).left := by
    intro χ χ'
    rw [Category.assoc, ← Over.comp_left]
    congr 2
    simp [comp_lift]
  have hT : ∀ χ χ' : D.toPre.X, (val ((U.gt e).t (χ + χ')) x z J).val *
      (val D.toPre.cub.t ((x ≫ (U.gt e).pG.left) ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (𝟙 D.toPre.P.A)) :
        D.toPre.P.A ⟶ G3 D.toPre.P.A).left) z J).val =
      (val ((U.gt e).t χ) x z J).val * (val ((U.gt e).t χ') x z J).val := by
    intro χ χ'
    have h := (val_mul hJ _ _ x).symm.trans ((val_corr hJ ((U.gt e).t_mul χ χ') x).trans (val_mul hJ _ _ x))
    have h' := (congrArg (val ((U.gt e).t (χ + χ')) x z J * ·) (val_pull hJ _ _ x)).symm.trans h
    rw [← hL χ χ']
    exact (Units.val_mul _ _).symm.trans ((congrArg Units.val h').trans (Units.val_mul _ _))
  have hSf : ∀ i ∉ (hf e).toFinset, Van (maximalIdeal R) (f i) e := fun i hi =>
    by_contra fun hc => hi ((hf e).mem_toFinset.2 hc)
  have hSg : ∀ i ∉ (hg e).toFinset, Van (maximalIdeal R) (g i) e := fun i hi =>
    by_contra fun hc => hi ((hg e).mem_toFinset.2 hc)
  have ef : evalE U.toUnifPre τ x z J J' = ∑ i ∈ (hf e).toFinset,
      sval (f i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t i) x z J).val := hτ _ hSf Z x z J J' hJ hJ'
  have eg : evalE U.toUnifPre τ' x z J J' = ∑ i ∈ (hg e).toFinset,
      sval (g i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t i) x z J).val := hτ' _ hSg Z x z J J' hJ hJ'
  have hP := fun q => hp q Z (x ≫ (U.gt e).pG.left) z J hJ
  have z₁ : ∀ q ∉ S, sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val = 0 :=
    fun q hq => by rw [vanAt _ (hS q hq), zero_mul]
  have z₂ : ∀ q ∉ (hf e).toFinset ×ˢ (hg e).toFinset,
      sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val = 0 := by
    intro q hq
    rw [Finset.mem_product, not_and_or] at hq
    rw [hP q]
    rcases hq with h | h
    · rw [vanAt _ (hSf _ h), zero_mul, zero_mul, zero_mul]
    · rw [vanAt _ (hSg _ h), mul_zero, zero_mul, zero_mul]
  show _ = ∑ q ∈ S, sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val
  rw [h1, ef, eg, Finset.sum_mul_sum, ← Finset.sum_product',
    Finset.sum_subset (Finset.subset_union_right (s₁ := (hf e).toFinset ×ˢ (hg e).toFinset)) (fun q _ hq => z₁ q hq),
    ← Finset.sum_subset (Finset.subset_union_left (s₂ := S)) (fun q _ hq => z₂ q hq)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hP q]
  linear_combination (-(sval (f q.1) (x ≫ (U.gt e).pG.left) z J * sval (g q.2) (x ≫ (U.gt e).pG.left) z J)) * hT q.1 q.2

end GlobalTheory.TwFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGenerat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFac

theorem exists_zpow {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, val t' r z J = val t r z J ^ n := by
  refine ⟨⟨fun j => (show Γ(Y, LB.wchart L φ j)ˣ from t.s j) ^ n⟩, fun i j => ?_, fun Z r z J => map_zpow _ _ _⟩
  refine ((map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_zpow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)
  exact (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ => (zpow_mul _ _ _).symm)

theorem exists_norm {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (S₀ ⟶ X)} {ε' : K' → ℤ}
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hF : FormEq (fun k => e ≫ φ k) ε φ' ε')
    (w : LB.Gen (LB.LinComb M φ ε)) (hw : w.IsGen) (v : LB.Gen (LB.LinComb M φ' ε')) (hv : v.IsGen) :
    ∃ u : LB.Gen (LB.LinComb M φ ε), u.IsGen ∧ ∀ y J, Good M y J → val u e y J = val v (𝟙 _) y J := by
  obtain ⟨u, hu, vu⟩ := exists_gen hM (φ' := φ) (ε' := ε) (fun U _ h => by
      have q := hF U (fun g => h (p ≫ g))
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [q, mul_inv_cancel, _root_.mul_one])
    (LB.mulGen M _ _ _ _ w (LB.pullGen M _ _ (LB.mulGen M _ _ _ _ v (LB.invGen M _ _ (LB.pullGen M _ _ w e))) p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hv
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hw _))) _))
  refine ⟨u, hu, fun y J hJ => ?_⟩
  rw [vu _ _ y J hJ, val_mul hJ, val_pull hJ, he, val_mul hJ, val_inv, val_pull hJ, Category.id_comp, mul_comm,
    inv_mul_cancel_right]

variable {R : Type} [CommRing R] [IsDomain R]

theorem tr_left (D : DegPre R) (mu : D.X) :
    (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left =
      (DegPre.prB D (FractionRing R)).left ≫ (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  refine (lift_snd _ _).trans ?_
  refine Eq.trans ?_ (MonObj.comp_mul _ _ _).symm
  rw [Category.comp_id]
  exact congrArg (DegPre.prB D (FractionRing R) * ·) (DVR.comp_cP D _ mu).symm

theorem prod_t (D : DegPre R) (a : D.P.A ⟶ D.P.A) (β : D.X) (n j : ℤ) {T : Over (Sp R)} (y : T ⟶ D.P.A)
    {U : Type} [CommGroup U] (g : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, g (y.left ≫ tφ D a β k) ^ tε n j k = g y.left ^ (n - 1) * g (y * DVR.cP D T β).left *
      (g (DVR.cP D T β).left)⁻¹ * g (1 : T ⟶ D.P.A).left * g (y ≫ a).left ^ j := by
  have e₀ : y.left ≫ tφ D a β 0 = y.left := Category.comp_id _
  have e₁ : y.left ≫ tφ D a β 1 = (y * DVR.cP D T β).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul y (𝟙 _) (DVR.cP D _ β)).trans (by rw [DVR.comp_cP, Category.comp_id]))
  have e₂ : y.left ≫ tφ D a β 2 = (DVR.cP D T β).left := congrArg (fun q => q.left) (DVR.comp_cP D y β)
  have e₃ : y.left ≫ tφ D a β 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) y)
  have e₄ : y.left ≫ tφ D a β 4 = (y ≫ a).left := rfl
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃, e₄]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem exists_fac (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) [IsMonHom a] (hh : ∀ y, D.c (h y) = D.c y ≫ a)
    (n j : ℤ) (mu β β' : D.X) (w : LB.Gen (LB.LinComb D.P.L (dφ D a mu β β') (dε n j))) (hw : w.IsGen) :
    ∃ u, IsFac D a h n j mu β β' u := by
  obtain ⟨p₁, h₁, v₁⟩ := exists_zpow (D.psi mu) (D.psi_gen mu) n
  obtain ⟨p₂, h₂, v₂⟩ := exists_zpow (D.psi (h mu)) (D.psi_gen _) j
  obtain ⟨p₃, h₃, v₃⟩ := exists_zpow D.rigK (DVR.pullGen_isGen _ _ _ _ D.rig_gen _) (n + j)
  have z₁ : DegPre.zF D (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R) = 1 := lift_snd _ _
  have z₃ : DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) =
      DVR.cP D _ mu := by
    rw [DVR.trF_eq, DVR.tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  obtain ⟨u, hu, vu⟩ := exists_norm D.P.isLB (fst (TF (R := R) (FractionRing R)) D.P.A).left
    (DegPre.zF D (FractionRing R)).left (congrArg (fun q => q.left) z₁) (fun U _ g => by
      have a₁ : ∀ χ, jFK (R := R) (FractionRing R) ≫ ptK (D.c χ) = (DVR.cP D (TF (R := R) (FractionRing R)) χ).left :=
        fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) (FractionRing R) ≫ (toUnit (TK R)).left ≫ eSec D.P.A =
          (1 : TF (R := R) (FractionRing R) ⟶ D.P.A).left := (Category.assoc _ _ _).symm
      have q₁ := prod_t D a β' n j (DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R)) g
      have q₂ := prod_t D a β n j
        (DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)) g
      have b₁ : (1 : TF (R := R) (FractionRing R) ⟶ D.P.A) ≫ a = 1 := MonObj.one_comp _
      have b₂ : DVR.cP D (TF (R := R) (FractionRing R)) mu ≫ a = DVR.cP D _ (h mu) := by
        rw [DVR.cP, DVR.cP, hh, Category.assoc]
      conv_rhs at q₁ => rw [z₂, b₁, _root_.one_mul]
      conv_rhs at q₂ => rw [z₃, b₂, ← DVR.cPoint_add]
      simp only [Over.comp_left, Category.assoc] at q₁ q₂
      refine (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    w hw (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂)
      (D.tau mu β)) p₃) (jFK (R := R) (FractionRing R)))
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ h₂) (DVR.tau_isGen D mu β)) h₃) _)
  refine ⟨u, hu, fun z J hJ => (vu z J hJ).trans ((val_pull hJ _ _ _).trans ?_)⟩
  rw [Category.id_comp]
  exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v₁ _ _ _ _) (v₂ _ _ _ _))) rfl)) (v₃ _ _ _ _))

theorem fac_exists_unique_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h : D.toPre.X →+ D.toPre.X), IsMonHom a → (∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a) → ∀ (n j : ℤ) (mu β β' : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j))), u₀.IsGen → (∃ u, IsFac D.toPre a h n j mu β β' u) ∧ (∀ u u', IsFac D.toPre a h n j mu β β' u → IsFac D.toPre a h n j mu β β' u' → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → val u x z J = val u' x z J) ∧ ∀ u : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a mu β β') (dε n j)), u.IsGen → ∃ c : (FractionRing R), ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) c) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  intro R _ _ _ _ D a h ha hh n j mu β β' u₀ hu₀
  have hL := D.toPre.P.isLB
  have hs := DVR.surj_appTop D.toPre (FractionRing R) GlobalTheory.globalFns_holds
  obtain ⟨w, hw, vw⟩ := exists_gen hL (φ' := dφ D.toPre a mu β β') (ε' := dε n j) (fun U _ g => by
      refine Finset.prod_congr rfl ?_
      rintro (k | k) -
      · rfl
      · simp only [dφ, Sum.elim_inr]
        rw [← Category.assoc, ← tr_left, Category.assoc])
    (LB.pullGen D.toPre.P.L _ _ u₀ (DegPre.prB D.toPre (FractionRing R)).left) (DVR.pullGen_isGen _ _ _ _ hu₀ _)
  refine ⟨exists_fac D.toPre a h hh n j mu β β' w hw, fun u u' hu hu' => ?_, fun u hu => ?_⟩
  · have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
    exact gen_unique hL (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left (DegPre.zF D.toPre (FractionRing R)).left
      (congrArg (fun q => q.left) z₁) hs hu.1 hu'.1 (fun y J hJ => (hu.2 y J hJ).trans (hu'.2 y J hJ).symm)
  · obtain ⟨c, hc⟩ := GlobalTheory.WeilMul.exists_ratio hL (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left hs hu hw
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom c, fun Z x z J hJ => ?_⟩
    have e : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom c) = c := Iso.hom_inv_id_apply _ c
    have e₂ := (hc Z x z J hJ).trans ((gs_pull x (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z ⊤ trivial c).symm)
    rw [vw _ _ z J hJ, val_pull hJ] at e₂
    refine Eq.trans ?_ (congrArg₂ (· * ·) (e₂.trans (congrArg (fun q => gs x z ⊤
      ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left.appTop.hom q)) e.symm)) rfl)
    rw [← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.TwFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueEqRootMulThetaOperatorValueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] [ArithBase o' Ω'] {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left) (x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)), IsGenLab ρ ρ' lab φ P₀ a a' x → ∀ (m : ℕ), S'.N = m ^ 2 → ∀ (κ x₀ : S.Gam) (h : S'.Gam), m • h = lab κ → ∃ ξ : Ω', (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ (t : S'.Gam) (v : Ω'), IsTwVal ρ.P S'.N m ρ.th₁ (ρ.fr κ) (genTo _) (x (S'.r • t)) (x h) ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom v) → v * S'.th (lab x₀) = ξ * φ (S.th x₀) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := by
  first | exact @GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul | exact GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul | (intros; apply GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleRigidLinearisationsSameLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationBundle_rigidLinearisations_same_localUnits : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (s : Sp R' ⟶ Sp R') (f₁ f₂ : G'.left ⟶ G'.left), f₁ = f₂ → ∀ (he₁ : eSec G' ≫ f₁ = s ≫ eSec G') (he₂ : eSec G' ≫ f₂ = s ≫ eSec G') (w₁ : LB.Iso U'.LG.L (U'.LG.L.pull f₁)) (w₂ : LB.Iso U'.LG.L (U'.LG.L.pull f₂)), w₁.IsGen → w₂.IsGen → LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₁ s he₁ U'.LG.L U'.LG.rig) → LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₂ s he₂ U'.LG.L U'.LG.rig) → ∀ (z : G'.left) (j k : U'.LG.L.ι), z ∈ U'.LG.L.U k → f₁ z ∈ U'.LG.L.U j → gw w₁ (𝟙 G'.left) z j k = gw w₂ (𝟙 G'.left) z j k := by
  first | exact @GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified | exact GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified | (intros; apply GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismClosedFibreTorusCharacStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_endomorphism_closedFibreTorus_characterMap : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (E : EndU U.toUnifPre), EndChar U E.aG E.h := by
  first | exact @GlobalTheory.Poinc.Eq8.endChar_endU | exact GlobalTheory.Poinc.Eq8.endChar_endU | (intros; apply GlobalTheory.Poinc.Eq8.endChar_endU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedAlongAllTraitsRestrictAffineOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedAlongAllTraits_restrict_affineOpen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsSemiAbelian G → UnifAlong G L.L → UnifAlong (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L := by
  first | exact @GlobalTheory.KeyVals.unifAlong_affineOpen | exact GlobalTheory.KeyVals.unifAlong_affineOpen | (intros; apply GlobalTheory.KeyVals.unifAlong_affineOpen <;> assumption)
end

