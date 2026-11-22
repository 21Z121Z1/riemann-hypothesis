import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0755
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeSpecAlgebraProd
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_baseChange_spAlg_prod (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (B : Over (Sp R)) [GrpObj B] (g : ℕ) :
    IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∃ (B' : Over (Sp D)) (_ : GrpObj B') (π : B'.left ⟶ B.left) (q : B'.left ⟶ (SpAlg R D ⊗ B).left), IsGrpPullback B' B (spMap (algebraMap R D)) π ∧ IsAbelianScheme B' ∧ SmoothOfRelativeDimension g B'.hom ∧ IsIso q ∧ q ≫ (fst (SpAlg R D) B).left = B'.hom ∧ q ≫ (snd (SpAlg R D) B).left = π := by
  intro hA hg
  refine ⟨(Over.pullback (spMap (algebraMap R D))).obj B, inferInstance, CategoryTheory.Limits.pullback.fst B.hom _,
    (CategoryTheory.Limits.pullbackSymmetry B.hom (spMap (algebraMap R D))).hom,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B _, GlobalTheory.isAbelianScheme_pullback_obj _ B hA,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (CategoryTheory.IsPullback.of_hasPullback _ _) hg,
    inferInstance, ?_, ?_⟩
  · simp
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftOfSplitRing
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLiftGlue

theorem exists_lift_of_split : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (e : R), IsIdempotentElem e → ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ → (∀ f : R, (f = e ∨ f = 1 - e) → ∃ (A : Over (Sp (R ⧸ Ideal.span {f}))) (_ : GrpObj A) (B : Over (Sp (R₀ ⧸ Ideal.span {π f}))) (_ : GrpObj B) (i : B.left ⟶ A.left) (j : B.left ⟶ A₀.left) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π ∧ IsGrpPullback B A (spMap ρ) i ∧ IsGrpPullback B A₀ (spMap (Ideal.Quotient.mk _)) j ∧ IsAbelianScheme A) → ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A := by
  intro R R₀ _ _ I hI π hπ hk e he A₀ _ hA₀ H
  obtain ⟨A₁, gA₁, B₁, gB₁, i₁, j₁, ρ₁, hρ₁, hp₁, hq₁, hab₁⟩ := H e (Or.inl rfl)
  obtain ⟨A₂, gA₂, B₂, gB₂, i₂, j₂, ρ₂, hρ₂, hp₂, hq₂, hab₂⟩ := H (1 - e) (Or.inr rfl)
  have cS := GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents R e (1 - e) he (by ring)
  have cT := GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents R₀ (π e) (π (1 - e)) (he.map π) (by rw [← map_add]; simp)
  obtain ⟨i, hi₁, hi₂, hpb⟩ := GlobalTheory.T.isPullback_coprodDesc_of_pieces_over_coprod _ _ cS _ _ cT (spMap π) (spMap ρ₁) (spMap ρ₂) (GlobalTheory.T.isPullback_spMap_quotient_span_baseChange R R₀ π e ρ₁ hρ₁) (GlobalTheory.T.isPullback_spMap_quotient_span_baseChange R R₀ π (1 - e) ρ₂ hρ₂)
    A₁.hom A₂.hom A₀.hom B₁.hom B₂.hom j₁ j₂ i₁ i₂ hq₁.1 hq₂.1 hp₁.1 hp₂.1
  have hsm := GlobalTheory.T.smooth_coprodDesc_of_smooth_pieces _ _ cS A₁.hom A₂.hom hab₁.smooth hab₂.smooth
  set X : Over (Sp R) := Over.mk (Limits.coprod.desc (A₁.hom ≫ spMap (Ideal.Quotient.mk (Ideal.span {e}))) (A₂.hom ≫ spMap (Ideal.Quotient.mk (Ideal.span {1 - e})))) with hX
  obtain ⟨m, hm⟩ := GlobalTheory.T.groupLaw_glue_over_coprod_base _ _ cS _ _ cT (spMap ρ₁) (spMap ρ₂) A₁ A₂ B₁ B₂ A₀ i₁ i₂ j₁ j₂ hp₁ hp₂ hq₁ hq₂ i hi₁ hi₂
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk, hI]⟩
  have hsm' : Smooth X.hom := hsm
  have hpb' : IsPullback i A₀.hom X.hom (spMap π) := hpb
  obtain ⟨e₁, he₁, he₁'⟩ := GlobalTheory.T.exists_section_lift_smooth_nilpotent_thickening R R₀ π hπ hnil X A₀ i hpb' hsm' (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left (Over.w _)
  have hw : ∀ g : A₀ ⊗ A₀ ⟶ A₀, (g.left ≫ i) ≫ X.hom = (Over.mk ((A₀ ⊗ A₀).hom ≫ spMap π)).hom := fun g ↦ by
    simp only [Over.mk_hom, Category.assoc, hpb'.w]; rw [← Category.assoc, Over.w]
  let l : Over.mk ((A₀ ⊗ A₀).hom ≫ spMap π) ⟶ X ⊗ X := lift (Over.homMk _ (hw (fst A₀ A₀))) (Over.homMk _ (hw (snd A₀ A₀)))
  have hl₁ : l.left ≫ (fst X X).left = (fst A₀ A₀).left ≫ i := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hl₂ : l.left ≫ (snd X X).left = (snd A₀ A₀).left ≫ i := by
    rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨g, hg, hab⟩ := GlobalTheory.T.exists_grpObj_isAbelianScheme_smoothLift_nilpotent R R₀ π hπ hnil A₀ hA₀ X i hpb' hsm' e₁ he₁ he₁' l.left hl₁ hl₂ m (hm l.left hl₁ hl₂)
  exact ⟨X, g, i, hg, hab⟩

end GlobalTheory.AbLiftGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedLieBasisTorusExtensionModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Adapt

set_option maxHeartbeats 1000000 in
theorem main : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∃ (vB : Fin D.toPre.P.g → (epsR V ⟶ D.toPre.P.A)) (r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r) (y : Fin A.g → (epsR V ⟶ G)) (gm₀ : Fin A.g → GtPt D.toPre (epsR V)) (gm : Fin A.g → GtPt D.toPre (TE V C)), IsLieBasis y ∧ Adapted ν vB bX σ gm ∧ ∀ j, TanRel U.toUnifPre (y j) (gm₀ j) ∧ GtTan (gm₀ j) ∧ GtPt.IsPull (spMap (dualMap (toF V C))) (gm₀ j) (gm j) := by
  intro V _ _ _ _ hV D A G _ _ hS U C _ _ _ _ _ _ hC N ν hν
  haveI := hV
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨H, _, _, hH⟩ := GlobalTheory.TorusModel.exists_isGt hG (GlobalTheory.TorusModel.splitExt D.toPre)
  obtain ⟨Φ, hp, ha⟩ := GlobalTheory.TorusModel.exists_points hG hH
  have hΦ : GlobalTheory.TorusModel.Represents Φ := ⟨hp, ha⟩
  obtain ⟨vB, hvB⟩ := GlobalTheory.KeyPow.exists_isLieBasis D.toPre.P.A D.toPre.P.smoothDim
  let r := Module.finrank ℤ N.X
  let bX : Module.Basis (Fin r) ℤ N.X := Module.finBasis ℤ N.X
  let bD : Module.Basis (Fin r) ℤ D.toPre.X := bX.map ν.eX.toIntLinearEquiv
  choose lf hlf using fun i => (GlobalTheory.MBLow.GtVec.main V D.toPre).1 (vB i) (hvB.1 i)
  choose tv htv using fun l : Fin r => GlobalTheory.T.exists_torusExtensionTangent_of_additiveMap V D.toPre ((Int.castAddHom V).comp (bD.coord l).toAddMonoidHom)
  have hco : ∀ (l : Fin r) (χ : D.toPre.X), ((Int.castAddHom V).comp (bD.coord l).toAddMonoidHom) χ = ((bD.repr χ l : ℤ) : V) :=
    fun l χ => by simp [Module.Basis.coord_apply]
  let gm₀ : Fin D.toPre.P.g ⊕ Fin r → GtPt D.toPre (epsR V) := Sum.elim lf tv
  have hgt : ∀ j, GtTan (gm₀ j) := fun j => by
    cases j with
    | inl i => exact (hlf i).1
    | inr l => exact (htv l).1
  let x : Fin D.toPre.P.g ⊕ Fin r → (epsR V ⟶ H) := fun j => (Φ _).symm (gm₀ j)
  have hx : ∀ j, Φ _ (x j) = gm₀ j := fun j => Equiv.apply_symm_apply _ _
  have hxB : ∀ (n : ℕ) (σ : Fin n ≃ Fin D.toPre.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := fun n σ =>
    GlobalTheory.T.lieBasis_torusExtension_of_lifts_and_duals V D.toPre H Φ hΦ r vB bD x hvB (fun j => by rw [hx]; exact hgt j) (fun i => by rw [hx]; exact (hlf i).2)
      (fun l => by
        rw [hx]
        refine ⟨(htv l).2.1, fun χ Z q z J hJ => ?_⟩
        rw [← hco]
        exact (htv l).2.2 χ Z q z J hJ) n σ
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GlobalTheory.MBLow.GtVec.isZero_of_isAdd (by simpa using ha T 1 1)
  let red : baseOver (Sp V) ⟶ epsR V := Over.homMk (redE V) GlobalTheory.MBLow.GtVec.red_comp
  have tanG : ∀ w : epsR V ⟶ H, GtTan (Φ _ w) ↔ red ≫ w = 1 := fun w =>
    ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((GlobalTheory.TorusModel.isPull_unique (hp _ _ red w) h).trans
      (GlobalTheory.MBLow.GtVec.isZero_unique ho (hz _))), fun h => ⟨Φ _ 1, hz _, h ▸ hp _ _ red w⟩⟩
  have tanH : ∀ w : epsR V ⟶ H, IsTangent w ↔ red ≫ w = 1 := fun w => by
    constructor
    · intro h
      apply Over.OverMorphism.ext
      refine h.trans ?_
      show _ = (toUnit _ ≫ η[H]).left
      simp
    · intro h
      have := congrArg (·.left) h
      refine this.trans ?_
      show (toUnit _ ≫ η[H]).left = _
      simp
  have : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  have : Module.Flat V (DualNumber V) := inferInstanceAs (Module.Flat V (V × V))
  have := isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal V) (DualNumber V)
  have := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber V
  have hT : GlobalTheory.AdicColimit.IsAdicColimit (IsLocalRing.maximalIdeal V) (epsR V) :=
    GlobalTheory.TorusModel.isAdicColimit_of_finite_flat (IsLocalRing.maximalIdeal V) (RingHom.id V) (by rwa [Ideal.map_id])
      (fun a ha => ⟨1, by rw [Ideal.map_id, pow_one]; exact ha⟩) (DualNumber V)
  let Rel : (epsR V ⟶ G) → (epsR V ⟶ H) → Prop := fun y w => TanRel U.toUnifPre y (Φ _ w)
  have h1 : Rel 1 1 := (tanRel_iff_isPointOf U.toUnifPre 1 (Φ _ 1)).2 (GlobalTheory.FormalPoint.isPointOf_one U.toUnifPre (hz _))
  have hmul : ∀ y y' w w', Rel y w → Rel y' w' → Rel (y * y') (w * w') := fun y y' w w' h h' =>
    GlobalTheory.MBLow.TanAdd.tanRel_mul U.toUnifPre y y' _ _ _ h h' (ha _ w w')
  have hsc : ∀ (c : V) (y : epsR V ⟶ G) (w : epsR V ⟶ H) (y' : epsR V ⟶ G) (w' : epsR V ⟶ H),
      y'.left = spMap (epsScaleR c) ≫ y.left → w'.left = spMap (epsScaleR c) ≫ w.left → Rel y w → Rel y' w' := by
    intro c y w y' w' e e' h
    obtain rfl : y' = GlobalTheory.SecJet.epsScale V c ≫ y := Over.OverMorphism.ext e
    obtain rfl : w' = GlobalTheory.SecJet.epsScale V c ≫ w := Over.OverMorphism.ext e'
    exact GlobalTheory.MBLow.TanAdd.tanRel_scale U.toUnifPre c y _ _ h (hp _ _ _ w)
  have hex : ∀ y, IsTangent y → ∃ w, IsTangent w ∧ Rel y w := fun y hy => by
    obtain ⟨gm, h₁, h₂, -⟩ := GlobalTheory.MBLow.TanLift.exists_tan U.toUnifPre y hy
    refine ⟨(Φ _).symm gm, (tanH _).2 ((tanG _).1 (by rw [Equiv.apply_symm_apply]; exact h₂)), ?_⟩
    show TanRel _ _ _
    rw [Equiv.apply_symm_apply]; exact h₁
  have huy : ∀ y y' w, IsTangent y → IsTangent y' → Rel y w → Rel y' w → y = y' := fun y y' w _ _ h h' =>
    ((tanRel_iff_isPointOf _ _ _).1 h).unique ((tanRel_iff_isPointOf _ _ _).1 h')
  have hux : ∀ y w w', Rel y w → Rel y w' → w = w' := fun y w w' h h' =>
    (GlobalTheory.TorusModel.existsUnique_lift U.toUnifPre hΦ hT y).unique ((tanRel_iff_isPointOf _ _ _).1 h)
      ((tanRel_iff_isPointOf _ _ _).1 h')
  choose yy hyy using fun j => (existsUnique_tangent_of_gtTan V hV D A G hS U (gm₀ j) (hgt j)).exists
  have hyB : ∀ (n : ℕ) (σ : Fin n ≃ Fin D.toPre.P.g ⊕ Fin r), IsLieBasis (fun k => yy (σ k)) := fun n σ =>
    GlobalTheory.T.isLieBasis_of_compatible_tangentRelation V G H Rel h1 hmul hsc hex huy hux n _ _ (hxB n σ) fun k => ⟨(hyy _).1, by
      show TanRel _ _ _
      rw [hx]; exact (hyy _).2⟩
  have hdim : D.toPre.P.g + r = A.g := GlobalTheory.T.lieBasis_card_eq_dim_uniformisation_dvr V D A G U.toUnifPre _ _ (hyB _ finSumFinEquiv.symm)
  let σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r := (finCongr hdim.symm).trans finSumFinEquiv.symm
  choose gmC hgmC using fun j => GlobalTheory.T.torusExtensionTangent_pullback_complexDualNumbers V D.toPre C N ν (gm₀ j) (hgt j)
  refine ⟨vB, r, bX, σ, fun k => yy (σ k), fun k => gm₀ (σ k), fun k => gmC (σ k), hyB _ σ,
    ⟨hvB, fun j => (hgmC _).2.1, fun i => ?_, fun l => ?_⟩, fun k => ⟨(hyy _).2, hgt _, (hgmC _).1⟩⟩
  · dsimp only
    rw [σ.apply_symm_apply (Sum.inl i), (hgmC _).1.1]
    show _ ≫ (lf i).b.left = _
    rw [(hlf i).2]
  · dsimp only
    rw [σ.apply_symm_apply (Sum.inr l)]
    refine ⟨(hgmC _).2.2.1 (htv l).2.1, fun χ => ?_⟩
    refine ((hgmC _).2.2.2 (((bD.repr (ν.eX χ) l : ℤ) : V)) (ν.eX χ) fun Z q z J hJ => ?_).trans ?_
    · have hv := (htv l).2.2 (ν.eX χ) Z q z J hJ
      rw [hco] at hv
      exact hv
    · have e : bD.repr (ν.eX χ) l = bX.repr χ l := by
        show (bX.map ν.eX.toIntLinearEquiv).repr (ν.eX χ) l = _
        rw [Module.Basis.map_repr]
        simp
      rw [e, map_intCast]

end GlobalTheory.MBLow.Adapt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyOfPullbackFiniteSurjective
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem exists_fam_of_pull : ∀ (S : Scheme.{0}) (A U U' : Over S) [GrpObj A] [IsLocallyNoetherian U.left],
    IsAbelianScheme A → ∀ (p : U' ⟶ U), IsFinite p.left → Surjective p.left → ∀ (N' : LB (A ⊗ U').left)
    (h : Fam A N') (c : Pic (A ⊗ U).left), GlobalTheory.CechPic.pull (A ◁ p).left c = cls N' h.isLB →
    ∃ M : LB (A ⊗ U).left, Fam A M ∧ Same A M N' p (𝟙 U') := by
  intro S A U U' _ _ hA p hfin hsurj N' h c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (u : Y ⟶ U'), evc hL a (u ≫ p) = evc h.isLB a u := by
    intro Y a u
    have e : lift a (u ≫ p) = lift a u ≫ (A ◁ p) := by ext <;> simp
    rw [evc, e, Over.comp_left, pull_comp, hc]
    rfl
  obtain ⟨M, hM, hMc⟩ := cls_surj (cls L hL - CechPic.pull (snd A U).left (evc hL (1 : U ⟶ A) (𝟙 U)))
  have form : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ U), evc hM a t = evc hL a t - evc hL (1 : Y ⟶ A) t := by
    intro Y a t
    rw [evc, hMc, map_sub, ← pull_comp, ← Over.comp_left, lift_snd, pull_evc, MonObj.comp_one, Category.comp_id]
    rfl
  have keyM : ∀ (Y : Over S) (a : Y ⟶ A) (u : Y ⟶ U'), evc hM a (u ≫ p) = evc h.isLB a u := by
    intro Y a u
    rw [form, key, key, h.add.evc_one h.isLB, sub_zero]
  refine ⟨M, ⟨hM, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A U hA M hM ((triv_ev_iff hM _ _).2 (by rw [form, sub_self])) ?_⟩, ?_⟩
  · intro K _ _ s t
    haveI := hfin
    haveI := hsurj
    obtain ⟨b, hb⟩ := exists_lift_pt p.left t.left
    let t' : Over.mk s ⟶ U' := Over.homMk b (by
      rw [← Over.w p, ← Category.assoc, hb, Over.w t])
    have ht : t = t' ≫ p := Over.OverMorphism.ext hb.symm
    rw [ht]
    refine (isAdditive_iff (pull_isLB hM _)).2 fun Y a a' y ↦ ?_
    have e : ∀ a₀ : Y ⟶ A, evc (pull_isLB hM _) a₀ y = evc h.isLB a₀ (y ≫ t') := fun a₀ ↦ by
      rw [evc_ev hM, lift_fst, lift_snd_assoc, ← Category.assoc, keyM]
    rw [e, e, e]
    exact (isAdditive_iff h.isLB).1 h.add _ _ _ _
  · rw [same_iff hM h.isLB, Category.comp_id]
    exact keyM _ _ _

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClassStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR A → ∃ g : Fn2 A, IsAdd (fv f) g := by
  first | exact @GlobalTheory.PtExt.exists_isAdd_of_mem_primDR | exact GlobalTheory.PtExt.exists_isAdd_of_mem_primDR | (intros; apply GlobalTheory.PtExt.exists_isAdd_of_mem_primDR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumFieldOfCoeffTendstoZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem exists_adic_sum_of_finsets {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {Ix : Type} (c : Ix → R) (S : ℕ → Finset Ix) (hmono : Monotone S)
    (hS : ∀ n i, i ∉ S n → c i ∈ I ^ n) :
    ∃ a : R, ∀ n, ∀ T : Finset Ix, S n ⊆ T → a - ∑ i ∈ T, c i ∈ I ^ n := by
  classical
  have key : ∀ n, ∀ T : Finset Ix, S n ⊆ T → ∑ i ∈ T, c i - ∑ i ∈ S n, c i ∈ I ^ n := by
    intro n T hT
    rw [← Finset.sum_sdiff hT, add_sub_cancel_right]
    exact Ideal.sum_mem _ fun i hi => hS n i (Finset.mem_sdiff.mp hi).2
  have hsm : ∀ n, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    simp
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance
    (f := fun n => ∑ i ∈ S n, c i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm, ← neg_mem_iff, neg_sub]
      exact key m _ (hmono hmn))
  refine ⟨a, fun n T hT => ?_⟩
  have h1 := ha n
  rw [SModEq.sub_mem, hsm] at h1
  have h2 := key n T hT
  have h3 := Ideal.add_mem _ h1 h2
  rw [← neg_mem_iff]
  convert h3 using 1
  ring

theorem exists_sumI_of_coeff {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {E : Type} [AddCommGroup E] [Module R E] {Jx : Type} [Fintype Jx] (g : Jx → E)
    {Ix : Type} (c : Ix → Jx → R) (h : ∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ I ^ n}.Finite) :
    ∃ s : E, GlobalTheory.UT.SumI I (fun i => ∑ k, c i k • g k) s := by
  classical
  have hmono : Monotone (fun n => (h n).toFinset) := by
    intro m n hmn i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun hk => hi fun k => Ideal.pow_le_pow_right hmn (hk k)
  have hS : ∀ k n i, i ∉ (h n).toFinset → c i k ∈ I ^ n := by
    intro k n i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi
    exact hi k
  choose a ha using fun k =>
    exists_adic_sum_of_finsets I (fun i => c i k) (fun n => (h n).toFinset) hmono (hS k)
  have hg : ∀ k, g k ∈ Submodule.span R (Set.range g) := fun k =>
    Submodule.subset_span ⟨k, rfl⟩
  refine ⟨∑ k, a k • g k, Submodule.span R (Set.range g),
    Submodule.fg_span (Set.finite_range g),
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k),
    fun i => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k),
    fun n => ⟨(h n).toFinset, fun T hT => ?_⟩⟩
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← Finset.sum_smul, ← sub_smul]
  exact Submodule.smul_mem_smul (ha k n T hT) (hg k)

theorem exists_sumF_of_coeff : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Jx : Type) [Fintype Jx] (g : Jx → F) (Ix : Type) (c : Ix → Jx → R), (∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ maximalIdeal R ^ n}.Finite) → ∃ s : F, GlobalTheory.UT.SumF (maximalIdeal R) F (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k) s := by
  intro R _ _ _ _ hc F _ _ Jx _ g Ix c h
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨s, hs⟩ := exists_sumI_of_coeff (maximalIdeal R) g c h
  refine ⟨s, ?_⟩
  have e : (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k)
      = fun i => ∑ k, c i k • g k := by
    funext i
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.smul_def]
    rfl
  rw [e]
  exact hs

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleProjectiveThetaModelOverModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.SegreModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem hasDiv_left {A B : Type} {a : A → Ω} {b : B → Ω} (h : M.HasDiv fun p : A × B => a p.1 * b p.2) :
    M.HasDiv a := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  refine ⟨i.1, left_ne_zero_of_mul h0, fun j => ?_⟩
  have := hi (j, i.2)
  rwa [mul_div_mul_right _ _ (right_ne_zero_of_mul h0)] at this

theorem hasDiv_right {A B : Type} {a : A → Ω} {b : B → Ω} (h : M.HasDiv fun p : A × B => a p.1 * b p.2) :
    M.HasDiv b := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  refine ⟨i.2, right_ne_zero_of_mul h0, fun j => ?_⟩
  have := hi (i.1, j)
  rwa [mul_div_mul_left _ _ (left_ne_zero_of_mul h0)] at this

theorem hasDiv_of_prod {K : Type} [Fintype K] {J : K → Type} {t : ∀ k, J k → Ω}
    (h : M.HasDiv fun i : ∀ k, J k => ∏ k, t k (i k)) (k : K) : M.HasDiv (t k) := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  have hne := Finset.prod_ne_zero_iff.1 h0
  refine ⟨i k, hne k (Finset.mem_univ _), fun j => ?_⟩
  have := hi (Function.update i k j)
  have e : ∏ l ∈ Finset.univ.erase k, t l (Function.update i k j l) = ∏ l ∈ Finset.univ.erase k, t l (i l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h1 : ∏ l ∈ Finset.univ.erase k, t l (i l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => hne l (Finset.mem_univ _)
  simp only at this
  rwa [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun l => t l (i l)) (Finset.mem_univ k),
    e, Function.update_self, mul_div_mul_right _ _ h1] at this

theorem subfield_eq_top {J : Type} {c : J → Ω} (h : M.IsCl c) (F : Subfield Ω)
    (ho : Set.range (algebraMap o Ω) ⊆ F) (hc : ∀ i j, c i ≠ 0 → c j / c i ∈ F) : F = ⊤ := by
  obtain ⟨i, hi, -⟩ := h.1 (genericPoint M.Z)
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi
  have hne : (U : Set M.Z).Nonempty := ⟨genericPoint M.Z, hD ▸ RatModel.div_genericPoint hi⟩
  have hle : ∀ x ∈ M.ringOn U, x ∈ F := by
    intro x hx
    rw [hR] at hx
    induction hx using Algebra.adjoin_induction with
    | mem _ h' => obtain ⟨j, rfl⟩ := h'; exact hc i j hi
    | algebraMap r => exact ho ⟨r, rfl⟩
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, -, rfl⟩ := RatModel.exists_eq_div hU hne x
  exact div_mem (hle _ ((RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
    (hle _ ((RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

theorem finite_of_eq_top (F : Subfield Ω) (h : F = ⊤) : Module.Finite F Ω :=
  Module.Finite.of_surjective (Algebra.linearMap F Ω) fun x => ⟨⟨x, h ▸ trivial⟩, rfl⟩

end GlobalTheory.Poinc.SegreModel

theorem GlobalTheory.Poinc.exists_admissible_projective_theta_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ∀ M₁ : RatModel o Ω, IsProjOver M₁.s → ∀ (K : Type) [Finite K] (Jk : K → Type) [∀ k, Finite (Jk k)] (t : ∀ k, Jk k → Ω), (∀ k j, t k j ≠ 0) → ∃ (Y : RatModel o Ω) (πY : Y.Z ⟶ M₁.Z) (U₀ : Y.Z.Opens) (EE : Y.Lat S.J) (_ : ZHOut ρ Y U₀ EE), M₁.IsHom Y (AlgHom.id o Ω) πY ∧ IsProper πY ∧ S.admitted Y U₀ ∧ S.IsEE Y U₀ EE ∧ ∀ k, Nonempty (Jk k) → Y.HasDiv (t k) := by
  intro o Ω _ _ _ _ S ρ hBig M₁ hM₁ K _ Jk _ t ht
  obtain ⟨n, c, hc⟩ := RatModel.exists_isCl_of_isProjOver hM₁
  have hN2 := S.N_ge
  haveI hN0 : NeZero S.N := ⟨by omega⟩
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by omega)⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI : Finite (AddSubgroup S.Gam) :=
    Finite.of_injective (fun H : AddSubgroup S.Gam => (H : Set S.Gam)) SetLike.coe_injective
  haveI : ∀ T₀ : AddSubgroup S.Gam, Finite (T₀ →+ ZMod S.N) := fun T₀ =>
    Finite.of_injective (fun f : T₀ →+ ZMod S.N => (f : T₀ → ZMod S.N)) DFunLike.coe_injective
  let K₁ := {k : K // Nonempty (Jk k)}
  let K₂ := {d : Σ T : AddSubgroup S.Gam, (T →+ ZMod S.N) // S.FF d.1 d.2 ≠ 0}
  letI : Fintype K₁ := Fintype.ofFinite _
  letI : Fintype K₂ := Fintype.ofFinite _
  let J₂ : K₂ → Type := fun d => S.J × (d.1.1 → ZMod ((S.r * S.N) ^ 2))
  let B := (∀ k : K₁, Jk k.1) × (∀ d : K₂, J₂ d)
  let b : B → Ω := fun p => (∏ k : K₁, t k.1 (p.1 k)) * ∏ d : K₂, S.FF d.1.1 d.1.2 (p.2 d)
  haveI : Finite B := inferInstance
  letI : Fintype (Fin (n + 1) × B) := Fintype.ofFinite _
  obtain ⟨p₀, hp₀⟩ : ∃ p, b p ≠ 0 := by
    choose κ hκ using fun d : K₂ => Function.ne_iff.1 d.2
    exact ⟨(fun k => k.2.some, κ), mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => ht _ _)
      (Finset.prod_ne_zero_iff.2 fun d _ => hκ d)⟩
  obtain ⟨i₀, hi₀, -⟩ := hc.1 (genericPoint M₁.Z)
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨Y, U₀, EE, hO, hD, hE, ⟨FinalForm⟩⟩ := GlobalTheory.zhSt_holds o Ω S ρ hBig (Fin (n + 1) × B) (fun p => c p.1 * b p.2)
    ⟨(i₀, p₀), mul_ne_zero hi₀ hp₀⟩ (by
      refine SegreModel.finite_of_eq_top _ (SegreModel.subfield_eq_top hc _
        (Set.subset_union_left.trans Subfield.subset_closure) fun i j _ =>
        Subfield.subset_closure (Or.inr ⟨(x₀, i, p₀), (x₀, j, p₀), ?_⟩))
      rw [mul_div_mul_left _ _ hx₀, mul_div_mul_right _ _ hp₀])
  have hb : Y.HasDiv b := SegreModel.hasDiv_right hD
  have h1 := SegreModel.hasDiv_left (a := fun q : ∀ k : K₁, Jk k.1 => ∏ k : K₁, t k.1 (q k))
    (b := fun q : ∀ d : K₂, J₂ d => ∏ d : K₂, S.FF d.1.1 d.1.2 (q d)) hb
  have h2 := SegreModel.hasDiv_right (a := fun q : ∀ k : K₁, Jk k.1 => ∏ k : K₁, t k.1 (q k))
    (b := fun q : ∀ d : K₂, J₂ d => ∏ d : K₂, S.FF d.1.1 d.1.2 (q d)) hb
  obtain ⟨π, hπ⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id o Ω) (SegreModel.hasDiv_left hD)
  refine ⟨Y, π, U₀, EE, FinalForm, hπ, ?_, ⟨hO, fun T c' _ h => ?_⟩, hE, fun k hk => ?_⟩
  · haveI := M₁.sep
    haveI : IsProper (π ≫ M₁.s) := by
      rw [hπ.inducedModelMorphism_comp_structureMap]
      obtain ⟨m, j, hj, hs⟩ := hO.proj
      rw [← hs]
      have := isProper_str o m
      infer_instance
    exact IsProper.of_comp π M₁.s
  · exact SegreModel.hasDiv_of_prod (t := fun d : K₂ => S.FF d.1.1 d.1.2) h2 ⟨⟨T, c'⟩, h⟩
  · exact SegreModel.hasDiv_of_prod (t := fun k : K₁ => t k.1) h1 ⟨k, hk⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartLiftToModuliSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineChart_lift_to_moduli_scheme : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (w : X₁.M.Z), X₁.π w ∈ Set.range i → ∃ (U : X₁.M.Z.Opens) (u : Sp (X₁.M.ringOn U) ⟶ F.X), IsAffineOpen U ∧ w ∈ U ∧ (∀ w' ∈ U, X₁.π w' ∈ Set.range i) ∧ spMap (X₁.M.ringOn U).val.toRingHom ≫ u = spMap X₁.S.R.val.toRingHom ≫ X₁.u := by
  first | exact @GlobalTheory.Poinc.ChartAt.exists_affine_chart_lift | exact GlobalTheory.Poinc.ChartAt.exists_affine_chart_lift | (intros; apply GlobalTheory.Poinc.ChartAt.exists_affine_chart_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfLineBundleIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_appellHumbertFrame_of_lineBundleIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L L' : LB A.left) (u' : HolUnif A L' g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), L.IsLB → L'.IsLB → LBIso L L' → GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → ∃ (u : HolUnif A L g) (χ : u.Λ → ℂ), u.ex = u'.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  first | exact @GlobalTheory.TransportFrame.exists_holUnif_isFactorAH_of_lbIso | exact GlobalTheory.TransportFrame.exists_holUnif_isFactorAH_of_lbIso | (intros; apply GlobalTheory.TransportFrame.exists_holUnif_isFactorAH_of_lbIso; all_goals assumption)
end

