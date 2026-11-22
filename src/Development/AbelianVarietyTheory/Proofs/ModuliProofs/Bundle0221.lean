import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGeneric
section
noncomputable section

namespace GlobalTheory.FinitePartGeneric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

theorem exists_normal_factor (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (A : Type) [CommRing A]
    [Algebra R A] [Module.Finite R A] (ψ : A →+* F)
    (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap (FractionRing R) F (algebraMap R _ r)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : Algebra (FractionRing R') F)
      (a : A →+* R'), AdmBase R' (maximalIdeal R') ∧
      (maximalIdeal R).map (a.comp (algebraMap R A)) ≤ maximalIdeal R' ∧
      ∀ y, algebraMap (FractionRing R') F (algebraMap R' _ (a y)) = ψ y := by
  obtain ⟨h₁, -, h₃, h₄⟩ := hR
  letI : Algebra R F := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).toAlgebra
  have : IsScalarTower R (FractionRing R) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ' : A →ₐ[R] F := { ψ with commutes' := hψ }
  have hi : ∀ y, IsIntegral R (ψ y) := fun y => (Algebra.IsIntegral.isIntegral (R := R) y).map ψ'
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := A)
  let L := IntermediateField.adjoin (FractionRing R) (ψ '' s)
  have : Finite (ψ '' s) := (s.finite_toSet.image ψ).to_subtype
  have : FiniteDimensional (FractionRing R) L :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨y, -, rfl⟩; exact (hi y).tower_top)
  have hm : ∀ y, ψ y ∈ L := fun y => by
    have hy : y ∈ Submodule.span R (s : Set A) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy => rw [Algebra.smul_def, map_mul, hψ]; exact mul_mem (L.algebraMap_mem _) hy
  obtain ⟨f₁, f₂, f₃, f₄, -⟩ := integralClosure_finite_local_of_isAdicComplete R h₄ L
  have : IsScalarTower R L F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let j : integralClosure R L →+* F := (algebraMap L F).comp (algebraMap _ L)
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  let a : A →+* integralClosure R L := (ψ.codRestrict L hm).codRestrict (integralClosure R L) fun y =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R L F) Subtype.val_injective).1 (hi y)
  have ha : a.comp (algebraMap R A) = algebraMap R _ := RingHom.ext fun r => hj (hψ r)
  refine ⟨integralClosure R L, inferInstance, inferInstance, f₂, (IsFractionRing.lift (g := j) hj).toAlgebra, a,
    ⟨f₃, inferInstance, f₄, CompleteFiniteExtension.isAdicComplete_of_finite_local R _⟩, ?_,
    fun y => IsFractionRing.lift_algebraMap (g := j) hj _⟩
  rw [ha]
  exact ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := R) _ _ inferInstance

theorem exists_normal_point (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : Over (Sp R))
    [IsFinite N.hom] (x : Sp F ⟶ N.left) (hx : x ≫ N.hom = jFK (R := R) F ≫ jK R) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : Algebra (FractionRing R') F)
      (φ : R →+* R') (ξ : Sp R' ⟶ N.left), AdmBase R' (maximalIdeal R') ∧
      (maximalIdeal R).map φ ≤ maximalIdeal R' ∧ ArcPull.Compat φ F ∧ ξ ≫ N.hom = spMap φ ∧
      (jFK (R := R') F ≫ jK R') ≫ ξ = x := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ N.left.isoSpec.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have e : φ ≫ ψ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hx])
  have e' : ∀ r, ψ.hom (φ.hom r) = algebraMap (FractionRing R) F (algebraMap R _ r) := fun r =>
    congrArg (fun q => q.hom r) e
  obtain ⟨R', i₁, i₂, i₃, i₄, a, h₁, h₂, h₃⟩ := exists_normal_factor R hR F Γ(N.left, ⊤) ψ.hom e'
  refine ⟨R', i₁, i₂, i₃, i₄, a.comp φ.hom, Spec.map (CommRingCat.ofHom a) ≫ N.left.isoSpec.inv, h₁, h₂,
    fun r => (e' r).symm.trans (h₃ _).symm, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]; rfl
  · rw [← Category.assoc, Iso.comp_inv_eq, ← hψ, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext h₃))

section Transport

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLin GlobalTheory.FormalPoint
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}

theorem isPointOf_thru {I : Ideal R} {I' : Ideal R'} {D : DegData R I} {D' : DegData R' I'}
    {hD : IsPullDeg φ D.toPre D'.toPre} {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} {U : Unif I D A G} {U' : Unif I' D' A' G'}
    (hU : IsPullUnif φ hD bc U U') {T : Over (Sp R)} {T' : Over (Sp R')} {h : T'.left ⟶ T.left}
    {g₀ : GtPt D.toPre T} {g : GtPt D'.toPre T'} (H : Thru hD.w hD.xe h g₀ g) {x₀ : T ⟶ G} {x : T' ⟶ G'}
    (hx : x.left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = h ≫ x₀.left)
    (h₀ : IsPointOf U.toUnifPre g₀ x₀) : IsPointOf U'.toUnifPre g x := by
  intro e Z r y hy
  obtain ⟨wL, -, he, -, HU⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨k, hf, hpt, -⟩ := HU e
  have gp := pull_grp hD
  obtain ⟨cb, cv⟩ := (hasCoords_iff _ _ _ _ _).1 (h₀ e Z (r ≫ h) (y ≫ k) (by
    rw [Category.assoc, hf, ← Category.assoc, hy, Category.assoc, hx, Category.assoc]))
  have hy' : y ≫ ((Over.map (thick R' I' e)).obj (thickObj R' I' e G')).hom = r ≫ T'.hom := by
    rw [← Over.w (fstG I' e G'), ← Category.assoc, hy, Category.assoc, Over.w]
  let y' : Over.mk (r ≫ T'.hom) ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G') := Over.homMk y hy'
  let r' : Over.mk (r ≫ T'.hom) ⟶ T' := Over.homMk r rfl
  have hb : y ≫ (U'.gt e).pG.left = r ≫ g.b.left := gp.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (y ≫ ·) hpt.1).trans ((Category.assoc _ _ _).symm.trans (cb.trans
      ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) ((H 0).1 2).symm).trans (Category.assoc _ _ _).symm))))))
    (by rw [Category.assoc, Category.assoc, Over.w, Over.w]; exact hy')
  refine (hasCoords_iff _ _ _ _ _).2 ⟨hb, fun χ z J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.toPre.P.isLB z
  have v := ConstFam.pmaps_val (hpt.2 χ).1 (hpt.2 χ).2 y hJ hJ'
  have eP : ∏ i, ConstFam.wVal hD.w z J J' (y ≫ D'.toPre.Oφ (U'.gt e).pG χ i) ^ Oinvε i =
      ∏ i, ConstFam.wVal hD.w z J J' (r ≫ DegPre.gtφT D'.toPre T' g.b χ i) ^ DegPre.gtε i :=
    Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w z J J' q ^ DegPre.gtε i)
      (comp_Oφ y' r' _ _ (Over.OverMorphism.ext hb) χ i)
  rw [eP] at v
  exact mul_left_cancel (v.symm.trans ((cv _ z J hJ).trans ((H χ).2 _ r z J J' hJ hJ')))

theorem isPullGtF_thru {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {T : Over (Sp R)} {T' : Over (Sp R')}
    {h : T'.left ⟶ T.left} {g₀ : GtPt D T} {g : GtPt D' T'} (H : Thru hD.w hD.xe h g₀ g) {F : Type} [Field F]
    [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] {σ : Sp F ⟶ T'.left} {q : GtPtF D F}
    {q' : GtPtF D' F} (hq : GtPt.IsPullF F (σ ≫ h) g₀ q) (hq' : GtPt.IsPullF F σ g q') : IsPullGtF φ hD F q q' := by
  have m := FieldRestrictionTest.maps_eq hq
  have m' := FieldRestrictionTest.maps_eq hq'
  have hψ : ∀ χ i, DegPre.gtφ D' F q'.b χ i ≫ proj hD = 𝟙 _ ≫ DegPre.gtφ D F q.b (hD.xe χ) i := fun χ i => by
    rw [m, m', Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) ((H χ).1 i)).trans (Category.assoc _ _ _).symm)
  refine ⟨(hψ 0 2).trans (Category.id_comp _), fun χ => ⟨hψ χ, maps_of_good ((isGen_iff _).1 hD.w_gen) D.P.isLB
    D'.P.isLB _ (q'.isGen χ) _ (q.isGen _) (hψ χ) fun y J J' hJ hJ' => ?_⟩⟩
  have a := (val_corr hJ (hq.2 (hD.xe χ)) (𝟙 _)).trans (val_pull hJ _ _ _)
  have a' := (val_corr hJ' (hq'.2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)
  rw [Category.id_comp] at a a'
  refine a.trans (((H χ).2 _ σ y J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ a'.symm))
  exact Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w y J J' q ^ DegPre.gtε i) (m' χ i).symm

end Transport

theorem main : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinitePart P.U.toUnifPre k N g₀ x₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F N x → ∀ q : QkPt P.D.toPre F k, q.y = 0 → GtPt.IsPullF F x g₀ q.g → IsImage P F k q (x ≫ x₀.left) := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k hk N g₀ x₀ hN F _ _ _ x hx q hq hg
  have hL := firstFiveLaws
  have := hN.finite
  obtain ⟨R', _, _, _, _, φ, ξ, hR', hI, hF, hξ, rfl⟩ := exists_normal_point R hR F N x hx
  have hφ : Function.Injective φ := fun a b e => IsFractionRing.injective R (FractionRing R)
    ((algebraMap (FractionRing R) F).injective (by rw [hF a, hF b, e]))
  obtain ⟨D', hD, A', U', hU⟩ := UT.EndBaseChange.exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange
    hL.2.2.2.2.psiOnExists hR hR' φ hφ hI t.semi P.U
  have hh : ξ ≫ N.hom = (𝟙_ (Over (Sp R'))).hom ≫ spMap φ := hξ.trans (Category.id_comp _).symm
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp R'))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh g₀
  let x₁ : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (specOf φ)).obj t.G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp R'))).hom (by rw [Category.assoc, Over.w]; exact hh))
      (pullback.lift_snd _ _ _)
  have e₁ : x₁.left ≫ pullback.fst t.G.hom (specOf φ) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ (Iso.refl ((Over.pullback (specOf φ)).obj t.G)).hom.left ≫ pullback.fst t.G.hom (specOf φ) =
      ξ ≫ x₀.left := (congrArg (x₁.left ≫ ·) (Category.id_comp _)).trans e₁
  have gG := isGrpPullback_pullback t.G (spMap φ)
  have hk₁ : x₁ ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ⟶ N := Over.homMk ξ hh
    have e : pushHom gG _ x₁ = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, hN.g_tors, MonObj.comp_one])
  have hp := isPointOf_thru hU hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hN.formal)
  obtain ⟨g', hg'⟩ := FieldRestrictionTest.exists_isPullF (toUnit (TF (R := R') F)) gp
  let y : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj t.G :=
    Over.homMk (pullback.lift (((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left) (jFK (R := R) F)
      (by rw [Category.assoc, Over.w]; exact hx)) (pullback.lift_snd _ _ _)
  have hy : (y ≫ P.U.gen.hom).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      ((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine ⟨_, hy, FiniteTorsionExt.main hL.1 R R' _ _ hR hR' φ P.D P.A t.G P.U _ (Iso.refl _)
    (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hU (maximalIdeal.isMaximal R').ne_top F hF k hk x₁ gp hk₁
    (fun e => ?_) q g' _ hq (isPullGtF_thru hgp hg hg') hg' ?_⟩
  · let xe : Over.mk (thick R' (maximalIdeal R') e) ⟶ (Over.map (thick R' (maximalIdeal R') e)).obj
        (thickObj R' (maximalIdeal R') e ((Over.pullback (specOf φ)).obj t.G)) :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick R' (maximalIdeal R') e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick R' (maximalIdeal R') e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩
  · rw [hy, Over.comp_left, Category.assoc (toUnit (TF (R := R') F)).left, e₂]
    exact Category.assoc _ _ _

end GlobalTheory.FinitePartGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KeyFormulaIffClauses
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence GlobalTheory.IndefiniteRowSideFullHecke.CubicWedgeNormPeriods GlobalTheory.KeyInputCompare

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyFormulaCompare

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def Same (u : HolUnif A L g) (F : Unif A L g) : Prop :=
  F.exp = u.ex ∧ ∀ i z h, F.fr i z h = u.fr i z

def toEpsPt (v : epsR ℂ ⟶ A) : EpsPt A := Over.homMk v.left ((Over.w v).trans (Category.comp_id _).symm)

def ofEpsPt (v : EpsPt A) : epsR ℂ ⟶ A := Over.homMk v.left ((Over.w v).trans (Category.comp_id _))

namespace Same

variable {u : HolUnif A L g} {F : Unif A L g} (h : Same u F)
include h

end Same

end Unif

section Analytic

end Analytic

section Principal

theorem tangent_bijective (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) :
    (∀ v, Geo.Tor.IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, Geo.Tor.IsTangent v ∧ u.IsDiff w v := by
  obtain ⟨u₀, H₀, χ₀, E₀, -, -, hv, hw, -⟩ := thetaUnifAV_closed x.P x.rig x.rig_gen
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u₀ hv hw u.ex
    u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u₀ F hF)
  have hd : ∀ w v, u.IsDiff w v ↔ u₀.IsDiff (e w) v :=
    UnifCompare.isDiff_iff u u₀ e.toContinuousLinearEquiv hF
  refine ⟨fun v hv' => ?_, fun w => ?_⟩
  · obtain ⟨w, h1, h2⟩ := hv v hv'
    refine ⟨e.symm w, (hd _ _).2 (by rwa [e.apply_symm_apply]), fun y hy => ?_⟩
    rw [← h2 _ ((hd _ _).1 hy), e.symm_apply_apply]
  · simp only [hd]
    exact hw (e w)

theorem det_ne_zero (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ)
    (hW : ∀ i, u.IsDiff (W i) (x.v i)) : W.det ≠ 0 := by
  obtain ⟨h₁, h₂⟩ := tangent_bijective x u
  refine ((Matrix.isUnit_iff_isUnit_det W).1 (Matrix.vecMul_surjective_iff_isUnit.1 fun w => ?_)).ne_zero
  obtain ⟨v, hv, hd⟩ := (h₂ w).exists
  obtain ⟨c, hc⟩ := (x.basis.2 v hv).exists
  exact ⟨c, (Matrix.vecMul_eq_sum c W).trans ((h₁ v hv).unique
    (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u W x.v c v x.basis.1 hW hc) hd)⟩

end Principal

section Clauses

abbrev RuleIn : Type 1 := ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ

def ruleEquiv : RuleIn ≃ Rule where
  toFun κ := fun K _ _ y => κ K ((keyInEquiv K).symm y)
  invFun ka := fun K _ _ x => ka K (keyInEquiv K x)
  left_inv _ := rfl
  right_inv _ := rfl

def HomIn (κ : RuleIn) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
    (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
    (∀ i, IsLieComb (M i) v (v' i)) →
    a ^ 8 * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ 4 * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩

def FunIn (κ : RuleIn) : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') (x : KeyIn K) (x' : KeyIn K'),
    KeyPB x' x f → (κ K' x' : K') = f (κ K x)

def IntIn (κ : RuleIn) : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), KeyPB xK x (algebraMap R K) →
    ∃ u : Rˣ, (κ K xK : K) = algebraMap R K u ∧
      ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
        (κ k xk : k) = r u

def ThetaIn (κ : RuleIn) : Prop :=
  ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) →
    (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    u.IsRig x.rig → u.IsFn x.th (thetaChar τ a b) →
    (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) → κ ℂ x = 1

def NormIn (κ : RuleIn) : Prop :=
  ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
    u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
    IsAddFundamentalDomain u.Λ Fd volume →
    nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
    nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
    ‖(κ ℂ x : ℂ)‖ * nth ^ 4 * nη ^ 2 = (2 * Real.pi) ^ (2 * x.P.g)

variable (κ : RuleIn)

end Clauses

end GlobalTheory.KeyFormulaCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalDescendedBundleNoetherian
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.DescentFamily

open GlobalTheory.CechPic

theorem card_ker_pullback {S S' : Scheme.{0}} (t : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) :
    Nat.card {x : 𝟙_ (Over S') ⟶ (Over.pullback t).obj A // x ≫ (Over.pullback t).map ψ = 1} =
      Nat.card {x : Over.mk ((𝟙_ (Over S')).hom ≫ t) ⟶ A // x ≫ ψ = 1} := by
  have hA := isGrpPullback_pullback A t
  have hB := isGrpPullback_pullback B t
  have inj : ∀ {G : Over S} [GrpObj G] (h : IsGrpPullback ((Over.pullback t).obj G) G t (pullback.fst G.hom t)),
      Function.Injective (pushHom h (𝟙_ (Over S'))) := fun h x y e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w, Over.w]))
  have surj : Function.Surjective (pushHom hA (𝟙_ (Over S'))) := fun x =>
    ⟨Over.homMk (hA.1.lift x.left (𝟙_ (Over S')).hom (Over.w x)) (hA.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hA.1.lift_fst _ _ _)⟩
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ ⟨inj hA, surj⟩) fun x => ?_)
  have e : pushHom hB (𝟙_ (Over S')) (x ≫ (Over.pullback t).map ψ) = pushHom hA (𝟙_ (Over S')) x ≫ ψ := by
    refine Over.OverMorphism.ext ?_
    show (x.left ≫ ((Over.pullback t).map ψ).left) ≫ pullback.fst B.hom t = (x.left ≫ pullback.fst A.hom t) ≫ ψ.left
    rw [Category.assoc, Category.assoc]
    exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _)
  exact (map_eq_one_iff _ (inj hB)).symm.trans (Eq.congr_left e)

theorem kTriv_fibre {S : Scheme.{0}} (P : Out.PolAV S) {n : ℕ} (B : Over S) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left)
    (hn : 0 < n) (hB : IsAbelianScheme B) (hM : M.IsLB) [IsMonHom ψ] [IsFinite ψ.left] [Etale ψ.left]
    [Surjective ψ.left] (hiso : LBIso (lbPow P.L n) (M.pull ψ.left)) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (t : Sp k ⟶ S) (hc : Nat.card {x : Over.mk (𝟙 _ ≫ t) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) :
    Out.KTriv ((Over.pullback t).obj B) (M.pull (pullback.fst B.hom t)) := by
  have hw : ((Over.pullback t).map ψ).left ≫ pullback.fst B.hom t = pullback.fst P.A.hom t ≫ ψ.left :=
    pullback.lift_fst _ _ _
  have hp : IsPullback (pullback.fst P.A.hom t) ((Over.pullback t).map ψ).left ψ.left (pullback.fst B.hom t) := by
    refine IsPullback.of_bot ?_ hw.symm (IsPullback.of_hasPullback B.hom t)
    have e : ((Over.pullback t).map ψ).left ≫ pullback.snd B.hom t = pullback.snd P.A.hom t :=
      Over.w ((Over.pullback t).map ψ)
    rw [e, Over.w ψ]
    exact IsPullback.of_hasPullback _ _
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom t)
  have hM' := pull_isLB hM (pullback.fst B.hom t)
  have h₁ : (lbPow (P.L.pull (pullback.fst P.A.hom t)) n).IsLB := LB.isLB_linComb hL' _ _
  have h₂ := pull_isLB hM' ((Over.pullback t).map ψ).left
  have h₀ := (cls_eq_iff (LB.isLB_linComb P.isLB _ _) (pull_isLB hM _)).2 hiso
  rw [cls_lbPow P.isLB, cls_pull hM] at h₀
  have he : cls _ h₁ = cls _ h₂ := by
    rw [cls_lbPow hL', cls_pull hM', cls_pull P.isLB, cls_pull hM, ← pull_comp, hw, pull_comp, ← h₀, map_nsmul]
  have hmon : IsMonHom ((Over.pullback t).map ψ) := inferInstance
  refine kTriv_of_descent firstFiveLaws.1 k (StrictPull.polPull P t) n _ ((Over.pullback t).map ψ) _ hn
    (PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B t)) hM' hmon
    (MorphismProperty.of_isPullback (P := @IsFinite) hp inferInstance)
    (MorphismProperty.of_isPullback (P := @Etale) hp inferInstance)
    (MorphismProperty.of_isPullback (P := @Surjective) hp inferInstance)
    ((card_ker_pullback t ψ).trans hc) ?_
  refine (cls_eq_iff (LB.isLB_linComb h₁ _ _) (LB.isLB_linComb h₂ _ _)).1 ?_
  refine (cls_cube_two (G := (Over.pullback t).obj P.A) h₁ _ _ _).trans
    (Eq.trans ?_ (cls_cube_two (G := (Over.pullback t).obj P.A) h₂ _ _ _).symm)
  exact congrArg (fun c => lam (G := (Over.pullback t).obj P.A) c _ _) he

end GlobalTheory.DescentFamily

namespace GlobalTheory

open GlobalTheory.CechPic

theorem relAmple_kTriv_of_descent_family : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R), Nat.card {x : Over.mk t ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) → LBIso (lbPow P.L n) (M.pull ψ.left) → Out.RelAmple B M ∧ Out.KTriv B M := by
  intro R _ _ P n B _ ψ M hu hn hB hM hψ hf he hs hc hiso
  have hA := P.isAb
  have hn' : (lbPow P.L n).IsLB := LB.isLB_linComb P.isLB _ _
  have hid : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := by rw [Over.id_left]; infer_instance
  have a₁ : Out.RelAmple P.A (lbPow P.L n) :=
    (relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L n hn hA hA P.isLB hid).2.1.2 P.ample
  have a₂ : Out.RelAmple P.A (M.pull ψ.left) :=
    (relAmple_finite_pow_iso _ P.A P.A (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hM _) hiso a₁
  have a₃ : Out.RelAmple B M :=
    (relAmple_finite_pow_iso _ P.A B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs a₂
  refine ⟨a₃, ?_⟩
  have loc : ∀ q : PrimeSpectrum R, ∃ f : R, f ∉ q.asIdeal ∧
      Out.KTriv ((Over.pullback (spMap (algebraMap R (Localization.Away f)))).obj B)
        (M.pull (pullback.fst B.hom (spMap (algebraMap R (Localization.Away f))))) := by
    intro q
    let k := AlgebraicClosure q.asIdeal.ResidueField
    let x : R →+* k := (algebraMap q.asIdeal.ResidueField k).comp (algebraMap R q.asIdeal.ResidueField)
    have : CharZero k := charZero_of_inj_zero fun m hm => by
      by_contra h
      have := (hu m (Nat.pos_of_ne_zero h)).map x
      rw [map_natCast, hm] at this
      exact not_isUnit_zero this
    obtain ⟨f, hf, H⟩ := kTriv_away_of_kTriv_fibre firstFiveLaws.1.globalFns R B M k x hB hM a₃
      (DescentFamily.kTriv_fibre P B ψ M hn hB hM hiso k (spMap x) (hc k _))
    refine ⟨f, fun h => hf ?_, H⟩
    show algebraMap q.asIdeal.ResidueField k (algebraMap R q.asIdeal.ResidueField f) = 0
    rw [Ideal.algebraMap_residueField_eq_zero.2 h, map_zero]
  choose f hf H using loc
  let j : ∀ q, Sp (Localization.Away (f q)) ⟶ Sp R := fun q => spMap (algebraMap R (Localization.Away (f q)))
  have hj : ∀ q, IsOpenImmersion (j q) := fun q => IsOpenImmersion.of_isLocalization (f q)
  let G := fun q => (Over.pullback (j q).isoOpensRange.inv).obj ((Over.pullback (j q)).obj B)
  have gp : ∀ q, IsGrpPullback (G q) ((Over.pullback (j q)).obj B) (j q).isoOpensRange.inv (pullback.fst _ _) :=
    fun q => isGrpPullback_pullback _ _
  have hM₁ := fun q => pull_isLB hM (pullback.fst B.hom (j q))
  have hB₁ := fun q => PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B (j q))
  have key := fun q => pol_pull _ _ _ (G q) _ _ _ _ (hM₁ q) (pull_isLB (hM₁ q) _) (hB₁ q) (gp q)
    ((cls_eq_iff (pull_isLB (hM₁ q) _) (pull_isLB (hM₁ q) _)).1 rfl)
  refine CoverGlue.kTriv_of_cover (Sp R) (PrimeSpectrum R) (fun q => (j q).opensRange) B G
    (fun q => pullback.fst _ (j q).isoOpensRange.inv ≫ pullback.fst B.hom (j q)) ?_
    (fun q => ((gp q).comp (isGrpPullback_pullback B (j q))).congr (Scheme.Hom.isoOpensRange_inv_comp _) rfl)
    M _ hM (fun q => pull_isLB (hM₁ q) _) (fun q => ?_) hB (fun q => (key q).1) (fun q => (key q).2.2 (H q))
  · refine top_le_iff.1 fun q _ => TopologicalSpace.Opens.mem_iSup.2 ⟨q, ?_⟩
    have : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (f q)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (f q)) (f q)]
      exact hf q
    exact this
  · rw [← cls_eq_iff (pull_isLB (hM₁ q) _) (pull_isLB hM _), cls_pull (hM₁ q), cls_pull hM, cls_pull hM, pull_comp]

end GlobalTheory
end
end

