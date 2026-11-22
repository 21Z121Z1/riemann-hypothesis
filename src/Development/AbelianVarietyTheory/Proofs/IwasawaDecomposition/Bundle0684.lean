import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalHolomorphicLatticeBasisConvex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBundleSquareSectionTransportExpansion
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqTransport

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_transport_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen → ∀ (σ : H0 U.LG.L 2), ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') := by
  intro R _ _ _ hCN G _ _ _ D D' A A' U U' wL hwL σ
  have hR := TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  haveI : IsNoetherianRing R := hR.1
  have hL := linComb_isLB U.LG.L U.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  have hL' := linComb_isLB U'.LG.L U'.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  let σ' : H0 U'.LG.L 2 := secOfIso σ hwL hL' hL
  obtain ⟨s, hs⟩ := exists_sec U'.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R))
    (ε' := fun _ => ((2 : ℕ) : ℤ)) (fun _ _ h => by simp only [Category.comp_id])
    (H1.SectionArithmetic.pullSec σ' (pullback.fst G.hom (jK R)))
  obtain ⟨E, hsE, -⟩ := (U'.expand 2 (by norm_num)).1 s
  obtain ⟨f', hf', -⟩ := IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D' A' G U'.toUnifPre 2 σ' s
    (SectionScalarValuation.secScal_of_sval U'.LG.isLB fun y J hJ =>
      ((hs _ _ y J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm) E hsE
  refine ⟨σ', f', hf', fun Z r z J J' hJ hJ' => ?_⟩
  have hm : r z ∈ (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)).U (fun _ => J' r) ⊓
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)).U (fun _ => J r) :=
    ⟨Set.mem_iInter.2 fun _ => hJ' r, Set.mem_iInter.2 fun _ => hJ r⟩
  have e := gs_secOfIso_eq wL σ hwL hL' hL (fun _ => J' r) (fun _ => J r) r z hm
  rw [sval_of σ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id]),
    sval_of σ' r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
  show _ = (gm r z _ (wL.s ((fun _ => J r), (fun _ => J' r)))).val * _
  have e' : gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J' r) (σ'.f fun _ => J' r) =
      ((gm r z _ (wL.s ((fun _ => J r), (fun _ => J' r))))⁻¹).val *
        gs r z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J r) (σ.f fun _ => J r) := e
  rw [e', ← _root_.mul_assoc, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, _root_.one_mul]

end GlobalTheory.SqTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBundleSquareSectionWeightZeroNonzero
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SquareSectionWeightZero

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), ∃ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) ∧ ¬ ∀ j, (f 0).f j = 0 := by
  intro R _ _ _ _ G _ _ _ D A U
  obtain ⟨h1, h2, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨E, hE⟩ := GlobalTheory.FamFree.exists_fam_support (F := FractionRing R) h1.globalFns h2.secTwist
    D.tau_bimult (k := 2) (by norm_num) (0 : D.toPre.X)
  have hE0 : ¬ ∀ j, (E.s 0).f j = 0 := (hE 0).2 ⟨0, by simp⟩
  obtain ⟨s, hs, -⟩ := (U.expand 2 (by norm_num)).2 E
  obtain ⟨r, hr, σ, f, -, hf, hexp⟩ := hs
  refine ⟨σ, f, hexp, fun h0 => hE0 ?_⟩
  have key := (GlobalTheory.ConstFam.secScal_iff_resF D.toPre (FractionRing R) (E.s 0) (f 0) r).1 (hf 0)
  have hf0 : (f 0 : GlobalTheory.ConstFam.SecBMod D.toPre 2 0) = 0 := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext h0
  rw [hf0] at key
  erw [map_zero] at key
  have hr' : GlobalTheory.ConstFam.toF (R := R) (FractionRing R) r ≠ 0 := by
    intro h
    apply hr
    have hinj : Function.Injective (GlobalTheory.ConstFam.toF (R := R) (FractionRing R)) :=
      (algebraMap (FractionRing R) (FractionRing R)).injective.comp (IsFractionRing.injective R _)
    exact hinj (h.trans (map_zero _).symm)
  let t : GlobalTheory.ConstFam.SecFMod D.toPre (FractionRing R) 2 0 := E.s 0
  have k2 : GlobalTheory.ConstFam.toF (R := R) (FractionRing R) r • t = 0 := key.symm
  have e0 : t = 0 := by rw [← inv_smul_smul₀ hr' t, k2, smul_zero]
  intro j
  exact congrArg (fun q : GlobalTheory.ConstFam.SecFMod D.toPre (FractionRing R) 2 0 => LB.Sec.f q j) e0

end GlobalTheory.SquareSectionWeightZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteLocalEtaleNeighbourhood
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem essFiniteType_int_stalk (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp F)
    [LocallyOfFiniteType s] (x : X) : Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum F := s x
  have h2 : (algebraMap F ((Spec.structureSheaf F).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  have hQ : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  have hF : Algebra.EssFiniteType ℚ F := inferInstance
  have hZF : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ ℚ F
  have h3 : (algebraMap ℤ F).EssFiniteType := RingHom.essFiniteType_algebraMap.2 hZF
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem exists_ringHom_stalk (F : Type) [Field F] (X : Scheme.{0}) (s : X ⟶ Sp F) (x : X) :
    Nonempty (F →+* X.presheaf.stalk x) := by
  let p : PrimeSpectrum F := s x
  exact ⟨(s.stalkMap x).hom.comp (algebraMap F ((Spec.structureSheaf F).presheaf.stalk p))⟩

theorem stalk_factor_eq {X : Scheme.{0}} {R : CommRingCat.{0}} {x y : X} (hy : y = x) (φ : X.presheaf.stalk x ⟶ R)
    (ψ : X.presheaf.stalk y ⟶ R) (h : Spec.map ψ ≫ X.fromSpecStalk y = Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ e : X.presheaf.stalk y →+* X.presheaf.stalk x, Function.Bijective e ∧ ψ.hom = φ.hom.comp e := by
  subst hy
  refine ⟨RingHom.id _, Function.bijective_id, ?_⟩
  have : ψ = φ := Spec.map_injective ((cancel_mono _).1 h)
  subst this
  rfl

end GlobalTheory.GenFan

namespace GlobalTheory.GenFan

theorem exists_chart : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp F), LocallyOfFiniteType s →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ x : X, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R)
    (ξ : Sp R ⟶ X), IsCN R ∧ ξ (closedPoint R) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified ∧ ∀ p, ξ p ⤳ x := by
  intro F _ _ X s hs hN x
  obtain ⟨hd, hic⟩ := hN x
  haveI : IsDomain (X.presheaf.stalk x) := hd
  haveI : IsIntegrallyClosed (X.presheaf.stalk x) := hic
  haveI : Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := essFiniteType_int_stalk F X s x
  haveI : IsNoetherianRing (X.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  obtain ⟨ι⟩ := exists_ringHom_stalk F X s x
  haveI : CharZero (X.presheaf.stalk x) := (RingHom.charZero_iff ι.injective).1 inferInstance
  have fg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (X.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) with hR
  set φ := algebraMap (X.presheaf.stalk x) R with hφ
  haveI : IsLocalHom φ := ((IsLocalRing.local_hom_TFAE φ).out 0 2).mpr hm.symm.le
  have hres : Function.Surjective ((residue R).comp φ) := by
    intro r
    obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)).2 r
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine ⟨b, ?_⟩
    rw [← ha, RingHom.comp_apply, ResidueField.map_residue]
  let ξ : Sp R ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x
  have hξ : ∀ p, ξ p = X.fromSpecStalk x (Spec.map (CommRingCat.ofHom φ) p) := fun p => Scheme.Hom.comp_apply _ _ _
  have hx : ξ (closedPoint R) = x := by
    refine (hξ _).trans ?_
    have : Spec.map (CommRingCat.ofHom φ) (closedPoint R) = closedPoint (X.presheaf.stalk x) := comap_closedPoint φ
    rw [this]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨e, he, hψ⟩ := stalk_factor_eq hx (CommRingCat.ofHom φ) (Scheme.stalkClosedPointTo ξ)
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)
  refine ⟨R, inferInstance, hRd, hloc, ξ, ⟨hRn, hRi, ?_, ?_⟩, hx, ?_, ?_, ?_⟩
  · rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  · exact (RingHom.charZero_iff (φ.comp ι).injective).1 inferInstance
  · rw [hψ]
    exact isEtaleCompletion_comp_bij e he φ ⟨RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
      hm.symm, RingHom.Finite.of_surjective _ hres⟩
  · rw [hψ, ← RingHom.comp_assoc]
    exact RingHom.FormallyUnramified.of_surjective (hres.comp he.2)
  · intro p
    have h : ξ p ∈ Set.range (X.fromSpecStalk x) := ⟨_, (hξ p).symm⟩
    rwa [Scheme.range_fromSpecStalk] at h

end GlobalTheory.GenFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFieldExtension
section
open TensorProduct
namespace GlobalTheory.FieldExtensionExists

theorem exists_field_extension {R R' K : Type} [CommRing R] [CommRing R'] [Field K]
    (ρ : R →+* R') (hinj : Function.Injective ρ) (hfin : ρ.Finite) (φ : R →+* K) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (χ : R' →+* L),
      χ.comp ρ = (algebraMap K L).comp φ := by
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Algebra.IsIntegral R R' := ⟨fun x => hfin.to_isIntegral x⟩
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨q, -, hq, hqc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker φ) (⊥ : Ideal R') (by
    intro x hx
    have : ρ x = 0 := hx
    have h0 : x = 0 := hinj (this.trans (map_zero ρ).symm)
    rw [h0]; exact Ideal.zero_mem _)
  have hqc' : q.comap ρ = RingHom.ker φ := hqc
  let j : (R ⧸ RingHom.ker φ) →+* (R' ⧸ q) := Ideal.quotientMap q ρ hqc'.ge
  have hj : Function.Injective j := Ideal.quotientMap_injective' hqc'.le
  have hjf : j.Finite := by
    apply RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (RingHom.ker φ))
    have : j.comp (Ideal.Quotient.mk (RingHom.ker φ)) = (Ideal.Quotient.mk q).comp ρ := by
      ext x; simp [j]
    rw [this]
    exact (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective).comp hfin
  letI : Algebra (R ⧸ RingHom.ker φ) (R' ⧸ q) := j.toAlgebra
  letI : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : Module.Finite (R ⧸ RingHom.ker φ) (R' ⧸ q) := hjf
  haveI : Nontrivial (K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _
      (RingHom.kerLift_injective φ) hj
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q))
  refine ⟨(K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) ⧸ M, Ideal.Quotient.field M, inferInstance,
    (inferInstance : Module.Finite K ((K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) ⧸ M)),
    (Ideal.Quotient.mk M).comp ((Algebra.TensorProduct.includeRight (R := R ⧸ RingHom.ker φ) (A := K)
      (B := R' ⧸ q)).toRingHom.comp (Ideal.Quotient.mk q)), ?_⟩
  ext r
  change Ideal.Quotient.mk M (Algebra.TensorProduct.includeRight (R := R ⧸ RingHom.ker φ) (A := K)
      (B := R' ⧸ q) (algebraMap (R ⧸ RingHom.ker φ) (R' ⧸ q) (Ideal.Quotient.mk _ r))) =
    Ideal.Quotient.mk M ((φ r) ⊗ₜ 1)
  rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem exists_extension : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R'),
    Function.Injective ρ → ρ.Finite → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
    ∀ (ψ : R →+* V), IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V')
      (f : V →+* V') (ψ' : R' →+* V'), GlobalTheory.LN.CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ' ∧
      ψ'.comp ρ = f.comp ψ := by
  intro R R' _ _ _ _ ρ hinj hfin V _ _ _ hV ψ hψ
  obtain ⟨h1, h2, h3⟩ := hV
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨L, _, _, _, χ, hχ⟩ := exists_field_extension ρ hinj hfin ((algebraMap V (FractionRing V)).comp ψ)
  obtain ⟨W, _, _, hW1, hW2, _, _, _, hc, -, hf, hl, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  have hWL : Function.Injective (algebraMap W L) := IsFractionRing.injective W L
  have hmem : ∀ x : R', ∃ w : W, algebraMap W L w = χ x := by
    intro x
    obtain ⟨P, hP, hPx⟩ := hfin.to_isIntegral x
    refine hint (χ x) ⟨P.map ψ, hP.map ψ, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← hχ, ← Polynomial.hom_eval₂, hPx, map_zero]
  choose g hg using hmem
  let ψ' : R' →+* W :=
    { toFun := g
      map_one' := hWL (by simp [hg])
      map_mul' := fun x y => hWL (by simp [hg])
      map_zero' := hWL (by simp [hg])
      map_add' := fun x y => hWL (by simp [hg]) }
  have hcomp : ψ'.comp ρ = (algebraMap V W).comp ψ := by
    ext r
    apply hWL
    have e1 := RingHom.congr_fun hχ r
    have e2 := RingHom.congr_fun hc (ψ r)
    simp only [RingHom.comp_apply] at e1 e2 ⊢
    rw [e2, ← e1]
    exact hg _
  have hloc : IsLocalHom (ψ'.comp ρ) := by rw [hcomp]; infer_instance
  have hmax : ((IsLocalRing.maximalIdeal W).comap ψ').IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hfin.to_isIntegral
    have e : (IsLocalRing.maximalIdeal W).comap (ψ'.comp ρ) = IsLocalRing.maximalIdeal R :=
      ((IsLocalRing.local_hom_TFAE (ψ'.comp ρ)).out 0 4).1 hloc
    rw [Ideal.comap_comap, e]
    infer_instance
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, ψ',
    ⟨hW1, hW2, charZero_of_injective_algebraMap hf⟩, hf, hl, ?_, hcomp⟩
  exact ((IsLocalRing.local_hom_TFAE ψ').out 0 4).2 (IsLocalRing.eq_maximalIdeal hmax)

end GlobalTheory.FieldExtensionExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteLocalDomainCover
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.LocExt

theorem exists_isCN_common_of_finite : ∀ (R₀ A R' : Type) [CommRing R₀] [IsLocalRing R₀] [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R'] [IsLocalRing R'] (φ : R₀ →+* A) (ρ : R₀ →+* R'), IsCN A → IsLocalHom φ → Function.Injective ρ → ρ.Finite → ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (ι : A →+* A₁) (σ : R' →+* A₁), IsCN A₁ ∧ Function.Injective ι ∧ ι.Finite ∧ IsLocalHom ι ∧ IsLocalHom σ ∧ σ.comp ρ = ι.comp φ := by
  intro R V R' _ _ _ _ _ _ _ ψ ρ hV hψ hρ hfin
  obtain ⟨hnoeth, hnorm, hcomp, hchar⟩ := hV
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  haveI : Algebra.IsIntegral R R' := Algebra.IsIntegral.of_finite R R'
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨q, -, hqprime, hq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker ψ) (⊥ : Ideal R')
    (by
      intro x hx
      have h0 : ρ x = 0 := Ideal.mem_bot.1 (Ideal.mem_comap.1 hx)
      rw [hρ (h0.trans (map_zero ρ).symm)]
      exact zero_mem _)
  haveI := hqprime
  let K := FractionRing V
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  let Ω := AlgebraicClosure K
  let ιK : V →+* Ω := (algebraMap K Ω).comp (algebraMap V K)
  have hιK : Function.Injective ιK := (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  let P := q.comap (algebraMap R R')
  let ψb : R ⧸ P →+* V := Ideal.Quotient.lift P ψ (fun a ha => by
    have : a ∈ RingHom.ker ψ := hq ▸ ha
    exact RingHom.mem_ker.1 this)
  have hψb : Function.Injective ψb := by
    refine (injective_iff_map_eq_zero ψb).2 fun x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : ψ a = 0 := hx
    have h2 : a ∈ P := by rw [show P = RingHom.ker ψ from hq]; exact RingHom.mem_ker.2 h1
    exact Ideal.Quotient.eq_zero_iff_mem.2 h2
  letI : Algebra (R ⧸ P) Ω := (ιK.comp ψb).toAlgebra
  haveI : Module.IsTorsionFree (R ⧸ P) (R' ⧸ q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (R ⧸ P) Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (by
      change Function.Injective (ιK.comp ψb)
      exact hιK.comp hψb)
  haveI : Algebra.IsAlgebraic (R ⧸ P) (R' ⧸ q) := Algebra.IsIntegral.isAlgebraic
  let φb : (R' ⧸ q) →ₐ[R ⧸ P] Ω := IsAlgClosed.lift
  let φ : R' →+* Ω := φb.toRingHom.comp (Ideal.Quotient.mk q)
  have hφρ : ∀ r, φ (ρ r) = ιK (ψ r) := fun r => by
    have := φb.commutes (Ideal.Quotient.mk P r)
    exact this
  have hint : ∀ x : R', ∃ p : Polynomial V, p.Monic ∧ p.eval₂ ιK (φ x) = 0 := fun x => by
    obtain ⟨p, hmon, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) x
    refine ⟨p.map ψ, hmon.map ψ, ?_⟩
    have hc : ιK.comp ψ = φ.comp (algebraMap R R') := RingHom.ext fun r => (hφρ r).symm
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := R')
  let L : IntermediateField K Ω := IntermediateField.adjoin K ((φ '' (s : Set R')) : Set Ω)
  have hintK : ∀ x : R', IsIntegral K (φ x) := fun x => by
    obtain ⟨p, hmon, hp⟩ := hint x
    refine ⟨p.map (algebraMap V K), hmon.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨x, -, rfl⟩
    exact hintK x)
  have hmem : ∀ x : R', φ x ∈ L := fun x => by
    have hx : x ∈ Submodule.span R (s : Set R') := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin K _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem L
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ?_ hy
      have : φ (algebraMap R R' r) = algebraMap K Ω (algebraMap V K (ψ r)) := hφρ r
      rw [this]
      exact L.algebraMap_mem _
  let φL : R' →+* L := φ.codRestrict L hmem
  let W := integralClosure V L
  haveI hWf : Module.Finite V W := IsIntegralClosure.finite V K L W
  haveI : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) W
  have hVL : Function.Injective (algebraMap V L) := by
    rw [IsScalarTower.algebraMap_eq V K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
  have hinjW : Function.Injective (algebraMap V W) := fun x y h => hVL (congrArg Subtype.val h)
  have hran : ∀ x : R', φL x ∈ W := fun x => by
    obtain ⟨p, hmon, hp⟩ := hint x
    refine ⟨p, hmon, ?_⟩
    apply Subtype.val_injective
    have h := Polynomial.hom_eval₂ p (algebraMap V L) (algebraMap L Ω) (φL x)
    refine h.trans ?_
    exact hp
  let ψ' : R' →+* W := φL.codRestrict W hran
  have hcomm : ψ'.comp ρ = (algebraMap V W).comp ψ := RingHom.ext fun r => by
    apply Subtype.val_injective
    apply Subtype.val_injective
    exact hφρ r
  haveI : CharZero W := charZero_of_injective_algebraMap hinjW
  have h1 : (maximalIdeal W).comap (algebraMap V W) = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal W))
  have hlocW : IsLocalHom (algebraMap V W) := ((local_hom_TFAE _).out 0 4).2 h1
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, ψ',
    ⟨IsNoetherianRing.of_finite V W, integralClosure.isIntegrallyClosedOfFiniteExtension K,
      CompleteFiniteExtension.isAdicComplete_of_finite_local V W, inferInstance⟩, hinjW,
    RingHom.finite_algebraMap.2 hWf, hlocW, ?_, hcomm⟩
  refine ((local_hom_TFAE ψ').out 0 4).2 ?_
  have hmR : (maximalIdeal W).comap (ψ'.comp (algebraMap R R')) = maximalIdeal R := by
    have h2 : (maximalIdeal V).comap ψ = maximalIdeal R := ((local_hom_TFAE _).out 0 4).1 hψ
    change (maximalIdeal W).comap (ψ'.comp ρ) = maximalIdeal R
    rw [hcomm, ← Ideal.comap_comap, h1, h2]
  have hQ : ((maximalIdeal W).comap ψ').IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
    rw [Ideal.comap_comap, hmR]
    exact maximalIdeal.isMaximal R
  exact IsLocalRing.eq_maximalIdeal hQ

end GlobalTheory.LocExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalHolomorphicLatticeBasisConvexStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)), IsOpen B → Convex ℝ B → (∀ b₀ ∈ B, ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧ ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b)) → ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, DifferentiableOn ℂ lam B ∧ ∀ b ∈ B, IsLatBasis (K b) (lam b) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global | exact GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global | (intros; apply GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.FlagBundle GlobalTheory.ShFam
open GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.LieBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F]

def IsLieBase (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z) (f : C.Y.X ⟶ X.X)
    (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) :
    Prop :=
  IsOpenImmersion j ∧ f ≫ j = C.π ∧ Tied e X j f₀ S A₀

def openPart {X : Var F} (j : X.X ⟶ gen Z) : X.X.Opens := j ⁻¹ᵁ (genBd Z).compl

def cxOf (e : F ≃+* c.F) (σ : c.F →+* ℂ) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (y : CxPts X.str (σ.comp e.toRingHom)) : CxPts (genStr Z) σ :=
  ⟨y.1 ≫ j, by
    have : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
    refine (cancel_mono (spMap e.toRingHom)).1 ?_
    rw [Category.assoc, Category.assoc, hj, y.2, ← Spec.map_comp]
    rfl⟩

variable {σ : c.F →+* ℂ} {r : ℕ}

open Classical in

def unfFam (U : Formalism.L2.PjFree.Unf Xo c σ r) : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r := fun σ' =>
  if h : σ = σ' then h ▸ U else { Comp := Empty, X := fun k => k.elim, un := fun k => k.elim }

variable (Z) in

def hodgeMet (U : Formalism.L2.PjFree.Unf Xo c σ r) : EigMet Z σ :=
  EigMet.hodge (unfFam U) (2 * Real.pi) Real.two_pi_pos (Classical.arbitrary (EigMet Z σ))

def FrameAt (e : F ≃+* c.F) {X : Var F} {j : X.X ⟶ gen Z} (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) {x : Sp ℂ ⟶ Z.X} (g : EigFrame Z σ x) : Prop :=
  ∃ (φ : c.F →+* X.X.presheaf.stalk (under y)) (fz : EigFrame Z φ (stalkPt X (under y) ≫ j ≫ genι Z))
    (ψ : X.X.presheaf.stalk (under y) →+* ℂ), y.1 = spMap ψ ≫ stalkPt X (under y) ∧
      fz.Coord (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) f₀ (A₀ * A⁻¹) ∧ fz.IsMap ψ g

open Classical in

def lieGram (e : F ≃+* c.F) (U : Formalism.L2.PjFree.Unf Xo c σ r) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ : Mat Dw.mult X.Fn) (A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) : Mat Dw.mult ℂ :=
  if h : ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g then
    fun τ => ((hodgeMet Z U).gram (cxOf e σ hj y) h.choose τ)ᵀ
  else 0

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianDualPairInCoisotropicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrangian_dual_pair_in_coisotropic : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), Mᵀ = -M → M.det ≠ 0 → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → ∃ (d : ℕ) (e f : Fin d → Fin r → ℝ), (∀ i, e i ∈ W) ∧ (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ := by
  first | exact @GlobalTheory.exists_lagrangian_dual_in_coisotropic | exact GlobalTheory.exists_lagrangian_dual_in_coisotropic | (intros; apply GlobalTheory.exists_lagrangian_dual_in_coisotropic <;> assumption)
end

