import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0024
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0026
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityOfMinguez
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0015
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BocksteinReductionIsRed
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

noncomputable section

namespace GlobalTheory.EtC.Bock.RedSpec
open GlobalTheory.EtC

variable (Q q : ℕ) [NeZero Q] [NeZero q] (hq : q ∣ Q) (i : ℤ)

abbrev ρ : ULift.{1} (ZMod Q) →+* ULift.{1} (ZMod q) :=
  (ULift.ringEquiv.symm : ZMod q ≃+* ULift.{1} (ZMod q)).toRingHom.comp
    ((ZMod.castHom hq (ZMod q)).comp (ULift.ringEquiv : ULift.{1} (ZMod Q) ≃+* ZMod Q).toRingHom)

def primRed {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), by
    obtain ⟨ξ, h⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q A).2.2.2.2.2 q hq ζ
    rw [← h]; exact ξ.2⟩

theorem primRed_val {A : Type} [CommRing A] (ζ : Prim Q A) : (primRed Q q hq ζ).1 = ζ.1 ^ (Q / q) := rfl

theorem primRed_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (ζ : Prim Q A) :
    Prim.map f (primRed Q q hq ζ) = primRed Q q hq (Prim.map f ζ) :=
  Subtype.ext (map_pow f ζ.1 (Q / q))

abbrev T (q : ℕ) (A : Type) [CommRing A] : Type 1 := (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A

abbrev cl {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (c : ULift.{1} (ZMod q)) : T i q A :=
  Submodule.Quotient.mk (Finsupp.single ζ c)

abbrev Rq (A : CommRingCat.{0}) : ModuleCat.{1} (ULift.{1} (ZMod Q)) :=
  (ModuleCat.restrictScalars.{1} (ρ Q q hq)).obj ((twF q i).obj A)

def gen (A : CommRingCat.{0}) (ζ : Prim Q A) : Rq Q q hq i A := (cl i (primRed Q q hq ζ) 1 : T i q A)

def redFree (A : CommRingCat.{0}) : (Prim Q A →₀ ULift.{1} (ZMod Q)) →ₗ[ULift.{1} (ZMod Q)] Rq Q q hq i A :=
  Finsupp.linearCombination _ (gen Q q hq i A)

theorem redFree_single (A : CommRingCat.{0}) (ζ : Prim Q A) (c : ULift.{1} (ZMod Q)) :
    redFree Q q hq i A (Finsupp.single ζ c) = (cl i (primRed Q q hq ζ) (ρ Q q hq c) : T i q A) := by
  rw [redFree, Finsupp.linearCombination_single]
  show (Submodule.Quotient.mk (ρ Q q hq c • Finsupp.single (primRed Q q hq ζ) 1) : T i q A) = _
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem pow_eq_of_mod {M : Type} [Monoid M] (z : M) (q : ℕ) (hz : z ^ q = 1) (n : ℕ) : z ^ n = z ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, hz, one_pow, one_mul]

theorem twRel_le_ker (A : CommRingCat.{0}) : twRel Q i A ≤ LinearMap.ker (redFree Q q hq i A) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, redFree_single, redFree_single]
  change (cl i (primRed Q q hq ξ) (ρ Q q hq 1) - cl i (primRed Q q hq ζ) (ρ Q q hq (ULift.up ((a ^ i : (ZMod Q)ˣ) : ZMod Q))) : T i q A) = 0
  rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero, map_one]
  let a' : (ZMod q)ˣ := Units.map (ZMod.castHom hq (ZMod q)).toMonoidHom a
  refine Submodule.subset_span ⟨primRed Q q hq ζ, primRed Q q hq ξ, a', ?_, ?_⟩
  · have hz : (ζ.1 ^ (Q / q)) ^ q = 1 := by
      rw [← pow_mul, Nat.div_mul_cancel hq]; exact (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q A).1 ζ
    have hv : (a' : ZMod q).val = (a : ZMod Q).val % q := by
      have : (a' : ZMod q) = (((a : ZMod Q).val : ℕ) : ZMod q) := by
        change ZMod.castHom hq (ZMod q) (a : ZMod Q) = _
        conv_lhs => rw [← ZMod.natCast_zmod_val (a : ZMod Q)]
        rw [map_natCast]
      rw [this, ZMod.val_natCast]
    rw [primRed_val, primRed_val, h, hv, ← pow_eq_of_mod _ q hz, ← pow_mul, ← pow_mul, mul_comm]
  · congr 2
    change ULift.up (ZMod.castHom hq (ZMod q) ((a ^ i : (ZMod Q)ˣ) : ZMod Q)) = ULift.up (((a' ^ i : (ZMod q)ˣ)) : ZMod q)
    rw [show a' ^ i = Units.map (ZMod.castHom hq (ZMod q)).toMonoidHom (a ^ i) from (map_zpow _ a i).symm]
    rfl

def redA (A : CommRingCat.{0}) : (twF Q i).obj A ⟶ Rq Q q hq i A :=
  ModuleCat.ofHom (Y := Rq Q q hq i A) ((twRel Q i A).liftQ (redFree Q q hq i A) (twRel_le_ker Q q hq i A))

theorem redA_cl (A : CommRingCat.{0}) (ζ : Prim Q A) (c : ULift.{1} (ZMod Q)) :
    (redA Q q hq i A).hom (cl i ζ c : T i Q A) = (cl i (primRed Q q hq ζ) (ρ Q q hq c) : T i q A) :=
  redFree_single Q q hq i A ζ c

def redNat : twF Q i ⟶ twF q i ⋙ ModuleCat.restrictScalars.{1} (ρ Q q hq) where
  app A := redA Q q hq i A
  naturality A B f := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ c => ?_))
    change (redA Q q hq i B).hom (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ c)) : T i Q B) =
      ((twF q i).map f).hom ((redA Q q hq i A).hom (cl i ζ c : T i Q A))
    rw [Finsupp.mapDomain_single, redA_cl, redA_cl]
    change _ = (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single (primRed Q q hq ζ) (ρ Q q hq c))) : T i q B)
    rw [Finsupp.mapDomain_single, primRed_map]

end GlobalTheory.EtC.Bock.RedSpec

namespace GlobalTheory.EtC.Bock.RedSpec
open GlobalTheory.EtC

variable (Q q : ℕ) [NeZero Q] [NeZero q] (hq : q ∣ Q) (i : ℤ)

def redPre : Scheme.Γ ⋙ twF Q i ⟶ ((restr (ZMod.castHom hq (ZMod q))).obj (tw q i)).obj :=
  Functor.whiskerLeft Scheme.Γ (redNat Q q hq i) ≫
    Functor.whiskerRight (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) (ModuleCat.restrictScalars.{1} (ρ Q q hq))

def redSh : tw Q i ⟶ (restr (ZMod.castHom hq (ZMod q))).obj (tw q i) :=
  ⟨sheafifyLift Scheme.etaleTopology (redPre Q q hq i) ((restr (ZMod.castHom hq (ZMod q))).obj (tw q i)).property⟩

end GlobalTheory.EtC.Bock.RedSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagonalComplementSecondProjectionIsFiniteEtaleStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f], IsFinite (GlobalTheory.EtC.Tr.diagComplHom f) ∧ Etale (GlobalTheory.EtC.Tr.diagComplHom f) := by
  first | (exact @GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (exact GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (intros; apply GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFibreFieldPointsCardLEOfIsFiniteIsAffineStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [IsAffine X], ∃ n, GlobalTheory.EtC.Tr.FibrePointsLE f n := by
  first | (exact @GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine) | (exact GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine) | (intros; apply GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibreFieldPointsCardLEDiagonalComplementSecondPrStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (n : ℕ), GlobalTheory.EtC.Tr.FibrePointsLE f (n + 1) → GlobalTheory.EtC.Tr.FibrePointsLE (GlobalTheory.EtC.Tr.diagComplHom f) n := by
  first | (exact @GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (exact GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (intros; apply GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (Formalism.AUTREP.GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), Formalism.L2.NG.HypOutside J χ B → ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → Formalism.AUTREP.IsUnif L s.v ϖ → ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by
  first | exact @GlobalTheory.TSetFin.finite_image_tSet | exact GlobalTheory.TSetFin.finite_image_tSet | (intros; apply GlobalTheory.TSetFin.finite_image_tSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsBaseChange
section
set_option autoImplicit false
noncomputable section
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1.Base

variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

theorem mapDR_ιMulti (n : ℕ) (v : Fin n → Ω[K⁄k]) :
    mapDR k K L (ExteriorAlgebra.ιMulti K n v) =
      ExteriorAlgebra.ιMulti L n (fun i => KaehlerDifferential.map k k K L (v i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  exact congrArg (fun l => List.prod l) (congrArg List.ofFn (funext fun i => by
    show mapDR k K L (ExteriorAlgebra.ι K (v i)) = _
    rw [mapDR, ExteriorAlgebra.lift_ι_apply]; rfl))

variable {k K L} in

theorem mapDR_basis {I : Type} [LinearOrder I] (bK : Module.Basis I K Ω[K⁄k]) (bL : Module.Basis I L Ω[L⁄k])
    (h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i)) (s : Finset I) :
    mapDR k K L (bK.ExteriorAlgebra s) = bL.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.basis_apply_ofCard _ rfl,
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_family, mapDR_ιMulti]
  exact congrArg _ (funext fun i => (h _).symm)

variable {k K L} in

theorem repr_mapDR {I : Type} [LinearOrder I] (bK : Module.Basis I K Ω[K⁄k]) (bL : Module.Basis I L Ω[L⁄k])
    (h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i)) (ω : DR k K) (s : Finset I) :
    bL.ExteriorAlgebra.repr (mapDR k K L ω) s = algebraMap K L (bK.ExteriorAlgebra.repr ω s) := by
  have : ((bL.ExteriorAlgebra.coord s).restrictScalars K ∘ₗ (mapDR k K L).toLinearMap) =
      Algebra.linearMap K L ∘ₗ bK.ExteriorAlgebra.coord s := by
    refine bK.ExteriorAlgebra.ext fun t => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, mapDR_basis bK bL h,
      LinearMap.coe_restrictScalars, Module.Basis.coord_apply, Module.Basis.repr_self, Algebra.linearMap_apply]
    by_cases hts : t = s
    · subst hts; simp
    · simp [Finsupp.single_apply, hts]
  exact congrArg (· ω) this

end GlobalTheory.W1.Base

namespace GlobalTheory.W1.Base

theorem forms_baseChange : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L],
    (∀ y : DR k L, ∃ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), y = ∑ j, b j • mapDR k K L (ω j)) ∧
      ∀ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), LinearIndependent K b →
        ∑ j, b j • mapDR k K L (ω j) = 0 → ∀ j, ω j = 0 := by
  intro k K L _ _ _ _ _ _ _ _ _
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let I := Module.Basis.ofVectorSpaceIndex K Ω[K⁄k]
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let bK : Module.Basis I K Ω[K⁄k] := Module.Basis.ofVectorSpace K Ω[K⁄k]
  let bL : Module.Basis I L Ω[L⁄k] := (bK.baseChange L).map (tensorKaehlerEquivOfFormallyEtale k K L)
  have h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i) := fun i => by
    simp only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
      mapBaseChange_tmul, one_smul]
  set BK := bK.ExteriorAlgebra
  set BL := bL.ExteriorAlgebra
  refine ⟨fun y => ?_, fun m b ω hb hsum j => ?_⟩
  · set S := (BL.repr y).support
    refine ⟨S.card, fun j => BL.repr y (S.equivFin.symm j), fun j => BK (S.equivFin.symm j), ?_⟩
    simp only [BK, BL, mapDR_basis bK bL h]
    conv_lhs => rw [← BL.linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_coe_sort]
    exact (Fintype.sum_equiv S.equivFin _ _ fun _ => by rw [Equiv.symm_apply_apply])
  · have hc : ∀ s, ∀ j, BK.repr (ω j) s = 0 := by
      intro s
      have h0 := congrArg (fun z => BL.repr z s) hsum
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
        map_zero, Finsupp.coe_zero, Pi.zero_apply, BK, BL, repr_mapDR bK bL h] at h0
      refine Fintype.linearIndependent_iff.1 hb (fun j => BK.repr (ω j) s) ?_
      simpa [Algebra.smul_def, mul_comm] using h0
    exact BK.repr.injective (Finsupp.ext fun s => by simpa using hc s j)

end GlobalTheory.W1.Base
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeSheafSumSectionsEqOfTwoSplittingsStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeSheaf_sum_sections_eq_of_two_splittings : ∀ (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m m' : ℕ} {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)}, GlobalTheory.EtC.Tr.SplitBy f y s → GlobalTheory.EtC.Tr.SplitBy f y s' → ∑ j, (GlobalTheory.EtC.free R).map (yoneda.map (s j)) = ∑ j, (GlobalTheory.EtC.free R).map (yoneda.map (s' j)) := by
  first | (exact @GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings) | (exact GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings) | (intros; apply GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorAlternatingSeriesIdentityStatement
section
open GlobalTheory.LatHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_alternating_series_identity : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E) (n : ℕ) (L : Lat O K r), 1 ≤ n → ∑ k ∈ Finset.range (n + 1), ((-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2)) • heckeElem k (heckeAll (n - k) φ) L = 0 := by
  first | exact @GlobalTheory.HeckeSeries.heckeSeries_identity | exact GlobalTheory.HeckeSeries.heckeSeries_identity | (intros; apply GlobalTheory.HeckeSeries.heckeSeries_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityOfMinguezStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howe_duality_of_minguez : GlobalTheory.Published.MinguezThetaGL → GlobalTheory.Published.HoweDualityGL := by
  first | exact @GlobalTheory.HoweBridge.main | exact GlobalTheory.HoweBridge.main | (intros; apply GlobalTheory.HoweBridge.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IndEtaleComp
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ind_etale_comp : ∀ (X Y Z : Type) [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  first | (exact @GlobalTheory.IndEtaleComp.isIndEtale_comp) | (exact GlobalTheory.IndEtaleComp.isIndEtale_comp) | (intros; apply GlobalTheory.IndEtaleComp.isIndEtale_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsArtinianRingFibQuot
section
open GlobalTheory.PD

namespace GlobalTheory

theorem finite_quotient_of_integral {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [Algebra.FiniteType k S] (f : R →ₐ[k] S) (hi : (f : R →+* S).IsIntegral) (I : Ideal S)
    (hc : ∀ r, ∃ c : k, f r - algebraMap k S c ∈ I) : Module.Finite k (S ⧸ I) := by
  classical
  letI : Algebra R S := (f : R →+* S).toAlgebra
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType k R S
  haveI : Algebra.IsIntegral R S := ⟨hi⟩
  haveI : Module.Finite R S := Algebra.IsIntegral.finite
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨⟨G.image (Ideal.Quotient.mk I), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hs : s ∈ Submodule.span R (G : Set S) := hG ▸ Submodule.mem_top
  induction hs using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha =>
    obtain ⟨c, hc⟩ := hc r
    have e : Ideal.Quotient.mk I (r • a) = c • Ideal.Quotient.mk I a := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap]
      congr 1
      exact Ideal.Quotient.eq.2 hc
    rw [e]
    exact Submodule.smul_mem _ _ ha

end GlobalTheory

namespace GlobalTheory.PD

theorem isArtinianRing_fib_quot : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : Type) [Field F] [Algebra k F] [Algebra F K]
    [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    IsArtinianRing (rB k K x {0} ⧸ Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))) := by
  intro k K _ _ _ F _ _ _ _ d x h
  haveI := h.smooth 0
  set I := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) with hI
  let f : rA k x {0} →ₐ[k] rB k K x {0} :=
    ((IsScalarTower.toAlgHom k F K).comp (rA k x {0}).val).codRestrict (rB k K x {0})
      (fun a => (integralClosure (rA k x {0}) K).algebraMap_mem a)
  have hi : (f : rA k x {0} →+* rB k K x {0}).IsIntegral := by
    intro s
    obtain ⟨p, hm, hp⟩ := s.2
    refine ⟨p, hm, Subtype.val_injective ?_⟩
    have e := Polynomial.hom_eval₂ p (f : rA k x {0} →+* rB k K x {0}) (rB k K x {0}).val.toRingHom s
    refine e.trans ?_
    exact hp
  have hc : ∀ r, ∃ c : k, f r - algebraMap k _ c ∈ I := by
    rintro ⟨r, hr⟩
    induction hr using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, hi0, j, rfl⟩ := hy
      rw [Finset.mem_singleton] at hi0
      subst hi0
      cases j using Fin.cases with
      | zero =>
        refine ⟨1, ?_⟩
        convert I.zero_mem using 1
        rw [map_one, sub_eq_zero]
        refine Subtype.ext ?_
        show algebraMap F K (x 0 / x 0) = 1
        rw [div_self (h.pd.ne 0), map_one]
      | succ j =>
        refine ⟨0, ?_⟩
        rw [map_zero, sub_zero]
        exact Ideal.subset_span ⟨j, rfl⟩
    | algebraMap r =>
      refine ⟨r, ?_⟩
      have : f ⟨algebraMap k F r, _⟩ = algebraMap k _ r := f.commutes r
      rw [this, sub_self]
      exact I.zero_mem
    | add a b ha hb iha ihb =>
      obtain ⟨c₁, h₁⟩ := iha
      obtain ⟨c₂, h₂⟩ := ihb
      refine ⟨c₁ + c₂, ?_⟩
      have : f ⟨a + b, add_mem ha hb⟩ = f ⟨a, ha⟩ + f ⟨b, hb⟩ := map_add f ⟨a, ha⟩ ⟨b, hb⟩
      rw [this, map_add]
      convert add_mem h₁ h₂ using 1
      ring
    | mul a b ha hb iha ihb =>
      obtain ⟨c₁, h₁⟩ := iha
      obtain ⟨c₂, h₂⟩ := ihb
      refine ⟨c₁ * c₂, ?_⟩
      have : f ⟨a * b, mul_mem ha hb⟩ = f ⟨a, ha⟩ * f ⟨b, hb⟩ := map_mul f ⟨a, ha⟩ ⟨b, hb⟩
      rw [this, map_mul]
      convert add_mem (I.mul_mem_right (f ⟨b, hb⟩) h₁) (I.mul_mem_left (algebraMap k _ c₁) h₂) using 1
      ring
  haveI := GlobalTheory.finite_quotient_of_integral f hi I hc
  exact IsArtinianRing.of_finite k _

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsEmptyOfFibreFieldPointsCardLEZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEmpty_of_fibreFieldPointsCardLE_zero : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X), GlobalTheory.EtC.Tr.FibrePointsLE f 0 → IsEmpty Z := by
  first | (exact @GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero) | (exact GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero) | (intros; apply GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero  <;> assumption)
end

