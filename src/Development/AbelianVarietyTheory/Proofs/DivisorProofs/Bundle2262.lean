import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0166
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealSpecBijectiveCalculus
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem baseIdeal_sup {R : Type} [CommRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (a b : Ideal R) : baseIdeal f (a ⊔ b) = baseIdeal f a ⊔ baseIdeal f b := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, baseIdeal_ideal, baseIdeal_ideal, baseIdeal_ideal,
    Ideal.map_sup]

theorem idealSheaf_ext_top {X : Scheme.{0}} [IsAffine X] {I J : X.IdealSheafData}
    (h : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J.ideal ⟨⊤, isAffineOpen_top X⟩) : I = J :=
  Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := Unit) (fun _ => ⟨⊤, isAffineOpen_top X⟩) iSup_const fun _ => h

theorem appLE_specMap_fromSpec {W : Scheme.{0}} (U : W.Opens) (hU : IsAffineOpen U) (C : Type) [CommRing C]
    (φ : Γ(W, U) →+* C) (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤
      (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U) :
    ((Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h).hom =
      (cst (𝟙 (Spec (CommRingCat.of C))) ⊤).comp φ := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have m1 : (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h =
      hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(W, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(W, U)).presheaf.map_id _
  have m3 : (Scheme.ΓSpecIso Γ(W, U)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  rw [m1, m2, m3]
  ext x
  simp only [cst, RingHom.comp_apply, rs_self]
  rfl

theorem specIdeal :
    (∀ (C : Type) [CommRing C], Function.Bijective (fun a : Ideal C => baseIdeal (𝟙 (Spec (CommRingCat.of C))) a) ∧ (∀ a b : Ideal C, baseIdeal (𝟙 (Spec (CommRingCat.of C))) (a ⊔ b) = baseIdeal (𝟙 _) a ⊔ baseIdeal (𝟙 _) b)) ∧ (∀ (W : Scheme.{0}) (V : W.affineOpens) (C : Type) [CommRing C] (φ : Γ(W, V.1) →+* C) (J : W.IdealSheafData), J.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) = baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((J.ideal V).map φ)) := by
  refine ⟨fun C _ => ⟨⟨fun a b hab => ?_, fun J => ?_⟩, fun a b => baseIdeal_sup _ a b⟩, fun W V C _ φ J => ?_⟩
  · have hb := cst_bijective (𝟙 (Spec (CommRingCat.of C))) (W := ⊤) rfl
    have e := congrArg (fun I : (Spec (CommRingCat.of C)).IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top _⟩) hab
    simp only [baseIdeal_ideal] at e
    rw [← Ideal.comap_map_of_bijective _ hb (I := a), e, Ideal.comap_map_of_bijective _ hb]
  · have hb := cst_bijective (𝟙 (Spec (CommRingCat.of C))) (W := ⊤) rfl
    refine ⟨(J.ideal ⟨⊤, isAffineOpen_top _⟩).comap (cst (𝟙 (Spec (CommRingCat.of C))) ⊤), idealSheaf_ext_top ?_⟩
    simp only [baseIdeal_ideal]
    exact Ideal.map_comap_of_surjective _ hb.2 _
  · have h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ V.1 :=
      fun x _ => V.2.range_fromSpec.subset ⟨_, rfl⟩
    refine idealSheaf_ext_top ?_
    rw [GlobalTheory.Principalise.comapIdealAffine J _ V ⟨⊤, isAffineOpen_top _⟩ h, baseIdeal_ideal, Ideal.map_map,
      appLE_specMap_fromSpec V.1 V.2 C φ h]

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRingUnitsInvertP
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.CoeffUnit

theorem mem_of_isIntegral_int {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h1 : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hy]
  exact y.2

theorem isUnit_of_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l' : Level H) (c' : Coeff l') (W : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (A : Type) [CommRing A] (β : c'.V W →+* A), IsUnit (p : A) → ∀ a : c'.V W, a ≠ 0 → IsUnit (β a) := by
  intro E _ _ _ H l' c' W p hp hpW A _ β hpA a ha
  haveI := c'.fin

  set x : c'.F := (a : c'.F) with hxdef
  have hx0 : x ≠ 0 := by
    intro h; apply ha; exact Subtype.ext h
  have halg : IsAlgebraic ℤ (x⁻¹ : c'.F) := by
    have h1 : IsAlgebraic ℚ (x⁻¹ : c'.F) := Algebra.IsAlgebraic.isAlgebraic _
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ c'.F).mpr h1
  obtain ⟨d, hd0, hdint⟩ := halg.exists_integral_multiple

  obtain ⟨n, hn0, hnint⟩ : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : c'.F) * x⁻¹) := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · refine ⟨n, by exact_mod_cast hd0, ?_⟩
      rw [zsmul_eq_mul] at hdint; exact_mod_cast hdint
    · refine ⟨n, by simpa using hd0, ?_⟩
      have := hdint.neg
      rw [zsmul_eq_mul] at this
      convert this using 1; push_cast; ring
  obtain ⟨k, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one

  have hpmax : ((p : W)) ∈ IsLocalRing.maximalIdeal W := by
    obtain ⟨h1, h2⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hpW
    convert h2 using 1
    ext; simp
  have hmunit : IsUnit ((m : W)) := by
    by_contra hm
    have hmmax : ((m : W)) ∈ IsLocalRing.maximalIdeal W := hm
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
    have hbez : ((1 : ℤ)) = (p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m := by
      have := Nat.gcd_eq_gcd_ab p m
      rw [hcop] at this
      exact_mod_cast this
    have h1 : ((1 : W)) ∈ IsLocalRing.maximalIdeal W := by
      have : ((1 : W)) = (p : W) * (Nat.gcdA p m : W) + (m : W) * (Nat.gcdB p m : W) := by
        have := congrArg (fun t : ℤ => (t : W)) hbez
        push_cast at this
        exact this
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hpmax) (Ideal.mul_mem_right _ _ hmmax)
    exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨u, hu⟩ := hmunit

  have hnW : (((n : c'.F) * x⁻¹ : c'.F) : ℂ) ∈ W := by
    apply mem_of_isIntegral_int W
    exact hnint.map (c'.F.val.restrictScalars ℤ)
  have hum : (((u⁻¹ : Wˣ) : W) : ℂ) * (m : ℂ) = 1 := by
    have h1 : ((u⁻¹ : Wˣ) : W) * (m : W) = 1 := by rw [← hu]; exact u.inv_mul
    have h2 := congrArg (fun t : W => (t : ℂ)) h1
    simpa using h2
  have hinv : (((u⁻¹ : Wˣ) : W) : ℂ) = (m : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left hum
  have hbW : ((((p : c'.F) ^ k * x⁻¹ : c'.F)) : ℂ) ∈ W := by
    have heq : ((((p : c'.F) ^ k * x⁻¹ : c'.F)) : ℂ)
        = (((u⁻¹ : Wˣ) : W) : ℂ) * ((((n : c'.F) * x⁻¹ : c'.F)) : ℂ) := by
      have hm0 : (m : ℂ) ≠ 0 := by
        have : m ≠ 0 := by rintro rfl; simp at hnm; exact hn0 hnm
        exact_mod_cast this
      rw [hinv, hnm]; push_cast; field_simp
    rw [heq]; exact W.mul_mem _ _ (SetLike.coe_mem _) hnW
  let b : c'.V W := ⟨(p : c'.F) ^ k * x⁻¹, ValuationSubring.mem_comap.mpr hbW⟩
  have hab : a * b = (p : c'.V W) ^ k := by
    apply Subtype.ext
    show (a : c'.F) * ((p : c'.F) ^ k * x⁻¹) = (((p : c'.V W) ^ k : c'.V W) : c'.F)
    rw [← hxdef]; push_cast; field_simp
  have hu' : IsUnit (β a * β b) := by
    rw [← map_mul, hab, map_pow, map_natCast]; exact hpA.pow k
  exact isUnit_of_mul_isUnit_left hu'

end GlobalTheory.CoeffUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisTorsionOfWeilPairingField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GeomBasis

theorem basis_of_weil : ∀ (h N : ℕ) (k : Type) [Field k] (S : Scheme.{0}) (x : Sp k ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (z : kˣ) (e₀ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ A)), L.IsLB → Odd N → IsPrimitiveRoot z N → (∀ a a', e₀ (a + a') = e₀ a * e₀ a') → (∀ a, e₀ a = 1 ↔ ∃ a', a = N • a') → (∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e₀ a = g) → (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a a', Out.WeilIs A L N (e a) (e a') (unitOn (z ^ (2 * omegaStd a a')))) → (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ ∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e a = g := by
  intro h N k _ S x A _ _ L z e₀ e hL hN hz add₀ ker₀ onto₀ add tors weil
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.2 hN) (by decide)
  haveI : NeZero N := ⟨hN0⟩
  have e0 : e 0 = 1 := GlobalTheory.LevCover.add_map_zero add
  have kerE : ∀ a, e a = 1 ↔ ∃ a', a = N • a' := by
    intro a
    constructor
    · intro ha
      apply GlobalTheory.SiegelOfPolarised.exists_smul_of_dvd
      intro b
      have w1 := weil a b
      have w0 := weil 0 b
      rw [ha] at w1
      rw [e0] at w0
      have hu := GlobalTheory.weilIs_unique_fieldPoint S A L hL k x _ _ _ _ _ w1 w0
      have h0 : omegaStd (0 : Fin h ⊕ Fin h → ℤ) b = 0 := by simp [omegaStd]
      rw [h0, mul_zero, zpow_zero] at hu
      have hd : (N : ℤ) ∣ 2 * omegaStd a b := (hz.zpow_eq_one_iff_dvd _).1 hu
      obtain ⟨m, hm⟩ := hN
      have hc : IsCoprime (N : ℤ) 2 := ⟨1, -(m : ℤ), by rw [hm]; push_cast; ring⟩
      exact hc.dvd_of_dvd_mul_left hd
    · rintro ⟨b, rfl⟩
      rw [GlobalTheory.LevCover.add_map_nsmul add, tors]
  have tors₀ : ∀ a, e₀ a ^ N = 1 := fun a => by
    rw [← GlobalTheory.LevCover.add_map_nsmul add₀]; exact (ker₀ _).2 ⟨a, rfl⟩
  let F : (Fin h ⊕ Fin h → ZMod N) → {g : Over.mk x ⟶ A // g ^ N = 1} :=
    fun c => ⟨e₀ fun i => ((c i).val : ℤ), tors₀ _⟩
  have hF : Function.Injective F := fun c c' hcc => by
    have e₁ : e₀ (fun i => ((c i).val : ℤ)) = e₀ fun i => ((c' i).val : ℤ) := congrArg Subtype.val hcc
    have e₂ := add₀ ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) fun i => ((c' i).val : ℤ)
    rw [sub_add_cancel, e₁] at e₂
    obtain ⟨b, hb⟩ := (ker₀ _).1 (mul_eq_right.1 e₂.symm)
    funext i
    have := congrArg (fun w : ℤ => (w : ZMod N)) (congrFun hb i)
    simpa [sub_eq_zero] using this
  have hF' : Function.Surjective F := by
    rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := onto₀ g hg
    refine ⟨fun i => (a i : ZMod N), Subtype.ext ?_⟩
    show e₀ (fun i => (((a i : ZMod N)).val : ℤ)) = e₀ a
    have d : ∀ i, (N : ℤ) ∣ a i - (((a i : ZMod N)).val : ℤ) := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by simp)
    choose b hb using d
    have hab : a - (fun i => (((a i : ZMod N)).val : ℤ)) = N • b := funext fun i => by simpa using hb i
    have := add₀ (a - fun i => (((a i : ZMod N)).val : ℤ)) fun i => (((a i : ZMod N)).val : ℤ)
    rw [sub_add_cancel, hab, (ker₀ _).2 ⟨b, rfl⟩, _root_.one_mul] at this
    exact this.symm
  have card : Nat.card {g : Over.mk x ⟶ A // g ^ N = 1} = N ^ Fintype.card (Fin h ⊕ Fin h) := by
    rw [← Nat.card_congr (Equiv.ofBijective F ⟨hF, hF'⟩), Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]
  exact ⟨kerE, GlobalTheory.SiegelOfPolarised.onto_torsion hN0 e add tors (fun a ha => (kerE a).1 ha) card⟩

end GlobalTheory.GeomBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfBaseStage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqTower

theorem bottom_const_ratio : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ),
      IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y → Y.IsConst W.ψ W.θ c → ∃ v : T → ℂ,
        X.IsConst W.ψ W.θ (fun t => v t * c t) ∧
        ∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀ := by
  intro _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩
  intro W S _ hN i j A A' WW X B B' WW₁ Y c hX hY hc
  obtain ⟨Y₁, hY₁, hc₁⟩ := GlobalTheory.T.definiteBottom_stage_transport_same_constants W i j X Y hX hY
  obtain ⟨Z₁, v₁, hZ₁, e1, e2, e3, hv₁, hc₂⟩ := GlobalTheory.T.definiteBottom_lattice_change_constants_awayUnit μ₀ hμ W S hN i j X Y₁ hX hY₁
  obtain ⟨Z₂, v₂, hZ₂, f1, f2, f3, f4, f5, f6, hv₂, hc₃⟩ := GlobalTheory.T.definiteBottom_framesChange_stageZero μ₀ hμ W S hN i j X Z₁ hX hZ₁ e1 e2 e3
  obtain ⟨κ, hκ, hX'⟩ := GlobalTheory.T.definiteBottom_tower_constants_differ_by_factor W i j X Z₂ hX hZ₂ f1 f2 f3 f4 f5 f6 _ (hc₃ _ (hc₂ _ (hc₁ c hc)))
  refine ⟨fun t => κ * (v₂ t * v₁ t), ?_, fun t => ?_⟩
  · convert hX' using 2 with t
    ring
  · obtain ⟨h1, ζ₁, u₁, q₁⟩ := hv₁ t
    obtain ⟨h2, ζ₂, u₂, q₂⟩ := hv₂ t
    refine ⟨mul_ne_zero hκ (mul_ne_zero h2 h1), ζ₂ * ζ₁, u₂.mul u₁, ?_⟩
    show κ * (v₂ t * v₁ t) = _ * (κ * (v₂ μ₀ * v₁ μ₀))
    rw [q₁, q₂, map_mul]
    ring

end GlobalTheory.SqTower

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleArchimedeanConstant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ReadMatch

theorem gbig_and {Q1 Q2 Q : GlobalTheory.SqTop.GP} (h1 : GlobalTheory.SqTop.GBig Q1) (h2 : GlobalTheory.SqTop.GBig Q2)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q G μ₀ C x b) : GlobalTheory.SqTop.GBig Q := by
  obtain ⟨A1, h1⟩ := h1
  obtain ⟨A2, h2⟩ := h2
  refine ⟨max A1 A2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, h1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, h2⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => h G μ₀ C _ _
    (h1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G)
    (h2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G)⟩

theorem bottom_reading : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ (r : ℂ) (rc : ℝ) (κ : ℂ), r ≠ 0 ∧ (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) ∧ κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
              (κ * starRingEnd ℂ u) • P.W.Om x h P.F := by
  intro hPr hTI hLM hInp hBS
  refine gbig_and (GlobalTheory.T.bottom_triangle_constant_exists hPr hTI hLM hInp hBS) (GlobalTheory.T.bottom_triangle_unit_constant hPr hTI hLM hInp hBS) ?_
  intro D T Lc sc G μ₀ C x b q1 q2 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨r, rc, hr, hrδ, hrc, H1⟩ := q1 W hW i j A A' WW X δ t0 hX
  obtain ⟨κ, hκ, H2⟩ := q2 W hW i j A A' WW X δ t0 hX hβ r rc hr hrδ hrc H1
  refine ⟨r, rc, κ, hr, hrc, hκ, fun s Q P P' hB => ?_⟩
  obtain ⟨u, hu0, huQ, huU, hEq⟩ := H2 s Q P P' hB
  refine ⟨u, hu0, huQ, huU, fun ea ed h g x y hg hy => ?_⟩
  rw [(H1 s Q P P' hB ea ed).2 h g x y hg hy, hEq ea ed,
    P.W.smul _ _ _ _ (GlobalTheory.NormSum.RepInv.test_mem (GlobalTheory.InducedType.induced_type D).1 P.crv P P.level_pos)]

end GlobalTheory.ReadMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedPowerSeriesEvaluationDivisibilityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_power_series_evaluation_divisibility : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (π : C), ‖π‖ < 1 → ∃ (B : Subring (PowerSeries C)) (ev : B →+* C) (t : B), (∀ Φ, Φ ∈ B ↔ ∃ b : ℝ, ∀ n, ‖PowerSeries.coeff n Φ‖ ≤ b) ∧ (∀ Φ : B, ev Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries C) * π ^ n) ∧ t ≠ 0 ∧ (∀ Φ, ev Φ = 0 ↔ t ∣ Φ) ∧ ∀ Φ : B, Φ ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ Φ := by
  first | exact @GlobalTheory.MBLow.BddPS.main | exact GlobalTheory.MBLow.BddPS.main | (intros; apply GlobalTheory.MBLow.BddPS.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CLocEqOneOfNotOverPair
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongW Formalism.UG GlobalTheory.DefU GlobalTheory.PRep GlobalTheory.CongSc

namespace GlobalTheory.LadicPair

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

end GlobalTheory.LadicPair

namespace GlobalTheory.LadicPair

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

variable [IsCMField E]

theorem cT_cLoc_conjSrc_mul {n : ℕ} (g : UA E n) (u : HeightOneSpectrum (𝓞 E)) :
    Matrix.transpose (((cLoc (conjSrc (IsCMField.complexConj E).toRingEquiv u) g : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _).map (conjLoc (IsCMField.complexConj E).toRingEquiv u)) *
      ((cLoc u g : GL (Fin n) (u.adicCompletion E)) : Matrix (Fin n) (Fin n) (u.adicCompletion E)) = 1 := by
  have h : cT (conjAd E) ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) * 1 *
      ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) = 1 := g.2
  rw [Matrix.mul_one] at h
  calc _ = (cT (conjAd E) ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) *
        ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E))).map ((pLoc E u).comp (pFin E)) := by
        rw [Matrix.map_mul]; rfl
    _ = 1 := by rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.LadicPair

namespace GlobalTheory.LadicPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

end GlobalTheory.LadicPair

namespace GlobalTheory.LadicPair

end GlobalTheory.LadicPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesFramedPointOfUnitTriangularChart
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagMod.Frames

theorem lies_of_chart_tri : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (F : Frames Y π), F.TopEigen → ∀ (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (z : Sp S ⟶ Z) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hx : z ≫ π = frX P ≫ Y.j) (U : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ σ, (U σ).BlockTriangular id) → (∀ σ i, IsUnit (U σ i i)) → (∀ σ i, frVec Y P rfl σ i = ∑ j, U σ j i • F.vecAt k z hz hx σ j) → F.Lies z P := by
  intro E _ _ _ H Dw l Xo c O _ β Y Z π F hT S _ _ P z k hz hx U hU hd hv
  obtain ⟨Q, hQ⟩ := hT.exists_chartFr (frX_snd P) hx k hz
  have hQx : frX Q ≫ Y.j = frX P ≫ Y.j := hQ.over.trans hx
  have hv' : ∀ σ i, frVec Y P rfl σ i = ∑ j, U σ j i • frVec Y Q hQx σ j := fun σ i => by
    rw [hQ.frVec_eq hx hQx]; exact hv σ i
  have e : P.x = Q.x := by
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd P) (frX_snd Q) hQx.symm]
  have hB : ∃ t, FrBor t Q P := by
    have hM := F.inM hz hx
    clear hv hQ
    revert hv' hQx hM
    obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P
    dsimp only at e
    subst e
    intro hQx hv' hM
    obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
    exact ⟨_, frBor_of_frVec hM hQx rfl
      (fun ix => match ix with | none => u0 | some p => (hd p.1 p.2).unit) U hU (fun _ _ => rfl) hv' fun _ => hu0⟩
  obtain ⟨t, ht⟩ := hB
  exact hQ.lies.frBor ht

end GlobalTheory.FlagMod.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassCartierDivisorPullbackEqPullbackStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardClass_cartierDivisorPullback_eq_pullback : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (D₀ : CartierDiv W) (D₁ : CartierDiv M), (∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g)) → cls (toLB D₁) (isLB_toLB D₁) = CechPic.pull f (cls (toLB D₀) (isLB_toLB D₀)) := by
  first | exact @GlobalTheory.PullCartier.cls_toLB_pull | exact GlobalTheory.PullCartier.cls_toLB_pull | (intros; apply GlobalTheory.PullCartier.cls_toLB_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackCartierDivisorBundleEqStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardPullback_cartierDivisorBundle_eq : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W),
    (∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    CechPic.pull q (cls (toLB E) (isLB_toLB E)) = cls (toLB D) (isLB_toLB D) := by
  first | exact @GlobalTheory.Cartier.PullPres.pull_cls_toLB | exact GlobalTheory.Cartier.PullPres.pull_cls_toLB | (intros; apply GlobalTheory.Cartier.PullPres.pull_cls_toLB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroStalkCompactFlagSpaceOverComponentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charZero_stalk_compactFlagSpaceOverComponent : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (y : Y₀ TF.X Z), CharZero ((Y₀ TF.X Z).presheaf.stalk y) := by
  first | exact @GlobalTheory.CompHS.charZero_stalk_Y₀ | exact GlobalTheory.CompHS.charZero_stalk_Y₀ | (intros; apply GlobalTheory.CompHS.charZero_stalk_Y₀ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHoldsStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_statement_holds : ChartSt := by
  first | exact @GlobalTheory.FlatModel.chartSt | exact GlobalTheory.FlatModel.chartSt | (intros; apply GlobalTheory.FlatModel.chartSt <;> assumption)
end

