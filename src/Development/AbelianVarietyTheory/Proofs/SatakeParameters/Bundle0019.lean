import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0018
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0013
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsContinuousForgetForget
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyEquivEllAdicCohomology

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmpBijectiveIff
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.FormalInv.Fib

variable {O : Type} [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω]

abbrev toBase {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) (C : Type) [CommRing C]
    [Algebra A C] : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ g

theorem toBase_comp {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) {C B : Type}
    [CommRing C] [Algebra A C] [CommRing B] [Algebra A B] (u : C →ₐ[A] B) :
    Spec.map (CommRingCat.ofHom (u : C →+* B)) ≫ toBase g C = toBase g B := by
  rw [toBase, toBase, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

abbrev fib {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) (C : Type) [CommRing C]
    [Algebra A C] : Scheme.{0} :=
  GlobalTheory.NCyc.gfib Ω (toBase g C)

def fibMap {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) {C B : Type}
    [CommRing C] [Algebra A C] [CommRing B] [Algebra A B] (u : C →ₐ[A] B) : fib Ω g B ⟶ fib Ω g C :=
  GlobalTheory.NCyc.gfibMap Ω (Spec.map (CommRingCat.ofHom (u : C →+* B))) (toBase_comp g u)

def fibStr {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) (C : Type) [CommRing C]
    [Algebra A C] : fib Ω g C ⟶ GlobalTheory.NCyc.gfib Ω g :=
  GlobalTheory.NCyc.gfibMap Ω (Spec.map (CommRingCat.ofHom (algebraMap A C))) rfl

theorem fibMap_comp {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) {C B D : Type}
    [CommRing C] [Algebra A C] [CommRing B] [Algebra A B] [CommRing D] [Algebra A D] (u : C →ₐ[A] B)
    (v : B →ₐ[A] D) : fibMap Ω g (v.comp u) = fibMap Ω g v ≫ fibMap Ω g u := by
  apply pullback.hom_ext
  · simp only [fibMap, Category.assoc, GlobalTheory.NCyc.gfibMap_fst, GlobalTheory.NCyc.gfibMap_fst_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  · simp only [fibMap, Category.assoc, GlobalTheory.NCyc.gfibMap_snd]

theorem fibMap_str {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) {C B : Type}
    [CommRing C] [Algebra A C] [CommRing B] [Algebra A B] (u : C →ₐ[A] B) :
    fibMap Ω g u ≫ fibStr Ω g C = fibStr Ω g B := by
  apply pullback.hom_ext
  · simp only [fibMap, fibStr, Category.assoc, GlobalTheory.NCyc.gfibMap_fst, GlobalTheory.NCyc.gfibMap_fst_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
  · simp only [fibMap, fibStr, Category.assoc, GlobalTheory.NCyc.gfibMap_snd]

end GlobalTheory.FormalInv.Fib

end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.FormalInv.Tors

open GlobalTheory.FormalInv.Fib GlobalTheory.NCyc

variable {O : Type} [CommRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)]
variable (K : Type) [Field K] [Algebra O K] (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
variable [IsAlgClosed Ω] [FaithfulSMul O Ω] [Algebra.IsAlgebraic O Ω]
variable {X : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of O)} {x : SpecialPoint p}

end GlobalTheory.FormalInv.Tors

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismFamilyDirectSummandCancellation
section
namespace GlobalTheory

theorem freeAlgebra_compHom_isScalarTower {k ι W : Type} [Field k] [AddCommGroup W] [Module k W]
    (φ : FreeAlgebra k ι →ₐ[k] Module.End k W) :
    @IsScalarTower k (FreeAlgebra k ι) W _ (Module.compHom W φ.toRingHom).toSMul _ := by
  letI : Module (FreeAlgebra k ι) W := Module.compHom W φ.toRingHom
  refine ⟨fun c r w => ?_⟩
  show φ (c • r) w = c • φ r w
  rw [map_smul]
  rfl

theorem endFamily_cancel : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V)
    (b : ι → Module.End k V') (c : ι → Module.End k U),
    (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) →
      ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by
  intro k ι V V' U _ _ _ _ _ _ _ _ _ _ a b c ⟨e, he⟩
  let φa : (FreeAlgebra k ι) →ₐ[k] Module.End k V := FreeAlgebra.lift k a
  let φb : (FreeAlgebra k ι) →ₐ[k] Module.End k V' := FreeAlgebra.lift k b
  let φc : (FreeAlgebra k ι) →ₐ[k] Module.End k U := FreeAlgebra.lift k c
  letI iV : Module (FreeAlgebra k ι) V := Module.compHom V φa.toRingHom
  letI iV' : Module (FreeAlgebra k ι) V' := Module.compHom V' φb.toRingHom
  letI iU : Module (FreeAlgebra k ι) U := Module.compHom U φc.toRingHom
  haveI tV : IsScalarTower k (FreeAlgebra k ι) V := freeAlgebra_compHom_isScalarTower φa
  haveI tV' : IsScalarTower k (FreeAlgebra k ι) V' := freeAlgebra_compHom_isScalarTower φb
  haveI tU : IsScalarTower k (FreeAlgebra k ι) U := freeAlgebra_compHom_isScalarTower φc
  haveI : IsArtinian (FreeAlgebra k ι) U := isArtinian_of_tower k inferInstance
  haveI : IsNoetherian (FreeAlgebra k ι) U := isNoetherian_of_tower k inferInstance

  have key : ∀ r : (FreeAlgebra k ι), ∀ x : V × U, e (φa r x.1, φc r x.2) = (φb r (e x).1, φc r (e x).2) := by
    intro r
    induction r using FreeAlgebra.induction with
    | grade0 s =>
      intro x
      simp only [φa, φb, φc, AlgHom.commutes, Module.algebraMap_end_apply]
      exact e.map_smul s x
    | grade1 i =>
      intro x
      have := he i x
      simp only [φa, φb, φc, FreeAlgebra.lift_ι_apply]
      simpa using this
    | mul r s hr hs =>
      intro x
      have h1 := hs x
      have h2 := hr (φa s x.1, φc s x.2)
      simp only [map_mul, Module.End.mul_apply]
      rw [h2, h1]
    | add r s hr hs =>
      intro x
      have h1 := hr x
      have h2 := hs x
      have hsum : ((φa (r + s)) x.1, (φc (r + s)) x.2)
          = ((φa r) x.1, (φc r) x.2) + ((φa s) x.1, (φc s) x.2) := by
        simp [map_add]
      rw [hsum, map_add, h1, h2]
      simp [map_add]
  let eR : (V × U) ≃ₗ[(FreeAlgebra k ι)] (V' × U) :=
    { e.toAddEquiv with
      map_smul' := fun r x => key r x }
  obtain ⟨f⟩ := GlobalTheory.T.cancel_artinian_noetherian_summand (FreeAlgebra k ι) V V' U ⟨eR⟩
  refine ⟨f.restrictScalars k, fun i x => ?_⟩
  have h : f (FreeAlgebra.ι k i • x) = FreeAlgebra.ι k i • f x := f.map_smul _ _
  change f (φa (FreeAlgebra.ι k i) x) = φb (FreeAlgebra.ι k i) (f x) at h
  simp only [φa, φb, FreeAlgebra.lift_ι_apply] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalSubringMonicRootsResidueStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_subring_monic_roots_residue : ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] (φ : k →+* K) (R : Subring K) (𝔪 : Ideal R),
    φ.range ≤ R → 𝔪.IsMaximal → (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) →
    (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) → (∀ x : K, IsIntegral R x → x ∈ R) →
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  first | (exact @GlobalTheory.LocInField.exists_local_subring) | (exact GlobalTheory.LocInField.exists_local_subring) | (intros; apply GlobalTheory.LocInField.exists_local_subring  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution
section
open Polynomial

namespace GlobalTheory.InertNorm

theorem isAdicComplete_map_of_finite {O : Type} [CommRing O] [IsNoetherianRing O] (I : Ideal O)
    [IsAdicComplete I O] (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    IsAdicComplete (I.map (algebraMap O R)) R := by
  rw [IsAdicComplete.map_algebraMap_iff]
  have : IsHausdorff I R := IsHausdorff.of_le_jacobson I R (IsAdicComplete.le_jacobson_bot I)
  have : IsPrecomplete I R := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module I R
  exact ⟨⟩

theorem finite_quotient_map_of_finite {O : Type} [CommRing O] (I : Ideal O) [Finite (O ⧸ I)]
    (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    Finite (R ⧸ I.map (algebraMap O R)) := by
  have : Module.Finite O (R ⧸ I.map (algebraMap O R)) := inferInstance
  have : Module.Finite (O ⧸ I) (R ⧸ I.map (algebraMap O R)) :=
    Module.Finite.of_restrictScalars_finite O (O ⧸ I) _
  exact Module.finite_of_finite (O ⧸ I)

theorem exists_dvd_mul_map_sub_X : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] (c : O →+* O), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) → ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X := by
  intro O _ _ I _ _ c hcc hcI hω f hf hfc hf0
  have : Module.Finite O (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  let J : Ideal (AdjoinRoot f) := I.map (algebraMap O (AdjoinRoot f))
  have : IsAdicComplete J (AdjoinRoot f) := isAdicComplete_map_of_finite I (AdjoinRoot f)
  have : Finite (AdjoinRoot f ⧸ J) := finite_quotient_map_of_finite I (AdjoinRoot f)

  have hev : f.eval₂ ((AdjoinRoot.of f).comp c) (AdjoinRoot.root f) = 0 := by
    rw [← Polynomial.eval₂_map, hfc, AdjoinRoot.eval₂_root]
  let c' : AdjoinRoot f →+* AdjoinRoot f :=
    AdjoinRoot.lift ((AdjoinRoot.of f).comp c) (AdjoinRoot.root f) hev
  have hc'mk : ∀ p : Polynomial O, c' (AdjoinRoot.mk f p) = AdjoinRoot.mk f (p.map c) := by
    intro p
    simp only [c', AdjoinRoot.lift_mk]
    rw [← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
  have hc'of : ∀ x : O, c' (algebraMap O (AdjoinRoot f) x) = algebraMap O (AdjoinRoot f) (c x) := by
    intro x
    simp only [AdjoinRoot.algebraMap_eq, c', AdjoinRoot.lift_of, RingHom.comp_apply]
  have hcomp : c.comp c = RingHom.id O := RingHom.ext hcc
  have hinv : ∀ y, c' (c' y) = y := by
    intro y
    induction y using AdjoinRoot.induction_on with
    | ih p => rw [hc'mk, hc'mk, Polynomial.map_map, hcomp, Polynomial.map_id]
  have hJ : ∀ y ∈ J, c' y ∈ J := by
    have : J ≤ J.comap c' := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, hc'of]
      exact Ideal.mem_map_of_mem _ (hcI x hx)
    exact fun y hy => this hy
  have hω' : ∃ ω, IsUnit (ω - c' ω) := by
    obtain ⟨ω, hu⟩ := hω
    refine ⟨algebraMap O (AdjoinRoot f) ω, ?_⟩
    rw [hc'of, ← map_sub]
    exact hu.map _
  have hroot : c' (AdjoinRoot.root f) = AdjoinRoot.root f := AdjoinRoot.lift_root _

  have hunit : IsUnit (AdjoinRoot.root f) := by
    have h0 : (f - Polynomial.C (f.coeff 0)).coeff 0 = 0 := by simp
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    have hm : AdjoinRoot.root f * AdjoinRoot.mk f q = -AdjoinRoot.of f (f.coeff 0) := by
      have := congrArg (AdjoinRoot.mk f) hq
      rw [map_sub, AdjoinRoot.mk_self, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, zero_sub] at this
      exact this.symm
    exact isUnit_of_mul_isUnit_left (hm ▸ (hf0.map (AdjoinRoot.of f)).neg)
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_norm_eq_fixed_unit_henselian (AdjoinRoot f) J c' hinv hJ hω' (AdjoinRoot.root f) hroot hunit
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨p, ?_⟩
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_mul, ← hc'mk, hx, AdjoinRoot.mk_X, sub_self]

end GlobalTheory.InertNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPolynomialSubringMaximalIntegralStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomialSubring_maximal_integral : ∀ (k K : Type) [Field k] [Field K] (φ : k →+* K), ∃ (D : Subring K) (m₀ : Ideal D), φ.range ≤ D ∧ m₀.IsMaximal ∧
    (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) ∧ ∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x) := by
  first | exact @GlobalTheory.exists_polySubring_maximal_integral | exact GlobalTheory.exists_polySubring_maximal_integral | (intros; apply GlobalTheory.exists_polySubring_maximal_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaElementEqOneOrLiesAboveFinitePlace
section
open NumberField IsDedekindDomain Neutral.HilbertClassField

namespace GlobalTheory

theorem inertiaEl_eq_one_or_liesAbove : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω),
    ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → g = 1 ∨ ∃ v : HeightOneSpectrum (𝓞 E), LiesAbove A v := by
  intro E Ω _ _ _ _ _ A g hg
  have hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x =>
    ReciprocityTheory.ChartRestriction.L1.mem_of_isIntegral A ((NumberField.RingOfIntegers.isIntegral_coe x).algebraMap)
  let φ : 𝓞 E →+* A := RingHom.codRestrict ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)) A hint
  let I : Ideal (𝓞 E) := Ideal.comap φ (IsLocalRing.maximalIdeal A)
  have hI : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A.nonunits ↔ x ∈ I := by
    intro x
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal, Ideal.mem_comap]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hint x, h⟩
  by_cases hbot : I = ⊥
  · left
    have hE : ∀ y : E, algebraMap E Ω y ∈ A := by
      intro y
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have hbn : algebraMap E Ω (algebraMap (𝓞 E) E b) ∉ A.nonunits := by
        rw [show algebraMap (𝓞 E) E b = (b : E) from rfl, hI, hbot, Ideal.mem_bot]; exact hb0
      have hbinv : (algebraMap E Ω (algebraMap (𝓞 E) E b))⁻¹ ∈ A := by
        rw [ValuationSubring.mem_nonunits_iff_or] at hbn
        push_neg at hbn; exact hbn.2
      rw [map_div₀, div_eq_mul_inv]
      exact mul_mem (hint a) hbinv
    have hall : ∀ x : Ω, x ∈ A := by
      intro x
      have hx : IsIntegral E x := ((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic x).isIntegral
      obtain ⟨p, hpm, hp⟩ := hx
      let ψ : E →+* A := RingHom.codRestrict (algebraMap E Ω) A hE
      have hcomp : (algebraMap A Ω).comp ψ = algebraMap E Ω := by ext; rfl
      have h1 : IsIntegral A x := ⟨p.map ψ, hpm.map ψ, by rw [Polynomial.eval₂_map, hcomp]; exact hp⟩
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
      rw [← hy]; exact y.2
    ext x
    have h := hg.2 x (hall x)
    rw [ValuationSubring.mem_nonunits_iff_or] at h
    rcases h with h | h
    · simpa [sub_eq_zero] using h
    · exact absurd (hall _) h
  · right
    exact ⟨⟨I, Ideal.IsPrime.comap φ, hbot⟩, fun x => hI x⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralClosureMaximalResidueOfAlgClosedStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_maximal_residue_of_algClosed : ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] (φ : k →+* K) (D : Subring K) (m₀ : Ideal D),
    φ.range ≤ D → m₀.IsMaximal → (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) →
    (∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x)) →
    ∃ (R : Subring K) (𝔪 : Ideal R), φ.range ≤ R ∧ 𝔪.IsMaximal ∧ (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) ∧
      (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) ∧ ∀ x : K, IsIntegral R x → x ∈ R := by
  first | exact @GlobalTheory.integralClosure_maximal_residue_algClosed | exact GlobalTheory.integralClosure_maximal_residue_algClosed | (intros; apply GlobalTheory.integralClosure_maximal_residue_algClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthIntegralCocyclesRationalCoboundariesLe
section
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

namespace GlobalTheory

theorem cocycle_bound_length_le : ∀ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (Z : Submodule O (G → V)), (∀ c ∈ Z, ∀ g, c g ∈ L.T) → Module.length O (↥(Z ⊓ (B1 ρ).restrictScalars O) ⧸ (latticeCoboundaries L).comap (Z ⊓ (B1 ρ).restrictScalars O).subtype) ≤ Module.length O ↥(Representation.invariants (repD L)) := by
  intro G _ LL _ O _ _ V _ _ _ _ ρ L Z hZ
  set M := Z ⊓ (B1 ρ).restrictScalars O with hM
  set K := (latticeCoboundaries L).comap M.subtype with hK

  let χ : V →ₗ[O] (G → V) ⧸ latticeCoboundaries L := (latticeCoboundaries L).mkQ ∘ₗ (cob ρ).restrictScalars O
  have hχ : L.T ≤ LinearMap.ker χ := by
    intro t ht
    simp only [LinearMap.mem_ker, χ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨t, ht, rfl⟩
  let ψ : ↥(Representation.invariants (repD L)) →ₗ[O] (G → V) ⧸ latticeCoboundaries L :=
    (L.T.liftQ χ hχ) ∘ₗ (Representation.invariants (repD L)).subtype
  let ι : M →ₗ[O] (G → V) ⧸ latticeCoboundaries L := (latticeCoboundaries L).mkQ ∘ₗ M.subtype
  have hKι : K ≤ LinearMap.ker ι := by
    intro x hx
    simpa [ι, K, Submodule.Quotient.mk_eq_zero] using hx
  let f : (M ⧸ K) →ₗ[O] (G → V) ⧸ latticeCoboundaries L := K.liftQ ι hKι
  have hfinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K x
    simp only [LinearMap.mem_ker, f, Submodule.liftQ_apply, ι, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, K, Submodule.mem_comap,
      Submodule.coe_subtype]
    exact hx
  have hrange : LinearMap.range f ≤ LinearMap.range ψ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨⟨c, hcM⟩, rfl⟩ := Submodule.Quotient.mk_surjective K x
    obtain ⟨hcZ, hcB⟩ := hcM
    obtain ⟨v, hv⟩ := hcB
    have hinv : L.T.mkQ v ∈ Representation.invariants (repD L) := by
      intro g
      change (Submodule.Quotient.mk ((ρ g) v) : V ⧸ L.T) = Submodule.Quotient.mk v
      rw [Submodule.Quotient.eq]
      have := hZ c hcZ g
      rw [← hv] at this
      simpa [cob] using this
    refine ⟨⟨_, hinv⟩, ?_⟩
    simp [ψ, f, ι, χ, hv]
  calc Module.length O (M ⧸ K) ≤ Module.length O (LinearMap.range ψ) :=
        Module.length_le_of_injective ((Submodule.inclusion hrange).comp f.rangeRestrict) (by
          intro a b hab
          apply hfinj
          have := congrArg Subtype.val hab
          simpa using this)
    _ ≤ _ := Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemPowHeightOneIdealIffDvdEmbeddingStatement
section
open NumberField IsDedekindDomain WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_pow_heightOneIdeal_iff_dvd_embedding : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)) (x : 𝓞 E) (y : W) (k : ℕ), ρ x = algebraMap W Qq y → (x ∈ P.asIdeal ^ k ↔ (p : W) ^ k ∣ y) := by
  first | exact @GlobalTheory.ordIdeal_of_embedding | exact GlobalTheory.ordIdeal_of_embedding | (intros; apply GlobalTheory.ordIdeal_of_embedding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullPreservesFiniteLimits
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Rel

set_option backward.isDefEq.respectTransparency.types false in

theorem pull_preservesFiniteLimits (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : Y ⟶ X) :
    PreservesFiniteLimits (pull R f) := by
  have : AB5OfSize.{0, 1} (ModuleCat.{1} (ULift.{1} R)) := AB5OfSize_of_univLE.{0, 1, 1, 1} _
  have hf (U : Y.Etaleᵒᵖ) : IsFiltered (CostructuredArrow (bc f).op U) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (bc f) (unop U))
  have : PreservesFiniteLimits ((bc f).op.lan : (_ ⥤ _ ⥤ ModuleCat.{1} (ULift.{1} R))) :=
    GlobalTheory.Et.Small.lan_preservesFiniteLimits _ _ (fun U => by have := hf U; infer_instance)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits (bc f) _ _ _

end GlobalTheory.EtC.Rel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QBinomialSumCardQuotientSubspacesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qBinomial_sum_card_quotient_subspaces : ∀ (k V : Type) [Field k] [Finite k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (X : ℂ), ∑ j ∈ Finset.range (Module.finrank k V + 1), (-1 : ℂ) ^ j * (Nat.card k : ℂ) ^ (j * (j - 1) / 2) * (Nat.card {W : Submodule k V // Module.finrank k (V ⧸ W) = j} : ℂ) * X ^ j = ∏ i ∈ Finset.range (Module.finrank k V), (1 - (Nat.card k : ℂ) ^ i * X) := by
  first | exact @GlobalTheory.qBinomial_subspaces | exact GlobalTheory.qBinomial_subspaces | (intros; apply GlobalTheory.qBinomial_subspaces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SurjectiveAlgebraMapAdicCompletionCompleteDvrStatement
section
open NumberField IsDedekindDomain WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_algebraMap_adicCompletion_complete_dvr : ∀ {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (π : W) (hπ : Irreducible π) (hc : IsAdicComplete (Ideal.span {π}) W) (v : HeightOneSpectrum W), Function.Surjective (algebraMap Qq (v.adicCompletion Qq)) := by
  first | exact @GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion | exact GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion | (intros; apply GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion <;> assumption)
end

