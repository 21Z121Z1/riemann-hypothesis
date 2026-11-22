import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0018
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointTwistedHermUnimodularEqSelfDual
section
namespace GlobalTheory.UnitLemma.TwistUnitAny

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem stable_of_unimodular (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (ε : B.A) (hε : ε = 1 ∨ ε = -1)
    (β x : B.A) (hβ : B.σ β = β * (ε * B.g)) (hx : B.σ x = x) (L : Submodule K.O B.A)
    (hU : ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm (β * x) y z ∈ (algebraMap K.O K.E).range) :
    ∀ y ∈ L, B.g * y ∈ L := by
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hsym : ∀ a b : B.A, T (β * x * a * B.σ b) ∈ R ↔ T (β * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← TwistUnit.trace_σ_mem B (β * x * a * B.σ b),
      show B.σ (β * x * a * B.σ b) = ε * (β * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  simp only [InvAlg.herm, ← hT, ← hR] at hU
  have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
    intro y hy
    rw [hU]
    intro y' hy'
    rw [hsym, show β * x * (B.g * (B.σ B.g * y)) * B.σ y' = β * x * y * B.σ y' by
      linear_combination (β * x * y * B.σ y') * hg]
    exact (hU y').1 hy' y hy
  intro y hy
  rw [hU]
  intro y' hy'
  have hb : B.σ B.g * (B.σ B.g * y') ∈ L := h1 _ (h1 y' hy')
  have := (hU _).1 hb y hy
  rw [hsym] at this
  rw [show β * x * y' * B.σ (B.g * y) = β * x * (B.g * (B.σ B.g * (B.σ B.g * y'))) * B.σ y by
    rw [map_mul]; linear_combination (-(β * x * y' * B.σ B.g * B.σ y)) * hg]
  exact this

theorem twisted_unit_eq_unit_any : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable →
    ∀ ε : B.A, (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs ε hε
  by_cases hi : IsIntegral K.O B.g
  · exact TwistUnit.twisted_unit_eq_unit K B hg hs hi ε hε
  have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hu : (ε * B.g) * B.σ (ε * B.g) = 1 := by
    rw [map_mul, hσε]; linear_combination B.g * B.σ B.g * hεε + hg
  obtain ⟨β₀, hβ⟩ := GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma K B (ε * B.g) hu
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  ext L
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hLat, hU⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g
      (stable_of_unimodular B hg ε hε β₀ x hβ hx L hU)) hi
  · rintro ⟨hLat, h2, -⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g h2) hi

end GlobalTheory.UnitLemma.TwistUnitAny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicVectorOfSeparableCharpoly
section
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem exists_cyclicVector_of_separable_charpoly {K : Type} [Field K] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v₀ : Fin n → K, ∀ u : Fin n → K, ∃ p : K[X], u = aeval γ p *ᵥ v₀ := by
  have hs' : (Matrix.toLin' γ).charpoly.Separable := by rwa [Matrix.charpoly_toLin']
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector K (Fin n → K) (Matrix.toLin' γ) hs'
  refine ⟨e, fun u => ?_⟩
  obtain ⟨p, hp⟩ := he u
  refine ⟨p, ?_⟩
  rw [← hp]
  have h : aeval (Matrix.toLin' γ) p = Matrix.toLin' (aeval γ p) := by
    have := (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toAlgHom γ p).symm
    exact this.symm
  rw [h, Matrix.toLin'_apply]

end GlobalTheory.LatOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetLineCoordinateIsoStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_det_line_coordinate_iso : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (σ : Λ →+* O) (q : eig C ρ σ ≃ₗ[C] (Fin N → C)), (∀ x, x ∈ quotLattice C ρ σ ↔ ∀ i, q x i ∈ (algebraMap O C).range) → ∃ δ : detLine C ρ σ N ≃ₗ[C] C, (∀ x : Fin N → eig C ρ σ, δ (exteriorPower.ιMulti C N x) = (Matrix.of fun i => q (x i)).det) ∧ ∀ w, w ∈ detLattice C ρ σ N ↔ δ w ∈ (algebraMap O C).range := by
  first | exact @GlobalTheory.detLine_coord | exact GlobalTheory.detLine_coord | (intros; apply GlobalTheory.detLine_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLiftGenericFibreOfFactorization
section
open CategoryTheory Limits

noncomputable section

namespace GlobalTheory.GenFibLift

open GlobalTheory.LocAcyc

theorem genFibMap_comp {T E F O : Type} [CommRing T] [CommRing E] [CommRing F] [CommRing O]
    [Algebra T E] [Algebra T F] [Algebra T O] (φ : E →ₐ[T] F) (ψ : F →ₐ[T] O) :
    genFibMap (ψ.comp φ) = (genFibMap ψ).comp (genFibMap φ) :=
  genFib_ringHom_ext (fun e => by
    simp only [RingHom.comp_apply, genFibMap_algebraMap, AlgHom.comp_apply])

def den {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (t : nonZeroDivisors T) :
    Algebra.algebraMapSubmonoid O (nonZeroDivisors T) :=
  ⟨algebraMap T O t, Submonoid.mem_map_of_mem _ t.2⟩

@[simp] theorem den_coe {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (t : nonZeroDivisors T) :
    ((den (O := O) t : Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) : O) = algebraMap T O t := rfl

theorem exists_mk' {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (x : GenFib T O) :
    ∃ (a : O) (t : nonZeroDivisors T), x = IsLocalization.mk' (GenFib T O) a (den t) := by
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) x
  obtain ⟨t, ht, hm⟩ := Submonoid.mem_map.1 m.2
  refine ⟨a, ⟨t, ht⟩, ?_⟩
  rw [show m = den ⟨t, ht⟩ from Subtype.ext hm.symm]

theorem exists_of_mk'_eq_zero {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (a : O)
    (m : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    (h : IsLocalization.mk' (GenFib T O) a m = 0) :
    ∃ t : nonZeroDivisors T, algebraMap T O t * a = 0 := by
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff a m).1 h
  obtain ⟨t, ht, hct⟩ := Submonoid.mem_map.1 c.2
  exact ⟨⟨t, ht⟩, by simpa [hct] using hc⟩

theorem genFibMap_mk' {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E]
    [Algebra T O] (ψ : E →ₐ[T] O) (e : E) (t : nonZeroDivisors T) :
    genFibMap ψ (IsLocalization.mk' (GenFib T E) e (den t)) =
      IsLocalization.mk' (GenFib T O) (ψ e) (den t) := by
  simp only [genFibMap, IsLocalization.map_mk']
  congr 1
  ext
  simp

theorem exists_finitePresentation_lift (T R O : Type) [CommRing T] [CommRing R] [CommRing O]
    [Algebra T R] [Algebra R O] [Algebra T O] [IsScalarTower T R O]
    (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GenFib T O) :
    ∃ (Z : Type) (_ : CommRing Z) (_ : Algebra R Z) (_ : Algebra T Z) (_ : IsScalarTower T R Z)
      (_ : Algebra.FinitePresentation R Z) (g : Z →ₐ[R] O) (w : U →+* GenFib T Z),
      (genFibMap (g.restrictScalars T)).comp w = u := by
  haveI : Algebra.FinitePresentation ℤ U := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, f, hf, s, hs⟩ := Algebra.FinitePresentation.out (R := ℤ) (A := U)

  choose a t ht using fun i : Fin n => exists_mk' (T := T) (u (f (MvPolynomial.X i)))
  let e : MvPolynomial (Fin n) R →ₐ[R] O := MvPolynomial.aeval a
  let θ : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R) :=
    MvPolynomial.eval₂Hom (Int.castRingHom _)
      (fun i => IsLocalization.mk' _ (MvPolynomial.X i : MvPolynomial (Fin n) R) (den (t i)))
  have key : (genFibMap (e.restrictScalars T)).comp θ = u.comp f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int
        (((genFibMap (e.restrictScalars T)).comp θ).comp MvPolynomial.C)
        ((u.comp f.toRingHom).comp MvPolynomial.C)) r
    · intro i
      simp only [RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_X', genFibMap_mk']
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ht i]
      simp [e]

  have hrel : ∀ r : s, ∃ (p : MvPolynomial (Fin n) R) (τ τ' : nonZeroDivisors T),
      θ r = IsLocalization.mk' _ p (den τ) ∧ e (algebraMap T _ τ' * p) = 0 := by
    intro r
    obtain ⟨p, τ, hp⟩ := exists_mk' (T := T) (θ r)
    have h0 : genFibMap (e.restrictScalars T) (θ r) = 0 := by
      have hr : (r : MvPolynomial (Fin n) ℤ) ∈ RingHom.ker f.toRingHom := hs ▸ Ideal.subset_span r.2
      rw [← RingHom.comp_apply, key, RingHom.comp_apply, RingHom.mem_ker.1 hr, map_zero]
    rw [hp, genFibMap_mk'] at h0
    obtain ⟨τ', hτ'⟩ := exists_of_mk'_eq_zero _ _ h0
    refine ⟨p, τ, τ', hp, ?_⟩
    rw [map_mul, ← hτ']
    simp [IsScalarTower.algebraMap_apply T R (MvPolynomial (Fin n) R),
      IsScalarTower.algebraMap_apply T R O]
  choose p τ τ' hθ he using hrel
  let I : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.span (Set.range fun r : s => algebraMap T _ (τ' r : T) * p r)
  have hIe : ∀ x ∈ I, e x = 0 := by
    intro x hx
    have hle : I ≤ RingHom.ker e := Ideal.span_le.2 (by rintro _ ⟨r, rfl⟩; exact he r)
    exact hle hx
  haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R) :=
    Algebra.FinitePresentation.mvPolynomial R R (Fin n)
  haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  let g : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] O := Ideal.Quotient.liftₐ I e hIe
  let q : MvPolynomial (Fin n) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) := Ideal.Quotient.mkₐ R I
  let w0 : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R ⧸ I) :=
    (genFibMap (q.restrictScalars T)).comp θ
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker w0 := by
    rw [← hs, Ideal.span_le]
    intro r hr
    rw [SetLike.mem_coe, RingHom.mem_ker]
    simp only [w0, RingHom.comp_apply]
    rw [hθ ⟨r, hr⟩, genFibMap_mk']
    have hu : IsUnit (algebraMap (MvPolynomial (Fin n) R ⧸ I) (GenFib T (MvPolynomial (Fin n) R ⧸ I))
        (algebraMap T _ (τ' ⟨r, hr⟩ : T))) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)) _ (den _)
    refine (hu.mul_right_eq_zero).1 ?_
    rw [← IsLocalization.mk'_one (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)),
      ← IsLocalization.mk'_mul, one_mul]
    have hz : (q.restrictScalars T) (algebraMap T _ (τ' ⟨r, hr⟩ : T) * p ⟨r, hr⟩) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩)
    rw [map_mul, AlgHom.commutes] at hz
    rw [hz, IsLocalization.mk'_zero]

  refine ⟨MvPolynomial (Fin n) R ⧸ I, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, g, RingHom.liftOfSurjective f.toRingHom hf ⟨w0, hker⟩, ?_⟩
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := hf x
  have hy : f y = f.toRingHom y := rfl
  rw [RingHom.comp_apply, hy, RingHom.liftOfSurjective_comp_apply]
  have hgq : (g.restrictScalars T).comp (q.restrictScalars T) = e.restrictScalars T := by
    exact AlgHom.ext fun x => AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I e hIe) x
  have hcomp : (genFibMap (g.restrictScalars T)).comp w0 = u.comp f.toRingHom := by
    simp only [w0]
    rw [← RingHom.comp_assoc, ← genFibMap_comp, hgq, key]
  exact RingHom.congr_fun hcomp y

theorem exists_etale_genFib_lift : ∀ (T R O : Type) [CommRing T] [CommRing R] [CommRing O]
    [Algebra T R] [Algebra R O] [Algebra T O] [IsScalarTower T R O],
    (∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
      ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
        (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g) →
    ∀ (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GlobalTheory.LocAcyc.GenFib T O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra T W) (_ : IsScalarTower T R W)
      (_ : Algebra.Etale R W) (ψ : W →ₐ[R] O) (uW : U →+* GlobalTheory.LocAcyc.GenFib T W),
      (GlobalTheory.LocAcyc.genFibMap (ψ.restrictScalars T)).comp uW = u := by
  intro T R O _ _ _ _ _ _ _ H U _ _ u
  obtain ⟨Z, _, _, _, _, _, g, w, hw⟩ := exists_finitePresentation_lift T R O U u
  obtain ⟨W, _, _, _, u0, v, hv⟩ := H Z g
  letI : Algebra T W := ((algebraMap R W).comp (algebraMap T R)).toAlgebra
  haveI hTRW : IsScalarTower T R W := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨W, inferInstance, inferInstance, inferInstance, hTRW, inferInstance, v,
    (genFibMap (u0.restrictScalars T)).comp w, ?_⟩
  rw [← RingHom.comp_assoc, ← genFibMap_comp]
  have hvu : (v.restrictScalars T).comp (u0.restrictScalars T) = g.restrictScalars T :=
    AlgHom.ext fun z => AlgHom.congr_fun hv z
  rw [hvu, hw]

end GlobalTheory.GenFibLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalEqOfMultiplicativeOnPoints
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_smul_fun_eq_eval_points (O C A : Type) [CommRing O] [IsDomain O] [Field C]
    [Algebra O C] [IsFractionRing O C] [CommRing A] [Algebra O A] [Module.Finite O A]
    [Module.Free O A] (κ : (A →ₐ[O] C) → C) :
    ∃ (d : O) (a : A), d ≠ 0 ∧ ∀ x : A →ₐ[O] C, x a = algebraMap O C d * κ x := by
  classical
  have hli : LinearIndependent C (fun x : A →ₐ[O] C => x.toLinearMap) :=
    linearIndependent_algHom_toLinearMap O A C
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    (Finsupp.linearCombination C (fun x : A →ₐ[O] C => x.toLinearMap))
    (LinearMap.ker_eq_bot.mpr hli)
  let l : (A →ₗ[O] C) →ₗ[C] C := Finsupp.linearCombination C κ ∘ₗ g
  have hl : ∀ x : A →ₐ[O] C, l x.toLinearMap = κ x := by
    intro x
    have := LinearMap.congr_fun hg (Finsupp.single x 1)
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      LinearMap.id_apply] at this
    simp only [l, LinearMap.comp_apply, this, Finsupp.linearCombination_single, one_smul]
  let B := Module.Free.chooseBasis O A
  let c := fun i => l (Algebra.linearMap O C ∘ₗ B.coord i)
  have hc : ∀ f : A →ₗ[O] C, l f = ∑ i, f (B i) * c i := by
    intro f
    have : f = ∑ i, f (B i) • (Algebra.linearMap O C ∘ₗ B.coord i) := by
      refine B.ext fun j => ?_
      rw [LinearMap.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Finsupp.single_apply, hij.symm]
      · simp
    conv_lhs => rw [this]
    simp only [map_sum, map_smul, smul_eq_mul, c]
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) c
  choose o ho using hd
  refine ⟨d, ∑ i, o i • B i, nonZeroDivisors.coe_ne_zero d, fun x => ?_⟩
  rw [← hl, hc, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, ho, Algebra.smul_def]
  simp only [AlgHom.toLinearMap_apply]
  ring

open scoped TensorProduct in
private lemma eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced {C V : Type} [Field C] [IsAlgClosed C] [CommRing V]
    [Algebra C V] [Module.Finite C V] [IsReduced V] (v : V) (hv : ∀ z : V →ₐ[C] C, z v = 0) :
    v = 0 := by
  haveI : IsArtinianRing V := IsArtinianRing.of_finite C V
  have hmem : v ∈ (⊥ : Ideal V).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    letI : Field (V ⧸ m) := Ideal.Quotient.field m
    have hsurj : Function.Surjective (algebraMap C (V ⧸ m)) := IsSepClosed.algebraMap_surjective C _
    let eqv : C ≃ₐ[C] V ⧸ m := AlgEquiv.ofBijective (Algebra.ofId C (V ⧸ m))
      ⟨(algebraMap C (V ⧸ m)).injective, hsurj⟩
    have h := hv (eqv.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.toAlgHom_eq_coe,
      AlgHom.coe_coe] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ eqv.symm.injective).mp h)
  rw [IsArtinianRing.jacobson_eq_radical] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact IsReduced.eq_zero v ⟨n, by simpa using hn⟩

open scoped TensorProduct in
private lemma exists_eq_one_and_eq_zero_of_ne_algHom {C V : Type} [Field C] [CommRing V] [Algebra C V]
    [Fintype (V →ₐ[C] C)] (z : V →ₐ[C] C) :
    ∃ w : V, z w = 1 ∧ ∀ z' : V →ₐ[C] C, z' ≠ z → z' w = 0 := by
  have hsep : ∀ z' : V →ₐ[C] C, z' ≠ z → ∃ a : V, z a ≠ z' a := by
    intro z' hz'
    by_contra h
    push_neg at h
    exact hz' (AlgHom.ext fun a => (h a).symm)
  classical
  let u : (V →ₐ[C] C) → V := fun z' =>
    if h : z' ≠ z then
      (z (hsep z' h).choose - z' (hsep z' h).choose)⁻¹ •
        ((hsep z' h).choose - algebraMap C V (z' (hsep z' h).choose))
    else 1
  have hu : ∀ z', z (u z') = 1 := by
    intro z'
    by_cases h : z' ≠ z
    · simp only [u, dif_pos h, map_smul, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, smul_eq_mul]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (hsep z' h).choose_spec)
    · simp only [u]
      rw [dif_neg h, map_one]
  have hu' : ∀ z', z' ≠ z → z' (u z') = 0 := by
    intro z' h
    simp only [u]
    rw [dif_pos h]
    simp
  refine ⟨∏ z' ∈ Finset.univ.erase z, u z', ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun z' _ => hu z'
  · intro z' hz'
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hz', Finset.mem_univ _⟩) (hu' z' hz')

open scoped TensorProduct in
private lemma sum_sum_mul_sub_mul_mul_eq_zero_of_sum_mul_eq {C ι : Type} [Field C] [Fintype ι] (c X Y : ι → C)
    (M : ι → ι → ι → C)
    (h : ∑ k, c k * ∑ i, ∑ j, M k i j * (X i * Y j) = (∑ i, c i * X i) * ∑ j, c j * Y j) :
    ∑ j, (∑ i, (∑ k, c k * M k i j - c i * c j) * X i) * Y j = 0 := by
  have e1 : ∑ j, (∑ i, (∑ k, c k * M k i j - c i * c j) * X i) * Y j =
      ∑ k, c k * ∑ i, ∑ j, M k i j * (X i * Y j) - (∑ i, c i * X i) * ∑ j, c j * Y j := by
    simp only [Finset.sum_mul, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    congr 1
    · conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, h, sub_self]

open scoped TensorProduct in

theorem _root_.GlobalTheory.exists_eval_eq_of_multiplicative_on_points : ∀ (O C A : Type) [CommRing O] [IsDomain O] [Field C] [IsAlgClosed C] [Algebra O C] [IsFractionRing O C] [IsIntegrallyClosed O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Free O A], IsReduced (C ⊗[O] A) → ∀ (Δ : A →ₐ[O] A ⊗[O] A) (ε : A →ₐ[O] O) (κ : (A →ₐ[O] C) → C), (∀ x y : A →ₐ[O] C, κ ((Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)).comp Δ) = κ x * κ y) → κ ((Algebra.ofId O C).comp ε) = 1 → ∃ b : A, ∀ x : A →ₐ[O] C, x b = κ x := by
  intro O C A _ _ _ _ _ _ _ _ _ _ _ hred Δ ε κ hmul _
  classical
  let e := Module.Free.chooseBasis O A
  let eC : Module.Basis (Module.Free.ChooseBasisIndex O A) C (C ⊗[O] A) :=
    Algebra.TensorProduct.basis C e
  let ext : (A →ₐ[O] C) → (C ⊗[O] A →ₐ[C] C) := fun x =>
    Algebra.TensorProduct.lift (Algebra.ofId C C) x (fun _ _ => Commute.all _ _)
  let res : (C ⊗[O] A →ₐ[C] C) → (A →ₐ[O] C) := fun z =>
    (z.restrictScalars O).comp Algebra.TensorProduct.includeRight
  have hres : ∀ x, res (ext x) = x := by
    intro x
    ext a
    simp [res, ext]
  have hevC : ∀ (z : C ⊗[O] A →ₐ[C] C) (a : Module.Free.ChooseBasisIndex O A → C),
      z (∑ i, a i • eC i) = ∑ i, a i * res z (e i) := by
    intro z a
    simp [eC, res, map_sum, Algebra.TensorProduct.basis_apply]
  have hcoord : ∀ a : Module.Free.ChooseBasisIndex O A → C,
      (∀ x : A →ₐ[O] C, ∑ i, a i * x (e i) = 0) → a = 0 := by
    intro a ha
    have hv : ∑ i, a i • eC i = 0 := by
      refine eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced (C := C) _ fun z => ?_
      rw [hevC]
      exact ha (res z)
    funext i
    have hi := congrArg (fun v => eC.repr v i) hv
    simpa [Finsupp.single_apply] using hi
  haveI : Finite (C ⊗[O] A →ₐ[C] C) := (linearIndependent_toLinearMap C (C ⊗[O] A) C).finite
  letI : Fintype (C ⊗[O] A →ₐ[C] C) := Fintype.ofFinite _
  choose w hw1 hw0 using fun z : C ⊗[O] A →ₐ[C] C => exists_eq_one_and_eq_zero_of_ne_algHom z
  let b' : C ⊗[O] A := ∑ z, κ (res z) • w z
  let c := eC.repr b'
  have hval : ∀ x, κ x = ∑ i, c i * x (e i) := by
    intro x
    have h1 : ext x b' = κ x := by
      simp only [b', map_sum, map_smul, smul_eq_mul]
      rw [Finset.sum_eq_single (ext x)]
      · rw [hw1, mul_one, hres]
      · intro z _ hz
        rw [hw0 z (ext x) (Ne.symm hz), mul_zero]
      · simp
    rw [← h1]
    conv_lhs => rw [← eC.sum_repr b']
    rw [hevC, hres]
  let m : Module.Free.ChooseBasisIndex O A → Module.Free.ChooseBasisIndex O A →
      Module.Free.ChooseBasisIndex O A → O := fun k i j => (e.tensorProduct e).repr (Δ (e k)) (i, j)
  have hprod : ∀ (x y : A →ₐ[O] C) k,
      (Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)) (Δ (e k)) =
        ∑ i, ∑ j, algebraMap O C (m k i j) * (x (e i) * y (e j)) := by
    intro x y k
    conv_lhs => rw [← (e.tensorProduct e).sum_repr (Δ (e k))]
    simp only [map_sum, map_smul, Module.Basis.tensorProduct_apply,
      Algebra.smul_def, Fintype.sum_prod_type, map_mul, AlgHom.commutes,
      Algebra.TensorProduct.lift_tmul, m]
  have key : ∀ x y : A →ₐ[O] C, ∑ j, (∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) *
      x (e i)) * y (e j) = 0 := by
    intro x y
    have h := hmul x y
    simp only [hval, AlgHom.comp_apply, hprod] at h
    exact sum_sum_mul_sub_mul_mul_eq_zero_of_sum_mul_eq c (fun i => x (e i)) (fun j => y (e j))
      (fun k i j => algebraMap O C (m k i j)) h
  have hrel : ∀ i j, c i * c j = ∑ k, c k * algebraMap O C (m k i j) := by
    have h1 : ∀ j, ∀ x : A →ₐ[O] C,
        ∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) * x (e i) = 0 := by
      intro j x
      exact congrFun (hcoord (fun j => ∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) *
        x (e i)) (key x)) j
    intro i j
    have h2 := congrFun (hcoord (fun i => ∑ k, c k * algebraMap O C (m k i j) - c i * c j) (h1 j)) i
    exact (sub_eq_zero.mp h2).symm
  let M : Submodule O C := Submodule.span O (insert 1 (Set.range c))
  have hcM : ∀ i, c i ∈ M := fun i => Submodule.subset_span (Set.mem_insert_of_mem 1 ⟨i, rfl⟩)
  have hoM : (1 : C) ∈ M := Submodule.subset_span (Set.mem_insert 1 _)
  have hMM : M * M ≤ M := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    rcases hs with rfl | ⟨i, rfl⟩ <;> rcases ht with rfl | ⟨j, rfl⟩ <;> dsimp only
    · rw [one_mul]
      exact hoM
    · rw [one_mul]
      exact hcM j
    · rw [mul_one]
      exact hcM i
    · rw [hrel]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hcM k)
  let S : Subalgebra O C :=
    M.toSubalgebra hoM fun u v hu hv => hMM (Submodule.mul_mem_mul hu hv)
  have hfg : (Subalgebra.toSubmodule S).FG := Submodule.fg_span ((Set.finite_range c).insert 1)
  have hint : ∀ i, ∃ o : O, algebraMap O C o = c i := fun i =>
    IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_mem_of_fg S hfg _ (hcM i))
  choose o ho using hint
  refine ⟨∑ i, o i • e i, fun x => ?_⟩
  rw [hval, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, ho]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePadicIntDomainEmbeddingStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_padicInt_domain_embedding : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C → (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D), Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by
  first | exact @GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain | exact GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain | (intros; apply GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetsSubalgebraFiniteAffineCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_sets_subalgebra_finite_affine_cover : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by
  first | exact @GlobalTheory.sub_choose_finite | exact GlobalTheory.sub_choose_finite | (intros; apply GlobalTheory.sub_choose_finite <;> assumption)
end

