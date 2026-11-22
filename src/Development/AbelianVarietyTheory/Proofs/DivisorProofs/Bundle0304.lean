import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

def Fits (T O : Type) [CommRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O]
    (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T)
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
    (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)) :
    Prop :=
  Function.Injective i ∧ IsLocalHom i ∧ IsUnit (q : A) ∧
    QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
    ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
      (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA ∧
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA

def Retracts (T O : Type) [CommRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O]
    (A : Type) [CommRing A] (i : A →+* T)
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
    (ρ : Localization.AtPrime QA →+* A) : Prop :=
  ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A ∧
    RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} ∧
    ∀ x : Localization.AtPrime QA,
      algebraMap T O (i (ρ x)) - jA x ∈ Ideal.span {algebraMap (Polynomial T) O Polynomial.X}

def PointAtZero (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (ρ : R →+* A) : Prop :=
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  ∃ s : GlobalTheory.KeyOriginNoeth.closure A R D →+* FractionRing A,
    s.comp (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D)) = (algebraMap A (FractionRing A)).comp ρ

end GlobalTheory.KeyOriginEnlarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulMemSubalgebraOfResBasicOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_mem_subalgebra_of_res_basicOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (T : ∀ j, Set (F.obj (op (V j)))) (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W := by
  first | exact @GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen | exact GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen | (intros; apply GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickeningStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_eq_of_square_zero_thickening : ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (Y : Scheme.{0}) (u w : Sp S ⟶ Y), spMap q ≫ u = spMap q ≫ w → ∀ V : Y.Opens, u ⁻¹ᵁ V = w ⁻¹ᵁ V := by
  first | exact @GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero | exact GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero | (intros; apply GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesCoordinateNearInfinity
section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped Topology

namespace GlobalTheory.PrinTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nL_inv (x : k) : ((nL x)⁻¹ : GL (Fin (1 + 1)) k) = nL (-x) := by
  rw [inv_eq_iff_mul_eq_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem continuous_nL : Continuous (nL : k → GL (Fin (1 + 1)) k) := by
  have h : Continuous fun x : k => ((nL x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [nL_inv]
  exact h.comp continuous_neg

theorem nL_zero : (nL (0 : k) : GL (Fin (1 + 1)) k) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exists_ev_nL_eq {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) :
    ∃ r : kˣ, ∀ z : k, valuation k z < valuation k (r : k) → ev f (nL z) = ev f 1 := by
  have hS : IsOpen {g : GL (Fin (1 + 1)) k | psRep μ₁ μ₂ g f = f} := isSmooth_parInd _ _ f
  have hU : nL ⁻¹' {g : GL (Fin (1 + 1)) k | psRep μ₁ μ₂ g f = f} ∈ 𝓝 (0 : k) :=
    (hS.preimage continuous_nL).mem_nhds (by simp [nL_zero])
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp hU
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hy.symm)
  refine ⟨Units.mk0 y hy0, fun z hz => ?_⟩
  have hz' : psRep μ₁ μ₂ (nL z) f = f := hγ (by rw [← hy]; exact hz)
  rw [← one_mul (nL z), ← ev_act, hz']

theorem coord_eq_of_far : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ,
    ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) →
      GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1 := by
  intro k _ _ _ _ μ₁ μ₂ f
  obtain ⟨r, hr⟩ := exists_ev_nL_eq f
  refine ⟨r⁻¹, fun x hx => ?_⟩
  rw [coord, wE_mul_nU_eq, ev_bor, hr]
  have hx0 : (0 : ValueGroupWithZero k) < valuation k (x : k) := by simp [zero_lt_iff]
  have hr0 : (0 : ValueGroupWithZero k) < valuation k (r : k) := by simp [zero_lt_iff]
  simp only [Units.val_inv_eq_inv_val, map_inv₀] at hx ⊢
  exact (inv_lt_comm₀ hr0 hx0).mp hx

end GlobalTheory.PrinTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesZeroOfCoordinateZero
section
noncomputable section

open Matrix

namespace GlobalTheory.PrinTwo

theorem eq_zero_of_ev_one_of_coord {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : PSp μ₁ μ₂) (h1 : ev f 1 = 0)
    (hc : ∀ x : k, coord f x = 0) : f = 0 := by
  apply ext_ev
  intro g
  have hz : ev (0 : PSp μ₁ μ₂) g = 0 := by
    have := ev_smul (0 : ℂ) (0 : PSp μ₁ μ₂) g
    simpa using this
  rw [hz]
  have hdet : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit |>.ne_zero
  rw [Matrix.det_fin_two] at hdet
  by_cases hr : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 = 0
  · rw [hr, mul_zero, sub_zero] at hdet
    have hp : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
    have hs : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
    have hg : g = bor (Units.mk0 _ hp) (Units.mk0 _ hs) ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 1) * 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hr]
    rw [hg, ev_bor, h1, mul_zero]
  · set D := (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0 * (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 -
      (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 1 * (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 with hD
    have hA : -D / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 ≠ 0 := div_ne_zero (neg_ne_zero.2 hdet) hr
    have hg : g = bor (Units.mk0 _ hA) (Units.mk0 _ hr) ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0) *
        (wE * nU ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0)) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hD] <;> field_simp <;> ring
    rw [hg, ev_bor]
    have := hc ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0)
    rw [coord] at this
    rw [this, mul_zero]

end GlobalTheory.PrinTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdImIteratedWirtingerDerivWordDifferentiableOnStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodIm_iteratedWirtingerDerivWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (w : List (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F × Bool)) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F → DifferentiableOn ℂ (fun σ : ℂ => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord w (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) z) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.prodIm_wirtWord_differentiableOn | exact GlobalTheory.HeckeTwo.prodIm_wirtWord_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.prodIm_wirtWord_differentiableOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRootPowerSumMapGaloisEq
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem prod_rootSum_map_algEquiv : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) (k : ℕ) (P : F'[X]),
    ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) =
      ∏ j ∈ Finset.range (Module.finrank F F'), rootSum θ (k * Nat.card F ^ j) P := by
  intro F F' _ _ _ _ θ k P
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  have hb := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F'
  rw [← Fintype.prod_bijective _ hb
    (fun n => rootSum θ k (P.map ((FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1 : F' ≃ₐ[F] F') : F' →+* F')))
    _ (fun _ => rfl)]
  rw [Finset.prod_range (fun j => rootSum θ (k * Nat.card F ^ j) P)]
  refine Finset.prod_congr rfl fun n _ => ?_
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have key := GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F' θ
    ((FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1 : F' ≃ₐ[F] F') : F' →+* F') (r * n.1) (fun x => by
      rw [hchar, pow_mul, ← hcard]
      show (FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1) x = _
      rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]) k P
  rw [key, hchar, pow_mul, ← hcard, Nat.card_eq_fintype_card]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaLogNorms
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ClosureFinite

theorem integralClosure_finite_of_etale (R K L : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Module.Finite K L]
    [Algebra.Etale K L] : Module.Finite R (integralClosure R L) := by
  classical
  obtain ⟨I, hI, Ai, hF, hA, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K L).mp inferInstance
  letI : ∀ i, Algebra R (Ai i) := fun i => ((algebraMap K (Ai i)).comp (algebraMap R K)).toAlgebra
  haveI : ∀ i, IsScalarTower R K (Ai i) := fun i => IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ψ : ∀ i, L →ₐ[K] Ai i := fun i => (Pi.evalAlgHom K Ai i).comp e.toAlgHom
  haveI : ∀ i, Module.Finite K (Ai i) := fun i =>
    Module.Finite.of_surjective (ψ i).toLinearMap (by
      intro y
      obtain ⟨x, hx⟩ := e.surjective (Pi.single i y)
      exact ⟨x, by simp [ψ, hx]⟩)
  haveI : ∀ i, Module.Finite R (integralClosure R (Ai i)) := fun i =>
    IsIntegralClosure.finite R K (Ai i) (integralClosure R (Ai i))
  let φ : integralClosure R L →ₗ[R] (∀ i, integralClosure R (Ai i)) :=
    LinearMap.pi (fun i =>
      (((ψ i).restrictScalars R).toLinearMap.comp (integralClosure R L).val.toLinearMap).codRestrict
        (integralClosure R (Ai i)).toSubmodule
        (fun x => IsIntegral.map ((ψ i).restrictScalars R) x.2))
  haveI : IsNoetherian R (∀ i, integralClosure R (Ai i)) := inferInstance
  have hφ : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    apply e.injective
    funext i
    have := congrArg (fun f => ((f i : integralClosure R (Ai i)) : Ai i)) h
    exact this
  haveI := isNoetherian_of_injective φ hφ
  exact Module.IsNoetherian.finite R _

end GlobalTheory.ClosureFinite

namespace GlobalTheory.ClosureFinite

theorem closure_finite : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ _ _ hinj D _ _ _ _
  classical
  let GF := GlobalTheory.LocAcyc.GenFib A R
  let S := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  let K' := FractionRing R
  have hS : ∀ y : S, IsUnit (algebraMap R K' y) := by
    rintro ⟨y, a, ha, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    intro h0
    rw [IsFractionRing.to_map_eq_zero_iff] at h0
    have : a = 0 := hinj (by simpa using h0)
    exact nonZeroDivisors.ne_zero ha this
  let g : GF →+* K' := IsLocalization.lift (M := S) hS
  letI : Algebra GF K' := g.toAlgebra
  haveI : IsScalarTower R GF K' :=
    IsScalarTower.of_algebraMap_eq (fun r => (IsLocalization.lift_eq (M := S) hS r).symm)
  have hg : Function.Injective (algebraMap GF K') := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
    change g (IsLocalization.mk' GF r s) = 0 at hx
    show IsLocalization.mk' GF r s = 0
    rw [IsLocalization.lift_mk', mul_eq_zero] at hx
    rcases hx with hx | hx
    · rw [IsFractionRing.to_map_eq_zero_iff] at hx
      rw [hx, IsLocalization.mk'_zero]
    · exact absurd hx (Units.ne_zero _)
  let L' := K' ⊗[GF] D
  let ι : D →ₐ[GF] L' := Algebra.TensorProduct.includeRight
  have hι : Function.Injective ι := by
    have h1 : Function.Injective ((Algebra.linearMap GF K').rTensor D) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hg
    intro x y hxy
    apply (TensorProduct.lid GF D).symm.injective
    apply h1
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact hxy
  have key : (ι : D →+* L').comp (GlobalTheory.KeyOriginNoeth.baseHom A R D) = algebraMap R L' := by
    ext r
    show ι (algebraMap GF D (algebraMap R GF r)) = algebraMap R L' r
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply GF K' L', IsScalarTower.algebraMap_apply R K' L',
      ← IsScalarTower.algebraMap_apply R GF K']
  letI inst : Algebra R (GlobalTheory.KeyOriginNoeth.closure A R D) := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  let Φ : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] integralClosure R L' :=
    { toFun := fun c => ⟨ι c.1, by
        have hc : (GlobalTheory.KeyOriginNoeth.baseHom A R D).IsIntegralElem c.1 := c.2
        obtain ⟨p, hp, he⟩ := hc
        refine ⟨p, hp, ?_⟩
        have h2 := Polynomial.hom_eval₂ p (GlobalTheory.KeyOriginNoeth.baseHom A R D) (ι : D →+* L') c.1
        rw [he, map_zero] at h2
        rw [← key]
        exact h2.symm⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show ι (x.1 + y.1) = ι x.1 + ι y.1
        exact map_add ι _ _
      map_smul' := fun r c => by
        apply Subtype.ext
        show ι (GlobalTheory.KeyOriginNoeth.baseHom A R D r * c.1) = r • ι c.1
        rw [map_mul, Algebra.smul_def]
        congr 1
        exact RingHom.congr_fun key r }
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    apply hι
    exact congrArg Subtype.val hxy
  haveI := integralClosure_finite_of_etale R K' L'
  haveI := isNoetherian_of_injective Φ hΦ
  exact Module.IsNoetherian.finite R _

end GlobalTheory.ClosureFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFreeOfCompleteRegularLocal
section
open IsLocalRing TensorProduct

namespace GlobalTheory.PurityComplete

variable (R : Type) [CommRing R] [IsRegularLocalRing R]

theorem algebraMap_mem_maximalIdeal {r : R} (hr : r ∈ maximalIdeal R) :
    algebraMap R (AdicCompletion (maximalIdeal R) R) r ∈
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ hr

theorem faithfullyFlat_adicCompletion :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
  haveI : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem modDepthGE_two_baseChange (A : Type) [CommRing A] [Algebra R A]
    (h : ReciprocityTheory.CA.ModDepthGE R A 2) :
    ReciprocityTheory.CA.ModDepthGE (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) R ⊗[R] A) 2 := by
  obtain ⟨rs, hl, hm, hreg⟩ := h
  refine ⟨rs.map (algebraMap R (AdicCompletion (maximalIdeal R) R)), by simp [hl], ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    exact algebraMap_mem_maximalIdeal R (hm s hs)
  · haveI := faithfullyFlat_adicCompletion R
    exact hreg.of_faithfullyFlat_of_isBaseChange (S := AdicCompletion (maximalIdeal R) R)
      (TensorProduct.isBaseChange R A (AdicCompletion (maximalIdeal R) R))

theorem etale_baseChange (A : Type) [CommRing A] [Algebra R A]
    (he : ∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A))
    (P : Ideal (AdicCompletion (maximalIdeal R) R)) [P.IsPrime]
    (hP : P ≠ maximalIdeal (AdicCompletion (maximalIdeal R) R)) :
    Algebra.Etale (Localization.AtPrime P)
      (TensorProduct (AdicCompletion (maximalIdeal R) R) (Localization.AtPrime P)
        (AdicCompletion (maximalIdeal R) R ⊗[R] A)) := by
  set C := AdicCompletion (maximalIdeal R) R
  set p : Ideal R := P.comap (algebraMap R C) with hpdef
  have hp : p ≠ maximalIdeal R := by
    intro h
    apply hP
    refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, ← hpdef, h]
  haveI := he p hp
  haveI : P.LiesOver p := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p P
  let e : Localization.AtPrime P ⊗[Localization.AtPrime p] (Localization.AtPrime p ⊗[R] A) ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime P ⊗[C] (C ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) (Localization.AtPrime P)
      (Localization.AtPrime P) A).trans
    (Algebra.TensorProduct.cancelBaseChange R C (Localization.AtPrime P)
      (Localization.AtPrime P) A).symm
  exact Algebra.Etale.of_equiv e

theorem free_of_free_baseChange (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A]
    (h : Module.Free (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal R) R ⊗[R] A)) :
    Module.Free R A := by
  haveI := faithfullyFlat_adicCompletion R
  haveI : Module.Flat R A := Module.Flat.of_flat_tensorProduct R A (AdicCompletion (maximalIdeal R) R)
  exact Module.free_of_flat_of_isLocalRing

end GlobalTheory.PurityComplete

namespace GlobalTheory.PurityStep

theorem purityFree_of_complete :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      (∀ (S : Type) [CommRing S] [IsRegularLocalRing S], IsAdicComplete (maximalIdeal S) S →
        ringKrullDim S = ringKrullDim R → GlobalTheory.PurityFree S) → GlobalTheory.PurityFree R := by
  intro R _ _ H A _ _ _ hd he
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
    GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R
  have hC := H (AdicCompletion (maximalIdeal R) R) inferInstance (UpperTheory.V.CA.g_dimcpl R)
  refine GlobalTheory.PurityComplete.free_of_free_baseChange R A ?_
  exact hC _ (GlobalTheory.PurityComplete.modDepthGE_two_baseChange R A hd)
    (fun P _ hP => GlobalTheory.PurityComplete.etale_baseChange R A he P hP)

end GlobalTheory.PurityStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneReOpenNearOfIsUnit
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory

theorem traceOpen_near_of_isUnit : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), SqOpen R → ∀ g : ℍ[R, a, b], nrm g = 1 → IsUnit (1 - g.re ^ 2) → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g → ∃ O : Set R, IsOpen O ∧ g.re ∈ O ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  intro R _ _ _ a b hsq g hg hu W hW
  set s := g.re with hs
  let φ : R × R → ℍ[R, a, b] := fun p => ⟨p.1, p.2 * g.imI, p.2 * g.imJ, p.2 * g.imK⟩
  have hφ : Continuous φ := by
    apply continuous_induced_rng.2
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa [coords, φ] using continuous_fst
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
  have hφs : φ (s, 1) = g := by ext <;> simp [φ, s]
  have hpre : φ ⁻¹' W ∈ 𝓝 (s, (1 : R)) := hφ.continuousAt.preimage_mem_nhds (by rw [hφs]; exact hW)
  obtain ⟨O₀, hO₀, V, hV, hOV⟩ := mem_nhds_prod_iff.1 hpre
  obtain ⟨U, hU, hUV⟩ := hsq V hV
  set c : R := ((hu.unit⁻¹ : Rˣ) : R) with hc_def
  have hc : c * (1 - s ^ 2) = 1 := by
    rw [hc_def]
    have := hu.unit.inv_mul
    simpa using this
  let r : R → R := fun t => (1 - t ^ 2) * c
  have hr : Continuous r := (continuous_const.sub (continuous_id.pow 2)).mul continuous_const
  have hrs : r s = 1 := by simp only [r]; rw [mul_comm]; exact hc
  refine ⟨interior (O₀ ∩ r ⁻¹' U), isOpen_interior, ?_, ?_⟩
  · rw [mem_interior_iff_mem_nhds]
    refine Filter.inter_mem hO₀ ?_
    exact hr.continuousAt.preimage_mem_nhds (by rw [hrs]; exact hU)
  · intro t ht
    have ht' := interior_subset ht
    obtain ⟨μ, hμV, hμ⟩ := hUV (r t) ht'.2
    refine ⟨φ (t, μ), hOV (Set.mk_mem_prod ht'.1 hμV), ?_, rfl⟩
    have hμ' : μ ^ 2 = (1 - t ^ 2) * c := hμ
    simp only [nrm, φ] at hg ⊢
    linear_combination μ ^ 2 * hg + (1 - s ^ 2) * hμ' + (1 - t ^ 2) * hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionUniformizerNilpotentStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_uniformizer_nilpotent : ∀ (p : ℕ) (W k Λ : Type) [CommRing W] [IsDomain W] [Field k] [CommRing Λ] (h e : ℕ) (c : W →+* k) (ρ : Λ →+* Matrix (Fin h) (Fin h) W) (π : Λ) (u : Λˣ), (p : W) ≠ 0 → Function.Surjective c → (∀ w, c w = 0 → (p : W) ∣ w) → c p = 0 → 0 < e → (p : Λ) = π ^ e * u → ((ρ π).map c) ^ e = 0 ∧ ∀ x : Fin h → k, (ρ π).map c *ᵥ x = 0 → ∃ y, x = ((ρ π).map c) ^ (e - 1) *ᵥ y := by
  first | exact @GlobalTheory.reduction_ker_uniformiser_eq_range_pow | exact GlobalTheory.reduction_ker_uniformiser_eq_range_pow | (intros; apply GlobalTheory.reduction_ker_uniformiser_eq_range_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIsometryFlagDomainGroupNeZeroStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_conj_isometry_flagDomainGroup_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ : GL (Fin r) E), X₂.Gm = X.Gm → (∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X₂.Gm v w) → (X₂.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0 := by
  first | exact @GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero | exact GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero | (intros; apply GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero <;> assumption)
end

