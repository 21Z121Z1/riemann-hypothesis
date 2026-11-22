import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0348
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0264
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandDeterminantIdentityOfRelativeLength
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandLengthIdentitiesOfRelativeLength

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePointsBaseChange
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBC

theorem exists_point_ext (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D]
    (ρ : R →+* A) (hρA : ρ.comp (algebraMap A R) = RingHom.id A)
    (h : GlobalTheory.KeyOriginEnlarge.PointAtZero A R D ρ) :
    ∃ S : D →+* FractionRing A,
      S.comp (GlobalTheory.KeyOriginNoeth.baseHom A R D) = (algebraMap A (FractionRing A)).comp ρ := by
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  obtain ⟨s, hs⟩ := h
  letI : Algebra (GlobalTheory.KeyOriginNoeth.closure A R D) D :=
    (GlobalTheory.KeyOriginNoeth.closure A R D).subtype.toAlgebra
  let g : A →+* GlobalTheory.KeyOriginNoeth.closure A R D :=
    (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D)).comp (algebraMap A R)
  let M : Submonoid (GlobalTheory.KeyOriginNoeth.closure A R D) := (nonZeroDivisors A).map g
  have hg : ∀ a : A, algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a) =
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) := fun _ => rfl
  have hR : ∀ r : R, algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D
      (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) r) = GlobalTheory.KeyOriginNoeth.baseHom A R D r :=
    fun _ => rfl
  haveI : IsLocalization M D :=
    { map_units := by
        rintro ⟨_, a, ha, rfl⟩
        show IsUnit (algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a))
        rw [hg]
        exact (IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A R)
          (⟨algebraMap A R a, a, ha, rfl⟩ : Algebra.algebraMapSubmonoid R (nonZeroDivisors A))).map
          (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D)
      surj := fun d => by
        obtain ⟨a, ha, hd⟩ := GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure A R D {d}
        refine ⟨(⟨_, hd d (Finset.mem_singleton_self d)⟩,
          ⟨g a, a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩), ?_⟩
        show d * algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a) = _
        rw [hg, mul_comm]
        rfl
      exists_of_eq := fun {x y} hxy => ⟨1, by rw [Subtype.ext hxy]⟩ }
  have hρa : ∀ a : A, ρ (algebraMap A R a) = a := fun a => congrArg (fun w => w a) hρA
  have hsr : ∀ r : R, s (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) r) =
      algebraMap A (FractionRing A) (ρ r) := fun r => congrArg (fun w => w r) hs
  have hu : ∀ y : M, IsUnit (s y) := by
    rintro ⟨_, a, ha, rfl⟩
    show IsUnit (s (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a)))
    rw [hsr, hρa]
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, ← map_zero (algebraMap A (FractionRing A))]
    exact fun h0 => nonZeroDivisors.ne_zero ha (IsFractionRing.injective A (FractionRing A) h0)
  refine ⟨IsLocalization.lift (M := M) (S := D) hu, ?_⟩
  apply RingHom.ext; intro r
  rw [RingHom.comp_apply, ← hR, IsLocalization.lift_eq, hsr]
  rfl

end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

theorem pointAtZero_bc : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA)
      (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) := by
  intro T O _ _ _ _ _ _ A A₁ _ _ _ _ f i i₁ hf EA _ _ _ _ QA _ jA hcomp hj ρ hρA hρX hunit DA _ _ q actA
    hq htor hpt
  haveI : Module.Finite (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA := htor.1
  obtain ⟨S, hS⟩ := exists_point_ext A (Localization.AtPrime QA) DA ρ hρA hpt

  have hfK : Function.Injective ((algebraMap A₁ (FractionRing A₁)).comp f) :=
    (IsFractionRing.injective A₁ (FractionRing A₁)).comp hf
  let φ : FractionRing A →+* FractionRing A₁ := IsFractionRing.lift hfK
  have hφ : ∀ a : A, φ (algebraMap A (FractionRing A) a) = algebraMap A₁ (FractionRing A₁) (f a) :=
    fun a => IsFractionRing.lift_algebraMap hfK a

  have hρ₁a : ∀ a : A₁, reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) a) = a :=
    fun a => congrArg (fun w => w a) (reduceLoc_algebraMap f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)
  have hu₀ : ∀ y : Algebra.algebraMapSubmonoid (Loc₁ f i i₁ EA QA jA hcomp hj) (nonZeroDivisors A₁),
      IsUnit (((algebraMap A₁ (FractionRing A₁)).comp
        (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)) y) := by
    rintro ⟨_, a, ha, rfl⟩
    simp only [RingHom.coe_comp, Function.comp_apply, hρ₁a]
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, ← map_zero (algebraMap A₁ (FractionRing A₁))]
    exact fun h0 => nonZeroDivisors.ne_zero ha (IsFractionRing.injective A₁ (FractionRing A₁) h0)
  let u : GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) →+* FractionRing A₁ :=
    IsLocalization.lift hu₀
  have hu : ∀ r, u (algebraMap _ (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) r) =
      algebraMap A₁ (FractionRing A₁) (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit r) :=
    fun r => IsLocalization.lift_eq hu₀ r

  let v : DA →+* FractionRing A₁ := φ.comp S
  have huv : u.comp (fibBC f i i₁ EA QA jA hcomp hj hf) =
      v.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) := by
    apply IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
    apply RingHom.ext; intro r
    simp only [RingHom.coe_comp, Function.comp_apply, fibBC_algebraMap, hu]
    have h1 := congrArg (fun w => w r) (reduceLoc_locBC f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)
    have h2 := congrArg (fun w => w r) hS
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
    rw [h1]
    show _ = φ (S (GlobalTheory.KeyOriginNoeth.baseHom A _ DA r))
    rw [h2, hφ]

  letI : Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) (FractionRing A₁) :=
    (v.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).toAlgebra
  let W₁ : BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA →+* FractionRing A₁ :=
    (Algebra.TensorProduct.productMap
      (⟨(u : Over (fibBC f i i₁ EA QA jA hcomp hj hf) →+* FractionRing A₁), fun r =>
        congrArg (fun w => w r) huv⟩ :
          Over (fibBC f i i₁ EA QA jA hcomp hj hf) →ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)]
            FractionRing A₁)
      (⟨v, fun _ => rfl⟩ : DA →ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] FractionRing A₁)).toRingHom
  have hW : ∀ y, W₁ (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))
      (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA) y) = u y := by
    intro y
    show W₁ ((show Over (fibBC f i i₁ EA QA jA hcomp hj hf) from y) ⊗ₜ (1 : DA)) = u y
    refine (Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).trans ?_
    rw [map_one, mul_one]
    rfl
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)
    (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)
  refine ⟨W₁.comp (GlobalTheory.KeyOriginNoeth.closure A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)
    (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)).subtype, ?_⟩
  apply RingHom.ext; intro r
  show W₁ (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))
      (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)
      (algebraMap _ (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) r)) = _
  rw [hW, hu]
  rfl

end GlobalTheory.KeyOriginBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralOverCosetRepresentativesStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_integral_over_coset_representatives : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a : ℕ) (K : Subgroup (GL (Fin a) k)),
    IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) → ∀ F : GL (Fin a) k → ℂ,
    (∀ g x, x ∈ K → F (g * x) = F g) → ∀ R : Finset (GL (Fin a) k),
    (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') → (∀ g, F g ≠ 0 → ∃ r ∈ R, r⁻¹ * g ∈ K) →
    ∫ g, F g ∂(haarVol (KO k (Fin a))) = ((haarVol (KO k (Fin a))).real (K : Set (GL (Fin a) k)) : ℂ) * ∑ r ∈ R, F r := by
  first | exact @GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets | exact GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets | (intros; apply GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HankelDeterminantIntegralOfQuotientStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hankelDeterminant_integral_of_quotient : ∀ (O F : Type) [CommRing O] [Field F] (ι : O →+* F) (e ψ : PowerSeries O) (φ : PowerSeries F) (n : ℕ), PowerSeries.map ι e * φ = PowerSeries.map ι ψ → ∃ z : O, ι z = ι (PowerSeries.constantCoeff e) ^ (2 * (n + 1)) * hankel (fun i => PowerSeries.coeff i φ) n := by
  first | exact @GlobalTheory.Nef.hankel_integral | exact GlobalTheory.Nef.hankel_integral | (intros; apply GlobalTheory.Nef.hankel_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLIsCharacterStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_isCharacter : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsChar ℂ ℂ α → IsChar ℂ ℂ β → IsChar ℂ ℂ (hc a b α β n) := by
  first | (exact @GlobalTheory.Shin.HCChar.hc_isChar) | (exact GlobalTheory.Shin.HCChar.hc_isChar) | (intros; apply GlobalTheory.Shin.HCChar.hc_isChar  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLTrivialOrthogonalHyperplStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_trivial_orthogonal_hyperplaneFixer : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → 0 < b → ∀ (α : GL (Fin a) F → ℂ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y → ∑ᶠ x, hc a b α (fun _ => 1) n x * star (Y x) = 0 := by
  first | (exact @GlobalTheory.Shin.hc_one_orth_hfree) | (exact GlobalTheory.Shin.hc_one_orth_hfree) | (intros; apply GlobalTheory.Shin.hc_one_orth_hfree  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductCuspidalGLListPropertiesStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraProductCuspidalGL_list_properties : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ L n, IsCl (J θ L n)) ∧ (∀ (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L + deg L' → J θ (L ++ L') n = hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) n) ∧ ∀ (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L → L.Perm L' → J θ L n = J θ L' n := by
  first | (exact @GlobalTheory.Shin.J_list_props) | (exact GlobalTheory.Shin.J_list_props) | (intros; apply GlobalTheory.Shin.J_list_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsion
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.DerivExpansion

theorem tsum_inv_cube : ∑' m : ℤ, 1 / (m : ℂ) ^ 3 = 0 := by
  have h : ∑' m : ℤ, 1 / (m : ℂ) ^ 3 = -∑' m : ℤ, 1 / (m : ℂ) ^ 3 := by
    conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq]
    rw [← tsum_neg]
    congr 1
    funext m
    simp only [Equiv.neg_apply, Int.cast_neg]
    ring
  linear_combination h / 2

theorem row_eq (N : ℕ) [NeZero N] (j : ZMod N) :
    ∑' m : ℤ, 1 / (((j.val : ℂ)) / N + m) ^ 3 =
      -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (ch N j * (1 + ch N j) / (1 - ch N j) ^ 3) := by
  rcases eq_or_ne j 0 with rfl | hj
  · have hc : ch N 0 = 1 := by simp [ch]
    simp only [ZMod.val_zero, Nat.cast_zero, zero_div, zero_add, hc, sub_self]
    rw [tsum_inv_cube]
    simp
  · set w : ℂ := ((j.val : ℂ)) / N with hw
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have him : w.im = 0 := by simp [hw, -ZMod.natCast_val]
    have hnot : ∀ n : ℤ, w ≠ n := by
      intro n hn
      rw [hw, div_eq_iff hN] at hn
      have hz : (j.val : ℤ) = n * N := by exact_mod_cast hn
      have h1 : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj ((ZMod.val_eq_zero j).mp h))
      have h2 : j.val < N := ZMod.val_lt j
      have h1' : (0 : ℤ) < j.val := by exact_mod_cast h1
      have h2' : (j.val : ℤ) < N := by exact_mod_cast h2
      rcases le_or_gt n 0 with h | h
      · nlinarith
      · nlinarith
    have hc : ch N j = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) := by
      rw [hw]
      unfold ch
      congr 1
      ring
    rw [hc]
    exact (GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger w him hnot).2

theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wpd N x) (cD N x) := by
  intro N _ x
  unfold HasQ
  intro τ
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  obtain ⟨T, hT, hS⟩ := GlobalTheory.T.torsionPoint_rows_sum_eq_divisor_series N 2 τ x _ (by norm_num) (GlobalTheory.T.hasSum_rows_inv_cube_derivWeierstrassP τ (tors N τ x))
  set q := Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) with hq
  set c0 : ℂ := if x 0 = 0 then ch N (x 1) * (1 + ch N (x 1)) / (1 - ch N (x 1)) ^ 3 else 0 with hc0
  have h0 : cSum N 2 (-1) x 0 = 0 := by simp [cSum]
  have hT' : HasSum (fun k : ℕ => cSum N 2 (-1) x k * q ^ k) T := by
    have e1 : ((-1 : ℂ)) ^ (2 + 1) = -1 := by norm_num
    simpa only [e1] using hT
  have hsum : HasSum (fun n : ℕ => cD N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N))
      (c0 + T) := by
    have hA : HasSum (fun n : ℕ => if n = 0 then c0 else 0) c0 := hasSum_ite_eq 0 c0
    convert hA.add hT' using 1
    funext n
    have hexp : Complex.exp (2 * Real.pi * Complex.I * n * τ / N) = q ^ n := by
      rw [hq, ← Complex.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [cD, h0, hc0]
    · simp [cD, hn]
  convert hsum using 1
  have hrow : (if x 0 = 0 then ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (2 + 1) else 0) =
      -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * c0 := by
    rw [hc0]
    split_ifs
    · exact row_eq N (x 1)
    · simp
  have hf : ((Nat.factorial 2 : ℕ) : ℂ) = 2 := by norm_num [Nat.factorial]
  rw [hrow, hf] at hS
  simp only [wpd]
  rw [div_eq_iff (pow_ne_zero 3 hπ)]
  linear_combination (-2) * hS

end GlobalTheory.WpFam.DerivExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoPoissonSummationFractionalIdealStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwo_poisson_summation_fractionalIdeal : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 → Summable (fun ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)} => GlobalTheory.HeckeTwo.fTerm σ z b ν.1) ∧ HasSum (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * ∑' ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)}, GlobalTheory.HeckeTwo.fTerm σ z b ν.1) := by
  first | exact @GlobalTheory.HeckeTwoPoisson.poisson | exact GlobalTheory.HeckeTwoPoisson.poisson | (intros; apply GlobalTheory.HeckeTwoPoisson.poisson <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeYDerivativeTermIntegralPolynomialDecayStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeYDerivativeTermIntegral_polynomial_decay : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N := by
  first | exact @GlobalTheory.HeckeTwo.TermDecay.intT_bound | exact GlobalTheory.HeckeTwo.TermDecay.intT_bound | (intros; apply GlobalTheory.HeckeTwo.TermDecay.intT_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCosetRepTranslatesOrthogonalStatement
section
open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCosetRepTranslates_orthogonal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    ∀ (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res k 1), T ≠ T' →
    ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0 := by
  first | exact @GlobalTheory.HeisUnit.tr_cosetRep_orth | exact GlobalTheory.HeisUnit.tr_cosetRep_orth | (intros; apply GlobalTheory.HeisUnit.tr_cosetRep_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandDeterminantIdentityOfRelativeLengthStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herbrand_determinant_identity_of_relativeLength : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∀ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ → RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r → DetIdentity v a Fil τ := by
  first | exact @GlobalTheory.HerbDet.detIdentity_of_relLen | exact GlobalTheory.HerbDet.detIdentity_of_relLen | (intros; apply GlobalTheory.HerbDet.detIdentity_of_relLen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandLengthIdentitiesOfRelativeLengthStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herbrand_lengthIdentities_of_relativeLength : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∀ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ → RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r → LengthIdentities v a Fil τ := by
  first | exact @GlobalTheory.HerbLen.lengthIdentities_of_relLen | exact GlobalTheory.HerbLen.lengthIdentities_of_relLen | (intros; apply GlobalTheory.HerbLen.lengthIdentities_of_relLen <;> assumption)
end

