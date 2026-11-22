import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

variable {n : ℕ}

def HermNorm.pointEquiv (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
    (Matrix.toLinearEquiv' h.mat.transpose
      (Matrix.invertibleOfIsUnitDet _ (by rw [Matrix.det_transpose]; exact h.isUnit_det)))

theorem HermNorm.pointEquiv_apply (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.pointEquiv y = h.pointOf y := rfl

theorem hausdorffMeasure_pointOf_preimage_null (h : HermNorm n) {d : ℝ} (hd : 0 ≤ d)
    {S : Set (EuclideanSpace ℂ (Fin n))} (hS : μH[d] S = 0) :
    μH[d] {y | WithLp.toLp 2 (h.pointOf y) ∈ S} = 0 := by
  let E : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    h.pointEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let F := LinearMap.toContinuousLinearMap E.symm.toLinearMap
  refine measure_mono_null (t := F '' S) (fun y hy => ⟨E y, hy, ?_⟩) ?_
  · simp [F]
  · exact le_zero_iff.1 ((F.lipschitz.hausdorffMeasure_image_le hd S).trans (by rw [hS, mul_zero]))

theorem frameDeriv_basisFun (j : Fin n) (g : MvPolynomial (Fin n) ℂ) :
    frameDeriv (EuclideanSpace.basisFun (Fin n) ℂ) j g = pderiv j g := by
  simp [frameDeriv, EuclideanSpace.basisFun_apply, PiLp.single_apply, apply_ite C, ite_mul]

theorem finrank_coneTangent_of_jacobian (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s : MvPolynomial (Fin n) ℂ)
    (hf : ∀ k, f k ∈ J) (hs : ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f))
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ coneSet h J) (hsy : eval (h.pointOf y) s ≠ 0)
    (hD : eval (h.pointOf y) (frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f) ≠ 0) :
    finrank ℂ (coneTangent h J y) = I₀.card := by
  set x := h.pointOf y with hx
  let a : Matrix {j // j ∉ I₀} (Fin n) ℂ := Matrix.of fun k j => eval x (pderiv j (f k))

  have hT : coneTangent h J y = (LinearMap.ker a.mulVecLin).comap h.pointEquiv.toLinearMap := by
    ext v
    simp only [coneTangent, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, HermNorm.pointEquiv_apply]
    constructor
    · intro hv
      funext k
      simpa [Matrix.mulVec, dotProduct, a] using hv (f k) (hf k)
    · intro hv q hq
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (hs q hq)
      have hq0 : eval x q = 0 := hy q hq
      have hf0 : ∀ k, eval x (f k) = 0 := fun k => hy _ (hf k)
      have hder : ∀ j, eval x s * eval x (pderiv j q) = ∑ k, eval x (c k) * a k j := by
        intro j
        have := congrArg (fun P => eval x (pderiv j P)) hc
        simp only [map_sum, pderiv_mul, map_add, map_mul, hq0, hf0, mul_zero, zero_add] at this
        simpa [a, mul_comm] using this.symm
      have hk : ∀ k, ∑ j, a k j * h.pointOf v j = 0 := fun k => by
        simpa [Matrix.mulVec, dotProduct] using congrFun hv k
      have : eval x s * ∑ j, eval x (pderiv j q) * h.pointOf v j = 0 := by
        rw [Finset.mul_sum]
        simp_rw [← mul_assoc, hder, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp_rw [mul_assoc, ← Finset.mul_sum, hk, mul_zero, Finset.sum_const_zero]
      exact (mul_eq_zero.1 this).resolve_left hsy

  let M : Matrix {j // j ∉ I₀} {j // j ∉ I₀} ℂ := Matrix.of fun k j => a k j
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    convert hD using 1
    rw [frameJacobianDet, RingHom.map_det]
    congr 1
    ext k j
    simp [M, a, frameDeriv_basisFun]
  have hsurj : Function.Surjective a.mulVecLin := by
    intro t
    obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM t
    refine ⟨fun j => if hj : j ∉ I₀ then v ⟨j, hj⟩ else 0, ?_⟩
    rw [← hv]
    funext k
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply]
    rw [← Finset.sum_subset (Finset.subset_univ I₀ᶜ) (fun j _ hj => by
      simp only [Finset.mem_compl, not_not] at hj; simp [hj]),
      Finset.sum_subtype I₀ᶜ (p := fun j => j ∉ I₀) (fun j => Finset.mem_compl)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [j.2]
  have hrank := LinearMap.finrank_range_add_finrank_ker a.mulVecLin
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun,
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin] at hrank
  rw [hT, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hle : I₀.card ≤ n := by simpa using Finset.card_le_univ I₀
  omega

theorem ConeTangentDim.proof (hDim : ConeKrullDimLe.Statement) (hNull : NullSmaller.Statement)
    (hJac : FrameJacobianGeneric.Statement) : ConeTangentDim.Statement := by
  intro n m h J hJ hm hmn hfin
  have := hJ.isPrime
  rw [ae_restrict_iff' (isClosed_coneSet h J).measurableSet, ae_iff]
  rcases (hDim n m h J hJ hm hmn hfin).lt_or_eq with hlt | heq
  · refine measure_mono_null (fun y hy => ?_)
      (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m J hlt))
    exact fun q hq => (Classical.not_imp.1 hy).1 q hq
  · obtain ⟨I₀, f, s, hcard, hf, hsJ, hDJ, hspan⟩ :=
      hJac n m J hJ.isPrime heq (EuclideanSpace.basisFun (Fin n) ℂ)
    set D := frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f
    have hsD : s * D ∉ J := fun h' => (hJ.isPrime.mem_or_mem h').elim hsJ hDJ
    have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {s * D})) < m := by
      rw [← ringKrullDim_eq_of_ringEquiv
          (R := (MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) (Ideal.span {s * D}))
          (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {s * D})),
        Ideal.map_span, Set.image_singleton]
      have hnz : Ideal.Quotient.mk J (s * D) ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
        mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
      rw [heq] at h1
      by_contra hge
      have h2 : ((m : ℕ) : WithBot ℕ∞) + 1 ≤
          ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J (s * D)}) + 1 := by
        gcongr; exact not_lt.1 hge
      have h3 := h2.trans h1
      exact absurd h3 (by exact_mod_cast (by omega : ¬ m + 1 ≤ m))
    refine measure_mono_null (fun y hy => ?_)
      (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m _ hdim))
    obtain ⟨hyC, hyT⟩ := Classical.not_imp.1 hy
    have hsD0 : eval (h.pointOf y) (s * D) = 0 := by
      by_contra hne
      rw [map_mul] at hne
      exact hyT (hcard ▸ finrank_coneTangent_of_jacobian h J I₀ f s hf hspan y hyC
        (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne))
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    change eval (h.pointOf y) (a + c * (s * D)) = 0
    rw [map_add, map_mul, hsD0, mul_zero, add_zero]
    exact hyC a ha

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFormsThroughPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem aeval_mul_homogeneousComponent {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n : ℕ}
    (q : MvPolynomial (Fin n) F) (e : ℕ) (t : Ω) (x : Fin n → Ω) :
    aeval (fun m => t * x m) (homogeneousComponent e q) = t ^ e * aeval x (homogeneousComponent e q) := by
  rw [homogeneousComponent_apply, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.mem_filter] at hα
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hdeg : Finsupp.degree α = ∑ i ∈ α.support, α i := rfl
  rw [← hα.2, hdeg]
  ring

theorem FormsThroughPoint.proof (hZ : IncidenceZeroLocus.Statement) (hI : ThroughPointIncIdeal.Statement)
    (hC : ChartZeroTrdeg.Statement) (hT : ThroughTwoPointsTrdeg.Statement)
    (hB : TrdegBaseAlgebraic.Statement) : FormsThroughPoint.Statement := by
  intro F _ n k Q hQ hdim x hx hxQ
  obtain ⟨q, hqQ, hqx⟩ := hxQ

  have h1 := ComponentOfIncIdeal.one_le_ringKrullDim_quot hQ
  obtain ⟨d, hd, hdk⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞) ∧
      d + 1 ≤ k := by
    generalize ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = D at h1 hdim ⊢
    induction D using WithBot.recBotCoe with
    | bot => exact absurd h1 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞) := hdim
        exact absurd (WithBot.coe_le_coe.mp h') (by simp)
      | coe m =>
        have h1' : 1 ≤ m := by exact_mod_cast h1
        have hm : m ≤ k := by exact_mod_cast hdim
        refine ⟨m - 1, ?_, by omega⟩
        rw [show m - 1 + 1 = m by omega]
        rfl

  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  let c : Fin n → AlgebraicClosure F := Pi.single j₀ (x j₀)⁻¹
  have hj₀' : x j₀ ≠ 0 := hj₀
  have hc : ∑ j, c j * x j = 1 := by
    rw [Finset.sum_eq_single j₀ (fun b _ hb => by simp [c, hb]) (by simp)]
    simp [c, hj₀']
  by_contra hno
  push Not at hno

  have hg := hI F n k Q x c hc hno
  let K := AlgebraicClosure F
  let R := MvPolynomial (Fin k × Fin n) K
  let Ω := AlgebraicClosure (FractionRing R)
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) Ω]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))
  let v : Fin k × Fin n → Ω := fun ij => algebraMap R Ω (genSubst x c ij)
  have hv : ∀ g ∈ incIdeal Q k, aeval v g = 0 := by
    intro g hgI
    have hval : aeval v g = algebraMap R Ω (aeval (genSubst x c) g) := aeval_algebraMap_apply Ω (genSubst x c) g
    rw [hval, hg g hgI, map_zero]
  obtain ⟨y, hy0, hyQ, hyv⟩ := hZ F n k Q hQ.isHomog Ω v hv

  have hnp : ∀ t : Ω, y ≠ fun m => t * algebraMap K Ω (x m) := by
    intro t ht
    obtain ⟨e, he⟩ : ∃ e, aeval x (homogeneousComponent e q) ≠ 0 := by
      by_contra h
      push Not at h
      apply hqx
      rw [← sum_homogeneousComponent q, map_sum]
      exact Finset.sum_eq_zero fun e _ => h e
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hy0
      rw [ht]
      funext m
      simp
    have hzero := hyQ _ (hQ.isHomog q hqQ e)
    have hscale := aeval_mul_homogeneousComponent q e t (algebraMap K Ω ∘ x)
    simp only [Function.comp_apply] at hscale
    rw [ht, hscale, aeval_algebraMap_apply] at hzero
    exact mul_ne_zero (pow_ne_zero _ ht0) ((map_ne_zero _).mpr he) hzero

  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy0
  have hk := hT K Ω n k hinj x c hc y j hj hnp hyv
  have hb := hB F K Ω inferInstance (Fin n) (fun m => y m * (y j)⁻¹)
  have hd' := hC F n d Q hQ hd Ω y j hyQ hj
  have hkd : (k : Cardinal) ≤ d := hk.trans (hb.trans hd')
  norm_cast at hkd
  omega

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIntChowFormExists
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

theorem chowFormExists : ChowFormExists.Statement :=
  ChowFormExists.of_affineChartTrdeg AffineChartTrdeg.proof

theorem exists_coeff_eq_apply {σ R S : Type*} [CommSemiring R] [CommSemiring S] (F : R → S) (hF : F 0 = 0)
    (p : MvPolynomial σ R) : ∃ q : MvPolynomial σ S, ∀ m, coeff m q = F (coeff m p) := by
  classical
  refine ⟨∑ m ∈ p.support, monomial m (F (coeff m p)), fun m' => ?_⟩
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, hF]

theorem exists_isPrimitive_map_eq_C_mul {σ : Type*} (g : MvPolynomial σ ℚ) (hg : g ≠ 0) :
    ∃ a : ℚ, a ≠ 0 ∧ ∃ f : MvPolynomial σ ℤ, IndefiniteRowSideFullHecke.ArithBezout.IsPrimitive f ∧
      map (Int.castRingHom ℚ) f = C a * g := by
  classical

  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ∏ m ∈ g.support, (g.coeff m).den := ⟨_, rfl⟩
  have hden : ∀ m, (g.coeff m).den ∣ d := by
    intro m
    by_cases hm : m ∈ g.support
    · rw [hd]; exact Finset.dvd_prod_of_mem _ hm
    · rw [notMem_support_iff.mp hm]; simp
  have hd0 : (d : ℚ) ≠ 0 := by
    rw [hd, Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun m _ => (g.coeff m).den_ne_zero

  let F : ℚ → ℤ := fun q => ((d / q.den : ℕ) : ℤ) * q.num
  have hF0 : F 0 = 0 := by simp [F]
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : MvPolynomial σ ℤ, ∀ m, coeff m f₀ = F (g.coeff m) :=
    exists_coeff_eq_apply F hF0 g
  have hmap₀ : map (Int.castRingHom ℚ) f₀ = C (d : ℚ) * g := by
    ext m
    rw [coeff_map, hf₀, coeff_C_mul]
    obtain ⟨k, hk⟩ := hden m
    simp only [F, eq_intCast, Int.cast_mul, Int.cast_natCast]
    rw [hk, Nat.mul_div_cancel_left _ (g.coeff m).den_pos, ← Rat.mul_den_eq_num (g.coeff m)]
    push_cast
    ring
  have hf₀ne : f₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hmap₀
    exact mul_ne_zero (C_ne_zero.mpr hd0) hg hmap₀.symm

  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℤ, c₀ = f₀.support.gcd (fun m => coeff m f₀) := ⟨_, rfl⟩
  have hc0 : c₀ ≠ 0 := by
    intro h0
    rw [h0, eq_comm, Finset.gcd_eq_zero_iff] at hc₀
    apply hf₀ne
    ext m
    by_cases hm : m ∈ f₀.support
    · simpa using hc₀ m hm
    · simpa using notMem_support_iff.mp hm
  have hdvd : ∀ m, c₀ ∣ coeff m f₀ := by
    intro m
    by_cases hm : m ∈ f₀.support
    · rw [hc₀]; exact Finset.gcd_dvd hm
    · rw [notMem_support_iff.mp hm]; exact dvd_zero _
  obtain ⟨f, hf⟩ : ∃ f : MvPolynomial σ ℤ, ∀ m, coeff m f = coeff m f₀ / c₀ :=
    exists_coeff_eq_apply (fun a => a / c₀) (by simp) f₀
  have hf₀eq : f₀ = C c₀ * f := by
    ext m
    rw [coeff_C_mul, hf, Int.mul_ediv_cancel' (hdvd m)]
  have hc0' : (c₀ : ℚ) ≠ 0 := by exact_mod_cast hc0
  refine ⟨(d : ℚ) / c₀, div_ne_zero hd0 hc0', f, fun c hc => ?_, ?_⟩
  ·
    have h1 : c * c₀ ∣ 1 * c₀ := by
      rw [one_mul]
      conv_rhs => rw [hc₀]
      refine Finset.dvd_gcd fun m _ => ?_
      rw [hf₀eq, coeff_C_mul, mul_comm c₀]
      exact mul_dvd_mul_right (hc m) c₀
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hc0).mp h1)
  · have h2 : C (c₀ : ℚ) * map (Int.castRingHom ℚ) f = C (d : ℚ) * g := by
      rw [← hmap₀, hf₀eq, map_mul, map_C, eq_intCast]
    calc map (Int.castRingHom ℚ) f = C ((c₀ : ℚ)⁻¹) * (C (c₀ : ℚ) * map (Int.castRingHom ℚ) f) := by
          rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc0', C_1, one_mul]
      _ = C ((d : ℚ) / c₀) * g := by
          rw [h2, ← mul_assoc, ← C_mul, div_eq_inv_mul]

theorem IntChowFormExists.proof (hA : ChowFormToComplexChowForm.Statement) (hG : GenericFibreIdeal.Statement)
    (hD : GenericFibreDim.Statement) : IntChowFormExists.Statement := by
  intro n e P hP
  have hQ := (hG n (e + 1) P hP).1
  obtain ⟨g, hg⟩ := chowFormExists ℚ n (e + 1) (genericIdeal P) hQ (hD n (e + 1) P hP)
  obtain ⟨δ, -, hδ⟩ := ChowFormMultiHomog.full ℚ n (e + 1) (genericIdeal P) g hQ hg
  obtain ⟨a, ha, f, hprim, hmap⟩ := exists_isPrimitive_map_eq_C_mul g hg.1
  have hC : IsChowForm (genericIdeal P) (e + 1) (map (Int.castRingHom ℚ) f) := by
    rw [hmap]
    exact isChowForm_C_mul hg ha
  have hH : IsMultiHomog δ (map (Int.castRingHom ℚ) f) := by
    rw [hmap, IsMultiHomog]
    simpa using (isWeightedHomogeneous_C _ a).mul hδ
  refine ⟨δ, f, hprim, ?_⟩
  have h := hA n e δ P _ hP hC hH
  rwa [map_map, show (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from
    RingHom.ext_int _ _] at h

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPointLengthModP
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime)

def PointLengthModP.varEquiv (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun x := x.2
  left_inv _ := rfl
  right_inv := fun ⟨(), _⟩ => rfl

theorem PointLengthModP.proof : PointLengthModP.Statement := by
  intro n p W F _ hp _ hpW hsurj hpF i
  classical
  let e : MvPolynomial (Fin n) ℤ ≃+* MRing (PBlk n) :=
    (renameEquiv ℤ (PointLengthModP.varEquiv n)).toRingEquiv
  set W' := IndefiniteRowSideFullHecke.ArithBezout.finIdeal W with hW'
  have hWe : W'.map e = W := by
    change (W.comap e).map e = W
    exact Ideal.map_comap_of_surjective _ e.surjective W
  set I : Ideal (MvPolynomial (Fin n) ℤ) := W' ⊔ Ideal.span {X i - 1} with hI
  have hJ : W ⊔ Ideal.span {(X ⟨(), i⟩ : MRing (PBlk n)) - 1} = I.map e := by
    rw [hI, Ideal.map_sup, hWe, Ideal.map_span, Set.image_singleton]
    congr 3
    simp [e, PointLengthModP.varEquiv]
  let E1 := Ideal.quotientEquiv I _ e hJ
  let φ : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) F := MvPolynomial.map (Int.castRingHom F)
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ hsurj
  have : CharP F p := (CharP.charP_iff_prime_eq_zero hp).2 (by exact_mod_cast hpF)
  have hker : RingHom.ker φ ≤ I := by
    rw [MvPolynomial.ker_map]
    apply Ideal.map_le_of_le_comap
    intro z hz
    rw [RingHom.mem_ker, eq_intCast, CharP.intCast_eq_zero_iff F p] at hz
    obtain ⟨c, rfl⟩ := hz
    simp only [Ideal.mem_comap, map_mul]
    apply Ideal.mul_mem_right
    apply Ideal.mem_sup_left
    show rename _ (C (p : ℤ)) ∈ W
    simpa [rename_C] using hpW
  set J' := W'.map φ ⊔ Ideal.span {(X i : MvPolynomial (Fin n) F) - 1} with hJ'def
  have hJ' : J' = I.map φ := by
    rw [hJ'def, hI, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    simp [φ]
  let f : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) F ⧸ J' := (Ideal.Quotient.mk J').comp φ
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hφ
  have hkerf : RingHom.ker f = I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, hJ', Ideal.comap_map_of_surjective _ hφ]
    exact sup_eq_left.2 hker
  let E2 : (MvPolynomial (Fin n) ℤ ⧸ I) ≃+* (MvPolynomial (Fin n) F ⧸ J') :=
    (Ideal.quotEquivOfEq hkerf.symm).trans (RingHom.quotientKerEquivOfSurjective hf)
  have hZ : Function.Surjective (algebraMap ℤ F) := by rw [algebraMap_int_eq]; exact hsurj
  rw [(E1.symm.trans E2).toIntAlgEquiv.toLinearEquiv.length_eq,
    Module.length_eq_of_surjective hZ, Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSheetArea
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)

def chosenSheet {n e : ℕ} (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ)
    (w : ((k : Unit) → PBlk n k) → ℂ) : (Fin e → ℂ) → (Σ k, PBlk n k) → ℂ := by
  classical
  exact if hγ : ∃ γ, IsSheet P Ψ y w γ then hγ.choose else 0

def ConeSheetArea.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (f : EuclideanSpace ℂ (Fin n) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      IntegrableOn f (coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P))
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) →
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
          ∫ y in coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P), f y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal *
          ∫ x : Fin e → ℂ, ∑ᶠ w ∈ fibre P Ψ x, ∫ t : ℂ,
            f (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
              (‖t‖ ^ (2 * e) *
                gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)

end GroundTheory.Heights₂.Heights
end
end

