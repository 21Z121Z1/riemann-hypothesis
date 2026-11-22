import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncidenceZeroLocus
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMassOfFibre
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0023

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjChowNonzero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjChowNonzero

theorem aeval_smul_of_isHomogeneous {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n m : ℕ}
    {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous m) (c : Ω) (x : Fin n → Ω) :
    aeval (c • x) φ = c ^ m * aeval x φ := by
  simp only [aeval_def, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hφ.degree_eq_sum_deg_support hd
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hdeg]
  ring

theorem aeval_smul_eq_zero {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W) {x : Fin n → Ω}
    (hx : ∀ q ∈ W, aeval x q = 0) (c : Ω) : ∀ q ∈ W, aeval (c • x) q = 0 := by
  intro q hq
  rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d q), hx _ (hW q hq d), mul_zero]

theorem eq_zero_of_isFiniteProjection {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω] {n d : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} (hW : IsHomogIdeal W)
    (hA : ComplexSets.IsFiniteProjection W A) {x : Fin n → Ω} (hx : ∀ q ∈ W, aeval x q = 0)
    (hAx : ∀ i, aeval x (ComplexSets.linPoly A i) = 0) : x = 0 := by
  funext j
  by_contra hj
  obtain ⟨p, hpm, hp⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk W (X j))
  set q := Polynomial.eval₂ (ComplexSets.pullback A).toRingHom (X j) p with hq_def
  have hq : q ∈ W := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hq_def, Polynomial.hom_eval₂]
    exact hp

  set ψ : MvPolynomial (Fin d) ℂ →+* Ω := (algebraMap ℂ Ω).comp (eval 0) with hψ
  have hcomp : ∀ c : Ω, ((aeval (c • x) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Ω) : MvPolynomial (Fin n) ℂ →+* Ω).comp
      (ComplexSets.pullback A).toRingHom = ψ := by
    intro c
    refine MvPolynomial.ringHom_ext (fun a => by simp [hψ, ComplexSets.pullback]) fun i => ?_
    have h1 := aeval_smul_of_isHomogeneous (Ω := Ω) (m := 1) ?_ c x (φ := ComplexSets.linPoly A i)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        ComplexSets.pullback, aeval_X, hψ, eval_X, Pi.zero_apply, map_zero]
      rw [h1, hAx i, mul_zero]
    · exact IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_C_mul_X _ _)
  have hroot : ∀ c : Ω, (p.map ψ).eval (c * x j) = 0 := by
    intro c
    have h := aeval_smul_eq_zero hW hx c q hq
    rw [hq_def, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂, hcomp c] at h
    simpa [Polynomial.eval_map] using h
  have hzero : p.map ψ = 0 := Polynomial.funext fun r => by
    have := hroot (r / x j)
    rw [div_mul_cancel₀ r hj] at this
    simpa using this
  exact (hpm.map ψ).ne_zero hzero

theorem aeval_ne_zero_of_not_incidence {n k : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin k × Fin n) ℂ} (hW : IsHomogIdeal W) (hf : IsChowForm W k f)
    (v : Fin k × Fin n → AlgebraicClosure ℂ)
    (hv : ∀ y : Fin n → AlgebraicClosure ℂ, (∀ q ∈ W, aeval y q = 0) →
      (∀ i, ∑ j, v (i, j) * y j = 0) → y = 0) :
    aeval v f ≠ 0 := by
  intro h0
  have hinc : ∀ g ∈ incIdeal W k, aeval v g = 0 := by
    intro g hg
    have hmem : ∀ u ∈ incidence W k, aeval u g = 0 := by
      simpa only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] using hg
    obtain ⟨h, rfl⟩ := (hf.2 g).mp hmem
    rw [map_mul, h0, zero_mul]
  obtain ⟨y, hy0, hyW, hyv⟩ := IncidenceZeroLocus.proof ℂ n k W hW (AlgebraicClosure ℂ) v hinc
  exact hy0 (hv y hyW hyv)

abbrev Loc (e : ℕ) : Type := Localization.Away (X 0 : MvPolynomial (Fin (e + 1)) ℂ)

theorem projVar_zero_ne (e : ℕ) : projVar e 0 ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin (e + 1)) ℂ) _)).mpr (X_ne_zero 0)

def toK (e : ℕ) : Loc e →+* FractionRing (MvPolynomial (Fin (e + 1)) ℂ) :=
  IsLocalization.Away.lift (X 0) (g := algebraMap _ _) (IsUnit.mk0 _ (projVar_zero_ne e))

def pt (e : ℕ) : Fin (e + 1) → ℂ := fun i => if i = 0 then 1 else 0

def atPt (e : ℕ) : Loc e →+* AlgebraicClosure ℂ :=
  IsLocalization.Away.lift (X 0) (g := (algebraMap ℂ (AlgebraicClosure ℂ)).comp (eval (pt e)))
    (by simp [pt])

def locPar {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (ij : Fin (e + 1) × Fin n) : Loc e :=
  Fin.cases (motive := fun _ => Loc e)
    (algebraMap ℂ (Loc e) (A 0 ij.2) * IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
    (fun i => algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Loc e)
      (X i.succ * C (A 0 ij.2) - X 0 * C (A i.succ ij.2))) ij.1

theorem toK_injective (e : ℕ) : Function.Injective (toK e) := by
  have h1 : Function.Injective (algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Loc e)) :=
    IsLocalization.injective (Loc e) (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0))
  have h2 := IsFractionRing.injective (MvPolynomial (Fin (e + 1)) ℂ)
    (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
  exact (IsLocalization.lift_injective_iff _).mpr fun a b => h1.eq_iff.trans h2.eq_iff.symm

theorem toK_invSelf (e : ℕ) :
    toK e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = (projVar e 0)⁻¹ := by
  have h := congrArg (toK e) (IsLocalization.Away.mul_invSelf (S := Loc e) (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
  rw [map_mul, map_one, toK, IsLocalization.Away.lift_eq] at h
  exact (eq_inv_of_mul_eq_one_right h)

theorem atPt_invSelf (e : ℕ) :
    atPt e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = 1 := by
  have h := congrArg (atPt e) (IsLocalization.Away.mul_invSelf (S := Loc e) (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
  rw [map_mul, map_one] at h
  unfold atPt at h ⊢
  rw [IsLocalization.Away.lift_eq] at h
  simpa [pt] using h

theorem toK_algebraMap (e : ℕ) (a : ℂ) :
    toK e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) a := by
  rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Loc e), toK,
    IsLocalization.Away.lift_eq, ← IsScalarTower.algebraMap_apply]

theorem atPt_algebraMap (e : ℕ) (a : ℂ) :
    atPt e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (AlgebraicClosure ℂ) a := by
  rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Loc e), atPt,
    IsLocalization.Away.lift_eq]
  simp

theorem value_eq {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    eval (fun j => projPar A (.inr j))
        (Vertical.specRest (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))) f (projPar A)) =
      toK e (aeval (locPar A) f) := by
  rw [Vertical.specRest, eval₂_comp_left, aeval_def, eval₂_comp_left]
  congr 1
  · ext a
    simp [toK_algebraMap]
  · funext ⟨i, j⟩
    cases i using Fin.cases with
    | zero => simp [locPar, projPar, map_mul, toK_algebraMap, toK_invSelf, div_eq_mul_inv]
    | succ i =>
      simp [locPar, projPar, toK, IsLocalization.Away.lift_eq, projVar,
        IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ)
          (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)), mul_comm]

theorem atPt_aeval {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    atPt e (aeval (locPar A) f) =
      aeval (fun ij : Fin (e + 1) × Fin n => Fin.cases (motive := fun _ => AlgebraicClosure ℂ)
        (algebraMap ℂ _ (A 0 ij.2)) (fun i => -algebraMap ℂ _ (A i.succ ij.2)) ij.1) f := by
  rw [aeval_def, eval₂_comp_left, aeval_def]
  congr 1
  · ext a
    simp [atPt_algebraMap]
  · funext ⟨i, j⟩
    cases i using Fin.cases with
    | zero => simp [locPar, atPt_algebraMap, atPt_invSelf]
    | succ i => simp [locPar, atPt, IsLocalization.Away.lift_eq, pt, Fin.succ_ne_zero]

end ProjChowNonzero

theorem ProjChowNonzero.proof : ProjChowNonzero.Statement := by
  intro n e W f A hW hf hA
  rw [ProjChowNonzero.value_eq]
  intro h0
  have h1 : aeval (ProjChowNonzero.locPar A) f = 0 :=
    (map_eq_zero_iff _ (ProjChowNonzero.toK_injective e)).mp h0
  have h2 := congrArg (ProjChowNonzero.atPt e) h1
  rw [map_zero, ProjChowNonzero.atPt_aeval] at h2
  refine ProjChowNonzero.aeval_ne_zero_of_not_incidence hW.isHomog hf _ (fun y hyW hyv => ?_) h2
  refine ProjChowNonzero.eq_zero_of_isFiniteProjection hW.isHomog hA hyW fun i => ?_
  have hi := hyv i
  cases i using Fin.cases with
  | zero => simpa [ComplexSets.linPoly] using hi
  | succ i =>
    simp only [Fin.cases_succ, neg_mul, Finset.sum_neg_distrib, neg_eq_zero] at hi
    simpa [ComplexSets.linPoly] using hi

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughPointIncIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ThroughPointIncIdeal.eval_aeval {F K : Type*} [Field F] [Field K] [Algebra F K] {σ τ : Type*}
    (s : σ → MvPolynomial τ K) (a : τ → K) (g : MvPolynomial σ F) :
    eval a (aeval s g) = aeval (fun i => eval a (s i)) g := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem ThroughPointIncIdeal.eval_genSubst_vanish {K : Type*} [Field K] {n k : ℕ} (x c : Fin n → K)
    (hc : ∑ j, c j * x j = 1) (a : Fin k × Fin n → K) (i : Fin k) :
    ∑ j, eval a (genSubst (k := k) x c (i, j)) * x j = 0 := by
  have h : ∀ j, eval a (genSubst (k := k) x c (i, j)) =
      a (i, j) - (∑ l, a (i, l) * x l) * c j := fun j => by simp [genSubst]
  simp_rw [h, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hc, mul_one, sub_self]

theorem ThroughPointIncIdeal.proof : ThroughPointIncIdeal.Statement := by
  intro F _ n k Q x c hc hinc g hg
  apply MvPolynomial.funext
  intro a
  rw [map_zero, ThroughPointIncIdeal.eval_aeval]
  have hu := hinc (fun ij => eval a (genSubst (k := k) x c ij))
    (ThroughPointIncIdeal.eval_genSubst_vanish x c hc a)
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
  exact hg _ hu

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

variable {m n : ℕ}

theorem HermNorm.pointOf_add' (h : HermNorm n) (v w : EuclideanSpace ℂ (Fin n)) :
    h.pointOf (v + w) = h.pointOf v + h.pointOf w := by
  simp only [HermNorm.pointOf]
  rw [← Matrix.mulVec_add]
  rfl

theorem HermNorm.pointOf_smul' (h : HermNorm n) (c : ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    h.pointOf (c • v) = c • h.pointOf v := by
  simp only [HermNorm.pointOf]
  rw [← Matrix.mulVec_smul]
  rfl

def coneTangent (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (y : EuclideanSpace ℂ (Fin n)) : Submodule ℂ (EuclideanSpace ℂ (Fin n)) where
  carrier := {v | ∀ q ∈ J, ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf v j = 0}
  add_mem' {v w} hv hw q hq := by
    simp only [HermNorm.pointOf_add', Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hv q hq, hw q hq, add_zero]
  zero_mem' q _ := by
    have h0 : h.pointOf 0 = 0 := by simpa using h.pointOf_smul' 0 0
    simp [h0]
  smul_mem' c v hv q hq := by
    simp only [HermNorm.pointOf_smul', Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
      ← Finset.mul_sum]
    rw [hv q hq, mul_zero]

def tangentJac (π : Fin m → Fin n → ℂ) (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : ℝ :=
  LinearMap.normDet (𝕜 := ℂ) (U := T) (V := EuclideanSpace ℂ (Fin m)) ((linProjₗ π).comp T.subtype) ^ 2

def coneJac (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : ℝ :=
  tangentJac π (coneTangent h J y)

def firstCoordVec (n : ℕ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun j => if (j : ℕ) = 0 then 1 else 0

def leadCoordPlane (n m : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin n)) where
  carrier := {y | ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0}
  add_mem' {v w} hv hw j hj := by
    simp [hv j hj, hw j hj]
  zero_mem' j _ := by
    simp
  smul_mem' c v hv j hj := by
    simp [hv j hj]

def tangentGaussProfile (n m : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) *
      ENNReal.ofReal (tangentJac π (leadCoordPlane n m))

def ConeAreaFormula.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
    ∀ (π : Fin m → Fin n → ℂ) (g : EuclideanSpace ℂ (Fin m) → ℝ≥0∞), Measurable g →
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in coneSet h J, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w : EuclideanSpace ℂ (Fin m), (fibreCount h J π w : ℝ≥0∞) * g w

def ConeTangentAverage.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
          ∫⁻ y in coneSet h J,
            (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
              ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        ∫⁻ y in coneSet h J, tangentGaussProfile n m ‖y‖ ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))

def ConeRadialIntegral.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → ∀ C : Set (EuclideanSpace ℂ (Fin n)),
    (∀ y ∈ C, ∀ t : ℝ, 0 < t → t • y ∈ C) →
    Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) {y | ‖y‖ < 1 ∧ y ∈ C} < ⊤ →
    ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ y in C, f ‖y‖ ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) {y | ‖y‖ < 1 ∧ y ∈ C} *
          ∫⁻ r in Set.Ioi (0 : ℝ), f r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))

def TangentGaussMoment.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → m ≤ n →
    Measurable (tangentGaussProfile n m) ∧ AntitoneOn (tangentGaussProfile n m) (Set.Ici 0) ∧
      (∀ r : ℝ, 0 < tangentGaussProfile n m r) ∧
      0 < ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile n m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) ∧
      ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile n m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) < ⊤

theorem ConeAreaFormula.hypotheses_inhabited :
    IsProjPrime (coordPlaneIdeal 1 1) ∧ 0 < 1 ∧ 1 ≤ 1 + 1 ∧
      (∀ᵐ π : Fin 1 → Fin (1 + 1) → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 1),
        fibreCount (HermNorm.std (1 + 1)) (coordPlaneIdeal 1 1) π w ≠ ⊤) ∧
      Measurable (fun _ : EuclideanSpace ℂ (Fin 1) => (1 : ℝ≥0∞)) := by
  refine ⟨isProjPrime_coordPlaneIdeal one_pos 1, one_pos, by norm_num, ?_, measurable_const⟩
  filter_upwards [ae_coordPlaneBlock_det_ne_zero 1 1] with π hπ
  refine Filter.Eventually.of_forall fun w => ?_
  rw [fibreCount_coordPlaneIdeal π hπ w]
  exact ENat.one_ne_top

theorem ConeTangentAverage.hypotheses_inhabited :
    IsProjPrime (coordPlaneIdeal 1 1) ∧ 0 < 1 ∧ 1 ≤ 1 + 1 ∧
      (∀ᵐ π : Fin 1 → Fin (1 + 1) → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 1),
        fibreCount (HermNorm.std (1 + 1)) (coordPlaneIdeal 1 1) π w ≠ ⊤) :=
by
  obtain ⟨h1, h2, h3, h4, -⟩ := ConeAreaFormula.hypotheses_inhabited
  exact ⟨h1, h2, h3, h4⟩

theorem ConeRadialIntegral.hypotheses_inhabited :
    0 < 1 ∧
      (∀ y ∈ {y : EuclideanSpace ℂ (Fin (1 + 1)) | ∀ j : Fin (1 + 1), 1 ≤ (j : ℕ) → y j = 0},
        ∀ t : ℝ, 0 < t → t • y ∈ {y : EuclideanSpace ℂ (Fin (1 + 1)) | ∀ j : Fin (1 + 1), 1 ≤ (j : ℕ) → y j = 0}) ∧
      Measure.hausdorffMeasure ((2 * 1 : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin (1 + 1)) | ‖y‖ < 1 ∧ ∀ j : Fin (1 + 1), 1 ≤ (j : ℕ) → y j = 0} < ⊤ ∧
      Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-r ^ 2))) := by
  refine ⟨one_pos, ?_, (coordBall_mass (by norm_num : 1 ≤ 1 + 1)).2, by fun_prop⟩
  intro y hy t _ j hj
  simp [hy j hj]

theorem TangentGaussMoment.hypotheses_inhabited : 0 < 1 ∧ 1 ≤ 2 := by
  norm_num

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionChowHeight
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt)

open Classical in

def SectionChowHeight.Statement : Prop :=
  ∀ (n e δ : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (P : Ideal (MRing (PBlk n)))
    (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℚ) (u : Fin n → ℤ)
    (g : Ideal (MRing (PBlk n)) → MvPolynomial (Fin (e + 1) × Fin n) ℚ)
    (d : Ideal (MRing (PBlk n)) → ℕ),
    IsUnit S → IsArithVar P (e + 1 + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) (e + 1) δ
      (map (Rat.castHom ℂ) f) →
    IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
    (∀ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u), IsHorizontal W →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) e (d W)
        (map (Rat.castHom ℂ) (g W))) →
      IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (IndefiniteRowSideFullHecke.ArithBezout.specFirst (fun j => (u j : ℚ)) f) δ =
        ∑ᶠ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u),
          (multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
            (if IsHorizontal W then IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g W) (d W) else 0)

end GroundTheory.Heights₂.Heights
end
end

