import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreIdeal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0032

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeGraphCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal NNReal

noncomputable section

theorem coneSet_hausdorff_null_of_dim_lt {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < d) :
    Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coneSet h J) = 0 := by
  set g : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.transpose h.mat)⁻¹)
  have hu : IsUnit (Matrix.transpose h.mat).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hsub : coneSet h J ⊆ g '' zeroSetEuc J := by
    intro y hy
    refine ⟨WithLp.toLp 2 (h.pointOf y), hy, ?_⟩
    ext i
    simp [g, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]
  refine measure_mono_null hsub (nonpos_iff_eq_zero.1 ?_)
  calc Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (g '' zeroSetEuc J)
      ≤ (‖g‖₊ : ℝ≥0∞) ^ ((2 * d : ℕ) : ℝ) * Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSetEuc J) :=
        g.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [NullSmaller.proof n d J hd, mul_zero]

theorem ConeGraphCover.proof (hDim : ConeFiniteFibreDim.Statement) (hTan : ConeTangentDim.Statement)
    (hLoc : ConeSmoothLocalGraph.Statement) : ConeGraphCover.Statement := by
  intro n m h J hJ hm hmn hfib
  have e0 : Fin n ≃ Fin m ⊕ Fin (n - m) :=
    (finCongr (Nat.add_sub_cancel' hmn).symm).trans finSumFinEquiv.symm
  rcases (hDim n m h J hJ hm hmn hfib).lt_or_eq with hlt | heq
  ·
    refine ⟨fun _ => e0, fun _ => ∅, fun _ => 0,
      fun _ => ⟨isOpen_empty, differentiableOn_empty, by simp, by simp⟩, ?_⟩
    exact measure_mono_null Set.sdiff_subset (coneSet_hausdorff_null_of_dim_lt h J m hlt)

  set S := {y | y ∈ coneSet h J ∧ finrank ℂ (coneTangent h J y) = m} with hSdef
  have hbad : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ S) = 0 := by
    have hae := hTan n m h J hJ hm hmn hfib
    rw [ae_iff] at hae
    refine measure_mono_null ?_ (nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans hae.le))
    intro y hy
    exact ⟨fun h' => hy.2 ⟨hy.1, h'⟩, hy.1⟩

  have hloc := fun y (hy : y ∈ S) => hLoc n m h J hJ.isPrime heq y hy.1 hy.2
  have : Nonempty (Fin n ≃ Fin m ⊕ Fin (n - m)) := ⟨e0⟩
  choose! E Om Ph U hUo hyU hCU hΩ hΦ hG hT using hloc

  obtain ⟨T, hTS, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable S U hUo
  have hScov : S ⊆ ⋃ y ∈ T, graphPt (E y) (Ph y) '' Om y := by
    intro y hy
    have hy' : y ∈ ⋃ z ∈ S, U z := Set.mem_biUnion hy (hyU y hy)
    rw [← hTU] at hy'
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 hy'
    exact Set.mem_biUnion hz (hCU z (hTS hz) ⟨hy.1, hyz⟩)
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  ·
    refine ⟨fun _ => e0, fun _ => ∅, fun _ => 0,
      fun _ => ⟨isOpen_empty, differentiableOn_empty, by simp, by simp⟩, ?_⟩
    refine measure_mono_null ?_ hbad
    intro y hy
    refine ⟨hy.1, fun hyS => ?_⟩
    have hy' := hScov hyS
    simp [hT0] at hy'
  · obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    have hfS : ∀ i, f i ∈ S := fun i => hTS (by rw [hf]; exact Set.mem_range_self i)
    refine ⟨fun i => E (f i), fun i => Om (f i), fun i => Ph (f i),
      fun i => ⟨hΩ _ (hfS i), hΦ _ (hfS i), hG _ (hfS i), hT _ (hfS i)⟩, ?_⟩
    refine measure_mono_null ?_ hbad
    intro y hy
    refine ⟨hy.1, fun hyS => hy.2 ?_⟩
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (hScov hyS)
    rw [hf] at hz
    obtain ⟨i, rfl⟩ := hz
    exact Set.mem_iUnion.2 ⟨i, hyz⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeJacMeasurable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

noncomputable section

variable {n : ℕ}

def coneJacMat (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : Matrix (Fin k) (Fin n) ℂ :=
  Matrix.of (fun i j => eval (h.pointOf y) (pderiv j (g i))) * h.mat.transpose

theorem continuous_coneJacMat (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ) :
    Continuous (coneJacMat h g) := by
  unfold coneJacMat
  refine Continuous.matrix_mul ?_ continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (MvPolynomial.continuous_eval _).comp h.continuous_pointOf

theorem mem_ker_coneJacMat (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)
    (y v : EuclideanSpace ℂ (Fin n)) :
    v ∈ LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y)) ↔
      ∀ i, ∑ j, eval (h.pointOf y) (pderiv j (g i)) * h.pointOf v j = 0 := by
  rw [LinearMap.mem_ker]
  change WithLp.toLp 2 (Matrix.mulVec (coneJacMat h g y) (WithLp.ofLp v)) = 0 ↔ _
  rw [WithLp.toLp_eq_zero, coneJacMat, ← Matrix.mulVec_mulVec, funext_iff]
  refine forall_congr' fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
  rfl

theorem coneTangent_eq_ker (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ}
    (g : Fin k → MvPolynomial (Fin n) ℂ) (hg : Submodule.span _ (Set.range g) = J)
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) :
    coneTangent h J y = LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y)) := by
  ext v
  rw [mem_ker_coneJacMat]
  constructor
  · intro hv i
    exact hv (g i) (hg ▸ Submodule.subset_span ⟨i, rfl⟩)
  · intro hv q hq
    rw [← hg] at hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hv i
    | zero => simp
    | add x z _ _ hx hz => simp [add_mul, Finset.sum_add_distrib, hx, hz]
    | smul a x hxmem hx =>
      have hx0 : eval (h.pointOf y) x = 0 := hy x (hg ▸ hxmem)
      calc ∑ j, eval (h.pointOf y) (pderiv j (a • x)) * h.pointOf v j
          = eval (h.pointOf y) a * ∑ j, eval (h.pointOf y) (pderiv j x) * h.pointOf v j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_eq_mul, pderiv_mul, map_add, map_mul, map_mul, hx0]
            ring
        _ = 0 := by rw [hx, mul_zero]

theorem coneTangent_eq_bot (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∉ coneSet h J) : coneTangent h J y = ⊥ := by
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ J, eval (h.pointOf y) q ≠ 0 := by
    simpa [coneSet] using hy
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  apply h.pointOf_eq_zero
  funext l
  have h1 : ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf v j = 0 := hv q hq
  have h2 : ∑ j, eval (h.pointOf y) (pderiv j (X l * q)) * h.pointOf v j = 0 :=
    hv _ (J.mul_mem_left _ hq)
  have h3 : ∀ j, eval (h.pointOf y) (pderiv j (X l * q)) * h.pointOf v j =
      h.pointOf y l * (eval (h.pointOf y) (pderiv j q) * h.pointOf v j) +
        if l = j then eval (h.pointOf y) q * h.pointOf v l else 0 := by
    intro j
    by_cases hj : l = j
    · subst hj
      simp
      ring
    · simp [pderiv_X_of_ne hj, hj]
      ring
  simp only [h3, Finset.sum_add_distrib, ← Finset.mul_sum, h1, mul_zero, zero_add,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  exact (mul_eq_zero.1 h2).resolve_left hq0

theorem starProjection_congr {U V : Submodule ℂ (EuclideanSpace ℂ (Fin n))} (e : U = V) :
    U.starProjection = V.starProjection := by
  subst e
  rfl

def gramOp {m : ℕ} (π : Fin m → Fin n → ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (LinearMap.toContinuousLinearMap (linProjₗ π)).adjoint ∘L LinearMap.toContinuousLinearMap (linProjₗ π)

theorem continuous_gramOp (m : ℕ) : Continuous (gramOp (n := n) (m := m)) := by
  have hL : Continuous fun π : Fin m → Fin n → ℂ =>
      LinearMap.toContinuousLinearMap (linProjₗ π) := by
    refine continuous_clm_apply.2 fun v => ?_
    simp only [LinearMap.coe_toContinuousLinearMap']
    change Continuous fun π : Fin m → Fin n → ℂ => linProj π v
    unfold linProj
    fun_prop
  exact (ContinuousLinearMap.adjoint.continuous.comp hL).clm_comp hL

def compressDet {m : ℕ} (π : Fin m → Fin n → ℂ)
    (Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : ℝ :=
  Complex.re (Q ∘L gramOp π ∘L Q + (1 - Q)).det

theorem continuous_compressDet (m : ℕ) :
    Continuous fun p : (Fin m → Fin n → ℂ) ×
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) => compressDet p.1 p.2 :=
  Complex.continuous_re.comp (ContinuousLinearMap.continuous_det.comp
    ((continuous_snd.clm_comp (((continuous_gramOp m).comp continuous_fst).clm_comp
      continuous_snd)).add (continuous_const.sub continuous_snd)))

theorem coneJac_eq_compressDet (hComp : TangentJacCompress.Statement) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) {m : ℕ} (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) :
    coneJac h J π y = compressDet π (coneTangent h J y).starProjection := by
  rw [coneJac, compressDet, gramOp, ContinuousLinearMap.comp_assoc, ← hComp n m π (coneTangent h J y), Complex.ofReal_re]

theorem ConeJacMeasurable.proof (hComp : TangentJacCompress.Statement)
    (hKer : KernelProjMeasurable.Statement) : ConeJacMeasurable.Statement := by
  classical
  intro n m h J _ _ _ _
  refine Measurable.aemeasurable ?_
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian J)
  let P : EuclideanSpace ℂ (Fin n) → (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    (coneSet h J).piecewise
      (fun y => (LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y))).starProjection) 0
  have hP : Measurable P :=
    Measurable.piecewise (isClosed_coneSet h J).measurableSet
      (hKer (EuclideanSpace ℂ (Fin n)) n k _ (continuous_coneJacMat h g)) measurable_const
  have hTP : ∀ y, (coneTangent h J y).starProjection = P y := by
    intro y
    by_cases hy : y ∈ coneSet h J
    · simp only [P, Set.piecewise_eq_of_mem _ _ _ hy]
      exact starProjection_congr (coneTangent_eq_ker h g hg hy)
    · simp only [P, Set.piecewise_eq_of_notMem _ _ _ hy]
      rw [starProjection_congr (coneTangent_eq_bot h hy), Submodule.starProjection_bot]
      rfl
  have hJac : (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => coneJac h J p.1 p.2) =
      fun p => compressDet p.1 (P p.2) := by
    funext p
    rw [coneJac_eq_compressDet hComp, hTP]
  have hM : Measurable fun q : (Fin m → Fin n → ℂ) ×
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) => compressDet q.1 q.2 :=
    (continuous_compressDet m).measurable
  have hM2 : Measurable fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => (p.1, P p.2) :=
    measurable_fst.prodMk (hP.comp measurable_snd)
  have hM3 := hM.comp hM2
  rw [hJac]
  exact hM3

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConePtsIntegral
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar ptsIntegral ptsIntegralAt pot)

theorem complexFibreIdeal_isRadical {n d : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P d) :
    (complexFibreIdeal P).IsRadical := by
  have hprime : (ObjectsChow.genericIdeal P).IsPrime :=
    (ObjectsChow.GenericFibreIdeal.proof n d P hP).1.isPrime
  have hcomp : (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℂ) := by
    refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, MvPolynomial.map_map,
      (RingHom.ext_int _ _ : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ)]
  have hmap : complexFibreIdeal P =
      (ObjectsChow.genericIdeal P).map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [complexFibreIdeal, ObjectsChow.genericIdeal, Ideal.map_map, hcomp]
  rw [hmap]
  exact RadicalBaseChange.proof ℚ ℂ (algebraMap ℚ ℂ) (Fin n) _ hprime.isRadical

theorem ConeIntegralPts.proof (hC : ConeIntegralComponents.Statement)
    (hW : ConeIntegralChart.Statement) : ConeIntegralPts.Statement := by
  intro n e S hS P u hP hu
  have hrad := complexFibreIdeal_isRadical hP
  have hΨ := ReciprocityTheory.ChartRestriction.G.Geo.goodProjExists Unit (PBlk n) P e hP
  have hpts : ptsIntegral P (pot fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
      (IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u) =
      ptsIntegralAt P hΨ.choose (pot fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
        (IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u) := by
    unfold ptsIntegral
    rw [dif_pos hΨ]
  rw [hpts, ← hW n e S hS P u hΨ.choose hP hu hΨ.choose_spec, ← hC n e _ P u hP hu, cycleIntegral]
  refine Finset.sum_congr rfl fun W hWm => ?_
  rw [fundCycle_apply_of_isRadical hrad hWm, Nat.cast_one, one_mul]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSmoothLocalGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

variable {n : ℕ}

theorem hasFDerivAt_eval_mvPolynomial (q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    HasFDerivAt (fun z : Fin n → ℂ => eval z q)
      (∑ j, eval x (pderiv j q) • ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ) x := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    have e1 : (fun z : Fin n → ℂ => eval z (C a)) = fun _ => a := by
      funext z
      simp
    rw [e1]
    convert hasFDerivAt_const (𝕜 := ℂ) a x
    ext v
    simp
  | add p q hp hq =>
    have e1 : (fun z : Fin n → ℂ => eval z (p + q)) = fun z => eval z p + eval z q := by
      funext z
      simp
    rw [e1]
    refine (hp.add hq).congr_fderiv ?_
    ext v
    simp [Finset.sum_add_distrib, add_mul]
  | mul_X p i hp =>
    have hfun : (fun z : Fin n → ℂ => eval z (p * X i)) = (fun z => eval z p) * (fun z => z i) := by
      funext z
      simp
    rw [hfun]
    refine (hp.mul (hasFDerivAt_apply i x)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, pderiv_mul,
      pderiv_X, map_add, map_mul, eval_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]
    simp only [apply_ite, map_one, map_zero, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · by_cases hij : i = i <;> simp [mul_comm]

def HermNorm.pointOfE (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) :=
  h.pointOfL.toLinearEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ))

theorem HermNorm.pointOfE_apply (h : HermNorm n) (v : EuclideanSpace ℂ (Fin n)) :
    h.pointOfE v = h.pointOf v := rfl

def HermNorm.pointOfC (h : HermNorm n) : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ))

theorem HermNorm.pointOfC_apply (h : HermNorm n) (v : EuclideanSpace ℂ (Fin n)) :
    h.pointOfC v = h.pointOf v := rfl

theorem hasFDerivAt_eval_pointOf (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) :
    HasFDerivAt (fun w => eval (h.pointOf w) q)
      ((∑ j, eval (h.pointOf z) (pderiv j q) • ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).comp
        h.pointOfC) z :=
  (hasFDerivAt_eval_mvPolynomial q (h.pointOfC z)).comp z h.pointOfC.hasFDerivAt

theorem fderiv_eval_pointOf_apply (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ)
    (z v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℂ (fun w => eval (h.pointOf w) q) z v =
      ∑ j, eval (h.pointOf z) (pderiv j q) * h.pointOf v j := by
  rw [(hasFDerivAt_eval_pointOf h q z).fderiv]
  simp [HermNorm.pointOfC_apply]

theorem contDiff_eval_pointOf (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ) :
    ContDiff ℂ 1 (fun w => eval (h.pointOf w) q) := by
  have ha : AnalyticOnNhd ℂ (fun w => eval (h.pointOfC w) q) Set.univ :=
    (AnalyticOnNhd.eval_mvPolynomial q).comp (h.pointOfC.analyticOnNhd Set.univ)
      (fun _ _ => Set.mem_univ _)
  exact contDiffOn_univ.1 (ha.contDiffOn uniqueDiffOn_univ)

theorem coneTangent_eq_comap (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) :
    coneTangent h J z = (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) (h.pointOf z)).comap
      (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) := rfl

theorem finrank_comap_equiv {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (φ : E ≃ₗ[ℂ] F) (S : Submodule ℂ F) :
    finrank ℂ (S.comap (φ : E →ₗ[ℂ] F)) = finrank ℂ S := by
  rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

theorem ConeSmoothLocalGraph.proof (hGen : PolyLocalGenerators.Statement)
    (hImp : HolomorphicImplicitGraph.Statement) : ConeSmoothLocalGraph.Statement := by
  intro n m h J hJ hdim y hy htan
  have hpy : ∀ q ∈ J, eval (h.pointOf y) q = 0 := hy
  have htanp : finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) (h.pointOf y)) = m := by
    rw [← htan, coneTangent_eq_comap, finrank_comap_equiv]
  obtain ⟨q, g, hqJ, hgp, htanq, hgen⟩ := hGen n m J hJ hdim (h.pointOf y) hpy htanp
  set f : Fin (n - m) → EuclideanSpace ℂ (Fin n) → ℂ := fun i w => eval (h.pointOf w) (q i) with hf
  have hker : ∀ z, (⨅ i, LinearMap.ker (fderiv ℂ (f i) z : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin n))) = (polyTangent (Set.range q) (h.pointOf z)).comap
        (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) := by
    intro z
    ext v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_comap,
      LinearEquiv.coe_coe, HermNorm.pointOfE_apply, hf, fderiv_eval_pointOf_apply]
    constructor
    · rintro hv _ ⟨i, rfl⟩
      exact hv i
    · intro hv i
      exact hv _ ⟨i, rfl⟩
  have hfC : ∀ i, ContDiff ℂ 1 (f i) := fun i => contDiff_eval_pointOf h (q i)
  set V : Set (EuclideanSpace ℂ (Fin n)) := {z | eval (h.pointOf z) g ≠ 0} with hV
  have hVo : IsOpen V :=
    isOpen_ne_fun ((continuous_eval g).comp h.continuous_pointOf) continuous_const
  have hfy : ∀ i, f i y = 0 := fun i => hpy _ (hqJ i)
  have hrank : finrank ℂ ↥(⨅ i, LinearMap.ker (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin n))) = m := by
    rw [hker, finrank_comap_equiv, htanq]
  obtain ⟨e, Ω, Φ, U, hU, hyU, hUV, hΩ, hΦ, hG, htanG⟩ := hImp n m f y V hfC hVo hgp hfy hrank
  have hGC : graphPt e Φ '' Ω ⊆ coneSet h J := by
    intro z hz
    rw [hG] at hz
    obtain ⟨hzU, hzq⟩ := hz
    have hgz : eval (h.pointOf z) g ≠ 0 := hUV hzU
    intro r hr
    have hspan : Ideal.span (Set.range q) ≤ RingHom.ker (eval (h.pointOf z)) :=
      Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hzq i)
    have h0 := hspan (hgen r hr)
    rw [RingHom.mem_ker, map_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left hgz
  refine ⟨e, Ω, Φ, U, hU, hyU, ?_, hΩ, hΦ, hGC, ?_⟩
  · rintro z ⟨hz, hzU⟩
    rw [hG]
    exact ⟨hzU, fun i => hz _ (hqJ i)⟩
  · intro x hx
    apply le_antisymm
    · rw [htanG x hx, hker, coneTangent_eq_comap]
      intro v hv
      simp only [Submodule.mem_comap] at hv ⊢
      rintro _ ⟨i, rfl⟩
      exact hv (q i) (hqJ i)
    · rintro _ ⟨v, rfl⟩
      intro r hr
      simp only [ContinuousLinearMap.coe_coe]
      by_cases hd : DifferentiableAt ℂ (graphPt e Φ) x
      · have hzero : (fun w => eval (h.pointOf w) r) ∘ graphPt e Φ =ᶠ[nhds x] fun _ => (0 : ℂ) := by
          filter_upwards [hΩ.mem_nhds hx] with w hw
          exact hGC ⟨w, hw, rfl⟩ r hr
        have hD := hzero.fderiv_eq (𝕜 := ℂ)
        rw [fderiv_const_apply, fderiv_comp x (hasFDerivAt_eval_pointOf h r _).differentiableAt hd] at hD
        have hDv := congrArg (fun L : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ => L v) hD
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Pi.zero_apply,
          ContinuousLinearMap.zero_apply, fderiv_eval_pointOf_apply] at hDv
        exact hDv
      · rw [fderiv_zero_of_not_differentiableAt hd]
        have h0 : h.pointOf 0 = 0 := by simpa using h.pointOf_smul' 0 0
        simp [h0]

end

end GroundTheory.Heights₂.Heights
end

