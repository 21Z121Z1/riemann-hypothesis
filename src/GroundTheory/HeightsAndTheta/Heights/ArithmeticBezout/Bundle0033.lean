import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSlabBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal NNReal

noncomputable section

theorem ConeSlabBound.proof (hV : VarietySlabMeasure.Statement) : ConeSlabBound.Statement := by
  intro n e h W f u hW hf hu
  have hWp : W.IsPrime := hW.isPrime
  have hdim := ChowFormDimLe.proof ℂ n (e + 1) W f hW hf

  let E := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let F : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ h.matᵀ.mulVecLin ∘ₗ E.toLinearMap)
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ (h.matᵀ)⁻¹.mulVecLin ∘ₗ E.toLinearMap)
  have hF : ∀ y i, F y i = h.pointOf y i := fun _ _ => rfl
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hLF : ∀ y, L (F y) = y := by
    intro y
    ext i
    change ((h.matᵀ)⁻¹ *ᵥ (h.matᵀ *ᵥ fun j => y j)) i = y i
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  obtain ⟨C, α, hC, hα, hb⟩ := hV n (e + 1) W u hWp hdim hu ‖F‖
  set s : ℝ := ((2 * (e + 1) : ℕ) : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  let K : ℝ≥0 := ‖L‖₊
  refine ⟨(K : ℝ) ^ s * C, α, hα, fun ε hε hε1 => ?_⟩

  have hsub : coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖} ⊆
      L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} := by
    rintro y ⟨⟨hy1, hyW⟩, hyu⟩
    refine ⟨F y, ⟨fun q hq => ?_, ?_, ?_⟩, hLF y⟩
    · have : (fun i => F y i) = h.pointOf y := funext (hF y)
      rw [this]
      exact hyW q hq
    · calc ‖F y‖ ≤ ‖F‖ * ‖y‖ := F.le_opNorm y
        _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hy1.le (norm_nonneg _)
        _ = ‖F‖ := mul_one _
    · simp only [hF]
      calc ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖ := hyu
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hy1.le hε.le
        _ = ε := mul_one _
  calc μH[s] (coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖})
      ≤ μH[s] (L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε}) := measure_mono hsub
    _ ≤ (K : ℝ≥0∞) ^ s * μH[s] {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} :=
        L.lipschitz.hausdorffMeasure_image_le hs0 _
    _ ≤ (K : ℝ≥0∞) ^ s * ENNReal.ofReal (C * ε ^ α) := by
        gcongr
        exact hb ε hε hε1
    _ = ENNReal.ofReal ((K : ℝ) ^ s * C * ε ^ α) := by
        rw [mul_assoc, ENNReal.ofReal_mul (Real.rpow_nonneg K.coe_nonneg _),
          ← ENNReal.ofReal_rpow_of_nonneg K.coe_nonneg hs0, ENNReal.ofReal_coe_nnreal]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentAverage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem mem_coneTangent_self {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) :
    y ∈ coneTangent h J y := by
  intro q hq
  have hd : ∀ d, eval (h.pointOf y) (∑ j, X j * pderiv j (homogeneousComponent d q)) = 0 := by
    intro d
    rw [(homogeneousComponent_isHomogeneous d q).sum_X_mul_pderiv, map_nsmul,
      hy _ (hJ.isHomog q hq d), smul_zero]
  calc ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf y j
      = eval (h.pointOf y) (∑ j, X j * pderiv j q) := by simp [map_sum, mul_comm]
    _ = ∑ d ∈ Finset.range (q.totalDegree + 1),
          eval (h.pointOf y) (∑ j, X j * pderiv j (homogeneousComponent d q)) := by
        conv_lhs => rw [← sum_homogeneousComponent q]
        simp only [map_sum, Finset.mul_sum]
        exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun d _ => hd d

theorem isClosed_coneSet {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (coneSet h J) := by
  have : coneSet h J = ⋂ q ∈ J, {y | eval (h.pointOf y) q = 0} := by
    ext y
    simp [coneSet]
  rw [this]
  exact isClosed_biInter fun q _ =>
    isClosed_eq ((MvPolynomial.continuous_eval q).comp h.continuous_pointOf) continuous_const

theorem sFinite_restrict_of_ball {n : ℕ} (μ : Measure (EuclideanSpace ℂ (Fin n)))
    (C : Set (EuclideanSpace ℂ (Fin n))) (hC : ∀ R : ℝ, μ (C ∩ Metric.ball 0 R) < ⊤) :
    SFinite (μ.restrict C) := by
  have : IsLocallyFiniteMeasure (μ.restrict C) := ⟨fun x => ⟨Metric.ball 0 (‖x‖ + 1),
    Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith)), by
      rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet, Set.inter_comm]
      exact hC _⟩⟩
  infer_instance

theorem ConeTangentAverage.proof (hMass : ConeLocalMass.Statement)
    (hMeas : ConeJacMeasurable.Statement) (hDim : ConeTangentDim.Statement)
    (hInv : TangentGaussInvariant.Statement) : ConeTangentAverage.Statement := by
  intro n m h J hJ hm hmn hfib
  have : SFinite ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
      Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)) :=
    sFinite_restrict_of_ball _ _ (hMass n m h J hJ hm hmn hfib)
  have hG : Measurable fun π : Fin m → Fin n → ℂ => matGauss π := by
    unfold matGauss
    exact (by fun_prop : Continuous fun π : Fin m → Fin n → ℂ =>
      Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2)).measurable.ennreal_ofReal
  have hP : Continuous fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => linProj p.1 p.2 := by
    unfold linProj
    fun_prop
  have hF : AEMeasurable (Function.uncurry fun (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) =>
      matGauss π * ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
        ENNReal.ofReal (coneJac h J π y)))
      ((volume : Measure (Fin m → Fin n → ℂ)).prod
        ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J))) :=
    (hG.comp measurable_fst).aemeasurable.mul
      (((measurable_one.indicator Metric.isOpen_ball.measurableSet).comp hP.measurable).aemeasurable.mul
        (hMeas n m h J hJ hm hmn hfib).ennreal_ofReal)
  rw [show (fun π : Fin m → Fin n → ℂ => matGauss π *
      ∫⁻ y in coneSet h J, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
        ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))) =
      fun π => ∫⁻ y in coneSet h J, matGauss π *
        ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y)) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) from
    funext fun π => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm,
    lintegral_lintegral_swap hF]
  refine lintegral_congr_ae ?_
  filter_upwards [hDim n m h J hJ hm hmn hfib, ae_restrict_mem (isClosed_coneSet h J).measurableSet]
    with y hy hyC
  simp only [← mul_assoc]
  exact hInv n m hm hmn _ hy y (mem_coneTangent_self h hJ hyC)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGraphAreaFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set

open scoped ENNReal

noncomputable section

theorem GraphAreaFibre.differentiableAt_graphPt {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {Φ : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hΦ : DifferentiableAt ℂ Φ x) : DifferentiableAt ℂ (graphPt e Φ) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => Φ y i) (e j)) x
  rcases e j with i | i
  · exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · exact (differentiableAt_piLp 2).1 hΦ i

theorem GraphAreaFibre.continuous_graphBase {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k) :
    Continuous (graphBase e : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin d)) := by
  unfold graphBase
  fun_prop

theorem GraphAreaFibre.proof (hInt : GraphAreaIntegral.Statement) (hJac : TangentJacComp.Statement)
    (hMult : AreaMultiplicityWeight.Statement) : GraphAreaFibre.Statement := by
  intro d k n e Ω Φ hΩ hΦ P hPΩ hPm T hT π
  set G : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := graphPt e Φ with hGdef
  set μ : Measure (EuclideanSpace ℂ (Fin d)) := Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) with hμdef
  have hdim : ((2 * d : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have : μ.IsAddHaarMeasure := by
    rw [hμdef, hdim]
    infer_instance

  set A : Set (EuclideanSpace ℂ (Fin d)) := Ω ∩ G ⁻¹' P with hAdef
  have hAΩ : A ⊆ Ω := inter_subset_left
  have hGA : G '' A = P := by
    rw [hAdef, image_inter_preimage]
    exact inter_eq_right.2 hPΩ
  have hAm : MeasurableSet A := by
    have hAeq : A = graphBase e '' P := by
      ext x
      constructor
      · rintro ⟨-, hxP⟩
        exact ⟨G x, hxP, graphBase_graphPt e Φ x⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨x, hx, rfl⟩ := hPΩ hy
        rw [graphBase_graphPt]
        exact ⟨hx, hy⟩
    rw [hAeq]
    refine hPm.image_of_continuousOn_injOn (GraphAreaFibre.continuous_graphBase e).continuousOn ?_
    intro y hy y' hy' h
    obtain ⟨x, -, rfl⟩ := hPΩ hy
    obtain ⟨x', -, rfl⟩ := hPΩ hy'
    rw [hGdef, graphBase_graphPt, graphBase_graphPt] at h
    rw [h]

  have hGd : ∀ x ∈ Ω, DifferentiableAt ℂ G x := fun x hx =>
    GraphAreaFibre.differentiableAt_graphPt e ((hΦ x hx).differentiableAt (hΩ.mem_nhds hx))
  let Lπ : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
    LinearMap.toContinuousLinearMap (linProjₗ π)
  set f : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin d) := fun x => linProj π (G x) with hfdef
  have hfd : ∀ x ∈ Ω, HasFDerivAt f ((Lπ.comp (fderiv ℂ G x)).restrictScalars ℝ) x := fun x hx =>
    (Lπ.hasFDerivAt.comp x (hGd x hx).hasFDerivAt).restrictScalars ℝ
  have hf' : ∀ x ∈ A, HasFDerivWithinAt f (fderiv ℝ f x) A x := fun x hx =>
    (hfd x (hAΩ hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  obtain ⟨hNm, hN⟩ := hMult (EuclideanSpace ℂ (Fin d)) μ A f (fun x => fderiv ℝ f x) hAm hf'

  have hcount : ∀ w, {y | y ∈ P ∧ linProj π y = w}.encard = {x ∈ A | f x = w}.encard := by
    intro w
    have hset : {y | y ∈ P ∧ linProj π y = w} = G '' {x ∈ A | f x = w} := by
      ext y
      constructor
      · rintro ⟨hy, hyw⟩
        obtain ⟨x, hx, rfl⟩ := hPΩ hy
        exact ⟨x, ⟨⟨hx, hy⟩, hyw⟩, rfl⟩
      · rintro ⟨x, ⟨⟨-, hxP⟩, hxw⟩, rfl⟩
        exact ⟨hxP, hxw⟩
    rw [hset, (graphPt_injective_of_graphBase e Φ).injOn.encard_image]
  have hNfun : (fun w : EuclideanSpace ℂ (Fin d) =>
      (({y | y ∈ P ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞)) =
      fun w => (({x ∈ A | f x = w}.encard : ℕ∞) : ℝ≥0∞) := by
    funext w
    rw [hcount w]

  have hc : μ = μ.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  refine ⟨?_, fun g hg => ?_⟩
  · rw [hNfun]
    exact hNm.mono_ac (Measure.absolutelyContinuous_isAddHaarMeasure volume μ)

  have h1 : ∫⁻ y in P, g (linProj π y) * ENNReal.ofReal (tangentJac π (T y))
      ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)) =
      ∫⁻ x in A, g (f x) * ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ := by
    rw [← hGA, hInt d k n e Ω Φ hΩ hΦ A hAΩ hAm]
    refine setLIntegral_congr_fun hAm fun x hx => ?_
    have hG' : fderiv ℝ G x = (fderiv ℂ G x).restrictScalars ℝ :=
      ((hGd x (hAΩ hx)).hasFDerivAt.restrictScalars ℝ).fderiv
    have hf'x : fderiv ℝ f x = (Lπ.comp (fderiv ℂ G x)).restrictScalars ℝ := (hfd x (hAΩ hx)).fderiv
    have hJ := hJac d n (fderiv ℂ G x : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) π
    have hTx : T (G x) = LinearMap.range (fderiv ℂ G x :
        EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := hT x (hAΩ hx) hx.2
    have hnn : 0 ≤ tangentJac π (T (G x)) := by
      unfold tangentJac
      positivity
    rw [mul_assoc, ← ENNReal.ofReal_mul hnn, hTx, hG', hf'x]
    congr 2
  rw [h1, hN g hg]
  simp_rw [hcount]
  rw [hc, Measure.smul_apply, lintegral_smul_measure]
  simp only [ENNReal.smul_def, smul_eq_mul]
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGraphAreaIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

theorem GraphAreaIntegral.continuous_areaJacobian {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by
  have h : (fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F)) =
      fun M => √((ContinuousLinearMap.adjoint M ∘L M).det) := by
    funext M
    rfl
  rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)).sqrt

theorem GraphAreaIntegral.proof (h : GraphAreaHolomorphic.Statement) : GraphAreaIntegral.Statement := by
  intro d m n e Ω F hΩ hF A hAΩ hA g
  set G := graphPt e F with hGdef
  set μ : Measure (EuclideanSpace ℂ (Fin d)) := μH[((2 * d : ℕ) : ℝ)] with hμ
  set ν : Measure (EuclideanSpace ℂ (Fin n)) := μH[((2 * d : ℕ) : ℝ)] with hν
  set J : EuclideanSpace ℂ (Fin d) → ℝ≥0∞ := fun x => ENNReal.ofReal (areaJacobian
    (fderiv ℝ G x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) with hJ
  have hJm : Measurable J := ENNReal.measurable_ofReal.comp
    (GraphAreaIntegral.continuous_areaJacobian.measurable.comp (measurable_fderiv ℝ G))
  have hGc : ContinuousOn G A := (continuousOn_graphPt e hF.continuousOn).mono hAΩ
  let f : A → EuclideanSpace ℂ (Fin n) := fun a => G a
  have hfc : Continuous f := hGc.domRestrict
  have hf : MeasurableEmbedding f :=
    { injective := fun a b hab => Subtype.ext (graphPt_injective_of_graphBase e F hab)
      measurable := hfc.measurable
      measurableSet_image' := fun s hs => by
        have hs' : MeasurableSet (((↑) : A → EuclideanSpace ℂ (Fin d)) '' s) :=
          MeasurableSet.subtype_image hA hs
        have : f '' s = G '' (((↑) : A → EuclideanSpace ℂ (Fin d)) '' s) := by
          rw [Set.image_image]
        rw [this]
        exact hs'.image_of_continuousOn_injOn (hGc.mono (by rintro _ ⟨a, -, rfl⟩; exact a.2))
          (graphPt_injective_of_graphBase e F).injOn }
  set M : Measure A := (μ.withDensity J).comap ((↑) : A → EuclideanSpace ℂ (Fin d)) with hM
  have hmeas : ν.restrict (G '' A) = M.map f := by
    ext1 S hS
    have hpre : ((↑) : A → EuclideanSpace ℂ (Fin d)) '' (f ⁻¹' S) = A ∩ G ⁻¹' S := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.2, ha⟩
      · rintro ⟨hx, hxS⟩
        exact ⟨⟨x, hx⟩, hxS, rfl⟩
    have hmS : MeasurableSet (A ∩ G ⁻¹' S) := by
      rw [← hpre]
      exact MeasurableSet.subtype_image hA (hf.measurable hS)
    rw [Measure.restrict_apply hS, Measure.map_apply hf.measurable hS,
      (MeasurableEmbedding.subtype_coe hA).comap_apply, hpre, withDensity_apply _ hmS,
      Set.inter_comm S, ← Set.image_inter_preimage]
    exact h d m n e Ω F hΩ hF _ (Set.inter_subset_left.trans hAΩ) hmS
  calc ∫⁻ y in G '' A, g y ∂ν = ∫⁻ y, g y ∂(M.map f) := by rw [hmeas]
    _ = ∫⁻ a, g (f a) ∂M := hf.lintegral_map g
    _ = ∫⁻ x in A, g (G x) ∂(μ.withDensity J) := lintegral_subtype_comap hA (fun x => g (G x))
    _ = ∫⁻ x, g (G x) ∂((μ.restrict A).withDensity J) := by rw [restrict_withDensity hA]
    _ = ∫⁻ x in A, J x * g (G x) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul_non_measurable _ hJm
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
    _ = ∫⁻ x in A, g (G x) * J x ∂μ := by simp_rw [mul_comm]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealNeBotDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealNeBotDim.proof (h₁ : IncIdealDim.Statement) : IncIdealNeBotDim.Statement := by
  intro F _ n k Q hQ hI
  have := hQ.isPrime
  obtain ⟨j, -⟩ := hQ.isRelevant
  have hn : 0 < n := j.pos

  have hle : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((n : ℕ) : WithBot ℕ∞) := by
    have h := ringKrullDim_le_of_surjective (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((m : ℕ) : WithBot ℕ∞) := by
    have hbot : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = D at hle hbot ⊢
    induction D using WithBot.recBotCoe with
    | bot => exact absurd rfl hbot
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hle
        exact ENat.natCast_ne_top n (top_le_iff.mp (WithBot.coe_le_coe.mp h'))
      | coe m => exact ⟨m, rfl⟩
  have hm1 : 1 ≤ m := one_le_of_isProjPrime hQ hm
  rw [hm]
  by_contra hlt
  have hkm : k < m := by
    by_contra h
    exact hlt (by exact_mod_cast Nat.le_of_not_lt h)

  have hdim := h₁ F n k (m - 1) Q hQ (by rw [Nat.sub_add_cancel hm1]; exact hm)
  have hmin : min k (m - 1) = k := min_eq_left (by omega)
  have hkn : k ≤ k * n := Nat.le_mul_of_pos_right k hn
  rw [hmin, Nat.sub_add_cancel hkn] at hdim

  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hgnz : g ∈ nonZeroDivisors (MvPolynomial (Fin k × Fin n) F) := mem_nonZeroDivisors_of_ne_zero hg0
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hgnz
  have h3 : ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ incIdeal Q k) ≤
      ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ Ideal.span {g}) :=
    ringKrullDim_le_of_surjective
      (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem _).mpr hg))
      (Ideal.Quotient.factor_surjective _)
  have hS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_add]
  rw [hdim] at h3
  rw [hS] at h2
  have h4 : (((k * n : ℕ) : WithBot ℕ∞)) + 1 ≤ ((k * n : ℕ) : WithBot ℕ∞) :=
    le_trans (add_le_add h3 le_rfl) h2
  have h5 : ((k * n + 1 : ℕ) : WithBot ℕ∞) ≤ ((k * n : ℕ) : WithBot ℕ∞) := by exact_mod_cast h4
  have h6 : k * n + 1 ≤ k * n := by exact_mod_cast h5
  omega

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentJacComp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

theorem TangentJacComp.real_inner_eq_re {d : ℕ} (x y : EuclideanSpace ℂ (Fin d)) :
    @inner ℝ _ _ x y = RCLike.re (@inner ℂ _ _ x y) := by
  simp [PiLp.inner_apply, Complex.inner, map_sum]

theorem TangentJacComp.adjoint_restrictScalars {d n : ℕ}
    (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    LinearMap.adjoint (L.restrictScalars ℝ) = (LinearMap.adjoint L).restrictScalars ℝ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [TangentJacComp.real_inner_eq_re, TangentJacComp.real_inner_eq_re]
  simp [LinearMap.adjoint_inner_left]

theorem TangentJacComp.areaJacobian_eq {d n : ℕ}
    (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    areaJacobian (L.restrictScalars ℝ) = L.normDet ^ 2 := by
  have hsq : ((L.normDet ^ 2 : ℝ) : ℂ) = LinearMap.det (LinearMap.adjoint L ∘ₗ L) := L.normDet_sq
  rw [areaJacobian, TangentJacComp.adjoint_restrictScalars]
  have hc : (LinearMap.adjoint L).restrictScalars ℝ ∘ₗ L.restrictScalars ℝ =
      (LinearMap.adjoint L ∘ₗ L).restrictScalars ℝ := rfl
  rw [hc, LinearMap.det_restrictScalars, ← hsq, Algebra.norm_complex_apply, Complex.normSq_ofReal,
    Real.sqrt_mul_self (by positivity)]

theorem TangentJacComp.proof : TangentJacComp.Statement := by
  intro d n L π
  have hc := LinearMap.normDet_comp L (linProjₗ π)
  have hr : |LinearMap.det (((linProjₗ π).comp L).restrictScalars ℝ)| =
      ((linProjₗ π).comp L).normDet ^ 2 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.normDet_eq_norm_det,
      Complex.sq_norm, abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [hr, hc, tangentJac, TangentJacComp.areaJacobian_eq]
  rw [mul_pow]
  rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartZeroTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartZeroTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (n d : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsProjPrime Q →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞) →
    ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (y : Fin n → Ω) (j : Fin n),
      (∀ q ∈ Q, aeval y q = 0) → y j ≠ 0 →
        Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => y m * (y j)⁻¹)) ≤ (d : Cardinal)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

