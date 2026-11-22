import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PInvDerivDecay
section
set_option maxSynthPendingDepth 1

noncomputable section

open Nat Set Filter Topology

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem norm_iteratedFDeriv_real_inv (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ‖iteratedFDeriv ℝ k (Inv.inv : ℂ → ℂ) z‖ = k ! * (‖z‖ ^ (k + 1))⁻¹ := by
  rw [← (contDiffAt_inv ℂ hz (n := k)).restrictScalars_iteratedFDeriv (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  simp

theorem InvDerivDecay.proof : InvDerivDecay.Statement := by
  intro v G ρ R hρ hG hv
  set t : Set ℂ := Metric.ball 0 ρ with ht_def
  have ht : IsOpen t := Metric.isOpen_ball
  have hK : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ t :=
    Metric.closedBall_subset_ball (by linarith)
  have hbd : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) (ρ / 2),
      ‖iteratedFDerivWithin ℝ i G t z‖ ≤ M := by
    intro i hi
    exact (isCompact_closedBall (0 : ℂ) (ρ / 2)).exists_bound_of_continuousOn
      ((hG.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) ht.uniqueDiffOn).mono hK)
  obtain ⟨M₀, hM₀⟩ := hbd 0 (by norm_num)
  obtain ⟨M₁, hM₁⟩ := hbd 1 (by norm_num)
  obtain ⟨M₂, hM₂⟩ := hbd 2 le_rfl
  set M : ℝ := max 0 (max M₀ (max M₁ M₂)) with hM_def
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMi : ∀ i : ℕ, i ≤ 2 → ∀ z ∈ Metric.closedBall (0 : ℂ) (ρ / 2),
      ‖iteratedFDerivWithin ℝ i G t z‖ ≤ M := by
    intro i hi z hz
    interval_cases i
    · exact (hM₀ z hz).trans (by simp [hM_def])
    · exact (hM₁ z hz).trans (by simp [hM_def])
    · exact (hM₂ z hz).trans (by simp [hM_def])
  set R₀ : ℝ := max R (max 1 (2 / ρ)) with hR₀_def
  refine ⟨4 * M, R₀, fun y hy => ?_⟩
  have hRR₀ : R ≤ R₀ := le_max_left _ _
  have h1R₀ : 1 ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have h2R₀ : 2 / ρ ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  set s : Set ℂ := {z | R₀ < ‖z‖} with hs_def
  have hs : IsOpen s := isOpen_lt continuous_const continuous_norm
  have hys : y ∈ s := hy
  have hy1 : 1 < ‖y‖ := lt_of_le_of_lt h1R₀ hy
  have hypos : 0 < ‖y‖ := by linarith
  have hy0 : y ≠ 0 := norm_pos_iff.mp hypos
  have hinvK : ∀ z ∈ s, z⁻¹ ∈ Metric.closedBall (0 : ℂ) (ρ / 2) := by
    intro z hz
    have hz' : R₀ < ‖z‖ := hz
    have hzpos : 0 < ‖z‖ := by linarith
    rw [mem_closedBall_zero_iff, norm_inv,
      inv_le_comm₀ hzpos (by positivity), inv_div]
    linarith
  have hmaps : MapsTo (Inv.inv : ℂ → ℂ) s t := fun z hz => hK (hinvK z hz)
  have hinvC : ContDiffOn ℝ 2 (Inv.inv : ℂ → ℂ) s := by
    intro z hz
    have hz' : R₀ < ‖z‖ := hz
    have hzpos : 0 < ‖z‖ := by linarith
    exact (contDiffAt_inv ℝ (norm_pos_iff.mp hzpos)).contDiffWithinAt
  have hev : v =ᶠ[𝓝 y] G ∘ Inv.inv := by
    filter_upwards [hs.mem_nhds hys] with z hz
    exact hv z (lt_of_le_of_lt hRR₀ hz)
  have hinvD : ∀ k : ℕ, ‖iteratedFDerivWithin ℝ k (Inv.inv : ℂ → ℂ) s y‖ =
      k ! * (‖y‖ ^ (k + 1))⁻¹ := by
    intro k
    rw [iteratedFDerivWithin_of_isOpen k hs hys, norm_iteratedFDeriv_real_inv k hy0]
  have hcomp : ∀ k : ℕ, iteratedFDeriv ℝ k v y = iteratedFDerivWithin ℝ k (G ∘ Inv.inv) s y := by
    intro k
    rw [iteratedFDerivWithin_of_isOpen k hs hys]
    exact (hev.iteratedFDeriv ℝ k).eq_of_nhds
  have hC : ∀ i, i ≤ 2 → ‖iteratedFDerivWithin ℝ i G t (y⁻¹)‖ ≤ M :=
    fun i hi => hMi i hi _ (hinvK y hys)
  constructor
  · have hD1 : ∀ i, 1 ≤ i → i ≤ 1 →
        ‖iteratedFDerivWithin ℝ i (Inv.inv : ℂ → ℂ) s y‖ ≤ ((‖y‖ ^ 2)⁻¹) ^ i := by
      intro i h1 h2
      obtain rfl : i = 1 := le_antisymm h2 h1
      rw [hinvD]
      simp
    have key := norm_iteratedFDerivWithin_comp_le (n := 1) hG hinvC (by norm_num)
      ht.uniqueDiffOn hs.uniqueDiffOn hmaps hys (fun i hi => hC i (by omega)) hD1
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), hcomp 1]
    refine key.trans ?_
    have hp : 0 < (‖y‖ ^ 2)⁻¹ := by positivity
    rw [div_eq_mul_inv]
    simp only [factorial_one, cast_one, one_mul, pow_one]
    exact mul_le_mul_of_nonneg_right (by linarith) hp.le
  · set D : ℝ := Real.sqrt (2 / ‖y‖ ^ 3) with hD_def
    have hDsq : D ^ 2 = 2 / ‖y‖ ^ 3 := Real.sq_sqrt (by positivity)
    have hD2 : ∀ i, 1 ≤ i → i ≤ 2 →
        ‖iteratedFDerivWithin ℝ i (Inv.inv : ℂ → ℂ) s y‖ ≤ D ^ i := by
      intro i h1 h2
      rw [hinvD]
      interval_cases i
      · rw [pow_one, hD_def, Real.le_sqrt (by positivity) (by positivity)]
        simp only [factorial_one, cast_one, one_mul]
        rw [inv_pow, ← pow_mul, inv_le_iff_one_le_mul₀ (by positivity)]
        rw [show (1 + 1) * 2 = 4 by norm_num, show ‖y‖ ^ 4 = ‖y‖ * ‖y‖ ^ 3 by ring,
          div_mul_eq_mul_div, ← mul_assoc, mul_div_assoc, div_self (by positivity)]
        nlinarith
      · rw [hDsq]
        simp [div_eq_mul_inv]
    have key := norm_iteratedFDerivWithin_comp_le (n := 2) hG hinvC le_rfl
      ht.uniqueDiffOn hs.uniqueDiffOn hmaps hys hC hD2
    rw [hcomp 2]
    refine key.trans (le_of_eq ?_)
    rw [hDsq]
    simp only [factorial_two, cast_ofNat]
    ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PLaplacianDecayZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian MeasureTheory Filter Topology

theorem LaplacianDecayZero.integral_line_eq_zero (v : ℂ → ℝ)
    (hdiff : Differentiable ℝ (fderiv ℝ v))
    (hlim : Tendsto (fderiv ℝ v) (cocompact ℂ) (𝓝 0)) (w e : ℂ) (he : ‖e‖ = 1) :
    ∫ t : ℝ, fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e = 0 := by
  have hγd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w + (s : ℂ) * e) e t := by
    intro t
    have := (((hasDerivAt_id t).ofReal_comp).mul_const e).const_add w
    simpa using this
  have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ v (w + (s : ℂ) * e) e)
      (fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e) t := by
    intro t
    have h1 := ((hdiff (w + (t : ℂ) * e)).hasFDerivAt).comp_hasDerivAt t (hγd t)
    have h2 := (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasDerivAt t h1
    exact h2
  have hiso : Isometry (fun s : ℝ => w + (s : ℂ) * e) := by
    refine Isometry.of_dist_eq fun s t => ?_
    rw [dist_eq_norm, dist_eq_norm,
      show w + (s : ℂ) * e - (w + (t : ℂ) * e) = ((s - t : ℝ) : ℂ) * e by push_cast; ring,
      norm_mul, he, mul_one, Complex.norm_real]
  have hcoc : Tendsto (fun s : ℝ => w + (s : ℂ) * e) (cocompact ℝ) (cocompact ℂ) :=
    hiso.isClosedEmbedding.tendsto_cocompact
  have hlim' : Tendsto (fun s : ℝ => fderiv ℝ v (w + (s : ℂ) * e) e) (cocompact ℝ) (𝓝 0) := by
    have := ((ContinuousLinearMap.apply ℝ ℝ e).continuous.tendsto 0).comp (hlim.comp hcoc)
    exact this
  by_cases hint : Integrable (fun t : ℝ => fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e)
  · have := integral_of_hasDerivAt_of_tendsto hF hint (hlim'.mono_left atBot_le_cocompact)
      (hlim'.mono_left atTop_le_cocompact)
    simpa using this
  · exact integral_undef hint

theorem LaplacianDecayZero.proof : LaplacianDecayZero.Statement := by
  intro v C R₀ hv hdec
  have hD2c : Continuous (iteratedFDeriv ℝ 2 v) := hv.continuous_iteratedFDeriv le_rfl
  have hdiff : Differentiable ℝ (fderiv ℝ v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hlim : Tendsto (fderiv ℝ v) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn : Tendsto (fun y : ℂ => ‖y‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    have hc : Tendsto (fun y : ℂ => C / ‖y‖ ^ 2) (cocompact ℂ) (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hn)
    refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) ?_ hc
    filter_upwards [hn.eventually_gt_atTop R₀] with y hy
    exact (hdec y hy).1

  obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ Metric.closedBall (0 : ℂ) (max R₀ 1),
      ‖iteratedFDeriv ℝ 2 v y‖ ≤ M :=
    (isCompact_closedBall 0 (max R₀ 1)).exists_bound_of_continuousOn hD2c.continuousOn
  have hR1 : (1 : ℝ) ≤ max R₀ 1 := le_max_right _ _
  have hMR : 0 ≤ |M| * (1 + max R₀ 1) ^ 3 :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) _)
  have hbound : ∀ y : ℂ, ‖iteratedFDeriv ℝ 2 v y‖ ≤
      (|M| * (1 + max R₀ 1) ^ 3 + 8 * |C|) * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
    intro y
    have hpos : 0 < 1 + ‖y‖ := by positivity
    rw [Real.rpow_neg hpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    by_cases hy : ‖y‖ ≤ max R₀ 1
    · have h1 := hM y (by simpa using hy)
      have h2 : (1 + ‖y‖) ^ 3 ≤ (1 + max R₀ 1) ^ 3 := by gcongr
      calc ‖iteratedFDeriv ℝ 2 v y‖ * (1 + ‖y‖) ^ 3 ≤ |M| * (1 + max R₀ 1) ^ 3 :=
            mul_le_mul (h1.trans (le_abs_self M)) h2 (by positivity) (abs_nonneg M)
        _ ≤ _ := by linarith [abs_nonneg C]
    · push Not at hy
      have hR0 : R₀ < ‖y‖ := lt_of_le_of_lt (le_max_left _ _) hy
      have hy1 : 1 < ‖y‖ := lt_of_le_of_lt hR1 hy
      have h1 := (hdec y hR0).2
      have h3 : ‖iteratedFDeriv ℝ 2 v y‖ * ‖y‖ ^ 3 ≤ |C| := by
        rw [le_div_iff₀ (by positivity)] at h1
        exact h1.trans (le_abs_self C)
      have h4 : (1 + ‖y‖) ^ 3 ≤ 8 * ‖y‖ ^ 3 := by
        calc (1 + ‖y‖) ^ 3 ≤ (2 * ‖y‖) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
          _ = 8 * ‖y‖ ^ 3 := by ring
      calc ‖iteratedFDeriv ℝ 2 v y‖ * (1 + ‖y‖) ^ 3
          ≤ ‖iteratedFDeriv ℝ 2 v y‖ * (8 * ‖y‖ ^ 3) := by gcongr
        _ = 8 * (‖iteratedFDeriv ℝ 2 v y‖ * ‖y‖ ^ 3) := by ring
        _ ≤ 8 * |C| := by gcongr
        _ ≤ _ := by linarith
  have hK : Integrable (fun y : ℂ =>
      (|M| * (1 + max R₀ 1) ^ 3 + 8 * |C|) * (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)).const_mul _

  have hpart : ∀ e : ℂ, ‖e‖ = 1 → Integrable (fun y => iteratedFDeriv ℝ 2 v y ![e, e]) := by
    intro e he
    refine hK.mono' ((continuous_eval_const (![e, e] : Fin 2 → ℂ)).comp hD2c).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    calc ‖iteratedFDeriv ℝ 2 v y ![e, e]‖
        ≤ ‖iteratedFDeriv ℝ 2 v y‖ * ∏ i, ‖(![e, e] : Fin 2 → ℂ) i‖ :=
          (iteratedFDeriv ℝ 2 v y).le_opNorm _
      _ = ‖iteratedFDeriv ℝ 2 v y‖ := by simp [Fin.prod_univ_two, he]
      _ ≤ _ := hbound y
  have hform : ∀ y e : ℂ, iteratedFDeriv ℝ 2 v y ![e, e] = fderiv ℝ (fderiv ℝ v) y e e := by
    intro y e
    rw [iteratedFDeriv_two_apply]
    rfl
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hemb := Complex.measurableEquivRealProd.symm.measurableEmbedding

  have htr : ∀ e : ℂ, ‖e‖ = 1 →
      (∫ y, iteratedFDeriv ℝ 2 v y ![e, e]) =
        ∫ p : ℝ × ℝ, iteratedFDeriv ℝ 2 v (Complex.measurableEquivRealProd.symm p) ![e, e] ∧
      Integrable (fun p : ℝ × ℝ =>
        iteratedFDeriv ℝ 2 v (Complex.measurableEquivRealProd.symm p) ![e, e])
        (volume.prod volume) := by
    intro e he
    exact ⟨(hmp.integral_comp hemb _).symm, (hmp.integrable_comp_emb hemb).mpr (hpart e he)⟩
  have hz1 : ∫ y, iteratedFDeriv ℝ 2 v y ![1, 1] = 0 := by
    obtain ⟨h1, h2⟩ := htr 1 (by simp)
    rw [h1, Measure.volume_eq_prod, integral_prod_symm _ h2]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun b => ?_)
    have := LaplacianDecayZero.integral_line_eq_zero v hdiff hlim ((b : ℂ) * Complex.I) 1 (by simp)
    simp only [Pi.zero_apply]
    rw [← this]
    congr 1
    ext x
    rw [hform, show Complex.measurableEquivRealProd.symm (x, b) = (b : ℂ) * Complex.I + (x : ℂ) * 1 from
      Complex.ext (by simp) (by simp)]
  have hzI : ∫ y, iteratedFDeriv ℝ 2 v y ![Complex.I, Complex.I] = 0 := by
    obtain ⟨h1, h2⟩ := htr Complex.I (by simp)
    rw [h1, Measure.volume_eq_prod, integral_prod _ h2]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun a => ?_)
    have := LaplacianDecayZero.integral_line_eq_zero v hdiff hlim (a : ℂ) Complex.I (by simp)
    simp only [Pi.zero_apply]
    rw [← this]
    congr 1
    ext t
    rw [hform, show Complex.measurableEquivRealProd.symm (a, t) = (a : ℂ) + (t : ℂ) * Complex.I from
      Complex.ext (by simp) (by simp)]
  have hΔ := laplacian_eq_iteratedFDeriv_complexPlane v
  have h1 := hpart 1 (by simp)
  have hI := hpart Complex.I (by simp)
  refine ⟨?_, ?_⟩
  · rw [hΔ]
    exact h1.add hI
  · rw [hΔ, integral_add h1 hI, hz1, hzI, add_zero]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PLevelSetLocalInj
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def polyDiff {J : Type} [Fintype J] (p : MvPolynomial J ℂ) (w₀ : J → ℂ) : (J → ℂ) →L[ℂ] ℂ :=
  ∑ j, eval w₀ (pderiv j p) • ContinuousLinearMap.proj j

theorem polyDiff_apply {J : Type} [Fintype J] (p : MvPolynomial J ℂ) (w₀ v : J → ℂ) :
    polyDiff p w₀ v = ∑ j, eval w₀ (pderiv j p) * v j := by
  simp [polyDiff]

theorem hasStrictFDerivAt_eval_poly {J : Type} [Fintype J] (p : MvPolynomial J ℂ) (w₀ : J → ℂ) :
    HasStrictFDerivAt (fun w => eval w p) (polyDiff p w₀) w₀ := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h0 : polyDiff (C a) w₀ = 0 := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [polyDiff_apply]
    rw [h0]
    simp only [eval_C]
    exact hasStrictFDerivAt_const a w₀
  | add p q hp hq =>
    have h0 : polyDiff (p + q) w₀ = polyDiff p w₀ + polyDiff q w₀ := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [polyDiff_apply, add_mul, Finset.sum_add_distrib]
    rw [h0]
    simp only [map_add]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasStrictFDerivAt (fun w : J → ℂ => w n)
        (ContinuousLinearMap.proj n : (J → ℂ) →L[ℂ] ℂ) w₀ :=
      hasStrictFDerivAt_apply n w₀
    have h := hp.mul hX
    have h0 : polyDiff (p * X n) w₀ =
        eval w₀ p • (ContinuousLinearMap.proj n : (J → ℂ) →L[ℂ] ℂ) + w₀ n • polyDiff p w₀ := by
      have key : ∀ j, eval w₀ (pderiv j (X n : MvPolynomial J ℂ)) = if j = n then 1 else 0 := by
        intro j
        by_cases hj : j = n
        · subst hj
          simp
        · simp [pderiv_X_of_ne (Ne.symm hj), hj]
      refine ContinuousLinearMap.ext fun v => ?_
      have s1 : ∑ j, eval w₀ p * (if j = n then (1 : ℂ) else 0) * v j = eval w₀ p * v n := by
        simp
      have s2 : ∑ j, eval w₀ (pderiv j p) * w₀ n * v j = w₀ n * ∑ j, eval w₀ (pderiv j p) * v j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp only [polyDiff_apply, pderiv_mul, map_add, map_mul, key, eval_X, add_mul,
        Finset.sum_add_distrib, s1, s2, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
      ring
    rw [h0]
    simp only [map_mul, eval_X]
    exact h

theorem polyDiff_pi_range_eq_top {J R : Type} [Fintype J] [Fintype R] (f : R → MvPolynomial J ℂ)
    (w₀ : J → ℂ) (hli : LinearIndependent ℂ (fun i => fun j => eval w₀ (pderiv j (f i)))) :
    LinearMap.range ((ContinuousLinearMap.pi fun i => polyDiff (f i) w₀ : (J → ℂ) →L[ℂ] (R → ℂ)) :
      (J → ℂ) →ₗ[ℂ] (R → ℂ)) = ⊤ := by
  classical
  let M : Matrix R J ℂ := Matrix.of fun i j => eval w₀ (pderiv j (f i))
  have hrank : M.rank = Fintype.card R := LinearIndependent.rank_matrix (M := M) hli
  have hLM : ((ContinuousLinearMap.pi fun i => polyDiff (f i) w₀ : (J → ℂ) →L[ℂ] (R → ℂ)) :
      (J → ℂ) →ₗ[ℂ] (R → ℂ)) = M.mulVecLin := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [polyDiff_apply, M, Matrix.mulVec, dotProduct]
  rw [hLM]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← hrank, Matrix.rank]

theorem exists_prod_bijective {J R : Type} [Fintype J] [Fintype R] (L : (J → ℂ) →ₗ[ℂ] (R → ℂ))
    (hL : LinearMap.range L = ⊤) (m : ℕ) (hm : m + Fintype.card R = Fintype.card J) :
    ∃ π : (J → ℂ) →ₗ[ℂ] (Fin m → ℂ),
      LinearMap.ker (L.prod π) = ⊥ ∧ LinearMap.range (L.prod π) = ⊤ := by
  have hK : Module.finrank ℂ (LinearMap.ker L) = m := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [hL, finrank_top, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card] at h
    omega
  obtain ⟨C, hC⟩ := (LinearMap.ker L).exists_isCompl
  have hKm : Module.finrank ℂ (LinearMap.ker L) = Module.finrank ℂ (Fin m → ℂ) := by
    rw [hK, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e : LinearMap.ker L ≃ₗ[ℂ] (Fin m → ℂ) := LinearEquiv.ofFinrankEq _ _ hKm
  let π : (J → ℂ) →ₗ[ℂ] (Fin m → ℂ) := e.toLinearMap ∘ₗ (LinearMap.ker L).projectionOnto C hC
  have hker : LinearMap.ker (L.prod π) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : L x = 0 := congrArg Prod.fst hx
    have h2 : π x = 0 := congrArg Prod.snd hx
    have hxK : x ∈ LinearMap.ker L := h1
    have h3 : (LinearMap.ker L).projectionOnto C hC x = ⟨x, hxK⟩ :=
      Submodule.projectionOnto_apply_of_mem_left hC hxK
    have h4 : e ⟨x, hxK⟩ = 0 := by
      have : π x = e ((LinearMap.ker L).projectionOnto C hC x) := rfl
      rw [this, h3] at h2
      exact h2
    have h5 : (⟨x, hxK⟩ : LinearMap.ker L) = 0 := (LinearEquiv.map_eq_zero_iff e).1 h4
    exact congrArg Subtype.val h5
  refine ⟨π, hker, ?_⟩
  rw [LinearMap.range_eq_top, ← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact LinearMap.ker_eq_bot.1 hker
  · rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega

theorem LevelSetLocalInj.proof : LevelSetLocalInj.Statement := by
  intro J _ R _ f w₀ hli m hm
  let F : (J → ℂ) → (R → ℂ) := fun w i => eval w (f i)
  let L : (J → ℂ) →L[ℂ] (R → ℂ) := ContinuousLinearMap.pi fun i => polyDiff (f i) w₀
  have hF : HasStrictFDerivAt F L w₀ :=
    hasStrictFDerivAt_pi.2 fun i => hasStrictFDerivAt_eval_poly (f i) w₀
  obtain ⟨πl, hker, hran⟩ :=
    exists_prod_bijective (L : (J → ℂ) →ₗ[ℂ] (R → ℂ)) (polyDiff_pi_range_eq_top f w₀ hli) m hm
  let π : (J → ℂ) →L[ℂ] (Fin m → ℂ) := LinearMap.toContinuousLinearMap πl
  let Φ : (J → ℂ) →L[ℂ] (R → ℂ) × (Fin m → ℂ) := L.prod π
  let E := ContinuousLinearEquiv.ofBijective Φ hker hran
  let G : (J → ℂ) → (R → ℂ) × (Fin m → ℂ) := fun w => (F w, π w)
  have hG : HasStrictFDerivAt G (E : (J → ℂ) →L[ℂ] (R → ℂ) × (Fin m → ℂ)) w₀ :=
    (hF.prodMk π.hasStrictFDerivAt).congr_fderiv (ContinuousLinearEquiv.coe_ofBijective Φ hker hran).symm
  refine ⟨(hG.toOpenPartialHomeomorph G).source, (hG.toOpenPartialHomeomorph G).open_source,
    hG.mem_toOpenPartialHomeomorph_source, π, ?_⟩
  rintro x ⟨hxU, hx⟩ y ⟨hyU, hy⟩ hxy
  apply (hG.toOpenPartialHomeomorph G).injOn hxU hyU
  rw [hG.toOpenPartialHomeomorph_coe]
  exact Prod.ext (funext fun i => (hx i).trans (hy i).symm) hxy

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBlocksLeadSandwich
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

open Classical in

def BlocksLeadSandwich.Statement : Prop :=
  ∀ (K L : Type) [Fintype K] [Fintype L] (n a₀ : ℕ) (f : (K → ℤ) → ℤ) (g : (K ⊕ L → ℤ) → ℤ)
    (p : MvPolynomial K ℚ) (p' : MvPolynomial (K ⊕ L) ℚ),
    p.totalDegree ≤ n → p'.totalDegree ≤ n →
    (∀ b : K → ℕ, (∀ k, a₀ ≤ b k) →
      (f (fun k => (b k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (b k : ℚ)) p) →
    (∀ b : K ⊕ L → ℕ, (∀ k, a₀ ≤ b k) →
      (g (fun k => (b k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (b k : ℚ)) p') →
    (∀ e : L → ℕ, ∃ c : ℕ, ∀ d δ : K → ℕ, (∀ k, c ≤ δ k) →
      f (fun k => (d k : ℤ)) ≤ g (Sum.elim (fun k => (d k : ℤ)) fun l => (e l : ℤ)) ∧
        g (Sum.elim (fun k => (d k : ℤ)) fun l => (e l : ℤ)) ≤ f (fun k => ((d k + δ k : ℕ) : ℤ))) →
    ∀ a : K → ℤ, (∀ k, 1 ≤ a k) →
      eventualValue (mixedDiff (fun _ : Fin n => Sum.elim a (0 : L → ℤ)) g) =
        eventualValue (mixedDiff (fun _ : Fin n => a) f)

namespace BlocksLeadSandwich

end BlocksLeadSandwich

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntMuDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def FlagIntMuDegree.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ b : Ψ × Fin N →₀ ℕ,
    b.degree ≠ (rhoBlock Ψ N j).degree →
      flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * monomial b 1) = 0

example : (1 : ℕ) ≤ 2 ∧
    (Finsupp.single ((), (0 : Fin 2)) 1 : Unit × Fin 2 →₀ ℕ).degree ≠ (rhoBlock Unit 2 1).degree := by
  have hrho : rhoBlock Unit 2 1 = 0 := by
    ext ⟨u, i⟩
    fin_cases i <;> simp [rhoBlock]
  refine ⟨by norm_num, ?_⟩
  rw [hrho]
  simp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntMuProd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def FlagIntMuProd.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N →
    flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * monomial (rhoBlock Ψ N j) 1) =
      ((dimN Ψ N j).factorial : ℚ) / ((j * (N - j)).factorial : ℚ) ^ Fintype.card Ψ *
        flagInt Unit N (muPoly Unit N j ^ (j * (N - j)) * monomial (rhoBlock Unit N j) 1) ^ Fintype.card Ψ

example : (1 : ℕ) ≤ 2 := by norm_num

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFsPotLaplacian
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Real

def FsPotLaplacian.Statement : Prop :=
  (∀ y : ℂ, Δ fsPotPlane y = 2 / (1 + ‖y‖ ^ 2) ^ 2) ∧
    MeasureTheory.Integrable (Δ fsPotPlane) ∧ ∫ y, Δ fsPotPlane y = 2 * π

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

