import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0020
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0026

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFibreAverage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem real_smul_mem_coneSet {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) (t : ℝ) :
    t • y ∈ coneSet h J := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  intro q hq
  rw [HermNorm.pointOf_smul']
  exact PointLine.smul_mem_zeroSet hJ.isHomog hy (t : ℂ) q hq

theorem coneFibreAverage_of_lt {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
      1 * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} := by
  have hlt : (finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) < ((2 * m : ℕ) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 2 * n < 2 * m)
  rw [Real.hausdorffMeasure_of_finrank_lt hlt, Measure.coe_zero, Pi.zero_apply, mul_zero]
  have hin : ∀ π : Fin m → Fin n → ℂ,
      ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) = 0 := by
    intro π
    rw [lintegral_congr_ae (g := fun _ => 0) (ae_restrict_of_ae (by
        filter_upwards [ae_fibreCount_eq_zero hnm h J π] with w hw
        simp [hw])), lintegral_zero]
  simp [hin]

theorem coneFibreAverage_zero {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : IsProjPrime J)
    (hfib : ∀ᵐ π : Fin 0 → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 0), fibreCount h J π w ≠ ⊤) :
    ∫⁻ π : Fin 0 → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1, (fibreCount h J π w : ℝ≥0∞) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1) *
        Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} := by
  have : (volume : Measure (Fin 0 → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (ae (volume : Measure (Fin 0 → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  have : (ae (volume : Measure (EuclideanSpace ℂ (Fin 0)))).NeBot := ae_neBot.2 (NeZero.ne _)
  have hcount : ∀ (π : Fin 0 → Fin n → ℂ) (w : EuclideanSpace ℂ (Fin 0)),
      fibreCount h J π w = (coneSet h J).encard := by
    intro π w
    rw [fibreCount]
    congr 1
    ext y
    simp [Subsingleton.elim (linProj π y) w]
  obtain ⟨π₀, hπ₀⟩ := hfib.exists
  obtain ⟨w₀, hw₀⟩ := hπ₀.exists
  rw [hcount] at hw₀
  have hsub : coneSet h J ⊆ {0} := by
    intro y hy
    by_contra hy0
    rw [Set.mem_singleton_iff] at hy0
    have hinf : (Set.range fun t : ℂ => t • y).Infinite :=
      Set.infinite_range_of_injective (smul_left_injective ℂ hy0)
    have hsub' : (Set.range fun t : ℂ => t • y) ⊆ coneSet h J := by
      rintro _ ⟨t, rfl⟩ q hq
      rw [HermNorm.pointOf_smul']
      exact PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq
    exact hw₀ (hinf.mono hsub').encard_eq
  have hset : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} = coneSet h J := by
    ext y
    refine ⟨fun hy => hy.2, fun hy => ⟨?_, hy⟩⟩
    rw [Set.mem_singleton_iff.1 (hsub hy)]
    simp
  have hmass : Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ) (coneSet h J) =
      ((coneSet h J).encard : ℝ≥0∞) := by
    rcases Set.subset_singleton_iff_eq.1 hsub with h0 | h0
    · rw [h0]
      simp
    · rw [h0, Nat.mul_zero, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton,
        Set.encard_singleton]
      simp
  have hgauss : ∀ π : Fin 0 → Fin n → ℂ, matGauss π = 1 := by
    intro π
    simp [matGauss]
  have huniv : (volume : Measure (Fin 0 → Fin n → ℂ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  simp_rw [hgauss, hcount, one_mul, setLIntegral_const]
  rw [lintegral_const, huniv, mul_one, hset, hmass, mul_comm]

theorem ConeFibreAverage.proof (hA : ConeAreaFormula.Statement) (hT : ConeTangentAverage.Statement)
    (hR : ConeRadialIntegral.Statement) (hG : TangentGaussMoment.Statement) :
    ConeFibreAverage.Statement := by
  intro n m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨volume (Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1), Metric.measure_ball_pos _ _ one_pos,
      measure_ball_lt_top, fun h J hJ hfib => coneFibreAverage_zero h J hJ hfib⟩
  by_cases hmn : m ≤ n
  swap
  · exact ⟨1, one_pos, ENNReal.one_lt_top, fun h J _ _ => coneFibreAverage_of_lt (by omega) h J⟩
  obtain ⟨hkm, hkanti, hkpos, hM0, hMtop⟩ := hG n m hm hmn
  set μ := Measure.hausdorffMeasure (X := EuclideanSpace ℂ (Fin n)) ((2 * m : ℕ) : ℝ) with hμ
  set k := tangentGaussProfile n m with hk
  set M := ∫⁻ r in Set.Ioi (0 : ℝ), k r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) with hM
  have hd : ((2 * m : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  obtain ⟨H, hHdef⟩ : ∃ H, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) = H := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) = V := ⟨_, rfl⟩
  have hH0 : H ≠ 0 := by
    rw [← hHdef, hd]
    exact (Metric.measure_ball_pos _ _ one_pos).ne'
  have hHtop : H ≠ ⊤ := by
    rw [← hHdef, hd]
    exact measure_ball_lt_top.ne
  have hV0 : V ≠ 0 := hVdef ▸ (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVtop : V ≠ ⊤ := hVdef ▸ measure_ball_lt_top.ne
  have hc0 : H⁻¹ * V ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.2 hHtop) hV0
  have hctop : H⁻¹ * V ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hH0) hVtop
  refine ⟨H⁻¹ * V * M, ENNReal.mul_pos hc0 hM0.ne', ENNReal.mul_lt_top hctop.lt_top hMtop, ?_⟩
  intro h J hJ hfib

  have hin : ∀ π : Fin m → Fin n → ℂ,
      ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
        H⁻¹ * V * ∫⁻ y in coneSet h J, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y) ∂μ := by
    intro π
    have harea := hA n m h J hJ hm hmn hfib π ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1)
      (measurable_one.indicator Metric.isOpen_ball.measurableSet)
    have hind : ∫⁻ w, (fibreCount h J π w : ℝ≥0∞) * (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 w = ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) := by
      rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
      congr 1
      funext w
      by_cases hw : w ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1 <;> simp [hw]
    rw [hind, hVdef, hHdef] at harea
    rw [mul_assoc, harea, ← mul_assoc, ENNReal.inv_mul_cancel hH0 hHtop, one_mul]
  have hlhs : ∫⁻ π : Fin m → Fin n → ℂ, matGauss π * ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
      H⁻¹ * V * ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
    rw [← hT n m h J hJ hm hmn hfib, ← lintegral_const_mul' _ _ hctop]
    refine lintegral_congr fun π => ?_
    rw [hin π]
    ring
  rw [hlhs]
  by_cases hfin : μ {y | ‖y‖ < 1 ∧ y ∈ coneSet h J} < ⊤
  · rw [hR n m hm (coneSet h J) (fun y hy t _ => real_smul_mem_coneSet h hJ hy t) hfin k hkm]
    ring
  · rw [not_lt, top_le_iff] at hfin
    rw [hfin, ENNReal.mul_top (ENNReal.mul_pos hc0 hM0.ne').ne']
    have hball : MeasurableSet {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} :=
      measurableSet_lt measurable_norm measurable_const
    have hge : k 1 * ⊤ ≤ ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
      calc k 1 * ⊤ = ∫⁻ y in coneSet h J, {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1}.indicator
              (fun _ => k 1) y ∂μ := by
            rw [lintegral_indicator_const hball, Measure.restrict_apply hball]
            congr 1
            exact hfin.symm
        _ ≤ ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
            refine lintegral_mono fun y => ?_
            by_cases hy : ‖y‖ < 1
            · rw [Set.indicator_of_mem (show y ∈ {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} from hy)]
              exact hkanti (Set.mem_Ici.2 (norm_nonneg y)) (Set.mem_Ici.2 zero_le_one) hy.le
            · rw [Set.indicator_of_notMem (show y ∉ {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} from hy)]
              exact bot_le
    rw [ENNReal.mul_top (hkpos 1).ne', top_le_iff] at hge
    rw [hge, ENNReal.mul_top hc0]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeRadialIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

open scoped ENNReal Pointwise

noncomputable section

theorem ConeRadialIntegral.proof : ConeRadialIntegral.Statement := by
  intro n m hm C hC hfin f hf
  set d : ℝ := ((2 * m : ℕ) : ℝ) with hd_def
  set c := Measure.hausdorffMeasure d {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ C} with hc_def
  have hd : 0 ≤ d := Nat.cast_nonneg _
  set D : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) with hD_def
  have hDm : Measurable D := ENNReal.measurable_ofReal.comp (by fun_prop)
  set ν : Measure ℝ := Measure.map (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖)
    ((Measure.hausdorffMeasure d).restrict C) with hν_def
  set ρ : Measure ℝ := c • (volume.restrict (Ioi (0 : ℝ))).withDensity D with hρ_def
  have h2m : 2 * m ≠ 0 := by omega

  have hνIio : ∀ r : ℝ, ν (Iio r) = ENNReal.ofReal (max r 0 ^ (2 * m)) * c := by
    intro r
    rw [hν_def, Measure.map_apply continuous_norm.measurable measurableSet_Iio,
      Measure.restrict_apply (measurableSet_Iio.preimage continuous_norm.measurable)]
    rcases le_or_gt r 0 with hr | hr
    · have hempty : (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖) ⁻¹' Iio r ∩ C = ∅ := by
        ext y
        simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_and]
        intro h
        exact absurd (lt_of_lt_of_le h hr) (not_lt.2 (norm_nonneg y))
      rw [hempty, measure_empty, max_eq_right hr, zero_pow h2m, ENNReal.ofReal_zero, zero_mul]
    · have hset : (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖) ⁻¹' Iio r ∩ C =
          r • {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ C} := by
        ext y
        simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_smul_set, mem_ofPred_eq]
        constructor
        · rintro ⟨hy, hyC⟩
          refine ⟨r⁻¹ • y, ⟨?_, hC y hyC r⁻¹ (inv_pos.2 hr)⟩, smul_inv_smul₀ hr.ne' y⟩
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_lt_iff₀ hr, mul_one]
          exact hy
        · rintro ⟨z, ⟨hz, hzC⟩, rfl⟩
          refine ⟨?_, hC z hzC r hr⟩
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
          calc r * ‖z‖ < r * 1 := mul_lt_mul_of_pos_left hz hr
            _ = r := mul_one r
      rw [hset, Measure.hausdorffMeasure_smul₀ hd hr.ne', max_eq_left hr.le, ENNReal.smul_def,
        smul_eq_mul]
      congr 1
      rw [hd_def, NNReal.rpow_natCast, ENNReal.ofReal_pow hr.le, ENNReal.coe_pow]
      congr 1
      rw [Real.nnnorm_of_nonneg hr.le, ENNReal.ofReal_eq_coe_nnreal hr.le]

  have hρIio : ∀ r : ℝ, ρ (Iio r) = ENNReal.ofReal (max r 0 ^ (2 * m)) * c := by
    intro r
    rw [hρ_def, Measure.smul_apply, smul_eq_mul, withDensity_apply _ measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, mul_comm]
    congr 1
    rcases le_or_gt r 0 with hr | hr
    · have hempty : Iio r ∩ Ioi (0 : ℝ) = ∅ := by
        ext t
        simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        linarith
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure, max_eq_right hr, zero_pow h2m,
        ENNReal.ofReal_zero]
    · rw [max_eq_left hr.le, inter_comm, Ioi_inter_Iio]
      have hcont : Continuous (fun t : ℝ => 2 * (m : ℝ) * t ^ (2 * m - 1)) := by fun_prop
      rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)]
      · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
          intervalIntegral.integral_const_mul, integral_pow]
        congr 1
        obtain ⟨k, hk⟩ : ∃ k, 2 * m = k + 1 := ⟨2 * m - 1, by omega⟩
        have hk' : 2 * m - 1 = k := by omega
        have hkR : 2 * (m : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hk
        rw [hk', hkR, hk, zero_pow (Nat.succ_ne_zero k), sub_zero]
        field_simp
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact mul_nonneg (by positivity) (pow_nonneg ht.1.le _)
  have hfinG : ∀ r : ℝ, ENNReal.ofReal (max r 0 ^ (2 * m)) * c ≠ ⊤ := fun r =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have hνρ : ν = ρ := by
    refine Measure.ext_of_Ico' ν ρ (fun a b _ => ?_) (fun a b hab => ?_)
    · exact ne_top_of_le_ne_top (by rw [hνIio b]; exact hfinG b)
        (measure_mono Ico_subset_Iio_self)
    · have hsub : Iio a ⊆ Iio b := Iio_subset_Iio hab.le
      have hIco : Ico a b = Iio b \ Iio a := by
        ext t
        simp only [mem_Ico, mem_sdiff, mem_Iio, not_lt]
        tauto
      rw [hIco, measure_sdiff hsub measurableSet_Iio.nullMeasurableSet (by rw [hνIio a]; exact hfinG a),
        measure_sdiff hsub measurableSet_Iio.nullMeasurableSet (by rw [hρIio a]; exact hfinG a),
        hνIio, hνIio, hρIio, hρIio]
  calc ∫⁻ y in C, f ‖y‖ ∂(Measure.hausdorffMeasure d) = ∫⁻ r, f r ∂ν := by
        rw [hν_def, lintegral_map hf continuous_norm.measurable]
    _ = ∫⁻ r, f r ∂ρ := by rw [hνρ]
    _ = c * ∫⁻ r in Ioi 0, f r * D r := by
        rw [hρ_def, lintegral_smul_measure, smul_eq_mul,
          lintegral_withDensity_eq_lintegral_mul _ hDm hf]
        congr 1
        refine lintegral_congr fun r => ?_
        simp only [Pi.mul_apply]
        exact mul_comm _ _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionComponents
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace SectionComponents

variable {F : Type} [Field F] {n : ℕ}

theorem exists_ringKrullDim_quotient_eq (Q : Ideal (MvPolynomial (Fin n) F)) [Q.IsPrime] :
    ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = m := by
  have _ : Algebra.FiniteType F (MvPolynomial (Fin n) F ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F Q) (Ideal.Quotient.mkₐ_surjective F Q)
  have hlt := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_lt_top F
    (A := MvPolynomial (Fin n) F ⧸ Q)
  have hnn := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) F ⧸ Q)
  cases h : ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) with
  | bot => rw [h] at hnn; exact absurd hnn (by simp)
  | coe y =>
    rw [h] at hlt
    have : y ≠ ⊤ := fun hy => by subst hy; exact lt_irrefl _ hlt
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp this
    exact ⟨m, rfl⟩

theorem ringKrullDim_quotient_add_one_le_of_lt {W' W : Ideal (MvPolynomial (Fin n) F)}
    [W'.IsPrime] (hlt : W' < W) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ W) + 1 ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ W') := by
  set p : Ideal (MvPolynomial (Fin n) F ⧸ W') := W.map (Ideal.Quotient.mk W')
  have hp : p ≠ ⊥ := by
    obtain ⟨x, hxW, hxW'⟩ := SetLike.exists_of_lt hlt
    intro h
    apply hxW'
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk W' x ∈ p := Ideal.mem_map_of_mem _ hxW
    rwa [h, Ideal.mem_bot] at this
  have hquot : ringKrullDim ((MvPolynomial (Fin n) F ⧸ W') ⧸ p) =
      ringKrullDim (MvPolynomial (Fin n) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hlt.le)
  have := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le p hp
  rwa [hquot] at this

theorem ringKrullDim_quotient_add_one_eq {P W : Ideal (MvPolynomial (Fin n) F)} [P.IsPrime]
    {f : MvPolynomial (Fin n) F} (hf : f ∉ P) (hW : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ W) + 1 = ringKrullDim (MvPolynomial (Fin n) F ⧸ P) := by
  have hWprime : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  set B := MvPolynomial (Fin n) F ⧸ P
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) (Ideal.Quotient.mkₐ_surjective F P)
  set W' : Ideal B := W.map (Ideal.Quotient.mk P)
  have _ : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hf
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk P f ∈ W' := Ideal.mem_map_of_mem _ hfW
    rwa [h, Ideal.mem_bot] at this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  obtain ⟨m, hm⟩ := exists_ringKrullDim_quotient_eq W
  obtain ⟨k, hk⟩ := exists_ringKrullDim_quotient_eq P
  change ringKrullDim B = _ at hk
  rw [hm, hk] at hform hdrop
  rw [hm]
  change _ = ringKrullDim B
  rw [hk]
  have hne : W'.height ≠ ⊤ := ne_top_of_le_ne_top ENat.one_ne_top hht
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hh] at hform hht
  have h1 : h ≤ 1 := by exact_mod_cast hht
  have h2 : h + m = k := by exact_mod_cast hform
  have h3 : m + 1 ≤ k := by exact_mod_cast hdrop
  have : m + 1 = k := by omega
  rw [← this]
  push_cast
  rfl

end SectionComponents

open SectionComponents in

theorem SectionComponents.proof_closed : SectionComponents.Statement := by
  intro F _ n J f hequi hf

  have fwd : ∀ P ∈ J.minimalPrimes, ∀ W : Ideal (MvPolynomial (Fin n) F),
      W ∈ (P ⊔ Ideal.span {f}).minimalPrimes → W ∈ (J ⊔ Ideal.span {f}).minimalPrimes := by
    intro P hP W hW
    have _ : P.IsPrime := hP.1.1
    have _ : W.IsPrime := hW.1.1
    refine ⟨⟨hW.1.1, sup_le_sup_right hP.1.2 _ |>.trans hW.1.2⟩, ?_⟩
    rintro Q ⟨hQ, hJQ⟩ hQW
    obtain ⟨P', hP', hP'Q⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hJQ)
    have _ : P'.IsPrime := hP'.1.1
    obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le
      (sup_le hP'Q (le_sup_right.trans hJQ) : P' ⊔ Ideal.span {f} ≤ Q)
    have _ : W'.IsPrime := hW'.1.1
    have hW'W : W' ≤ W := hW'Q.trans hQW
    suffices W' = W by rw [← this]; exact hW'Q
    by_contra hne
    have hlt := ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hW'W hne)
    rw [ringKrullDim_quotient_add_one_eq (hf P hP) hW, hequi P hP P' hP',
      ← ringKrullDim_quotient_add_one_eq (hf P' hP') hW'] at hlt
    obtain ⟨m, hm⟩ := exists_ringKrullDim_quotient_eq W'
    rw [hm] at hlt
    have : m + 1 ≤ m := by exact_mod_cast hlt
    omega
  intro P hP W
  refine ⟨fun hW => ⟨fwd P hP W hW, le_sup_left.trans hW.1.2⟩, ?_⟩
  rintro ⟨hW, hPW⟩
  have _ : W.IsPrime := hW.1.1
  obtain ⟨W', hW', hW'W⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPW (le_sup_right.trans hW.1.2) : P ⊔ Ideal.span {f} ≤ W)
  have heq : W = W' := le_antisymm (hW.2 (fwd P hP W' hW').1 hW'W) hW'W
  rwa [heq]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeGeoNum
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime IsMultiHomog IsRelevant geoNum)

def ChowDegreeGeoNum.Statement : Prop :=
  ∀ (n e p : ℕ) (W : Ideal (MRing (PBlk n))) (F : Type) [Field F],
    p.Prime → IsMultiProjPrime W → C (p : ℤ) ∈ W →
      ringKrullDim (MRing (PBlk n) ⧸ W) = ((e + 1 : ℕ) : WithBot ℕ∞) →
      Function.Surjective (Int.castRingHom F) → ((p : ℤ) : F) = 0 →
        (chowDegree ((IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F))) (e + 1)
          : ℤ) = geoNum e W (fun _ _ => 1)

def redTwo : MRing (PBlk 1) →+* MvPolynomial (Σ _ : Unit, PBlk 1 ()) (ZMod 2) :=
  MvPolynomial.map (Int.castRingHom (ZMod 2))

def blkOneEquiv : (Σ _ : Unit, PBlk 1 ()) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(), 0⟩
  left_inv := by
    rintro ⟨⟨⟩, i⟩
    fin_cases i
    rfl
  right_inv _ := rfl

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeComponents
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

def ConeIntegralComponents.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℂ),
    IsArithVar P (e + 1) → (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W) →
      ∑ W ∈ (fundCycle (complexFibreIdeal P)).support, coneIntegral h W e (fsLog h u) =
        coneIntegral h (complexFibreIdeal P) e (fsLog h u)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFiniteFibreDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def ConeFiniteFibreDim.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ m

end

end GroundTheory.Heights₂.Heights
end

