import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.StatementsWitness

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PKroneckerLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology Set
open scoped Real UpperHalfPlane ModularForm

noncomputable section

theorem kroneckerLimit_rpow_neg_le {X s : ℝ} (hX : 0 < X) (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    X ^ (-s) ≤ X ^ (-1 : ℝ) + X ^ (-2 : ℝ) := by
  rcases le_total 1 X with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h (show -s ≤ -1 by linarith)
    have := Real.rpow_nonneg hX.le (-2 : ℝ)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hX h (show (-2 : ℝ) ≤ -s by linarith)
    have := Real.rpow_nonneg hX.le (-1 : ℝ)
    linarith

theorem kroneckerLimit_tendsto_shiftedSum (hT : ShiftedSumIntegral.Statement) {a : ℝ} (ha : 0 < a)
    (u : ℝ) :
    Tendsto (fun s : ℝ ↦ ∑' n : ℤ, (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-s)) (𝓝[>] 1)
      (𝓝 (∑' n : ℤ, (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-1 : ℝ))) := by
  have hX : ∀ n : ℤ, 0 < ((n : ℝ) + u) ^ 2 + a ^ 2 := fun n ↦ by positivity
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n : ℤ ↦ (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-1 : ℝ) +
      (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-2 : ℝ))
    ((hT a u 1 ha (by norm_num)).1.add (hT a u 2 ha (by norm_num)).1) (fun n ↦ ?_) ?_
  · have : ContinuousAt (fun s : ℝ ↦ (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-s)) 1 :=
      continuousAt_const.rpow continuousAt_neg (Or.inl (hX n).ne')
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with s hs n
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hX n).le _)]
    exact kroneckerLimit_rpow_neg_le (hX n) hs.1.le hs.2.le

theorem kroneckerLimit_tendsto_zeta_two :
    Tendsto (fun s : ℝ ↦ ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ (2 * s))) (𝓝[>] 1) (𝓝 (π ^ 2 / 6)) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < n + 1 := fun n ↦ by positivity
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℝ) ^ (2 : ℝ))) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_rpow.mpr (show (1 : ℝ) < 2 by norm_num))
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hval : ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ (2 * 1 : ℝ)) = π ^ 2 / 6 := by
    have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, sub_zero] at h
    rw [← h.tsum_eq]
    refine tsum_congr fun n ↦ ?_
    rw [mul_one, Real.rpow_two]
    push_cast
    ring
  rw [← hval]
  refine tendsto_tsum_of_dominated_convergence (bound := fun n : ℕ ↦ 1 / ((n + 1 : ℝ) ^ (2 : ℝ)))
    hsum (fun n ↦ ?_) ?_
  · have : ContinuousAt (fun s : ℝ ↦ 1 / ((n + 1 : ℝ) ^ (2 * s))) 1 :=
      continuousAt_const.div
        (continuousAt_const.rpow (continuousAt_const.mul continuousAt_id) (Or.inl (hpos n).ne'))
        (Real.rpow_pos_of_pos (hpos n) _).ne'
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s) n
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := Real.rpow_pos_of_pos (hpos n) (2 * s); positivity)]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (hpos n) _)
      (Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
        (by linarith))

theorem kroneckerLimit_tendsto_gammaRatio :
    Tendsto (fun s : ℝ ↦ √π * Real.Gamma (s - 1 / 2) / Real.Gamma s) (𝓝[>] 1) (𝓝 π) := by
  have hG12 : ContinuousAt Real.Gamma (1 - 1 / 2) :=
    (Real.differentiableAt_Gamma fun m h ↦ by
      have := (m.cast_nonneg : (0 : ℝ) ≤ m); linarith).continuousAt
  have hG1 : ContinuousAt Real.Gamma 1 :=
    (Real.differentiableAt_Gamma fun m h ↦ by
      have := (m.cast_nonneg : (0 : ℝ) ≤ m); linarith).continuousAt
  have hnum : ContinuousAt (fun s : ℝ ↦ √π * Real.Gamma (s - 1 / 2)) 1 :=
    continuousAt_const.mul (hG12.comp_of_eq (continuousAt_id.sub continuousAt_const) rfl)
  have hcont : ContinuousAt (fun s : ℝ ↦ √π * Real.Gamma (s - 1 / 2) / Real.Gamma s) 1 :=
    hnum.div hG1 (by rw [Real.Gamma_one]; norm_num)
  have hval : √π * Real.Gamma (1 - 1 / 2) / Real.Gamma 1 = π := by
    rw [Real.Gamma_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq, div_one,
      Real.mul_self_sqrt Real.pi_pos.le]
  have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
  beta_reduce at h
  rwa [hval] at h

theorem kroneckerLimit_term_bound (hI : PowerIntegral.Statement) (hT : ShiftedSumIntegral.Statement)
    {y : ℝ} (hy : 0 < y) (x : ℝ) (m : ℕ) {s : ℝ} (h1 : 1 < s) (h2 : s < 2) :
    ‖y ^ s * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * x) ^ 2 + ((m + 1) * y) ^ 2) ^ (-s)) -
        √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * ((m + 1) * y) ^ (1 - 2 * s))‖ ≤
      (y ^ (-1 : ℝ) + y ^ (-2 : ℝ)) * ((m : ℝ) + 1) ^ (-2 : ℝ) := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hA : 0 < ((m : ℝ) + 1) * y := by positivity
  have hb := (hT _ ((m + 1) * x) s hA (by linarith)).2
  rw [hI _ s hA (by linarith)] at hb
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy s)]
  calc y ^ s * |_| ≤ y ^ s * (((m : ℝ) + 1) * y) ^ (-2 * s) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hy.le _)
    _ = ((m : ℝ) + 1) ^ (-2 * s) * y ^ (-s) := by
        rw [Real.mul_rpow hm.le hy.le, show -s = s + -2 * s by ring, Real.rpow_add hy]; ring
    _ ≤ ((m : ℝ) + 1) ^ (-2 : ℝ) * (y ^ (-1 : ℝ) + y ^ (-2 : ℝ)) :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le
            (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]) (by linarith))
          (kroneckerLimit_rpow_neg_le hy h1.le h2.le)
          (Real.rpow_nonneg hy.le _)
          (Real.rpow_nonneg hm.le _)
    _ = _ := by ring

theorem kroneckerLimit_main_term {y : ℝ} (hy : 0 < y) (c s : ℝ) (m : ℕ) :
    y ^ s * (c * (((m : ℝ) + 1) * y) ^ (1 - 2 * s)) =
      c * y ^ (1 - s) * (1 / (((m : ℝ) + 1) ^ (2 * s - 1))) := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  rw [Real.mul_rpow hm.le hy.le, show (1 - 2 * s) = -(2 * s - 1) by ring, Real.rpow_neg hm.le,
    show (1 - s) = s + -(2 * s - 1) by ring, Real.rpow_add hy]
  ring

theorem KroneckerLimit.proof (hS : KroneckerSplit.Statement) (hI : PowerIntegral.Statement)
    (hT : ShiftedSumIntegral.Statement) (hC : CotangentSum.Statement) (hE : LogEta.Statement)
    (hG : GammaZetaLimit.Statement) : KroneckerLimit.Statement := by
  intro τ
  have hy : 0 < τ.im := τ.im_pos
  have hA : ∀ m : ℕ, 0 < ((m : ℝ) + 1) * τ.im := fun m ↦ by positivity
  have hsum2 : Summable (fun m : ℕ ↦
      (τ.im ^ (-1 : ℝ) + τ.im ^ (-2 : ℝ)) * ((m : ℝ) + 1) ^ (-2 : ℝ)) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num))
    exact (by simpa [Nat.cast_add, Nat.cast_one] using this :
      Summable (fun m : ℕ ↦ ((m : ℝ) + 1) ^ (-2 : ℝ))).mul_left _
  have hys : Tendsto (fun s : ℝ ↦ τ.im ^ s) (𝓝[>] 1) (𝓝 τ.im) := by
    have := ((Real.continuousAt_const_rpow (b := 1) hy.ne').tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    simpa using this

  have hD : Tendsto (fun s : ℝ ↦ ∑' m : ℕ, τ.im ^ s * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)) -
          √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * ((m + 1) * τ.im) ^ (1 - 2 * s)))
      (𝓝[>] 1) (𝓝 (∑' m : ℕ, τ.im * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-1 : ℝ)) - π * ((m + 1) * τ.im) ^ (-1 : ℝ)))) := by
    refine tendsto_tsum_of_dominated_convergence hsum2 (fun m ↦ ?_) ?_
    · have h2 : Tendsto (fun s : ℝ ↦ (((m : ℝ) + 1) * τ.im) ^ (1 - 2 * s)) (𝓝[>] 1)
          (𝓝 ((((m : ℝ) + 1) * τ.im) ^ (-1 : ℝ))) := by
        have : ContinuousAt (fun s : ℝ ↦ (((m : ℝ) + 1) * τ.im) ^ (1 - 2 * s)) 1 :=
          continuousAt_const.rpow (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
            (Or.inl (hA m).ne')
        have h := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
        beta_reduce at h
        rwa [show (1 : ℝ) - 2 * 1 = -1 by norm_num] at h
      exact hys.mul ((kroneckerLimit_tendsto_shiftedSum hT (hA m) _).sub
        (kroneckerLimit_tendsto_gammaRatio.mul h2))
    · filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with s hs m
      exact kroneckerLimit_term_bound hI hT hy τ.re m hs.1 hs.2

  have hEq : ∀ s : ℝ, 1 < s → s < 2 →
      kroneckerSum τ s - π / (s - 1) =
        2 * τ.im ^ s * (∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ (2 * s))) +
        2 * (∑' m : ℕ, τ.im ^ s * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)) -
          √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * ((m + 1) * τ.im) ^ (1 - 2 * s))) +
        (2 * (√π * Real.Gamma (s - 1 / 2) / Real.Gamma s) * τ.im ^ (1 - s) *
          (∑' m : ℕ, 1 / ((m + 1 : ℝ) ^ (2 * s - 1))) - π / (s - 1)) := by
    intro s h1 h2
    set c := √π * Real.Gamma (s - 1 / 2) / Real.Gamma s with hc
    have hDs : Summable (fun m : ℕ ↦ τ.im ^ s * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)) - c * ((m + 1) * τ.im) ^ (1 - 2 * s))) :=
      Summable.of_norm_bounded hsum2 (fun m ↦ kroneckerLimit_term_bound hI hT hy τ.re m h1 h2)
    have hM : ∑' m : ℕ, τ.im ^ s * (c * ((m + 1) * τ.im) ^ (1 - 2 * s)) =
        c * τ.im ^ (1 - s) * ∑' m : ℕ, 1 / ((m + 1 : ℝ) ^ (2 * s - 1)) := by
      simp_rw [kroneckerLimit_main_term hy]
      exact tsum_mul_left
    have hMs : Summable (fun m : ℕ ↦ τ.im ^ s * (c * ((m + 1) * τ.im) ^ (1 - 2 * s))) := by
      simp_rw [kroneckerLimit_main_term hy]
      refine Summable.mul_left _ ?_
      have := (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_rpow.mpr (show 1 < 2 * s - 1 by linarith))
      simpa [Nat.cast_add, Nat.cast_one] using this
    have hsplit : ∑' m : ℕ, τ.im ^ s * (∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)) =
        (∑' m : ℕ, τ.im ^ s * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)) - c * ((m + 1) * τ.im) ^ (1 - 2 * s))) +
        ∑' m : ℕ, τ.im ^ s * (c * ((m + 1) * τ.im) ^ (1 - 2 * s)) := by
      rw [← hDs.tsum_add hMs]
      exact tsum_congr fun m ↦ by ring
    rw [hS τ s h1, hsplit, hM]
    ring

  have hD' : ∑' m : ℕ, τ.im * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-1 : ℝ)) - π * ((m + 1) * τ.im) ^ (-1 : ℝ)) =
      2 * π * (-(π * τ.im / 12) - Real.log ‖η (τ : ℂ)‖) := by
    rw [← (hE τ).tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun m ↦ ?_
    rw [hC _ _ (hA m)]
    have hq : Complex.exp (2 * π * Complex.I *
        ((((m + 1) * τ.re : ℝ) : ℂ) + (((m + 1) * τ.im : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (2 * π * Complex.I * (τ : ℂ)) ^ (m + 1) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      conv_rhs => rw [← Complex.re_add_im (τ : ℂ)]
      push_cast
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    rw [hq]
    simp_rw [← pow_mul]
    rw [Real.rpow_neg_one]
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    have := hy.ne'
    field_simp
    ring
  have hη : η (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hval : 2 * τ.im * (π ^ 2 / 6) +
      2 * (∑' m : ℕ, τ.im * ((∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-1 : ℝ)) - π * ((m + 1) * τ.im) ^ (-1 : ℝ))) +
      (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log τ.im) =
      2 * π * (Real.eulerMascheroniConstant - Real.log 2 -
        Real.log (Real.sqrt τ.im * ‖η (τ : ℂ)‖ ^ 2)) := by
    rw [hD', Real.log_mul (Real.sqrt_pos.mpr hy).ne' (pow_pos (norm_pos_iff.mpr hη) 2).ne',
      Real.log_sqrt hy.le, Real.log_pow]
    push_cast
    ring
  rw [← hval]
  refine Tendsto.congr' ?_ (((((tendsto_const_nhds (x := (2 : ℝ))).mul hys).mul
    kroneckerLimit_tendsto_zeta_two).add (tendsto_const_nhds.mul hD)).add (hG τ.im hy))
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with s hs
  exact (hEq s hs.1 hs.2).symm

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PKroneckerSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

lemma kroneckerTerm_eq (τ : ℍ) {s : ℝ} (hs : 0 < s) (p : ℤ × ℤ) :
    (if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)) =
      τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s) := by
  split_ifs with h
  · subst h
    simp [Real.zero_rpow (mul_pos two_pos hs).ne']
  · rfl

lemma summable_kroneckerTerm (τ : ℍ) {s : ℝ} (hs : 1 < s) :
    Summable fun p : ℤ × ℤ ↦ τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s) := by
  have hk : 2 < 2 * s := by linarith
  have hy : 0 ≤ τ.im ^ s := Real.rpow_nonneg τ.im_pos.le _
  have h1 := (EisensteinSeries.summable_one_div_norm_rpow hk).mul_left
    (τ.im ^ s * EisensteinSeries.r τ ^ (-(2 * s)))
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at h1
  refine Summable.of_nonneg_of_le
    (fun p ↦ div_nonneg hy (Real.rpow_nonneg (norm_nonneg _) _)) (fun p ↦ ?_) h1
  have hb := EisensteinSeries.summand_bound τ (by linarith : (0 : ℝ) ≤ 2 * s)
    ((finTwoArrowEquiv ℤ).symm p)
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.comp_apply] at hb ⊢
  rw [div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg _), mul_assoc]
  exact mul_le_mul_of_nonneg_left hb hy

lemma kroneckerTerm_eq_rpow (τ : ℍ) (s : ℝ) (m n : ℤ) :
    τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) =
      τ.im ^ s * (((n : ℝ) + m * τ.re) ^ 2 + (m * τ.im) ^ 2) ^ (-s) := by
  have h : ‖(m : ℂ) * τ + n‖ ^ 2 = ((n : ℝ) + m * τ.re) ^ 2 + (m * τ.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two, h, Real.rpow_neg (by positivity),
    div_eq_mul_inv]

lemma kroneckerTerm_neg (τ : ℍ) (s : ℝ) (m n : ℤ) :
    τ.im ^ s / ‖((-m : ℤ) : ℂ) * τ + ((-n : ℤ) : ℂ)‖ ^ (2 * s) =
      τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) := by
  rw [show ((-m : ℤ) : ℂ) * τ + ((-n : ℤ) : ℂ) = -((m : ℂ) * τ + n) by push_cast; ring, norm_neg]

lemma tsum_int_split {f : ℤ → ℝ} (h : Summable f) :
    ∑' n : ℤ, f n = ∑' n : ℕ, f (n + 1) + f 0 + ∑' n : ℕ, f (-(n + 1)) :=
  tsum_of_add_one_of_neg_add_one
    (h.comp_injective (show Function.Injective fun n : ℕ ↦ (n : ℤ) + 1 from
      fun a b h ↦ by simpa using h))
    (h.comp_injective (show Function.Injective fun n : ℕ ↦ -((n : ℤ) + 1) from
      fun a b h ↦ by simpa using h))

lemma kroneckerRow_zero (τ : ℍ) {s : ℝ} (hs : 0 < s)
    (h : Summable fun n : ℤ ↦ τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + n‖ ^ (2 * s)) :
    ∑' n : ℤ, τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + n‖ ^ (2 * s) =
      2 * τ.im ^ s * ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ (2 * s)) := by
  rw [tsum_int_split h]
  have e1 : ∀ n : ℕ, τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + (((n : ℤ) + 1 : ℤ) : ℂ)‖ ^ (2 * s) =
      τ.im ^ s * (1 / ((n + 1 : ℝ) ^ (2 * s))) := by
    intro n
    have : ‖((0 : ℤ) : ℂ) * τ + (((n : ℤ) + 1 : ℤ) : ℂ)‖ = (n : ℝ) + 1 := by
      rw [show ((0 : ℤ) : ℂ) * τ + (((n : ℤ) + 1 : ℤ) : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [this, mul_one_div]
  have e2 : ∀ n : ℕ, τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + ((-((n : ℤ) + 1) : ℤ) : ℂ)‖ ^ (2 * s) =
      τ.im ^ s * (1 / ((n + 1 : ℝ) ^ (2 * s))) := by
    intro n
    rw [← e1 n]
    simpa using kroneckerTerm_neg τ s 0 ((n : ℤ) + 1)
  have e0 : τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + ((0 : ℤ) : ℂ)‖ ^ (2 * s) = 0 := by
    simp [Real.zero_rpow (mul_pos two_pos hs).ne']
  simp only [e1, e2, e0, add_zero, tsum_mul_left]
  ring

lemma kroneckerRow_neg (τ : ℍ) (s : ℝ) (m : ℤ) :
    ∑' n : ℤ, τ.im ^ s / ‖((-m : ℤ) : ℂ) * τ + n‖ ^ (2 * s) =
      ∑' n : ℤ, τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) := by
  rw [← tsum_comp_neg]
  exact tsum_congr fun n ↦ kroneckerTerm_neg τ s m n

theorem KroneckerSplit.proof : KroneckerSplit.Statement := by
  intro τ s hs
  have hs0 : 0 < s := by linarith
  have hsum := summable_kroneckerTerm τ hs
  have hcol : Summable fun m : ℤ ↦ ∑' n : ℤ, τ.im ^ s / ‖(m : ℂ) * τ + n‖ ^ (2 * s) :=
    hsum.prod
  rw [kroneckerSum, tsum_congr (kroneckerTerm_eq τ hs0), hsum.tsum_prod, tsum_int_split hcol]
  have hrow0 : Summable fun n : ℤ ↦ τ.im ^ s / ‖((0 : ℤ) : ℂ) * τ + n‖ ^ (2 * s) :=
    hsum.prod_factor 0
  simp only [kroneckerRow_neg, kroneckerRow_zero τ hs0 hrow0]
  have e : ∀ m : ℕ, ∑' n : ℤ, τ.im ^ s / ‖(((m : ℤ) + 1 : ℤ) : ℂ) * τ + n‖ ^ (2 * s) =
      τ.im ^ s * ∑' n : ℤ, (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s) := by
    intro m
    rw [← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [kroneckerTerm_eq_rpow]
    push_cast
    rfl
  simp only [e]
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PPowerIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open MeasureTheory Set Real

noncomputable section

theorem PowerIntegral.integral_rpow_mul_exp_neg_mul {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * exp (-(c * u)) = c ^ (-s) * Gamma s := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := s - 1) (b := c) one_pos
    (by linarith) hc
  have e1 : (-(s - 1 + 1) / 1 : ℝ) = -s := by ring
  have e2 : ((s - 1 + 1) / 1 : ℝ) = s := by ring
  rw [e1, e2, one_div_one, mul_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  simp only [rpow_one, neg_mul]

theorem PowerIntegral.integrand_split (a s u t : ℝ) :
    u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) =
      (u ^ (s - 1) * exp (-(a ^ 2 * u))) * exp (-u * t ^ 2) := by
  rw [mul_assoc, ← exp_add]
  ring_nf

theorem PowerIntegral.proof : PowerIntegral.Statement := by
  intro a s ha hs
  have hs0 : 0 < s := by linarith
  have hΓ : Gamma s ≠ 0 := (Gamma_pos_of_pos hs0).ne'
  have h1 : ∀ t : ℝ, (t ^ 2 + a ^ 2) ^ (-s) =
      (Gamma s)⁻¹ * ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) := by
    intro t
    rw [PowerIntegral.integral_rpow_mul_exp_neg_mul (by positivity) hs0,
      mul_comm ((t ^ 2 + a ^ 2) ^ (-s)), ← mul_assoc, inv_mul_cancel₀ hΓ, one_mul]
  have h2 : ∀ u ∈ Ioi (0 : ℝ), ∫ t : ℝ, u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) =
      √π * (u ^ (s - 3 / 2) * exp (-(a ^ 2 * u))) := by
    intro u hu
    have hu : 0 < u := hu
    simp_rw [PowerIntegral.integrand_split a s u]
    rw [integral_const_mul, integral_gaussian, sqrt_div pi_pos.le]
    have e : u ^ (s - 3 / 2) = u ^ (s - 1) / √u := by
      rw [sqrt_eq_rpow, ← rpow_sub hu]
      congr 1
      ring
    have hsu : 0 < √u := sqrt_pos.mpr hu
    rw [e]
    field_simp
  have hmeas : Measurable
      (Function.uncurry fun t u : ℝ => u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u))) := by
    unfold Function.uncurry
    fun_prop
  have hint : Integrable
      (Function.uncurry fun t u : ℝ => u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
      have hu : 0 < u := hu
      simp only [Function.uncurry_apply_pair]
      simp_rw [PowerIntegral.integrand_split a s u]
      exact (integrable_exp_neg_mul_sq hu).const_mul _
    · have hq : (-1 : ℝ) < s - 3 / 2 := by linarith
      have hI := (integrableOn_rpow_mul_exp_neg_mul_rpow hq one_pos (pow_pos ha 2)).const_mul √π
      refine IntegrableOn.congr_fun hI (fun u hu => ?_) measurableSet_Ioi
      have hu : 0 < u := hu
      simp only [Function.uncurry_apply_pair]
      simp only [rpow_one, neg_mul]
      rw [← h2 u hu]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      exact (norm_of_nonneg (mul_nonneg (rpow_nonneg hu.le _) (exp_pos _).le)).symm
  have hpow : (a ^ 2) ^ (-(s - 1 / 2)) = a ^ (1 - 2 * s) := by
    rw [← rpow_natCast, ← rpow_mul ha.le]
    congr 1
    push_cast
    ring
  have hs' : 0 < s - 1 / 2 := by linarith
  calc ∫ t : ℝ, (t ^ 2 + a ^ 2) ^ (-s)
      = ∫ t : ℝ, (Gamma s)⁻¹ *
          ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) :=
        integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = (Gamma s)⁻¹ * ∫ u in Ioi (0 : ℝ), ∫ t : ℝ,
          u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) := by
        rw [integral_const_mul, integral_integral_swap hint]
    _ = (Gamma s)⁻¹ * ∫ u in Ioi (0 : ℝ), √π * (u ^ (s - 3 / 2) * exp (-(a ^ 2 * u))) := by
        rw [setIntegral_congr_fun measurableSet_Ioi h2]
    _ = (Gamma s)⁻¹ * (√π * ((a ^ 2) ^ (-(s - 1 / 2)) * Gamma (s - 1 / 2))) := by
        rw [integral_const_mul, show s - 3 / 2 = (s - 1 / 2) - 1 by ring,
          PowerIntegral.integral_rpow_mul_exp_neg_mul (pow_pos ha 2) hs']
    _ = √π * Gamma (s - 1 / 2) / Gamma s * a ^ (1 - 2 * s) := by
        rw [hpow]
        field_simp

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.StatementsMean
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

def PeriodLatticeCM.Statement (_S : PrimeDiscriminant K) (F : CMFamily K) : Prop :=
  ∀ s : F.k →+* ℂ, ∃ L : PeriodPair,
    F.periodLattice s = L.lattice ∧ latticeEnd L = cmRing (F.restrict s)

def IdealInvArea.Statement (_S : PrimeDiscriminant K) : Prop :=
  ∀ (σ : K →+* ℂ) (L : PeriodPair), latticeEnd L = cmRing σ →
    ∀ 𝔞 : (Ideal (𝓞 K))⁰,
      latticeArea (idealLattice σ ↑(FractionalIdeal.mk0 K 𝔞)⁻¹ * L.lattice) =
        latticeArea L.lattice / (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.SuperlatticeRatio
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial
open scoped Real MatrixGroups Manifold

noncomputable section

def SuperlatticeRatio.Statement : Prop :=
  ∀ (L L' : PeriodPair) (p : ℕ) (hp : p.Prime), L.lattice ≤ L'.lattice →
    L.lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup = p →
      ∃ τ : ℍ, (weierstrassCurve L).j = modularJ τ ∧
        latticeDiscr L'.lattice / latticeDiscr L.lattice ∈ heckeRatios ⟨p, hp.pos⟩ τ

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

