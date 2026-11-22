import Mathlib

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailKernel
section
open Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem norm_exp_sub_one_le_of_re_nonneg (u : ℂ) (hu : 0 ≤ u.re) :
    ‖Complex.exp u - 1‖ ≤ Real.exp u.re * ‖u‖ := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => Complex.exp ((t : ℂ) * u)) (f' := fun t : ℝ => Complex.exp ((t : ℂ) * u) * u)
    (C := Real.exp u.re * ‖u‖) (a := 0) (b := 1)
    (fun t _ => by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * u) u t := by
        simpa using ((hasDerivAt_id t).ofReal_comp).mul_const u
      exact h1.cexp.hasDerivWithinAt)
    (fun t ht => by
      rw [norm_mul, Complex.norm_exp]
      have hre : ((t : ℂ) * u).re = t * u.re := by simp
      rw [hre]
      gcongr
      nlinarith [ht.1, ht.2])
    1 (by simp)
  simpa using key

theorem tail_kernel_cpow (y η : ℝ) (hy : 0 < y) (hη : 0 ≤ η) (hη1 : η ≤ 1) (w : ℂ) (hw0 : 0 ≤ w.re)
    (hw2 : w.re ≤ 2) :
    ‖((y * (1 + η) : ℝ) : ℂ) ^ w - (y : ℂ) ^ w‖ ≤ 4 * η * ‖w‖ * y ^ w.re := by
  have hy1 : (0 : ℝ) < 1 + η := by linarith
  have hL0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
  have hLη : Real.log (1 + η) ≤ η := by
    have := Real.log_le_sub_one_of_pos hy1
    linarith
  have hL2 : Real.log (1 + η) ≤ Real.log 2 := Real.log_le_log hy1 (by linarith)
  have hsplit : ((y * (1 + η) : ℝ) : ℂ) ^ w = (y : ℂ) ^ w * ((1 + η : ℝ) : ℂ) ^ w := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg hy.le hy1.le w
  have hpow : ((1 + η : ℝ) : ℂ) ^ w = Complex.exp (w * (Real.log (1 + η) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy1.ne'), ← Complex.ofReal_log hy1.le, mul_comm]
  have hre : 0 ≤ (w * (Real.log (1 + η) : ℂ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg hw0 hL0
  have hb := norm_exp_sub_one_le_of_re_nonneg _ hre
  have hre' : (w * (Real.log (1 + η) : ℂ)).re = w.re * Real.log (1 + η) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hnorm : ‖w * (Real.log (1 + η) : ℂ)‖ = ‖w‖ * Real.log (1 + η) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
  have hexp : Real.exp (w.re * Real.log (1 + η)) ≤ 4 := by
    have h4 : Real.exp (2 * Real.log 2) = 4 := by
      rw [two_mul, Real.exp_add, Real.exp_log two_pos]; norm_num
    rw [← h4]
    apply Real.exp_le_exp.mpr
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  rw [hre', hnorm] at hb
  have hyw : ‖(y : ℂ) ^ w‖ = y ^ w.re := Complex.norm_cpow_eq_rpow_re_of_pos hy w
  have hypos : 0 ≤ y ^ w.re := Real.rpow_nonneg hy.le _
  rw [hsplit, hpow, ← mul_sub_one, norm_mul, hyw]
  calc y ^ w.re * ‖Complex.exp (w * (Real.log (1 + η) : ℂ)) - 1‖
      ≤ y ^ w.re * (Real.exp (w.re * Real.log (1 + η)) * (‖w‖ * Real.log (1 + η))) := by gcongr
    _ ≤ y ^ w.re * (4 * (‖w‖ * η)) := by
        gcongr
    _ = 4 * η * ‖w‖ * y ^ w.re := by ring

theorem tail_kernel_norm_lower (σ u : ℝ) (hσ1 : σ ≤ 1 - 1 / 800) :
    (1 / 800 + |u|) / 2 ≤ ‖(σ : ℂ) + (u : ℂ) * I - 1‖ := by
  have h1 := Complex.abs_re_le_norm ((σ : ℂ) + (u : ℂ) * I - 1)
  have h2 := Complex.abs_im_le_norm ((σ : ℂ) + (u : ℂ) * I - 1)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add] at h1 h2
  have hre : 1 / 800 ≤ |σ - 1| := by
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  linarith

theorem tail_kernel_half (T : ℝ) (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, 2 / (1 / 800 + u) = 2 * Real.log (1 + 800 * T) := by
  have hfun : (fun u : ℝ => 2 / (1 / 800 + u)) = fun u => 2 * (u + 1 / 800)⁻¹ := by
    funext u; rw [div_eq_mul_inv, add_comm]
  have hsh := intervalIntegral.integral_comp_add_right (a := 0) (b := T) (fun x : ℝ => x⁻¹) (1 / 800)
  rw [hfun, intervalIntegral.integral_const_mul, hsh,
    integral_inv_of_pos (by norm_num) (by linarith)]
  congr 2
  field_simp
  ring

theorem tail_kernel_line (σ T : ℝ) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1 - 1 / 800) (hT : 0 ≤ T) :
    ∫ u in (-T)..T, 1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖ ≤ 4 * Real.log (1 + 800 * T) := by
  have hg : Continuous (fun u : ℝ => 2 / (1 / 800 + |u|)) :=
    Continuous.div continuous_const (continuous_const.add continuous_abs) (fun x => by positivity)
  have hne : ∀ u : ℝ, ‖(σ : ℂ) + (u : ℂ) * I - 1‖ ≠ 0 := by
    intro u
    have := tail_kernel_norm_lower σ u hσ1
    have : 0 < (1 / 800 + |u|) / 2 := by positivity
    linarith
  have hf : Continuous (fun u : ℝ => 1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖) :=
    Continuous.div continuous_const
      (((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).norm) hne
  calc ∫ u in (-T)..T, 1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖
      ≤ ∫ u in (-T)..T, 2 / (1 / 800 + |u|) := by
        apply intervalIntegral.integral_mono_on (by linarith) (hf.intervalIntegrable _ _)
          (hg.intervalIntegrable _ _)
        intro u _
        have h3 := tail_kernel_norm_lower σ u hσ1
        have hp : 0 < (1 / 800 + |u|) / 2 := by positivity
        have := one_div_le_one_div_of_le hp h3
        rwa [one_div_div] at this
    _ = 4 * Real.log (1 + 800 * T) := by
        have hsplit := (intervalIntegral.integral_add_adjacent_intervals (a := -T) (b := 0) (c := T)
          (hg.intervalIntegrable (μ := MeasureTheory.volume) _ _)
          (hg.intervalIntegrable (μ := MeasureTheory.volume) _ _))
        have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := T)
          (fun u : ℝ => 2 / (1 / 800 + |u|))
        simp only [neg_zero, abs_neg] at hneg
        have hpos : ∫ u in (0 : ℝ)..T, 2 / (1 / 800 + |u|) = ∫ u in (0 : ℝ)..T, 2 / (1 / 800 + u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [Set.uIcc_of_le hT] at hu
          simp only [abs_of_nonneg hu.1]
        rw [← hsplit, ← hneg, hpos, tail_kernel_half T hT]
        ring

end Formalism.HermitianLattices.Ext.BoxTail
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailMertens
section
open Finset ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_mertens_psi (N : ℕ) :
    ∑ n ∈ Icc 1 N, (Λ n : ℝ) ≤ (Real.log 4 + 4) * (N : ℝ) := by
  have h := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (Nat.cast_nonneg N)
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast] at h
  have hsub : ∑ n ∈ Icc 1 N, (Λ n : ℝ) = ∑ n ∈ Icc 0 N, (Λ n : ℝ) := by
    apply Finset.sum_subset
    · intro n hn
      simp only [mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      simp only [mem_Icc] at hn hn'
      have h0 : n = 0 := by omega
      subst h0
      simp
  rw [hsub]
  exact h

theorem tail_mertens_nat (N : ℕ) :
    ∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ) / (n : ℝ) ≤
      (∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ)) / ((N : ℝ) + 1)
        + (Real.log 4 + 4) * Real.log ((N : ℝ) + 1) := by
  have hc : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  induction N with
  | zero => simp
  | succ M ih =>
    have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
    have hM2 : (0:ℝ) < (M:ℝ) + 1 + 1 := by positivity
    have hB := tail_mertens_psi (M + 1)
    push_cast at hB
    have hlog : 1 / ((M:ℝ) + 1 + 1) ≤ Real.log ((M:ℝ) + 1 + 1) - Real.log ((M:ℝ) + 1) := by
      rw [← Real.log_div hM2.ne' hM1.ne']
      have h := Real.one_sub_inv_le_log_of_pos (x := ((M:ℝ) + 1 + 1) / ((M:ℝ) + 1)) (by positivity)
      calc 1 / ((M:ℝ) + 1 + 1) = 1 - (((M:ℝ) + 1 + 1) / ((M:ℝ) + 1))⁻¹ := by
            field_simp
            ring
        _ ≤ _ := h
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 + 1 by omega)]
    push_cast
    set B := ∑ n ∈ Icc 1 (M + 1), (Λ n : ℝ) with hBdef
    set L := (Λ (M + 1 + 1) : ℝ) with hLdef
    have key1 : B / ((M:ℝ) + 1) ≤ (B + (Real.log 4 + 4)) / ((M:ℝ) + 1 + 1) := by
      rw [div_le_div_iff₀ hM1 hM2]
      nlinarith
    have key2 : (Real.log 4 + 4) / ((M:ℝ) + 1 + 1) ≤
        (Real.log 4 + 4) * (Real.log ((M:ℝ) + 1 + 1) - Real.log ((M:ℝ) + 1)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hlog hc
    rw [add_div] at key1 ⊢
    linarith

theorem tail_mertens : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 2 ≤ y →
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ C * Real.log y := by
  have hc : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 4 + 4) * (1 / Real.log 2 + 1),
    mul_nonneg hc (add_nonneg (one_div_nonneg.2 hl2.le) zero_le_one), ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  obtain ⟨M, hM⟩ : ∃ M, ⌊y⌋₊ = M + 1 :=
    ⟨⌊y⌋₊ - 1, by
      have : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega⟩
  rw [hM]
  have h1 := tail_mertens_nat M
  have hpsi := tail_mertens_psi (M + 1)
  push_cast at hpsi
  have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
  have hMy : (M:ℝ) + 1 ≤ y := by
    have := Nat.floor_le hy0
    rw [hM] at this
    push_cast at this
    exact this
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlogM : Real.log ((M:ℝ) + 1) ≤ Real.log y := Real.log_le_log hM1 hMy
  have hq : (∑ n ∈ Icc 1 (M + 1), (Λ n : ℝ)) / ((M:ℝ) + 1) ≤ Real.log 4 + 4 := by
    rw [div_le_iff₀ hM1]
    exact hpsi
  have hone : 1 ≤ Real.log y / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    linarith
  calc _ ≤ (Real.log 4 + 4) + (Real.log 4 + 4) * Real.log y := by
        have := mul_le_mul_of_nonneg_left hlogM hc
        linarith
    _ ≤ (Real.log 4 + 4) * (Real.log y / Real.log 2) + (Real.log 4 + 4) * Real.log y := by
        have := mul_le_mul_of_nonneg_left hone hc
        linarith
    _ = (Real.log 4 + 4) * (1 / Real.log 2 + 1) * Real.log y := by
        field_simp

end Formalism.HermitianLattices.Ext.BoxTail
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailNum
section
noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_num_rpow (x ε : ℝ) (hx : 0 < x) :
    (x ^ 400) ^ (1 - 1 / 400 + ε / 1600 : ℝ) = x ^ 399 * x ^ (ε / 4) := by
  rw [← Real.rpow_natCast x 400, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x 399,
    ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

theorem tail_num_alg (x Q K l a g : ℝ) (hx : 0 < x) (hQ : 0 < Q) :
    x * ((K * l * (l * (1 / x ^ 2) * (x ^ 399 * a) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * g / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2)))
      = K * l ^ 2 * a + K * (l * x ^ 403 / Q) + (x ^ 398 + 1) * g / x ^ 399 := by
  have hx0 : x ≠ 0 := hx.ne'
  have hQ0 : Q ≠ 0 := hQ.ne'
  field_simp

theorem tail_num_third (x : ℝ) (hx : 3 ≤ x) :
    (x ^ 398 + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 399 ≤ 802 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hp : 0 < x ^ 398 := by positivity
  have hp1 : 1 ≤ x ^ 398 := one_le_pow₀ hx1
  have hA : x ^ 400 + x ^ 400 * (1 / x ^ 2) = x ^ 398 * (x ^ 2 + 1) := by
    field_simp
  have hsq : x ^ 2 + 1 ≤ x ^ 3 := by nlinarith
  have hA1 : x ^ 398 * (x ^ 2 + 1) ≤ x ^ 401 := by
    have : x ^ 401 = x ^ 398 * x ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsq hp.le
  have hApos : 0 < x ^ 398 * (x ^ 2 + 1) := by positivity
  have hAge : 1 ≤ x ^ 398 * (x ^ 2 + 1) := by nlinarith
  have hL0 : 0 ≤ Real.log (x ^ 398 * (x ^ 2 + 1)) := Real.log_nonneg hAge
  have hL1 : Real.log (x ^ 398 * (x ^ 2 + 1)) ≤ 401 * x := by
    calc Real.log (x ^ 398 * (x ^ 2 + 1)) ≤ Real.log (x ^ 401) := Real.log_le_log hApos hA1
      _ = 401 * Real.log x := by rw [Real.log_pow]; norm_num
      _ ≤ 401 * x := by
        have := Real.log_le_sub_one_of_pos hx0
        linarith
  have hx399 : x ≤ x ^ 399 := by
    have : x ^ 399 = x * x ^ 398 := by ring
    rw [this]
    nlinarith
  rw [hA, div_le_iff₀ (by positivity : (0:ℝ) < x ^ 399)]
  calc (x ^ 398 + 1) * Real.log (x ^ 398 * (x ^ 2 + 1))
      ≤ (x ^ 398 + 1) * (401 * x) := mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = 401 * x ^ 399 + 401 * x := by ring
    _ ≤ 802 * x ^ 399 := by linarith

theorem tail_num_exp (ε K : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop, K * (x ^ 404 * Real.exp (-(x ^ (ε / 6)))) ≤ 1 / 3 := by
  have hs : 0 < ε / 6 := by positivity
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ (ε / 6)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hs
  have h2 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (404 / (ε / 6)) 1 one_pos).comp h1
  have hc : ε / 6 * (404 / (ε / 6)) = (404 : ℝ) := by field_simp
  have h3 : Filter.Tendsto (fun x : ℝ => x ^ 404 * Real.exp (-(x ^ (ε / 6))))
      Filter.atTop (nhds 0) := by
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    simp only [Function.comp, neg_mul, one_mul]
    rw [← Real.rpow_mul hx.le, hc]
    congr 1
    exact_mod_cast Real.rpow_natCast x 404
  have h4 : Filter.Tendsto (fun x : ℝ => K * (x ^ 404 * Real.exp (-(x ^ (ε / 6)))))
      Filter.atTop (nhds 0) := by
    simpa using h3.const_mul K
  exact h4.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))

theorem tail_num (ε K : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 0 ≤ K) : ∃ x₀ : ℝ, 3 ≤ x₀ ∧
    ∀ x Q : ℝ, x₀ ≤ x → 0 < Q → x ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (ε / 4) →
      x * ((K * Real.log Q * (Real.log Q * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + ε / 1600) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ x ^ ε := by
  have hq : 0 < ε / 4 := by positivity
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      K * (x ^ 404 * Real.exp (-(x ^ (ε / 6)))) ≤ 1 / 3 ∧ K + 803 ≤ x ^ (ε / 4) :=
    (tail_num_exp ε K hε).and
      ((tendsto_rpow_atTop hq).eventually (Filter.eventually_ge_atTop (K + 803)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max N 3, le_max_right _ _, ?_⟩
  intro x Q hx hQ hlo hhi
  have hxN : N ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hexp, hy⟩ := hN x hxN
  rw [tail_num_rpow x ε hx0, tail_num_alg x Q K (Real.log Q) (x ^ (ε / 4))
    (Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2))) hx0 hQ]
  set y := x ^ (ε / 4) with hydef
  set l := Real.log Q with hldef
  have hs0 : 0 < x ^ (ε / 6) := Real.rpow_pos_of_pos hx0 _
  have hl0 : 0 ≤ l := by linarith
  have hy0 : 0 ≤ y := by linarith
  have ht1 : K * l ^ 2 * y ≤ K * y ^ 3 := by
    have : l ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hl0 hhi 2
    have h' : l ^ 2 * y ≤ y ^ 2 * y := mul_le_mul_of_nonneg_right this hy0
    calc K * l ^ 2 * y = K * (l ^ 2 * y) := by ring
      _ ≤ K * (y ^ 2 * y) := mul_le_mul_of_nonneg_left h' hK
      _ = K * y ^ 3 := by ring
  have hyx : y ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : ε / 4 ≤ 1)
    rwa [Real.rpow_one] at this
  have hlx : l ≤ x := le_trans hhi hyx
  have hQinv : 1 / Q ≤ Real.exp (-(x ^ (ε / 6))) := by
    have hQe : Real.exp (x ^ (ε / 6)) ≤ Q := by
      calc Real.exp (x ^ (ε / 6)) ≤ Real.exp l := Real.exp_le_exp.2 hlo
        _ = Q := Real.exp_log hQ
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hQe
  have ht2 : K * (l * x ^ 403 / Q) ≤ 1 / 3 := by
    have hin : l * x ^ 403 / Q ≤ x ^ 404 * Real.exp (-(x ^ (ε / 6))) := by
      calc l * x ^ 403 / Q = (l * x ^ 403) * (1 / Q) := by ring
        _ ≤ (x * x ^ 403) * Real.exp (-(x ^ (ε / 6))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hlx (by positivity)) hQinv
            (by positivity) (by positivity)
        _ = x ^ 404 * Real.exp (-(x ^ (ε / 6))) := by ring
    exact le_trans (mul_le_mul_of_nonneg_left hin hK) hexp
  have ht3 := tail_num_third x hx3
  have hpow : x ^ ε = y * y * y * y := by
    rw [hydef, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  have hy1 : 803 ≤ y := by linarith
  have hy3 : y ≤ y ^ 3 := by nlinarith
  have hfin : K * y ^ 3 + 1 / 3 + 802 ≤ y * y * y * y := by
    have : (K + 803) * y ^ 3 ≤ y * y ^ 3 :=
      mul_le_mul_of_nonneg_right hy (by positivity)
    nlinarith
  rw [hpow]
  linarith

end Formalism.HermitianLattices.Ext.BoxTail
end
end

