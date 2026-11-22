import Formalism.Bundle0001

-- bundled from Formalism.ZetaNonvanishing.MellinSAux
section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def mxS (n : ℕ) (x : ℝ) : ℝ := max (x / n - 1) 0

lemma mxS_nonneg (n : ℕ) (x : ℝ) : 0 ≤ mxS n x := by
  show 0 ≤ max (x / n - 1) 0
  exact le_max_right _ _

lemma mxS_eq_indicator {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    mxS n x = (Ioi (n : ℝ)).indicator (fun x => x / n - 1) x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  show max (x / n - 1) 0 = _
  by_cases hx : x ∈ Ioi (n : ℝ)
  · rw [Set.indicator_of_mem hx]
    have h1 : 1 ≤ x / n := by
      rw [le_div_iff₀ hn0]
      have := Set.mem_Ioi.mp hx
      linarith
    exact max_eq_left (sub_nonneg.mpr h1)
  · rw [Set.indicator_of_notMem hx]
    have h1 : x / n ≤ 1 := (div_le_one hn0).mpr (le_of_not_gt (fun h => hx (Set.mem_Ioi.mpr h)))
    exact max_eq_right (sub_nonpos.mpr h1)

lemma mxS_mellin {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1) = (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsub : Ioi (n : ℝ) ⊆ Ioi 1 := Ioi_subset_Ioi hn1
  have ha : (-s).re < -1 := by
    simp only [Complex.neg_re]
    linarith
  have hb : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h'
    linarith
  have hs2 : -s + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at h'
    linarith

  have hfun : (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) =
      (Ioi (n : ℝ)).indicator (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    rw [mxS_eq_indicator hn x]
    by_cases hx : x ∈ Ioi (n : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Complex.ofReal_zero, zero_mul]
  have heq : EqOn (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)) (Ioi (n : ℝ)) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans hn0 (Set.mem_Ioi.mp hx)).ne'
    have hpow : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * x := by
      calc (x : ℂ) ^ (-s) = (x : ℂ) ^ ((-s - 1) + 1) := by rw [sub_add_cancel]
        _ = (x : ℂ) ^ (-s - 1) * x := by rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
    show ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)
    rw [hpow]
    push_cast
    ring
  have hA : Integrable (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s)) (volume.restrict (Ioi (n : ℝ))) :=
    Integrable.const_mul (integrableOn_Ioi_cpow_of_lt ha hn0) (1 / (n : ℂ))
  have hB : Integrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (volume.restrict (Ioi (n : ℝ))) :=
    integrableOn_Ioi_cpow_of_lt hb hn0
  have hint : IntegrableOn (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1))
      (Ioi (n : ℝ)) := hA.sub hB
  have hg := hint.congr_fun heq.symm measurableSet_Ioi
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul,
    integral_Ioi_cpow_of_lt ha hn0, integral_Ioi_cpow_of_lt hb hn0, sub_add_cancel,
    Complex.ofReal_natCast, Complex.cpow_add _ _ hnC, Complex.cpow_one]
  field_simp
  ring

lemma mxS_mellin_real {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => mxS n x * x ^ (-σ - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), mxS n x * x ^ (-σ - 1) = (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsub : Ioi (n : ℝ) ⊆ Ioi 1 := Ioi_subset_Ioi hn1
  have ha : -σ < -1 := by linarith
  have hb : -σ - 1 < -1 := by linarith
  have hσ0 : σ ≠ 0 := (by linarith : (0 : ℝ) < σ).ne'
  have hσ1 : σ - 1 ≠ 0 := (by linarith : (0 : ℝ) < σ - 1).ne'
  have hσ2 : -σ + 1 ≠ 0 := (by linarith : -σ + 1 < 0).ne
  have hnR : (n : ℝ) ≠ 0 := hn0.ne'

  have hfun : (fun x : ℝ => mxS n x * x ^ (-σ - 1)) =
      (Ioi (n : ℝ)).indicator (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1)) := by
    funext x
    rw [mxS_eq_indicator hn x]
    by_cases hx : x ∈ Ioi (n : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have heq : EqOn (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1))
      (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)) (Ioi (n : ℝ)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hn0 (Set.mem_Ioi.mp hx)
    have hpow : x ^ (-σ) = x ^ (-σ - 1) * x := by
      calc x ^ (-σ) = x ^ ((-σ - 1) + 1) := by rw [sub_add_cancel]
        _ = x ^ (-σ - 1) * x := by rw [Real.rpow_add hx0, Real.rpow_one]
    show (x / n - 1) * x ^ (-σ - 1) = 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)
    rw [hpow]
    ring
  have hA : Integrable (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ)) (volume.restrict (Ioi (n : ℝ))) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt ha hn0) (1 / (n : ℝ))
  have hB : Integrable (fun x : ℝ => x ^ (-σ - 1)) (volume.restrict (Ioi (n : ℝ))) :=
    integrableOn_Ioi_rpow_of_lt hb hn0
  have hint : IntegrableOn (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1))
      (Ioi (n : ℝ)) := hA.sub hB
  have hg := hint.congr_fun heq.symm measurableSet_Ioi
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul,
    integral_Ioi_rpow_of_lt ha hn0, integral_Ioi_rpow_of_lt hb hn0, sub_add_cancel,
    Real.rpow_add hn0, Real.rpow_one]
  field_simp
  ring

lemma integrable_tsum_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : ℕ → α → ℝ} (hφ : ∀ n, Integrable (φ n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ φ n x)
    (hsx : ∀ x, Summable (fun n => φ n x)) (hs : Summable fun n => ∫ x, φ n x ∂μ) :
    Integrable (fun x => ∑' n, φ n x) μ := by
  have hall : ∀ᵐ x ∂μ, ∀ n, 0 ≤ φ n x := ae_all_iff.mpr h0
  have hm : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (φ n x)) μ :=
    fun n => (hφ n).aemeasurable.ennreal_ofReal
  have hmeas : AEMeasurable (fun x => ∑' n, ENNReal.ofReal (φ n x)) μ :=
    AEMeasurable.ennreal_tsum hm
  have hlin : ∫⁻ x, ∑' n, ENNReal.ofReal (φ n x) ∂μ = ENNReal.ofReal (∑' n, ∫ x, φ n x ∂μ) := by
    rw [lintegral_tsum hm,
      ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg_of_ae (h0 n)) hs]
    exact tsum_congr fun n => (ofReal_integral_eq_lintegral_ofReal (hφ n) (h0 n)).symm
  have hint := integrable_toReal_of_lintegral_ne_top hmeas (by rw [hlin]; exact ENNReal.ofReal_ne_top)
  refine hint.congr ?_
  filter_upwards [hall] with x hx
  rw [← ENNReal.ofReal_tsum_of_nonneg hx (hsx x), ENNReal.toReal_ofReal (tsum_nonneg hx)]

end Formalism
end
end

-- bundled from Formalism.ZetaNonvanishing.RHofHalfPlane
section
open Complex

noncomputable section

namespace Formalism

lemma zeta_neg_odd_ne_zero (m : ℕ) : riemannZeta (-((2 * m + 1 : ℕ) : ℂ)) ≠ 0 := by
  set t : ℂ := ((2 * m + 2 : ℕ) : ℂ) with ht
  have htre : t.re = 2 * (m : ℝ) + 2 := by simp [ht]
  have ht1 : (1 : ℝ) < t.re := by rw [htre]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hn : ∀ n : ℕ, t ≠ -n := by
    intro n hn
    have := congrArg Complex.re hn
    rw [htre] at this
    simp at this
    have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have ht1' : t ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [htre] at this
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hfe := riemannZeta_one_sub hn ht1'
  have hsub : (1 : ℂ) - t = -((2 * m + 1 : ℕ) : ℂ) := by
    rw [ht]; push_cast; ring
  rw [hsub] at hfe
  rw [hfe]
  have hcos : Complex.cos (Real.pi * t / 2) = ((Real.cos (((m + 1 : ℕ) : ℝ) * Real.pi) : ℝ) : ℂ) := by
    rw [ht]; push_cast; ring_nf
  have hpi : (2 * ((Real.pi : ℝ) : ℂ)) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_)
    (riemannZeta_ne_zero_of_one_lt_re ht1)
  · exact (cpow_ne_zero_iff).mpr (Or.inl hpi)
  · exact Complex.Gamma_ne_zero hn
  · rw [hcos, Real.cos_nat_mul_pi]
    push_cast
    exact pow_ne_zero _ (by norm_num)

theorem riemannHypothesis_of_zero_free_halfPlane : RHofHalfPlane := by
  intro h s hs htriv hs1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · by_cases hn : ∃ n : ℕ, s = -n
    · obtain ⟨n, rfl⟩ := hn
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
      · rcases k with _ | m
        · simp [riemannZeta_zero] at hs
        · exact htriv ⟨m, by push_cast; ring⟩
      · exact zeta_neg_odd_ne_zero k hs
    · simp only [not_exists] at hn
      have hfe := riemannZeta_one_sub hn hs1
      rw [hs, mul_zero] at hfe
      exact h (1 - s) (by simp; linarith) hfe
  · exact h s hgt hs

end Formalism
end
end

