import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HkRowIntegral

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HeckeKernelCellContinuous
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace Hk2

lemma rpow_bd {κ x t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hx : κ ≤ x) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    x ^ (-t) ≤ (κ ^ 2)⁻¹ := by
  calc x ^ (-t) ≤ κ ^ (-t) := Real.rpow_le_rpow_of_nonpos hκ hx (by linarith)
    _ ≤ κ ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hκ hκ1 (by linarith)
    _ = (κ ^ 2)⁻¹ := by rw [Real.rpow_neg hκ.le, Real.rpow_two]

lemma rpow_diff {κ ρ a b t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hρ : κ ≤ ρ) (ha : ρ ≤ a) (hb : ρ ≤ b)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |a ^ (-t) - b ^ (-t)| ≤ 2 * (κ ^ 2)⁻¹ * ρ⁻¹ * |a - b| := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hκ hρ
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun x : ℝ => x ^ (-t)) (f' := fun x : ℝ => (-t) * x ^ (-t - 1)) (s := Set.Ici ρ)
    (C := 2 * (κ ^ 2)⁻¹ * ρ⁻¹) (x := b) (y := a)
    (fun x hx => (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_lt_of_le hρ0 hx)))).hasDerivWithinAt)
    (fun x hx => by
      have hx' : ρ ≤ x := hx
      have hx0 : 0 < x := lt_of_lt_of_le hρ0 hx'
      rw [Real.rpow_sub hx0, Real.rpow_one, norm_mul, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_neg, abs_of_nonneg ht0, abs_of_pos hx0,
        abs_of_nonneg (Real.rpow_nonneg hx0.le _), div_eq_mul_inv, ← mul_assoc]
      have h1 := rpow_bd hκ hκ1 (hρ.trans hx') ht0 ht2
      have h2 : x⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ0 hx'
      have h3 : 0 ≤ x ^ (-t) := Real.rpow_nonneg hx0.le _
      gcongr)
    (convex_Ici ρ) hb ha
  simpa [Real.norm_eq_abs] using key

lemma inv_sq_diff {ρ : ℝ} {w w' : ℂ} (hρ : 0 < ρ) (hw : ρ ≤ ‖w‖) (hw' : ρ ≤ ‖w'‖) :
    ‖(w ^ 2)⁻¹ - (w' ^ 2)⁻¹‖ ≤ 2 * (ρ ^ 3)⁻¹ * ‖w - w'‖ := by
  have h0 : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hρ hw)
  have h0' : w' ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hρ hw')
  have e : (w ^ 2)⁻¹ - (w' ^ 2)⁻¹ = (w' - w) * (w⁻¹ * (w' ^ 2)⁻¹ + (w ^ 2)⁻¹ * w'⁻¹) := by
    field_simp
    ring
  have i1 : ‖w‖⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ hw
  have i2 : ‖w'‖⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ hw'
  have p1 : 0 ≤ ‖w‖⁻¹ := by positivity
  have p2 : 0 ≤ ‖w'‖⁻¹ := by positivity
  have b1 : ‖w⁻¹ * (w' ^ 2)⁻¹‖ ≤ (ρ ^ 3)⁻¹ := by
    rw [norm_mul, norm_inv, norm_inv, norm_pow, ← inv_pow, ← inv_pow]
    calc ‖w‖⁻¹ * ‖w'‖⁻¹ ^ 2 ≤ ρ⁻¹ * ρ⁻¹ ^ 2 := by gcongr
      _ = ρ⁻¹ ^ 3 := by ring
  have b2 : ‖(w ^ 2)⁻¹ * w'⁻¹‖ ≤ (ρ ^ 3)⁻¹ := by
    rw [norm_mul, norm_inv, norm_inv, norm_pow, ← inv_pow, ← inv_pow]
    calc ‖w‖⁻¹ ^ 2 * ‖w'‖⁻¹ ≤ ρ⁻¹ ^ 2 * ρ⁻¹ := by gcongr
      _ = ρ⁻¹ ^ 3 := by ring
  rw [e, norm_mul, norm_sub_rev w' w, mul_comm]
  gcongr
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (ρ ^ 3)⁻¹ + (ρ ^ 3)⁻¹ := add_le_add b1 b2
    _ = 2 * (ρ ^ 3)⁻¹ := by ring

lemma hk_diff {κ ρ s : ℝ} {w w' : ℂ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hρ : κ ≤ ρ) (hw : ρ ≤ ‖w‖)
    (hw' : ρ ≤ ‖w'‖) (hd : ‖w - w'‖ ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖hk s w - hk s w'‖ ≤ 4 * (κ ^ 2)⁻¹ * (ρ ^ 3)⁻¹ := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hκ hρ
  have e : hk s w - hk s w' = ((w ^ 2)⁻¹ - (w' ^ 2)⁻¹) * ((‖w‖ ^ (-(2 * s)) : ℝ) : ℂ)
      + (w' ^ 2)⁻¹ * ((‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s)) : ℝ) : ℂ) := by
    unfold hk
    push_cast
    ring
  have a1 : ‖(w ^ 2)⁻¹ - (w' ^ 2)⁻¹‖ ≤ 2 * (ρ ^ 3)⁻¹ := by
    refine (inv_sq_diff hρ0 hw hw').trans ?_
    have : 0 ≤ 2 * (ρ ^ 3)⁻¹ := by positivity
    nlinarith
  have a2 : ‖((‖w‖ ^ (-(2 * s)) : ℝ) : ℂ)‖ ≤ (κ ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact rpow_bd hκ hκ1 (hρ.trans hw) (by linarith) (by linarith)
  have a3 : ‖(w' ^ 2)⁻¹‖ ≤ (ρ ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    exact inv_anti₀ (by positivity) (by gcongr)
  have a4 : ‖((‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s)) : ℝ) : ℂ)‖ ≤ 2 * (κ ^ 2)⁻¹ * ρ⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (rpow_diff hκ hκ1 hρ hw hw' (by linarith) (by linarith)).trans ?_
    have h1 : |‖w‖ - ‖w'‖| ≤ 1 := (abs_norm_sub_norm_le w w').trans hd
    have : 0 ≤ 2 * (κ ^ 2)⁻¹ * ρ⁻¹ := by positivity
    nlinarith
  rw [e]
  calc _ ≤ ‖((w ^ 2)⁻¹ - (w' ^ 2)⁻¹) * ((‖w‖ ^ (-(2 * s)) : ℝ) : ℂ)‖
        + ‖(w' ^ 2)⁻¹ * ((‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s)) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 * (ρ ^ 3)⁻¹ * (κ ^ 2)⁻¹ + (ρ ^ 2)⁻¹ * (2 * (κ ^ 2)⁻¹ * ρ⁻¹) := by
        rw [norm_mul, norm_mul]
        gcongr
    _ = 4 * (κ ^ 2)⁻¹ * (ρ ^ 3)⁻¹ := by
        field_simp
        ring

def kap (τ : ℂ) : ℝ := |τ.im| / (|τ.im| + 2 + |τ.re|)

lemma kap_pos {τ : ℂ} (hτ : τ.im ≠ 0) : 0 < kap τ := by
  have : 0 < |τ.im| := abs_pos.mpr hτ
  unfold kap
  positivity

lemma kap_le_one (τ : ℂ) : kap τ ≤ 1 := by
  unfold kap
  have h1 : 0 ≤ |τ.im| := abs_nonneg _
  have h2 : 0 ≤ |τ.re| := abs_nonneg _
  rw [div_le_one (by linarith)]
  linarith

lemma lower {τ : ℂ} (m n : ℤ) (hn : n ≠ 0) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    kap τ * (|(m : ℝ)| + |(n : ℝ)|) ≤ ‖(m : ℂ) + (x : ℂ) + (n : ℂ) * τ‖ := by
  set W := ‖(m : ℂ) + (x : ℂ) + (n : ℂ) * τ‖ with hW
  have hY : 0 ≤ |τ.im| := abs_nonneg _
  have hA : 0 ≤ |τ.re| := abs_nonneg _
  have hN : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  have h1 : |(n : ℝ)| * |τ.im| ≤ W := by
    have := Complex.abs_im_le_norm ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)
    simpa [abs_mul] using this
  have h2 : |(m : ℝ)| ≤ W + |(n : ℝ)| + |(n : ℝ)| * |τ.re| := by
    have h := Complex.abs_re_le_norm ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)
    have e : ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ).re = (m : ℝ) + x + (n : ℝ) * τ.re := by simp
    rw [e] at h
    have e2 : (m : ℝ) = ((m : ℝ) + x + (n : ℝ) * τ.re) - x - (n : ℝ) * τ.re := by ring
    calc |(m : ℝ)| = |((m : ℝ) + x + (n : ℝ) * τ.re) - x - (n : ℝ) * τ.re| := by rw [← e2]
      _ ≤ |((m : ℝ) + x + (n : ℝ) * τ.re) - x| + |(n : ℝ) * τ.re| := abs_sub _ _
      _ ≤ |(m : ℝ) + x + (n : ℝ) * τ.re| + |x| + |(n : ℝ) * τ.re| := by
          gcongr
          exact abs_sub _ _
      _ ≤ W + |(n : ℝ)| + |(n : ℝ)| * |τ.re| := by
          rw [abs_mul, abs_of_nonneg hx0]
          gcongr
          linarith
  unfold kap
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  have k1 := mul_le_mul_of_nonneg_left h2 hY
  have k2 := mul_le_mul_of_nonneg_right h1 hA
  nlinarith

lemma summ : Summable (fun p : ℤ × ℤ => ((|(p.1 : ℝ)| + |(p.2 : ℝ)|) ^ 3)⁻¹) := by
  have h := EisensteinSeries.summable_one_div_norm_rpow (k := 3) (by norm_num)
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at h
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) h
  simp only [Function.comp, finTwoArrowEquiv_symm_apply]
  have hN : ‖![p.1, p.2]‖ = max |(p.1 : ℝ)| |(p.2 : ℝ)| := by
    rw [EisensteinSeries.norm_eq_max_natAbs]
    simp [Nat.cast_natAbs]
  rw [hN]
  have q1 : 0 ≤ |(p.1 : ℝ)| := abs_nonneg _
  have q2 : 0 ≤ |(p.2 : ℝ)| := abs_nonneg _
  rcases eq_or_lt_of_le (le_max_of_le_left q1 : 0 ≤ max |(p.1 : ℝ)| |(p.2 : ℝ)|) with h0 | h0
  · have z1 : |(p.1 : ℝ)| = 0 := le_antisymm (h0 ▸ le_max_left _ _) q1
    have z2 : |(p.2 : ℝ)| = 0 := le_antisymm (h0 ▸ le_max_right _ _) q2
    rw [z1, z2]
    simp
  · rw [Real.rpow_neg h0.le]
    have : (max |(p.1 : ℝ)| |(p.2 : ℝ)|) ^ (3 : ℝ) = (max |(p.1 : ℝ)| |(p.2 : ℝ)|) ^ 3 := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [this]
    apply inv_anti₀ (by positivity)
    gcongr
    exact max_le (by linarith) (by linarith)

lemma pt_ne_zero {τ : ℂ} (hτ : τ.im ≠ 0) {n : ℤ} (hn : n ≠ 0) (m : ℤ) (x : ℝ) :
    (m : ℂ) + (x : ℂ) + (n : ℂ) * τ ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  rcases this with h | h
  · exact hn h
  · exact hτ h

lemma hk_cont {τ : ℂ} (hτ : τ.im ≠ 0) {n : ℤ} (hn : n ≠ 0) (m : ℤ) :
    Continuous (Function.uncurry fun (s x : ℝ) => hk s ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)) := by
  unfold hk Function.uncurry
  have c : Continuous fun q : ℝ × ℝ => (m : ℂ) + ((q.2 : ℝ) : ℂ) + (n : ℂ) * τ := by fun_prop
  refine Continuous.mul ?_ ?_
  · exact (c.pow 2).inv₀ (fun q => pow_ne_zero 2 (pt_ne_zero hτ hn m q.2))
  · refine Complex.continuous_ofReal.comp ?_
    refine Continuous.rpow c.norm (by fun_prop) (fun q => Or.inl ?_)
    exact norm_ne_zero_iff.mpr (pt_ne_zero hτ hn m q.2)

lemma cell_cont {τ : ℂ} (hτ : τ.im ≠ 0) {p : ℤ × ℤ} (hp : p.2 ≠ 0) :
    Continuous fun s : ℝ => hkCell τ s p := by
  unfold hkCell
  refine Continuous.sub ?_ ?_
  · have h := (hk_cont hτ hp p.1).comp (Continuous.prodMk continuous_id (continuous_const (y := (0 : ℝ))))
    simpa [Function.uncurry, Function.comp_def] using h
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hk_cont hτ hp p.1) 0 1

lemma cell_bound {τ : ℂ} (hτ : τ.im ≠ 0) {p : ℤ × ℤ} (hp : p.2 ≠ 0) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    ‖hkCell τ s p‖ ≤ 4 * (kap τ ^ 2)⁻¹ * ((kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)) ^ 3)⁻¹ := by
  have hκ := kap_pos hτ
  have hκ1 := kap_le_one τ
  have hN : (1 : ℝ) ≤ |(p.2 : ℝ)| := by
    have : (1 : ℤ) ≤ |p.2| := Int.one_le_abs hp
    exact_mod_cast this
  have hρ : kap τ ≤ kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|) := by
    have : 0 ≤ |(p.1 : ℝ)| := abs_nonneg _
    nlinarith
  have cx : Continuous fun x : ℝ => hk s ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ) := by
    have h := (hk_cont hτ hp p.1).comp (Continuous.prodMk (continuous_const (y := s)) continuous_id)
    simpa [Function.uncurry, Function.comp_def] using h
  have e : hkCell τ s p = ∫ x in (0 : ℝ)..1, (hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ)
      - hk s ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ)) := by
    rw [intervalIntegral.integral_sub (by simp) (cx.intervalIntegrable 0 1)]
    simp [hkCell]
  rw [e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := 4 * (kap τ ^ 2)⁻¹ * ((kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)) ^ 3)⁻¹)
    (f := fun x : ℝ => hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ) - hk s ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ))
    (fun x hx => by
      rw [Set.uIoc_of_le zero_le_one] at hx
      have l0 := lower (τ := τ) p.1 p.2 hp (le_refl (0 : ℝ)) zero_le_one
      have lx := lower (τ := τ) p.1 p.2 hp hx.1.le hx.2
      simp only [Complex.ofReal_zero, add_zero] at l0
      refine hk_diff hκ hκ1 hρ l0 lx ?_ hs0 hs1
      have : (p.1 : ℂ) + (p.2 : ℂ) * τ - ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ) = -(x : ℂ) := by ring
      rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
      exact hx.2)
  simpa using this

end Hk2

theorem hecke_kernel_cell_bound : HkCellBound := by
  intro τ hτ
  refine ⟨fun p => 4 * (Hk2.kap τ ^ 2)⁻¹ * ((Hk2.kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)) ^ 3)⁻¹, ?_,
    fun s p hs0 hs1 hp => Hk2.cell_bound hτ hp hs0 hs1⟩
  have h := Hk2.summ.mul_left (4 * (Hk2.kap τ ^ 2)⁻¹ * (Hk2.kap τ ^ 3)⁻¹)
  refine h.congr (fun p => ?_)
  rw [mul_pow, mul_inv]
  ring

theorem hecke_kernel_cell_continuous : HkCellCont := by
  intro τ p hτ hp
  exact ((Hk2.cell_cont hτ hp).tendsto 0).mono_left nhdsWithin_le_nhds

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HeckeKernelLineZero
section
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory

namespace Formalism.L2.Th1.F

namespace Hk3

lemma one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

lemma integrable_J {a : ℝ} (ha : 1 / 2 < a) : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-a)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * a)
    (by simp; linarith)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

lemma bound_f {a : ℝ} (t : ℝ) : ‖t * (1 + t ^ 2) ^ (-a)‖ ≤ (1 + t ^ 2) ^ (-(a - 1 / 2)) := by
  have hp := one_add_sq_pos t
  have h1 : |t| ≤ (1 + t ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.abs_le_sqrt (by linarith)
  have h2 : (1 + t ^ 2) ^ (-(a - 1 / 2)) = (1 + t ^ 2) ^ ((1 : ℝ) / 2) * (1 + t ^ 2) ^ (-a) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le _), h2]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp.le _)

lemma tendsto_f {a : ℝ} (ha : 1 / 2 < a) {l : Filter ℝ}
    (hl : Tendsto (fun t : ℝ => 1 + t ^ 2) l atTop) :
    Tendsto (fun t : ℝ => t * (1 + t ^ 2) ^ (-a)) l (𝓝 0) := by
  refine squeeze_zero_norm (fun t => bound_f t) ?_
  exact (tendsto_rpow_neg_atTop (y := a - 1 / 2) (by linarith)).comp hl

lemma tendsto_top : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
  tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by norm_num))

lemma tendsto_bot : Tendsto (fun t : ℝ => 1 + t ^ 2) atBot atTop := by
  have := tendsto_top.comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this

lemma hasDeriv_f (a t : ℝ) :
    HasDerivAt (fun t : ℝ => t * (1 + t ^ 2) ^ (-a))
      ((1 - 2 * a) * (1 + t ^ 2) ^ (-a) + 2 * a * (1 + t ^ 2) ^ (-(a + 1))) t := by
  have hp := one_add_sq_pos t
  have h0 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  have h1 := h0.rpow_const (p := -a) (Or.inl hp.ne')
  have h2 := (hasDerivAt_id t).mul h1
  refine h2.congr_deriv ?_
  have h3 : (1 + t ^ 2) ^ (-a) = (1 + t ^ 2) * (1 + t ^ 2) ^ (-(a + 1)) := by
    nth_rewrite 2 [← Real.rpow_one (1 + t ^ 2)]
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have h4 : -a - 1 = -(a + 1) := by ring
  simp only [id, h4]
  rw [h3]
  ring

lemma J_rec {a : ℝ} (ha : 1 / 2 < a) : hkJ (a + 1) = (2 * a - 1) / (2 * a) * hkJ a := by
  have hi1 := integrable_J ha
  have hi2 := integrable_J (a := a + 1) (by linarith)
  have h := integral_of_hasDerivAt_of_tendsto (hasDeriv_f a)
    ((hi1.const_mul (1 - 2 * a)).add (hi2.const_mul (2 * a)))
    (tendsto_f ha tendsto_bot) (tendsto_f ha tendsto_top)
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul] at h
  have ha0 : (2 * a) ≠ 0 := by linarith
  unfold hkJ
  field_simp
  linarith

lemma J_one : hkJ 1 = Real.pi := by
  unfold hkJ
  rw [← integral_univ_inv_one_add_sq]
  congr 1
  ext t
  rw [Real.rpow_neg_one]

lemma J_tendsto : Tendsto (fun s : ℝ => hkJ (1 + s)) (𝓝[>] 0) (𝓝 Real.pi) := by
  rw [← J_one]
  unfold hkJ
  refine tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => (1 + t ^ 2)⁻¹) ?_ ?_
    integrable_inv_one_add_sq ?_
  · exact Eventually.of_forall fun s => Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine Eventually.of_forall fun t => ?_
    have hp := one_add_sq_pos t
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le _), ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg t]) (by
      have : (0 : ℝ) < s := hs
      linarith)
  · refine Eventually.of_forall fun t => ?_
    have hp := one_add_sq_pos t
    have hc : Continuous (fun s : ℝ => (1 + t ^ 2) ^ (-(1 + s))) :=
      Continuous.rpow continuous_const (by fun_prop) (fun _ => Or.inl hp.ne')
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this

end Hk3

theorem hecke_kernel_j_rules : HkJRules := ⟨fun _ ha => Hk3.J_rec ha, Hk3.J_one, Hk3.J_tendsto⟩

namespace Hk3

lemma hk_tendsto (w : ℂ) : Tendsto (fun s : ℝ => hk s w) (𝓝[>] 0) (𝓝 (1 / w ^ 2)) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [hk]
  · have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hc : Continuous (fun s : ℝ => hk s w) := by
      unfold hk
      refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
      exact Continuous.rpow continuous_const (by fun_prop) (fun _ => Or.inl hp.ne')
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [hk] using this

lemma hk_int_bound {s : ℝ} (hs : 0 ≤ s) (m : ℤ) : ‖hk s (m : ℂ)‖ ≤ |(m : ℝ)| ^ (-(2 : ℝ)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hk]
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have h3 : |(m : ℝ)| ^ (-(2 : ℝ)) = (|(m : ℝ)| ^ 2)⁻¹ := by
      rw [Real.rpow_neg h0, Real.rpow_two]
    unfold hk
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg h0 _), h3]
    have h2 : |(m : ℝ)| ^ (-(2 * s)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    exact mul_le_of_le_one_right (by positivity) h2

end Hk3

theorem hecke_kernel_line_zero : HkRowZero := by
  refine tendsto_tsum_of_dominated_convergence (bound := fun m : ℤ => |(m : ℝ)| ^ (-(2 : ℝ)))
    (Real.summable_abs_int_rpow (by norm_num)) (fun m => Hk3.hk_tendsto (m : ℂ)) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact fun m => Hk3.hk_int_bound (le_of_lt hs) m

namespace Hk3

lemma tsum_abs_int {b : ℝ} (hb : 1 < b) :
    ∑' n : ℤ, |(n : ℝ)| ^ (-b) = 2 * ∑' n : ℕ, 1 / (n : ℝ) ^ b := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ b) := Real.summable_one_div_nat_rpow.mpr hb
  have e1 : (fun n : ℕ => |((n : ℤ) : ℝ)| ^ (-b)) = fun n : ℕ => 1 / (n : ℝ) ^ b := by
    ext n
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n), Real.rpow_neg (Nat.cast_nonneg n),
      one_div]
  have e2 : (fun n : ℕ => |((-(n : ℤ) : ℤ) : ℝ)| ^ (-b)) = fun n : ℕ => 1 / (n : ℝ) ^ b := by
    ext n
    rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n),
      Real.rpow_neg (Nat.cast_nonneg n), one_div]
  rw [Summable.tsum_of_nat_of_neg (f := fun n : ℤ => |(n : ℝ)| ^ (-b)) (by rw [e1]; exact hs)
    (by rw [e2]; exact hs), e1, e2, Int.cast_zero, abs_zero, Real.zero_rpow (by linarith)]
  ring

lemma term_eq (hv : HkIntValue) {τ : ℂ} (hτ : τ.im ≠ 0) {s : ℝ} (hs : 0 < s) (n : ℤ) :
    (if n = 0 then 0 else hkInt τ s n) =
      ((|(n : ℝ)| ^ (-(1 + 2 * s)) *
        (|τ.im| ^ (-(1 + 2 * s)) * (hkJ (1 + s) - 2 * hkJ (2 + s))) : ℝ) : ℂ) := by
  split_ifs with h
  · subst h
    rw [Int.cast_zero, abs_zero, Real.zero_rpow (by linarith)]
    simp
  · rw [hv τ s n hτ hs h, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_assoc]

lemma K_eq (hj : HkJRules) {s : ℝ} (hs : 0 < s) :
    hkJ (1 + s) - 2 * hkJ (2 + s) = -(s / (s + 1)) * hkJ (1 + s) := by
  have h := hj.1 (1 + s) (by linarith)
  have e : 1 + s + 1 = 2 + s := by ring
  rw [e] at h
  rw [h]
  have h1 : s + 1 ≠ 0 := by linarith
  have h2 : 1 + s ≠ 0 := by linarith
  field_simp
  ring

lemma tsum_eq (hv : HkIntValue) (hj : HkJRules) {τ : ℂ} (hτ : τ.im ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∑' n : ℤ, if n = 0 then 0 else hkInt τ s n) =
      (((((1 + 2 * s) - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 2 * s)) *
        (|τ.im| ^ (-(1 + 2 * s)) * (-(1 / (s + 1)) * hkJ (1 + s))) : ℝ) : ℂ) := by
  simp_rw [term_eq hv hτ hs]
  rw [← Complex.ofReal_tsum, tsum_mul_right, tsum_abs_int (by linarith), K_eq hj hs]
  congr 1
  ring

lemma real_limit (hj : HkJRules) {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun s : ℝ => (((1 + 2 * s) - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 2 * s)) *
        (|y| ^ (-(1 + 2 * s)) * (-(1 / (s + 1)) * hkJ (1 + s)))) (𝓝[>] 0)
      (𝓝 (-(Real.pi / |y|))) := by
  have hp : 0 < |y| := abs_pos.mpr hy
  have hm : Tendsto (fun s : ℝ => 1 + 2 * s) (𝓝[>] 0) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Continuous (fun s : ℝ => 1 + 2 * s) := by fun_prop
      simpa using (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs ⊢
      linarith
  have h2 := tendsto_sub_mul_tsum_nat_rpow.comp hm
  have h3 : Tendsto (fun s : ℝ => |y| ^ (-(1 + 2 * s))) (𝓝[>] 0) (𝓝 (|y|⁻¹)) := by
    have hc : Continuous (fun s : ℝ => |y| ^ (-(1 + 2 * s))) :=
      Continuous.rpow continuous_const (by fun_prop) (fun _ => Or.inl hp.ne')
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [Real.rpow_neg_one] using this
  have h4 : Tendsto (fun s : ℝ => -(1 / (s + 1))) (𝓝[>] 0) (𝓝 (-1)) := by
    have hc : ContinuousAt (fun s : ℝ => -(1 / (s + 1))) 0 :=
      (ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)).neg
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have h := h2.mul (h3.mul (h4.mul hj.2.2))
  have e : (1 : ℝ) * (|y|⁻¹ * (-1 * Real.pi)) = -(Real.pi / |y|) := by
    rw [div_eq_mul_inv]
    ring
  rw [e] at h
  exact h

end Hk3

theorem hkIntLimit_of (hv : HkIntValue) (hj : HkJRules) : HkIntLimit := by
  intro τ hτ
  refine ⟨fun s hs => ?_, ?_⟩
  · simp_rw [Hk3.term_eq hv hτ hs]
    exact Complex.summable_ofReal.mpr
      ((Real.summable_abs_int_rpow (b := 1 + 2 * s) (by linarith)).mul_right _)
  · have h := (Complex.continuous_ofReal.tendsto _).comp (Hk3.real_limit hj hτ)
    rw [Complex.ofReal_neg] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Hk3.tsum_eq hv hj hτ hs).symm

end Formalism.L2.Th1.F
end
end

