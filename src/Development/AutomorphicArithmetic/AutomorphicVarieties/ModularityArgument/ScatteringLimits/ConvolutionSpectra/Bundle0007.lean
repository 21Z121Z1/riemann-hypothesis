import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvNear
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0003

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResBelow
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem side {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Sc H V W)
    (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (k : Ker β) (hB : ∀ u, B (M.J u) = M.J (conv β u)) (f : ℕ → H)
    (q0 : Tendsto (fun n => ∫ t in Iic (0 : ℝ), Real.exp t * ‖M.F.U t (f n) - f n‖ ^ 2) atTop (𝓝 0))
    (p : Tendsto (fun n => M.P (Ioi M.T₀) (f n)) atTop (𝓝 0)) :
    Tendsto (fun n => B (f n) - M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) atTop (𝓝 0) ∧
      Tendsto (fun n => M.P (Ioi M.T₀) (B (f n))) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := convNear β k
  have a : Tendsto (fun n => B (f n) - M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) atTop (𝓝 0) := by
    have := (q0.const_mul C).sqrt
    rw [mul_zero, Real.sqrt_zero] at this
    refine squeeze_zero_norm (fun n => Real.le_sqrt_of_sq_le ?_) this
    obtain ⟨u, hu⟩ := M.J.surjective (f n)
    simp only [← hu, hB, M.J.symm_apply_apply, M.hJ, ← map_sub, M.J.norm_map]
    exact hC u
  refine ⟨a, ?_⟩
  let G : H →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L (symb β 0).compLpL 2 volume ∘L
    (M.J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
  have := (((M.P (Ioi M.T₀)).continuous.tendsto 0).comp a).add ((G.continuous.tendsto 0).comp p)
  simp only [map_zero, add_zero] at this
  refine this.congr fun n => ?_
  have e : G (M.P (Ioi M.T₀) (f n)) = M.P (Ioi M.T₀) (M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) := by
    show M.J ((symb β 0).compLpL 2 volume (M.J.symm (M.J (cut V _ _)))) = M.J (cut V _ (M.J.symm (M.J _)))
    rw [M.J.symm_apply_apply, M.J.symm_apply_apply]
    refine congrArg M.J (Lp.ext ?_)
    filter_upwards [(symb β 0).coeFn_compLpL (cut V (Ioi M.T₀) (M.J.symm (f n))), (symb β 0).coeFn_compLpL (M.J.symm (f n)),
      cutSpec (Ioi M.T₀) measurableSet_Ioi (M.J.symm (f n)),
      cutSpec (Ioi M.T₀) measurableSet_Ioi ((symb β 0).compLpL 2 volume (M.J.symm (f n)))] with x h1 h2 h3 h4
    erw [h1, h3, h4]
    by_cases hx : x ∈ Ioi M.T₀
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, map_zero]
  simp only [Function.comp_apply, map_sub, e, sub_add_cancel]

theorem UpperTheory.V.Z.IntegralApplyAeEq.resBelow :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → IsUnit (symb β 0) → IsUnit (symb β' 0) → M.Acts B β β' → IsCompactOperator (M.abelian₂ M.T₀ M.T₀ ∘L B ∘L M.abelian₂ M.T₀ M.T₀) →
      ∀ f : ℕ → H, (∀ n, ‖f n‖ = 1) → Tendsto (fun n => M.abelian₂ M.T₀ M.T₀ (f n) - f n) atTop (𝓝 0) →
        Tendsto (fun n => (⟪f n, M.F.av wR (f n)⟫_ℂ).re) atTop (𝓝 1) → False := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc f hf t1 t2
  set Λ := M.abelian₂ M.T₀ M.T₀ with hΛ
  obtain ⟨-, -, -, -, -, -, l2, -, l4⟩ := (projLaws M).2.2.2.2.2.2.2 M.T₀ M.T₀ (by linarith)
  let q : H → ℝ := fun h => ∫ t in Iic (0 : ℝ), Real.exp t * ‖M.F.U t h - h‖ ^ 2
  have q0 : Tendsto (fun n => q (f n)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (2 : ℝ))).sub (t2.const_mul 2)
    simp only [mul_one, sub_self] at this
    exact this.congr fun n => by simp only [q, (resCob M.F _).2, hf]; ring
  have p1 : Tendsto (fun n => M.P (Ioi M.T₀) (f n)) atTop (𝓝 0) := by
    have := (((M.P (Ioi M.T₀)).continuous.tendsto 0).comp t1).neg
    simp only [map_zero, neg_zero] at this
    exact this.congr fun n => by
      have l : M.P (Ioi M.T₀) (Λ (f n)) = 0 := DFunLike.congr_fun l2 _
      simp [l]
  have p2 : Tendsto (fun n => M.P' (Ioi M.T₀) (f n)) atTop (𝓝 0) := by
    have := (((M.P' (Ioi M.T₀)).continuous.tendsto 0).comp t1).neg
    simp only [map_zero, neg_zero] at this
    exact this.congr fun n => by
      have l : M.P' (Ioi M.T₀) (Λ (f n)) = 0 := DFunLike.congr_fun l4 _
      simp [l]
  obtain ⟨a1, a2⟩ := side M B β k1 ha.1 f q0 p1
  obtain ⟨-, a3⟩ := side M.swap B β' k2 ha.2 f (q0.congr fun n => by
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    show _ = Real.exp t * ‖M.F.U (-t) (f n) - f n‖ ^ 2
    rw [← M.F.norm t (M.F.U (-t) (f n) - f n), map_sub, ← M.F.add, add_neg_cancel, M.F.zero, norm_sub_rev]) p2
  have a4 : Tendsto (fun n => B (f n) - (Λ ∘L B ∘L Λ) (f n)) atTop (𝓝 0) := by
    have := (a2.add a3).sub (((Λ ∘L B).continuous.tendsto 0).comp t1)
    simp only [map_zero, add_zero, sub_zero] at this
    refine this.congr fun n => ?_
    have e : Λ (B (f n)) = B (f n) - M.P (Ioi M.T₀) (B (f n)) - M.swap.P (Ioi M.swap.T₀) (B (f n)) := rfl
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_sub, e]
    abel
  obtain ⟨S, hS, hsub⟩ := hc.image_closedBall_subset_compact 1
  obtain ⟨y, -, φ, hφ, hy⟩ := hS.tendsto_subseq fun n => hsub ⟨f n, by simp [hf], rfl⟩
  obtain ⟨s, hs⟩ := u1
  let G : H →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L ((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).compLpL 2 volume ∘L
    (M.J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
  have hG : ∀ h, G (M.J ((symb β 0).compLpL 2 volume (M.J.symm h))) = h := fun h => by
    show M.J (((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).compLpL 2 volume (M.J.symm (M.J _))) = h
    rw [M.J.symm_apply_apply, ← M.J.eq_symm_apply]
    refine Lp.ext ?_
    filter_upwards [((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).coeFn_compLpL ((symb β 0).compLpL 2 volume (M.J.symm h)),
      (symb β 0).coeFn_compLpL (M.J.symm h)] with x h1 h2
    rw [h1, h2, ← hs]
    exact DFunLike.congr_fun s.inv_mul _
  have c1 : Tendsto (fun n => f (φ n)) atTop (𝓝 (G y)) := by
    have := (G.continuous.tendsto _).comp ((hy.add (a4.comp hφ.tendsto_atTop)).sub (a1.comp hφ.tendsto_atTop))
    simp only [add_zero, sub_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, ContinuousLinearMap.coe_coe, add_sub_cancel, sub_sub_cancel, hG]
  set g := G y
  have g1 : ‖g‖ = 1 := tendsto_nhds_unique c1.norm (by simp [hf])
  have qc : Continuous q := by
    simp only [q, (resCob M.F _).2]
    fun_prop
  have g2 : q g = 0 := tendsto_nhds_unique ((qc.tendsto g).comp c1) (q0.comp hφ.tendsto_atTop)
  have cg : Continuous fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2 := by
    have := M.F.cont g
    fun_prop
  have ig : IntegrableOn (fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2) (Iic 0) := by
    refine Integrable.mono' ((integrableOn_exp_Iic 0).mul_const 4) cg.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have : ‖M.F.U t g - g‖ ≤ 2 := (norm_sub_le _ _).trans_eq (by rw [M.F.norm, g1]; norm_num)
    gcongr
    nlinarith [norm_nonneg (M.F.U t g - g)]
  have g3 := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun t => by positivity) ig).1 g2
  have g4 : EqOn (fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2) 0 (Iio 0) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset Iio_subset_Iic_self g3) isOpen_Iio cg.continuousOn
      continuousOn_const
  have g5 : ∀ᶠ t in atBot, ⟪g, M.F.U t g⟫_ℂ = 1 := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    have := g4 ht
    simp only [Pi.zero_apply, mul_eq_zero, (Real.exp_pos t).ne', false_or, pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero] at this
    rw [this, inner_self_eq_norm_sq_to_K, g1]; simp
  exact one_ne_zero (tendsto_nhds_unique (tendsto_const_nhds.congr' (g5.mono fun _ h => h.symm)) ((projLaws M).1 g g).2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TailB
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem half {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (g : L V) (q a : ℝ) (hq : 0 < q) (h : WLe 2 g q) :
    ∫⁻ y in Ioi a, ‖g y‖ₑ ≤ ENNReal.ofReal (99 / 140 * Real.exp (-a) * q) := by
  set l := 5 / 7 * Real.exp (-a) / q with hl
  have l0 : 0 < l := by positivity
  have i1 : IntegrableOn (fun y => Real.exp (-2 * y)) (Ioi a) := integrableOn_exp_mul_Ioi (by norm_num) a
  have i2 : IntegrableOn (fun y => l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y)) (Ioi a) :=
    (h.1.integrableOn.const_mul _).add (i1.const_mul _)
  have pt : ∀ y, ‖g y‖ ≤ l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y) := fun y => by
    have e1 : Real.exp (-2 * y) = (Real.exp (2 * y))⁻¹ := by rw [← Real.exp_neg]; ring_nf
    have e0 := Real.exp_pos (2 * y)
    rw [e1]
    set E := Real.exp (2 * y)
    rw [← sub_nonneg]
    have : l / 2 * (E * ‖g y‖ ^ 2) + (2 * l)⁻¹ * E⁻¹ - ‖g y‖ = (l * E * ‖g y‖ - 1) ^ 2 / (2 * l * E) := by
      field_simp; ring
    rw [this]; positivity
  calc _ ≤ ∫⁻ y in Ioi a, ENNReal.ofReal (l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y)) :=
        lintegral_mono fun y => by rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (pt y)
    _ = ENNReal.ofReal (∫ y in Ioi a, l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y)) :=
        (ofReal_integral_eq_lintegral_ofReal i2 (Eventually.of_forall fun y => (norm_nonneg _).trans (pt y))).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_add (h.1.integrableOn.const_mul _) (i1.const_mul _), integral_const_mul, integral_const_mul,
          integral_exp_mul_Ioi (by norm_num)]
        have h1 : ∫ y in Ioi a, Real.exp (2 * y) * ‖g y‖ ^ 2 ≤ q ^ 2 :=
          (setIntegral_le_integral h.1 (Eventually.of_forall fun y => by positivity)).trans h.2
        refine (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) le_rfl).trans_eq ?_
        have e1 : Real.exp (-2 * a) = Real.exp (-a) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        have e0 := Real.exp_pos (-a)
        rw [e1, hl]
        field_simp; ring

theorem UpperTheory.V.Z.IntegralApplyAeEq.tailB :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (φ : ℝ → ℂ) (e : V) (p : L W) (Q α β : ℝ), Continuous φ → (∀ x, 1 / 2 < |x| → φ x = 0) → ∫ x, ‖φ x‖ ≤ 1 → 0 ≤ Q →
      WLe (-2) p Q → α ≤ β → ‖∫ s in α..β, M.cor φ e p s‖ ≤ 6 / 5 * ‖e‖ * Real.exp (2 * M.T₀) * Q * Real.exp (-α) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M φ e p Q α β φc φs φi hQ hp hαβ
  set g : L V := M.J.symm (M.J' p) with hg
  have hcut : ∀ a : ℝ, ‖cut V (Ioi a) g‖ ≤ ‖cut W (Iic (2 * M.T₀ - a)) p‖ := fun a => by
    have h1 := cutLaws (V := W) (Iic (2 * M.T₀ - a)) (Ioi (2 * M.T₀ - a)) measurableSet_Iic measurableSet_Ioi
    have h2 := h1.2.2.1 (Iic_disjoint_Ioi le_rfl)
    rw [Iic_union_Ioi, h1.2.2.2.1] at h2
    have h3 : p = cut W (Iic (2 * M.T₀ - a)) p + cut W (Ioi (2 * M.T₀ - a)) p := DFunLike.congr_fun h2 p
    have h4 := DFunLike.congr_fun ((projLaws M).2.2.2.2.2.2.2 a (2 * M.T₀ - a) (by linarith)).1 (M.J' p)
    change M.J (cut V (Ioi a) (M.J.symm (M.J' (cut W (Ioi (2 * M.T₀ - a)) (M.J'.symm (M.J' p)))))) = 0 at h4
    rw [M.J'.symm_apply_apply, M.J.map_eq_zero_iff] at h4
    have h5 : cut V (Ioi a) g = cut V (Ioi a) (M.J.symm (M.J' (cut W (Iic (2 * M.T₀ - a)) p))) := by
      rw [hg]
      conv_lhs => rw [h3]
      rw [map_add, map_add, map_add, h4, add_zero]
    rw [h5]
    refine ((cutLaws (V := V) (Ioi a) (Ioi a) measurableSet_Ioi measurableSet_Ioi).2.2.2.2.2.1 _).trans_eq ?_
    rw [M.J.symm.norm_map, M.J'.norm_map]
  have hw := wBound g p (2 * M.T₀) Q hcut hp
  have φcs : HasCompactSupport φ := HasCompactSupport.intro (isCompact_Icc (a := -(1 / 2)) (b := 1 / 2)) fun x hx =>
    φs x (by rw [mem_Icc, ← abs_le, not_le] at hx; exact hx)
  have φI : Integrable φ := φc.integrable_of_hasCompactSupport φcs
  have hsv := ((svSpec (V := V)).1 φ (φc.memLp_of_hasCompactSupport φcs) e).1
  have gm : Measurable fun y => ‖g y‖ₑ := (Lp.stronglyMeasurable g).enorm
  have hcor : ∀ s, ‖M.cor φ e p s‖ₑ ≤ ∫⁻ x, ‖φ x‖ₑ * ‖e‖ₑ * ‖g (x + s)‖ₑ := fun s => by
    have e1 : M.J' p = M.J g := by rw [hg, M.J.apply_symm_apply]
    rw [Sc.cor, e1, M.hJ, M.J.inner_map_map, L2.inner_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
    filter_upwards [hsv, sh_ae V s g] with x h1 h2
    rw [h1, h2, ← enorm_smul]
    exact enorm_inner_le _ _
  have main : ∀ q, Real.exp (2 * M.T₀) * Q < q → ‖∫ s in α..β, M.cor φ e p s‖ ≤ 6 / 5 * ‖e‖ * Real.exp (-α) * q := by
    intro q hq
    have q0 : 0 ≤ Real.exp (2 * M.T₀) * Q := by positivity
    have q1 : 0 < q := q0.trans_lt hq
    have hB := half g q (α - 1 / 2) q1 ⟨hw.1, hw.2.trans (pow_le_pow_left₀ q0 hq.le 2)⟩
    set B := 99 / 140 * Real.exp (-(α - 1 / 2)) * q with hBd
    have B0 : 0 ≤ B := by positivity
    have h1 : ‖∫ s in α..β, M.cor φ e p s‖ₑ ≤ ENNReal.ofReal (‖e‖ * B) := by
      rw [intervalIntegral.integral_of_le hαβ]
      calc _ ≤ ∫⁻ s in Ioc α β, ∫⁻ x, ‖φ x‖ₑ * ‖e‖ₑ * ‖g (x + s)‖ₑ :=
            (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono hcor)
        _ = ∫⁻ x, ∫⁻ s in Ioc α β, ‖φ x‖ₑ * ‖e‖ₑ * ‖g (x + s)‖ₑ :=
            lintegral_lintegral_swap (((φc.measurable.enorm.comp measurable_snd).mul_const _).mul
              (gm.comp (measurable_snd.add measurable_fst))).aemeasurable
        _ ≤ ∫⁻ x, ‖φ x‖ₑ * (‖e‖ₑ * ENNReal.ofReal B) := by
            refine lintegral_mono fun x => ?_
            by_cases hx : 1 / 2 < |x|
            · simp [φs x hx]
            have gx : Measurable fun s => ‖g (x + s)‖ₑ := gm.comp (measurable_const.add measurable_id)
            rw [lintegral_const_mul _ gx, mul_assoc]
            gcongr
            refine le_trans ?_ hB
            rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioi,
              ← lintegral_add_left_eq_self (fun y => (Ioi (α - 1 / 2)).indicator (fun y => ‖g y‖ₑ) y) x]
            refine lintegral_mono fun s => ?_
            by_cases hs : s ∈ Ioc α β
            · have h7 : x + s ∈ Ioi (α - 1 / 2) := by
                have h5 := (abs_le.1 (not_lt.1 hx)).1
                have h6 := hs.1
                rw [mem_Ioi]
                linarith
              rw [indicator_of_mem hs]
              exact (indicator_of_mem h7 fun y => ‖g y‖ₑ).ge
            · rw [indicator_of_notMem hs]
              exact bot_le
        _ = (∫⁻ x, ‖φ x‖ₑ) * (‖e‖ₑ * ENNReal.ofReal B) := lintegral_mul_const _ φc.measurable.enorm
        _ ≤ 1 * (‖e‖ₑ * ENNReal.ofReal B) := by
            gcongr
            rw [← ofReal_integral_norm_eq_lintegral_enorm φI]
            exact ENNReal.ofReal_le_one.2 φi
        _ = _ := by rw [one_mul, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    refine h1.trans ?_
    have h2 : Real.exp (1 / 2) ≤ 169 / 100 := by
      refine (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) two_ne_zero).1 ?_
      rw [← Real.exp_nat_mul]
      norm_num
      linarith [Real.exp_one_lt_d9]
    have h3 : Real.exp (-(α - 1 / 2)) = Real.exp (-α) * Real.exp (1 / 2) := by rw [← Real.exp_add]; ring_nf
    rw [hBd, h3]
    have h4 : 0 ≤ ‖e‖ * Real.exp (-α) * q := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h4]
  have := ge_of_tendsto (x := 𝓝[>] (Real.exp (2 * M.T₀) * Q))
    (((continuous_const (y := 6 / 5 * ‖e‖ * Real.exp (-α))).mul continuous_id).tendsto _ |>.mono_left nhdsWithin_le_nhds)
    (eventually_mem_nhdsWithin.mono fun q hq => main q hq)
  refine this.trans_eq ?_
  simp only [Pi.mul_apply, id]; ring
end

