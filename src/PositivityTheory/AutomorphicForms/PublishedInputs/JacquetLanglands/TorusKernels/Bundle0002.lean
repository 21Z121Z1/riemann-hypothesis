import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ARpowHalfSq
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

theorem a_sq_rpow {n : ℝ} (hn : 0 ≤ n) (k : ℕ) : (n ^ 2) ^ ((k : ℝ) / 2) = n ^ k := by
  rw [← Real.rpow_natCast n 2, ← Real.rpow_mul hn, ← Real.rpow_natCast n k]
  congr 1
  push_cast <;> ring

theorem a_rpow_half_sq {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : a ^ ((k : ℝ) / 2) * a ^ ((k : ℝ) / 2) = a ^ k := by
  rw [← Real.mul_rpow ha ha, ← sq, a_sq_rpow ha]

theorem p5 (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : ‖j1 k g z‖ * |(g • z).1.im| ^ ((k : ℝ) / 2) = |z.1.im| ^ ((k : ℝ) / 2) := by
  have hden : den g z.1 ≠ 0 := den_ne g z.2
  have hD : 0 < ‖den g z.1‖ := norm_pos_iff.mpr hden
  have hdet : 0 < |g.val.det| := abs_pos.mpr g.det_ne_zero
  have him : (g • z).1.im = g.val.det * z.1.im / Complex.normSq (den g z.1) := by
    rw [coe_smul, im_div]
  have hns : Complex.normSq (den g z.1) = ‖den g z.1‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have habs : |(g • z).1.im| = |g.val.det| * |z.1.im| / ‖den g z.1‖ ^ 2 := by
    rw [him, hns, abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖den g z.1‖ ^ 2)]
  have hj : ‖j1 k g z‖ = ‖den g z.1‖ ^ k * |g.val.det| ^ (-(k : ℝ) / 2) := by
    rw [j1, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hinv : |g.val.det| ^ (-(k : ℝ) / 2) * |g.val.det| ^ ((k : ℝ) / 2) = 1 := by
    rw [neg_div, Real.rpow_neg (abs_nonneg _), inv_mul_cancel₀ (Real.rpow_pos_of_pos hdet _).ne']
  have hDk : ‖den g z.1‖ ^ k ≠ 0 := pow_ne_zero _ hD.ne'
  rw [hj, habs, Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (abs_nonneg _) (abs_nonneg _),
    a_sq_rpow (norm_nonneg _)]
  rw [show ∀ A B C E : ℝ, A * B * (C * E / A) = (B * C) * E * (A / A) from fun _ _ _ _ => by ring,
    hinv, div_self hDk, one_mul, mul_one]

theorem a_sub_conj_ne (z w : P) (h : 0 < z.1.im * w.1.im) : z.1 - conj w.1 ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
  have hzw : z.1.im = -w.1.im := by linarith
  rw [hzw] at h
  nlinarith [sq_nonneg w.1.im]

theorem p6 (k : ℕ) (z w : P) (hk : 1 ≤ k) : ‖q1 k z w‖ * |z.1.im| ^ ((k : ℝ) / 2) = ((k : ℝ) - 1) / (4 * Real.pi) * kap z w ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) / 2 ≠ 0 := by
    intro h0
    linarith
  by_cases h : 0 < z.1.im * w.1.im
  · have hq : q1 k z w = ((k : ℂ) - 1) / (4 * Real.pi) * ((w.1 - conj w.1) / (z.1 - conj w.1)) ^ k := by
      rw [q1, if_pos h]
    have hkap : kap z w = 4 * (z.1.im * w.1.im) / ‖z.1 - conj w.1‖ ^ 2 := by
      rw [kap, if_pos h]
    have hd : z.1 - conj w.1 ≠ 0 := a_sub_conj_ne z w h
    have hdn : 0 < ‖z.1 - conj w.1‖ := norm_pos_iff.mpr hd
    have hww : ‖w.1 - conj w.1‖ = 2 * |w.1.im| := by
      rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    have hc : ‖((k : ℂ) - 1) / (4 * Real.pi)‖ = ((k : ℝ) - 1) / (4 * Real.pi) := by
      have hpi := Real.pi_pos
      have e : ((k : ℂ) - 1) / (4 * Real.pi) = ((((k : ℝ) - 1) / (4 * Real.pi) : ℝ) : ℂ) := by
        push_cast <;> ring
      rw [e, Complex.norm_real, Real.norm_of_nonneg (by apply div_nonneg <;> linarith)]
    have hzw : z.1.im * w.1.im = |z.1.im| * |w.1.im| := by
      rw [← abs_mul, abs_of_pos h]
    have h4 : (4 : ℝ) ^ ((k : ℝ) / 2) = 2 ^ k := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, a_sq_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hq, norm_mul, hc, norm_pow, norm_div, hww, hkap, hzw,
      Real.div_rpow (by positivity) (by positivity), a_sq_rpow hdn.le,
      Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (abs_nonneg _) (abs_nonneg _), h4,
      div_pow, mul_pow, ← a_rpow_half_sq (abs_nonneg w.1.im) k]
    ring
  · have hq : q1 k z w = 0 := by
      rw [q1, if_neg h]
    have hkap : kap z w = 0 := by
      rw [kap, if_neg h]
    rw [hq, hkap, norm_zero, zero_mul, Real.zero_rpow hk0, mul_zero, zero_mul]

end UpperTheory.Esk.AutomorphyFactorLemmas
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ActionIntegralSwapProof
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Esk.AnnihilatorQuotientResidues

variable {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] {μ : Measure Y}

def actEquiv (hP : Pres G μ) (g : G) : Y ≃ᵐ Y where
  toEquiv := MulAction.toPerm g
  measurable_toFun := (hP g).measurable
  measurable_invFun := (hP g⁻¹).measurable

lemma embed (hP : Pres G μ) (g : G) : MeasurableEmbedding (fun y : Y => g • y) :=
  (actEquiv hP g).measurableEmbedding

lemma enorm_cut {b : Y → ℝ} (hb : IsCut G b) (y : Y) (x : ℂ) :
    ‖b y • x‖ₑ = ENNReal.ofReal (b y) * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal (hb.nonneg y)]

lemma lint_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ
      = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ := by
  rw [← lintegral_tsum]
  · congr 1
    funext y
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb'.nonneg _)
      (hb'.sum y).summable, (hb'.sum y).tsum_eq, ENNReal.ofReal_one, one_mul]
  · intro g
    exact ((ENNReal.measurable_ofReal.comp (hb'.meas.comp (hP g).measurable)).mul
      ((ENNReal.measurable_ofReal.comp hb.meas).mul hu)).aemeasurable

lemma lint_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℝ≥0∞)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ
      = ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ := by
  have h := (hP g).lintegral_comp_emb (embed hP g)
    (fun z => ENNReal.ofReal (b (g⁻¹ • z)) * (ENNReal.ofReal (b' z) * u z))
  rw [← h]
  congr 1
  funext y
  simp only [inv_smul_smul, hinv]
  ring

lemma lint_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ = ∫⁻ y, ENNReal.ofReal (b' y) * u y ∂μ := by
  rw [lint_split hP hb hb' u hu, lint_split hP hb' hb u hu]
  calc _ = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ :=
        tsum_congr (lint_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq
        (fun g => ∫⁻ y, ENNReal.ofReal (b (g • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ)

lemma integrable_swap [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) : Integrable (fun y => b' y • u y) μ := by
  refine ⟨(hb'.meas.smul hu).aestronglyMeasurable, ?_⟩
  have h := hi.hasFiniteIntegral
  have e := lint_eq hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm (fun g y => by simp only [hinv])
  simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h ⊢
  rwa [← e]

lemma int_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hi : Integrable (fun y => b y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∑' g : G, ∫ y, b' (g • y) • (b y • u y) ∂μ := by
  rw [← integral_tsum]
  · congr 1
    funext y
    rw [(hb'.sum y).summable.tsum_smul_const, (hb'.sum y).tsum_eq, one_smul]
  · intro g
    exact ((hb'.meas.comp (hP g).measurable).smul (hb.meas.smul hu)).aestronglyMeasurable
  · have h := hi.hasFiniteIntegral
    have e := lint_split hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm
    simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h e ⊢
    rw [← e]
    exact h.ne

lemma int_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℂ)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫ y, b' (g • y) • (b y • u y) ∂μ = ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := by
  have h := (hP g).integral_comp (embed hP g) (fun z => b (g⁻¹ • z) • (b' z • u z))
  rw [← h]
  congr 1
  funext y
  simp only [inv_smul_smul, hinv]
  rw [smul_comm]

lemma int_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) (hi' : Integrable (fun y => b' y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∫ y, b' y • u y ∂μ := by
  rw [int_split hP hb hb' u hu hi, int_split hP hb' hb u hu hi']
  calc _ = ∑' g : G, ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := tsum_congr (int_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq (fun g => ∫ y, b (g • y) • (b' y • u y) ∂μ)

end UpperTheory.Esk.AnnihilatorQuotientResidues

theorem UpperTheory.Esk.action_integral_swap_proof : UpperTheory.Esk.C1 := by
  intro G Y _ _ _ _ μ hP b b' hb hb'
  refine ⟨fun u hu hinv => UpperTheory.Esk.AnnihilatorQuotientResidues.lint_eq hP hb hb' u hu hinv, fun u hu hinv hi => ?_⟩
  have hi' := UpperTheory.Esk.AnnihilatorQuotientResidues.integrable_swap hP hb hb' u hu hinv hi
  exact ⟨hi', UpperTheory.Esk.AnnihilatorQuotientResidues.int_eq hP hb hb' u hu hinv hi hi'⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.BNeg
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

theorem b_cv : Continuous (fun z : P => z.1) := by
  exact continuous_subtype_val

theorem b_ne (z w : ℂ) (h : 0 < z.im * w.im) : z - conj w ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.im h0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at h1
  have h2 : w.im = -z.im := by linarith
  rw [h2] at h
  nlinarith [mul_self_nonneg z.im]

theorem b_neg (z w : P) (h : ¬ 0 < z.1.im * w.1.im) : z.1.im * w.1.im < 0 := by
  have hne : z.1.im * w.1.im ≠ 0 := mul_ne_zero z.2 w.2
  exact lt_of_le_of_ne (not_lt.mp h) hne

theorem p7 (k : ℕ) (g : GL (Fin 2) ℝ) : Continuous (j1 k g) := by
  unfold j1 den
  exact (((continuous_const.mul b_cv).add continuous_const).pow k).mul continuous_const

theorem p8 (k : ℕ) : Continuous fun p : P × P => q1 k p.1 p.2 := by
  have hz : Continuous fun p : P × P => p.1.1 := b_cv.comp continuous_fst
  have hw : Continuous fun p : P × P => p.2.1 := b_cv.comp continuous_snd
  have hf : Continuous fun p : P × P => p.1.1.im * p.2.1.im :=
    (Complex.continuous_im.comp hz).mul (Complex.continuous_im.comp hw)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : 0 < p.1.1.im * p.2.1.im
  · have hU : ∀ᶠ q in nhds p, 0 < q.1.1.im * q.2.1.im := (hf.tendsto p).eventually (lt_mem_nhds hp)
    have hg : ContinuousAt (fun q : P × P =>
        ((k : ℂ) - 1) / (4 * Real.pi) * ((q.2.1 - conj q.2.1) / (q.1.1 - conj q.2.1)) ^ k) p := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.pow
      apply ContinuousAt.div
      · exact (hw.sub (Complex.continuous_conj.comp hw)).continuousAt
      · exact (hz.sub (Complex.continuous_conj.comp hw)).continuousAt
      · exact b_ne _ _ hp
    apply hg.congr
    filter_upwards [hU] with q hq
    simp only [q1, if_pos hq]
  · have hV : ∀ᶠ q in nhds p, q.1.1.im * q.2.1.im < 0 :=
      (hf.tendsto p).eventually (gt_mem_nhds (b_neg p.1 p.2 hp))
    have hg : ContinuousAt (fun _ : P × P => (0 : ℂ)) p := continuousAt_const
    apply hg.congr
    filter_upwards [hV] with q hq
    simp only [q1, if_neg (not_lt.mpr hq.le)]

theorem p9 (k : ℕ) (w : P) : Hol1 fun z => q1 k z w := by
  intro t ht
  have ht' : t.im ≠ 0 := ht
  apply DifferentiableAt.differentiableWithinAt
  have hcont : Continuous fun s : ℂ => s.im * w.1.im := Complex.continuous_im.mul continuous_const
  by_cases hp : 0 < t.im * w.1.im
  · have hU : ∀ᶠ s in nhds t, 0 < s.im * w.1.im := (hcont.tendsto t).eventually (lt_mem_nhds hp)
    have hd : DifferentiableAt ℂ (fun s : ℂ =>
        ((k : ℂ) - 1) / (4 * Real.pi) * ((w.1 - conj w.1) / (s - conj w.1)) ^ k) t := by
      apply DifferentiableAt.mul (differentiableAt_const _)
      apply DifferentiableAt.pow
      apply DifferentiableAt.div (differentiableAt_const _) (differentiableAt_id.sub (differentiableAt_const _))
      exact b_ne _ _ hp
    apply hd.congr_of_eventuallyEq
    filter_upwards [hU] with s hs
    have hs' : s.im ≠ 0 := fun h0 => by rw [h0, zero_mul] at hs; exact lt_irrefl _ hs
    simp only [ext1, dif_pos hs', q1, if_pos hs]
  · have hneg : t.im * w.1.im < 0 := lt_of_le_of_ne (not_lt.mp hp) (mul_ne_zero ht' w.2)
    have hV : ∀ᶠ s in nhds t, s.im * w.1.im < 0 := (hcont.tendsto t).eventually (gt_mem_nhds hneg)
    apply (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [hV] with s hs
    by_cases hs' : s.im ≠ 0
    · simp only [ext1, dif_pos hs', q1, if_neg (not_lt.mpr hs.le)]
    · simp only [ext1, dif_neg hs']

end UpperTheory.Esk.AutomorphyFactorLemmas
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.CayleyTransformProof
section
noncomputable section

open MeasureTheory Set Complex Metric
open scoped ComplexConjugate Real

namespace UpperTheory.Esk.CayleyTransform

def cay (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

theorem im_cay (w : ℂ) (hw : w ≠ 1) : (cay w).im = (1 - normSq w) / normSq (1 - w) := by
  have hn : normSq (1 - w) ≠ 0 := (normSq_pos.2 (sub_ne_zero.2 hw.symm)).ne'
  rw [cay, Complex.div_im]
  simp only [normSq_apply, mul_im, mul_re, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im] at hn ⊢
  field_simp
  ring

theorem hasDerivAt_cay (w : ℂ) (hw : w ≠ 1) : HasDerivAt cay (2 * Complex.I / (1 - w) ^ 2) w := by
  have h1 : (1 - w) ≠ 0 := sub_ne_zero.2 hw.symm
  have := (((hasDerivAt_id w).const_add 1).const_mul Complex.I).div ((hasDerivAt_id w).const_sub 1) h1
  have hf : cay = (fun y => Complex.I * (1 + id y)) / (fun x => 1 - id x) := by
    funext x; simp [cay]
  rw [hf]
  refine this.congr_deriv ?_
  show (Complex.I * 1 * (1 - w) - Complex.I * (1 + w) * -1) / (1 - w) ^ 2 = 2 * Complex.I / (1 - w) ^ 2
  ring

theorem det_cay (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = normSq c := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

theorem ne_one_of_mem (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := by
  rintro rfl; simp at hw

theorem normSq_lt_of_mem (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : normSq w < 1 := by
  rw [mem_ball_zero_iff] at hw
  rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]

theorem image_cay : cay '' ball (0 : ℂ) 1 = {t : ℂ | 0 < t.im} := by
  ext t
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 := ne_one_of_mem w hw
    have h2 := normSq_lt_of_mem w hw
    simp only [mem_ofPred_eq]
    rw [im_cay w h1]
    exact div_pos (by linarith) (normSq_pos.2 (sub_ne_zero.2 h1.symm))
  · intro ht
    simp only [mem_ofPred_eq] at ht
    have hd : t + Complex.I ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    refine ⟨(t - Complex.I) / (t + Complex.I), ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.2 hd)]
      rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
      simp only [normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
      nlinarith
    · have h3 : 1 - (t - Complex.I) / (t + Complex.I) ≠ 0 := by
        rw [one_sub_div hd]; simp [hd]
      rw [cay, div_eq_iff h3]
      field_simp
      ring

theorem injOn_cay : InjOn cay (ball (0 : ℂ) 1) := by
  intro a ha b hb hab
  have h1 : 1 - a ≠ 0 := sub_ne_zero.2 (ne_one_of_mem a ha).symm
  have h2 : 1 - b ≠ 0 := sub_ne_zero.2 (ne_one_of_mem b hb).symm
  simp only [cay] at hab
  rw [div_eq_div_iff h1 h2] at hab
  have : Complex.I * (2 * (a - b)) = 0 := by linear_combination hab
  simpa [sub_eq_zero] using this

theorem step2 (g : ℂ → ℂ) (hg : IntegrableOn g {t : ℂ | 0 < t.im}) :
    IntegrableOn (fun w => ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) * g (cay w)) (ball 0 1) ∧
    ∫ t in {t : ℂ | 0 < t.im}, g t = ∫ w in ball (0 : ℂ) 1, ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) * g (cay w) := by
  have hs : MeasurableSet (ball (0 : ℂ) 1) := measurableSet_ball
  have hf' : ∀ w ∈ ball (0 : ℂ) 1, HasFDerivWithinAt cay
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ)
      (ball 0 1) w := fun w hw =>
    ((hasDerivAt_cay w (ne_one_of_mem w hw)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ w ∈ ball (0 : ℂ) 1,
      |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ).det|
        = 4 / normSq (1 - w) ^ 2 := by
    intro w hw
    rw [det_cay, abs_of_nonneg (normSq_nonneg _), map_div₀, map_pow, map_mul]
    simp [normSq_apply]
    norm_num
  have hpt : EqOn (fun w => |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ).det| • g (cay w))
      (fun w => ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) * g (cay w)) (ball 0 1) := by
    intro w hw
    simp only
    rw [hdet w hw, Complex.real_smul]
  rw [← image_cay] at hg ⊢
  constructor
  · exact ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hf' injOn_cay g).1 hg).congr_fun
      hpt hs
  · rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hf' injOn_cay]
    exact setIntegral_congr_fun hs hpt

theorem step1 (h : P → ℂ) (h0 : ∀ z : P, z.1.im < 0 → h z = 0) (hi : Integrable h) :
    IntegrableOn (fun t : ℂ => ((1 / t.im ^ 2 : ℝ) : ℂ) * ext1 h t) {t : ℂ | 0 < t.im} ∧
    ∫ z, h z = ∫ t in {t : ℂ | 0 < t.im}, ((1 / t.im ^ 2 : ℝ) : ℂ) * ext1 h t := by
  set S : Set ℂ := {t | t.im ≠ 0} with hSdef
  have hS : MeasurableSet S := (isOpen_ne_fun continuous_im continuous_const).measurableSet
  set g : ℂ → ℂ := fun t => ((1 / t.im ^ 2 : ℝ) : ℂ) * ext1 h t with hg
  have hρ : Measurable (fun z : S => ENNReal.ofReal (1 / z.1.im ^ 2)) := by fun_prop
  have hfin : ∀ᵐ z ∂(Measure.comap (Subtype.val : S → ℂ) volume), ENNReal.ofReal (1 / z.1.im ^ 2) < ⊤ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  set h' : S → ℂ := fun z => h ⟨z.1, z.2⟩ with hh'
  have key : (fun z : S => (ENNReal.ofReal (1 / z.1.im ^ 2)).toReal • h' z) = g ∘ Subtype.val := by
    funext z
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hz : (z : ℂ).im ≠ 0 := z.2
    simp [g, ext1, hz, h', Complex.real_smul]
  have hi' : Integrable h'
      ((Measure.comap (Subtype.val : S → ℂ) volume).withDensity fun z => ENNReal.ofReal (1 / z.1.im ^ 2)) := hi
  have iS : IntegrableOn g S := by
    rw [integrableOn_iff_comap_subtypeVal hS, ← key]
    exact (integrable_withDensity_iff_integrable_smul' hρ hfin).1 hi'
  have hsub : {t : ℂ | 0 < t.im} ⊆ S := fun t ht => ne_of_gt ht
  refine ⟨iS.mono_set hsub, ?_⟩
  have e1 : ∫ z, h z = ∫ z : S, h' z ∂((Measure.comap (Subtype.val : S → ℂ) volume).withDensity
      fun z => ENNReal.ofReal (1 / z.1.im ^ 2)) := rfl
  rw [e1, integral_withDensity_eq_integral_toReal_smul hρ hfin, key]
  change ∫ z : S, g z ∂(Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap hS g]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (f := g) hS hsub ?_
  intro t ⟨ht1, ht2⟩
  have hlt : t.im < 0 := lt_of_le_of_ne (not_lt.1 ht2) ht1
  simp [g, ext1, h0 ⟨t, ht1⟩ hlt]

theorem step3 (F : ℂ → ℂ) (hF : IntegrableOn F (ball 0 1)) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F (circleMap 0 p.1 p.2)) (Ioo 0 1 ×ˢ Ioo (-π) π) ∧
    ∫ w in ball (0 : ℂ) 1, F w = ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π, (p.1 : ℂ) * F (circleMap 0 p.1 p.2) := by
  have hp : MeasurePreserving Complex.measurableEquivRealProd.symm volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm
  have hSm : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := measurableSet_Ioo.prod measurableSet_Ioo
  have he : ∀ q : ℝ × ℝ, ‖Complex.measurableEquivRealProd.symm q‖ = √(q.1 ^ 2 + q.2 ^ 2) := by
    intro q
    change ‖Complex.equivRealProd.symm q‖ = _
    rw [Complex.equivRealProd_symm_apply, Complex.norm_def, Complex.normSq_add_mul_I]
  have hsub : polarCoord.symm '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) ⊆
      Complex.measurableEquivRealProd.symm ⁻¹' ball 0 1 := by
    rintro _ ⟨p, hp', rfl⟩
    simp only [mem_preimage, mem_ball_zero_iff]
    rw [measurableEquivRealProd_symm_polarCoord_symm_apply, norm_polarCoord_symm, abs_of_pos hp'.1.1]
    exact hp'.1.2
  have hae : polarCoord.symm '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) =ᵐ[volume]
      Complex.measurableEquivRealProd.symm ⁻¹' ball 0 1 := by
    filter_upwards [polarCoord_source_ae_eq_univ] with q hq
    have hq' : q ∈ polarCoord.source := by
      change polarCoord.source q
      rw [hq]; trivial
    apply propext
    constructor
    · exact fun h => hsub h
    · intro hqT
      have hm := polarCoord.map_source hq'
      refine ⟨polarCoord q, ⟨⟨hm.1, ?_⟩, hm.2⟩, polarCoord.left_inv hq'⟩
      change Complex.measurableEquivRealProd.symm q ∈ ball (0 : ℂ) 1 at hqT
      rw [mem_ball_zero_iff, he] at hqT
      simpa using hqT
  have hG : IntegrableOn (F ∘ Complex.measurableEquivRealProd.symm)
      (Complex.measurableEquivRealProd.symm ⁻¹' ball 0 1) :=
    (hp.integrableOn_comp_preimage Complex.measurableEquivRealProd.symm.measurableEmbedding).2 hF
  have hG' := hG.mono_set hsub
  have hder : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π,
      HasFDerivWithinAt polarCoord.symm (fderivPolarCoordSymm p) (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) p :=
    fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt
  have hinj : InjOn polarCoord.symm (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) :=
    polarCoord.symm.injOn.mono (fun p hp => show p ∈ polarCoord.target from ⟨hp.1.1, hp.2⟩)
  have hpt : EqOn (fun p : ℝ × ℝ => |(fderivPolarCoordSymm p).det| •
      (F ∘ Complex.measurableEquivRealProd.symm) (polarCoord.symm p))
      (fun p : ℝ × ℝ => (p.1 : ℂ) * F (circleMap 0 p.1 p.2)) (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := by
    intro p hp
    simp only
    rw [det_fderivPolarCoordSymm, abs_of_pos hp.1.1, Function.comp_apply,
      measurableEquivRealProd_symm_polarCoord_symm_apply, Complex.polarCoord_symm_apply,
      Complex.real_smul]
    congr 2
    rw [circleMap, zero_add, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  constructor
  · exact ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hSm hder hinj _).1 hG').congr_fun
      hpt hSm
  · rw [← hp.setIntegral_preimage_emb Complex.measurableEquivRealProd.symm.measurableEmbedding F (ball 0 1),
      ← setIntegral_congr_set hae,
      integral_image_eq_integral_abs_det_fderiv_smul volume hSm hder hinj]
    exact setIntegral_congr_fun hSm hpt

end UpperTheory.Esk.CayleyTransform

open UpperTheory.Esk.CayleyTransform in
theorem UpperTheory.Esk.cayley_transform_proof : UpperTheory.Esk.B2 := by
  intro h h0 hi
  obtain ⟨i1, e1⟩ := step1 h h0 hi
  obtain ⟨i2, e2⟩ := step2 _ i1
  set F : ℂ → ℂ := fun w => ((4 / (1 - normSq w) ^ 2 : ℝ) : ℂ) * ext1 h (cay w) with hF
  have eqD : EqOn (fun w => ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) *
      (((1 / (cay w).im ^ 2 : ℝ) : ℂ) * ext1 h (cay w))) F (ball 0 1) := by
    intro w hw
    have hw1 : normSq w < 1 := by
      rw [mem_ball_zero_iff] at hw
      rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    have hne : w ≠ 1 := by rintro rfl; simp at hw1
    have hn : 0 < normSq (1 - w) := normSq_pos.2 (sub_ne_zero.2 hne.symm)
    have h1 : 0 < 1 - normSq w := by linarith
    simp only [F]
    rw [im_cay w hne, ← mul_assoc, ← ofReal_mul]
    congr 2
    field_simp
  have i3 := i2.congr_fun eqD measurableSet_ball
  obtain ⟨i4, e4⟩ := step3 F i3
  have eqS : EqOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F (circleMap 0 p.1 p.2))
      (fun p : ℝ × ℝ => ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) *
        ext1 h (Complex.I * (1 + circleMap 0 p.1 p.2) / (1 - circleMap 0 p.1 p.2)))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hc : normSq (circleMap 0 r θ) = r ^ 2 := by
      rw [normSq_eq_norm_sq, norm_circleMap_zero, abs_of_pos hr.1]
    simp only [F, hc, cay]
    push_cast
    ring
  refine ⟨i4.congr_fun eqS (measurableSet_Ioo.prod measurableSet_Ioo), ?_⟩
  rw [e1, e2, setIntegral_congr_fun measurableSet_ball eqD, e4]
  exact setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) eqS
end
end

