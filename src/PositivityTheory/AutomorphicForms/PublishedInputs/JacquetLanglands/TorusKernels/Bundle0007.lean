import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Bundle0002
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Bundle0003
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ActionsPreserveMeasuresProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ActionsPreserveMeasuresLemmas

open UpperTheory.Esk

theorem count_pres {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] (f : α → α)
    (hf : Function.Bijective f) : MeasurePreserving f Measure.count Measure.count := by
  refine ⟨measurable_of_countable f, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_of_countable f) hs, Measure.count_apply hs,
    Measure.count_apply ((Set.to_countable _).measurableSet)]
  congr 1
  exact Set.encard_preimage_of_injective_subset_range hf.1 (hf.2.range_eq ▸ Set.subset_univ s)

theorem countable_PG (F : Type) [Field F] [Countable F] : Countable (PG F) := by
  have : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  have : Countable (GL (Fin 2) F) :=
    Function.Injective.countable (f := fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) fun a b h => Units.ext h
  exact QuotientGroup.mk_surjective.countable

theorem smulX {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (g : GL (Fin 2) F) (z : D.Xs) :
    ((g : PG F) • z) = (fun v => D.r v g • z v : I → P) := rfl

end UpperTheory.Esk.ActionsPreserveMeasuresLemmas

open UpperTheory.Esk.ActionsPreserveMeasuresLemmas in
theorem UpperTheory.Esk.actions_preserve_measures_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a := by
  intro h1 h2 h3 F I Gf _ _ _ D ax
  have : SigmaFinite (volume : Measure P) := h1.1
  have : (volume : Measure P).IsOpenPosMeasure := h1.2.1
  have : Countable F := ax.cF
  have hPG : Countable (PG F) := countable_PG F
  have : Countable D.Om := ax.cO
  have : Countable D.Cj := hPG
  have hXs : SigmaFinite (volume : Measure D.Xs) :=
    show SigmaFinite (Measure.pi fun _ : I => (volume : Measure P)) from inferInstance
  have presX : ∀ γ : PG F, MeasurePreserving (fun z : D.Xs => γ • z) volume volume := by
    intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    simp only [smulX]
    exact measurePreserving_pi (fun _ : I => (volume : Measure P)) (fun _ : I => (volume : Measure P))
      (fun v => (h1.2.2 (D.r v g)).2)
  have contX : ∀ γ : PG F, Continuous fun z : D.Xs => γ • z := by
    intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    simp only [smulX]
    exact continuous_pi fun v => (h1.2.2 (D.r v g)).1.comp (continuous_apply v)
  refine ⟨hPG, hXs, presX, ?_, ?_, contX, inferInstanceAs (BorelSpace (I → P)), ?_⟩
  · intro γ
    exact (count_pres (fun ω : D.Om => γ • ω) (MulAction.bijective γ)).prod (presX γ)
  · intro γ
    exact (count_pres (fun ω : D.Cj × D.Om => γ • ω) (MulAction.bijective γ)).prod (presX γ)
  · intro δ hδ
    have hk : Continuous fun p : P × P => kap p.1 p.2 := h3.2.2.2.2.1
    have hk1 : ∀ z : P, Continuous fun w => kap z w := fun z => hk.comp (continuous_const.prodMk continuous_id)
    set U : Set P := {w | δ < kap iP w} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const (hk1 iP)
    have hUp : 0 < volume U := hUo.measure_pos volume ⟨iP, by
      show δ < kap iP iP
      rw [h3.2.1 iP]; exact hδ⟩
    obtain ⟨c0, hc0, hc0U⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hUp
    have hS : ∀ z : P, MeasurableSet {w | δ ≤ kap z w} := fun z =>
      measurableSet_le measurable_const (hk1 z).measurable
    have hball : ∀ z : P, (c0 : ℝ≥0∞) ≤ volume {w | δ ≤ kap z w} := by
      intro z
      obtain ⟨g, -, -, hg⟩ := h3.2.2.2.2.2 z
      have hf := (h1.2.2 g).2
      have hpre : (fun w : P => g • w) ⁻¹' {w | δ ≤ kap z w} = {w | δ ≤ kap iP w} := by
        ext w
        show δ ≤ kap z (g • w) ↔ δ ≤ kap iP w
        rw [← hg, h2.2.2.2.1 g iP w]
      rw [← hf.measure_preimage (hS z).nullMeasurableSet, hpre]
      refine hc0U.le.trans (measure_mono fun w hw => ?_)
      exact le_of_lt (show δ < kap iP w from hw)
    refine ⟨c0 ^ Fintype.card I, pow_pos (by exact_mod_cast hc0) _, fun z => ?_⟩
    have hset : {w : X I | Near δ z w} = Set.univ.pi fun v => {w | δ ≤ kap (z v) w} := by
      ext w
      simp [Near, Set.mem_pi]
    rw [hset]
    refine ⟨MeasurableSet.univ_pi fun v => hS (z v), ?_⟩
    rw [volume_pi, Measure.pi_pi, ENNReal.coe_pow, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun v _ => hball (z v)
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AutomorphyFactorKernelAlgebraProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

theorem den_mul (g h : GL (Fin 2) ℝ) (z : P) : den (g * h) z.1 = den g (h • z).1 * den h z.1 := by
  have h0 := den_ne h z.2
  rw [coe_smul]
  conv_rhs => rw [den, add_mul, mul_assoc, div_mul_cancel₀ _ h0]
  simp [num, den, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem p1 (k : ℕ) (g h : GL (Fin 2) ℝ) (z : P) : j1 k (g * h) z = j1 k g (h • z) * j1 k h z := by
  simp only [j1, den_mul, mul_pow, Units.val_mul, Matrix.det_mul, abs_mul,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _), Complex.ofReal_mul]
  ring

theorem p2 (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : j1 k g z ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (den_ne g z.2))
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (abs_pos.2 g.det_ne_zero) _).ne')

theorem im_smul (g : GL (Fin 2) ℝ) (z : P) :
    (g • z).1.im = g.val.det * z.1.im / Complex.normSq (den g z.1) := by
  rw [coe_smul, im_div]

theorem sub_conj (g : GL (Fin 2) ℝ) (z w : P) :
    (g • z).1 - conj (g • w).1 = (g.val.det : ℂ) * (z.1 - conj w.1) / (den g z.1 * conj (den g w.1)) := by
  rw [coe_smul, coe_smul, map_div₀, div_sub_div _ _ (den_ne g z.2) ((map_ne_zero _).2 (den_ne g w.2))]
  congr 1
  simp only [num, den, map_add, map_mul, Complex.conj_ofReal, det_eq]
  push_cast
  ring

theorem sign (g : GL (Fin 2) ℝ) (z w : P) : 0 < (g • z).1.im * (g • w).1.im ↔ 0 < z.1.im * w.1.im := by
  rw [im_smul, im_smul]
  have hd : g.val.det ≠ 0 := g.det_ne_zero
  have nz : 0 < Complex.normSq (den g z.1) := Complex.normSq_pos.2 (den_ne g z.2)
  have nw : 0 < Complex.normSq (den g w.1) := Complex.normSq_pos.2 (den_ne g w.2)
  have hc : 0 < g.val.det ^ 2 / (Complex.normSq (den g z.1) * Complex.normSq (den g w.1)) :=
    div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hd))) (mul_pos nz nw)
  rw [show g.val.det * z.1.im / Complex.normSq (den g z.1) * (g.val.det * w.1.im / Complex.normSq (den g w.1))
      = g.val.det ^ 2 / (Complex.normSq (den g z.1) * Complex.normSq (den g w.1)) * (z.1.im * w.1.im) by
    field_simp]
  exact ⟨fun h => pos_of_mul_pos_right h hc.le, fun h => mul_pos hc h⟩

theorem ratio (g : GL (Fin 2) ℝ) (z w : P) (h : 0 < z.1.im * w.1.im) :
    ((g • w).1 - conj (g • w).1) / ((g • z).1 - conj (g • w).1)
      = (w.1 - conj w.1) / (z.1 - conj w.1) * (den g z.1 / den g w.1) := by
  have hd : (g.val.det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 g.det_ne_zero
  have h1 := den_ne g z.2
  have h2 := den_ne g w.2
  have h3 : conj (den g w.1) ≠ 0 := (map_ne_zero _).2 h2
  have h4 : z.1 - conj w.1 ≠ 0 := b_ne _ _ h
  have h5 : w.1 - conj w.1 ≠ 0 := b_ne _ _ (mul_self_pos.2 w.2)
  rw [sub_conj, sub_conj]
  field_simp

theorem p3 (k : ℕ) (g : GL (Fin 2) ℝ) (z w : P) :
    q1 k (g • z) (g • w) * j1 k g w = j1 k g z * q1 k z w := by
  unfold q1
  rw [if_congr (sign g z w) rfl rfl]
  split_ifs with h
  · rw [ratio g z w h, mul_pow, div_pow (den g z.1)]
    have h2 := pow_ne_zero k (den_ne g w.2)
    simp only [j1]
    field_simp
  · simp

theorem p4 (g : GL (Fin 2) ℝ) (z w : P) : kap (g • z) (g • w) = kap z w := by
  unfold kap
  rw [if_congr (sign g z w) rfl rfl]
  split_ifs with h
  · have hd : g.val.det ≠ 0 := g.det_ne_zero
    have nz : 0 < Complex.normSq (den g z.1) := Complex.normSq_pos.2 (den_ne g z.2)
    have nw : 0 < Complex.normSq (den g w.1) := Complex.normSq_pos.2 (den_ne g w.2)
    have h4 : ‖z.1 - conj w.1‖ ≠ 0 := norm_ne_zero_iff.2 (b_ne _ _ h)
    rw [im_smul, im_smul, sub_conj, norm_div, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, div_pow, mul_pow, mul_pow, sq_abs]
    simp only [Complex.sq_norm]
    field_simp
  · rfl

end UpperTheory.Esk.AutomorphyFactorLemmas

namespace UpperTheory.Esk

open AutomorphyFactorLemmas in
theorem automorphy_factor_kernel_algebra_proof : B1b :=
  ⟨p1, p2, p3, p4, p5, fun k z w hk => p6 k z w hk, p7, p8, p9⟩

end UpperTheory.Esk
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ConjNeOne
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

theorem key_id (α β u ub : ℂ) (hα : α ≠ 0) (hu : 1 - u ≠ 0) (h1 : β - α * u ≠ 0) (h2 : α - β * ub ≠ 0)
    (hA : α - β * u * ub ≠ 0) :
    (Complex.I * (β + α * u) / (β - α * u) - -Complex.I * (α + β * ub) / (α - β * ub)) /
      (Complex.I * (1 + u) / (1 - u) - -Complex.I * (α + β * ub) / (α - β * ub)) * ((β - α * u) / (1 - u)) =
      β * (1 - u * ub) / (1 - β / α * (u * ub)) := by
  have hI := Complex.I_ne_zero
  have e1 : Complex.I * (1 + u) / (1 - u) - -Complex.I * (α + β * ub) / (α - β * ub) =
      2 * Complex.I * (α - β * u * ub) / ((1 - u) * (α - β * ub)) := by
    field_simp; ring
  have e2 : Complex.I * (β + α * u) / (β - α * u) - -Complex.I * (α + β * ub) / (α - β * ub) =
      2 * Complex.I * α * β * (1 - u * ub) / ((β - α * u) * (α - β * ub)) := by
    field_simp; ring
  have e3 : 1 - β / α * (u * ub) = (α - β * u * ub) / α := by field_simp
  rw [e1, e2, e3]
  field_simp

theorem pow_combine (c X Y S T : ℂ) (k : ℕ) (h : X * Y / S = T) :
    c * X ^ k * (Y ^ k * (S ^ k)⁻¹) = c * T ^ k := by
  rw [← h, div_pow, mul_pow]; ring

theorem cayley_val (k : ℕ) (m : GL (Fin 2) ℝ) (a b : ℝ) (h00 : m 0 0 = a) (h01 : m 0 1 = b)
    (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ext1 (U k m) (Complex.I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ)) =
      ((k : ℂ) - 1) / (4 * Real.pi) * (eta a b * (1 - (r : ℂ) ^ 2) / (1 - eta a b ^ 2 * (r : ℂ) ^ 2)) ^ k := by
  set u := circleMap 0 r θ with hu_def
  have hnu : ‖u‖ = r := by simp [u, abs_of_pos hr0]
  have hu1 : (1 : ℂ) - u ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hnu; linarith
  have huu : u * conj u = (r : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnu]; push_cast; ring
  have hn : u.re ^ 2 + u.im ^ 2 = r ^ 2 := by
    rw [← hnu, Complex.sq_norm, Complex.normSq_apply]; ring
  set z := Complex.I * (1 + u) / (1 - u) with hz_def
  have hz_im : z.im = (1 - r ^ 2) / Complex.normSq (1 - u) := by
    rw [hz_def, Complex.div_im, ← sub_div]
    congr 1
    simp
    nlinarith [hn]
  have hzpos : 0 < z.im := by
    rw [hz_im]
    apply div_pos
    · nlinarith
    · exact Complex.normSq_pos.2 hu1
  have hz : z.im ≠ 0 := hzpos.ne'
  set zP : P := ⟨z, hz⟩ with hzP
  have hzP1 : zP.1 = z := rfl
  have hzpos' : 0 < zP.1.im := hzpos
  have hext : ext1 (U k m) z = F k m zP := by
    unfold ext1; rw [dif_pos hz]; exact if_pos hzpos'
  have hab : 0 < a ^ 2 + b ^ 2 := by
    have := lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 hb)); nlinarith [sq_nonneg a]
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (a ^ 2 + b ^ 2) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.2 hab
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := by rw [hs_def]; exact Real.sq_sqrt hab.le
  have hS0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hα0 : (a : ℂ) + b * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hb this
  have hβ0 : (a : ℂ) - b * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hb this
  have hden : den m z = (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u) / (1 - u) := by
    rw [eq_div_iff hu1]; unfold den; rw [h10, h11, hz_def]; push_cast; field_simp; ring
  have hnum : num m z = Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) / (1 - u) := by
    rw [eq_div_iff hu1]; unfold num; rw [h00, h01, hz_def]; field_simp
    linear_combination (b * (1 - u)) * Complex.I_sq
  have h1 : ((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u ≠ 0 := by
    have := den_ne m hz; rw [hden] at this; exact (div_ne_zero_iff.1 this).1
  have h2 : ((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * conj u ≠ 0 := by
    have h := (map_ne_zero (starRingEnd ℂ)).2 h1
    convert h using 1
    simp only [map_sub, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]; ring
  have hA : ((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * u * conj u ≠ 0 := by
    intro h
    rw [mul_assoc, huu, ← Complex.ofReal_pow] at h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.zero_im] at this
    have h3 : b * (1 + r ^ 2) = 0 := by
      linear_combination this
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hb h4
    · nlinarith [sq_nonneg r]
  have hw : (m • zP).1 = Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) /
      (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u) := by
    rw [coe_smul, hzP1, hnum, hden, div_div_div_cancel_right₀ hu1]
  have hwb : conj (Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) /
      (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u)) =
      -Complex.I * (((a : ℂ) + b * Complex.I) + ((a : ℂ) - b * Complex.I) * conj u) /
      (((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * conj u) := by
    simp only [map_div₀, map_sub, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]; ring
  have hwim : 0 < (m • zP).1.im := by
    rw [coe_smul, im_div, det_eq, h00, h01, h10, h11]
    apply div_pos (mul_pos (by nlinarith) hzpos') (Complex.normSq_pos.2 (den_ne m hz))
  have hdet : |m.val.det| = s ^ 2 := by
    rw [det_eq, h00, h01, h10, h11, hs2, abs_of_pos (by nlinarith)]; ring
  have hrp : (|m.val.det| ^ (-(k : ℝ) / 2) : ℝ) = (s ^ k)⁻¹ := by
    rw [hdet, ← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le,
      show ((2 : ℕ) : ℝ) * (-(k : ℝ) / 2) = -(k : ℝ) by push_cast; ring, Real.rpow_neg hs.le, Real.rpow_natCast]
  have hηsq : (((a : ℂ) - b * Complex.I) / (s : ℂ)) ^ 2 = ((a : ℂ) - b * Complex.I) / ((a : ℂ) + b * Complex.I) := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hS0) hα0, ← Complex.ofReal_pow, hs2]
    push_cast
    linear_combination (-((a : ℂ) - b * Complex.I) * (b : ℂ) ^ 2) * Complex.I_sq
  rw [hext]
  unfold F q1 j1
  rw [if_pos (mul_pos hzpos' hwim), hrp]
  push_cast
  refine pow_combine _ _ _ _ _ k ?_
  rw [hw, hwb, hzP1, hden, key_id _ _ _ _ hα0 hu1 h1 h2 hA, ← huu, eta, ← hs_def, hηsq]
  field_simp

end UpperTheory.Esk.RadialIntegralLemmas
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ContinuousCompTorusMap
section
noncomputable section

namespace UpperTheory.Esk.OrbitalSingularIntegrals

open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood

open scoped Real

def SepHol {n : ℕ} (f : (Fin n → ℂ) → ℂ) (S : Set (Fin n → ℂ)) : Prop :=
  ContinuousOn f S ∧ ∀ ζ ∈ S, ∀ i, DifferentiableAt ℂ (fun t => f (Function.update ζ i t)) (ζ i)

theorem continuous_comp_torusMap' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall c r)) :
    Continuous fun θ => f (torusMap c (fun _ => r) θ) :=
  hf.comp_continuous (continuous_torusMap c r) (torusMap_mem_closedBall c hr)

theorem torusIntegrable_kernel' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall c r)) (hz : z ∈ ball c r) :
    TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * f ζ) c (fun _ => r) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
  refine Continuous.mul ?_ (continuous_comp_torusMap' hr.le hf)
  refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr hz θ i
  exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const

theorem cauchy' : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (r : ℝ), 0 < r →
    SepHol f (closedBall c r) → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ) = (2 * π * I) ^ n * f z
  | 0, f, c, r, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, f, c, r, hr, hf, z, hz => by
    rw [torusIntegral_succ (torusIntegrable_kernel' hr hf.1 hz)]
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr).mp hz 0
    have hz' : Fin.tail z ∈ ball (fun i => c (Fin.succ i)) r :=
      (mem_ball_pi_iff hr).mpr fun i => (mem_ball_pi_iff hr).mp hz i.succ
    have hcons : ∀ x ∈ closedBall (c 0) r, ∀ y ∈ closedBall (fun i => c (Fin.succ i)) r,
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ closedBall c r := by
      intro x hx y hy
      refine (mem_closedBall_pi_iff hr.le).mpr fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using (mem_closedBall_pi_iff hr.le).mp hy j
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * f (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * f (Fin.cons x (Fin.tail z)))) (sphere (c 0) r) := by
      intro x hx
      have hxc : x ∈ closedBall (c 0) r := sphere_subset_closedBall hx
      have hS : SepHol (fun y => f (Fin.cons x y)) (closedBall (fun i => c (Fin.succ i)) r) := by
        refine ⟨?_, fun ζ hζ j => ?_⟩
        · exact hf.1.comp (differentiable_cons_right x).continuous.continuousOn
            (fun y hy => hcons x hxc y hy)
        · have h1 := hf.2 (Fin.cons x ζ) (hcons x hxc ζ hζ) j.succ
          have e : (fun t => f (Fin.cons x (Function.update ζ j t) : Fin (n + 1) → ℂ)) =
              fun t => f (Function.update (Fin.cons x ζ : Fin (n + 1) → ℂ) j.succ t) := by
            funext t
            rw [Fin.cons_update]
          show DifferentiableAt ℂ (fun t => f (Fin.cons x (Function.update ζ j t) : Fin (n + 1) → ℂ)) (ζ j)
          rw [e]
          simpa only [Fin.cons_succ] using h1
      have ih := cauchy' n (fun y => f (Fin.cons x y)) (fun i => c (Fin.succ i)) r hr hS (Fin.tail z) hz'
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr.le key, circleIntegral.integral_const_mul]
    have hd : DifferentiableOn ℂ (fun x => f (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) := by
      intro x hx
      have h1 := hf.2 (Fin.cons x (Fin.tail z)) (hcons x hx _ (ball_subset_closedBall hz')) 0
      simp only [Fin.update_cons_zero, Fin.cons_zero] at h1
      exact h1.differentiableWithinAt
    have h1 := hd.circleIntegral_sub_inv_smul hz0
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

variable {n : ℕ}

theorem integrableOn_fctl' {c : Fin n → ℂ} {r : ℝ} {f : (Fin n → ℂ) → ℂ}
    (hc : Continuous fun θ => f (torusMap c (fun _ => r) θ)) (g : C(Cube n, ℂ)) :
    IntegrableOn (fun θ => jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
  exact ((continuous_jac r).mul (g.continuous.comp continuous_cubeProj)).mul hc

def fctlCLM' (c : Fin n → ℂ) (r : ℝ) (f : (Fin n → ℂ) → ℂ)
    (hc : Continuous fun θ => f (torusMap c (fun _ => r) θ)) : C(Cube n, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fctl c r f
      map_add' := fun g g' => by
        simp only [fctl, ContinuousMap.add_apply, mul_add, add_mul]
        exact integral_add (integrableOn_fctl' hc g) (integrableOn_fctl' hc g')
      map_smul' := fun a g => by
        simp only [fctl, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext θ
        ring }
    (by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
        (((continuous_jac r).mul hc).continuousOn)
      refine ⟨M * volume.real (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)), fun g => ?_⟩
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top
        fun θ hθ => ?_).trans (le_of_eq (by ring))
      have h1 : ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ ≤ M := hM θ hθ
      rw [mul_comm (jac r θ), mul_assoc, norm_mul, mul_comm M]
      calc ‖g (cubeProj θ)‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖
          ≤ ‖g‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ :=
            mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖g‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

theorem fctlCLM'_kern {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : SepHol f (closedBall c r)) (hz : z ∈ ball c r) :
    fctlCLM' c r f (continuous_comp_torusMap' hr.le hf.1) (kern c r z) = (2 * π * I) ^ n * f z := by
  rw [← cauchy' n f c r hr hf z hz]
  show fctl c r f (kern c r z) = _
  unfold fctl torusIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  simp only [jac, kern_apply hr hz, cubeProj_of_mem hθ, smul_eq_mul]
  ring

theorem osgFin (U : Set (Fin n → ℂ)) (hU : IsOpen U) (f : (Fin n → ℂ) → ℂ) (hf : SepHol f U) :
    AnalyticOnNhd ℂ f U := by
  intro z0 hz0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z0 hz0
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : closedBall z0 (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
  have hS : SepHol f (closedBall z0 (ε / 2)) :=
    ⟨hf.1.mono hsub, fun ζ hζ i => hf.2 ζ (hsub hζ) i⟩
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have han : AnalyticAt ℂ (fun z => ((2 * π * I : ℂ) ^ n)⁻¹ *
      fctlCLM' z0 (ε / 2) f (continuous_comp_torusMap' hr.le hS.1) (kern z0 (ε / 2) z)) z0 :=
    analyticAt_const.mul (((fctlCLM' z0 (ε / 2) f _).analyticAt _).comp (kern_analyticAt z0 hr))
  refine han.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  rw [fctlCLM'_kern hr hS hz, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end UpperTheory.Esk.OrbitalSingularIntegrals

open UpperTheory.Esk.OrbitalSingularIntegrals in
theorem UpperTheory.Esk.pf_Osg : UpperTheory.Esk.Osg := by
  intro I _ _ U hU f hf hsep
  set n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let Φ : (Fin n → ℂ) → (I → ℂ) := fun w i => w (e i)
  have hΦ : Continuous Φ := continuous_pi fun i => continuous_apply (e i)
  let g : (Fin n → ℂ) → ℂ := fun w => f (Φ w)
  let V : Set (Fin n → ℂ) := Φ ⁻¹' U
  have hV : IsOpen V := hU.preimage hΦ
  have hupd : ∀ (w : Fin n → ℂ) (j : Fin n) (t : ℂ), Φ (Function.update w j t) = Function.update (Φ w) (e.symm j) t := by
    intro w j t
    funext i
    by_cases h : i = e.symm j
    · subst h
      simp [Φ]
    · have h' : e i ≠ j := fun h' => h (by rw [← h']; simp)
      simp [Φ, h, h']
  have hg : SepHol g V := by
    refine ⟨hf.comp hΦ.continuousOn (fun w hw => hw), fun w hw j => ?_⟩
    have h1 := hsep (Φ w) hw (e.symm j)
    have e1 : (fun t => g (Function.update w j t)) = fun t => f (Function.update (Φ w) (e.symm j) t) := by
      funext t
      simp only [g, hupd]
    rw [e1]
    simpa [Φ] using h1
  have hA := osgFin V hV g hg
  let Ψ : (I → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm j)
  have hΨ : ∀ z, Φ (Ψ z) = z := by
    intro z
    funext i
    simp [Φ, Ψ]
  intro z hz
  have hmem : Ψ z ∈ V := by
    show Φ (Ψ z) ∈ U
    rw [hΨ]
    exact hz
  have h2 := (hA (Ψ z) hmem).comp (Ψ.analyticAt z)
  have hfe : g ∘ Ψ = f := by
    funext w
    simp only [Function.comp, g, hΨ]
  rwa [hfe] at h2
end
end

