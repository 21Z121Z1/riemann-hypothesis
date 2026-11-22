import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaWeightStatement

-- bundled from ReciprocityTheory.L2DbarEstimates.SkodaWeights.HlinVsqPos
section
namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates ComplexConjugate
open scoped ENNReal InnerProductSpace

lemma hlin_sqC (a : ℂ) : ((‖a‖ ^ 2 : ℝ) : ℂ) = a * conj a := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma hlin_vsqC {p : ℕ} (w : Fin p → ℂ) : ((vsq w : ℝ) : ℂ) = ∑ i, w i * conj (w i) := by
  rw [vsq, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => hlin_sqC (w i)

lemma hlin_vsq_pos {p : ℕ} {g : Fin p → ℂ} (hg : g ≠ 0) : 0 < vsq g := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖g j‖) (Finset.mem_univ i))

theorem perpNorm : PerpNormStatement := by
  intro p g w hg
  have hs : ((vsq g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hlin_vsq_pos hg).ne'
  obtain ⟨c, hc⟩ : ∃ c, c = ∑ j, (starRingEnd ℂ) (g j) * w j := ⟨_, rfl⟩
  have hc' : ∑ i, g i * conj (w i) = conj c := by
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Complex.conj_conj, mul_comm]
  have key : ((vsq (perp g w) : ℝ) : ℂ) =
      ((vsq w : ℝ) : ℂ) - ((‖c‖ ^ 2 : ℝ) : ℂ) / ((vsq g : ℝ) : ℂ) := by
    rw [hlin_vsqC (perp g w), hlin_vsqC w, hlin_sqC]
    simp only [perp, ← hc]
    have e : ∀ i, (w i - g i * (c / ((vsq g : ℝ) : ℂ))) *
        conj (w i - g i * (c / ((vsq g : ℝ) : ℂ))) =
        w i * conj (w i) - conj c / ((vsq g : ℝ) : ℂ) * (conj (g i) * w i)
          - c / ((vsq g : ℝ) : ℂ) * (g i * conj (w i))
          + c * conj c / ((vsq g : ℝ) : ℂ) ^ 2 * (g i * conj (g i)) := by
      intro i
      simp only [map_sub, map_mul, map_div₀, Complex.conj_ofReal]
      ring
    rw [Finset.sum_congr rfl (fun i _ => e i)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← hc, hc', ← hlin_vsqC g]
    field_simp <;> ring
  rw [hc] at key
  exact_mod_cast key

theorem perpTrace : PerpTraceStatement := by
  intro p g hg
  have hs := hlin_vsq_pos hg
  refine ⟨fun i => sub_nonneg.mpr ((div_le_one hs).mpr
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖g j‖) (Finset.mem_univ i))), ?_⟩
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  change _ - vsq g / vsq g = _
  rw [div_self hs.ne']
  simp

lemma hlin_orth {p : ℕ} (g w : Fin p → ℂ) (hg : g ≠ 0) :
    ∑ j, conj (g j) * perp g w j = 0 := by
  have hs : ((vsq g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hlin_vsq_pos hg).ne'
  simp only [perp, mul_sub, Finset.sum_sub_distrib]
  have h2 : ∑ j, conj (g j) * (g j * ((∑ j, conj (g j) * w j) / ((vsq g : ℝ) : ℂ))) =
      ((vsq g : ℝ) : ℂ) * ((∑ j, conj (g j) * w j) / ((vsq g : ℝ) : ℂ)) := by
    generalize (∑ j, conj (g j) * w j) / ((vsq g : ℝ) : ℂ) = X
    rw [hlin_vsqC g, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2, mul_div_assoc', mul_div_cancel_left₀ _ hs, sub_self]

private lemma norm_sum_mul_sq_le_sum_sq_mul_sum_sq {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ q ∈ s, a q * b q‖ ^ 2 ≤ (∑ q ∈ s, ‖a q‖ ^ 2) * ∑ q ∈ s, ‖b q‖ ^ 2 := by
  calc ‖∑ q ∈ s, a q * b q‖ ^ 2 ≤ (∑ q ∈ s, ‖a q‖ * ‖b q‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => norm_mul _ _))
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s _ _

theorem perpEntry : PerpEntryStatement := by
  intro p g w i hg
  have hs := hlin_vsq_pos hg
  have horth := hlin_orth g w hg
  have hsplit : conj (g i) * perp g w i = -∑ j ∈ Finset.univ.erase i, conj (g j) * perp g w j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at horth
    linear_combination horth
  have hcs := norm_sum_mul_sq_le_sum_sq_mul_sum_sq (Finset.univ.erase i) (fun j => conj (g j)) (perp g w)
  have h0 : ‖conj (g i) * perp g w i‖ ^ 2 ≤
      (∑ j ∈ Finset.univ.erase i, ‖conj (g j)‖ ^ 2) *
        ∑ j ∈ Finset.univ.erase i, ‖perp g w j‖ ^ 2 := by
    rw [hsplit, norm_neg]
    exact hcs
  simp only [norm_mul, Complex.norm_conj, mul_pow] at h0
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), Finset.sum_erase_eq_sub (Finset.mem_univ i)] at h0
  change ‖g i‖ ^ 2 * ‖perp g w i‖ ^ 2 ≤ (vsq g - ‖g i‖ ^ 2) * (vsq (perp g w) - ‖perp g w i‖ ^ 2) at h0
  rw [one_sub_div hs.ne', div_mul_eq_mul_div, le_div_iff₀ hs]
  nlinarith [h0]

end ReciprocityTheory.L2DbarEstimates.H
end

-- bundled from ReciprocityTheory.L2DbarEstimates.SkodaWeights.NeedBergmanClosed
section
namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates

def NeedBergmanClosed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ ψ : M → ℝ, Continuous ψ →
    IsClosed (holSub n z ψ : Set (WeightedL2 n z ψ))

end ReciprocityTheory.L2DbarEstimates.H
end

-- bundled from ReciprocityTheory.L2DbarEstimates.SkodaWeights.WeightedIntegralEqLintegral
section
namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace

lemma measurable_exp_neg_density {M : Type*} [MeasurableSpace M] {ψ : M → ℝ} (hψ : Measurable ψ) :
    Measurable (fun x => ENNReal.ofReal (Real.exp (-ψ x))) := (hψ.neg.exp).ennreal_ofReal

lemma ae_weighted_iff_ae (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (P : M → Prop) :
    (∀ᵐ x ∂wvol n z ψ, P x) ↔ ∀ᵐ x ∂vol n z, P x := by
  unfold wvol
  rw [ae_withDensity_iff (measurable_exp_neg_density hψ)]
  refine ⟨fun h => h.mono fun x hx => hx ?_, fun h => h.mono fun x hx _ => hx⟩
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

lemma weightedIntegral_eq_lintegral (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (f : M → ℂ) :
    wint n z f ψ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂wvol n z ψ := by
  unfold wint wvol
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_exp_neg_density hψ)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm (‖f x‖ ^ 2), ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.rpow_two,
    ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

lemma eLpNorm_two_weighted_eq (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (f : M → ℂ) :
    eLpNorm f 2 (wvol n z ψ) = wint n z f ψ ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), ENNReal.toReal_ofNat,
    ← weightedIntegral_eq_lintegral n z hψ f]

theorem l2w (n : ℕ) (M : Type*) [MeasurableSpace M] : WeightedL2Properties n M := by
  intro z ψ hψ
  refine ⟨fun P => ae_weighted_iff_ae n z hψ P, fun F => ?_, fun f hf hfin => ?_⟩
  · have hlt := Lp.eLpNorm_lt_top F
    have hw : wint n z F ψ = eLpNorm F 2 (wvol n z ψ) ^ (2 : ℝ) := by
      rw [eLpNorm_two_weighted_eq n z hψ, ← ENNReal.rpow_mul]
      norm_num
    refine ⟨?_, ?_⟩
    · rw [hw]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne
    · rw [hw, Lp.norm_def, ← ENNReal.toReal_rpow, Real.rpow_two]
  · have hmem : MemLp f 2 (wvol n z ψ) := by
      refine ⟨hf.mono_ac (withDensity_absolutelyContinuous _ _), ?_⟩
      rw [eLpNorm_two_weighted_eq n z hψ f]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne
    exact ⟨hmem.toLp f, (ae_weighted_iff_ae n z hψ (fun x => (hmem.toLp f : M → ℂ) x = f x)).mp
      (MemLp.coeFn_toLp hmem)⟩

theorem volOpenPos (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    VolOpenPosStatement n M := by
  intro z hz U hU ⟨x, hx⟩
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz x
  have hW : IsOpen (U ∩ e.source) := hU.inter e.open_source
  have hinj : Set.InjOn z e.source := by
    intro a ha b hb hab
    rw [he ha, he hb] at hab
    exact e.injOn ha hb hab
  have himg : z '' (U ∩ e.source) = e '' (U ∩ e.source) :=
    Set.image_congr fun y hy => he hy.2
  have hpos : 0 < volume (z '' (U ∩ e.source)) := by
    rw [himg]
    exact (e.isOpen_image_of_subset_source hW Set.inter_subset_right).measure_pos _
      ⟨e x, x, ⟨hx, hxe⟩, rfl⟩
  rw [← vol_image n z hz e.source e.open_source hinj _ hW.measurableSet
    Set.inter_subset_right] at hpos
  exact hpos.trans_le (measure_mono Set.inter_subset_left)

end ReciprocityTheory.L2DbarEstimates.H
end

