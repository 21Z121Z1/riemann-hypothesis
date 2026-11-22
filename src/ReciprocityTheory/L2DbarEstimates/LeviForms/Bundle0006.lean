import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.AddLogPosOfThreeQuartersLe
section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

universe u

noncomputable section

def dualSig (s : ℝ) : ℝ := 3 / 4 + (s - 3 / 4) * Real.smoothTransition ((s - 3 / 4) * 8)

lemma dualSig_contDiff : ContDiff ℝ ∞ dualSig := by
  unfold dualSig
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).mul contDiff_const)))

lemma dualSig_ge (s : ℝ) : 3 / 4 ≤ dualSig s := by
  unfold dualSig
  rcases le_or_gt s (3 / 4) with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by nlinarith)]
    simp
  · have := Real.smoothTransition.nonneg ((s - 3 / 4) * 8)
    nlinarith

lemma dualSig_eq {s : ℝ} (hs : 7 / 8 ≤ s) : dualSig s = s := by
  unfold dualSig
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

lemma add_log_pos_of_three_quarters_le {s : ℝ} (hs : 3 / 4 ≤ s) : 0 < s + Real.log s := by
  have h0 : 0 < s := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos h0
  have h2 : s⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ h0 (by norm_num)]
    linarith
  linarith

def dualK (c t : ℝ) : ℝ := -Real.log (dualSig (c - t) + Real.log (dualSig (c - t)))

lemma dualK_contDiff (c : ℝ) : ContDiff ℝ ∞ (dualK c) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => dualSig (c - t)) :=
    dualSig_contDiff.comp (contDiff_const.sub contDiff_id)
  have hpos : ∀ t, 0 < dualSig (c - t) := fun t => by linarith [dualSig_ge (c - t)]
  have hl : ContDiff ℝ ∞ (fun t : ℝ => Real.log (dualSig (c - t))) :=
    hs.log (fun t => (hpos t).ne')
  have hsum : ContDiff ℝ ∞ (fun t : ℝ => dualSig (c - t) + Real.log (dualSig (c - t))) := hs.add hl
  have := hsum.log (fun t => (add_log_pos_of_three_quarters_le (dualSig_ge (c - t))).ne')
  exact this.neg

lemma dualK_eq {c t : ℝ} (h : 7 / 8 ≤ c - t) :
    dualK c t = -Real.log ((c - t) + Real.log (c - t)) := by
  unfold dualK
  rw [dualSig_eq h]

lemma dualK_deriv {c t : ℝ} (h : 1 ≤ c - t) :
    deriv (dualK c) t = (1 + 1 / (c - t)) / ((c - t) + Real.log (c - t)) := by
  have hev : dualK c =ᶠ[𝓝 t] fun u => -Real.log ((c - u) + Real.log (c - u)) := by
    have : ∀ᶠ u in 𝓝 t, u < t + 1 / 8 := eventually_lt_nhds (by linarith)
    filter_upwards [this] with u hu
    exact dualK_eq (by linarith)
  rw [hev.deriv_eq]
  have hs0 : c - t ≠ 0 := by linarith
  have hpos : 0 < (c - t) + Real.log (c - t) := add_log_pos_of_three_quarters_le (by linarith)
  have h1 : HasDerivAt (fun u : ℝ => c - u) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub c
  have h2 := h1.log hs0
  have h4 : HasDerivAt (fun u => -Real.log ((c - u) + Real.log (c - u)))
      (-((-1 + -1 / (c - t)) / ((c - t) + Real.log (c - t)))) t :=
    ((h1.add h2).log hpos.ne').neg
  rw [h4.deriv]
  field_simp
  ring

lemma dual_dbarDot_comp_real {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℝ → ℝ)
    (hk : ContDiff ℝ ∞ k) (f : M → ℝ) (hf : CkR n z 1 f) (x : M) (ξ : Fin n → ℂ) :
    ‖dbarDot n z (fun y => (k (f y) : ℂ)) x ξ‖ =
      |deriv k (f x)| * ‖dDot n z (fun y => (f y : ℂ)) x ξ‖ := by
  have : dbarDot n z (fun y => (k (f y) : ℂ)) x ξ =
      ((deriv k (f x) : ℝ) : ℂ) * (starRingEnd ℂ) (dDot n z (fun y => (f y : ℂ)) x ξ) := by
    unfold dbarDot dDot
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [db_comp_real n z k hk f hf i x, db_ofReal, map_mul]
    ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]

theorem dual (n : ℕ) (M : Type u) [TopologicalSpace M]
    (hT : TwistLeviStatement n M) (hB : BasicStatement n M) : DualStatement n M := by
  intro z g ph ph2 r j ε δ hz hg hph hphL hph2 hph2L hr hj hε hδ hbd
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun x ξ => ?_, fun x ξ _ => ?_, fun x ξ _ => ?_⟩ <;> simp [dbarDot, Levi]
  obtain ⟨hB1, -, -, -⟩ := hB g ph ph2 r j ε δ hr hε hbd
  obtain ⟨-, -, hT1, hT2⟩ := hT z g ph ph2 r j ε δ hz hg hph hphL hph2 hph2L hr hj hε hδ hbd
  obtain ⟨hW, -, -, -⟩ := hT z g ph ph2 r j ε ε hz hg hph hphL hph2 hph2L hr hj hε hε hbd
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlw : SmoothR n z (lw n g ph r ε) := by
    have e : (fun y => (lw n g ph r ε y : ℂ)) = fun y => (1 / (n : ℂ)) *
        (((wgt n g ph ph2 r j ε y : ℝ) : ℂ) - (ph2 y : ℂ) - ((n : ℂ) + j) * (ph y : ℂ)) := by
      funext y
      unfold wgt
      push_cast
      field_simp
      ring
    unfold SmoothR
    rw [e]
    exact Smooth.mul _ _ _ _ (Smooth.const _ _ _)
      (Smooth.sub _ _ _ _ (Smooth.sub _ _ _ _ hW hph2) (Smooth.mul _ _ _ _ (Smooth.const _ _ _) hph))
  have hlw1 : CkR n z 1 (lw n g ph r ε) := SmoothR.ckR n z 1 _ hlw
  have hev0 : ∀ y, 0 ≤ ev n g ph r y := fun y => by unfold ev; positivity
  have hxx : ∀ y, xx n g ph r ε y = (1 + Real.log (1 + ε ^ 2)) - lw n g ph r ε y := fun y => rfl
  have htw : (fun y => (twist n g ph r ε y : ℂ)) =
      fun y => ((dualK (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε y) : ℝ) : ℂ) := by
    funext y
    rw [dualK_eq (by rw [← hxx]; linarith [(hB1 y).1])]
    unfold twist eta
    rw [hxx]
  have hevf : (fun y => (ev n g ph r y : ℂ)) =
      fun y => (((fun t => Real.exp t - ε ^ 2) (lw n g ph r ε y) : ℝ) : ℂ) := by
    funext y
    simp only
    unfold lw
    rw [Real.exp_log (by have := hev0 y; positivity)]
    push_cast
    ring
  have hnT : ∀ x ξ, ‖dbarDot n z (fun y => (twist n g ph r ε y : ℂ)) x ξ‖ =
      kap n g ph r ε x / eta n g ph r ε x * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ := by
    intro x ξ
    rw [htw, dual_dbarDot_comp_real n z _ (dualK_contDiff _) _ hlw1,
      dualK_deriv (by rw [← hxx]; exact (hB1 x).1)]
    rw [← hxx]
    congr 1
    rw [abs_of_nonneg]
    · rfl
    · have h1 := (hB1 x).1
      have h2 := (hB1 x).2.1
      unfold eta at h2
      positivity
  have hnE : ∀ x ξ, ‖dbarDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ =
      (ev n g ph r x + ε ^ 2) * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ := by
    intro x ξ
    rw [hevf, dual_dbarDot_comp_real n z _ (Real.contDiff_exp.sub contDiff_const) _ hlw1]
    congr 1
    simp only [deriv_sub_const, Real.deriv_exp]
    unfold lw
    rw [Real.exp_log (by have := hev0 x; positivity), abs_of_nonneg (by have := hev0 x; positivity)]
  refine ⟨fun x ξ => ?_, fun x ξ hx => ?_, fun x ξ hx => ?_⟩
  · rw [hnT]
    set X := xx n g ph r ε x
    set E := eta n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h1 := hT1 x ξ
    have hX : 1 ≤ X := (hB1 x).1
    have hE : 1 ≤ E := (hB1 x).2.1
    have hk : kap n g ph r ε x = 1 + 1 / X := rfl
    have hb : bfun n g ph r ε x = (X + 1) ^ 2 / ((X + 1) ^ 2 + E) := rfl
    rw [hk] at h1 ⊢
    rw [hb]
    have hid : ((1 + 1 / X) / E) ^ 2 =
        (X + 1) ^ 2 / ((X + 1) ^ 2 + E) * (1 / (X ^ 2 * E) + ((1 + 1 / X) / E) ^ 2) := by
      have : X ≠ 0 := by positivity
      have : E ≠ 0 := by positivity
      have : (X + 1) ^ 2 + E ≠ 0 := by positivity
      field_simp
      ring
    rw [mul_pow, hid, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · rw [hnT]
    set X := xx n g ph r ε x
    set E := eta n g ph r ε x
    set K := kap n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h1 := hT1 x ξ
    have h2 := hT2 x ξ hx
    have hX : 1 ≤ X := (hB1 x).1
    have hE : 1 ≤ E := (hB1 x).2.1
    have hK2 : K ≤ 2 := (hB1 x).2.2.1
    have hK1 : 1 ≤ K := by
      have : K = 1 + 1 / X := rfl
      rw [this]
      have : 0 < 1 / X := by positivity
      linarith
    have hΘ : 0 ≤ Θ := le_trans (by positivity) h1
    have hE0 : 0 < E := by linarith
    calc (K / E * D) ^ 2 = K / E ^ 2 * (K * D ^ 2) := by field_simp
      _ ≤ K / E ^ 2 * (E * Θ) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = K / E * Θ := by field_simp
      _ ≤ 2 / E * Θ := mul_le_mul_of_nonneg_right (by gcongr) hΘ
  · rw [hnE]
    set E := eta n g ph r ε x
    set K := kap n g ph r ε x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖
    set Θ := (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re
    have h2 := hT2 x ξ hx
    have hK1 : 1 ≤ K := by
      have : K = 1 + 1 / xx n g ph r ε x := rfl
      rw [this]
      have : 0 < 1 / xx n g ph r ε x := by have := (hB1 x).1; positivity
      linarith
    have hev := hev0 x
    have hQ : (ev n g ph r x + ε ^ 2) ^ 2 ≤ 4 * ε ^ 4 := by nlinarith
    have hD : D ^ 2 ≤ E * Θ := le_trans (le_mul_of_one_le_left (by positivity) hK1) h2
    calc ((ev n g ph r x + ε ^ 2) * D) ^ 2 = (ev n g ph r x + ε ^ 2) ^ 2 * D ^ 2 := by ring
      _ ≤ 4 * ε ^ 4 * D ^ 2 := mul_le_mul_of_nonneg_right hQ (by positivity)
      _ ≤ 4 * ε ^ 4 * (E * Θ) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = 4 * ε ^ 4 * E * Θ := by ring

end

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.LogLeviA
section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

noncomputable section

def llShift (c t : ℝ) : ℝ :=
  Real.smoothTransition ((t + 3 * c / 4) / (c / 4)) * (t + c) +
    (1 - Real.smoothTransition ((t + 3 * c / 4) / (c / 4)))

theorem llShift_contDiff (c : ℝ) : ContDiff ℝ ∞ (llShift c) := by
  unfold llShift
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition ((t + 3 * c / 4) / (c / 4))) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)
  exact (h1.mul (contDiff_id.add contDiff_const)).add (contDiff_const.sub h1)

theorem llShift_pos {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 < llShift c t := by
  unfold llShift
  set s := Real.smoothTransition ((t + 3 * c / 4) / (c / 4)) with hs
  have h0 : 0 ≤ s := Real.smoothTransition.nonneg _
  have h1 : s ≤ 1 := Real.smoothTransition.le_one _
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; norm_num
  · have ht : 0 < (t + 3 * c / 4) / (c / 4) := by
      by_contra hn
      have := Real.smoothTransition.zero_of_nonpos (not_lt.mp hn)
      rw [← hs] at this; linarith
    have ht' : 0 < t + 3 * c / 4 := by
      have := (div_pos_iff.mp ht)
      rcases this with h2 | h2
      · exact h2.1
      · linarith [h2.2]
    nlinarith

theorem llShift_eq {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : -c / 2 ≤ t) : llShift c t = t + c := by
  unfold llShift
  have : Real.smoothTransition ((t + 3 * c / 4) / (c / 4)) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ (by linarith)]
    linarith
  rw [this]; ring

theorem llSmoothR_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℝ) (hf : ∀ i ∈ s, SmoothR n z (f i)) :
    SmoothR n z (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    show Smooth n z (fun x => ((∑ i ∈ (∅ : Finset ι), f i x : ℝ) : ℂ))
    simpa using Smooth.const n z (0 : ℂ)
  | insert a s ha ih =>
    have h1 := SmoothR.add n z (f a) (fun x => ∑ i ∈ s, f i x)
      (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1

theorem llSmoothR_ev {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) :
    SmoothR n z (ev n g ph r) := by
  have h1 : SmoothR n z (fun x => ∑ i, ‖g i x‖ ^ 2) :=
    llSmoothR_sum n z Finset.univ (fun i x => ‖g i x‖ ^ 2)
      (fun i _ => Smooth.normSq n z (g i) (Holo.smooth n z (g i) (hg i)))
  have h2 : SmoothR n z (fun x => Real.exp (-ph x)) :=
    SmoothR.comp n z (fun t => Real.exp (-t)) (Real.contDiff_exp.comp contDiff_neg) ph hph
  have h3 : SmoothR n z (fun _ : M => (r ^ 2)⁻¹) := Smooth.const n z (((r ^ 2)⁻¹ : ℝ) : ℂ)
  have h4 := SmoothR.mul n z _ _ (SmoothR.mul n z _ _ h1 h2) h3
  have he : ev n g ph r = fun x => (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) * (r ^ 2)⁻¹ := by
    funext x; simp [ev, div_eq_mul_inv]
  rw [he]; exact h4

theorem llEv_nonneg {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (x : M) :
    0 ≤ ev n g ph r x := by
  unfold ev
  exact div_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Real.exp_pos _).le)
    (sq_nonneg _)

def llLog (c t : ℝ) : ℝ := Real.log (llShift c t)

theorem llLog_contDiff {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (llLog c) :=
  (llShift_contDiff c).log fun t => (llShift_pos hc t).ne'

theorem llLog_eventually {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : -c / 2 < t) :
    llLog c =ᶠ[𝓝 t] fun s => Real.log (s + c) := by
  filter_upwards [lt_mem_nhds ht] with s hs
  simp [llLog, llShift_eq hc hs.le]

theorem llLog_deriv {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : -c / 2 < t) :
    deriv (llLog c) t = (t + c)⁻¹ := by
  rw [(llLog_eventually hc ht).deriv_eq]
  have hpos : t + c ≠ 0 := by linarith
  have := ((hasDerivAt_id t).add_const c).log hpos
  simpa using this.deriv

theorem llLog_deriv2 {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : -c / 2 < t) :
    deriv (deriv (llLog c)) t = -((t + c) ^ 2)⁻¹ := by
  have hev : deriv (llLog c) =ᶠ[𝓝 t] fun s => (s + c)⁻¹ := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact llLog_deriv hc hs
  rw [hev.deriv_eq]
  have hpos : t + c ≠ 0 := by linarith
  have h1 := ((hasDerivAt_id t).add_const c).inv hpos
  have h2 : HasDerivAt (fun s => (s + c)⁻¹) (-((t + c) ^ 2)⁻¹) t := by
    convert h1 using 1 <;> first | rfl | (simp [div_eq_mul_inv])
  exact h2.deriv

end

end ReciprocityTheory.L2DbarEstimates.I
end

