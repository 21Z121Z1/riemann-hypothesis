import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0010
import ReciprocityTheory.L2DbarEstimates.LeviForms.FixedA

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.ApplyB
section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff Classical

theorem ap_gt_eq_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (c : M → ℂ) (W : M → Set M) (hS : (zeroSet n g).Finite) (y : M) :
    gt n z g c W y = ∑ p ∈ hS.toFinset, (W p).indicator (fun y => c p * jac n z g y) y := by
  unfold gt
  exact finsum_mem_eq_finite_toFinset_sum _ hS

theorem ap_gt_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (hS : (zeroSet n g).Finite)
    (hW : IsLocalData n g ph r W m) (x : M) (hx : ev n g ph r x < m) :
    gt n z g c W =ᶠ[𝓝 x]
      fun y => (∑ p ∈ hS.toFinset, if x ∈ W p then c p else 0) * jac n z g y := by
  have key : ∀ p ∈ hS.toFinset, ∀ᶠ y in 𝓝 x,
      (W p).indicator (fun y => c p * jac n z g y) y = (if x ∈ W p then c p else 0) * jac n z g y := by
    intro p hp
    have hpS : p ∈ zeroSet n g := hS.mem_toFinset.1 hp
    obtain ⟨hWo, -, -, hfr, -⟩ := hW.2 p hpS
    by_cases hxW : x ∈ W p
    · filter_upwards [hWo.mem_nhds hxW] with y hy
      simp [hy, hxW]
    · have hxc : x ∉ closure (W p) := by
        intro hc
        have hfx : x ∈ frontier (W p) := ⟨hc, by rwa [hWo.interior_eq]⟩
        exact absurd (hfr x hfx) (not_le.2 hx)
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
      have hyW : y ∉ W p := fun h => hy (subset_closure h)
      simp [hyW, hxW]
  filter_upwards [(Filter.eventually_all_finset _).2 key] with y hy
  rw [ap_gt_eq_sum n z g c W hS y, Finset.sum_mul]
  exact Finset.sum_congr rfl hy

theorem ap_cutExt_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (χ : ℝ → ℝ) (ε : ℝ)
    (hcont : Continuous (ev n g ph r)) (hχ0 : ∀ t, 1 ≤ t → χ t = 0) (hε : 0 < ε) (x : M)
    (hx : ε ^ 2 < ev n g ph r x) :
    cutExt n z g ph r c W χ ε =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hx] with y hy
  simp only [cutExt]
  rw [hχ0 _ ((one_le_div (by positivity)).2 hy.le)]
  simp

theorem ap_cutExt_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ)
    (ε : ℝ) (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) (x : M)
    (hx : ev n g ph r x < m) :
    cutExt n z g ph r c W χ ε =ᶠ[𝓝 x] fun y => (χ (ev n g ph r y / ε ^ 2) : ℂ) *
      ((∑ p ∈ hS.toFinset, if x ∈ W p then c p else 0) * jac n z g y) := by
  filter_upwards [ap_gt_local n z g ph r c W m hS hW x hx] with y hy
  simp only [cutExt, hy]

theorem ap_smooth_cutExt {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (hph : SmoothR n z ph) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) (hχs : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ t, 1 ≤ t → χ t = 0) (hε : 0 < ε) (hm : ε ^ 2 < m) :
    Smooth n z (cutExt n z g ph r c W χ ε) := by
  have hev := ap_smoothR_ev n z g hg ph hph r
  have hcont := ap_cont_of_smoothR n z hz _ hev
  apply ap_smooth_of_local
  intro x
  by_cases hx : ev n g ph r x < m
  · refine ⟨_, ?_, ap_cutExt_local n z g ph r c W m χ ε hS hW x hx⟩
    have hk : SmoothR n z (fun y => χ (ev n g ph r y / ε ^ 2)) :=
      SmoothR.comp n z (fun t => χ (t / ε ^ 2)) (hχs.comp (contDiff_id.div_const _)) _ hev
    exact Smooth.mul n z _ _ hk (Holo.smooth n z _ (Holo.mul n z _ _ (Holo.const n z _)
      (ap_holo_jac n z g hg)))
  · exact ⟨fun _ => 0, Smooth.const n z 0,
      ap_cutExt_zero n z g ph r c W χ ε hcont hχ0 hε x (by linarith [not_lt.1 hx])⟩

theorem ap_hasDerivAt_chi (χ : ℝ → ℝ) (hχs : ContDiff ℝ ∞ χ) (ε t : ℝ) :
    HasDerivAt (fun t => χ (t / ε ^ 2)) (deriv χ (t / ε ^ 2) * (1 / ε ^ 2)) t := by
  have h1 : HasDerivAt χ (deriv χ (t / ε ^ 2)) (t / ε ^ 2) :=
    ((hχs.differentiable (by simp)) _).hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => t / ε ^ 2) (1 / ε ^ 2) t := (hasDerivAt_id t).div_const _
  exact h1.comp t h2

theorem ap_dbar_cutExt {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (hph : SmoothR n z ph) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) (hχs : ContDiff ℝ ∞ χ)
    (x : M) (hx : ev n g ph r x < m) (ξ : Fin n → ℂ) :
    dbarDot n z (cutExt n z g ph r c W χ ε) x ξ =
      ((deriv χ (ev n g ph r x / ε ^ 2) * (1 / ε ^ 2) : ℝ) : ℂ) * gt n z g c W x *
        dbarDot n z (fun y => (ev n g ph r y : ℂ)) x ξ := by
  have hev := ap_smoothR_ev n z g hg ph hph r
  have hloc := ap_cutExt_local n z g ph r c W m χ ε hS hW x hx
  have hgx := (ap_gt_local n z g ph r c W m hS hW x hx).self_of_nhds
  set C := ∑ p ∈ hS.toFinset, if x ∈ W p then c p else 0
  have hJ : Holo n z (fun y => C * jac n z g y) :=
    Holo.mul n z _ _ (Holo.const n z _) (ap_holo_jac n z g hg)
  have hk : SmoothR n z (fun y => χ (ev n g ph r y / ε ^ 2)) :=
    SmoothR.comp n z (fun t => χ (t / ε ^ 2)) (hχs.comp (contDiff_id.div_const _)) _ hev
  have hderiv : deriv (fun t => χ (t / ε ^ 2)) (ev n g ph r x) =
      deriv χ (ev n g ph r x / ε ^ 2) * (1 / ε ^ 2) := (ap_hasDerivAt_chi χ hχs ε _).deriv
  unfold dbarDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ap_db_congr n z hz j _ _ x hloc,
    db_mul n z _ _ (Smooth.ck n z 1 _ hk) (Smooth.ck n z 1 _ (Holo.smooth n z _ hJ)) j x,
    Holo.db_eq_zero n z _ hJ j x,
    db_comp_real n z (fun t => χ (t / ε ^ 2)) (hχs.comp (contDiff_id.div_const _)) _
      (SmoothR.ckR n z 1 _ hev) j x, hderiv, hgx]
  ring

theorem ap_measurable_gt {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
    (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ)
    (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) :
    Measurable (gt n z g c W) := by
  have hJ : Continuous (jac n z g) :=
    Smooth.continuous n z hz _ (Holo.smooth n z _ (ap_holo_jac n z g hg))
  have h : gt n z g c W = fun y => ∑ p ∈ hS.toFinset, (W p).indicator (fun y => c p * jac n z g y) y :=
    funext (ap_gt_eq_sum n z g c W hS)
  rw [h]
  apply Finset.measurable_sum
  intro p hp
  exact (measurable_const.mul hJ.measurable).indicator
    (hW.2 p (hS.mem_toFinset.1 hp)).1.measurableSet

theorem ap_cutExt_support {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (χ : ℝ → ℝ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (x : M) (hx : x ∉ ⋃ p ∈ hS.toFinset, closure (W p)) :
    cutExt n z g ph r c W χ ε x = 0 := by
  simp only [cutExt, ap_gt_eq_sum n z g c W hS x]
  rw [Finset.sum_eq_zero, mul_zero]
  intro p hp
  have : x ∉ W p := fun h => hx (Set.mem_biUnion hp (subset_closure h))
  simp [this]

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.EvLevi
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff ComplexConjugate

theorem evLevi (n : ℕ) (M : Type u) [TopologicalSpace M] : EvLeviStatement n M := by
  intro z g ph r _ hg hph hr x ξ
  have hS : SmoothR n z (fun y => ∑ i, ‖g i y‖ ^ 2) := evl_smoothR_sumSq n z Finset.univ g hg
  have hE : SmoothR n z (fun y => Real.exp (-ph y)) := SmoothR.comp n z _ contDiff_exp_neg ph hph
  have hSE : SmoothR n z (fun y => (∑ i, ‖g i y‖ ^ 2) * Real.exp (-ph y)) :=
    SmoothR.mul n z _ _ hS hE
  have hev : ev n g ph r = fun y => (r ^ 2)⁻¹ * ((∑ i, ‖g i y‖ ^ 2) * Real.exp (-ph y)) := by
    funext y; unfold ev; ring
  have hvx : ev n g ph r x = (r ^ 2)⁻¹ * ((∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x)) := by
    rw [hev]
  have hLev : Levi n z (ev n g ph r) x ξ = (((r ^ 2)⁻¹ : ℝ) : ℂ) *
      Levi n z (fun y => (∑ i, ‖g i y‖ ^ 2) * Real.exp (-ph y)) x ξ := by
    rw [hev]; exact levi_const_mul n z _ _ (SmoothR.ckR n z 2 _ hSE) x ξ
  have hLSE : Levi n z (fun y => (∑ i, ‖g i y‖ ^ 2) * Real.exp (-ph y)) x ξ =
      Levi n z (fun y => ∑ i, ‖g i y‖ ^ 2) x ξ * ((Real.exp (-ph x) : ℝ) : ℂ) +
        ((∑ i, ‖g i x‖ ^ 2 : ℝ) : ℂ) * Levi n z (fun y => Real.exp (-ph y)) x ξ +
        conj (dDot n z (fun y => ((∑ i, ‖g i y‖ ^ 2 : ℝ) : ℂ)) x ξ) *
          dDot n z (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) x ξ +
        dDot n z (fun y => ((∑ i, ‖g i y‖ ^ 2 : ℝ) : ℂ)) x ξ *
          conj (dDot n z (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) x ξ) :=
    evl_levi_mul n z _ _ (SmoothR.ckR n z 2 _ hS) (SmoothR.ckR n z 2 _ hE) x ξ
  rw [evl_levi_sumSq n z Finset.univ g hg x ξ, evl_levi_expNeg n z ph hph x ξ,
    evl_dDot_sumSq n z Finset.univ g hg x ξ, evl_dDot_expNeg n z ph hph x ξ] at hLSE
  have hdev : dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ = (((r ^ 2)⁻¹ : ℝ) : ℂ) *
      ((∑ i, conj (g i x) * dDot n z (g i) x ξ) * ((Real.exp (-ph x) : ℝ) : ℂ) +
        ((∑ i, ‖g i x‖ ^ 2 : ℝ) : ℂ) *
          (-((Real.exp (-ph x) : ℝ) : ℂ) * dDot n z (fun y => (ph y : ℂ)) x ξ)) := by
    have hf : (fun y => (ev n g ph r y : ℂ)) = fun y => (((r ^ 2)⁻¹ : ℝ) : ℂ) *
        (((∑ i, ‖g i y‖ ^ 2 : ℝ) : ℂ) * ((Real.exp (-ph y) : ℝ) : ℂ)) := by
      funext y; rw [hev]; simp only [Complex.ofReal_mul]
    rw [hf, evl_dDot_const_mul n z _ _ (Ck.mul n z 1 _ _ (SmoothR.ckR n z 1 _ hS)
      (SmoothR.ckR n z 1 _ hE)) x ξ, evl_dDot_mul n z _ _ (SmoothR.ckR n z 1 _ hS)
      (SmoothR.ckR n z 1 _ hE) x ξ, evl_dDot_sumSq n z Finset.univ g hg x ξ,
      evl_dDot_expNeg n z ph hph x ξ]
  have hCS := evl_cs Finset.univ (fun i => g i x) (fun i => dDot n z (g i) x ξ)
  generalize hP : ∑ i, conj (g i x) * dDot n z (g i) x ξ = P at hLSE hdev hCS
  generalize hb : dDot n z (fun y => (ph y : ℂ)) x ξ = b at hLSE hdev
  generalize hL : Levi n z ph x ξ = Lp at hLSE ⊢
  generalize hSx : ∑ i, ‖g i x‖ ^ 2 = Sx at hLSE hdev hCS hvx
  generalize hQ : ∑ i, ‖dDot n z (g i) x ξ‖ ^ 2 = Q at hLSE hCS
  have hSx0 : 0 ≤ Sx := hSx ▸ Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQ0 : 0 ≤ Q := hQ ▸ Finset.sum_nonneg fun i _ => sq_nonneg _
  have hN : ‖dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ ^ 2 =
      ((r ^ 2)⁻¹) ^ 2 * Real.exp (-ph x) ^ 2 *
        ((P.re - Sx * b.re) ^ 2 + (P.im - Sx * b.im) ^ 2) := by
    rw [hdev, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hR : (Levi n z (ev n g ph r) x ξ).re = (r ^ 2)⁻¹ * (Q * Real.exp (-ph x) +
      Sx * (Real.exp (-ph x) * (b.re ^ 2 + b.im ^ 2 - Lp.re)) -
      2 * Real.exp (-ph x) * (P.re * b.re + P.im * b.im)) := by
    rw [hLev, hLSE]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.neg_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, map_mul, map_neg, Complex.conj_ofReal]
    ring
  rw [hN, hR, hvx]
  rw [Complex.sq_norm, Complex.normSq_apply] at hCS
  exact evl_alg _ _ Sx Q P.re P.im b.re b.im Lp.re (by positivity) (Real.exp_pos _) hSx0 hQ0
    (by nlinarith [hCS])

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.FixedB
section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_lintegral_ball_translate {n : ℕ} (y₀ : V n) (ρ : ℝ) (Φ : V n → ℝ≥0∞) :
    ∫⁻ y in ball (0 : V n) ρ, Φ (y₀ + y) = ∫⁻ y in ball y₀ ρ, Φ y := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  have h : ∀ y, (ball (0 : V n) ρ).indicator (fun y => Φ (y₀ + y)) y =
      (ball y₀ ρ).indicator Φ (y₀ + y) := fun y => by
    simp [Set.indicator, mem_ball, dist_eq_norm]
  simp_rw [h]
  exact lintegral_add_left_eq_self ((ball y₀ ρ).indicator Φ) y₀

theorem fx_tendsto_zero_of_weighted {M : Type*} [TopologicalSpace M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (hn : 1 ≤ n) (hV : VanishStatement n)
    (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) (p : M) (hp : p ∈ e.source) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ball (z p) ρ ⊆ e.target) (c₀ C' Cb : ℝ) (hc₀ : 0 < c₀) (hC' : 0 < C')
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝[>] 0)) (u : ℕ → M → ℂ) (w : ℕ → M → ℝ)
    (hu : ∀ k, Measurable (u k)) (hw : ∀ k, Measurable (w k))
    (hdiff : ∀ k, DifferentiableOn ℂ (fun y => u k (e.symm y)) (ball (z p) ρ))
    (hlow : ∀ k, ∀ y ∈ ball (z p) ρ,
      c₀ * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ)) ≤ w k (e.symm y))
    (hint : ∀ k, ∫⁻ x, ENNReal.ofReal (‖u k x‖ ^ 2 * w k x) ∂vol n z ≤ ENNReal.ofReal Cb) :
    Tendsto (fun k => u k p) atTop (𝓝 0) := by
  have hzp : e.symm (z p) = p := by rw [he hp]; exact e.left_inv hp
  have key := hV hn ρ C' (c₀⁻¹ * Cb) δ (fun k y => u k (e.symm (z p + y))) hρ hC' hδ ?_ ?_
  · simpa [hzp] using key
  · intro k
    refine (hdiff k).comp ((differentiableOn_const _).add differentiableOn_id) fun y hy => ?_
    simpa [mem_ball, dist_eq_norm] using hy
  · intro k
    have h1 := fx_lintegral_ball_translate (z p) ρ
      (fun y => ENNReal.ofReal (‖u k (e.symm y)‖ ^ 2 * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ))))
    simp only [add_sub_cancel_left] at h1
    rw [h1]
    set f' : M → ℝ≥0∞ := e.source.indicator fun x => ENNReal.ofReal (‖u k x‖ ^ 2 * w k x)
      with hf'
    have hf'm : Measurable f' :=
      (ENNReal.measurable_ofReal.comp (((hu k).norm.pow_const 2).mul (hw k))).indicator
        e.open_source.measurableSet
    have hchart := lintegral_vol_chart n z hz e he f' hf'm
      (fun x hx => by simp [hf', hx])
    calc ∫⁻ y in ball (z p) ρ,
          ENNReal.ofReal (‖u k (e.symm y)‖ ^ 2 * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ)))
        ≤ ∫⁻ y in ball (z p) ρ, ENNReal.ofReal c₀⁻¹ * f' (e.symm y) := by
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          have hs : e.symm y ∈ e.source := e.map_target (hball hy)
          rw [hf', Set.indicator_of_mem hs, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc₀.le)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 := hlow k y hy
          have h3 : (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ)) ≤ c₀⁻¹ * w k (e.symm y) := by
            rw [le_inv_mul_iff₀ hc₀]; exact h2
          calc ‖u k (e.symm y)‖ ^ 2 * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ))
              ≤ ‖u k (e.symm y)‖ ^ 2 * (c₀⁻¹ * w k (e.symm y)) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = _ := by ring
      _ = ENNReal.ofReal c₀⁻¹ * ∫⁻ y in ball (z p) ρ, f' (e.symm y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c₀⁻¹ * ∫⁻ y in e.target, f' (e.symm y) := by
          gcongr
      _ = ENNReal.ofReal c₀⁻¹ * ∫⁻ x, f' x ∂vol n z := by rw [hchart]
      _ ≤ ENNReal.ofReal c₀⁻¹ * ENNReal.ofReal Cb := by
          gcongr
          refine (lintegral_mono fun x => ?_).trans (hint k)
          exact Set.indicator_le_self _ _ x
      _ = ENNReal.ofReal (c₀⁻¹ * Cb) := (ENNReal.ofReal_mul (inv_nonneg.mpr hc₀.le)).symm

theorem fx_exists_ball_bounds {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph ph2 : M → ℝ)
    (hph : SmoothR n z ph) (hph2 : SmoothR n z ph2) (r : ℝ) (hr : 0 < r) (j : ℕ) (ε : ℝ)
    (hε : 0 < ε) (p : M) (hp : p ∈ zeroSet n g) (U : Set M) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source ∧
      ∃ ρ > 0, ∃ C1 > 0, ∃ A : ℝ, ball (z p) ρ ⊆ e.target ∧ ∀ y ∈ ball (z p) ρ,
        e.symm y ∈ U ∧ ev n g ph r (e.symm y) ≤ ε ^ 2 / 2 ∧
        ev n g ph r (e.symm y) ≤ C1 * ‖y - z p‖ ^ 2 ∧
        ph2 (e.symm y) + ((n : ℝ) + j) * ph (e.symm y) ≤ A := by
  obtain ⟨e, he, hpe⟩ := exists_chart n z hz p
  have hzp : z p ∈ e.target := by rw [he hpe]; exact e.map_source hpe
  have hsp : e.symm (z p) = p := by rw [he hpe]; exact e.left_inv hpe
  have hcs : ContinuousAt e.symm (z p) := e.continuousAt_symm hzp
  have hre : ∀ f : M → ℝ, SmoothR n z f → Continuous f := fun f hf =>
    (Complex.continuous_re.comp (Smooth.continuous n z hz _ hf)).congr fun x => by simp
  have hev0 : ev n g ph r p = 0 := fx_ev_eq_zero n g ph r p hp

  have hlip : ∀ i, ∃ c : ℝ, ∀ᶠ y in 𝓝 (z p), ‖g i (e.symm y)‖ ≤ c * ‖y - z p‖ := by
    intro i
    have hd : DifferentiableAt ℂ (fun y => g i (e.symm y)) (z p) :=
      (hg i e he).differentiableAt (e.open_target.mem_nhds hzp)
    obtain ⟨c, hc⟩ := hd.hasFDerivAt.isBigO_sub.bound
    refine ⟨c, hc.mono fun y hy => ?_⟩
    have h0 : g i (e.symm (z p)) = 0 := by rw [hsp]; exact hp i
    simpa [h0] using hy
  choose c hc using hlip
  have h1 : ∀ᶠ y in 𝓝 (z p), y ∈ e.target := e.open_target.mem_nhds hzp
  have h2 : ∀ᶠ y in 𝓝 (z p), e.symm y ∈ U := hcs.preimage_mem_nhds (by rw [hsp]; exact hU.mem_nhds hpU)
  have hevc : ContinuousAt (fun y => ev n g ph r (e.symm y)) (z p) :=
    (fx_continuous_ev n z hz g hg ph hph r).continuousAt.comp hcs
  have h3 : ∀ᶠ y in 𝓝 (z p), ev n g ph r (e.symm y) < ε ^ 2 / 2 := by
    refine hevc.eventually (gt_mem_nhds ?_)
    show ev n g ph r (e.symm (z p)) < _
    rw [hsp, hev0]; positivity
  have hψc : ContinuousAt (fun y => ph2 (e.symm y) + ((n : ℝ) + j) * ph (e.symm y)) (z p) :=
    (((hre _ hph2).add (continuous_const.mul (hre _ hph))).continuousAt).comp hcs
  have h4 : ∀ᶠ y in 𝓝 (z p), ph2 (e.symm y) + ((n : ℝ) + j) * ph (e.symm y) <
      ph2 p + ((n : ℝ) + j) * ph p + 1 := by
    refine hψc.eventually (gt_mem_nhds ?_)
    simp only [hsp]; linarith
  have hxc : ContinuousAt (fun y => Real.exp (-ph (e.symm y))) (z p) :=
    ((Real.continuous_exp.comp (hre _ hph).neg).continuousAt).comp hcs
  have h5 : ∀ᶠ y in 𝓝 (z p), Real.exp (-ph (e.symm y)) < Real.exp (-ph p) + 1 := by
    refine hxc.eventually (gt_mem_nhds ?_)
    simp only [hsp]; linarith
  have h6 : ∀ᶠ y in 𝓝 (z p), ∀ i, ‖g i (e.symm y)‖ ≤ c i * ‖y - z p‖ :=
    Filter.eventually_all.2 hc
  obtain ⟨ρ, hρ, hall⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and (h3.and (h4.and (h5.and h6)))))
  set C1 : ℝ := (∑ i, c i ^ 2) * (Real.exp (-ph p) + 1) / r ^ 2 + 1 with hC1
  have hC1pos : 0 < C1 := by positivity
  refine ⟨e, he, hpe, ρ, hρ, C1, hC1pos, ph2 p + ((n : ℝ) + j) * ph p + 1,
    fun y hy => (hall y hy).1, fun y hy => ?_⟩
  obtain ⟨-, hU', h3', h4', h5', h6'⟩ := hall y hy
  refine ⟨hU', h3'.le, ?_, h4'.le⟩
  have hs : ∑ i, ‖g i (e.symm y)‖ ^ 2 ≤ (∑ i, c i ^ 2) * ‖y - z p‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h6' i) 2
  have hr2 : 0 < r ^ 2 := by positivity
  unfold ev
  rw [div_le_iff₀ hr2]
  have hsum0 : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc (∑ i, ‖g i (e.symm y)‖ ^ 2) * Real.exp (-ph (e.symm y))
      ≤ ((∑ i, c i ^ 2) * ‖y - z p‖ ^ 2) * (Real.exp (-ph p) + 1) :=
        mul_le_mul hs h5'.le (Real.exp_pos _).le (by positivity)
    _ ≤ C1 * ‖y - z p‖ ^ 2 * r ^ 2 := by
        rw [hC1, add_mul, add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_cancel_right₀ _ hr2.ne']
        nlinarith [sq_nonneg ‖y - z p‖, sq_nonneg r, mul_nonneg hsum0 (sq_nonneg ‖y - z p‖)]

end

end ReciprocityTheory.L2DbarEstimates.I
end

