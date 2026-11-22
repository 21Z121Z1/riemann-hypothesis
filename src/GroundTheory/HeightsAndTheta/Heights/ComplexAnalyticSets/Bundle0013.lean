import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChangeOfVariablesDegree
section
set_option maxSynthPendingDepth 1

open scoped ContDiff

open MeasureTheory Metric

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace ChangeOfVariablesDegree

theorem continuous_det_fderiv {n : ℕ} (φ : (Fin n → ℝ) → Fin n → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Continuous fun x => (fderiv ℝ φ x).det := by
  have : (fun x => (fderiv ℝ φ x).det) = fun x => detCML (entriesCLM (fderiv ℝ φ x)) := by
    funext x; rw [det_fderiv_eq_det_jacobian]; rfl
  rw [this]
  exact detCML.cont.comp (entriesCLM.continuous.comp (hφ.continuous_fderiv (by simp)))

theorem hasCompactSupport_comp_sub {n : ℕ} (φ : (Fin n → ℝ) → Fin n → ℝ) (C : ℝ)
    (hC : ∀ x, ‖φ x - x‖ ≤ C) (g : (Fin n → ℝ) → ℝ) (hgc : HasCompactSupport g)
    (y₀ : Fin n → ℝ) : HasCompactSupport fun x => g (φ x - y₀) := by
  obtain ⟨r, hr⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (r + ‖y₀‖ + C))
    fun x hx => ?_
  by_contra hne
  have h1 := hr (subset_tsupport _ hne)
  rw [mem_closedBall_zero_iff] at h1
  apply hx
  rw [mem_closedBall_zero_iff]
  have h2 : ‖x‖ ≤ ‖φ x - y₀‖ + ‖y₀‖ + ‖φ x - x‖ := by
    calc ‖x‖ = ‖(φ x - y₀) + y₀ - (φ x - x)‖ := by congr 1; abel
      _ ≤ ‖(φ x - y₀) + y₀‖ + ‖φ x - x‖ := norm_sub_le _ _
      _ ≤ ‖φ x - y₀‖ + ‖y₀‖ + ‖φ x - x‖ := by gcongr; exact norm_add_le _ _
  linarith [hC x]

theorem clm_apply_eq_sum {n : ℕ} (T : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    T v = ∑ k, v k * T (Pi.single k 1) := by
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin n → ℝ) := by
    ext m; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul]

variable {m : ℕ}

theorem integral_fderiv_comp_mul_det_eq_zero (φ : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hu : HasCompactSupport fun x => φ x - x)
    (g : (Fin (m + 1) → ℝ) → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ x, fderiv ℝ g (φ x) (Pi.single 0 1) * (fderiv ℝ φ x).det = 0 := by
  obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
  set H : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ := fun x => Function.update (φ x) 0 (g (φ x))
    with hH
  have hH0 : (fun x => H x 0) = fun x => g (φ x) := by
    funext x; simp [hH]
  have hHk : ∀ k, k ≠ 0 → (fun x => H x k) = fun x => φ x k := by
    intro k hk; funext x; simp [hH, hk]
  have hHs : ContDiff ℝ ∞ H := by
    refine contDiff_pi.2 fun k => ?_
    by_cases hk : k = 0
    · subst hk; rw [hH0]; exact hg.comp hφ
    · rw [hHk k hk]; exact (contDiff_apply ℝ ℝ k).comp hφ
  have hHc : HasCompactSupport fun x => H x 0 := by
    rw [hH0]
    simpa using hasCompactSupport_comp_sub φ C hC g hgc 0
  have hdet : ∀ x, (fderiv ℝ H x).det =
      fderiv ℝ g (φ x) (Pi.single 0 1) * (fderiv ℝ φ x).det := by
    intro x
    have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
    have hgd : DifferentiableAt ℝ g (φ x) := (hg.differentiable (by simp)) (φ x)
    set c : Fin (m + 1) → ℝ := fun k => fderiv ℝ g (φ x) (Pi.single k 1) with hc
    have hJ : Matrix.of (jacobian H x) = (Matrix.of (jacobian φ x)).updateRow 0
        (∑ k, c k • (Matrix.of (jacobian φ x)) k) := by
      ext r l
      rw [Matrix.of_apply, jacobian_eq_fderiv_apply H x ((hHs.differentiable (by simp)) x)]
      by_cases hr : r = 0
      · subst hr
        rw [hH0, Matrix.updateRow_self]
        have : fderiv ℝ (fun y => g (φ y)) x = (fderiv ℝ g (φ x)).comp (fderiv ℝ φ x) :=
          fderiv_comp x hgd hφd
        rw [this, ContinuousLinearMap.comp_apply, clm_apply_eq_sum]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, hc]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [jacobian, mul_comm]
      · rw [hHk r hr, Matrix.updateRow_ne hr, Matrix.of_apply,
          jacobian_eq_fderiv_apply φ x hφd]
    rw [det_fderiv_eq_det_jacobian, hJ, Matrix.det_updateRow_sum, det_fderiv_eq_det_jacobian,
      smul_eq_mul]
  simp_rw [← hdet]
  exact integral_det_fderiv_eq_zero H hHs 0 hHc

theorem integral_comp_sub_mul_det_eq (φ : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hu : HasCompactSupport fun x => φ x - x)
    (f : (Fin (m + 1) → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (s : ℝ) :
    ∫ x, f (φ x - s • (Pi.single 0 1 : Fin (m + 1) → ℝ)) * (fderiv ℝ φ x).det =
      ∫ x, f (φ x) * (fderiv ℝ φ x).det := by
  set e : Fin (m + 1) → ℝ := Pi.single 0 1 with he
  obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
  have hC' : ∀ x, ‖φ x - x‖ ≤ C := hC
  obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨Cf, hCf⟩ := ((hf.continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := e))).bounded_above_of_compact_support (hfc.fderiv_apply (𝕜 := ℝ) e)
  have hdc := continuous_det_fderiv φ hφ
  set Φ : ℝ → ℝ := fun s => ∫ x, f (φ x - s • e) * (fderiv ℝ φ x).det with hΦ
  have hderiv : ∀ s₀, HasDerivAt Φ 0 s₀ := by
    intro s₀
    set R := r + C + (|s₀| + 1) * ‖e‖ with hR
    set F' : ℝ → (Fin (m + 1) → ℝ) → ℝ :=
      fun s x => -(fderiv ℝ f (φ x - s • e) e) * (fderiv ℝ φ x).det with hF'
    have hbound : ∀ᵐ x ∂(volume : Measure (Fin (m + 1) → ℝ)), ∀ s ∈ ball s₀ 1,
        ‖F' s x‖ ≤ (closedBall (0 : Fin (m + 1) → ℝ) R).indicator
          (fun x => Cf * |(fderiv ℝ φ x).det|) x := by
      refine Filter.Eventually.of_forall fun x s hs => ?_
      by_cases hx : x ∈ closedBall (0 : Fin (m + 1) → ℝ) R
      · rw [Set.indicator_of_mem hx]
        simp only [hF', norm_mul, norm_neg, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hCf (φ x - s • e))
          (abs_nonneg _)
      · rw [Set.indicator_of_notMem hx]
        have hnot : φ x - s • e ∉ tsupport f := by
          intro hmem
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          apply hx
          rw [mem_closedBall_zero_iff]
          have hs' : |s| ≤ |s₀| + 1 := by
            rw [mem_ball, Real.dist_eq] at hs
            have := abs_sub_abs_le_abs_sub s s₀
            linarith
          have hse : ‖s • e‖ ≤ (|s₀| + 1) * ‖e‖ := by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right hs' (norm_nonneg _)
          have h2 : ‖x‖ ≤ ‖φ x - s • e‖ + ‖s • e‖ + ‖φ x - x‖ := by
            calc ‖x‖ = ‖(φ x - s • e) + s • e - (φ x - x)‖ := by congr 1; abel
              _ ≤ ‖(φ x - s • e) + s • e‖ + ‖φ x - x‖ := norm_sub_le _ _
              _ ≤ ‖φ x - s • e‖ + ‖s • e‖ + ‖φ x - x‖ := by gcongr; exact norm_add_le _ _
          linarith [hC' x]
        have h0 : fderiv ℝ f (φ x - s • e) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hnot (tsupport_fderiv_subset ℝ h)
        simp [hF', h0]
    have hdiff : ∀ᵐ x ∂(volume : Measure (Fin (m + 1) → ℝ)), ∀ s ∈ ball s₀ 1,
        HasDerivAt (fun s => f (φ x - s • e) * (fderiv ℝ φ x).det) (F' s x) s := by
      refine Filter.Eventually.of_forall fun x s _ => ?_
      have hl : HasDerivAt (fun s : ℝ => φ x - s • e) (-e) s := by
        simpa using ((hasDerivAt_id s).smul_const e).const_sub (φ x)
      have := (((hf.differentiable (by simp)) (φ x - s • e)).hasFDerivAt.comp_hasDerivAt s
        hl).mul_const ((fderiv ℝ φ x).det)
      refine this.congr_deriv ?_
      simp only [hF', map_neg, neg_mul]
    have hcF : ∀ s : ℝ, Continuous fun x => f (φ x - s • e) * (fderiv ℝ φ x).det := fun s =>
      (hf.continuous.comp (hφ.continuous.sub continuous_const)).mul hdc
    have hcF' : Continuous (F' s₀) :=
      (((hf.continuous_fderiv (by simp)).comp (hφ.continuous.sub continuous_const)).clm_apply
        continuous_const).neg.mul hdc
    have hcB : Continuous fun x => Cf * |(fderiv ℝ φ x).det| := continuous_const.mul hdc.abs
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun s x => f (φ x - s • e) * (fderiv ℝ φ x).det) (F' := F') (x₀ := s₀)
      (bound := (closedBall (0 : Fin (m + 1) → ℝ) R).indicator
        fun x => Cf * |(fderiv ℝ φ x).det|)
      (ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => (hcF s).aestronglyMeasurable)
      ((hcF s₀).integrable_of_hasCompactSupport
        (hasCompactSupport_comp_sub φ C hC' f hfc _).mul_right)
      hcF'.aestronglyMeasurable
      hbound
      ((hcB.continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)).integrable_indicator measurableSet_closedBall)
      hdiff
    have h0 : ∫ x, F' s₀ x = 0 := by
      simp only [hF', neg_mul, integral_neg]
      have hg := integral_fderiv_comp_mul_det_eq_zero φ hφ hu (fun y => f (y - s₀ • e))
        (hf.comp (contDiff_id.sub contDiff_const))
        (hfc.comp_homeomorph (Homeomorph.subRight (s₀ • e)))
      simp only [fderiv_comp_sub] at hg
      rw [hg, neg_zero]
    rw [← h0]
    exact key.2
  have hΦd : Differentiable ℝ Φ := fun s => (hderiv s).differentiableAt
  have := is_const_of_deriv_eq_zero hΦd (fun s => (hderiv s).deriv) s 0
  simpa [hΦ] using this

end ChangeOfVariablesDegree

theorem ChangeOfVariablesDegree.proof : ChangeOfVariablesDegree.Statement := by
  intro n φ hφ hu f hf hfc
  cases n with
  | zero =>
    have hid : φ = id := funext fun x => Subsingleton.elim _ _
    subst hid
    simp only [fderiv_id, id_eq, ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
      LinearMap.det_id, mul_one]
  | succ m =>
    set e : Fin (m + 1) → ℝ := Pi.single 0 1 with he
    obtain ⟨C, hC⟩ := (hφ.continuous.sub continuous_id).bounded_above_of_compact_support hu
    have hC' : ∀ x, ‖φ x - x‖ ≤ C := hC
    obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall 0
    obtain ⟨ru, hru⟩ := hu.isCompact.isBounded.subset_closedBall 0
    have he1 : ‖e‖ = 1 := by simp [he, Pi.norm_single]
    set R := |r| + |ru| + |C| + 1 with hR
    have hpt : ∀ x, f (φ x - R • e) * (fderiv ℝ φ x).det = f (x - R • e) := by
      intro x
      have hRe : ‖R • e‖ = R := by
        rw [norm_smul, he1, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
      by_cases hx : x ∈ tsupport fun x => φ x - x
      · have hx' := hru hx
        rw [mem_closedBall_zero_iff] at hx'
        have hf1 : f (φ x - R • e) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          have h2 : ‖R • e‖ ≤ ‖φ x - R • e‖ + ‖φ x - x‖ + ‖x‖ := by
            calc ‖R • e‖ = ‖-(φ x - R • e) + (φ x - x) + x‖ := by congr 1; abel
              _ ≤ ‖-(φ x - R • e) + (φ x - x)‖ + ‖x‖ := norm_add_le _ _
              _ ≤ ‖φ x - R • e‖ + ‖φ x - x‖ + ‖x‖ := by
                gcongr; exact (norm_add_le _ _).trans (by rw [norm_neg])
          rw [hRe] at h2
          linarith [hC' x, le_abs_self r, le_abs_self ru, le_abs_self C]
        have hf2 : f (x - R • e) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
          have h1 := hr hmem
          rw [mem_closedBall_zero_iff] at h1
          have h2 : ‖R • e‖ ≤ ‖x - R • e‖ + ‖x‖ := by
            calc ‖R • e‖ = ‖-(x - R • e) + x‖ := by congr 1; abel
              _ ≤ ‖-(x - R • e)‖ + ‖x‖ := norm_add_le _ _
              _ = ‖x - R • e‖ + ‖x‖ := by rw [norm_neg]
          rw [hRe] at h2
          have := abs_nonneg C
          linarith [le_abs_self r, le_abs_self ru]
        rw [hf1, hf2, zero_mul]
      · rw [notMem_tsupport_iff_eventuallyEq] at hx
        have hev : φ =ᶠ[nhds x] id := hx.mono fun y hy => by simpa [sub_eq_zero] using hy
        have hfd : fderiv ℝ φ x = ContinuousLinearMap.id ℝ _ := by
          rw [hev.fderiv_eq, fderiv_id]
        have hφx : φ x = x := hev.self_of_nhds
        rw [hfd, hφx, ContinuousLinearMap.det,
          ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one]
    calc ∫ x, f (φ x) * (fderiv ℝ φ x).det
        = ∫ x, f (φ x - R • e) * (fderiv ℝ φ x).det :=
          (ChangeOfVariablesDegree.integral_comp_sub_mul_det_eq φ hφ hu f hf hfc R).symm
      _ = ∫ x, f (x - R • e) := by simp_rw [hpt]
      _ = ∫ x, f x := integral_sub_right_eq_self f (R • e)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCircleArgumentPrinciple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Complex Real

noncomputable section

theorem CircleArgumentPrinciple.differentiable_prod_sub (Z : Multiset ℂ) :
    Differentiable ℂ fun s : ℂ => (Z.map fun a => s - a).prod := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a Z ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (differentiable_id.sub_const a).mul ih

theorem CircleArgumentPrinciple.integral_prod_mul {O : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hO : IsOpen O)
    (hball : closedBall c r ⊆ O) {u φ : ℂ → ℂ} (hu : DifferentiableOn ℂ u O)
    (hu0 : ∀ s ∈ closedBall c r, u s ≠ 0) (hφ : DifferentiableOn ℂ φ O) (Z : Multiset ℂ)
    (hZ : ∀ a ∈ Z, a ∈ ball c r) :
    (2 * π * I)⁻¹ * (∮ s in C(c, r), φ s * deriv (fun s => (Z.map fun a => s - a).prod * u s) s /
      ((Z.map fun a => s - a).prod * u s)) = (Z.map φ).sum := by
  induction Z using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, one_mul, Multiset.sum_zero]
    have hd : ∀ z ∈ closedBall c r, DifferentiableAt ℂ (fun s => φ s * deriv u s / u s) z := by
      intro z hz
      have hzO : O ∈ 𝓝 z := hO.mem_nhds (hball hz)
      exact ((hφ.differentiableAt hzO).mul ((hu.deriv hO).differentiableAt hzO)).div
        (hu.differentiableAt hzO) (hu0 z hz)
    rw [circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
      (fun z hz => hd z (ball_subset_closedBall hz.1)), mul_zero]
  | cons a Z ih =>
    have hZ' : ∀ b ∈ Z, b ∈ ball c r := fun b hb => hZ b (Multiset.mem_cons_of_mem hb)
    have ha : a ∈ ball c r := hZ a (Multiset.mem_cons_self a Z)
    set F : ℂ → ℂ := fun s => (Z.map fun b => s - b).prod * u s with hFdef
    have hF : DifferentiableOn ℂ F O :=
      ((CircleArgumentPrinciple.differentiable_prod_sub Z).differentiableOn).mul hu

    have hne : ∀ s ∈ sphere c r, ∀ b ∈ a ::ₘ Z, s - b ≠ 0 := by
      intro s hs b hb h0
      have hb' := hZ b hb
      obtain rfl := sub_eq_zero.1 h0
      rw [mem_ball] at hb'
      rw [mem_sphere] at hs
      linarith
    have hFne : ∀ s ∈ sphere c r, F s ≠ 0 := by
      intro s hs
      refine mul_ne_zero (Multiset.prod_ne_zero ?_) (hu0 s (sphere_subset_closedBall hs))
      simp only [Multiset.mem_map, not_exists, not_and]
      exact fun b hb h0 => hne s hs b (Multiset.mem_cons_of_mem hb) h0
    have hsplit : Set.EqOn
        (fun s => φ s * deriv (fun s => ((a ::ₘ Z).map fun b => s - b).prod * u s) s /
          (((a ::ₘ Z).map fun b => s - b).prod * u s))
        (fun s => (s - a)⁻¹ • φ s + φ s * deriv F s / F s) (sphere c r) := by
      intro s hs
      have hsO : O ∈ 𝓝 s := hO.mem_nhds (hball (sphere_subset_closedBall hs))
      have hfun : (fun s => ((a ::ₘ Z).map fun b => s - b).prod * u s) = fun s => (s - a) * F s := by
        funext w
        simp only [Multiset.map_cons, Multiset.prod_cons, hFdef, mul_assoc]
      have hval : ((a ::ₘ Z).map fun b => s - b).prod * u s = (s - a) * F s := by
        simp only [Multiset.map_cons, Multiset.prod_cons, hFdef, mul_assoc]
      have hder : deriv (fun s => (s - a) * F s) s = 1 * F s + (s - a) * deriv F s :=
        (((hasDerivAt_id' s).sub_const a).mul (hF.differentiableAt hsO).hasDerivAt).deriv
      have hsa : s - a ≠ 0 := hne s hs a (Multiset.mem_cons_self a Z)
      have hFs := hFne s hs
      show φ s * deriv (fun s => ((a ::ₘ Z).map fun b => s - b).prod * u s) s /
          (((a ::ₘ Z).map fun b => s - b).prod * u s) = (s - a)⁻¹ • φ s + φ s * deriv F s / F s
      rw [hfun, hder, hval, smul_eq_mul]
      field_simp
    have hint1 : CircleIntegrable (fun s => (s - a)⁻¹ • φ s) c r := by
      refine ContinuousOn.circleIntegrable hr.le ?_
      simp only [smul_eq_mul]
      refine ContinuousOn.mul ?_ (hφ.continuousOn.mono (sphere_subset_closedBall.trans hball))
      exact (continuousOn_id.sub continuousOn_const).inv₀
        (fun s hs => hne s hs a (Multiset.mem_cons_self a Z))
    have hint2 : CircleIntegrable (fun s => φ s * deriv F s / F s) c r := by
      refine ContinuousOn.circleIntegrable hr.le ?_
      intro s hs
      have hsO : O ∈ 𝓝 s := hO.mem_nhds (hball (sphere_subset_closedBall hs))
      exact (((hφ.differentiableAt hsO).mul ((hF.deriv hO).differentiableAt hsO)).div
        (hF.differentiableAt hsO) (hFne s hs)).continuousAt.continuousWithinAt
    have hcauchy : (2 * π * I : ℂ)⁻¹ • (∮ s in C(c, r), (s - a)⁻¹ • φ s) = φ a :=
      two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        Set.countable_empty ha (hφ.continuousOn.mono hball)
        (fun z hz => hφ.differentiableAt (hO.mem_nhds (hball (ball_subset_closedBall hz.1))))
    rw [circleIntegral.integral_congr hr.le hsplit, circleIntegral.integral_add hint1 hint2, mul_add,
      ← smul_eq_mul, hcauchy, ih hZ', Multiset.map_cons, Multiset.sum_cons]

theorem CircleArgumentPrinciple.factorisation {h : ℂ → ℂ} {O : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hO : IsOpen O) (hball : closedBall c r ⊆ O) (hh : DifferentiableOn ℂ h O)
    (hsph : ∀ s ∈ sphere c r, h s ≠ 0) :
    ∃ (Z : Multiset ℂ) (u : ℂ → ℂ),
      (∀ a ∈ Z, a ∈ ball c r) ∧ DifferentiableOn ℂ u O ∧ (∀ s ∈ closedBall c r, u s ≠ 0) ∧
      (∀ s ∈ O, h s = (Z.map fun a => s - a).prod * u s) := by
  have han : AnalyticOnNhd ℂ h O := hh.analyticOnNhd hO

  have hord : ∀ z ∈ closedBall c r, analyticOrderAt h z ≠ ⊤ := by
    intro z hz htop
    have h0 := (han.mono hball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall c r).isPreconnected hz (analyticOrderAt_eq_top.1 htop)
    have hs : c + (r : ℂ) ∈ sphere c r := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact hsph _ hs (h0 (sphere_subset_closedBall hs))

  set S0 : Set ℂ := {z | z ∈ closedBall c r ∧ h z = 0} with hS0def
  have hS0fin : S0.Finite := by
    apply IsCompact.finite
    · refine (isCompact_closedBall c r).of_isClosed_subset ?_ (fun z hz => hz.1)
      exact (hh.continuousOn.mono hball).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
    · rw [isDiscrete_iff_nhdsNE]
      intro z hz
      rcases (han z (hball hz.1)).eventually_eq_zero_or_eventually_ne_zero with h1 | h1
      · exact absurd (analyticOrderAt_eq_top.2 h1) (hord z hz.1)
      · rw [Filter.inf_principal_eq_bot]
        filter_upwards [h1] with w hw hwS
        exact hw hwS.2
  set S : Finset ℂ := hS0fin.toFinset with hSdef
  have hmemS : ∀ a, a ∈ S ↔ a ∈ closedBall c r ∧ h a = 0 := fun a => hS0fin.mem_toFinset
  set m : ℂ → ℕ := fun a => analyticOrderNatAt h a with hmdef
  have hmcast : ∀ a ∈ S, analyticOrderAt h a = (m a : ℕ∞) := fun a ha =>
    (Nat.cast_analyticOrderNatAt (hord a ((hmemS a).1 ha).1)).symm
  have hmpos : ∀ a ∈ S, m a ≠ 0 := by
    intro a ha h0
    have h1 := hmcast a ha
    rw [h0, Nat.cast_zero, analyticOrderAt_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact h1 (han a (hball ((hmemS a).1 ha).1))
    · exact h1 ((hmemS a).1 ha).2
  set P : ℂ → ℂ := fun s => ∏ a ∈ S, (s - a) ^ m a with hPdef
  set Z : Multiset ℂ := ∑ a ∈ S, Multiset.replicate (m a) a with hZdef
  have hPZ : ∀ s, (Z.map fun a => s - a).prod = P s := by
    intro s
    simp only [hZdef, hPdef]
    induction S using Finset.induction_on with
    | empty => simp
    | insert b T hb ih =>
      rw [Finset.sum_insert hb, Finset.prod_insert hb, Multiset.map_add, Multiset.prod_add, ih,
        Multiset.map_replicate, Multiset.prod_replicate]
  have hPdiff : Differentiable ℂ P := by
    simp only [hPdef]
    fun_prop
  have hP0 : ∀ s, P s = 0 ↔ s ∈ S := by
    intro s
    simp only [hPdef, Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨a, ha, h0⟩
      rw [sub_eq_zero.1 ((pow_eq_zero_iff (hmpos a ha)).1 h0)]
      exact ha
    · intro hs
      exact ⟨s, hs, by rw [sub_self]; exact zero_pow (hmpos s hs)⟩

  have hloc : ∀ a ∈ S, ∃ G : ℂ → ℂ, AnalyticAt ℂ G a ∧ G a ≠ 0 ∧
      ∀ᶠ w in 𝓝[≠] a, P w ≠ 0 ∧ h w / P w = G w := by
    intro a ha
    obtain ⟨g, hg, hga, hev⟩ :=
      (han a (hball ((hmemS a).1 ha).1)).analyticOrderAt_eq_natCast.1 (hmcast a ha)
    set Q : ℂ → ℂ := fun w => ∏ b ∈ S.erase a, (w - b) ^ m b with hQdef
    have hPQ : ∀ w, P w = (w - a) ^ m a * Q w := fun w =>
      (Finset.mul_prod_erase S (fun b => (w - b) ^ m b) ha).symm
    have hQa : Q a ≠ 0 := by
      simp only [hQdef]
      rw [Finset.prod_ne_zero_iff]
      intro b hb
      exact pow_ne_zero _ (sub_ne_zero.2 (Finset.ne_of_mem_erase hb).symm)
    have hQan : AnalyticAt ℂ Q a := by
      simp only [hQdef]
      fun_prop
    refine ⟨fun w => g w / Q w, hg.div hQan hQa, div_ne_zero hga hQa, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds (hQan.continuousAt.eventually_ne hQa),
      self_mem_nhdsWithin] with w hw hQw hwa
    have hpow : (w - a) ^ m a ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hwa)
    refine ⟨by rw [hPQ]; exact mul_ne_zero hpow hQw, ?_⟩
    rw [hw, hPQ, smul_eq_mul, mul_div_mul_left _ _ hpow]
  set u : ℂ → ℂ := fun s => if P s = 0 then limUnder (𝓝[≠] s) (fun w => h w / P w) else h s / P s
    with hudef
  have hu_near : ∀ a ∈ S, ∃ G : ℂ → ℂ, AnalyticAt ℂ G a ∧ G a ≠ 0 ∧ u =ᶠ[𝓝 a] G := by
    intro a ha
    obtain ⟨G, hG, hGa, hev⟩ := hloc a ha
    refine ⟨G, hG, hGa, ?_⟩
    have hlim : limUnder (𝓝[≠] a) (fun w => h w / P w) = G a :=
      Tendsto.limUnder_eq ((hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
        (hev.mono fun w hw => hw.2.symm))
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with w hw
    by_cases hwa : w = a
    · subst hwa
      simp only [hudef, (hP0 w).2 ha, if_true, hlim]
    · obtain ⟨hPw, hq⟩ := hw hwa
      simp only [hudef, hPw, if_false, hq]
  have hu_off : ∀ s, P s ≠ 0 → u =ᶠ[𝓝 s] fun w => h w / P w := by
    intro s hs
    filter_upwards [(hPdiff s).continuousAt.eventually_ne hs] with w hw
    simp only [hudef, hw, if_false]
  refine ⟨Z, u, ?_, ?_, ?_, ?_⟩
  ·
    intro a haZ
    obtain ⟨b, hb, hab⟩ := Multiset.mem_sum.1 haZ
    rw [Multiset.eq_of_mem_replicate hab]
    obtain ⟨hbc, hb0⟩ := (hmemS b).1 hb
    rw [mem_ball]
    refine lt_of_le_of_ne (mem_closedBall.1 hbc) fun hbr => hsph b ?_ hb0
    exact mem_sphere.2 hbr
  ·
    intro s hs
    by_cases hPs : P s = 0
    · obtain ⟨G, hG, -, hEq⟩ := hu_near s ((hP0 s).1 hPs)
      exact (hG.differentiableAt.congr_of_eventuallyEq hEq).differentiableWithinAt
    · exact (((hh.differentiableAt (hO.mem_nhds hs)).div (hPdiff s) hPs).congr_of_eventuallyEq
        (hu_off s hPs)).differentiableWithinAt
  ·
    intro s hs
    by_cases hPs : P s = 0
    · obtain ⟨G, -, hGs, hEq⟩ := hu_near s ((hP0 s).1 hPs)
      rw [hEq.eq_of_nhds]
      exact hGs
    · have hhs : h s ≠ 0 := fun h0 => hPs ((hP0 s).2 ((hmemS s).2 ⟨hs, h0⟩))
      simp only [hudef, hPs, if_false]
      exact div_ne_zero hhs hPs
  ·
    intro s hs
    rw [hPZ]
    by_cases hPs : P s = 0
    · rw [hPs, zero_mul]
      exact ((hmemS s).1 ((hP0 s).1 hPs)).2
    · simp only [hudef, hPs, if_false]
      field_simp

theorem CircleArgumentPrinciple.proof : CircleArgumentPrinciple.Statement := by
  intro h O c r hr hO hball hh hsph
  obtain ⟨Z, u, hZ, hu, hu0, hfac⟩ := CircleArgumentPrinciple.factorisation hr hO hball hh hsph
  refine ⟨Z, u, hZ, hu, hu0, hfac, fun φ hφ => ?_⟩
  rw [← CircleArgumentPrinciple.integral_prod_mul hr hO hball hu hu0 hφ Z hZ]
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro s hs
  have hsO : s ∈ O := hball (sphere_subset_closedBall hs)
  have heq : h =ᶠ[𝓝 s] fun w => (Z.map fun a => w - a).prod * u w :=
    Filter.eventually_of_mem (hO.mem_nhds hsO) hfac
  simp only [heq.deriv_eq, hfac s hsO]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

