import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollB
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0002
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.NormIteratedFDerivCompLeOfIsOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

namespace ArgumentConvergenceLemmas

open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)

noncomputable section

theorem molli_contDiffAt {D : ℕ} (ρ : Mollifier D) {P : Set (Fin D → ℂ)} (hP : IsOpen P)
    {u : (Fin D → ℂ) → ℝ} (hu : ContinuousOn u P) {ε : ℝ} (hε : 0 < ε) {z : Fin D → ℂ}
    (hz : z ∈ shrink P ε) : ContDiffAt ℝ ∞ (molli ρ ε u) z := by
  obtain ⟨δ, hδ, hδP⟩ := ReciprocityTheory.AnForm.A.exists_thick hP hε.le hz
  have hi : Integrable ((closedBall z (ε + δ)).indicator u) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).2
      ((hu.mono hδP).integrableOn_compact (isCompact_closedBall z (ε + δ)))
  have hg := (ReciprocityTheory.AnForm.A.scaled_hasCompactSupport ρ hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := ⊤) (ReciprocityTheory.AnForm.A.scaled_contDiff ρ ε)
    hi.locallyIntegrable
  refine hg.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ hε (C := closedBall z (ε + δ))
    (closedBall_subset_closedBall' (by linarith)), convolution_def]
  rfl

section Calculus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_fderiv_fderiv_eq (g : E → F) (y : E) :
    ‖fderiv ℝ (fderiv ℝ g) y‖ = ‖iteratedFDeriv ℝ 2 g y‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

theorem norm_iteratedFDeriv_sub_eq {a b : E → ℝ} {V : Set E} (hV : IsOpen V)
    (ha : ContDiffOn ℝ 2 a V) (hb : ContDiffOn ℝ 2 b V) {z : E} (hz : z ∈ V) :
    ‖iteratedFDeriv ℝ 0 (fun y => a y - b y) z‖ = ‖a z - b z‖ ∧
      ‖iteratedFDeriv ℝ 1 (fun y => a y - b y) z‖ = ‖fderiv ℝ a z - fderiv ℝ b z‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => a y - b y) z‖ =
        ‖fderiv ℝ (fderiv ℝ a) z - fderiv ℝ (fderiv ℝ b) z‖ := by
  have da : DifferentiableAt ℝ a z :=
    (ha.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  have db : DifferentiableAt ℝ b z :=
    (hb.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  refine ⟨norm_iteratedFDeriv_zero, ?_, ?_⟩
  · rw [norm_iteratedFDeriv_one, fderiv_fun_sub da db]
  · rw [← norm_fderiv_fderiv_eq, fderiv2_sub_of_contDiffOn hV ha hb hz]

theorem norm_iteratedFDeriv_comp_le_of_isOpen {g : F → G} {f : E → F} {s : Set E} {t : Set F}
    (hs : IsOpen s) (ht : IsOpen t) (hg : ContDiffOn ℝ 2 g t) (hf : ContDiffOn ℝ 2 f s)
    (hst : MapsTo f s t) {x : E} (hx : x ∈ s) {n : ℕ} (hn : n ≤ 2) {C d : ℝ}
    (hC : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i f x‖ ≤ d ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * d ^ n := by
  have hn' : (n : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hn
  rw [← iteratedFDerivWithin_of_isOpen n hs hx]
  refine norm_iteratedFDerivWithin_comp_le (hg.of_le hn') (hf.of_le hn') le_rfl ht.uniqueDiffOn
    hs.uniqueDiffOn hst hx (fun i hi => ?_) (fun i hi1 hi => ?_)
  · rw [iteratedFDerivWithin_of_isOpen i ht (hst hx)]
    exact hC i (hi.trans hn)
  · rw [iteratedFDerivWithin_of_isOpen i hs hx]
    exact hD i hi1 (hi.trans hn)

theorem exists_bound_iteratedFDeriv {f : E → F} {s K : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ B : ℝ, ∀ i : ℕ, i ≤ 2 → ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := by
  have h : ∀ i : ℕ, i ≤ 2 → ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := fun i hi =>
    hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hf hs (by exact_mod_cast hi)).mono hKs)
  obtain ⟨B0, h0⟩ := h 0 (by norm_num)
  obtain ⟨B1, h1⟩ := h 1 (by norm_num)
  obtain ⟨B2, h2⟩ := h 2 le_rfl
  refine ⟨max B0 (max B1 B2), fun i hi y hy => ?_⟩
  interval_cases i
  · exact (h0 y hy).trans (le_max_left _ _)
  · exact (h1 y hy).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h2 y hy).trans ((le_max_right _ _).trans (le_max_right _ _))

end Calculus

theorem tendstoUniformlyOn_of_norm_le {Y α : Type*} [SeminormedAddCommGroup α] {F : ℝ → Y → α}
    {f : Y → α} {K : Set Y} {β : ℝ → ℝ} (hβ : Tendsto β (𝓝[>] 0) (𝓝 0))
    (h : ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ K, ‖F t y - f y‖ ≤ β t) :
    TendstoUniformlyOn F f (𝓝[>] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  filter_upwards [h, hβ.eventually (gt_mem_nhds he)] with t ht hβt y hy
  rw [dist_comm, dist_eq_norm]
  exact (ht y hy).trans_lt hβt

theorem tendsto_logErrorBound_nhdsWithin (C : ℝ) : Tendsto (fun t => errorWithLinear C t) (𝓝[>] 0) (𝓝 0) := by
  have hell : Tendsto ell (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun t => errE C t) (𝓝[>] 0) (𝓝 0) := by
    have := (h1.comp hell).const_mul C
    rw [mul_zero] at this
    refine this.congr fun t => ?_
    simp only [Function.comp, errE, mul_div_assoc]
  have h3 : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  simpa [errorWithLinear] using h2.add h3

theorem logErrorBound_pos {C t : ℝ} (hC : 0 < C) (ht : 0 < t) (ht1 : t < Real.exp (-1)) :
    0 < errorWithLinear C t := by
  have hl : 1 < ell t := by
    have := Real.log_lt_log ht ht1
    rw [Real.log_exp] at this
    show 1 < Real.log t⁻¹
    rw [Real.log_inv]
    linarith
  have hlog : 0 < Real.log (ell t) := Real.log_pos hl
  have hl0 : 0 < ell t := by linarith
  unfold errorWithLinear errE
  positivity

end

end ArgumentConvergenceLemmas

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PDivisorNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Metric
open ReciprocityTheory.AnForm.A (coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem DivisorNull.exists_chart_mem_alt {A : FinHolAtlas D X} (R : RegChartData A) (x : X) :
    ∃ j, x ∈ (R.ψ j).source ∧ R.ψ j x ∈ R.W j := by
  obtain ⟨j, hx, hW⟩ := R.cover x
  exact ⟨j, hx, R.closure_W'_subset j (subset_closure (R.closure_W''_subset j (subset_closure hW)))⟩

theorem DivisorNull.not_mem_Yo_iff {A : FinHolAtlas D X} (R : RegChartData A) (j : Fin R.n) {y : X}
    (hy : y ∈ (R.ψ j).source) (hW : R.ψ j y ∈ R.W j) :
    y ∉ R.Yo ↔ ∏ i ∈ R.S j, R.ψ j y i = 0 := by
  have h := R.mem_Yo_iff j _ hW
  rw [(R.ψ j).left_inv hy] at h
  rw [h, not_not, Finset.prod_eq_zero_iff]
  rfl

theorem DivisorNull.isAnalyticSubset_compl_Yo {A : FinHolAtlas D X} (R : RegChartData A) :
    A.IsAnalyticSubset R.Yoᶜ := by
  intro x
  obtain ⟨j, hx, hW⟩ := DivisorNull.exists_chart_mem_alt R x
  refine ⟨(R.ψ j).source ∩ R.ψ j ⁻¹' R.W j, (R.ψ j).isOpen_inter_preimage (R.isOpen_kappaOpenNeighbourhood j), ⟨hx, hW⟩,
    1, fun _ y => ∏ i ∈ R.S j, R.ψ j y i, ?_, ?_⟩
  · intro _ k
    have hk := (R.compat j k).1
    show AnalyticOnNhd ℂ (fun z => ∏ i ∈ R.S j, (R.ψ j ∘ (A.chart k).symm) z i) _
    refine Finset.analyticOnNhd_fun_prod _ fun i _ z hz => ?_
    have hz' : AnalyticAt ℂ (R.ψ j ∘ (A.chart k).symm) z := hk z ⟨hz.1, hz.2.1⟩
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt _).comp hz'
  · ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hy, hs, hw⟩
      exact ⟨⟨hs, hw⟩, fun _ => (DivisorNull.not_mem_Yo_iff R j hs hw).1 hy⟩
    · rintro ⟨⟨hs, hw⟩, h⟩
      exact ⟨(DivisorNull.not_mem_Yo_iff R j hs hw).2 (h 0), hs, hw⟩

theorem DivisorNull.interior_compl_Yo {A : FinHolAtlas D X} (R : RegChartData A) :
    interior R.Yoᶜ = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨U, hUY, hU, hxU⟩ := mem_interior.1 hx
  obtain ⟨j, hxs, hW⟩ := DivisorNull.exists_chart_mem_alt R x
  have hO : IsOpen (R.W j ∩ (R.ψ j).symm ⁻¹' U) := by
    have h2 := ((R.ψ j).isOpen_inter_preimage_symm hU).inter (R.isOpen_kappaOpenNeighbourhood j)
    convert h2 using 1
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨⟨R.W_subset j hz, hzU⟩, hz⟩
    · rintro ⟨⟨_, hzU⟩, hz⟩
      exact ⟨hz, hzU⟩
  have hxO : R.ψ j x ∈ R.W j ∩ (R.ψ j).symm ⁻¹' U := by
    refine ⟨hW, ?_⟩
    show (R.ψ j).symm (R.ψ j x) ∈ U
    rw [(R.ψ j).left_inv hxs]
    exact hxU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO _ hxO
  let w : Fin D → ℂ := fun i => if R.ψ j x i = 0 then ((ε / 2 : ℝ) : ℂ) else R.ψ j x i
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i
    by_cases h : R.ψ j x i = 0
    · simp only [w, if_pos h, ne_eq, Complex.ofReal_eq_zero]
      linarith
    · simp only [w, if_neg h]
      exact h
  have hwb : w ∈ ball (R.ψ j x) ε := by
    rw [mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
    intro i
    by_cases h : R.ψ j x i = 0
    · rw [Pi.sub_apply]
      simp only [w]
      rw [if_pos h, h, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · simp only [w, Pi.sub_apply, if_neg h, sub_self, norm_zero]
      exact hε
  obtain ⟨hwW, hwU⟩ := hball hwb
  have hsrc : (R.ψ j).symm w ∈ (R.ψ j).source := (R.ψ j).map_target (R.W_subset j hwW)
  have hright : R.ψ j ((R.ψ j).symm w) = w := (R.ψ j).right_inv (R.W_subset j hwW)
  have hprod := (DivisorNull.not_mem_Yo_iff R j hsrc (by rw [hright]; exact hwW)).1 (hUY hwU)
  rw [hright, Finset.prod_eq_zero_iff] at hprod
  obtain ⟨i, -, hi⟩ := hprod
  exact hw0 i hi

theorem DivisorNull.proof : DivisorNull.Statement :=
  fun _ R => ⟨DivisorNull.isAnalyticSubset_compl_Yo R, DivisorNull.interior_compl_Yo R⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PKaehlerBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot chartIdx)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

noncomputable section

theorem two_le_smooth_kb : (2 : WithTop ℕ∞) ≤ ∞ := by norm_cast

theorem regChartData_isCompact_univ {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    (R : RegChartData A) : IsCompact (Set.univ : Set X) := by
  have hK : ∀ j, IsCompact ((R.ψ j).symm '' closure (R.W'' j)) := fun j => by
    have hc : IsCompact (closure (R.W'' j)) :=
      (R.isCompact_closure_middle j).of_isClosed_subset isClosed_closure
        ((R.closure_W''_subset j).trans subset_closure)
    refine hc.image_of_continuousOn ((R.ψ j).continuousOn_symm.mono ?_)
    exact (R.closure_W''_subset j).trans (subset_closure.trans
      ((R.closure_W'_subset j).trans (R.W_subset j)))
  refine (isCompact_iUnion hK).of_isClosed_subset isClosed_univ fun x _ => ?_
  obtain ⟨j, hx, hxW⟩ := R.cover x
  exact Set.mem_iUnion.2 ⟨j, R.ψ j x, subset_closure hxW, (R.ψ j).left_inv hx⟩

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem levi_abs_le_local (A : FinHolAtlas D X) (θ om : LocPot X) (hθ : IsPotential A θ)
    (hom : IsPotential A om) (hpos : IsPosPot A om) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ M : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (θ.U p ∩ om.U p) ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin D → ℂ,
        |levi (θ.φ p ∘ (A.chart j).symm) y u| ≤ M * levi (om.φ p ∘ (A.chart j).symm) y u := by
  set c := A.chart j with hc
  set O := c.target ∩ c.symm ⁻¹' (θ.U p ∩ om.U p) with hO
  have hOo : IsOpen O := c.continuousOn_symm.isOpen_inter_preimage c.open_target
    ((θ.isOpen_U p).inter (om.isOpen_U p))
  have hpO : c p ∈ O := ⟨c.map_source hp, by
    simp only [Set.mem_preimage, c.left_inv hp]; exact ⟨θ.mem_U p, om.mem_U p⟩⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hOo _ hpO
  have hcb : Metric.closedBall (c p) (r / 2) ⊆ O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrO
  have homs : ContDiffOn ℝ 2 (om.φ p ∘ c.symm) O :=
    ((hom.1 p j).mono fun y hy => ⟨hy.1, hy.2.2⟩).of_le two_le_smooth_kb
  have hθs : ContDiffOn ℝ 2 (θ.φ p ∘ c.symm) O :=
    ((hθ.1 p j).mono fun y hy => ⟨hy.1, hy.2.1⟩).of_le two_le_smooth_kb
  set K := Metric.closedBall (c p) (r / 2) ×ˢ Metric.sphere (0 : Fin D → ℂ) 1 with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKO : K ⊆ O ×ˢ Set.univ := Set.prod_mono hcb (Set.subset_univ _)
  have hpos' : ∀ q ∈ K, 0 < levi (om.φ p ∘ c.symm) q.1 q.2 := by
    rintro ⟨y, u⟩ ⟨hy, hu⟩
    refine hpos p j y ⟨(hcb hy).1, (hcb hy).2.2⟩ u ?_
    rintro rfl
    simp at hu
  have hcont : ContinuousOn (fun q : (Fin D → ℂ) × (Fin D → ℂ) =>
      |levi (θ.φ p ∘ c.symm) q.1 q.2| / levi (om.φ p ∘ c.symm) q.1 q.2) K :=
    (((continuousOn_levi hOo hθs).mono hKO).abs).div ((continuousOn_levi hOo homs).mono hKO)
      (fun q hq => (hpos' q hq).ne')
  obtain ⟨M, hM⟩ := hKc.bddAbove_image hcont
  refine ⟨r / 2, by linarith, M, hcb, fun y hy u => ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp [levi_zero]
  · have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
    obtain ⟨v, hv'⟩ : ∃ v : Fin D → ℂ, v = ‖u‖⁻¹ • u := ⟨_, rfl⟩
    have hv : v ∈ Metric.sphere (0 : Fin D → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hv', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hq : (y, v) ∈ K := ⟨hy, hv⟩
    have h1 : |levi (θ.φ p ∘ c.symm) y v| / levi (om.φ p ∘ c.symm) y v ≤ M :=
      hM ⟨(y, v), hq, rfl⟩
    have h2 := hpos' _ hq
    have h3 : |levi (θ.φ p ∘ c.symm) y v| ≤ M * levi (om.φ p ∘ c.symm) y v := by
      rwa [div_le_iff₀ h2] at h1
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ‖u‖ := ⟨_, rfl⟩
    have huv : u = s • v := by
      rw [hs, hv', smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [huv, levi_smul_dir, levi_smul_dir, abs_mul, abs_of_nonneg (sq_nonneg s)]
    have : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith

theorem levi_abs_le_global (A : FinHolAtlas D X) (hX : IsCompact (Set.univ : Set X))
    (θ om : LocPot X) (hθ : IsPotential A θ) (hom : IsPotential A om) (hpos : IsPosPot A om) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (θ.U x ∩ om.U x),
      ∀ v : Fin D → ℂ,
        |levi (θ.φ x ∘ (A.chart k).symm) y v| ≤ M * levi (om.φ x ∘ (A.chart k).symm) y v := by
  classical
  have hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source := fun p =>
    Classical.choose_spec (A.cover p)
  have key := fun p => levi_abs_le_local A θ om hθ hom hpos p (chartIdx A p) (hsrc p)
  choose r hr m hsub hbd using key
  let V : X → Set X := fun p => (A.chart (chartIdx A p)).source ∩
    (A.chart (chartIdx A p)) ⁻¹' Metric.ball (A.chart (chartIdx A p) p) (r p)
  have hVo : ∀ p, IsOpen (V p) := fun p =>
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := hX.elim_finite_subcover V hVo
    (fun p _ => Set.mem_iUnion.2 ⟨p, hsrc p, Metric.mem_ball_self (hr p)⟩)
  refine ⟨∑ p ∈ t, |m p|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro x k y hy v
  set C := ∑ p ∈ t, |m p| with hC
  obtain ⟨hyk, hyU⟩ := hy
  have hqθ : (A.chart k).symm y ∈ θ.U x := hyU.1
  have hqom : (A.chart k).symm y ∈ om.U x := hyU.2
  set q := (A.chart k).symm y with hq
  obtain ⟨p, hpt, hqV⟩ : ∃ p ∈ t, q ∈ V p := by
    simpa using ht (Set.mem_univ q)
  set j := chartIdx A p with hj
  set c := A.chart j with hc
  have hqs : q ∈ c.source := hqV.1
  have hqb : c q ∈ Metric.ball (c p) (r p) := hqV.2
  have hcqO := hsub p (Metric.ball_subset_closedBall hqb)
  have hqp : q ∈ θ.U p ∩ om.U p := by
    have := hcqO.2; rwa [Set.mem_preimage, c.left_inv hqs] at this
  have hcqt : c q ∈ c.target := c.map_source hqs
  have hsc : c.symm (c q) = q := c.left_inv hqs
  set τ := c ∘ (A.chart k).symm with hτd
  have hτ : AnalyticAt ℂ τ y := A.holo k j y ⟨hyk, hqs⟩
  have hτy : τ y = c q := rfl
  have hsrcev : ∀ᶠ y' in 𝓝 y, (A.chart k).symm y' ∈ c.source :=
    ((A.chart k).continuousAt_symm hyk).preimage_mem_nhds (c.open_source.mem_nhds hqs)
  have hgerm : ∀ f : X → ℝ, f ∘ (A.chart k).symm =ᶠ[𝓝 y] (f ∘ c.symm) ∘ τ := fun f => by
    filter_upwards [hsrcev] with y' hy'
    simp only [Function.comp_apply, τ, c.left_inv hy']
  have hsm : ∀ P : LocPot X, IsPotential A P → ∀ z, q ∈ P.U z →
      ContDiffAt ℝ 2 (P.φ z ∘ c.symm) (c q) := by
    intro P hP z hz
    have hOz : IsOpen (c.target ∩ c.symm ⁻¹' P.U z) :=
      c.continuousOn_symm.isOpen_inter_preimage c.open_target (P.isOpen_U z)
    exact ((hP.1 z j).of_le two_le_smooth_kb).contDiffAt
      (hOz.mem_nhds ⟨hcqt, by simp only [Set.mem_preimage, hsc]; exact hz⟩)
  have hbase : ∀ P : LocPot X, IsPotential A P → q ∈ P.U x → q ∈ P.U p → ∀ u : Fin D → ℂ,
      levi (P.φ x ∘ c.symm) (c q) u = levi (P.φ p ∘ c.symm) (c q) u := by
    intro P hP hx hp u
    obtain ⟨W, hWo, hqW, G, hG, hGeq⟩ := hP.2 x p q ⟨hx, hp⟩
    have hGa : AnalyticAt ℂ (G ∘ c.symm) (c q) :=
      hG j (c q) ⟨hcqt, by show c.symm (c q) ∈ W; rw [hsc]; exact hqW⟩
    have hRe : ContDiffAt ℝ 2 (fun z => ((G ∘ c.symm) z).re) (c q) := by
      have := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp (c q)
        (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
      simpa [Function.comp_def] using this
    have hev : P.φ x ∘ c.symm =ᶠ[𝓝 (c q)]
        fun z => (P.φ p ∘ c.symm) z + 1 * ((G ∘ c.symm) z).re := by
      have hopen : IsOpen (W ∩ P.U x ∩ P.U p) :=
        (hWo.inter (P.isOpen_U x)).inter (P.isOpen_U p)
      have : ∀ᶠ z in 𝓝 (c q), c.symm z ∈ W ∩ P.U x ∩ P.U p :=
        (c.continuousAt_symm hcqt).preimage_mem_nhds
          (hopen.mem_nhds (by rw [hsc]; exact ⟨⟨hqW, hx⟩, hp⟩))
      filter_upwards [this] with z hz
      have := hGeq (c.symm z) hz
      simp only [Function.comp_apply, one_mul]
      linarith
    rw [levi_congr hev, levi_add_smul 1 (hsm P hP p hp) hRe, levi_re_analytic hGa]
    ring
  have htr : ∀ P : LocPot X, IsPotential A P → q ∈ P.U x → q ∈ P.U p →
      levi (P.φ x ∘ (A.chart k).symm) y v = levi (P.φ p ∘ c.symm) (c q) (fderiv ℂ τ y v) := by
    intro P hP hx hp
    rw [levi_congr (hgerm _), levi_comp v hτ (by rw [hτy]; exact hsm P hP x hx), hτy,
      hbase P hP hx hp]
  have hb := hbd p (c q) (Metric.ball_subset_closedBall hqb) (fderiv ℂ τ y v)
  have hLom : 0 ≤ levi (om.φ p ∘ c.symm) (c q) (fderiv ℂ τ y v) := by
    rcases eq_or_ne (fderiv ℂ τ y v) 0 with h0 | h0
    · rw [h0, levi_zero]
    · exact (hpos p j (c q) ⟨hcqt, hcqO.2.2⟩ _ h0).le
  have hCm : m p ≤ C :=
    (le_abs_self (m p)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (m i)) hpt)
  rw [htr θ hθ hqθ hqp.1, htr om hom hqom hqp.2]
  nlinarith

theorem KaehlerBound.proof : KaehlerBound.Statement := by
  intro D X _ A R
  obtain ⟨M, hM0, hM⟩ := levi_abs_le_global A (regChartData_isCompact_univ R) R.θ R.om R.θ_pot
    R.om_pot R.om_pos
  have hK : (0 : ℝ) < M + 1 := by linarith
  have hsm : ∀ P : LocPot X, IsPotential A P → ∀ x k,
      ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x,
        ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y := fun P hP x k y hy =>
    ((hP.1 x k).of_le two_le_smooth_kb).contDiffAt
      (((A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target
        (P.isOpen_U x)).mem_nhds hy)
  have hsmul : ∀ (P : LocPot X) (a : ℝ) x k y, ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y →
      ∀ w, levi ((P.rsmul a).φ x ∘ (A.chart k).symm) y w =
        a * levi (P.φ x ∘ (A.chart k).symm) y w := by
    intro P a x k y hy w
    have h := levi_add_smul a (contDiffAt_const (c := (0 : ℝ))) hy w
    have he : (P.rsmul a).φ x ∘ (A.chart k).symm =
        fun z => (0 : ℝ) + a * (P.φ x ∘ (A.chart k).symm) z := by
      funext z
      simp [LocPot.rsmul]
    rw [he, h, levi_const, zero_add]
  have key : ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.θ.U x ∩ R.om.U x),
      ∀ w : Fin D → ℂ,
        levi ((thetaOmega R).φ x ∘ (A.chart k).symm) y w =
            levi (R.θ.φ x ∘ (A.chart k).symm) y w + levi (R.om.φ x ∘ (A.chart k).symm) y w ∧
          levi ((R.om.rsmul (M + 1)).φ x ∘ (A.chart k).symm) y w =
            (M + 1) * levi (R.om.φ x ∘ (A.chart k).symm) y w ∧
          |levi (R.θ.φ x ∘ (A.chart k).symm) y w| ≤
            M * levi (R.om.φ x ∘ (A.chart k).symm) y w ∧
          0 ≤ levi (R.om.φ x ∘ (A.chart k).symm) y w := by
    intro x k y hy w
    have hθs := hsm R.θ R.θ_pot x k y ⟨hy.1, hy.2.1⟩
    have homs := hsm R.om R.om_pot x k y ⟨hy.1, hy.2.2⟩
    refine ⟨?_, hsmul R.om (M + 1) x k y homs w, hM x k y hy w, ?_⟩
    · have he : (thetaOmega R).φ x ∘ (A.chart k).symm = fun z =>
          (R.θ.φ x ∘ (A.chart k).symm) z + 1 * (R.om.φ x ∘ (A.chart k).symm) z := by
        funext z
        show R.θ.φ x _ + R.om.φ x _ = _
        simp
      rw [he, levi_add_smul 1 hθs homs w, one_mul]
    · rcases eq_or_ne w 0 with h0 | h0
      · rw [h0, levi_zero]
      · exact (R.om_pos x k y ⟨hy.1, hy.2.2⟩ w h0).le
  refine ⟨⟨R.om.rsmul (M + 1), ReciprocityTheory.AnForm.M.isPotentialRsmul A (M + 1) R.om R.om_pot,
    fun x k y hy w hw => ?_⟩, ?_, ?_⟩
  · rw [hsmul R.om (M + 1) x k y (hsm R.om R.om_pot x k y hy) w]
    exact mul_pos hK (R.om_pos x k y hy w hw)
  · intro x k y hy w
    have hy' : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.θ.U x ∩ R.om.U x) :=
      ⟨hy.1, hy.2.1.2.1, hy.2.1.2.2⟩
    obtain ⟨h1, h2, h3, h4⟩ := key x k y hy' w
    show 1 * levi ((thetaOmega R).φ x ∘ (A.chart k).symm) y w ≤
      1 * levi ((R.om.rsmul (M + 1)).φ x ∘ (A.chart k).symm) y w
    rw [h1, h2]
    have := abs_le.mp h3
    nlinarith
  · intro x k y hy w
    have hy' : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.θ.U x ∩ R.om.U x) :=
      ⟨hy.1, hy.2.2.1, hy.2.2.2⟩
    obtain ⟨h1, h2, h3, h4⟩ := key x k y hy' w
    show -1 * levi ((R.om.rsmul (M + 1)).φ x ∘ (A.chart k).symm) y w ≤
      1 * levi ((thetaOmega R).φ x ∘ (A.chart k).symm) y w
    rw [h1, h2]
    have := abs_le.mp h3
    nlinarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)

def LemmaETailMass.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    Dense (secOpen s) → (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    ∃ CE : ℝ, ∀ u : Fin D → X → ℝ, (∀ i, IsLemmaEPot A Om L s C₁ (u i)) →
      TailMassBound A (secOpen s) (rSec L s) (fun i => potForm Om.pot (u i)) CE

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

