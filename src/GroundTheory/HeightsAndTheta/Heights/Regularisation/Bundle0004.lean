import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi)

noncomputable section

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

section ChangeOfChart

variable {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}

theorem comp_symm_eventuallyEq {E : Type*} (g : X → E) {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) :
    (g ∘ (A.chart i).symm) ∘ (A.chart i ∘ ψ.symm) =ᶠ[𝓝 (ψ x)] g ∘ ψ.symm := by
  have h : ∀ᶠ y in 𝓝 (ψ x), ψ.symm y ∈ (A.chart i).source :=
    (ψ.continuousAt_symm (ψ.map_source hx)).preimage_mem_nhds
      (by rw [ψ.left_inv hx]; exact (A.chart i).open_source.mem_nhds hxi)
  filter_upwards [h] with y hy
  simp [(A.chart i).left_inv hy]

theorem analyticAt_chart_comp_symm (hψ : IsCompatChart A ψ) {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) : AnalyticAt ℂ (A.chart i ∘ ψ.symm) (ψ x) :=
  (hψ i).2 (ψ x) ⟨ψ.map_source hx, by simp [ψ.left_inv hx, hxi]⟩

theorem analyticAt_comp_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hψ : IsCompatChart A ψ) {g : X → E} {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) (hg : AnalyticAt ℂ (g ∘ (A.chart i).symm) (A.chart i x)) :
    AnalyticAt ℂ (g ∘ ψ.symm) (ψ x) := by
  have hτ := analyticAt_chart_comp_symm hψ hx i hxi
  have hg' : AnalyticAt ℂ (g ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (ψ x)) := by
    simpa [ψ.left_inv hx] using hg
  exact (hg'.comp hτ).congr (comp_symm_eventuallyEq g hx i hxi)

theorem contDiffAt_comp_symm (hψ : IsCompatChart A ψ) {n : WithTop ℕ∞} {g : X → ℝ} {x : X}
    (hx : x ∈ ψ.source) (i : Fin A.n) (hxi : x ∈ (A.chart i).source)
    (hg : ContDiffAt ℝ n (g ∘ (A.chart i).symm) (A.chart i x)) :
    ContDiffAt ℝ n (g ∘ ψ.symm) (ψ x) := by
  have hτ := (analyticAt_chart_comp_symm hψ hx i hxi).restrictScalars (𝕜 := ℝ)
  have hg' : ContDiffAt ℝ n (g ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (ψ x)) := by
    simpa [ψ.left_inv hx] using hg
  exact (hg'.comp (ψ x) hτ.contDiffAt).congr_of_eventuallyEq
    (comp_symm_eventuallyEq g hx i hxi).symm

theorem analyticAt_transition {ψ' : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ)
    (hψ' : IsCompatChart A ψ') {x : X} (hx : x ∈ ψ.source) (hx' : x ∈ ψ'.source) :
    AnalyticAt ℂ (ψ' ∘ ψ.symm) (ψ x) := by
  obtain ⟨i, hi⟩ := A.cover x
  refine analyticAt_comp_symm hψ hx i hi ((hψ' i).1 (A.chart i x) ⟨(A.chart i).map_source hi, ?_⟩)
  simp [(A.chart i).left_inv hi, hx']

theorem contDiffAt_comp_symm_of_smoothOn (hψ : IsCompatChart A ψ) {U : Set X} (hU : IsOpen U)
    {f : X → ℝ} (hf : A.SmoothOn U f) {x : X} (hxU : x ∈ U) (hx : x ∈ ψ.source) :
    ContDiffAt ℝ ∞ (f ∘ ψ.symm) (ψ x) := by
  obtain ⟨i, hi⟩ := A.cover x
  exact contDiffAt_comp_symm hψ hx i hi (smoothOn_contDiffAt hU hf hi hxU)
where

  smoothOn_contDiffAt {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) {i : Fin A.n}
      {x : X} (hi : x ∈ (A.chart i).source) (hxU : x ∈ U) :
      ContDiffAt ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i x) :=
    (hf i).contDiffAt (((A.chart i).continuousOn_symm.isOpen_inter_preimage
      (A.chart i).open_target hU).mem_nhds ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hxU]⟩)

theorem analyticAt_comp_symm_of_holoOn (hψ : IsCompatChart A ψ) {W : Set X}
    {G : X → ℂ} (hG : A.HoloOn W G) {x : X} (hxW : x ∈ W) (hx : x ∈ ψ.source) :
    AnalyticAt ℂ (G ∘ ψ.symm) (ψ x) := by
  obtain ⟨i, hi⟩ := A.cover x
  exact analyticAt_comp_symm hψ hx i hi
    (hG i (A.chart i x) ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hxW]⟩)

end ChangeOfChart

theorem isPsh_congr {U : Set (Fin D → ℂ)} {φ ψ : (Fin D → ℂ) → ℝ} (h : EqOn φ ψ U)
    (hφ : IsPsh U φ) : IsPsh U ψ := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in 𝓝[U] z, φ x < y := hφ.1 z hz y (by show φ z < y; rw [h hz]; exact hy)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
    rwa [← h hxU]
  · have hs : EqOn (fun ζ : ℂ => φ (z + ζ • w)) (fun ζ => ψ (z + ζ • w)) (sphere 0 |(1 : ℝ)|) :=
      fun ζ hζ => h (hd ζ (by simp at hζ; rw [hζ]))
    obtain ⟨h1, h2⟩ := hφ.2 z w hd
    refine ⟨(circleIntegrable_congr hs).1 h1, ?_⟩
    have hz : z ∈ U := by simpa using hd 0 (by simp)
    rw [← Real.circleAverage_congr_sphere hs, ← h hz]
    exact h2

namespace RegChartData

variable (R : RegChartData A)

theorem isOpen_Yo : IsOpen R.Yo := by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨j, hj⟩ := R.cover x
  have hxs : x ∈ (R.chart j).source := R.mid_subset_source j (R.inner_subset_mid j hj)
  have hV : IsOpen ((R.chart j).source ∩ R.chart j ⁻¹' (coordDiv (R.S j))ᶜ) :=
    (R.chart j).continuousOn.isOpen_inter_preimage (R.chart j).open_source
      (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _).isOpen_compl
  refine Filter.mem_of_superset (hV.mem_nhds ⟨hxs, (R.mem_Yo j x hxs).1 hx⟩) fun y hy => ?_
  exact (R.mem_Yo j y hy.1).2 hy.2

theorem symm_mem_Yo (j : Fin R.N) {y : Fin D → ℂ} (hy : y ∈ (R.chart j).target)
    (hyA : y ∉ coordDiv (R.S j)) : (R.chart j).symm y ∈ R.Yo :=
  (R.mem_Yo j _ ((R.chart j).map_target hy)).2 (by rwa [(R.chart j).right_inv hy])

theorem continuousOn_u (j : Fin R.N) :
    ContinuousOn (R.u j) ((R.chart j).target \ coordDiv (R.S j)) := by
  intro y hy
  have hq : ContinuousAt (R.q j) y :=
    ((R.q_smooth j).continuousOn).continuousAt ((R.chart j).open_target.mem_nhds hy.1)
  have hx : (R.chart j).symm y ∈ (R.chart j).source := (R.chart j).map_target hy.1
  have hph := contDiffAt_comp_symm_of_smoothOn (R.compat j) R.isOpen_Yo R.ph_smooth
    (R.symm_mem_Yo j hy.1 hy.2) hx
  rw [(R.chart j).right_inv hy.1] at hph
  exact (hq.add hph.continuousAt).continuousWithinAt

theorem smoothed_local (ρ : Mollifier D) (K : ℝ) {t : ℝ} (ht : 0 < t) (j : Fin R.N)
    {z : Fin D → ℂ} (hz : closedBall z t ⊆ (R.chart j).target) :
    ContDiffAt ℝ ∞ (R.smoothed ρ K t j) z ∧ ∀ w, 0 ≤ levi (R.smoothed ρ K t j) z w := by
  obtain ⟨δ, hδ, hδsub⟩ :=
    (isCompact_closedBall z t).exists_cthickening_subset_open (R.chart j).open_target hz
  rw [cthickening_closedBall hδ.le ht.le] at hδsub
  set U' := ball z (δ + t) with hU'
  have hU'sub : U' ⊆ (R.chart j).target := ball_subset_closedBall.trans hδsub
  obtain ⟨M, hM⟩ := (isCompact_closedBall z (δ + t)).bddAbove_image
    ((R.q_smooth j).continuousOn.mono hδsub)

  have hcont : ContinuousOn (R.u j) (U' \ coordDiv (R.S j)) :=
    (R.continuousOn_u j).mono (sdiff_subset_sdiff_left hU'sub)
  have hpsh : IsPsh (U' \ coordDiv (R.S j)) (R.u j) :=
    isPsh_mono (R.u_psh j) (sdiff_subset_sdiff_left hU'sub)
  have hbound : ∀ y ∈ U' \ coordDiv (R.S j), R.u j y ≤
      |M + R.Cph| * Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := by
    intro y hy
    have hyt : y ∈ (R.chart j).target := hU'sub hy.1
    have h1 : R.q j y ≤ M := hM ⟨y, ball_subset_closedBall hy.1, rfl⟩
    have h2 : R.ph ((R.chart j).symm y) ≤ R.Cph := R.ph_le _ (R.symm_mem_Yo j hyt hy.2)
    have hy1 : ‖y‖ < 1 := by simpa using R.target_subset j hyt
    have hs : 0 ≤ ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹ := Finset.sum_nonneg fun i _ => by
      rw [Real.log_inv]
      exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) ((norm_le_pi_norm y i).trans hy1.le))
    have hL : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := by
      have := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hs (a := Real.exp 1))
      rwa [Real.log_exp] at this
    have : R.u j y = R.q j y + R.ph ((R.chart j).symm y) := rfl
    calc R.u j y ≤ M + R.Cph := by rw [this]; linarith
      _ ≤ |M + R.Cph| := le_abs_self _
      _ ≤ _ := le_mul_of_one_le_right (abs_nonneg _) hL
  have hext := (ReciprocityTheory.AnForm.A.pshExtension_thm D (R.S j) U' (R.u j) |M + R.Cph| isOpen_ball
    (hU'sub.trans (R.target_subset j)) hcont hpsh hbound).2 K

  have heq : EqOn (limsupExt U' (coordDiv (R.S j)) (fun y => max (R.u j y) (-K)))
      (R.trunc K j) U' := by
    intro y hy
    simp only [RegChartData.trunc, limsupExt]
    split_ifs with hA
    · congr 1
      rw [nhdsWithin_restrict ((R.chart j).target \ coordDiv (R.S j)) hy isOpen_ball]
      congr 1
      ext v
      constructor
      · rintro ⟨hv1, hv2⟩; exact ⟨⟨hU'sub hv1, hv2⟩, hv1⟩
      · rintro ⟨⟨-, hv2⟩, hv1⟩; exact ⟨hv1, hv2⟩
    · rfl
  have htr : IsPsh U' (R.trunc K j) := isPsh_congr heq hext
  obtain ⟨hopen, hsm, hpm, -⟩ := (ReciprocityTheory.AnForm.A.mollify_thm D ρ U' (R.trunc K j) isOpen_ball htr).1 t ht
  have hz' : z ∈ shrink U' t := closedBall_subset_ball (lt_add_of_pos_left t hδ)
  have hlevi := (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D (shrink U' t) _ hopen
    (hsm.of_le (WithTop.coe_le_coe.mpr le_top))).1 hpm
  exact ⟨hsm.contDiffAt (hopen.mem_nhds hz'), fun w => hlevi.2 z hz' w⟩

end RegChartData

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartComparison
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' polyMax_mono')

noncomputable section

theorem log_inv_facts {t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a)
    (hta : t < Real.exp (-(Real.exp 1 + 2 * a))) :
    Real.exp 1 + 2 * a < Real.log t⁻¹ ∧ 1 < Real.log (Real.log t⁻¹) := by
  have h1 : Real.log t < -(Real.exp 1 + 2 * a) := by
    have := Real.log_lt_log ht hta
    rwa [Real.log_exp] at this
  rw [Real.log_inv]
  have he := Real.exp_pos 1
  refine ⟨by linarith, ?_⟩
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith

theorem ChartComparison.proof (h0 : MollifiedLowerBound.Statement)
    (h1 : PolyMaxOscillation.Statement) (h2 : PolyMaxLowerBound.Statement)
    (h3 : TruncPsh.Statement) (h4 : TruncTransfer.Statement) : ChartComparison.Statement := by
  intro X _ _ _ D A R ρ
  obtain ⟨δ, B₀, hδ, hV⟩ := h3 X D A R
  choose V hVo _hVt hVball hVpsh using hV
  obtain ⟨δ₁, L, B₁, hδ₁, hL, hT⟩ := h4 X D A R
  obtain ⟨C₂, t₂, ht₂, hlow⟩ := h2 X D A R
  obtain ⟨b, hb⟩ := mollifier_exists_bound ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  obtain ⟨C₁, hC₁⟩ : ∃ c : ℝ, c = L + 2 := ⟨_, rfl⟩
  have hC₁3 : 3 ≤ C₁ := by linarith
  obtain ⟨a, ha⟩ : ∃ c : ℝ, c = |Real.log (δ / C₁)| := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ abs_nonneg _
  obtain ⟨B₀', hB₀'⟩ : ∃ c : ℝ, c = max B₀ 0 := ⟨_, rfl⟩
  obtain ⟨C₂', hC₂'⟩ : ∃ c : ℝ, c = max C₂ 0 := ⟨_, rfl⟩
  have hB₀'0 : 0 ≤ B₀' := hB₀' ▸ le_max_right _ _
  have hC₂'0 : 0 ≤ C₂' := hC₂' ▸ le_max_right _ _
  have hC₂C₂' : C₂ ≤ C₂' := hC₂' ▸ le_max_left _ _
  have hlog4 : 0 ≤ Real.log (4 * C₁ ^ 2) := Real.log_nonneg (by nlinarith)
  obtain ⟨E, hE⟩ : ∃ c : ℝ, c = (1 + c₀) * (2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂')) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ c : ℝ, c = max (max E L) (C₂' + |B₁| + 1) := ⟨_, rfl⟩
  have hCE : E ≤ C := hC ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hCL : L ≤ C := hC ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hCB : C₂' + |B₁| + 1 ≤ C := hC ▸ le_max_right _ _
  have hC0 : 0 ≤ C := by linarith [abs_nonneg B₁]
  have hC₁2 : 0 < C₁ + 2 := by linarith
  refine ⟨C, min (min t₂ δ₁) (min (δ / (C₁ + 2)) (Real.exp (-(Real.exp 1 + 2 * a)))),
    lt_min (lt_min ht₂ hδ₁) (lt_min (div_pos hδ hC₁2) (Real.exp_pos _)), ?_⟩
  intro t ht ht₀ K hK
  simp only [lt_min_iff] at ht₀
  obtain ⟨⟨htt₂, htδ₁⟩, htδ, hte⟩ := ht₀
  have hCt : t * (C₁ + 2) < δ := (lt_div_iff₀ hC₁2).1 htδ
  have hCt' : t * (C₁ + 2) = C₁ * t + 2 * t := by ring
  have hC₁t : C₁ * t ≤ δ := by linarith
  have hC₁tlt : C₁ * t < δ := by linarith
  have htLt : t ≤ L * t := le_mul_of_one_le_left ht.le hL
  have hLt : L * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  have h2t : 2 * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  have htC : t ≤ C₁ * t := le_mul_of_one_le_left ht.le (by linarith)
  obtain ⟨hℓa, hlogℓ⟩ := log_inv_facts ht ha0 hte
  have hℓ0 : 0 < Real.log t⁻¹ := by linarith [Real.exp_pos 1]
  have hK0 : 0 ≤ K := le_trans (mul_nonneg hC0 (by linarith)) hK
  have hKB : -K + B₁ ≤ -C₂ * Real.log (Real.log t⁻¹) := by
    have h1' : (C₂' + |B₁| + 1) * Real.log (Real.log t⁻¹) ≤ C * Real.log (Real.log t⁻¹) :=
      mul_le_mul_of_nonneg_right hCB (by linarith)
    have h2' : B₁ ≤ |B₁| * Real.log (Real.log t⁻¹) := by
      have := le_mul_of_one_le_right (abs_nonneg B₁) hlogℓ.le
      linarith [le_abs_self B₁]
    have h3' : C₂ * Real.log (Real.log t⁻¹) ≤ C₂' * Real.log (Real.log t⁻¹) :=
      mul_le_mul_of_nonneg_right hC₂C₂' (by linarith)
    have h4' : (C₂' + |B₁| + 1) * Real.log (Real.log t⁻¹) = C₂' * Real.log (Real.log t⁻¹) +
        |B₁| * Real.log (Real.log t⁻¹) + Real.log (Real.log t⁻¹) := by ring
    have h5' : -C₂ * Real.log (Real.log t⁻¹) = -(C₂ * Real.log (Real.log t⁻¹)) := by ring
    linarith
  have key : ∀ j k : Fin R.N, ∀ x ∈ R.mid j ∩ R.mid k,
      R.phReg ρ K t j x - R.phReg ρ K t k x ≤ E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) + L * t := by
    intro j k x hx
    obtain ⟨hpj, -⟩ := hVpsh j K
    obtain ⟨hpk, hbk⟩ := hVpsh k K
    have hball : ∀ r, r ≤ δ → closedBall (R.chart k x) r ⊆ V k := fun r hr =>
      (closedBall_subset_closedBall hr).trans (hVball k x hx.2)
    have hballj : closedBall (R.chart j x) t ⊆ V j :=
      (closedBall_subset_closedBall (by linarith : t ≤ δ)).trans (hVball j x hx.1)

    have hi : molli ρ t (R.trunc K j) (R.chart j x) ≤ polyMax (R.trunc K j) (R.chart j x) t :=
      (((mollify_thm D ρ (V j) (R.trunc K j) (hVo j) hpj).1 t ht).2.2.2 (R.chart j x) hballj).2

    have hii : polyMax (R.trunc K j) (R.chart j x) t ≤
        max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B₁) +
          (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t :=
      polyMax_le' ht.le fun y hy => hT K j k x hx t ht htδ₁ y hy
    have mono : ∀ s s', 0 ≤ s → s ≤ s' → s' ≤ δ →
        polyMax (R.trunc K k) (R.chart k x) s ≤ polyMax (R.trunc K k) (R.chart k x) s' :=
      fun s s' hs hss' hs' => polyMax_mono' hpk.1 hs hss' (hball _ hs')
    have hlowk := hlow t ht htt₂ K k x hx.2
    have e0 := mono t (L * t) ht.le htLt (by linarith)
    have e1 := mono (L * t) (C₁ * t) (by linarith) hLt hC₁t
    have h4C : 0 < 4 * C₁ := by linarith
    have hq : t / (4 * C₁) ≤ t / 4 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith)
    have e2 := mono (t / (4 * C₁)) (t / 4) (by positivity) hq (by linarith)
    have e3 := mono (t / 4) (2 * t) (by positivity) (by linarith) (by linarith)
    have e4 := mono (2 * t) (C₁ * t) (by positivity) h2t hC₁t
    have e5 := mono t (C₁ * t) ht.le htC hC₁t
    have hmax : max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B₁) =
        polyMax (R.trunc K k) (R.chart k x) (L * t) := max_eq_left (by linarith)
    rw [hmax] at hii

    have hiv := h0 D ρ b (V k) (R.trunc K k) (R.chart k x) t (hVo k) hpk ht
      (hball _ (by linarith)) hb
    rw [← hc₀] at hiv

    have hv := h1 D (V k) (R.trunc K k) (R.chart k x) δ t C₁ (hVo k) hpk (hball δ le_rfl) ht
      (by linarith) hC₁tlt
    have hMδ : polyMax (R.trunc K k) (R.chart k x) δ ≤ B₀' :=
      polyMax_le' hδ.le fun y hy => (hbk y (hVball k x hx.2 hy)).trans
        (max_le (hB₀' ▸ le_max_left _ _) (by linarith))
    have hN : polyMax (R.trunc K k) (R.chart k x) δ - polyMax (R.trunc K k) (R.chart k x) (C₁ * t) ≤
        (B₀' + C₂') * Real.log (Real.log t⁻¹) := by
      have h1' : C₂ * Real.log (Real.log t⁻¹) ≤ C₂' * Real.log (Real.log t⁻¹) :=
        mul_le_mul_of_nonneg_right hC₂C₂' (by linarith)
      have h2' : B₀' ≤ B₀' * Real.log (Real.log t⁻¹) := le_mul_of_one_le_right hB₀'0 hlogℓ.le
      have h3' : -C₂ * Real.log (Real.log t⁻¹) = -(C₂ * Real.log (Real.log t⁻¹)) := by ring
      have h4' : (B₀' + C₂') * Real.log (Real.log t⁻¹) =
          B₀' * Real.log (Real.log t⁻¹) + C₂' * Real.log (Real.log t⁻¹) := by ring
      linarith
    have hden : Real.log t⁻¹ / 2 ≤ Real.log (δ / (C₁ * t)) := by
      rw [show δ / (C₁ * t) = (δ / C₁) * t⁻¹ by field_simp,
        Real.log_mul (div_pos hδ (by linarith)).ne' (inv_pos.2 ht).ne']
      have := neg_abs_le (Real.log (δ / C₁))
      rw [← ha] at this
      linarith [Real.exp_pos 1]
    have hden0 : 0 < Real.log (δ / (C₁ * t)) := by linarith
    have hP : 0 ≤ 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') := by positivity
    have hO : polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁)) ≤
        2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) := by
      refine hv.trans ?_
      rw [div_le_iff₀ hden0]
      calc Real.log (4 * C₁ ^ 2) * (polyMax (R.trunc K k) (R.chart k x) δ -
              polyMax (R.trunc K k) (R.chart k x) (C₁ * t))
          ≤ Real.log (4 * C₁ ^ 2) * ((B₀' + C₂') * Real.log (Real.log t⁻¹)) :=
            mul_le_mul_of_nonneg_left hN hlog4
        _ = 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') *
              (Real.log (Real.log t⁻¹) / Real.log t⁻¹) * (Real.log t⁻¹ / 2) := by
            have hx := div_mul_cancel₀ (Real.log (Real.log t⁻¹)) hℓ0.ne'
            linear_combination (-(Real.log (4 * C₁ ^ 2) * (B₀' + C₂'))) * hx
        _ ≤ 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') *
              (Real.log (Real.log t⁻¹) / Real.log t⁻¹) * Real.log (δ / (C₁ * t)) :=
            mul_le_mul_of_nonneg_left hden (mul_nonneg hP (div_nonneg (by linarith) hℓ0.le))
    have hc : c₀ * (polyMax (R.trunc K k) (R.chart k x) (2 * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / 4)) ≤
        c₀ * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₀0
    have hfin : (1 + c₀) * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) ≤
        E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) := by
      rw [hE]
      have := mul_le_mul_of_nonneg_left hO (by linarith : (0 : ℝ) ≤ 1 + c₀)
      linarith
    have hsum : polyMax (R.trunc K k) (R.chart k x) (L * t) -
          polyMax (R.trunc K k) (R.chart k x) (2 * t) +
          c₀ * (polyMax (R.trunc K k) (R.chart k x) (2 * t) -
            polyMax (R.trunc K k) (R.chart k x) (t / 4)) ≤
        (1 + c₀) * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) := by
      have h' : polyMax (R.trunc K k) (R.chart k x) (L * t) -
          polyMax (R.trunc K k) (R.chart k x) (2 * t) ≤
          polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
            polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁)) := by linarith
      calc _ ≤ (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
              polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) +
            c₀ * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
              polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) := add_le_add h' hc
        _ = _ := by ring
    simp only [RegChartData.phReg, RegChartData.smoothed]
    linarith
  have hr : 0 ≤ Real.log (Real.log t⁻¹) / Real.log t⁻¹ := div_nonneg (by linarith) hℓ0.le
  intro j k x hx
  have hEC : E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) + L * t ≤
      C * Real.log (Real.log t⁻¹) / Real.log t⁻¹ + C * t := by
    rw [mul_div_assoc]
    have := mul_le_mul_of_nonneg_right hCE hr
    have := mul_le_mul_of_nonneg_right hCL ht.le
    linarith
  exact abs_sub_le_iff.2 ⟨(key j k x hx).trans hEC, (key k j x ⟨hx.2, hx.1⟩).trans hEC⟩

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PMaxOscillation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric

noncomputable section

theorem PolyMaxOscillation.proof (h0 : ReciprocityTheory.AnForm.A.PolyMaxLogConvexStatement) :
    PolyMaxOscillation.Statement := by
  intro D U u z δ t C₁ hU hu hδ ht hC hCt
  have hC0 : 0 < C₁ := by linarith
  have hb0 : 0 < C₁ * t := mul_pos hC0 ht
  have hδ0 : 0 < δ := hb0.trans hCt
  have hconv := (h0 D U u z δ hU hu hδ0 hδ).1
  have ha0 : 0 < t / (4 * C₁) := by positivity
  have hab : t / (4 * C₁) < C₁ * t := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have key := hconv.slope_mono_adjacent
    (Set.mem_Iic.2 (Real.log_le_log ha0 (hab.trans hCt).le)) (Set.mem_Iic.2 le_rfl)
    (Real.log_lt_log ha0 hab) (Real.log_lt_log hb0 hCt)
  simp only [Real.exp_log ha0, Real.exp_log hb0, Real.exp_log hδ0] at key
  have h1 : Real.log (C₁ * t) - Real.log (t / (4 * C₁)) = Real.log (4 * C₁ ^ 2) := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    congr 1
    field_simp
  have h2 : Real.log δ - Real.log (C₁ * t) = Real.log (δ / (C₁ * t)) :=
    (Real.log_div hδ0.ne' hb0.ne').symm
  have hL1 : 0 < Real.log (4 * C₁ ^ 2) := by
    rw [← h1]
    exact sub_pos.2 (Real.log_lt_log ha0 hab)
  rw [h1, h2, div_le_iff₀ hL1] at key
  rw [mul_div_assoc, mul_comm (Real.log (4 * C₁ ^ 2))]
  exact key

theorem PolyMaxOscillation.proof_closed : PolyMaxOscillation.Statement :=
  PolyMaxOscillation.proof ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm

end

end GroundTheory.Heights₂.Heights.Regular
end

