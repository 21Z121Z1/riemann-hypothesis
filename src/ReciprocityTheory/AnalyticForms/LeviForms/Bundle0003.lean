import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0002
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt

-- bundled from ReciprocityTheory.AnalyticForms.LeviForms.ProjectiveLineLogLogRegularized
section
namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def projectiveLineLogLog (y : OnePoint ℂ) : ℝ := -Real.log (rW fsPot projectiveLinePairSection y)

def projectiveLineLogLogRegularized (t : ℝ) (y : OnePoint ℂ) : ℝ :=
  if projectiveLinePairSection y y = 0 then -Real.log (Real.log (1 / t)) else
    ReciprocityTheory.AnForm.A.regMax (epsT 1 t) ![projectiveLineLogLog y, -Real.log (Real.log (1 / t))]

def ProjectiveLineLogLogInhabited : Prop :=
  (∀ y, logNormSec fsPot projectiveLinePairSection y ≤ 0) ∧ IsSingWeight p1 fsPot projectiveLinePairSection fsPot projectiveLineLogLog 1 ∧
    ∃ C t₀ : ℝ, IsRegFamily p1 fsPot fsPot projectiveLinePairSection fsPot projectiveLineLogLog projectiveLineLogLogRegularized C t₀ ∧
      IsRegFamilyC2 p1 projectiveLinePairSection projectiveLineLogLog projectiveLineLogLogRegularized

theorem projectiveLine_isRegFamily : IsRegFamily p1 fsPot fsPot projectiveLinePairSection fsPot llw llT 2 T0 := by
  refine ⟨Real.exp_pos _, (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (neg_lt_zero.2 (Real.exp_pos _))), fun t ht ht0 => ?_⟩
  have hη := eps_pos ht ht0
  have hL := logell_pos ht ht0
  have hℓ := ell_pos ht ht0
  have hr3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
  refine ⟨llT_smooth t ht ht0, ?_, ?_, ?_, llT_psh t ht ht0, ?_, ?_, ?_⟩
  · intro y
    by_cases hy : y = OnePoint.infty
    · subst hy; rw [llT_infty]; linarith
    · rw [llT_ne t hy]
      have := rm_le (η := epsT 1 t) (a := llw y) (b := -Real.log (Real.log (1 / t))) (m := 0) hη.le
        (by linarith [projectiveLineLogLog_le_neg_one y]) (by linarith)
      linarith [eps_le_one ht ht0]
  · intro y hy
    rw [llT_ne t (fun h => hy ((mem_boundary_projectiveLine y).2 h))]
    exact rm_ge_left _ _ _
  · intro y
    by_cases hy : y = OnePoint.infty
    · subst hy; rw [llT_infty]; linarith
    · rw [llT_ne t hy]
      have := rm_ge_right (epsT 1 t) (llw y) (-Real.log (Real.log (1 / t)))
      linarith
  · intro y hy hr
    rw [llT_ne t (fun h => hy ((mem_boundary_projectiveLine y).2 h)), epsT_two]
    have hc : -Real.log (Real.log (1 / t)) ≤ llw y := by
      rw [llw]; exact neg_le_neg (Real.log_le_log (rW_pos y) hr)
    have := rm_le hη.le (le_refl (llw y)) hc
    linarith
  · intro y hy
    rw [llT_ne t (fun h => hy ((mem_boundary_projectiveLine y).2 h)), epsT_two]
    have hrp := rW_pos y
    have hre := projectiveLine_weight_ge_exp_one y
    have h1 : Real.log (rW fsPot projectiveLinePairSection y) - Real.log (Real.log (1 / t)) ≤
        rW fsPot projectiveLinePairSection y / Real.log (1 / t) := by
      rw [← Real.log_div hrp.ne' hℓ.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hrp hℓ)
      linarith
    have h2 : rW fsPot projectiveLinePairSection y / Real.log (1 / t) ≤ epsT 1 t * rW fsPot projectiveLinePairSection y := by
      have e : epsT 1 t * rW fsPot projectiveLinePairSection y =
          Real.log (Real.log (1 / t)) * rW fsPot projectiveLinePairSection y / Real.log (1 / t) := by
        unfold epsT; ring
      rw [e]
      apply div_le_div_of_nonneg_right _ hℓ.le
      have := logell_big ht ht0
      nlinarith [one_le_exp_one]
    have hc : -Real.log (Real.log (1 / t)) ≤ llw y + epsT 1 t * rW fsPot projectiveLinePairSection y := by
      rw [llw]; linarith
    have hm : llw y ≤ llw y + epsT 1 t * rW fsPot projectiveLinePairSection y := by
      have := mul_nonneg hη.le hrp.le; linarith
    have := rm_le hη.le hm hc
    have h5 : epsT 1 t / 2 ≤ epsT 1 t * rW fsPot projectiveLinePairSection y := by nlinarith [one_le_exp_one]
    linarith
  · intro t' htt' ht0' y
    have ht' : 0 < t' := lt_of_lt_of_le ht htt'
    have hη' := eps_pos ht' ht0'
    have hmono := eps_mono ht htt' ht0'
    have hc : -Real.log (Real.log (1 / t)) ≤ -Real.log (Real.log (1 / t')) :=
      neg_le_neg (Real.log_le_log (ell_pos ht' ht0') (ell_anti ht htt'))
    rw [epsT_two]
    by_cases hy : y = OnePoint.infty
    · subst hy; rw [llT_infty, llT_infty]; linarith
    · rw [llT_ne t hy, llT_ne t' hy]
      have := rm_le (m := ReciprocityTheory.AnForm.A.regMax (epsT 1 t') ![llw y, -Real.log (Real.log (1 / t'))])
        hη.le (rm_ge_left _ _ _) (le_trans hc (rm_ge_right _ _ _))
      linarith

theorem tuo_of_eventually {α β : Type*} [UniformSpace β] {F : ℝ → α → β} {f : α → β}
    {p : Filter ℝ} {K : Set α} (h : ∀ᶠ t in p, ∀ y ∈ K, F t y = f y) :
    TendstoUniformlyOn F f p K := by
  intro u hu
  filter_upwards [h] with t ht y hy
  rw [ht y hy]
  exact refl_mem_uniformity hu

theorem regFamilyC2_of_chart (j : Fin 2) (K : Set (Fin 1 → ℂ))
    (hK : K ⊆ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ) (hKc : IsCompact K) :
    TendstoUniformlyOn (fun t => llT t ∘ (p1.chart j).symm) (llw ∘ (p1.chart j).symm)
        (nhdsWithin 0 (Set.Ioi 0)) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (llT t ∘ (p1.chart j).symm))
        (fderiv ℝ (llw ∘ (p1.chart j).symm)) (nhdsWithin 0 (Set.Ioi 0)) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (llT t ∘ (p1.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (llw ∘ (p1.chart j).symm))) (nhdsWithin 0 (Set.Ioi 0)) K := by
  have hVeq : (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ =
      {w | j = 1 → w 0 ≠ 0} := Set.ext fun w => chartV_iff j w
  have hVo : IsOpen ((p1.chart j).target ∩ (p1.chart j).symm ⁻¹' (bdry projectiveLinePairSection)ᶜ) := by
    rw [hVeq]; exact isOpen_goodSet j
  obtain ⟨δ, hδ, hδV⟩ := hKc.exists_cthickening_subset_open hVo hK
  have hC : IsCompact (Metric.cthickening δ K) := hKc.cthickening
  have hgc : ContinuousOn (fun w => -Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)))
      (Metric.cthickening δ K) :=
    (contDiffOn_llwChart j).continuousOn.mono (fun w hw => (chartV_iff j w).1 (hδV hw))
  obtain ⟨m, hm⟩ := hC.bddBelow_image hgc
  have hT : 0 < min T0 (Real.exp (-Real.exp (1 - m))) := lt_min (Real.exp_pos _) (Real.exp_pos _)
  have hev : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ w ∈ Metric.cthickening δ K,
      llT t ((p1.chart j).symm w) = llw ((p1.chart j).symm w) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    intro w hw
    have ht0 : t ≤ T0 := le_trans ht.2.le (min_le_left _ _)
    have ht1 : t ≤ Real.exp (-Real.exp (1 - m)) := le_trans ht.2.le (min_le_right _ _)
    have hwj : j = 1 → w 0 ≠ 0 := (chartV_iff j w).1 (hδV hw)
    rw [llT_chart_eq t j w hwj, projectiveLineLogLog_chart j w hwj]
    apply rm_eq_left (eps_pos ht.1 ht0).le
    have h1 : Real.exp (1 - m) ≤ Real.log (1 / t) := ell_ge ht.1 ht1
    have h2 : 1 - m ≤ Real.log (Real.log (1 / t)) := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    have h3 := eps_le_one ht.1 ht0
    have h4 : m ≤ -Real.log (Real.exp 1 + 2 * fsGk j (fsQ w)) := hm ⟨w, hw, rfl⟩
    linarith
  have hloc : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ y ∈ K,
      (llT t ∘ (p1.chart j).symm) =ᶠ[𝓝 y] (llw ∘ (p1.chart j).symm) := by
    filter_upwards [hev] with t ht y hy
    have hmem : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening hδ K hy)
    filter_upwards [hmem] with w hw
    exact ht w (Metric.thickening_subset_cthickening δ K hw)
  refine ⟨tuo_of_eventually ?_, tuo_of_eventually ?_, tuo_of_eventually ?_⟩
  · filter_upwards [hloc] with t ht y hy
    exact (ht y hy).eq_of_nhds
  · filter_upwards [hloc] with t ht y hy
    exact (ht y hy).fderiv_eq (𝕜 := ℝ)
  · filter_upwards [hloc] with t ht y hy
    exact ((ht y hy).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)

theorem projectiveLine_isRegFamilyC2 : IsRegFamilyC2 p1 projectiveLinePairSection llw llT :=
  fun j K hK hKc => regFamilyC2_of_chart j K hK hKc

theorem isRegFamily_inhabited : IsRegFamilyInhabitStatement := by
  intro e X _ A Θ L s hΘ hpos hL
  have hT : (0 : ℝ) < Real.exp (-Real.exp 1) := Real.exp_pos _
  have hT1 : Real.exp (-Real.exp 1) < 1 := (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (neg_lt_zero.2 (Real.exp_pos _)))
  have hεnn : ∀ t, 0 < t → t ≤ Real.exp (-Real.exp 1) → 0 ≤ epsT 1 t := by
    intro t ht ht0
    have h1 : Real.exp 1 ≤ Real.log (1 / t) := ell_ge ht ht0
    have h2 : 0 ≤ Real.log (Real.log (1 / t)) :=
      Real.log_nonneg (by linarith [one_le_exp_one])
    unfold epsT
    rw [one_mul]
    exact div_nonneg h2 (by linarith [Real.exp_pos 1])
  have hlog : ∀ t, 0 < t → t ≤ Real.exp (-Real.exp 1) → 0 ≤ Real.log (Real.log (1 / t)) := by
    intro t ht ht0
    have h1 : Real.exp 1 ≤ Real.log (1 / t) := ell_ge ht ht0
    exact Real.log_nonneg (by linarith [one_le_exp_one])
  refine ⟨⟨hT, hT1, fun t ht ht0 => ?_⟩, fun j K _ _ => ⟨?_, ?_, ?_⟩⟩
  · have hε := hεnn t ht ht0
    have hr3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
    refine ⟨fun j => contDiffOn_const, fun _ => zero_le_one, fun _ _ => le_refl _,
      fun _ => by linarith [hlog t ht ht0], ?_, fun _ _ _ => by linarith,
      fun y _ => ?_, fun t' htt' ht0' _ => ?_⟩
    · intro x j y hy w
      have hyD : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
      have hc : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y :=
        ((hΘ.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm
          (Θ.isOpen_U x)).mem_nhds hyD)).of_le two_le_inf
      have h0 : 0 ≤ levi (Θ.φ x ∘ (A.chart j).symm) y w := by
        by_cases hw : w = 0
        · rw [hw, levi_zero]
        · exact (hpos x j y hyD w hw).le
      show 0 ≤ levi (fun z => Θ.φ x ((A.chart j).symm z) + 0 +
        epsT 1 t * Θ.φ x ((A.chart j).symm z)) y w
      simp only [add_zero]
      rw [levi_add_smul (f := fun z => Θ.φ x ((A.chart j).symm z))
        (g := fun z => Θ.φ x ((A.chart j).symm z)) (epsT 1 t) hc hc w]
      have := mul_nonneg hε h0
      exact add_nonneg h0 this
    · have h1 : Real.exp 1 ≤ rW L s y := by
        have := hL y; unfold rW; linarith
      have := mul_nonneg hε (le_trans (Real.exp_pos 1).le h1)
      linarith
    · have := hεnn t' (lt_of_lt_of_le ht htt') ht0'
      linarith
  · exact tuo_of_eventually (Eventually.of_forall fun _ _ _ => rfl)
  · exact tuo_of_eventually (Eventually.of_forall fun _ _ _ => rfl)
  · exact tuo_of_eventually (Eventually.of_forall fun _ _ _ => rfl)

theorem projectiveLineLogLog_inhabited : ProjectiveLineLogLogInhabited :=
  ⟨fun y => logNormSec_nonpos y, singWeight, 2, T0, projectiveLine_isRegFamily, projectiveLine_isRegFamilyC2⟩

theorem isRegFamilyInhabit : IsRegFamilyInhabitStatement := isRegFamily_inhabited

end

end ReciprocityTheory.AnForm.P
end

-- bundled from ReciprocityTheory.AnalyticForms.LeviForms.RegChart
section
namespace ReciprocityTheory.AnForm.P

open MeasureTheory Metric
open scoped ContDiff

noncomputable section

def polyMaxOff {D : ℕ} (S : Finset (Fin D)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ) : ℝ :=
  sSup (φ '' (closedBall z t \ ReciprocityTheory.AnForm.A.coordDiv S))

def PolyMaxOscStatement : Prop :=
  ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ : ℝ),
    (∀ i ∈ S, 1 ≤ m i) →
    ContinuousOn u (ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S) →
    ReciprocityTheory.AnForm.A.IsPsh (ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S) u →
    (∀ z ∈ ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S,
      -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅) →
    ∀ C₁ : ℝ, 1 ≤ C₁ → ∃ C t₀ : ℝ, 0 < t₀ ∧ t₀ < 1 ∧ ∀ t, 0 < t → t ≤ t₀ →
      ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4),
        -C * Real.log (Real.log (1 / t)) ≤ polyMaxOff S u z (t / (4 * C₁)) ∧
        polyMaxOff S u z (C₁ * t) - polyMaxOff S u z (t / (4 * C₁)) ≤ epsT C t

def RegChartStatement : Prop :=
  ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (q ph : (Fin D → ℂ) → ℝ) (C₅ K : ℝ),
    (∀ i ∈ S, 1 ≤ m i) →
    ContDiffOn ℝ ∞ q (ball 0 2) →
    ContDiffOn ℝ ∞ ph (ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S) →
    ReciprocityTheory.AnForm.A.IsLeviPsh (ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S) (fun z => q z + ph z) →
    (∀ z ∈ ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S,
      -C₅ * Real.log (rLoc S m z) ≤ ph z ∧ ph z ≤ C₅) →
    (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S,
      ‖fderiv ℝ ph z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) →
    ∃ (C t₀ : ℝ) (phT : ℝ → (Fin D → ℂ) → ℝ), 0 < t₀ ∧ t₀ < 1 ∧
      (∀ t, 0 < t → t ≤ t₀ →
        ContDiffOn ℝ ∞ (phT t) (ball 0 (5 / 4)) ∧
        ReciprocityTheory.AnForm.A.IsLeviPsh (ball 0 (5 / 4)) (fun z => q z + phT t z) ∧
        (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4),
          phT t z ≤ C ∧ -C * Real.log (Real.log (1 / t)) ≤ phT t z) ∧
        (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S,
          ph z ≤ phT t z ∧ phT t z ≤ ph z + t ^ ((1 : ℝ) / 3) + epsT C t * rLoc S m z ∧
          (rLoc S m z ≤ Real.log (1 / t) + K → phT t z ≤ ph z + t ^ ((1 : ℝ) / 3))) ∧
        (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4),
          polyMaxOff S (fun x => q x + ph x) z t - epsT C t ≤ q z + phT t z ∧
            q z + phT t z ≤ polyMaxOff S (fun x => q x + ph x) z t) ∧
        ∀ t', t ≤ t' → t' ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4),
          phT t z ≤ phT t' z + C * epsT C t') ∧
      ∀ K ⊆ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, IsCompact K →
        TendstoUniformlyOn phT ph (nhdsWithin 0 (Set.Ioi 0)) K ∧
        TendstoUniformlyOn (fun t => fderiv ℝ (phT t)) (fderiv ℝ ph) (nhdsWithin 0 (Set.Ioi 0)) K ∧
        TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT t))) (fderiv ℝ (fderiv ℝ ph))
          (nhdsWithin 0 (Set.Ioi 0)) K

end

end ReciprocityTheory.AnForm.P
end

-- bundled from ReciprocityTheory.AnalyticForms.LeviForms.RegChartA
section
namespace ReciprocityTheory.AnForm.P.RegularChartScaling

open MeasureTheory Metric Filter Topology Set
open ReciprocityTheory.AnForm.A

noncomputable section

variable {D : ℕ}

lemma isPsh_mono {U V : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (h : IsPsh U φ) (hVU : V ⊆ U) :
    IsPsh V φ :=
  ⟨h.1.mono hVU, fun z w hzw => h.2 z w fun ζ hζ => hVU (hzw ζ hζ)⟩

lemma isPsh_scale {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (h : IsPsh U φ) (c : ℝ) :
    IsPsh {y | c • y ∈ U} (fun y => φ (c • y)) := by
  refine ⟨fun y hy t ht => ?_, fun z w hzw => ?_⟩
  · have hc : ContinuousWithinAt (fun y : Fin D → ℂ => c • y) {y | c • y ∈ U} y :=
      (continuous_const_smul c).continuousWithinAt
    exact (hc.tendsto_nhdsWithin (fun y hy => hy)).eventually (h.1 (c • y) hy t ht)
  · have e : ∀ ζ : ℂ, c • (z + ζ • w) = c • z + ζ • (c • w) := fun ζ => by
      rw [smul_add, smul_comm c ζ w]
    have := h.2 (c • z) (c • w) fun ζ hζ => by
      rw [← e]
      exact hzw ζ hζ
    simp only [e]
    exact this

lemma exists_far_point (z : Fin D → ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ x ∈ closedBall z s, (∀ i, s ≤ ‖x i‖) ∧ ‖x‖ ≤ ‖z‖ + s := by
  classical
  let u : Fin D → ℂ := fun i => if z i = 0 then 1 else z i / (‖z i‖ : ℂ)
  have hu : ∀ i, ‖u i‖ = 1 := by
    intro i
    by_cases h : z i = 0
    · simp [u, h]
    · simp only [u, if_neg h, norm_div, Complex.norm_real, norm_norm]
      exact div_self (norm_ne_zero_iff.mpr h)
  let w : Fin D → ℂ := fun i => (s : ℂ) * u i
  have hw : ‖w‖ ≤ s := by
    refine (pi_norm_le_iff_of_nonneg hs.le).mpr fun i => ?_
    simp [w, norm_mul, hu, abs_of_pos hs]
  refine ⟨z + w, ?_, fun i => ?_, (norm_add_le _ _).trans (by linarith)⟩
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hw
  · by_cases h : z i = 0
    · simp [w, u, h, abs_of_pos hs]
    · have hzi : 0 < ‖z i‖ := norm_pos_iff.mpr h
      have hc : (‖z i‖ : ℂ) ≠ 0 := by exact_mod_cast hzi.ne'
      have e : (z + w) i = ((‖z i‖ + s) / ‖z i‖ : ℝ) * z i := by
        simp only [Pi.add_apply, w, u, if_neg h]
        push_cast
        field_simp
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_cancel₀ _ hzi.ne']
      linarith

lemma not_mem_coordDiv_of {S : Finset (Fin D)} {x : Fin D → ℂ} {s : ℝ} (hs : 0 < s)
    (h : ∀ i, s ≤ ‖x i‖) : x ∉ coordDiv S := by
  rintro ⟨i, -, hi⟩
  have := h i
  rw [hi, norm_zero] at this
  linarith

lemma smul_mem_coordDiv_iff {S : Finset (Fin D)} {c : ℝ} (hc : c ≠ 0) (x : Fin D → ℂ) :
    c • x ∈ coordDiv S ↔ x ∈ coordDiv S := by
  simp only [coordDiv, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_zero, hc, false_or]

lemma mem_ball_smul_iff {R : ℝ} (hR : 0 < R) (y : Fin D → ℂ) :
    R • y ∈ ball (0 : Fin D → ℂ) R ↔ y ∈ ball (0 : Fin D → ℂ) 1 := by
  simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  exact mul_lt_iff_lt_one_right hR

lemma mem_closure_off (S : Finset (Fin D)) {R : ℝ} {y : Fin D → ℂ} (hy : y ∈ ball (0 : Fin D → ℂ) R) :
    y ∈ closure (ball (0 : Fin D → ℂ) R \ coordDiv S) := by
  classical
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hyR : ‖y‖ < R := by simpa using hy
  set m := min ε (R - ‖y‖) with hm
  have hm0 : 0 < m := lt_min hε (by linarith)
  have hfin : {t : ℝ | ∃ i, y i + (t : ℂ) = 0}.Finite := by
    have hsub : {t : ℝ | ∃ i, y i + (t : ℂ) = 0} ⊆ Set.range (fun i => -(y i).re) := by
      rintro t ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have := congrArg Complex.re hi
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
      show -(y i).re = t
      linarith
    exact (Set.finite_range _).subset hsub
  obtain ⟨t, ⟨ht0, htm⟩, htbad⟩ := ((Set.Ioo_infinite hm0).diff hfin).nonempty
  have hc : ‖fun _ : Fin D => (t : ℂ)‖ ≤ t :=
    (pi_norm_le_iff_of_nonneg ht0.le).mpr fun i => by simp [abs_of_pos ht0]
  refine ⟨y + fun _ => (t : ℂ), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_zero_right]
    have := min_le_right ε (R - ‖y‖)
    calc ‖y + fun _ => (t : ℂ)‖ ≤ ‖y‖ + ‖fun _ : Fin D => (t : ℂ)‖ := norm_add_le _ _
      _ < R := by linarith
  · rintro ⟨i, -, hi⟩
    exact htbad ⟨i, by simpa using hi⟩
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
    have := min_le_left ε (R - ‖y‖)
    linarith

open Classical in

def extT (S : Finset (Fin D)) (R : ℝ) (v : (Fin D → ℂ) → ℝ) (κ : ℝ) (x : Fin D → ℂ) : ℝ :=
  limsupExt (ball (0 : Fin D → ℂ) 1) (coordDiv S) (fun y => max (v (R • y)) (-κ)) (R⁻¹ • x)

lemma ext_exists (S : Finset (Fin D)) {R : ℝ} (hR : 0 < R) {u : (Fin D → ℂ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hc : ContinuousOn u (ball 0 R \ coordDiv S))
    (hp : IsPsh (ball 0 R \ coordDiv S) u) (hub : ∀ x ∈ ball 0 R \ coordDiv S, u x ≤ B)
    (κ : ℝ) :
    ∃ w : (Fin D → ℂ) → ℝ, w = extT S R u κ ∧ IsPsh (ball 0 R) w ∧
      (∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, w x = max (u x) (-κ)) ∧
      ∀ x ∈ ball (0 : Fin D → ℂ) R, ∀ δ > 0, ∃ y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S,
        dist y x < δ ∧ w x ≤ max (u y) (-κ) + δ := by
  classical
  set v : (Fin D → ℂ) → ℝ := fun y => u (R • y) with hv
  have hmemR : ∀ y : Fin D → ℂ, R • y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S ↔
      y ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S := by
    intro y
    rw [Set.mem_diff, Set.mem_diff, mem_ball_smul_iff hR, smul_mem_coordDiv_iff hR.ne']
  have hset : {y : Fin D → ℂ | R • y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S} =
      ball (0 : Fin D → ℂ) 1 \ coordDiv S := by
    ext y
    exact hmemR y
  have hvc : ContinuousOn v (ball (0 : Fin D → ℂ) 1 \ coordDiv S) :=
    hc.comp (continuous_const_smul R).continuousOn fun y hy => (hmemR y).mpr hy
  have hvp : IsPsh (ball (0 : Fin D → ℂ) 1 \ coordDiv S) v := by
    have := isPsh_scale hp R
    rwa [hset] at this
  have hvb : ∀ z ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S,
      v z ≤ B * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖z i‖⁻¹) := by
    intro z hz
    have h1 : v z ≤ B := hub _ ((hmemR z).mpr hz)
    have hsum : 0 ≤ ∑ i ∈ S, Real.log ‖z i‖⁻¹ := by
      refine Finset.sum_nonneg fun i hi => ?_
      have hzi : z i ≠ 0 := fun h0 => hz.2 ⟨i, hi, h0⟩
      have hlt : ‖z i‖ ≤ 1 := by
        have h3 := norm_le_pi_norm z i
        have h2 : ‖z‖ < 1 := by simpa using hz.1
        linarith
      apply Real.log_nonneg
      rw [one_le_inv₀ (norm_pos_iff.mpr hzi)]
      exact hlt
    have hlog : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖z i‖⁻¹) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hlog hB]
  have hext := (pshExtension_thm D S (ball 0 1) v B isOpen_ball subset_rfl hvc hvp hvb).2 κ
  refine ⟨extT S R u κ, rfl, ?_, ?_, ?_⟩
  · have h4 := isPsh_scale hext R⁻¹
    have hset2 : {x : Fin D → ℂ | R⁻¹ • x ∈ ball (0 : Fin D → ℂ) 1} = ball 0 R := by
      ext x
      simp only [Set.mem_setOf_eq]
      rw [← mem_ball_smul_iff hR, smul_inv_smul₀ hR.ne']
    rw [hset2] at h4
    exact h4
  · intro x hx
    have hx' : R⁻¹ • x ∉ coordDiv S := by
      rw [smul_mem_coordDiv_iff (inv_ne_zero hR.ne')]
      exact hx.2
    simp only [extT, limsupExt, if_neg hx', smul_inv_smul₀ hR.ne']
  · intro x hx δ hδ
    by_cases hxA : x ∈ coordDiv S
    · set x' := R⁻¹ • x with hx'
      have hxeq : R • x' = x := by rw [hx', smul_inv_smul₀ hR.ne']
      have hx'A : x' ∈ coordDiv S := (smul_mem_coordDiv_iff (inv_ne_zero hR.ne') x).mpr hxA
      have hx'U : x' ∈ ball (0 : Fin D → ℂ) 1 := by
        rw [← mem_ball_smul_iff hR, hxeq]
        exact hx
      set F : (Fin D → ℂ) → ℝ := fun y => max (u (R • y)) (-κ) with hF
      have hw : extT S R u κ x = limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') := by
        simp only [extT, limsupExt]
        rw [if_pos ((smul_mem_coordDiv_iff (inv_ne_zero hR.ne') x).mpr hxA)]
      haveI : (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x').NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_off S hx'U)
      have hcob : IsCoboundedUnder (· ≤ ·) (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') F :=
        isCoboundedUnder_le_of_le _ (fun y => le_max_right _ _)
      have hfreq := frequently_lt_of_lt_limsup hcob
        (show limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') - δ <
          limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') by linarith)
      have hev : ∀ᶠ y in 𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x',
          y ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S ∧ dist y x' < δ / R :=
        Filter.Eventually.and eventually_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x' (div_pos hδ hR)))
      obtain ⟨y, hy1, hy2, hy3⟩ := (hfreq.and_eventually hev).exists
      refine ⟨R • y, (hmemR y).mpr hy2, ?_, ?_⟩
      · rw [← hxeq, dist_smul₀, Real.norm_eq_abs, abs_of_pos hR]
        calc R * dist y x' < R * (δ / R) := mul_lt_mul_of_pos_left hy3 hR
          _ = δ := by field_simp
      · have hFy : F y = max (u (R • y)) (-κ) := rfl
        rw [hw]
        linarith
    · have hx' : R⁻¹ • x ∉ coordDiv S := by
        rw [smul_mem_coordDiv_iff (inv_ne_zero hR.ne')]
        exact hxA
      have hwx : extT S R u κ x = max (u x) (-κ) := by
        simp only [extT, limsupExt, if_neg hx', smul_inv_smul₀ hR.ne']
      exact ⟨x, ⟨hx, hxA⟩, by simp [hδ], by linarith⟩

end

end ReciprocityTheory.AnForm.P.RegularChartScaling
end

