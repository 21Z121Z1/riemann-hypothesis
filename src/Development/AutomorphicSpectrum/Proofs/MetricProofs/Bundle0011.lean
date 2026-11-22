import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothExtensionAcrossClosedDense
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothGlue

theorem continuousAt_of_smoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {N : Set X} {E : X → ℝ} (hN : IsOpen N) (hS : A.SmoothOn N E) {p : X} (hp : p ∈ N) :
    ContinuousAt E p := by
  obtain ⟨j, hj⟩ := A.cover p
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N) :=
    (A.chart j).isOpen_inter_preimage_symm hN
  have hz : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' N := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simpa [Set.mem_preimage, (A.chart j).left_inv hj] using hp
  have h1 : ContinuousAt (E ∘ (A.chart j).symm) (A.chart j p) :=
    ((hS j).continuousOn).continuousAt (hopen.mem_nhds hz)
  have h2 : ContinuousAt (A.chart j) p := (A.chart j).continuousAt hj
  have h1' : ContinuousAt (E ∘ (A.chart j).symm) ((A.chart j) p) := h1
  have h3 : ContinuousAt ((E ∘ (A.chart j).symm) ∘ (A.chart j)) p :=
    ContinuousAt.comp h1' h2
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

theorem eq_of_dense_compl {X : Type} [TopologicalSpace X] {B W : Set X} {f g : X → ℝ}
    (hD : Dense Bᶜ) (hW : IsOpen W) (hf : ∀ p ∈ W, ContinuousAt f p)
    (hg : ∀ p ∈ W, ContinuousAt g p) (hfg : ∀ y ∈ W, y ∉ B → f y = g y) :
    ∀ y ∈ W, f y = g y := by
  intro y hy
  by_contra hne
  have hc : ContinuousAt (fun w => f w - g w) y := (hf y hy).sub (hg y hy)
  have hev : ∀ᶠ w in 𝓝 y, f w - g w ≠ 0 := hc.eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨w, hwB, hw1, hw2⟩ := hD.inter_nhds_nonempty (hev.and (hW.mem_nhds hy))
  exact hw1 (sub_eq_zero.mpr (hfg w hw2 hwB))

theorem glue : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (u : X → ℝ), IsClosed B → Dense Bᶜ → (∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ B → E y = u y) → ∃ u' : X → ℝ, A.Smooth u' ∧ ∀ y ∉ B, u' y = u y := by
  intro e X _ A B u _ hD h
  classical
  choose N E hN hx hS hE using h
  have hagree : ∀ x y, ∀ w ∈ N x ∩ N y, E x w = E y w := by
    intro x y
    refine eq_of_dense_compl hD ((hN x).inter (hN y))
      (fun p hp => continuousAt_of_smoothOn A (hN x) (hS x) hp.1)
      (fun p hp => continuousAt_of_smoothOn A (hN y) (hS y) hp.2) ?_
    intro w hw hwB
    rw [hE x w hw.1 hwB, hE y w hw.2 hwB]
  refine ⟨fun y => if y ∈ B then E y y else u y, ?_, ?_⟩
  · have hu' : ∀ x, ∀ y ∈ N x, (if y ∈ B then E y y else u y) = E x y := by
      intro x y hy
      by_cases hB : y ∈ B
      · rw [if_pos hB]
        exact hagree y x y ⟨hx y, hy⟩
      · rw [if_neg hB]
        exact (hE x y hy hB).symm
    intro j z hz
    have hzt : z ∈ (A.chart j).target := hz.1
    set x := (A.chart j).symm z with hxdef
    have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N x) :=
      (A.chart j).isOpen_inter_preimage_symm (hN x)
    have hzm : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' N x := ⟨hzt, hx x⟩
    have hc : ContDiffAt ℝ ∞ (E x ∘ (A.chart j).symm) z :=
      (hS x j).contDiffAt (hopen.mem_nhds hzm)
    refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hopen.mem_nhds hzm] with w hw
    exact hu' x _ hw.2
  · intro y hy
    simp [hy]

end GlobalTheory.CompanionTheory.SmoothGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChart
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem bdry_snc_chart :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
      (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X),
      IsSection A L s → IsSNC A L s m W → ∀ x,
        ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
          ∃ S : Finset (Fin e), ∀ y ∈ ψ.source, (y ∈ bdry s ↔ ∃ i ∈ S, ψ y i = 0) := by
  classical
  intro e X _ A L s nb m W hs hsnc x
  obtain ⟨ψ, hψ, hx, hsub, σ, -, -, u, -, hu, hfac⟩ := hsnc x
  refine ⟨ψ, hψ, hx, Finset.univ.filter (fun i => ∃ k, σ k = some i ∧ m k ≠ 0), ?_⟩
  intro y hy
  have hglue := hs.2 x y y ⟨hsub hy, L.mem_U y⟩
  have hzero : s y y = 0 ↔ s x y = 0 := by
    have e1 : Real.exp (-L.φ x y) ≠ 0 := (Real.exp_pos _).ne'
    have e2 : Real.exp (-L.φ y y) ≠ 0 := (Real.exp_pos _).ne'
    constructor
    · intro h
      rw [h, norm_zero, zero_mul] at hglue
      exact norm_eq_zero.mp ((mul_eq_zero.mp hglue).resolve_right e1)
    · intro h
      rw [h, norm_zero, zero_mul] at hglue
      exact norm_eq_zero.mp ((mul_eq_zero.mp hglue.symm).resolve_right e2)
  have hmem : y ∈ bdry s ↔ s y y = 0 := Iff.rfl
  rw [hmem, hzero, hfac y hy, mul_eq_zero, or_iff_right (hu y hy), Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    cases hσ : σ k with
    | none => simp [hσ] at hk
    | some i =>
      simp only [hσ] at hk
      have hm : m k ≠ 0 := by
        intro h
        rw [h, pow_zero] at hk
        exact one_ne_zero hk
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, k, hσ, hm⟩, pow_eq_zero_iff hm |>.mp hk⟩
  · rintro ⟨i, hi, h0⟩
    obtain ⟨k, hk, hm⟩ := (Finset.mem_filter.mp hi).2
    refine ⟨k, Finset.mem_univ k, ?_⟩
    simp only [hk]
    rw [h0, zero_pow hm]

end GlobalTheory.CompanionTheory.Metric
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeakConvergenceOffZeroSet
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.UClose

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem trunc_pos_den {a δ : ℝ} (hδ : 0 < δ) : 0 < a ^ 2 + δ := by positivity

theorem trunc_continuous {N : X → ℝ} (hN : Continuous N) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Continuous fun y => Real.log (1 + ε / (N y ^ 2 + δ)) := by
  have hden : Continuous fun y => N y ^ 2 + δ := by fun_prop
  have hq : Continuous fun y => 1 + ε / (N y ^ 2 + δ) :=
    continuous_const.add (continuous_const.div hden fun y => (trunc_pos_den hδ).ne')
  refine hq.log fun y => ?_
  have := div_pos hε (trunc_pos_den (a := N y) hδ)
  linarith

theorem trunc_nonneg {a ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    0 ≤ Real.log (1 + ε / (a ^ 2 + δ)) := by
  apply Real.log_nonneg
  have := div_pos hε (trunc_pos_den (a := a) hδ)
  linarith

theorem trunc_le_top {a ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Real.log (1 + ε / (a ^ 2 + δ)) ≤ Real.log (1 + ε / δ) := by
  have h1 := div_pos hε (trunc_pos_den (a := a) hδ)
  apply Real.log_le_log (by linarith)
  have : ε / (a ^ 2 + δ) ≤ ε / δ :=
    div_le_div_of_nonneg_left hε.le hδ (by nlinarith [sq_nonneg a])
  linarith

theorem trunc_le_green {a ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (ha : a ≠ 0) :
    Real.log (1 + ε / (a ^ 2 + δ)) ≤ Real.log (1 + ε / a ^ 2) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have h1 : 0 < ε / (a ^ 2 + δ) := div_pos hε (by linarith)
  apply Real.log_le_log (by linarith)
  have : ε / (a ^ 2 + δ) ≤ ε / a ^ 2 :=
    div_le_div_of_nonneg_left hε.le ha2 (by linarith)
  linarith

theorem trunc_mono {a ε δ δ' : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδδ : δ ≤ δ') :
    Real.log (1 + ε / (a ^ 2 + δ')) ≤ Real.log (1 + ε / (a ^ 2 + δ)) := by
  have hd : 0 < a ^ 2 + δ := trunc_pos_den hδ
  have h1 : 0 < ε / (a ^ 2 + δ') := div_pos hε (by linarith)
  apply Real.log_le_log (by linarith)
  have : ε / (a ^ 2 + δ') ≤ ε / (a ^ 2 + δ) :=
    div_le_div_of_nonneg_left hε.le hd (by linarith)
  linarith

theorem trunc_tendsto {a ε : ℝ} (hε : 0 < ε) (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => Real.log (1 + ε / (a ^ 2 + 1 / ((n : ℝ) + 1)))) atTop
      (𝓝 (Real.log (1 + ε / a ^ 2))) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ => a ^ 2 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (a ^ 2 + 0)) :=
    tendsto_const_nhds.add h0
  rw [add_zero] at h1
  have h2 : Tendsto (fun n : ℕ => 1 + ε / (a ^ 2 + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (1 + ε / a ^ 2)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div h1 ha2.ne')
  have h3 : 1 + ε / a ^ 2 ≠ 0 := by
    have := div_pos hε ha2
    linarith
  exact (Real.continuousAt_log h3).tendsto.comp h2

theorem ae_ne_zero {ν : Measure X} {N : X → ℝ} (h0 : ν {y | N y = 0} = 0) :
    ∀ᵐ y ∂ν, N y ≠ 0 := by
  rw [ae_iff]
  simpa using h0

theorem green_measurable {N : X → ℝ} (hN : Continuous N) (ε : ℝ) :
    Measurable fun y => Real.log (1 + ε / N y ^ 2) := by
  have := hN.measurable
  fun_prop

theorem green_nonneg {a ε : ℝ} (hε : 0 < ε) : 0 ≤ Real.log (1 + ε / a ^ 2) := by
  apply Real.log_nonneg
  have : 0 ≤ ε / a ^ 2 := by positivity
  linarith

theorem limit_bound (μ : Measure X) (μT : ℝ → Measure X) (N : X → ℝ) [IsFiniteMeasure μ]
    (hN : Continuous N) (hμ0 : μ {y | N y = 0} = 0)
    (hw : ∀ (g : X → ℝ) (B : ℝ), Continuous g → (∀ y, |g y| ≤ B) →
      Tendsto (fun t => ∫ y, g y ∂μT t) (𝓝[>] 0) (𝓝 (∫ y, g y ∂μ)))
    {ε η : ℝ} (hε : 0 < ε)
    (hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsFiniteMeasure (μT t) ∧ μT t {y | N y = 0} = 0 ∧
      Integrable (fun y => Real.log (1 + ε / N y ^ 2)) (μT t) ∧
      ∫ y, Real.log (1 + ε / N y ^ 2) ∂μT t ≤ η) :
    Integrable (fun y => Real.log (1 + ε / N y ^ 2)) μ ∧
      ∫ y, Real.log (1 + ε / N y ^ 2) ∂μ ≤ η := by
  have habs : ∀ {δ : ℝ}, 0 < δ → ∀ y, |Real.log (1 + ε / (N y ^ 2 + δ))| ≤ Real.log (1 + ε / δ) := by
    intro δ hδ y
    rw [abs_of_nonneg (trunc_nonneg hε hδ)]
    exact trunc_le_top hε hδ
  have hint : ∀ (ν : Measure X) [IsFiniteMeasure ν] {δ : ℝ}, 0 < δ →
      Integrable (fun y => Real.log (1 + ε / (N y ^ 2 + δ))) ν := by
    intro ν _ δ hδ
    refine Integrable.of_bound (trunc_continuous hN hε hδ).measurable.aestronglyMeasurable
      (Real.log (1 + ε / δ)) (Eventually.of_forall fun y => ?_)
    simpa [Real.norm_eq_abs] using habs hδ y
  have hstep : ∀ {δ : ℝ}, 0 < δ → ∫ y, Real.log (1 + ε / (N y ^ 2 + δ)) ∂μ ≤ η := by
    intro δ hδ
    refine le_of_tendsto (hw _ _ (trunc_continuous hN hε hδ) (habs hδ)) ?_
    filter_upwards [hev] with t ht
    obtain ⟨hf, h0, hi, hle⟩ := ht
    refine le_trans (integral_mono_ae (hint (μT t) hδ) hi ?_) hle
    filter_upwards [ae_ne_zero h0] with y hy
    exact trunc_le_green hε hδ.le hy
  have hη : 0 ≤ η :=
    le_trans (integral_nonneg fun y => trunc_nonneg hε one_pos) (hstep one_pos)
  have hδn : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hlim := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
    (f := fun (n : ℕ) y => ENNReal.ofReal (Real.log (1 + ε / (N y ^ 2 + 1 / ((n : ℝ) + 1)))))
    (F := fun y => ENNReal.ofReal (Real.log (1 + ε / N y ^ 2)))
    (fun n => ((trunc_continuous hN hε (hδn n)).measurable.ennreal_ofReal).aemeasurable)
    (by
      filter_upwards with y
      intro m n hmn
      apply ENNReal.ofReal_le_ofReal
      apply trunc_mono hε (hδn n)
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact one_div_le_one_div_of_le (by positivity) (by linarith))
    (by
      filter_upwards [ae_ne_zero hμ0] with y hy
      exact (ENNReal.continuous_ofReal.tendsto _).comp (trunc_tendsto hε hy))
  have hbound : ∫⁻ y, ENNReal.ofReal (Real.log (1 + ε / N y ^ 2)) ∂μ ≤ ENNReal.ofReal η := by
    refine le_of_tendsto' hlim fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hint μ (hδn n))
      (Eventually.of_forall fun y => trunc_nonneg hε (hδn n))]
    exact ENNReal.ofReal_le_ofReal (hstep (hδn n))
  have hnn : 0 ≤ᵐ[μ] fun y => Real.log (1 + ε / N y ^ 2) :=
    Eventually.of_forall fun y => green_nonneg hε
  have hG : Integrable (fun y => Real.log (1 + ε / N y ^ 2)) μ :=
    ⟨(green_measurable hN ε).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)⟩
  refine ⟨hG, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff hη, ofReal_integral_eq_lintegral_ofReal hG hnn]
  exact hbound

theorem neg_log_split {a ε : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    -Real.log a = (1 / 2) * Real.log (1 + ε / a ^ 2) + -Real.log (a ^ 2 + ε) / 2 := by
  have ha2 : 0 < a ^ 2 := by positivity
  have h : 1 + ε / a ^ 2 = (a ^ 2 + ε) / a ^ 2 := by field_simp
  rw [h, Real.log_div (by positivity) ha2.ne', Real.log_pow]
  push_cast
  ring

theorem smooth_continuous {N : X → ℝ} (hN : Continuous N) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun y => -Real.log (N y ^ 2 + ε) / 2 := by
  have hden : Continuous fun y => N y ^ 2 + ε := by fun_prop
  exact ((hden.log fun y => (trunc_pos_den hε).ne').neg).div_const 2

theorem smooth_bound {N : X → ℝ} (hN1 : ∀ y, 0 ≤ N y ∧ N y ≤ 1) {ε : ℝ} (hε : 0 < ε) (y : X) :
    |-Real.log (N y ^ 2 + ε) / 2| ≤ |Real.log ε| + |Real.log (1 + ε)| := by
  obtain ⟨h0, h1⟩ := hN1 y
  have hsq : N y ^ 2 ≤ 1 := by nlinarith
  have hlo : Real.log ε ≤ Real.log (N y ^ 2 + ε) :=
    Real.log_le_log hε (by nlinarith [sq_nonneg (N y)])
  have hhi : Real.log (N y ^ 2 + ε) ≤ Real.log (1 + ε) :=
    Real.log_le_log (trunc_pos_den hε) (by linarith)
  have h2 := le_abs_self (Real.log (1 + ε))
  have h3 := neg_abs_le (Real.log ε)
  have h4 := abs_nonneg (Real.log ε)
  have h5 := abs_nonneg (Real.log (1 + ε))
  rw [abs_le]
  constructor <;> linarith

theorem split_integral (ν : Measure X) [IsFiniteMeasure ν] {N : X → ℝ} (hN : Continuous N)
    (hN1 : ∀ y, 0 ≤ N y ∧ N y ≤ 1) (h0 : ν {y | N y = 0} = 0) {ε : ℝ} (hε : 0 < ε)
    (hG : Integrable (fun y => Real.log (1 + ε / N y ^ 2)) ν) :
    Integrable (fun y => -Real.log (N y)) ν ∧
      ∫ y, -Real.log (N y) ∂ν = (1 / 2) * ∫ y, Real.log (1 + ε / N y ^ 2) ∂ν +
        ∫ y, -Real.log (N y ^ 2 + ε) / 2 ∂ν := by
  have hF : Integrable (fun y => -Real.log (N y ^ 2 + ε) / 2) ν :=
    Integrable.of_bound (smooth_continuous hN hε).measurable.aestronglyMeasurable
      (|Real.log ε| + |Real.log (1 + ε)|)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact smooth_bound hN1 hε y)
  have hae : (fun y => -Real.log (N y)) =ᵐ[ν]
      fun y => (1 / 2) * Real.log (1 + ε / N y ^ 2) + -Real.log (N y ^ 2 + ε) / 2 := by
    filter_upwards [ae_ne_zero h0] with y hy
    exact neg_log_split hε (lt_of_le_of_ne (hN1 y).1 hy.symm)
  have hsum := (hG.const_mul (1 / 2)).add hF
  refine ⟨hsum.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add (hG.const_mul (1 / 2)) hF, integral_const_mul]

end GlobalTheory.CompanionTheory.Ar.Giv.UClose

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem tendsto_integral_neg_log_of_green_small :
    ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (μT : ℝ → Measure X) (N : X → ℝ), IsFiniteMeasure μ → (∀ᶠ t in 𝓝[>] (0 : ℝ), IsFiniteMeasure (μT t)) → Continuous N → (∀ y, 0 ≤ N y ∧ N y ≤ 1) → μ {y | N y = 0} = 0 → (∀ᶠ t in 𝓝[>] (0 : ℝ), μT t {y | N y = 0} = 0) → (∀ (g : X → ℝ) (B : ℝ), Continuous g → (∀ y, |g y| ≤ B) → Tendsto (fun t => ∫ y, g y ∂μT t) (𝓝[>] 0) (𝓝 (∫ y, g y ∂μ))) → (∀ η : ℝ, 0 < η → ∃ ε₀ t₁ : ℝ, 0 < ε₀ ∧ 0 < t₁ ∧ ∀ ε t : ℝ, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ → Integrable (fun y => Real.log (1 + ε / N y ^ 2)) (μT t) ∧ ∫ y, Real.log (1 + ε / N y ^ 2) ∂μT t ≤ η) → Integrable (fun y => -Real.log (N y)) μ ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), Integrable (fun y => -Real.log (N y)) (μT t)) ∧ Tendsto (fun t => ∫ y, -Real.log (N y) ∂μT t) (𝓝[>] 0) (𝓝 (∫ y, -Real.log (N y) ∂μ)) := by
  intro X _ _ _ μ μT N hμ hμT hN hN1 hμ0 hμT0 hw hsmall
  have hev : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      IsFiniteMeasure (μT t) ∧ μT t {y | N y = 0} = 0 ∧
      Integrable (fun y => Real.log (1 + ε / N y ^ 2)) (μT t) ∧
      ∫ y, Real.log (1 + ε / N y ^ 2) ∂μT t ≤ η := by
    intro η hη
    obtain ⟨ε₀, t₁, hε₀, ht₁, h⟩ := hsmall η hη
    refine ⟨ε₀, hε₀, ?_⟩
    filter_upwards [hμT, hμT0, Ioc_mem_nhdsGT ht₁] with t h1 h2 h3
    exact ⟨h1, h2, h ε₀ t hε₀ le_rfl h3.1 h3.2⟩
  obtain ⟨ε₁, hε₁, he₁⟩ := hev 1 one_pos
  have hlim := UClose.limit_bound μ μT N hN hμ0 hw hε₁ he₁
  refine ⟨(UClose.split_integral μ hN hN1 hμ0 hε₁ hlim.1).1, ?_, ?_⟩
  · filter_upwards [he₁] with t ht
    obtain ⟨h1, h2, h3, _⟩ := ht
    exact (UClose.split_integral (μT t) hN hN1 h2 hε₁ h3).1
  · rw [Metric.tendsto_nhds]
    intro e he
    obtain ⟨ε, hε, hE⟩ := hev (e / 2) (by positivity)
    obtain ⟨hGi, hGle⟩ := UClose.limit_bound μ μT N hN hμ0 hw hε hE
    have hF := hw _ _ (UClose.smooth_continuous hN hε) (UClose.smooth_bound hN1 hε)
    have hFe := (Metric.tendsto_nhds.1 hF) (e / 2) (by positivity)
    filter_upwards [hE, hFe] with t ht h5
    obtain ⟨h1, h2, h3, h4⟩ := ht
    rw [(UClose.split_integral (μT t) hN hN1 h2 hε h3).2,
      (UClose.split_integral μ hN hN1 hμ0 hε hGi).2, Real.dist_eq]
    rw [Real.dist_eq] at h5
    have a : 0 ≤ ∫ y, Real.log (1 + ε / N y ^ 2) ∂μ :=
      integral_nonneg fun y => UClose.green_nonneg hε
    have b : 0 ≤ ∫ y, Real.log (1 + ε / N y ^ 2) ∂μT t :=
      integral_nonneg fun y => UClose.green_nonneg hε
    rw [abs_lt] at h5 ⊢
    constructor <;> linarith [h5.1, h5.2]

end GlobalTheory.CompanionTheory.Ar.Giv
end

