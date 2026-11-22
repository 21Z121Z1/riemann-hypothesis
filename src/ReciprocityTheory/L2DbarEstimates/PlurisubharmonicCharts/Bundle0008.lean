import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0007
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle0001
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxE
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

theorem dbv_add {n : ℕ} (D₁ D₂ : V n →L[ℝ] ℂ) (ζ : V n) : dbv (D₁ + D₂) ζ = dbv D₁ ζ + dbv D₂ ζ := by
  simp only [dbv, ContinuousLinearMap.add_apply]
  ring

theorem dbv_smul {n : ℕ} (c : ℂ) (D : V n →L[ℝ] ℂ) (ζ : V n) : dbv (c • D) ζ = c * dbv D ζ := by
  simp only [dbv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dbv_holo {n : ℕ} {G : V n → ℂ} {v : V n} (hG : DifferentiableAt ℂ G v) (ζ : V n) :
    dbv (fderiv ℝ G v) ζ = 0 := by
  unfold dbv
  rw [hG.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul, ← mul_assoc, I_mul_I]
  ring

theorem leviV_smul_real {n : ℕ} (g : V n → ℂ) (u : V n) (r : ℝ) (ζ : V n) :
    leviV n g u (r • ζ).ofLp = ((r ^ 2 : ℝ) : ℂ) * leviV n g u ζ.ofLp := by
  unfold leviV
  simp only [WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

private theorem contDiffOn_infty_wd_wdb {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) :
    ContDiffOn ℝ ∞ (wd n j g) U ∧ ContDiffOn ℝ ∞ (wdb n j g) U := by
  have hF : ∀ v : V n, ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y v) U := fun v =>
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2.clm_apply contDiffOn_const
  constructor
  · unfold wd
    exact ((hF _).sub (contDiffOn_const.mul (hF _))).div_const 2
  · unfold wdb
    exact ((hF _).add (contDiffOn_const.mul (hF _))).div_const 2

theorem continuousOn_wd_wdb {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (j k : Fin n) : ContinuousOn (wd n j (wdb n k g)) U := ((contDiffOn_infty_wd_wdb hU (contDiffOn_infty_wd_wdb hU hg k).2 j).1).continuousOn

theorem levi_pos_compact {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) {K0 : Set (V n)} (hK0 : IsCompact K0) (hK0U : K0 ⊆ U)
    (hpos : ∀ u ∈ K0, ∀ ζ : V n, ζ ≠ 0 → 0 < (leviV n g u ζ.ofLp).re) :
    ∃ m > 0, ∀ u ∈ K0, ∀ ζ : V n, m * ‖ζ‖ ^ 2 ≤ (leviV n g u ζ.ofLp).re := by
  have hcont : ContinuousOn (fun q : V n × V n => (leviV n g q.1 q.2.ofLp).re)
      (K0 ×ˢ Metric.sphere (0 : V n) 1) := by
    unfold leviV
    refine Complex.continuous_re.comp_continuousOn ?_
    refine continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun k _ => ?_
    refine (((continuousOn_wd_wdb hU hg j k).comp continuousOn_fst fun q hq => hK0U hq.1).mul
      ((EuclideanSpace.proj j : V n →L[ℂ] ℂ).continuous.comp continuous_snd).continuousOn).mul
      (Complex.continuous_conj.comp
        ((EuclideanSpace.proj k : V n →L[ℂ] ℂ).continuous.comp continuous_snd)).continuousOn
  by_cases hne : (K0 ×ˢ Metric.sphere (0 : V n) 1).Nonempty
  · obtain ⟨q0, hq0, hmin⟩ := (hK0.prod (isCompact_sphere 0 1)).exists_isMinOn hne hcont
    have hq0ne : q0.2 ≠ 0 := by
      intro h
      have := mem_sphere_zero_iff_norm.1 hq0.2
      rw [h, norm_zero] at this
      exact zero_ne_one this
    refine ⟨(leviV n g q0.1 q0.2.ofLp).re, hpos _ hq0.1 _ hq0ne, fun u hu ζ => ?_⟩
    rcases eq_or_ne ζ 0 with rfl | hζ
    · simp [leviV]
    · have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
      have h1 : (‖ζ‖⁻¹ : ℝ) • ζ ∈ Metric.sphere (0 : V n) 1 := by
        simp [norm_smul, hn.ne']
      have hmin' : (leviV n g q0.1 q0.2.ofLp).re ≤ (leviV n g u ((‖ζ‖⁻¹ : ℝ) • ζ).ofLp).re :=
        isMinOn_iff.1 hmin (u, (‖ζ‖⁻¹ : ℝ) • ζ) ⟨hu, h1⟩
      have hζ' : ζ = ‖ζ‖ • ((‖ζ‖⁻¹ : ℝ) • ζ) := by
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      conv_rhs => rw [hζ', leviV_smul_real, Complex.re_ofReal_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hmin' (sq_nonneg _)
  · refine ⟨1, one_pos, fun u hu ζ => ?_⟩
    rcases eq_or_ne ζ 0 with rfl | hζ
    · simp [leviV]
    · exfalso
      apply hne
      refine ⟨(u, (‖ζ‖⁻¹ : ℝ) • ζ), hu, ?_⟩
      simp [norm_smul, (norm_pos_iff.2 hζ).ne']

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeDA
section
open Complex ComplexConjugate Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

namespace LeviFormQuadraticSums

variable {n : ℕ}

theorem wdb_sum {ι : Type*} (s : Finset ι) {g : ι → V n → ℂ} {y : V n}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) y) (j : Fin n) :
    wdb n j (fun w => ∑ i ∈ s, g i w) y = ∑ i ∈ s, wdb n j (g i) y := by
  simp only [wdb, fderiv_fun_sum hg, FunLike.coe_sum, Finset.sum_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]

theorem norm_sum_mul_sq_le {d : ℕ} (x y : Fin d → ℂ) :
    ‖∑ k, x k * y k‖ ^ 2 ≤ (∑ k, ‖x k‖ ^ 2) * (∑ k, ‖y k‖ ^ 2) := by
  have h1 : ‖∑ k, x k * y k‖ ≤ ∑ k, ‖x k‖ * ‖y k‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖x k‖) (fun k => ‖y k‖)
  calc ‖∑ k, x k * y k‖ ^ 2 ≤ (∑ k, ‖x k‖ * ‖y k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem normSq_eq_ofReal {z : ℂ} : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.sq_norm]

section Main

variable {d : ℕ} (p : V n → V d) (U : Set (V n)) (c : ℝ)

theorem q_eq : (fun x => ((‖p x‖ ^ 2 / c : ℝ) : ℂ)) =
    fun x => ∑ k, (c : ℂ)⁻¹ * (p x k * conj (p x k : ℂ)) := by
  funext x
  simp only [normSq_eq_ofReal]
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  rw [div_eq_inv_mul, Finset.mul_sum]

variable {p U}

end Main

end LeviFormQuadraticSums

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open Filter Topology Set ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open scoped ContDiff

noncomputable section

theorem fc_clm_decomp (n : ℕ) (D : V n →L[ℝ] ℂ) (u : V n) :
    D u = ∑ a, ((D (bas n a) - Complex.I * D (Complex.I • bas n a)) / 2 * u a +
      (D (bas n a) + Complex.I * D (Complex.I • bas n a)) / 2 * (starRingEnd ℂ) (u a)) := by
  have hu : u = ∑ a, ((u a).re • bas n a + (u a).im • (Complex.I • bas n a)) := by
    ext b
    simp [bas, EuclideanSpace.single_apply, Finset.sum_add_distrib, Complex.real_smul,
      Pi.single_apply, mul_ite, mul_one, mul_zero]
  conv_lhs => rw [hu]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have h1 : u a = ((u a).re : ℂ) + ((u a).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : (starRingEnd ℂ) (u a) = ((u a).re : ℂ) - ((u a).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(D (bas n a) - Complex.I * D (Complex.I • bas n a)) / 2) * h1 +
    (-(D (bas n a) + Complex.I * D (Complex.I • bas n a)) / 2) * h2 +
    (((u a).im : ℂ) * D (Complex.I • bas n a)) * Complex.I_mul_I

theorem fc_wdb_holo (n : ℕ) (p : V n → ℂ) (v : V n) (hp : DifferentiableAt ℂ p v) (j : Fin n) :
    wdb n j p v = 0 := by
  unfold wdb
  rw [hp.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  linear_combination (fderiv ℂ p v (bas n j) / 2) * Complex.I_mul_I

theorem fc_wd_sum (n : ℕ) (j : Fin n) {ι : Type*} (s : Finset ι) (f : ι → V n → ℂ) (v : V n)
    (hf : ∀ a ∈ s, DifferentiableAt ℝ (f a) v) :
    wd n j (fun y => ∑ a ∈ s, f a y) v = ∑ a ∈ s, wd n j (f a) v := by
  unfold wd
  have e : (fun y => ∑ a ∈ s, f a y) = ∑ a ∈ s, f a := by
    funext y
    simp
  rw [e, fderiv_sum hf]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

theorem fc_leviV_congr (n : ℕ) (g₁ g₂ : V n → ℂ) (v : V n) (h : g₁ =ᶠ[𝓝 v] g₂)
    (ξ : Fin n → ℂ) : leviV n g₁ v ξ = leviV n g₂ v ξ := by
  unfold leviV
  have hk : ∀ k, wdb n k g₁ =ᶠ[𝓝 v] wdb n k g₂ := fun k =>
    h.eventuallyEq_nhds.mono fun y hy => by
      unfold wdb
      rw [hy.fderiv_eq (𝕜 := ℝ)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  unfold wd
  rw [(hk k).fderiv_eq (𝕜 := ℝ)]

end

end ReciprocityTheory.L2DbarEstimates.Y
end

