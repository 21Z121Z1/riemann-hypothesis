import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzShiftIteratedFDerivBound
section
open scoped ContDiff

namespace GlobalTheory

theorem schwartz_shift_iteratedFDeriv_bound
    {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : SchwartzMap V ℂ) (a : V) (p : E →L[ℝ] V) (n M : ℕ) (R : ℝ) :
    ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖ ≤ C * ((1 + ‖y‖) ^ M)⁻¹ := by
  set S : ℝ := 2 ^ M * (Finset.Iic (M, n)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f with hS
  set B : ℝ := ‖a‖ + ‖p‖ * max R 0 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨‖p‖ ^ n * ((1 + B) ^ M * S), fun y t ht => ?_⟩
  have hy0 : 0 < (1 + ‖y‖) ^ M := by positivity

  have hcomp : (fun t => f (y + a + p t)) = (fun v => f (y + a + v)) ∘ p := rfl
  have hg : ContDiff ℝ ∞ (fun v => f (y + a + v)) :=
    (f.smooth ⊤).comp (contDiff_const.add contDiff_id)
  have e1 := ContinuousLinearMap.iteratedFDeriv_comp_right p hg t (i := n)
    (by exact_mod_cast le_top)
  have e2 : iteratedFDeriv ℝ n (fun v => f (y + a + v)) (p t)
      = iteratedFDeriv ℝ n f (y + a + p t) := iteratedFDeriv_comp_add_left n (y + a) (p t)
  set v := y + a + p t with hv
  have hD : ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖
      ≤ ‖p‖ ^ n * ‖iteratedFDeriv ℝ n f v‖ := by
    rw [hcomp, e1, e2]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [Finset.prod_const, mul_comm]

  have hdec : (1 + ‖v‖) ^ M * ‖iteratedFDeriv ℝ n f v‖ ≤ S :=
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M, n)) le_rfl le_rfl f v

  have hpt : ‖p t‖ ≤ ‖p‖ * max R 0 :=
    (p.le_opNorm t).trans (mul_le_mul_of_nonneg_left (ht.trans (le_max_left _ _)) (norm_nonneg _))
  have hyv : 1 + ‖y‖ ≤ (1 + ‖v‖) * (1 + B) := by
    have : y = v - a - p t := by rw [hv]; abel
    have h1 : ‖y‖ ≤ ‖v‖ + ‖a‖ + ‖p t‖ := by
      rw [this]
      calc ‖v - a - p t‖ ≤ ‖v - a‖ + ‖p t‖ := norm_sub_le _ _
        _ ≤ ‖v‖ + ‖a‖ + ‖p t‖ := by gcongr; exact norm_sub_le _ _
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith [mul_nonneg hv0 hB0]
  have hyM : (1 + ‖y‖) ^ M ≤ (1 + ‖v‖) ^ M * (1 + B) ^ M := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hyv M
  have hDf0 : 0 ≤ ‖iteratedFDeriv ℝ n f v‖ := norm_nonneg _
  have key : (1 + ‖y‖) ^ M * ‖iteratedFDeriv ℝ n f v‖ ≤ (1 + B) ^ M * S := by
    calc (1 + ‖y‖) ^ M * ‖iteratedFDeriv ℝ n f v‖
        ≤ (1 + ‖v‖) ^ M * (1 + B) ^ M * ‖iteratedFDeriv ℝ n f v‖ :=
          mul_le_mul_of_nonneg_right hyM hDf0
      _ = (1 + B) ^ M * ((1 + ‖v‖) ^ M * ‖iteratedFDeriv ℝ n f v‖) := by ring
      _ ≤ (1 + B) ^ M * S := mul_le_mul_of_nonneg_left hdec (by positivity)
  have hf' : ‖iteratedFDeriv ℝ n f v‖ ≤ (1 + B) ^ M * S * ((1 + ‖y‖) ^ M)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hy0, mul_comm]; exact key
  calc ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖
      ≤ ‖p‖ ^ n * ‖iteratedFDeriv ℝ n f v‖ := hD
    _ ≤ ‖p‖ ^ n * ((1 + B) ^ M * S * ((1 + ‖y‖) ^ M)⁻¹) :=
        mul_le_mul_of_nonneg_left hf' (by positivity)
    _ = ‖p‖ ^ n * ((1 + B) ^ M * S) * ((1 + ‖y‖) ^ M)⁻¹ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecomposition
section
open scoped ContDiff
open MeasureTheory Set Filter Topology Metric

noncomputable section

namespace GlobalTheory.SchwartzDiv

section Param

variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}

theorem hasFDerivAt_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W}
    (hΘ : ContDiff ℝ ∞ Θ) (t₀ : P) :
    HasFDerivAt (fun t => ∫ y, φ y • Θ (t, c y) ∂ν) (∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t₀ ∂ν) t₀ := by
  have hΘs : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
    ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
      (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
  have hΘ' := hΘs.continuous
  have hK : IsCompact (closedBall t₀ 1 ×ˢ S) := (isCompact_closedBall t₀ 1).prod hS
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ'.continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hΘ.continuous.continuousOn
  have hm : ∀ t, AEStronglyMeasurable (fun y => φ y • Θ (t, c y)) ν := fun t =>
    hφ.1.smul ((hΘ.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F' := fun t y => φ y • fderiv ℝ (fun s => Θ (s, c y)) t) (bound := fun y => ‖φ y‖ * C)
    (ball_mem_nhds t₀ one_pos) (.of_forall hm) ?_ ?_ ?_ (hφ.norm.mul_const C) ?_
  · refine Integrable.mono' (hφ.norm.mul_const C₀) (hm t₀) ?_
    filter_upwards [hcS] with y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC₀ _ ⟨mem_closedBall_self zero_le_one, hy⟩) (norm_nonneg _)
  · exact hφ.1.smul ((hΘ'.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  · filter_upwards [hcS] with y hy t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (t, c y) ⟨ball_subset_closedBall ht, hy⟩) (norm_nonneg _)
  · refine .of_forall fun y t _ => ?_
    have hd : ContDiff ℝ ∞ fun s => Θ (s, c y) := hΘ.comp (contDiff_id.prodMk contDiff_const)
    exact ((hd.differentiable (by simp)) t).hasFDerivAt.const_smul (φ y)

theorem contDiff_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W}
    (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ fun t => ∫ y, φ y • Θ (t, c y) ∂ν := by
  rw [contDiff_infty]
  intro n
  induction n generalizing W with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t =>
      (hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t).continuousAt)
  | succ n ih =>
    have hΘ' : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
      ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
        (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨fun t => ∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t ∂ν,
      ih hΘ', fun t => hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t⟩

end Param

def invCut (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1) * t⁻¹

theorem invCut_of_one_le {t : ℝ} (ht : 1 ≤ t) : invCut t = t⁻¹ := by
  rw [invCut, Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem invCut_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : invCut t = 0 := by
  rw [invCut, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem contDiff_invCut : ContDiff ℝ ∞ invCut := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge 0 t with h | h
  · exact ((Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).contDiffAt).mul (contDiffAt_inv ℝ h.ne')
  · have : invCut =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show t < 1 / 2 by linarith)] with s hs
      exact invCut_of_le_half hs.le
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem hasTemperateGrowth_invCut : invCut.HasTemperateGrowth := by
  refine ⟨contDiff_invCut, fun n => ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (contDiff_invCut.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).continuousOn
  refine ⟨0, max C (Nat.factorial n : ℝ), fun x => ?_⟩
  rw [pow_zero, mul_one]
  rcases lt_or_ge x (1 / 2) with h1 | h1
  · have : invCut =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      exact invCut_of_le_half hs.le
    rw [(this.iteratedFDeriv ℝ n).eq_of_nhds]
    simp only [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
    exact le_max_of_le_right (Nat.cast_nonneg _)
  rcases le_or_gt x 2 with h2 | h2
  · exact (hC x ⟨h1, h2⟩).trans (le_max_left _ _)
  · have : invCut =ᶠ[𝓝 x] Inv.inv := by
      filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < x by linarith)] with s hs
      exact invCut_of_one_le hs.le
    rw [(this.iteratedFDeriv ℝ n).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, iter_deriv_inv]
    refine le_trans ?_ (le_max_right _ _)
    have hx : ‖x ^ (-1 - n : ℤ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (zpow_pos (by linarith) _)]
      exact zpow_le_one_of_nonpos₀ (by linarith) (by omega)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
    calc (Nat.factorial n : ℝ) * ‖x ^ (-1 - n : ℤ)‖ ≤ Nat.factorial n * 1 := by gcongr
      _ = Nat.factorial n := mul_one _

end GlobalTheory.SchwartzDiv

namespace GlobalTheory.SchwartzDiv

theorem hadamard (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (hf0 : f 0 = 0) :
    ∃ (n : ℕ) (L : Fin n → V →L[ℝ] ℝ) (h g : Fin n → SchwartzMap V ℂ),
      (∀ i x, g i x = (L i x : ℂ) * h i x) ∧ ∀ x, f x = ∑ i, g i x := by
  let b := Module.finBasis ℝ V
  let L : Fin (Module.finrank ℝ V) → V →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hL : ∀ i x, L i x = b.repr x i := fun i x => by simp [L, Module.Basis.coord_apply]
  let q : V → ℝ := fun x => ∑ i, L i x ^ 2
  have hq : q.HasTemperateGrowth := by
    simp only [q]
    exact Function.HasTemperateGrowth.sum fun i _ => ((L i).hasTemperateGrowth).pow 2
  have hqs : ContDiff ℝ ∞ q := hq.1
  have hfs : ContDiff ℝ ∞ f := f.smooth ⊤
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hfs.fderiv_right (by simp)

  let k : Fin (Module.finrank ℝ V) → V → ℂ := fun i x => ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) (b i)
  have hk : ∀ i, ContDiff ℝ ∞ (k i) := by
    intro i
    have hΘ : ContDiff ℝ ∞ fun p : V × ℝ => fderiv ℝ f (p.2 • p.1) (b i) :=
      (hfd.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_const
    have key := contDiff_integral_smul_param (ν := volume.restrict (Ioc (0 : ℝ) 1)) (c := id)
      (S := Icc (0 : ℝ) 1) (φ := fun _ => (1 : ℂ)) aestronglyMeasurable_id isCompact_Icc
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => Ioc_subset_Icc_self ht)
      (integrableOn_const (by simp)) hΘ
    convert key using 2 with x
    simp [k, intervalIntegral.integral_of_le zero_le_one]
  have key : ∀ x, f x = ∑ i, (L i x : ℂ) * k i x := by
    intro x
    have hc : ∀ v : V, Continuous fun t : ℝ => fderiv ℝ f (t • x) v := fun v =>
      (hfd.continuous.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
    have h1 : ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) x = f ((1 : ℝ) • x) - f ((0 : ℝ) • x) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => f (t • x)) (fun t _ => ?_)
        ((hc x).intervalIntegrable _ _)
      have := (f.differentiableAt (x := t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
      simp only [one_smul] at this
      exact this
    rw [one_smul, zero_smul, hf0, sub_zero] at h1
    rw [← h1]
    have h2 : ∀ t : ℝ, fderiv ℝ f (t • x) x = ∑ i, (L i x : ℂ) * fderiv ℝ f (t • x) (b i) := by
      intro t
      rw [show fderiv ℝ f (t • x) x = fderiv ℝ f (t • x) (∑ i, b.repr x i • b i) by rw [b.sum_repr], map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Complex.real_smul, hL]
    simp_rw [h2]
    rw [intervalIntegral.integral_finset_sum (f := fun i t => (L i x : ℂ) * fderiv ℝ f (t • x) (b i))
      fun i _ => (continuous_const.mul (hc (b i))).intervalIntegrable _ _]
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _

  let β : V → ℝ := fun x => 1 - q x * invCut (q x)
  have hβs : ContDiff ℝ ∞ β := contDiff_const.sub (hqs.mul (contDiff_invCut.comp hqs))
  have hβ0 : ∀ x, 1 ≤ q x → β x = 0 := by
    intro x hx
    simp only [β]
    rw [invCut_of_one_le hx, mul_inv_cancel₀ (by linarith), sub_self]
  have hnorm : ∀ x, q x < 1 → ‖x‖ ≤ ∑ i, ‖b i‖ := by
    intro x hx
    have hLi : ∀ i, |L i x| ≤ 1 := by
      intro i
      have : L i x ^ 2 ≤ q x :=
        Finset.single_le_sum (f := fun j => L j x ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      exact (sq_le_one_iff_abs_le_one _).1 (by linarith)
    calc ‖x‖ = ‖∑ i, L i x • b i‖ := by simp only [hL, b.sum_repr]
      _ ≤ ∑ i, ‖L i x • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖b i‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) (hLi i)
  have hβc : HasCompactSupport (fun x => (β x : ℂ)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : V) (∑ i, ‖b i‖)) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    have : 1 ≤ q x := by
      by_contra h
      exact absurd (hnorm x (not_le.1 h)) (not_le.2 hx)
    rw [hβ0 x this, Complex.ofReal_zero]
  have hnear : ∀ i, HasCompactSupport ((fun x => (β x : ℂ)) * k i) := fun i => hβc.mul_right
  have hnears : ∀ i, ContDiff ℝ ∞ ((fun x => (β x : ℂ)) * k i) := fun i =>
    (Complex.ofRealCLM.contDiff.comp hβs).mul (hk i)

  let a : Fin (Module.finrank ℝ V) → V → ℂ := fun i x => ((L i x * invCut (q x) : ℝ) : ℂ)
  have ha : ∀ i, (a i).HasTemperateGrowth := fun i =>
    Function.Complex.hasTemperateGrowth_ofReal.comp ((L i).hasTemperateGrowth.mul (hasTemperateGrowth_invCut.comp hq))
  have hLc : ∀ i, (fun x => (L i x : ℂ)).HasTemperateGrowth := fun i =>
    Function.Complex.hasTemperateGrowth_ofReal.comp (L i).hasTemperateGrowth
  let h : Fin (Module.finrank ℝ V) → SchwartzMap V ℂ := fun i =>
    (hnear i).toSchwartzMap (hnears i) + SchwartzMap.smulLeftCLM ℂ (a i) f
  have hh : ∀ i x, h i x = (β x : ℂ) * k i x + a i x * f x := by
    intro i x
    have e : ((hnear i).toSchwartzMap (hnears i) : V → ℂ) x = (β x : ℂ) * k i x := rfl
    simp only [h, SchwartzMap.add_apply, e, SchwartzMap.smulLeftCLM_apply_apply (ha i), smul_eq_mul]
  refine ⟨Module.finrank ℝ V, L, h, fun i => SchwartzMap.smulLeftCLM ℂ (fun x => (L i x : ℂ)) (h i),
    fun i x => by rw [SchwartzMap.smulLeftCLM_apply_apply (hLc i), smul_eq_mul], fun x => ?_⟩
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hLc _), smul_eq_mul, hh]
  have e1 : ∀ i, (L i x : ℂ) * ((β x : ℂ) * k i x + a i x * f x) =
      (β x : ℂ) * ((L i x : ℂ) * k i x) + ((L i x ^ 2 * invCut (q x) : ℝ) : ℂ) * f x := by
    intro i; simp only [a]; push_cast; ring
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, ← Finset.mul_sum, ← key x,
    ← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.sum_mul]
  simp only [β, q]
  push_cast
  ring

end GlobalTheory.SchwartzDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzWeightedSobolevOfFinrankZero
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem schwartz_weighted_sobolev_of_finrank_zero :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], finrank ℝ E = 0 → ∀ (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  intro E _ _ _ _ _ μ _ hE k n
  haveI : Subsingleton E := Module.finrank_zero_iff.mp hE
  have hcpt : IsCompact (univ : Set E) := (Set.subsingleton_univ).isCompact
  have hfin : μ univ ≠ ∞ := hcpt.measure_lt_top.ne
  have hne : μ univ ≠ 0 := isOpen_univ.measure_ne_zero μ univ_nonempty
  set m : ℝ := μ.real univ with hm
  have hmpos : 0 < m := ENNReal.toReal_pos hne hfin
  refine ⟨n, Real.sqrt m⁻¹, Real.sqrt_nonneg _, fun f x => ?_⟩
  have hx : x = 0 := Subsingleton.elim _ _
  subst hx
  set a : ℝ := ‖iteratedFDeriv ℝ n f (0 : E)‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have h1 : ‖(0 : E)‖ ^ k * a ≤ a := by
    apply mul_le_of_le_one_left ha0
    rw [norm_zero]
    exact pow_le_one₀ le_rfl zero_le_one
  refine h1.trans ?_
  have hterm : ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2 ∂μ = m * a ^ 2 := by
    have : (fun z : E => (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2) = fun _ => a ^ 2 := by
      funext z
      rw [Subsingleton.elim z 0, pow_zero, one_mul]
    rw [this, integral_const, smul_eq_mul]
  have hnn : ∀ i j : ℕ, 0 ≤ ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ :=
    fun i j => integral_nonneg fun z => sq_nonneg _
  have hle : m * a ^ 2 ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ := by
    rw [← hterm]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ∑ j ∈ Finset.range (n + 1),
        ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ)
      (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)
      (Finset.mem_range.mpr (Nat.succ_pos n)))
    exact Finset.single_le_sum
      (f := fun j => ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ)
      (fun j _ => hnn 0 j) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  rw [← Real.sqrt_mul (inv_nonneg.mpr hmpos.le)]
  apply Real.le_sqrt_of_sq_le
  calc a ^ 2 = m⁻¹ * (m * a ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hmpos.le)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearFixedSpan
section
namespace GlobalTheory

theorem semilinear_fixed_span (L : Type) [Field L] (s : L ≃+* L) (r : ℕ) (hr : 0 < r)
    (hsr : ∀ x, (⇑s)^[r] x = x) (hsi : ∀ i, 0 < i → i < r → ∃ x, (⇑s)^[i] x ≠ x)
    (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (F : V →+ V)
    (hF : ∀ (a : L) (v : V), F (a • v) = s a • F v) (hFr : ∀ v, (⇑F)^[r] v = v) :
    Submodule.span L {v | F v = v} = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (LinearMap.ext h)

  have hFi : ∀ (i : ℕ) (a : L) (w : V), (⇑F)^[i] (a • w) = (⇑s)^[i] a • (⇑F)^[i] w := by
    intro i
    induction i with
    | zero => intro a w; simp
    | succ n ih =>
      intro a w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, hF]

  have htr : ∀ w : V, F (∑ i ∈ Finset.range r, (⇑F)^[i] w) = ∑ i ∈ Finset.range r, (⇑F)^[i] w := by
    intro w
    rw [map_sum]
    have h1 := Finset.sum_range_succ' (fun i => (⇑F)^[i] w) r
    have h2 := Finset.sum_range_succ (fun i => (⇑F)^[i] w) r
    simp only [Function.iterate_succ_apply'] at h1
    rw [hFr w] at h2
    rw [show (⇑F)^[0] w = w from rfl] at h1
    exact add_right_cancel (h1.symm.trans h2)

  let χ : Fin r → (L →* L) := fun i => (((s : L →+* L) ^ (i : ℕ) : L →+* L) : L →* L)
  have hχ : ∀ (i : Fin r) (a : L), χ i a = (⇑s)^[i] a := by
    intro i a
    simp [χ, RingHom.coe_pow]
  have hinj : Function.Injective χ := by
    intro i j hij
    have key : ∀ (i j : Fin r), (i : ℕ) < j → χ i = χ j → False := by
      intro i j hlt he
      obtain ⟨x, hx⟩ := hsi ((j : ℕ) - i) (Nat.sub_pos_of_lt hlt) (by omega)
      apply hx
      have h3 := congrArg (fun g : L →* L => g x) he
      simp only [hχ] at h3
      have hj : (j : ℕ) = (i : ℕ) + ((j : ℕ) - i) := by omega
      rw [hj, Function.iterate_add_apply] at h3
      exact ((s.injective.iterate _) h3).symm
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact (key i j h hij).elim
    · exact Fin.ext h
    · exact (key j i h hij.symm).elim
  have hli := (linearIndependent_monoidHom L L).comp χ hinj
  have hsum : ∑ i : Fin r, f ((⇑F)^[i] v) • (((fun g : L →* L => (g : L → L)) ∘ χ) i) = 0 := by
    funext a
    have hfix : (∑ i ∈ Finset.range r, (⇑F)^[i] (a • v)) ∈ Submodule.span L {v | F v = v} :=
      Submodule.subset_span (htr (a • v))
    have h0 := hfk hfix
    rw [LinearMap.mem_ker, map_sum] at h0
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, hχ,
      Pi.zero_apply]
    rw [Fin.sum_univ_eq_sum_range (fun i => f ((⇑F)^[i] v) * (⇑s)^[i] a)]
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFi, map_smul, smul_eq_mul, mul_comm]
  exact hv ((Fintype.linearIndependent_iff.1 hli) (fun i => f ((⇑F)^[(i : ℕ)] v)) hsum ⟨0, hr⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralLeOfExpanding
section
open MeasureTheory

namespace GlobalTheory

theorem volume_le_mul_volume_image_of_expanding (N : ℕ) (S : Set (Fin N → ℝ)) (K : ℝ)
    (f : (Fin N → ℝ) → (Fin N → ℝ)) (hK : 0 ≤ K)
    (hf : ∀ t ∈ S, ∀ t' ∈ S, ‖t - t'‖ ≤ K * ‖f t - f t'‖) :
    volume S ≤ ENNReal.ofReal (K ^ N) * volume (f '' S) := by
  have hinj : Set.InjOn f S := by
    intro a ha b hb hab
    have := hf a ha b hb
    rw [hab, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hg : ∀ a ∈ S, Function.invFunOn f S (f a) = a := fun a ha => hinj.leftInvOn_invFunOn ha
  have hlip : LipschitzOnWith K.toNNReal (Function.invFunOn f S) (f '' S) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [hg a ha, hg b hb, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK]
    exact hf a ha b hb
  have himg : Function.invFunOn f S '' (f '' S) = S := hinj.invFunOn_image subset_rfl
  have h := hlip.hausdorffMeasure_image_le (d := (Fintype.card (Fin N) : ℝ)) (by positivity)
  rw [himg, hausdorffMeasure_pi_real, Fintype.card_fin, ENNReal.rpow_natCast] at h
  rw [ENNReal.ofReal_pow hK]
  exact h

theorem setIntegral_le_of_expanding (N : ℕ) (A Q : Set (Fin N → ℝ)) (K : ℝ)
    (f : (Fin N → ℝ) → (Fin N → ℝ)) (h₁ h₂ : (Fin N → ℝ) → ℝ)
    (hA : IsCompact A) (hQ : IsCompact Q) (hK : 0 ≤ K) (c₁ : Continuous h₁) (c₂ : Continuous h₂)
    (n₁ : ∀ t, 0 ≤ h₁ t) (n₂ : ∀ t, 0 ≤ h₂ t) (hm : ∀ t ∈ A, f t ∈ Q ∧ h₁ t ≤ h₂ (f t))
    (hf : ∀ t ∈ A, ∀ t' ∈ A, ‖t - t'‖ ≤ K * ‖f t - f t'‖) :
    ∫ t in A, h₁ t ≤ K ^ N * ∫ t in Q, h₂ t := by
  have i₁ : IntegrableOn h₁ A volume := c₁.continuousOn.integrableOn_compact hA
  have i₂ : IntegrableOn h₂ Q volume := c₂.continuousOn.integrableOn_compact hQ
  have hKN : 0 ≤ K ^ N := pow_nonneg hK N
  have hI₂ : 0 ≤ ∫ t in Q, h₂ t := integral_nonneg n₂
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKN hI₂), ENNReal.ofReal_mul hKN,
    ofReal_integral_eq_lintegral_ofReal i₁ (Filter.Eventually.of_forall n₁),
    ofReal_integral_eq_lintegral_ofReal i₂ (Filter.Eventually.of_forall n₂),
    lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall n₁) c₁.aemeasurable,
    lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall n₂) c₂.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun r => ?_
  have m₁ : MeasurableSet {a | r < h₁ a} := measurableSet_lt measurable_const c₁.measurable
  have m₂ : MeasurableSet {a | r < h₂ a} := measurableSet_lt measurable_const c₂.measurable
  rw [Measure.restrict_apply m₁, Measure.restrict_apply m₂]
  refine (volume_le_mul_volume_image_of_expanding N _ K f hK
    (fun t ht t' ht' => hf t ht.2 t' ht'.2)).trans ?_
  gcongr
  rintro _ ⟨a, ⟨ha, haA⟩, rfl⟩
  exact ⟨lt_of_lt_of_le ha (hm a haA).2, (hm a haA).1⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellInt
section
noncomputable section

namespace GlobalTheory.PoleInertCalc

variable {K : Type} [NormedField K]

def supN {m : ℕ} (ξ : Fin m → K × K) : ℝ := ⨆ i, max ‖(ξ i).1‖ ‖(ξ i).2‖

def hQ (d : K) {m : ℕ} (ξ : Fin m → K × K) : K := ∑ i, ((ξ i).1 ^ 2 - d * (ξ i).2 ^ 2)

def rad (d : K) {m : ℕ} (ξ : Fin m → K × K) : ℝ := max (max 1 (supN ξ)) ‖hQ d ξ‖

def c0 (q s : ℝ) : ℝ := (1 - q ^ (-s)) / (1 - q ^ (1 - s))

def nIso (q : ℝ) (m : ℕ) : ℝ := q ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q ^ m - q ^ ((m : ℤ) - 1)) - 1

def primDen (q : ℝ) (m e : ℕ) : ℝ :=
  if e = 0 then 1 - q ^ (-(2 * (m : ℤ))) else nIso q m * q ^ (-(2 * (m : ℤ))) * q ^ (1 - (e : ℤ))

def shellInt (q u : ℝ) (m j : ℕ) : ℝ :=
  u ^ j * primDen q m j + ∑ e ∈ Finset.range j, (primDen q m e - primDen q m (e + 1)) * u ^ (2 * j - e)

end GlobalTheory.PoleInertCalc

end
end

