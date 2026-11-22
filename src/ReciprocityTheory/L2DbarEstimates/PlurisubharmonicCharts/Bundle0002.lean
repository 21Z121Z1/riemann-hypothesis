import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0066

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
section
open Complex ComplexConjugate Filter Topology

namespace ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative

open ReciprocityTheory.L2DbarEstimates

variable {n : ℕ}

theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} (hmax : IsLocalMax g 0)
    (hd : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ g t) : deriv (deriv g) 0 ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hd2 : DifferentiableAt ℝ (deriv g) 0 := by
    by_contra hnd
    rw [deriv_zero_of_not_differentiableAt hnd] at hpos
    exact lt_irrefl _ hpos
  have h0 : deriv g 0 = 0 := hmax.deriv_eq_zero
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd2.hasDerivAt
  have hev : ∀ᶠ t in 𝓝[≠] (0:ℝ), 0 < slope (deriv g) 0 t := hslope.eventually (lt_mem_nhds hpos)
  rw [eventually_nhdsWithin_iff] at hev
  have hmax' : ∀ᶠ y in 𝓝 (0:ℝ), g y ≤ g 0 := hmax
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((hev.and hd).and hmax')
  have ht : 0 < ε / 2 := half_pos hε
  have hdist : ∀ y ∈ Set.Icc (0:ℝ) (ε / 2), dist y 0 < ε := by
    intro y hy
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hy.1]
    linarith [hy.2]
  have hcont : ContinuousOn g (Set.Icc 0 (ε / 2)) := fun y hy =>
    ((hball (hdist y hy)).1.2).continuousAt.continuousWithinAt
  have hdiffOn : DifferentiableOn ℝ g (Set.Ioo 0 (ε / 2)) := fun y hy =>
    ((hball (hdist y (Set.Ioo_subset_Icc_self hy))).1.2).differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope g ht hcont hdiffOn
  have hcpos : 0 < deriv g c := by
    have h := (hball (hdist c (Set.Ioo_subset_Icc_self hc))).1.1
      (Set.mem_compl_singleton_iff.mpr hc.1.ne')
    simp only [slope_def_field, h0, sub_zero] at h
    exact (div_pos_iff_of_pos_right hc.1).mp h
  rw [hcd, sub_zero] at hcpos
  have hgt := (div_pos_iff_of_pos_right ht).mp hcpos
  have hle := (hball (hdist (ε / 2) ⟨ht.le, le_rfl⟩)).2
  linarith

private theorem differentiableAt_fderiv_of_contDiffAt_two' {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (fderiv ℝ f) x :=
  (hf.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt (by norm_num)

set_option maxHeartbeats 400000 in

theorem snd_nonpos_of_isLocalMax {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (u : V n) : fderiv ℝ (fderiv ℝ f) x u u ≤ 0 := by
  have hD := differentiableAt_fderiv_of_contDiffAt_two' hf
  have hγd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • u) u t := fun t => by
    simpa using ((hasDerivAt_id' t).smul_const u).const_add x
  have hγ : Tendsto (fun t : ℝ => x + t • u) (𝓝 0) (𝓝 x) := by
    have h := (hγd 0).continuousAt.tendsto
    simpa using h
  have hev := hγ.eventually (ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf)
  have hgd : ∀ t : ℝ, DifferentiableAt ℝ f (x + t • u) →
      HasDerivAt (fun t : ℝ => f (x + t • u)) (fderiv ℝ f (x + t • u) u) t :=
    fun t ht => ht.hasFDerivAt.comp_hasDerivAt t (hγd t)
  have hg : IsLocalMax (fun t : ℝ => f (x + t • u)) 0 := by
    show ∀ᶠ t in 𝓝 (0:ℝ), f (x + t • u) ≤ f (x + (0:ℝ) • u)
    filter_upwards [hγ.eventually (show ∀ᶠ y in 𝓝 x, f y ≤ f x from hmax)] with t ht
    simpa using ht
  have hdg : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ (fun t : ℝ => f (x + t • u)) t := by
    filter_upwards [hev] with t ht using (hgd t ht).differentiableAt
  have hEq : deriv (fun t : ℝ => f (x + t • u)) =ᶠ[𝓝 0] fun t => fderiv ℝ f (x + t • u) u := by
    filter_upwards [hev] with t ht using (hgd t ht).deriv
  have hφ : HasFDerivAt (fun y => fderiv ℝ f y u) ((fderiv ℝ (fderiv ℝ f) x).flip u) (x + (0:ℝ) • u) := by
    rw [zero_smul, add_zero]
    exact (hD.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).congr_fderiv (by ext b; simp)
  have h3 := hφ.comp_hasDerivAt (0:ℝ) (hγd 0)
  have h4 : ((fderiv ℝ (fderiv ℝ f) x).flip u) u = fderiv ℝ (fderiv ℝ f) x u u :=
    ContinuousLinearMap.flip_apply _ _ _
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • u) u) (fderiv ℝ (fderiv ℝ f) x u u) 0 := by
    rw [← h4]
    exact h3
  have h := deriv_deriv_nonpos_of_isLocalMax hg hdg
  rwa [hEq.deriv_eq, h2.deriv] at h

private theorem wirtinger_wirtingerBar_ofReal_lemma_2 {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) (j k : Fin n) :
    ReciprocityTheory.L2DbarEstimates.wd n j (ReciprocityTheory.L2DbarEstimates.wdb n k (fun y => (f y : ℂ))) x =
      (((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) +
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) -
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) / 4 := by
  have hD := differentiableAt_fderiv_of_contDiffAt_two' hf
  have hψ : ∀ a : ReciprocityTheory.L2DbarEstimates.V n, HasFDerivAt (fun y => ((fderiv ℝ f y a : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip a)) x := by
    intro a
    have h1 : HasFDerivAt (fun y => fderiv ℝ f y a) ((fderiv ℝ (fderiv ℝ f) x).flip a) x :=
      (hD.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).congr_fderiv (by ext b; simp)
    exact (Complex.ofRealCLM.hasFDerivAt.comp x h1).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
  have hG : HasFDerivAt (fun y => (2⁻¹ : ℂ) * (((fderiv ℝ f y (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ f y (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)))
      ((2⁻¹ : ℂ) • (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip (ReciprocityTheory.L2DbarEstimates.bas n k)) +
        I • Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip (I • ReciprocityTheory.L2DbarEstimates.bas n k)))) x :=
    ((hψ (ReciprocityTheory.L2DbarEstimates.bas n k)).add ((hψ (I • ReciprocityTheory.L2DbarEstimates.bas n k)).const_mul I)).const_mul (2⁻¹ : ℂ)
  have hE : ReciprocityTheory.L2DbarEstimates.wdb n k (fun y => (f y : ℂ)) =ᶠ[𝓝 x] fun y =>
      (2⁻¹ : ℂ) * (((fderiv ℝ f y (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ f y (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) := by
    filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf] with y hy
    rw [ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy, div_eq_inv_mul]
  rw [ReciprocityTheory.L2DbarEstimates.wd_congr hE, ReciprocityTheory.L2DbarEstimates.wd, hG.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  push_cast
  linear_combination
    (-((fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) / 4) * I_sq

private theorem euclideanLeviForm_ofReal_eq_lemma_3 {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) (ξ : Fin n → ℂ) :
    ReciprocityTheory.L2DbarEstimates.leviV n (fun y => (f y : ℂ)) x ξ =
      ∑ j, ∑ k, (((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) +
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) -
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) / 4 *
          ξ j * conj (ξ k) := by
  simp only [ReciprocityTheory.L2DbarEstimates.leviV, wirtinger_wirtingerBar_ofReal_lemma_2 hf]

private theorem re_div_four_mul_mul_conj_mul_four (P Q : ℝ) (z w : ℂ) :
    (((P : ℂ) + I * (Q : ℂ)) / 4 * z * conj w).re * 4 =
      P * (z.re * w.re + z.im * w.im) - Q * (z.im * w.re - z.re * w.im) := by
  have h4 : ((P : ℂ) + I * (Q : ℂ)) / 4 = ((P / 4 : ℝ) : ℂ) + I * ((Q / 4 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h4]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem bilinear_apply_sum_sum (T : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℝ) (v w : Fin n → ReciprocityTheory.L2DbarEstimates.V n) :
    T (∑ j, v j) (∑ k, w k) = ∑ j, ∑ k, T (v j) (w k) := by
  have h : ∀ a : ReciprocityTheory.L2DbarEstimates.V n, T (∑ j, v j) a = ∑ j, T (v j) a := fun a => by
    rw [map_sum, ContinuousLinearMap.sum_apply]
  rw [h]
  exact Finset.sum_congr rfl fun j _ => map_sum (T (v j)) w Finset.univ

theorem leviV_re_eq {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (ξ : Fin n → ℂ) :
    (leviV n (fun y => (f y : ℂ)) x ξ).re * 4 =
      fderiv ℝ (fderiv ℝ f) x (∑ k, ((ξ k).re • bas n k + (ξ k).im • (I • bas n k)))
          (∑ k, ((ξ k).re • bas n k + (ξ k).im • (I • bas n k))) +
      fderiv ℝ (fderiv ℝ f) x (∑ k, ((ξ k).re • (I • bas n k) - (ξ k).im • bas n k))
          (∑ k, ((ξ k).re • (I • bas n k) - (ξ k).im • bas n k)) := by
  rw [euclideanLeviForm_ofReal_eq_lemma_3 hf, bilinear_apply_sum_sum, bilinear_apply_sum_sum]
  simp only [Complex.re_sum, Finset.sum_mul, re_div_four_mul_mul_conj_mul_four]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem leviV_re_nonpos_of_isLocalMax {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (ξ : Fin n → ℂ) : (leviV n (fun y => (f y : ℂ)) x ξ).re ≤ 0 := by
  have h := leviV_re_eq hf ξ
  have h1 := snd_nonpos_of_isLocalMax hf hmax
    (∑ k, ((ξ k).re • ReciprocityTheory.L2DbarEstimates.bas n k + (ξ k).im • (I • ReciprocityTheory.L2DbarEstimates.bas n k)))
  have h2 := snd_nonpos_of_isLocalMax hf hmax
    (∑ k, ((ξ k).re • (I • ReciprocityTheory.L2DbarEstimates.bas n k) - (ξ k).im • ReciprocityTheory.L2DbarEstimates.bas n k))
  linarith

theorem leviV_ofReal_add {f g : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((f y + g y : ℝ) : ℂ)) x ξ =
      leviV n (fun y => (f y : ℂ)) x ξ + leviV n (fun y => (g y : ℂ)) x ξ := by
  have hfg : ContDiffAt ℝ 2 (fun y => f y + g y) x := hf.add hg
  have hT : fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    have hev : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 x] fun y => fderiv ℝ f y + fderiv ℝ g y := by
      filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf,
        ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hg] with y hfy hgy
      exact fderiv_add hfy hgy
    rw [hev.fderiv_eq]
    exact fderiv_add (differentiableAt_fderiv_of_contDiffAt_two' hf)
      (differentiableAt_fderiv_of_contDiffAt_two' hg)
  rw [euclideanLeviForm_ofReal_eq_lemma_3 hfg, euclideanLeviForm_ofReal_eq_lemma_3 hf, euclideanLeviForm_ofReal_eq_lemma_3 hg, hT]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ContinuousLinearMap.add_apply]
  push_cast
  ring

theorem leviV_ofReal_const_mul {f : V n → ℝ} {x : V n} (c : ℝ) (hf : ContDiffAt ℝ 2 f x)
    (ξ : Fin n → ℂ) :
    leviV n (fun y => ((c * f y : ℝ) : ℂ)) x ξ = (c : ℂ) * leviV n (fun y => (f y : ℂ)) x ξ := by
  have hcf : ContDiffAt ℝ 2 (fun y => c * f y) x := contDiffAt_const.mul hf
  have hT : fderiv ℝ (fderiv ℝ (fun y => c * f y)) x = c • fderiv ℝ (fderiv ℝ f) x := by
    have hev : fderiv ℝ (fun y => c * f y) =ᶠ[𝓝 x] fun y => c • fderiv ℝ f y := by
      filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf] with y hy
      exact fderiv_const_mul hy c
    rw [hev.fderiv_eq]
    exact fderiv_const_smul (differentiableAt_fderiv_of_contDiffAt_two' hf) c
  rw [euclideanLeviForm_ofReal_eq_lemma_3 hcf, euclideanLeviForm_ofReal_eq_lemma_3 hf, hT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

end ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSum
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

def fsProj (f : ℕ) : (Fin f → ℝ) → UnitAddTorus (Fin f) := fun t i => (t i : UnitAddCircle)

theorem fsProj_isOpenQuotientMap (f : ℕ) : IsOpenQuotientMap (fsProj f) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

theorem fsProj_eq {f : ℕ} (s t : Fin f → ℝ) (h : fsProj f s = fsProj f t) :
    ∃ n : Fin f → ℤ, t = s + fun i => (n i : ℝ) := by
  have hi : ∀ i, ∃ k : ℤ, t i = s i + k := by
    intro i
    have h1 : ((s i : ℝ) : UnitAddCircle) = (t i : UnitAddCircle) := congrFun h i
    have h2 : (((t i - s i : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h2
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose n hn using hi
  exact ⟨n, funext fun i => by simp [hn i]⟩

def fsFun {f : ℕ} (g : (Fin f → ℝ) → ℂ) : UnitAddTorus (Fin f) → ℂ :=
  fun θ => g (Function.surjInv (fsProj_isOpenQuotientMap f).surjective θ)

theorem fsFun_proj {f : ℕ} (g : (Fin f → ℝ) → ℂ)
    (hper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x) (t : Fin f → ℝ) :
    fsFun g (fsProj f t) = g t := by
  unfold fsFun
  set s := Function.surjInv (fsProj_isOpenQuotientMap f).surjective (fsProj f t)
  have hs : fsProj f s = fsProj f t := Function.surjInv_eq _ _
  obtain ⟨n, hn⟩ := fsProj_eq s t hs
  rw [hn, hper]

theorem fsFun_continuous {f : ℕ} (g : (Fin f → ℝ) → ℂ) (hg : Continuous g)
    (hper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x) :
    Continuous (fsFun g) := by
  rw [(fsProj_isOpenQuotientMap f).isQuotientMap.continuous_iff]
  have : fsFun g ∘ fsProj f = g := funext fun t => fsFun_proj g hper t
  rw [this]; exact hg

theorem fs_mFourier_proj {f : ℕ} (m : Fin f → ℤ) (t : Fin f → ℝ) :
    UnitAddTorus.mFourier m (fsProj f t) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ k, (m k : ℂ) * (t k : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fsProj, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem four_sum (f : ℕ) : FOURSumStatement f := by
  intro Ω h hΩ hh hper h0 hsum x
  set g : (Fin f → ℝ) → ℂ := fun x => h (fun k => (x k : ℂ)) with hgdef
  have hreal : ∀ y : Fin f → ℝ, (fun k => ((y k : ℝ) : ℂ)) ∈ tube f Ω := by
    intro y
    show (fun k => ((y k : ℝ) : ℂ).im) ∈ Ω
    have e : (fun k => (((y k : ℝ) : ℂ)).im) = 0 := by funext k; simp
    rw [e]; exact h0
  have hg : Continuous g := by
    have hc : Continuous (fun y : Fin f → ℝ => (fun k => ((y k : ℝ) : ℂ))) := by fun_prop
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hopen : IsOpen (tube f Ω) := hΩ.preimage (by fun_prop)
    exact ((hh _ (hreal y)).differentiableAt (hopen.mem_nhds (hreal y))).continuousAt.comp
      hc.continuousAt
  have hgper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x := by
    intro y n
    have := hper _ (hreal y) n
    simp only [hgdef]
    convert this using 2
    funext k
    simp
  let F : C(UnitAddTorus (Fin f), ℂ) := ⟨fsFun g, fsFun_continuous g hg hgper⟩
  have hcoef : ∀ ν, UnitAddTorus.mFourierCoeff F ν = fourCoeff h 0 ν := by
    intro ν
    rw [UnitAddTorus.mFourierCoeff_eq_integral _ ν 0, fourCoeff]
    have hset : ({x : Fin f → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin f → ℝ) i) ((0 : Fin f → ℝ) i + 1)}
        : Set (Fin f → ℝ)) = Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1) := by
      ext x; simp
    rw [hset]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have h1 : (fun i => ((t i : ℝ) : UnitAddCircle)) = fsProj f t := rfl
    have h2 : F (fsProj f t) = g t := fsFun_proj g hgper t
    beta_reduce
    rw [h1, h2, smul_eq_mul, fs_mFourier_proj]
    simp only [hgdef, Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero, Pi.neg_apply, Int.cast_neg]
    rw [mul_comm]
    congr 2
    simp [Finset.sum_neg_distrib]
  have hs : Summable (UnitAddTorus.mFourierCoeff F) := by
    refine Summable.of_norm ?_
    simpa [hcoef] using hsum
  have := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (fsProj f x)
  simp only [hcoef, smul_eq_mul, fs_mFourier_proj] at this
  rw [show F (fsProj f x) = g x from fsFun_proj g hgper x] at this
  exact this

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IndCount
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

open Finset

theorem mem_multiLe_iff {n j : ℕ} {α : Fin n → ℕ} : α ∈ multiLe n j ↔ ∑ i, α i ≤ j := by
  unfold multiLe
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hα⟩
    rw [Finset.mem_range] at ha
    rw [Nat.mem_antidiagonalTuple] at hα
    omega
  · intro h
    exact ⟨∑ i, α i, Finset.mem_range.2 (by omega), Nat.mem_antidiagonalTuple.2 rfl⟩

theorem card_multiLe_succ (n j : ℕ) :
    (multiLe (n + 1) j).card = ∑ a ∈ range (j + 1), (multiLe n (j - a)).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij' (fun α _ => (⟨α 0, Fin.tail α⟩ : Σ _ : ℕ, Fin n → ℕ))
    (fun p _ => (Fin.cons p.1 p.2 : Fin (n + 1) → ℕ)) ?_ ?_ ?_ ?_
  · intro α hα
    simp only [mem_multiLe_iff, Fin.sum_univ_succ] at hα
    simp only [Finset.mem_sigma, Finset.mem_range, mem_multiLe_iff, Fin.tail]
    exact ⟨by omega, by omega⟩
  · rintro ⟨a, β⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range, mem_multiLe_iff] at hp
    simp only [mem_multiLe_iff, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    omega
  · intro α _
    exact Fin.cons_self_tail α
  · rintro ⟨a, β⟩ _
    simp only [Fin.cons_zero, Fin.tail_cons]

theorem ind_count : INDCountStatement := by
  unfold INDCountStatement
  intro n
  induction n with
  | zero =>
    intro j
    have h : multiLe 0 j = {finZeroElim} := by
      ext α
      simp only [mem_multiLe_iff, Finset.mem_singleton, Fin.sum_univ_zero]
      exact ⟨fun _ => funext fun i => i.elim0, fun _ => Nat.zero_le _⟩
    rw [h, Finset.card_singleton]
    simp
  | succ n ih =>
    intro j
    induction j with
    | zero =>
      rw [card_multiLe_succ, Finset.sum_range_one, ih]
      simp
    | succ j ihj =>
      rw [card_multiLe_succ, Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      rw [← card_multiLe_succ n j, ihj, ih (j + 1)]
      have h1 : (j + (n + 1)).choose (n + 1) = (j + 1 + n).choose (n + 1) := by
        congr 1
        omega
      have h2 : (j + 1 + (n + 1)).choose (n + 1) =
          (j + 1 + n).choose n + (j + 1 + n).choose (n + 1) := by
        rw [show j + 1 + (n + 1) = (j + 1 + n) + 1 by omega]
        exact Nat.choose_succ_succ' _ _
      omega

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

section Newton

open Polynomial

private theorem trace_pow_eq_zero_of_le_dim {K : Type*} [Field K] (r : ℕ)
    (N : Matrix (Fin r) (Fin r) K) (h : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) :
    ∀ k, 1 ≤ k → (N ^ k).trace = 0 := by
  first | exact UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim .. | (apply UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> first | assumption | infer_instance)

private theorem trace_aeval_X_mul {K : Type*} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ k : ℕ, (N ^ (k + 1)).trace = 0) (p : K[X]) :
    (aeval N (X * p)).trace = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, Matrix.trace_add, hp, hq, add_zero]
  | monomial n a =>
    rw [show (X * monomial n a : K[X]) = monomial (n + 1) a by
      rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]; ring]
    rw [aeval_monomial, ← Algebra.smul_def, Matrix.trace_smul, h, smul_zero]

private theorem isNilpotent_of_trace_pow_succ {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (h : ∀ k : ℕ, (N ^ (k + 1)).trace = 0) : IsNilpotent N := by
  classical
  have hint : IsIntegral K N := Algebra.IsIntegral.isIntegral N
  have hμ : minpoly K N ≠ 0 := minpoly.ne_zero hint
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly K N) hμ 0
  set m := (minpoly K N).rootMultiplicity 0
  simp only [map_zero, sub_zero] at hq hnd
  have hcop : IsCoprime (X ^ (m + 1)) q :=
    ((Polynomial.irreducible_X).coprime_iff_not_dvd.mpr hnd).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hXq : aeval N (X ^ (m + 1) * q) = 0 := by
    rw [show (X ^ (m + 1) * q : K[X]) = X * minpoly K N by rw [hq]; ring, map_mul,
      minpoly.aeval, mul_zero]
  have h1 : aeval N (u * X ^ (m + 1)) + aeval N (v * q) = 1 := by
    rw [← map_add, huv, map_one]
  have hprod : aeval N (u * X ^ (m + 1)) * aeval N (v * q) = 0 := by
    rw [← map_mul, show (u * X ^ (m + 1) * (v * q) : K[X]) = u * v * (X ^ (m + 1) * q) by ring,
      map_mul, hXq, mul_zero]
  set e := aeval N (u * X ^ (m + 1)) with he_def
  have he : IsIdempotentElem e := by
    have : aeval N (v * q) = 1 - e := by rw [← h1]; abel
    rw [this, mul_sub, mul_one, sub_eq_zero] at hprod
    exact hprod.symm
  have hτ : e.trace = 0 := by
    rw [he_def, show (u * X ^ (m + 1) : K[X]) = X * (u * X ^ m) by ring]
    exact trace_aeval_X_mul N h _
  have hle : IsIdempotentElem (Matrix.toLin' e) := by
    have h3 := Matrix.toLin'_mul e e
    rw [he.eq] at h3
    exact h3.symm
  have hl0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hle (by rw [Matrix.trace_toLin'_eq, hτ])
  have he0 : e = 0 := Matrix.toLin'.map_eq_zero_iff.mp hl0
  have hvq : aeval N (v * q) = 1 := by rw [← h1, he0, zero_add]
  refine ⟨m + 1, ?_⟩
  calc N ^ (m + 1) = N ^ (m + 1) * aeval N (v * q) := by rw [hvq, mul_one]
    _ = aeval N (v * (X ^ (m + 1) * q)) := by
        rw [show (v * (X ^ (m + 1) * q) : K[X]) = X ^ (m + 1) * (v * q) by ring,
          map_mul (aeval N) (X ^ (m + 1)), map_pow, aeval_X]
    _ = 0 := by rw [map_mul, hXq, mul_zero]

end Newton

theorem isNilpotent_of_trace_pow {K : Type*} [Field K] [CharZero K] (r : ℕ)
    (N : Matrix (Fin r) (Fin r) K) (h : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) :
    IsNilpotent N :=
  isNilpotent_of_trace_pow_succ N fun k => trace_pow_eq_zero_of_le_dim r N h (k + 1) (by omega)

end

end ReciprocityTheory.L2DbarEstimates.Y
end

