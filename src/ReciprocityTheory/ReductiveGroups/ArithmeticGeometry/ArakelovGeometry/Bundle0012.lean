import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0011
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamSt
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.MorseGenSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology ContDiff

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem det_interp (M₀ M₁ : Matrix (Fin D) (Fin D) ℂ) (t : ℂ) :
    ((1 - t) • M₀ + t • M₁).det = ∑ i ∈ Finset.range (D + 1),
      (D.choose i : ℂ) * t ^ i * (1 - t) ^ (D - i) *
        mixedDisc (fun j : Fin D => if j.val < i then M₁ else M₀) := by
  rw [add_comm]
  exact ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc t (1 - t) M₁ M₀

theorem gaamix_cxHessian_comb {a b ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (s u : ℝ)
    (ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 a y') (hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 b y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => s * a y' + u * b y') :
    cxHessian ψ y = (s : ℂ) • cxHessian a y + (u : ℂ) • cxHessian b y := by
  have hd : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => s • fderiv ℝ a y' + u • fderiv ℝ b y' := by
    filter_upwards [hψ.eventuallyEq_nhds, ha, hb] with y' h1 h2 h3
    rw [h1.fderiv_eq]
    have d2 := h2.differentiableAt (by norm_num)
    have d3 := h3.differentiableAt (by norm_num)
    exact ((d2.hasFDerivAt.const_mul s).add (d3.hasFDerivAt.const_mul u)).fderiv
  have hH : fderiv ℝ (fderiv ℝ ψ) y =
      s • fderiv ℝ (fderiv ℝ a) y + u • fderiv ℝ (fderiv ℝ b) y := by
    rw [hd.fderiv_eq]
    have d2 := (ha.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have d3 := (hb.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact ((d2.hasFDerivAt.const_smul s).add (d3.hasFDerivAt.const_smul u)).fderiv
  ext i j
  simp only [cxHessian, hH, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply]
  push_cast
  ring

theorem gaamix_ne_zero_of_mcPts {P : Ideal (MRing (GlobalTheory κ))} {z : Ix κ → ℂ} (hz : z ∈ mcPts P) :
    z ≠ 0 := by
  obtain ⟨i, hi⟩ := hz.1 ()
  rintro rfl
  exact hi rfl

theorem gaamix_contDiffAt_log {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m)
    {γ : (Fin D → ℂ) → Ix κ → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : γ y ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (m.ρ (γ y'))) y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hγ
  have hdU : DifferentiableOn ℂ γ U := fun y' h => (hU y' h).differentiableWithinAt
  have hc : ContDiffAt ℝ ∞ γ y :=
    ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hUo hdU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ
  have hρ : ContDiffAt ℝ ∞ m.ρ (γ y) :=
    hm.contDiffAt (isOpen_ne.mem_nhds hy)
  exact_mod_cast (contDiffAt_infty.mp ((hρ.comp y hc).log (m.pos _ hy).ne')) 2

theorem gaamix_log_interp (m₀ m₁ : ConeMetric ℂ (Ix κ)) (t : ℝ) {z : Ix κ → ℂ} (hz : z ≠ 0) :
    Real.log ((interp m₀ m₁ t).ρ z) = (1 - t) * Real.log (m₀.ρ z) + t * Real.log (m₁.ρ z) := by
  have h₀ := m₀.pos z hz
  have h₁ := m₁.pos z hz
  show Real.log (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) = _
  rw [Real.log_mul (Real.rpow_pos_of_pos h₀ _).ne' (Real.rpow_pos_of_pos h₁ _).ne',
    Real.log_rpow h₀, Real.log_rpow h₁]

theorem gbamix_maDensity_interp {m₀ m₁ : ConeMetric ℂ (Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) (t : ℝ) {γ : (Fin D → ℂ) → Ix κ → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ≠ 0) :
    maDensity (fun j y' => purePot (interp m₀ m₁ t) D j (γ y')) y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        maDensity (fun j y' => mixPot m₀ m₁ D i j (γ y')) y := by
  have hev : ∀ᶠ y' in 𝓝 y, ∀ᶠ y'' in 𝓝 y', DifferentiableAt ℂ γ y'' ∧ γ y'' ≠ 0 :=
    hγ.eventually_nhds
  have ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (m₀.ρ (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact gaamix_contDiffAt_log h₀ (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (m₁.ρ (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact gaamix_contDiffAt_log h₁ (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hψ : (fun y' => Real.log ((interp m₀ m₁ t).ρ (γ y'))) =ᶠ[𝓝 y]
      fun y' => (1 - t) * Real.log (m₀.ρ (γ y')) + t * Real.log (m₁.ρ (γ y')) := by
    filter_upwards [hγ] with y' hy'
    exact gaamix_log_interp m₀ m₁ t hy'.2
  have hH := gaamix_cxHessian_comb (1 - t) t ha hb hψ
  set H₀ := cxHessian (fun y'' => Real.log (m₀.ρ (γ y''))) y
  set H₁ := cxHessian (fun y'' => Real.log (m₁.ρ (γ y''))) y
  have hmix : ∀ i, (fun k => cxHessian (fun y' => mixPot m₀ m₁ D i k (γ y')) y) =
      fun j : Fin D => if j.val < i then H₁ else H₀ := by
    intro i
    funext k
    by_cases hk : k.val < i
    · simp only [mixPot, hk, if_true]; rfl
    · simp only [mixPot, hk, if_false]; rfl
  have hpure : (fun k => cxHessian (fun y' => purePot (interp m₀ m₁ t) D k (γ y')) y) =
      fun _ => (1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁ := by
    funext k
    show cxHessian (fun y' => Real.log ((interp m₀ m₁ t).ρ (γ y'))) y = _
    rw [hH]
    push_cast
    rfl
  simp only [maDensity]
  have hc : mixedDisc (fun _ : Fin D => (1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁) =
      ((1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁).det := ReciprocityTheory.AnForm.A.mdisc_const _
  rw [hpure, hc, det_interp, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmix i]
  have e : (D.choose i : ℂ) * (t : ℂ) ^ i * (1 - (t : ℂ)) ^ (D - i) =
      ((D.choose i * t ^ i * (1 - t) ^ (D - i) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  ring

theorem gbamix_ne_zero_of_blocks {z : Ix κ → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : z ≠ 0 := by
  obtain ⟨i, hi⟩ := hz ()
  rintro rfl
  exact hi rfl

theorem gbamix_smoothHerm_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  exact (show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m.ρ {z | z ≠ 0} from hm).mono
    fun z hz => gbamix_ne_zero_of_blocks hz

theorem gbamix_logRatio_deg {m₀ m₁ : ConeMetric ℂ (Ix κ)} (c : Unit → ℂ) (z : Ix κ → ℂ)
    (hc : ∀ k, c k ≠ 0) : logRatio m₀ m₁ (fun p => c p.1 * z p) = logRatio m₀ m₁ z := by
  have e : (fun p : Ix κ => c p.1 * z p) = c () • z := by
    funext p
    rfl
  unfold logRatio
  rw [e, m₀.smul, m₁.smul, mul_div_mul_left _ _ (norm_ne_zero_iff.2 (hc ()))]

theorem gbamix_smooth_logRatio {m₀ m₁ : ConeMetric ℂ (Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio m₀ m₁) {z | z ≠ 0} := by
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀.ρ {z | z ≠ 0} := h₀
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁.ρ {z | z ≠ 0} := h₁
  show ContDiffOn ℝ _ (fun z => Real.log (m₁.ρ z / m₀.ρ z)) {z | z ≠ 0}
  exact (h1.div h0 fun z hz => (m₀.pos z hz).ne').log fun z hz =>
    (div_pos (m₁.pos z hz) (m₀.pos z hz)).ne'

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsBoundIteratedFDerivCompact
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff

theorem contDiffOn_of_analyticOnNhd {D : ℕ} {J : Type} [Fintype J] {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (hγ : AnalyticOnNhd ℂ γ U) : ContDiffOn ℝ ∞ γ U := by
  exact fun x hx => ((hγ x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt

theorem contDiffOn_log_metric_param {D : ℕ} {J : Type} [Fintype J] {P : Ideal (MvPolynomial J ℤ)}
    {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → J → ℂ} (m : ConeMetric ℂ J) (hm : IsSmoothMetric m)
    (hγ : IsParam P U γ) : ContDiffOn ℝ ∞ (fun y => Real.log (m.ρ (γ y))) U := by
  obtain ⟨_, hana, hpts, _⟩ := hγ
  have hγs : ContDiffOn ℝ ∞ γ U := contDiffOn_of_analyticOnNhd hana
  have hρ := hm.comp hγs (fun y hy => (hpts y hy).1)
  exact hρ.log (fun y hy => (m.pos _ (hpts y hy).1).ne')

theorem measurable_coneMetric {J : Type} [Fintype J] (m : ConeMetric ℂ J) (hm : IsSmoothMetric m) :
    Measurable m.ρ := by
  exact measurable_of_continuousOn_compl_singleton 0 (hm.continuousOn.mono fun z hz => hz)

theorem sectionFunction_homogeneous {J : Type} [Fintype J] {b : MvPolynomial J ℚ} {n : ℕ}
    (hb : ∃ f : MvPolynomial J ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f) (c : ℂ)
    (z : J → ℂ) : secFun b (c • z) = c ^ n * secFun b z := by
  obtain ⟨f, hf, rfl⟩ := hb
  simp only [secFun, MvPolynomial.map_map]
  have hg := hf.map ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ))
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have := hg (MvPolynomial.mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem differentiable_mvPolynomial_eval {J : Type} [Fintype J] (p : MvPolynomial J ℂ) :
    Differentiable ℂ (fun z : J → ℂ => eval z p) := by
  refine MvPolynomial.induction_on (motive := fun p => Differentiable ℂ fun z : J → ℂ => eval z p) p ?_ ?_ ?_
  · intro a
    simp only [MvPolynomial.eval_C]
    exact differentiable_const a
  · intro p q hp hq
    simp only [map_add]
    exact hp.add hq
  · intro p i hp
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (differentiable_apply i)

theorem exists_bound_iteratedFDeriv_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {U K : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hK : IsCompact K)
    (hKU : K ⊆ U) (k : ℕ) : ∃ B, 0 ≤ B ∧ ∀ y ∈ K, ‖iteratedFDeriv ℝ k f y‖ ≤ B := by
  have hcont : ContinuousOn (fun y => iteratedFDeriv ℝ k f y) U := fun y hy =>
    ((hf.contDiffAt (hU.mem_nhds hy)).continuousAt_iteratedFDeriv (by exact_mod_cast le_top)).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKU)
  exact ⟨max C 0, le_max_right _ _, fun y hy => (hC y hy).trans (le_max_left _ _)⟩

theorem exp_eq_interpolatedWeight {J : Type} [Fintype J] (m₀ m₁ : ConeMetric ℂ J) (t : ℝ) (n : ℕ)
    (z : J → ℂ) (hz : z ≠ 0) :
    Real.exp (-((n : ℝ) * (2 * ((1 - t) * Real.log (m₀.ρ z) + t * Real.log (m₁.ρ z))))) =
      wgt (interp m₀ m₁ t) n z := by
  have h0 := m₀.pos z hz
  have h1 := m₁.pos z hz
  have hA : 0 < m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t :=
    mul_pos (Real.rpow_pos_of_pos h0 _) (Real.rpow_pos_of_pos h1 _)
  have hlog : Real.log (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) =
      (1 - t) * Real.log (m₀.ρ z) + t * Real.log (m₁.ρ z) := by
    rw [Real.log_mul (Real.rpow_pos_of_pos h0 _).ne' (Real.rpow_pos_of_pos h1 _).ne',
      Real.log_rpow h0, Real.log_rpow h1]
  show _ = ((m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) ^ (2 * n))⁻¹
  rw [← hlog, Real.exp_neg,
    show (n : ℝ) * (2 * Real.log (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t)) =
      ((2 * n : ℕ) : ℝ) * Real.log (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) by push_cast; ring,
    Real.exp_nat_mul, Real.exp_log hA]

theorem iteratedFDeriv_linear_comb_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ₀ ψ₁ : E → ℝ) (y₀ y : E) (k : ℕ) (a₀ a₁ : ℝ)
    (h₀ : ContDiffAt ℝ k ψ₀ (y₀ + y)) (h₁ : ContDiffAt ℝ k ψ₁ (y₀ + y)) :
    iteratedFDeriv ℝ k (fun y => a₀ * ψ₀ (y₀ + y) + a₁ * ψ₁ (y₀ + y)) y =
      a₀ • iteratedFDeriv ℝ k ψ₀ (y₀ + y) + a₁ • iteratedFDeriv ℝ k ψ₁ (y₀ + y) := by
  have hshift : ∀ ψ : E → ℝ, iteratedFDeriv ℝ k (fun y => ψ (y₀ + y)) y = iteratedFDeriv ℝ k ψ (y₀ + y) := by
    intro ψ
    have := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ) (f := ψ) (s := Set.univ) k y₀ y
    simpa [iteratedFDerivWithin_univ] using this
  have hc0 : ContDiffAt ℝ k (fun y => ψ₀ (y₀ + y)) y := h₀.comp y (contDiffAt_const.add contDiffAt_id)
  have hc1 : ContDiffAt ℝ k (fun y => ψ₁ (y₀ + y)) y := h₁.comp y (contDiffAt_const.add contDiffAt_id)
  have e : (fun y => a₀ * ψ₀ (y₀ + y) + a₁ * ψ₁ (y₀ + y)) =
      fun y => a₀ • (fun y => ψ₀ (y₀ + y)) y + a₁ • (fun y => ψ₁ (y₀ + y)) y := rfl
  rw [e, fun_iteratedFDeriv_add_apply (hc0.const_smul a₀) (hc1.const_smul a₁),
    iteratedFDeriv_const_smul_apply' hc0, iteratedFDeriv_const_smul_apply' hc1, hshift, hshift]

theorem iteratedFDeriv_convexComb_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ₀ ψ₁ : E → ℝ) (y₀ y : E) (k : ℕ) {t B₀ B₁ : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ContDiffAt ℝ k ψ₀ (y₀ + y)) (h₁ : ContDiffAt ℝ k ψ₁ (y₀ + y))
    (hb₀ : ‖iteratedFDeriv ℝ k ψ₀ (y₀ + y)‖ ≤ B₀) (hb₁ : ‖iteratedFDeriv ℝ k ψ₁ (y₀ + y)‖ ≤ B₁) :
    ‖iteratedFDeriv ℝ k (fun y => (2 * (1 - t)) * ψ₀ (y₀ + y) + (2 * t) * ψ₁ (y₀ + y)) y‖ ≤
      2 * (B₀ + B₁) := by
  rw [iteratedFDeriv_linear_comb_shift ψ₀ ψ₁ y₀ y k _ _ h₀ h₁]
  obtain ⟨ht0, ht1⟩ := ht
  have n0 := norm_nonneg (iteratedFDeriv ℝ k ψ₀ (y₀ + y))
  have n1 := norm_nonneg (iteratedFDeriv ℝ k ψ₁ (y₀ + y))
  calc ‖(2 * (1 - t)) • iteratedFDeriv ℝ k ψ₀ (y₀ + y) + (2 * t) • iteratedFDeriv ℝ k ψ₁ (y₀ + y)‖
      ≤ ‖(2 * (1 - t)) • iteratedFDeriv ℝ k ψ₀ (y₀ + y)‖ + ‖(2 * t) • iteratedFDeriv ℝ k ψ₁ (y₀ + y)‖ :=
        norm_add_le _ _
    _ = (2 * (1 - t)) * ‖iteratedFDeriv ℝ k ψ₀ (y₀ + y)‖ + (2 * t) * ‖iteratedFDeriv ℝ k ψ₁ (y₀ + y)‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith)]
    _ ≤ 2 * (B₀ + B₁) := by
        nlinarith [mul_le_mul_of_nonneg_left hb₀ (by linarith : (0 : ℝ) ≤ 1 - t),
          mul_le_mul_of_nonneg_left hb₁ ht0, mul_nonneg ht0 hB₀, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) hB₁]

theorem integrable_normSq_combination {X : Type*} [MeasurableSpace X] {μ : Measure X} {r : ℕ}
    (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (c : Fin r → ℂ) : Integrable (fun x => ‖∑ i, c i * s i x‖ ^ 2 * w x) μ := by
  have hg : Integrable (fun x => ∑ i, ∑ j, (starRingEnd ℂ (c i) * c j) *
      (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _
  refine hg.re.congr (ae_of_all _ fun x => ?_)
  have h : ((‖∑ i, c i * s i x‖ ^ 2 * w x : ℝ) : ℂ) = ∑ i, ∑ j, (starRingEnd ℂ (c i) * c j) *
      (starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) := by
    rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, map_sum,
      Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul]
    ring
  dsimp only
  rw [← h]
  rfl

theorem cone_metric_weight_nonneg {J : Type} [Fintype J] (m : ConeMetric ℂ J) (n : ℕ) (z : J → ℂ) :
    0 ≤ wgt m n z := by
  exact inv_nonneg.2 (pow_nonneg (m.nonneg z) _)

theorem sectionNormSq_nonneg {J : Type} [Fintype J] {μ : Measure (J → ℂ)} {r : ℕ}
    (s : Fin r → (J → ℂ) → ℂ) (m : ConeMetric ℂ J) (n : ℕ) (c : Fin r → ℂ) :
    0 ≤ bNormSq μ s (wgt m n) c := by
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (cone_metric_weight_nonneg m n x)

theorem isDegreeZero_weightedCombination {J : Type} [Fintype J] (m : ConeMetric ℂ J) {n r : ℕ}
    {b : Fin r → MvPolynomial J ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial J ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (c : Fin r → ℂ) :
    IsDegZero (fun z => ‖∑ k, c k * secFun (b k) z‖ ^ 2 * wgt m n z) := by
  intro c' z hc
  have hs : ∀ k, secFun (b k) (c' • z) = c' ^ n * secFun (b k) z := fun k => sectionFunction_homogeneous (hb k) c' z
  simp only [hs]
  have hsum : ∑ k, c k * (c' ^ n * secFun (b k) z) = c' ^ n * ∑ k, c k * secFun (b k) z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum, norm_mul, norm_pow]
  simp only [wgt]
  rw [m.smul, mul_pow ‖c'‖ (m.ρ z), mul_inv]
  have hc' : ‖c'‖ ^ (2 * n) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hc)
  calc (‖c'‖ ^ n * ‖∑ k, c k * secFun (b k) z‖) ^ 2 * ((‖c'‖ ^ (2 * n))⁻¹ * (m.ρ z ^ (2 * n))⁻¹)
      = (‖c'‖ ^ (2 * n) * (‖c'‖ ^ (2 * n))⁻¹) *
          (‖∑ k, c k * secFun (b k) z‖ ^ 2 * (m.ρ z ^ (2 * n))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hc', one_mul]

theorem measurable_interpolatedWeight {J : Type} [Fintype J] (m₀ m₁ : ConeMetric ℂ J)
    (h₀ : IsSmoothMetric m₀) (h₁ : IsSmoothMetric m₁) (t : ℝ) (n : ℕ) :
    Measurable (wgt (interp m₀ m₁ t) n) := by
  have hρ0 := measurable_coneMetric m₀ h₀
  have hρ1 := measurable_coneMetric m₁ h₁
  show Measurable fun z => ((m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) ^ (2 * n))⁻¹
  exact (((hρ0.pow_const _).mul (hρ1.pow_const _)).pow_const _).inv

theorem differentiable_sectionCombination {J : Type} [Fintype J] {r : ℕ} (b : Fin r → MvPolynomial J ℚ)
    (c : Fin r → ℂ) : Differentiable ℂ (fun z : J → ℂ => ∑ k, c k * secFun (b k) z) := by
  have h : ∀ k, Differentiable ℂ (secFun (b k)) := fun k => differentiable_mvPolynomial_eval _
  fun_prop

theorem setIntegral_parametrisation_le {J : Type} [Fintype J] {D : ℕ} {μ : Measure (J → ℂ)} {δ : ℝ}
    {γ' : (Fin D → ℂ) → J → ℂ} {ν' : (Fin D → ℂ) → ℝ}
    (hν' : IsDensityFor μ (Metric.ball 0 δ) γ' ν')
    {g : (J → ℂ) → ℝ} (hgm : Measurable g) (hg0 : IsDegZero g) (hgnn : ∀ z, 0 ≤ g z)
    (hgi : Integrable g μ) {h : (Fin D → ℂ) → ℝ} (hc : ContinuousOn h (Metric.ball 0 δ))
    (heq : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) δ, h y = g (γ' y) * ν' y) :
    IntegrableOn h (Metric.ball 0 δ) ∧ ∫ y in Metric.ball (0 : Fin D → ℂ) δ, h y ≤ ∫ z, g z ∂μ := by
  obtain ⟨_, hpos, hden⟩ := hν'
  have hU : MeasurableSet (Metric.ball (0 : Fin D → ℂ) δ) := measurableSet_ball
  have hh0 : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) δ, 0 ≤ h y := fun y hy => by
    rw [heq y hy]; exact mul_nonneg (hgnn _) (hpos y hy).le
  have hkey := hden g hgm hg0 hgnn
  have hlin : ∫⁻ y in Metric.ball (0 : Fin D → ℂ) δ, ENNReal.ofReal (h y) =
      ∫⁻ y in Metric.ball (0 : Fin D → ℂ) δ, ENNReal.ofReal (g (γ' y) * ν' y) :=
    setLIntegral_congr_fun hU (fun y hy => by rw [heq y hy])
  have hle : ∫⁻ y in Metric.ball (0 : Fin D → ℂ) δ, ENNReal.ofReal (h y) ≤ ∫⁻ z, ENNReal.ofReal (g z) ∂μ := by
    rw [hlin, ← hkey]
    exact setLIntegral_le_lintegral _ _
  have hgfin : ∫⁻ z, ENNReal.ofReal (g z) ∂μ < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hgnn)]
    exact ENNReal.ofReal_lt_top
  have hmeas : AEStronglyMeasurable h (volume.restrict (Metric.ball (0 : Fin D → ℂ) δ)) :=
    hc.aestronglyMeasurable hU
  have hnn : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : Fin D → ℂ) δ)] h := ae_restrict_of_forall_mem hU hh0
  have hint : IntegrableOn h (Metric.ball 0 δ) := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hle hgfin
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hgnn) hgi.aestronglyMeasurable]
  exact ENNReal.toReal_mono hgfin.ne hle

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

