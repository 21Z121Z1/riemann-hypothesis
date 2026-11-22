import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaFderivCompApply
section
open Complex ComplexConjugate Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ}

private theorem I_pow_three' : I ^ 3 = -I := by
  rw [pow_succ, I_sq, neg_one_mul]

private theorem eq_sum_coord_smul_basis (w : V n) : w = ∑ j, w j • bas n j := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr w]
  simp [bas]

private theorem clm_apply_eq_sum_wd_wdb_basis (D : V n →L[ℝ] ℂ) (w : V n) :
    D w = ∑ b, (w b * ((D (bas n b) - I * D (I • bas n b)) / 2) +
      conj (w b) * ((D (bas n b) + I * D (I • bas n b)) / 2)) := by
  conv_lhs => rw [eq_sum_coord_smul_basis w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  conv_lhs => rw [← Complex.re_add_im (w b), add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul,
    map_add, map_smul, map_smul]
  conv_rhs => rw [← Complex.re_add_im (w b)]
  simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination ((w b).im * D (I • bas n b)) * Complex.I_sq

private theorem fderiv_comp_holomorphic_apply {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (v : V n) :
    fderiv ℝ (U ∘ G) y v = fderiv ℝ U (G y) (fderiv ℂ G y v) := by
  have hG' : HasFDerivAt G ((fderiv ℂ G y).restrictScalars ℝ) y := hG.hasFDerivAt.restrictScalars ℝ
  rw [(hU.hasFDerivAt.comp y hG').fderiv]
  rfl

private theorem wdb_comp_holomorphic_eq_sum_conj {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (k : Fin n) :
    wdb n k (U ∘ G) y = ∑ b, wdb n b U (G y) * conj (fderiv ℂ G y (bas n k) b) := by
  unfold wdb
  rw [fderiv_comp_holomorphic_apply hU hG, fderiv_comp_holomorphic_apply hU hG, map_smul (fderiv ℂ G y),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (fderiv ℂ G y (bas n k)),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (I • fderiv ℂ G y (bas n k))]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, I_pow_three']
  ring

private theorem wd_comp_holomorphic_eq_sum {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (k : Fin n) :
    wd n k (U ∘ G) y = ∑ b, wd n b U (G y) * fderiv ℂ G y (bas n k) b := by
  unfold wd
  rw [fderiv_comp_holomorphic_apply hU hG, fderiv_comp_holomorphic_apply hU hG, map_smul (fderiv ℂ G y),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (fderiv ℂ G y (bas n k)),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (I • fderiv ℂ G y (bas n k))]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, I_pow_three']
  ring

private theorem differentiableAt_fderiv_basis_coord_of_contDiffAt {G : V n → V n} {y : V n} (hG : ContDiffAt ℂ 2 G y) (k b : Fin n) :
    DifferentiableAt ℂ (fun v => fderiv ℂ G v (bas n k) b) y := by
  have h1 : ContDiffAt ℂ 1 (fderiv ℂ G) y := hG.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℂ 1 (fun v => fderiv ℂ G v (bas n k)) y := h1.clm_apply contDiffAt_const
  have h3 : ContDiffAt ℂ 1 (fun v => (EuclideanSpace.proj b : V n →L[ℂ] ℂ) (fderiv ℂ G v (bas n k))) y :=
    (EuclideanSpace.proj b : V n →L[ℂ] ℂ).contDiff.contDiffAt.comp y h2
  exact h3.differentiableAt one_ne_zero

private theorem differentiableAt_wdb_of_contDiffAt {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℝ 2 g y) (k : Fin n) :
    DifferentiableAt ℝ (wdb n k g) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by norm_num)
  have hb : ∀ u : V n, DifferentiableAt ℝ (fun v => fderiv ℝ g v u) y := fun u =>
    (h1.clm_apply contDiffAt_const).differentiableAt one_ne_zero
  have := ((hb (bas n k)).add ((hb (I • bas n k)).const_mul I)).mul_const (2⁻¹ : ℂ)
  unfold wdb
  simp only [div_eq_mul_inv]
  exact this

private theorem wd_finset_sum {ι : Type*} (s : Finset ι) (Φ : ι → V n → ℂ) (y : V n)
    (hΦ : ∀ i ∈ s, DifferentiableAt ℝ (Φ i) y) (j : Fin n) :
    wd n j (fun w => ∑ i ∈ s, Φ i w) y = ∑ i ∈ s, wd n j (Φ i) y := by
  have hF : fderiv ℝ (fun w => ∑ i ∈ s, Φ i w) y = ∑ i ∈ s, fderiv ℝ (Φ i) y := by
    have H := HasFDerivAt.sum (u := s) (A := Φ) fun i hi => (hΦ i hi).hasFDerivAt
    try simp only [Finset.sum_fn] at H
    exact H.fderiv
  simp only [wd, hF, ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_div]

private theorem wd_mul_eq_leibniz {p q : V n → ℂ} {y : V n} (hp : DifferentiableAt ℝ p y)
    (hq : DifferentiableAt ℝ q y) (j : Fin n) :
    wd n j (fun w => p w * q w) y = wd n j p y * q y + p y * wd n j q y := by
  have hF : fderiv ℝ (fun w => p w * q w) y = p y • fderiv ℝ q y + q y • fderiv ℝ p y :=
    (hp.hasFDerivAt.mul hq.hasFDerivAt).fderiv
  simp only [wd, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem wd_conj_holomorphic_eq_zero {h : V n → ℂ} {y : V n} (hh : DifferentiableAt ℂ h y) (j : Fin n) :
    wd n j (fun v => (starRingEnd ℂ) (h v)) y = 0 := by
  have H := (hh.hasFDerivAt.restrictScalars ℝ).star
  have H2 : fderiv ℝ (fun v => (starRingEnd ℂ) (h v)) y =
      ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ h y).restrictScalars ℝ) := H.fderiv
  simp only [wd, H2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul, smul_eq_mul, ContinuousLinearEquiv.coe_coe, starL'_apply, star_mul', Complex.star_def,
    Complex.conj_I]
  ring_nf
  try simp only [Complex.I_sq]
  try ring

theorem cmpa_hess_comp {τ : V n → V n} {h : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U)
    (hxU : x ∈ U) (hτ : DifferentiableOn ℂ τ U) (hh : ContDiffAt ℝ 2 h (τ x)) (j k : Fin n) :
    wd n j (wdb n k (h ∘ τ)) x = ∑ m, ∑ l, wd n l (wdb n m h) (τ x) *
      (fderiv ℂ τ x (bas n j)) l * conj ((fderiv ℂ τ x (bas n k)) m) := by
  have hτc : ContDiffOn ℂ ∞ τ U := by
    rw [contDiffOn_piLp]
    intro i
    exact contDiffOn_of_differentiableOn n _ U hU
      ((EuclideanSpace.proj i : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hτ)
  have hG : ContDiffAt ℂ 2 τ x := (contDiffOn_infty.1 hτc 2).contDiffAt (hU.mem_nhds hxU)
  have hGd : ∀ᶠ v in 𝓝 x, DifferentiableAt ℂ τ v :=
    (hG.eventually (by simp)).mono fun v hv => hv.differentiableAt (by simp)
  have hUd : ∀ᶠ v in 𝓝 x, DifferentiableAt ℝ h (τ v) := by
    have h1 : ∀ᶠ w in 𝓝 (τ x), DifferentiableAt ℝ h w :=
      (hh.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
    exact Filter.Tendsto.eventually hG.continuousAt h1
  have ev : wdb n k (h ∘ τ) =ᶠ[𝓝 x]
      fun v => ∑ b, wdb n b h (τ v) * conj (fderiv ℂ τ v (bas n k) b) := by
    filter_upwards [hGd, hUd] with v h1 h2
    exact wdb_comp_holomorphic_eq_sum_conj h2 h1 k
  have hGy : DifferentiableAt ℂ τ x := hG.differentiableAt (by simp)
  have e1 : wd n j (wdb n k (h ∘ τ)) x = wd n j (fun v => ∑ b, wdb n b h (τ v) *
      conj (fderiv ℂ τ v (bas n k) b)) x := by
    simp only [wd, ev.fderiv_eq]
  have hp : ∀ b, DifferentiableAt ℝ (fun v => wdb n b h (τ v)) x := fun b =>
    (differentiableAt_wdb_of_contDiffAt hh b).comp x (hGy.restrictScalars ℝ)
  have hq : ∀ b, DifferentiableAt ℝ (fun v => conj (fderiv ℂ τ v (bas n k) b)) x :=
    fun b => ((differentiableAt_fderiv_basis_coord_of_contDiffAt hG k b).restrictScalars ℝ).star
  rw [e1, wd_finset_sum Finset.univ (fun b v => wdb n b h (τ v) * conj (fderiv ℂ τ v (bas n k) b))
      x (fun b _ => (hp b).mul (hq b)) j]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [wd_mul_eq_leibniz (hp b) (hq b) j, wd_conj_holomorphic_eq_zero (differentiableAt_fderiv_basis_coord_of_contDiffAt hG k b) j, mul_zero, add_zero]
  have e2 := wd_comp_holomorphic_eq_sum (U := wdb n b h) (differentiableAt_wdb_of_contDiffAt hh b) hGy j
  simp only [Function.comp_def] at e2
  rw [e2, Finset.sum_mul]

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA
section
open Complex ComplexConjugate Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ}

theorem I_pow_three_eq_neg_I : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring

theorem flA_expand (w : V n) : w = ∑ j, w j • bas n j := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr w]
  simp [bas]

theorem flA_apply_sum (D : V n →L[ℂ] V n) (ξ : Fin n → ℂ) (a : Fin n) :
    D (WithLp.toLp 2 ξ) a = ∑ j, ξ j * D (bas n j) a := by
  conv_lhs => rw [flA_expand (WithLp.toLp 2 ξ)]
  simp [map_sum, map_smul]

theorem flA_decomp (D : V n →L[ℝ] ℂ) (w : V n) :
    D w = ∑ b, (w b * ((D (bas n b) - I * D (I • bas n b)) / 2) +
      conj (w b) * ((D (bas n b) + I * D (I • bas n b)) / 2)) := by
  conv_lhs => rw [flA_expand w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hcb : w b • bas n b = (w b).re • bas n b + (w b).im • (I • bas n b) := by
    conv_lhs => rw [← Complex.re_add_im (w b)]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [hcb, map_add, map_smul, map_smul]
  conv_rhs => rw [← Complex.re_add_im (w b)]
  simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf; simp only [I_sq]; ring_nf

theorem flA_fderiv_comp {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (v : V n) :
    fderiv ℝ (U ∘ G) y v = fderiv ℝ U (G y) (fderiv ℂ G y v) := by
  rw [(hU.hasFDerivAt.comp y (hG.hasFDerivAt.restrictScalars ℝ)).fderiv]; rfl

theorem flA_wdb_comp {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (k : Fin n) :
    wdb n k (U ∘ G) y = ∑ b, wdb n b U (G y) * conj (fderiv ℂ G y (bas n k) b) := by
  simp only [wdb]
  rw [flA_fderiv_comp hU hG, flA_fderiv_comp hU hG, map_smul,
    flA_decomp (fderiv ℝ U (G y)) (fderiv ℂ G y (bas n k)),
    flA_decomp (fderiv ℝ U (G y)) (I • fderiv ℂ G y (bas n k))]
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring_nf; simp only [I_sq, I_pow_three_eq_neg_I]; ring_nf

theorem flA_wd_comp {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (k : Fin n) :
    wd n k (U ∘ G) y = ∑ b, wd n b U (G y) * fderiv ℂ G y (bas n k) b := by
  simp only [wd]
  rw [flA_fderiv_comp hU hG, flA_fderiv_comp hU hG, map_smul,
    flA_decomp (fderiv ℝ U (G y)) (fderiv ℂ G y (bas n k)),
    flA_decomp (fderiv ℝ U (G y)) (I • fderiv ℂ G y (bas n k))]
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring_nf; simp only [I_sq, I_pow_three_eq_neg_I]; ring_nf

theorem sum_four_comm_bis (T : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ j, ∑ k, T a b j k = ∑ j, ∑ k, ∑ b, ∑ a, T a b j k := by
  calc ∑ a, ∑ b, ∑ j, ∑ k, T a b j k = ∑ a, ∑ j, ∑ k, ∑ b, T a b j k := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_; rw [Finset.sum_comm]
    _ = ∑ j, ∑ k, ∑ b, ∑ a, T a b j k := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => ?_; rw [Finset.sum_comm]

theorem flA_diff_comp_apply {G : V n → V n} {y : V n} (hG : ContDiffAt ℂ 2 G y) (k b : Fin n) :
    DifferentiableAt ℂ (fun v => fderiv ℂ G v (bas n k) b) y := by
  have hD1 : DifferentiableAt ℂ (fderiv ℂ G) y :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact (EuclideanSpace.proj b : V n →L[ℂ] ℂ).differentiableAt.comp y
    (hD1.clm_apply (differentiableAt_const _))

theorem flA_leviV_comp {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : ContDiffAt ℝ 2 U (G y)) (hG : ContDiffAt ℂ 2 G y) (ξ : Fin n → ℂ) :
    leviV n (U ∘ G) y ξ = leviV n U (G y) (fun b => fderiv ℂ G y (WithLp.toLp 2 ξ) b) := by
  have hGy : DifferentiableAt ℂ G y := hG.differentiableAt (by simp)
  have hGd : ∀ᶠ v in 𝓝 y, DifferentiableAt ℂ G v :=
    (hG.eventually (by simp)).mono fun v hv => hv.differentiableAt (by simp)
  have hUd : ∀ᶠ v in 𝓝 y, DifferentiableAt ℝ U (G v) :=
    hG.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hU)
  have hev : ∀ k, wdb n k (U ∘ G) =ᶠ[𝓝 y]
      fun v => ∑ b, wdb n b U (G v) * conj (fderiv ℂ G v (bas n k) b) := by
    intro k; filter_upwards [hGd, hUd] with v h1 h2; exact flA_wdb_comp h2 h1 k
  have hA : ∀ b, DifferentiableAt ℝ (fun v => wdb n b U (G v)) y := fun b =>
    (differentiableAt_wdb hU).comp y (hGy.restrictScalars ℝ)
  have hB := flA_diff_comp_apply hG
  have hwd : ∀ j k, wd n j (wdb n k (U ∘ G)) y = ∑ b, (∑ a, wd n a (wdb n b U) (G y) *
      fderiv ℂ G y (bas n j) a) * conj (fderiv ℂ G y (bas n k) b) := by
    intro j k
    have hc : ∀ b, DifferentiableAt ℝ (fun v => conj (fderiv ℂ G v (bas n k) b)) y := fun b =>
      differentiableAt_conj ((hB k b).restrictScalars ℝ)
    rw [wd_congr (hev k), wd_sum Finset.univ
      (f := fun b v => wdb n b U (G v) * conj (fderiv ℂ G v (bas n k) b))
      (fun b _ => (hA b).mul (hc b))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [wd_mul (hA b) (hc b), wd_conj ((hB k b).restrictScalars ℝ),
      wdb_of_differentiableAt (hB k b)]
    rw [show (fun v => wdb n b U (G v)) = wdb n b U ∘ G from rfl,
      flA_wd_comp (differentiableAt_wdb hU) hGy j]
    simp
  simp only [leviV]
  simp_rw [hwd, flA_apply_sum]
  simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [sum_four_comm_bis, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem flA_leviV_log_normSq {h : V n → ℂ} {y : V n}
    (hh : ∀ᶠ v in 𝓝 y, DifferentiableAt ℂ h v) (hne : h y ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((Real.log (‖h v‖ ^ 2) : ℝ) : ℂ)) y ξ = 0 := by
  set Lf : V n → ℂ := fun v => Complex.log (h v / h y) with hLf
  have hcont : ContinuousAt (fun v => h v / h y) y :=
    (hh.self_of_nhds.continuousAt).div_const _
  have hslit : ∀ᶠ v in 𝓝 y, h v / h y ∈ Complex.slitPlane := by
    apply hcont.eventually_mem
    rw [div_self hne]
    exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
  have hLd : ∀ᶠ v in 𝓝 y, DifferentiableAt ℂ Lf v := by
    filter_upwards [hh, hslit] with v h1 h2
    have h3 : DifferentiableAt ℂ (fun v => h v / h y) v := by
      simpa [div_eq_mul_inv] using h1.mul_const (h y)⁻¹
    exact h3.clog h2
  obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.mp hLd
  have hLc : ContDiffOn ℂ ∞ Lf t := contDiffOn_of_differentiableOn n Lf t hto
    (fun v hv => (ht v hv).differentiableWithinAt)
  have hL2 : ∀ v ∈ t, ContDiffAt ℂ 2 Lf v := fun v hv =>
    ((hLc v hv).contDiffAt (hto.mem_nhds hv)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hne' : ∀ᶠ v in 𝓝 y, h v ≠ 0 := hh.self_of_nhds.continuousAt.eventually_ne hne
  have hF : (fun v => ((Real.log (‖h v‖ ^ 2) : ℝ) : ℂ)) =ᶠ[𝓝 y]
      fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v + conj (Lf v) := by
    filter_upwards [hne'] with v hv
    have h1 : Lf v + conj (Lf v) = ((2 * (Lf v).re : ℝ) : ℂ) := by
      rw [Complex.add_conj]
    rw [add_assoc, h1, Complex.log_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.mpr hv) (norm_ne_zero_iff.mpr hne), Real.log_pow,
      Real.log_pow]
    push_cast; try ring
  rw [leviV_congr hF]
  have hwdb : ∀ k, wdb n k (fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v + conj (Lf v))
      =ᶠ[𝓝 y] fun v => conj (wd n k Lf v) := by
    intro k
    filter_upwards [hto.mem_nhds hyt] with v hv
    have hd : DifferentiableAt ℂ Lf v := ht v hv
    rw [wdb_add (f := fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v) (g := fun v => conj (Lf v))
        ((differentiableAt_const _).add (hd.restrictScalars ℝ))
        (differentiableAt_conj (hd.restrictScalars ℝ)),
      wdb_add (f := fun _ => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ)) (g := Lf)
        (differentiableAt_const _) (hd.restrictScalars ℝ),
      wdb_conj (hd.restrictScalars ℝ), wdb_of_differentiableAt hd,
      wdb_of_differentiableAt (differentiableAt_const _)]
    ring
  have hz : ∀ j k, wd n j (wdb n k (fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v +
      conj (Lf v))) y = 0 := by
    intro j k
    have hwk : wd n k Lf =ᶠ[𝓝 y] fun v => fderiv ℂ Lf v (bas n k) := by
      filter_upwards [hto.mem_nhds hyt] with v hv
      exact wd_of_differentiableAt (ht v hv)
    have hdk : DifferentiableAt ℂ (fun v => fderiv ℂ Lf v (bas n k)) y :=
      (((hL2 y hyt).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
        (differentiableAt_const _)
    rw [wd_congr (hwdb k), wd_conj (differentiableAt_wd (hL2 y hyt |>.restrict_scalars ℝ)),
      wdb_congr hwk, wdb_of_differentiableAt hdk]
    simp
  simp only [leviV, hz, zero_mul, Finset.sum_const_zero]

theorem flA_leviV_add {F G : V n → ℝ} {y : V n} (hF : ContDiffAt ℝ 2 F y)
    (hG : ContDiffAt ℝ 2 G y) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((F v + G v : ℝ) : ℂ)) y ξ =
      leviV n (fun v => (F v : ℂ)) y ξ + leviV n (fun v => (G v : ℂ)) y ξ := by
  have hFc : ContDiffAt ℝ 2 (fun v => (F v : ℂ)) y := ofRealCLM.contDiff.contDiffAt.comp y hF
  have hGc : ContDiffAt ℝ 2 (fun v => (G v : ℂ)) y := ofRealCLM.contDiff.contDiffAt.comp y hG
  have hfun : (fun v => ((F v + G v : ℝ) : ℂ)) = fun v => (F v : ℂ) + (G v : ℂ) := by
    funext v; push_cast; rfl
  have hev : ∀ k, wdb n k (fun v => (F v : ℂ) + (G v : ℂ)) =ᶠ[𝓝 y]
      fun v => wdb n k (fun v => (F v : ℂ)) v + wdb n k (fun v => (G v : ℂ)) v := by
    intro k
    filter_upwards [eventually_differentiableAt_of_contDiffAt hFc,
      eventually_differentiableAt_of_contDiffAt hGc] with v h1 h2
    exact wdb_add h1 h2
  rw [hfun]
  simp only [leviV]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wd_congr (hev k), wd_add (differentiableAt_wdb hFc) (differentiableAt_wdb hGc)]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
end

