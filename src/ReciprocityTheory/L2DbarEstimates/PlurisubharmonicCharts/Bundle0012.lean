import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0011
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0009
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0007
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle0002

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxL
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem aap_continuous_nsq (la : La) (u : ι → Y → ℂ)
    (hcoc : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → u i y = A.g la i j y * u j y)
    (hc : ∀ i, ContinuousOn (u i ∘ (A.chart i).symm) (A.chart i).target) :
    Continuous (A.nsq la u) := by
  have hloc : ∀ i y, y ∈ (A.chart i).source →
      A.nsq la u y = ‖u i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
    intro i y hy
    have hg := A.g_ne la (A.pick y) i y (A.mem_pick y) hy
    have ht := A.ph_trans la (A.pick y) i y (A.mem_pick y) hy
    have hg2 : 0 < ‖A.g la (A.pick y) i y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hg) 2
    have hp : A.ph la (A.pick y) y = A.ph la i y + Real.log (‖A.g la (A.pick y) i y‖ ^ 2) := by
      linarith
    unfold nsq
    rw [hcoc (A.pick y) i y (A.mem_pick y) hy, hp, norm_mul, mul_pow, neg_add, Real.exp_add,
      Real.exp_neg (Real.log _), Real.exp_log hg2]
    field_simp
  rw [continuous_iff_continuousAt]
  intro y0
  have hy0 : y0 ∈ (A.chart (A.pick y0)).source := A.mem_pick y0
  have hs : (A.chart (A.pick y0)).source ∈ 𝓝 y0 := (A.chart (A.pick y0)).open_source.mem_nhds hy0
  have hu : ContinuousOn (u (A.pick y0)) (A.chart (A.pick y0)).source := by
    have h1 := (hc (A.pick y0)).comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    exact h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
  have hph : ContinuousOn (A.ph la (A.pick y0)) (A.chart (A.pick y0)).source := by
    have h1 := (A.smooth_ph la (A.pick y0)).continuousOn.comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    exact h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
  have hf : ContinuousOn (fun y => ‖u (A.pick y0) y‖ ^ 2 * Real.exp (-A.ph la (A.pick y0) y))
      (A.chart (A.pick y0)).source :=
    (hu.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  exact (hf.congr fun y hy => hloc (A.pick y0) y hy).continuousAt hs

theorem continuous_nsq_of_isSec {la : La} {u : ι → Y → ℂ} (hu : A.IsSec la u) :
    Continuous (A.nsq la u) := by
  exact A.aap_continuous_nsq la u (fun i j y hi hj => hu.2 i j y (Set.mem_univ y) hi hj)
    (fun i => (hu.1 i).continuousOn.mono fun v hv => ⟨hv, Set.mem_univ _⟩)

theorem continuous_sqn_of_isSec {N : ℕ} {la : La} {w : Fin N → ι → Y → ℂ} (hw : ∀ k, A.IsSec la (w k)) :
    Continuous (A.sqn la w) := by
  show Continuous fun y => ∑ k, A.nsq la (w k) y
  exact continuous_finset_sum _ fun k _ => A.continuous_nsq_of_isSec (hw k)

theorem int_h_le {Sf : Finset Y} (D : CutData A Sf) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) {ps1 : Y → ℝ}
    (hps1 : A.SmoothFn ps1) (η : ℝ) (hTS : ∀ P ∈ Sf, ∀ y ∈ D.T P, 0 < A.sqn L s y) (Ch : ℝ) :
    ∃ Hb : ℝ≥0∞, Hb < ⊤ ∧ ∀ δ : ℝ, 0 < δ →
      ∫⁻ y, (⋃ P ∈ Sf, D.T P).indicator (fun _ => ENNReal.ofReal Ch) y *
        ENNReal.ofReal (Real.exp (-A.psD L w s ps1 η δ y)) ∂A.mu ≤ Hb := by
  classical
  have hTeq : ∀ P, D.T P = (A.chart (A.pick P)).symm ''
      (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
    fun P => rfl
  have hS : ∀ P, IsCompact
      (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
    fun P => (isCompact_closedBall _ _).diff isOpen_ball
  have hStgt : ∀ P ∈ Sf, ∀ v ∈ closedBall (A.chart (A.pick P) P) (D.r2 P) \
      ball (A.chart (A.pick P) P) (D.r1 P), v ∈ (A.chart (A.pick P)).target :=
    fun P hP v hv => (D.8 P hP hv.1).1
  have hTc : ∀ P ∈ Sf, IsCompact (D.T P) := by
    intro P hP
    rw [hTeq P]
    exact (hS P).image_of_continuousOn
      ((A.chart (A.pick P)).continuousOn_symm.mono fun v hv => hStgt P hP v hv)
  have hμT : ∀ P ∈ Sf, A.mu (D.T P) < ⊤ := by
    intro P hP
    have hTs : D.T P ⊆ (A.chart (A.pick P)).source := by
      rw [hTeq P]
      rintro _ ⟨v, hv, rfl⟩
      exact (A.chart (A.pick P)).map_target (hStgt P hP v hv)
    rw [A.mu_chart (A.pick P) (D.T P) (hTc P hP).isClosed.measurableSet hTs]
    have himg : (A.chart (A.pick P)) '' D.T P =
        closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P) := by
      rw [hTeq P, Set.image_image]
      exact (Set.image_congr fun v hv => (A.chart (A.pick P)).right_inv (hStgt P hP v hv)).trans
        (Set.image_id' _)
    rw [himg]
    have hcont : ContinuousOn
        (fun v => Real.exp (A.ph A.kap (A.pick P) ((A.chart (A.pick P)).symm v)))
        (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
      Real.continuous_exp.comp_continuousOn
        ((A.smooth_ph A.kap (A.pick P)).continuousOn.mono fun v hv => hStgt P hP v hv)
    obtain ⟨C', hC'⟩ := (hS P).exists_bound_of_continuousOn hcont
    calc ∫⁻ v in closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P),
          ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick P) ((A.chart (A.pick P)).symm v)))
        ≤ ∫⁻ v in closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P),
          ENNReal.ofReal C' :=
          setLIntegral_mono' (hS P).isClosed.measurableSet fun v hv =>
            ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC' v hv))
      _ = ENNReal.ofReal C' * volume
          (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
          setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hS P).measure_lt_top
  obtain ⟨K, hK⟩ : ∃ K, K = ⋃ P ∈ Sf, D.T P := ⟨_, rfl⟩
  rw [← hK]
  have hKc : IsCompact K := by
    rw [hK]
    exact Sf.isCompact_biUnion hTc
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hμK : A.mu K < ⊤ := by
    rw [hK]
    exact (measure_biUnion_finset_le Sf _).trans_lt (ENNReal.sum_lt_top.mpr fun P hP => hμT P hP)
  have hsK : ∀ y ∈ K, 0 < A.sqn L s y := by
    intro y hy
    rw [hK, Set.mem_iUnion₂] at hy
    obtain ⟨P, hP, hyP⟩ := hy
    exact hTS P hP y hyP
  have hps1c : Continuous ps1 := by
    rw [continuous_iff_continuousAt]
    intro y0
    have hy0 := A.mem_pick y0
    have h1 := (hps1 (A.pick y0)).continuousOn.comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    have h2 : ContinuousOn ps1 (A.chart (A.pick y0)).source :=
      h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
    exact h2.continuousAt ((A.chart (A.pick y0)).open_source.mem_nhds hy0)
  have hwc : Continuous (A.sqn L w) := A.continuous_sqn_of_isSec hD.sec_w
  have hsc : Continuous (A.sqn L s) := A.continuous_sqn_of_isSec hD.sec_s
  have hwpos : ∀ y, 0 < A.sqn L w y := by
    intro y
    obtain ⟨k, hk⟩ := hD.no_common_zero y
    have hle : A.nsq L (w k) y ≤ A.sqn L w y :=
      Finset.single_le_sum (f := fun k => A.nsq L (w k) y)
        (fun j _ => by simp only [nsq]; positivity) (Finset.mem_univ k)
    have hpos : 0 < A.nsq L (w k) y := by
      simp only [nsq]
      exact mul_pos (pow_pos (norm_pos_iff.mpr hk) 2) (Real.exp_pos _)
    linarith
  have hGc : ContinuousOn (fun y => Real.exp (-ps1 y - η * Real.log (A.sqn L w y) -
      (n : ℝ) * Real.log (A.sqn L s y))) K := by
    apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.sub
    · exact (hps1c.neg.sub (continuous_const.mul (hwc.log fun y => (hwpos y).ne'))).continuousOn
    · exact continuousOn_const.mul (hsc.continuousOn.log fun y hy => (hsK y hy).ne')
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hGc
  have hbound : ∀ y ∈ K, ∀ δ : ℝ, 0 < δ → Real.exp (-A.psD L w s ps1 η δ y) ≤ C := by
    intro y hy δ hδ
    refine le_trans ?_ ((Real.le_norm_self _).trans (hC y hy))
    apply Real.exp_le_exp.mpr
    unfold psD
    have h1 : Real.log (A.sqn L s y) ≤ Real.log (A.sqn L s y + δ) :=
      Real.log_le_log (hsK y hy) (by linarith)
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  refine ⟨ENNReal.ofReal Ch * ENNReal.ofReal C * A.mu K,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hμK,
    fun δ hδ => ?_⟩
  calc ∫⁻ y, K.indicator (fun _ => ENNReal.ofReal Ch) y *
        ENNReal.ofReal (Real.exp (-A.psD L w s ps1 η δ y)) ∂A.mu
      ≤ ∫⁻ y, K.indicator (fun _ => ENNReal.ofReal Ch * ENNReal.ofReal C) y ∂A.mu := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ K
        · simp only [Set.indicator_of_mem hy]
          exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hbound y hy δ hδ))
        · simp [hy]
    _ = ENNReal.ofReal Ch * ENNReal.ofReal C * A.mu K := lintegral_indicator_const hKm _

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
section
open MeasureTheory Filter Topology Complex ComplexConjugate
open scoped ContDiff ENNReal ComplexOrder

namespace ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

universe u

variable {n : ℕ}

private theorem contDiffAt_ofReal_comp' {f : V n → ℝ} {x : V n} {m : WithTop ℕ∞} (hf : ContDiffAt ℝ m f x) :
    ContDiffAt ℝ m (fun v => ((f v : ℝ) : ℂ)) x := by
  first
  | exact Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  | exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x hf).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun v => by simp)
  | fun_prop

private theorem fderiv_wdb_apply_of_hasFDerivAt_flip {g : V n → ℂ} {x : V n} (k : Fin n)
    (hlin : ∀ v : V n, HasFDerivAt (fun y => fderiv ℝ g y v) ((fderiv ℝ (fderiv ℝ g) x).flip v) x)
    (u : V n) : fderiv ℝ (wdb n k g) x u =
      (fderiv ℝ (fderiv ℝ g) x u (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ g) x u (Complex.I • bas n k)) / 2 := by
  have h3 := ((hlin (bas n k)).add ((hlin (Complex.I • bas n k)).const_mul Complex.I)).mul_const
    ((2 : ℂ)⁻¹)
  have hw : wdb n k g = fun y =>
      (fderiv ℝ g y (bas n k) + Complex.I * fderiv ℝ g y (Complex.I • bas n k)) * (2 : ℂ)⁻¹ := by
    funext y
    simp only [wdb]
    ring
  rw [hw]
  first
  | rw [(show HasFDerivAt (𝕜 := ℝ) (fun y => (fderiv ℝ g y (bas n k) +
      Complex.I * fderiv ℝ g y (Complex.I • bas n k)) * (2 : ℂ)⁻¹) _ x from h3).fderiv]
  | erw [h3.fderiv]
  simp [div_eq_mul_inv]
  try ring

theorem cmpb_det_nonneg {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    0 ≤ (cHess n (fun v => ((f v : ℝ) : ℂ)) x).det.re := by
  set g : V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hgeq
  have hg2 : ContDiffAt ℝ 2 g x := contDiffAt_ofReal_comp' hf
  have hD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg2.fderiv_right (m := 1) (by first | exact one_add_one_eq_two.le | norm_num)).differentiableAt (by first | exact one_ne_zero | exact le_rfl)
  have hsym : ∀ u v : V n, fderiv ℝ (fderiv ℝ g) x u v = fderiv ℝ (fderiv ℝ g) x v u := by
    have hs : IsSymmSndFDerivAt ℝ g x := by
      first
      | exact hg2.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
      | exact hg2.isSymmSndFDerivAt (by simp [minSmoothness])
      | exact hg2.isSymmSndFDerivAt le_rfl
    exact fun u v => hs u v
  have hlin : ∀ v : V n, HasFDerivAt (fun y => fderiv ℝ g y v)
      ((fderiv ℝ (fderiv ℝ g) x).flip v) x := by
    intro v
    have h := hD.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
    first
    | simpa using h
    | (convert h using 1; simp)
  have hval : ∀ u v : V n, fderiv ℝ (fun y => fderiv ℝ g y v) x u = fderiv ℝ (fderiv ℝ g) x u v := by
    intro u v
    rw [(hlin v).fderiv, ContinuousLinearMap.flip_apply]
  have hc1 : ∀ y v : V n, (starRingEnd ℂ) (fderiv ℝ g y v) = fderiv ℝ g y v := by
    intro y v
    have e : fderiv ℝ ((Complex.conjCLE : ℂ → ℂ) ∘ g) y =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g y) := Complex.conjCLE.comp_fderiv
    have hg' : (Complex.conjCLE : ℂ → ℂ) ∘ g = g := by
      funext z; simp [hgeq]
    rw [hg'] at e
    have := congrArg (fun L : V n →L[ℝ] ℂ => L v) e
    simpa using this.symm
  have hc2 : ∀ u v : V n, (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ g) x u v) = fderiv ℝ (fderiv ℝ g) x u v := by
    intro u v
    have e : fderiv ℝ ((Complex.conjCLE : ℂ → ℂ) ∘ fun y => fderiv ℝ g y v) x =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (fun y => fderiv ℝ g y v) x) :=
      Complex.conjCLE.comp_fderiv
    have hh : (Complex.conjCLE : ℂ → ℂ) ∘ (fun y => fderiv ℝ g y v) = fun y => fderiv ℝ g y v := by
      funext z; simpa using hc1 z v
    rw [hh] at e
    have := congrArg (fun L : V n →L[ℝ] ℂ => L u) e
    rw [← hval u v]
    simpa using this.symm
  have key : ∀ (k : Fin n) (u : V n), fderiv ℝ (wdb n k g) x u =
      (fderiv ℝ (fderiv ℝ g) x u (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ g) x u (Complex.I • bas n k)) / 2 :=
    fun k u => fderiv_wdb_apply_of_hasFDerivAt_flip k hlin u
  have hH : ∀ j k : Fin n, cHess n g x j k =
      (fderiv ℝ (fderiv ℝ g) x (bas n j) (bas n k) +
        fderiv ℝ (fderiv ℝ g) x (Complex.I • bas n j) (Complex.I • bas n k) +
        Complex.I * (fderiv ℝ (fderiv ℝ g) x (bas n j) (Complex.I • bas n k) -
          fderiv ℝ (fderiv ℝ g) x (Complex.I • bas n j) (bas n k))) / 4 := by
    intro j k
    simp only [cHess, Matrix.of_apply, wd, key]
    linear_combination (-(fderiv ℝ (fderiv ℝ g) x (Complex.I • bas n j) (Complex.I • bas n k)) / 4) *
      Complex.I_sq
  have hHerm : (cHess n g x).IsHermitian := by
    refine Matrix.IsHermitian.ext fun j k => ?_
    show (starRingEnd ℂ) (cHess n g x k j) = cHess n g x j k
    rw [hH k j, hH j k]
    simp only [map_div₀, map_add, map_sub, map_mul, Complex.conj_I, hc2, map_ofNat]
    linear_combination (1 / 4 : ℂ) * hsym (bas n k) (bas n j) +
      (1 / 4 : ℂ) * hsym (Complex.I • bas n k) (Complex.I • bas n j) -
      (Complex.I / 4) * hsym (bas n k) (Complex.I • bas n j) +
      (Complex.I / 4) * hsym (Complex.I • bas n k) (bas n j)
  have hq : ∀ v : Fin n → ℂ,
      dotProduct (star v) (Matrix.mulVec (cHess n g x) v) = leviV n g x (star v) := by
    intro v
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, starRingEnd_apply, star_star]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hnn : ∀ v : Fin n → ℂ, 0 ≤ dotProduct (star v) (Matrix.mulVec (cHess n g x) v) := by
    intro v
    have him : (dotProduct (star v) (Matrix.mulVec (cHess n g x) v)).im = 0 := by
      first
      | simpa using hHerm.im_star_dotProduct_mulVec_self v
      | exact hHerm.im_star_dotProduct_mulVec_self v
    have hre : 0 ≤ (dotProduct (star v) (Matrix.mulVec (cHess n g x) v)).re := by
      rw [hq v]; exact hL (star v)
    exact Complex.le_def.2 ⟨by simpa using hre, by simpa using him.symm⟩
  have hPSD : (cHess n g x).PosSemidef := by
    first
    | exact ⟨hHerm, hnn⟩
    | exact ⟨hHerm, fun v => hnn v⟩
    | refine ⟨hHerm, fun v => ?_⟩
      have h := hnn ⇑v
      convert h using 1
      simp [Finsupp.sum_fintype, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hdet := hPSD.det_nonneg
  simpa using (Complex.le_def.1 hdet).1

theorem cmpb_leviV_const (c : ℝ) (x : V n) (ξ : Fin n → ℂ) :
    leviV n (fun _ => ((c : ℝ) : ℂ)) x ξ = 0 := by
  have h : ∀ k, wdb n k (fun _ : V n => ((c : ℝ) : ℂ)) = fun _ => 0 := by
    intro k; funext y; simp [wdb]
  simp [leviV, h, wd]

theorem cmpb_cHess_congr {g₁ g₂ : V n → ℂ} {x : V n} (h : g₁ =ᶠ[𝓝 x] g₂) :
    cHess n g₁ x = cHess n g₂ x := by
  have hw : ∀ k, wdb n k g₁ =ᶠ[𝓝 x] wdb n k g₂ := by
    intro k
    have hn : ∀ᶠ y in 𝓝 x, g₁ =ᶠ[𝓝 y] g₂ := by
      first
      | exact h.eventuallyEq_nhds
      | exact h.eventually_nhds
    filter_upwards [hn] with y hy
    simp only [wdb, hy.fderiv_eq]
  ext j k
  simp only [cHess, Matrix.of_apply, wd, (hw k).fderiv_eq]

theorem cmpb_cHess_add_const (g : V n → ℂ) (c : ℂ) (x : V n) :
    cHess n (fun v => g v + c) x = cHess n g x := by
  have h : ∀ k, wdb n k (fun v => g v + c) = wdb n k g := by
    intro k; funext y; simp only [wdb, fderiv_add_const]
  ext j k
  simp only [cHess, Matrix.of_apply, h]

section Atlas

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

namespace WeightedAtlas

end WeightedAtlas

end Atlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

