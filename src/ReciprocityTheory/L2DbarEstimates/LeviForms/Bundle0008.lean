import ReciprocityTheory.L2DbarEstimates.LeviForms.TwBound
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0004
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0006
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle0002

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.ImportsAlt
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

theorem tw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (hH : HStatement n M) (hC : HoloClosedNeed n M) :
    TWStatement n M := by
  intro X ps Ph F0 a b hps hPh hCb hlevi hF0 hF0w ha hb ha0 hb0 _ hA hB
  refine ⟨bergmanExists n M hC X ps F0 hps
    (Smooth.continuous n X.z X.isLocalHomeomorph F0 hF0).measurable hF0w, ?_⟩
  exact twBound n M hH X ps Ph F0 a b hps hPh hCb hlevi hF0 hF0w ha hb ha0 hb0 hA hB

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.LogLevi
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem logLevi (n : ℕ) (M : Type u) [TopologicalSpace M]
    (hEv : EvLeviStatement n M) (hCh : ChainStatement n M) : LogLeviStatement n M := by
  intro z g ph r ε hz hg hph hpsh hr hε x ξ
  set c : ℝ := ε ^ 2 with hc_def
  have hc : 0 < c := by positivity
  have hvs : SmoothR n z (ev n g ph r) := llSmoothR_ev n z g ph r hg hph
  have hk : ContDiff ℝ ∞ (llLog c) := llLog_contDiff hc
  have hlw : lw n g ph r ε = fun y => llLog c (ev n g ph r y) := by
    funext y
    have hy : -c / 2 ≤ ev n g ph r y := by linarith [llEv_nonneg n g ph r y]
    simp only [lw, llLog]
    rw [llShift_eq hc hy]
  set e := ev n g ph r x with he_def
  have he0 : 0 ≤ e := llEv_nonneg n g ph r x
  have ht : -c / 2 < e := by linarith
  have hQ : 0 < e + c := by linarith

  have hL : (Levi n z (lw n g ph r ε) x ξ).re =
      (e + c)⁻¹ * (Levi n z (ev n g ph r) x ξ).re -
        ((e + c) ^ 2)⁻¹ * ‖dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ ^ 2 := by
    rw [hlw, hCh z hz (llLog c) (ev n g ph r) (by simpa using contDiff_infty.mp hk 2) hvs x ξ,
      llLog_deriv hc ht, llLog_deriv2 hc ht]
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    ring

  have hD : dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ =
      (((e + c)⁻¹ : ℝ) : ℂ) * dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ := by
    rw [hlw]
    unfold dDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [d_comp_real n z (llLog c) hk (ev n g ph r) (SmoothR.ckR n z 1 _ hvs) j x,
      llLog_deriv hc ht]
    ring
  have hN : ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 =
      ((e + c) ^ 2)⁻¹ * ‖dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ ^ 2 := by
    rw [hD, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hQ)]
    rw [mul_pow, inv_pow]
  obtain ⟨h1, h2⟩ := hEv z g ph r hz hg hph hr x ξ
  have hLp : 0 ≤ (Levi n z ph x ξ).re := hpsh x ξ
  rw [hN, hL]
  rw [← he_def] at h1 h2
  generalize (Levi n z (ev n g ph r) x ξ).re = A at h1 h2 ⊢
  generalize ‖dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ ^ 2 = N at h1 h2 ⊢
  generalize (Levi n z ph x ξ).re = P at h1 h2 hLp ⊢
  have hQne : e + c ≠ 0 := hQ.ne'
  constructor
  · have key : N ≤ e * A + e * (e + c) * P := by
      nlinarith [mul_nonneg (mul_nonneg he0 hc.le) hLp]
    rw [← sub_nonneg]
    have hid : e * ((e + c)⁻¹ * A - ((e + c) ^ 2)⁻¹ * N + P) - c * (((e + c) ^ 2)⁻¹ * N) =
        (e * A + e * (e + c) * P - N) * (e + c)⁻¹ := by
      field_simp
      ring
    rw [hid]
    exact mul_nonneg (by linarith) (inv_nonneg.mpr hQ.le)
  · have key : 0 ≤ (e + c) * A + (e + c) ^ 2 * P - N := by
      nlinarith [mul_nonneg hc.le h2, mul_nonneg (mul_nonneg hQ.le hc.le) hLp]
    have hid : (e + c)⁻¹ * A - ((e + c) ^ 2)⁻¹ * N + P =
        ((e + c) * A + (e + c) ^ 2 * P - N) * ((e + c) ^ 2)⁻¹ := by
      field_simp
      ring
    rw [hid]
    exact mul_nonneg key (inv_nonneg.mpr (sq_nonneg _))

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.MacofFderivApplyContDiffOn
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

noncomputable section

theorem macof_fderiv_apply_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (u : V n) : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y u) U := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2.clm_apply contDiffOn_const

theorem macof_wd_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) : ContDiffOn ℝ ∞ (wd n j g) U := by
  unfold wd
  exact ((macof_fderiv_apply_contDiffOn hU hg _).sub
    (contDiffOn_const.mul (macof_fderiv_apply_contDiffOn hU hg _))).div_const 2

theorem macof_wdb_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) : ContDiffOn ℝ ∞ (wdb n j g) U := by
  unfold wdb
  exact ((macof_fderiv_apply_contDiffOn hU hg _).add
    (contDiffOn_const.mul (macof_fderiv_apply_contDiffOn hU hg _))).div_const 2

def macofDet (n : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℂ) ℂ where
  toMultilinearMap :=
    ((Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap).restrictScalars ℝ
  cont := by
    show Continuous fun v : Fin n → Fin n → ℂ => Matrix.det (Matrix.of v)
    exact continuous_id.matrix_det

def macofRow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap.toLinearMap M i

theorem macofRow_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (u : Fin n → ℂ) :
    macofRow M i u = (M.updateRow i u).det := rfl

theorem macof_hasFDerivAt_det {n : ℕ} (B : V n → Matrix (Fin n) (Fin n) ℂ) (y : V n)
    (B' : Fin n → Fin n → (V n →L[ℝ] ℂ))
    (hB : ∀ i l, HasFDerivAt (fun w => B w i l) (B' i l) y) (v : V n) :
    fderiv ℝ (fun w => (B w).det) y v =
      ∑ i, ((B y).updateRow i (fun l => B' i l v)).det := by
  have hrows : HasFDerivAt (fun w => (fun i l => B w i l : Fin n → Fin n → ℂ))
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun l => B' i l) y :=
    hasFDerivAt_pi.2 fun i => hasFDerivAt_pi.2 fun l => hB i l
  have hcomp := ((macofDet n).hasFDerivAt (fun i l => B y i l)).comp y hrows
  have hc2 : HasFDerivAt (fun w => (B w).det)
      (((macofDet n).linearDeriv fun i l => B y i l).comp
        (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun l => B' i l)) y := hcomp
  rw [hc2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
    ContinuousLinearMap.pi_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

theorem macof_swap {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {i j : Fin n} (h : i ≠ j)
    (e c : Fin n → ℂ) :
    ((M.updateRow i e).updateRow j c).det = -((M.updateRow j e).updateRow i c).det := by
  have hB : (M.updateRow j e).updateRow i c =
      ((M.updateRow i e).updateRow j c).submatrix (Equiv.swap i j) id := by
    ext a b
    simp only [Matrix.submatrix_apply, id]
    rcases eq_or_ne a i with rfl | ha
    · simp [Matrix.updateRow_apply, h]
    rcases eq_or_ne a j with rfl | hb
    · simp [Matrix.updateRow_apply, h, ha, Ne.symm h]
    · simp [Matrix.updateRow_apply, ha, hb, Equiv.swap_apply_of_ne_of_ne ha hb]
  rw [hB, Matrix.det_permute, Equiv.Perm.sign_swap h]
  simp

private theorem wd_wd_comm_of_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {G : V n → ℂ}
    (hG : ContDiffOn ℝ ∞ G U) (i j : Fin n) {y : V n} (hy : y ∈ U) :
    wd n j (wd n i G) y = wd n i (wd n j G) y := by
  have hGa : ContDiffAt ℝ ∞ G y := hG.contDiffAt (hU.mem_nhds hy)
  have hsym := hGa.isSymmSndFDerivAt (by first | (simp; norm_cast) | simp | norm_cast)
  have hD2 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) y) y :=
    ((hGa.fderiv_right (m := 1) (by first | norm_cast | simp)).differentiableAt
      (by first | simp | decide)).hasFDerivAt
  have key : ∀ (a : Fin n) (v : V n), fderiv ℝ (wd n a G) y v =
      (fderiv ℝ (fderiv ℝ G) y v (bas n a) -
        Complex.I * fderiv ℝ (fderiv ℝ G) y v (Complex.I • bas n a)) / 2 := by
    intro a v
    have h1 : HasFDerivAt (fun w => fderiv ℝ G w (bas n a))
        ((fderiv ℝ (fderiv ℝ G) y).flip (bas n a)) y := by
      have h0 := hD2.clm_apply (hasFDerivAt_const (bas n a) y)
      simpa using h0
    have h2 : HasFDerivAt (fun w => fderiv ℝ G w (Complex.I • bas n a))
        ((fderiv ℝ (fderiv ℝ G) y).flip (Complex.I • bas n a)) y := by
      have h0 := hD2.clm_apply (hasFDerivAt_const (Complex.I • bas n a) y)
      simpa using h0
    have h3 := (h1.sub (h2.const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    have hwd : wd n a G = fun w =>
        (fderiv ℝ G w (bas n a) - Complex.I * fderiv ℝ G w (Complex.I • bas n a)) / 2 := by
      funext w
      rfl
    have h4 : HasFDerivAt (fun w =>
        (fderiv ℝ G w (bas n a) - Complex.I * fderiv ℝ G w (Complex.I • bas n a)) / 2)
        ((2 : ℂ)⁻¹ • ((fderiv ℝ (fderiv ℝ G) y).flip (bas n a) -
          Complex.I • (fderiv ℝ (fderiv ℝ G) y).flip (Complex.I • bas n a))) y := by
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.sub_apply]
      ring
    rw [hwd, h4.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  show (fderiv ℝ (wd n i G) y (bas n j) - Complex.I * fderiv ℝ (wd n i G) y (Complex.I • bas n j)) / 2 =
    (fderiv ℝ (wd n j G) y (bas n i) - Complex.I * fderiv ℝ (wd n j G) y (Complex.I • bas n i)) / 2
  rw [key i, key i, key j, key j, hsym (bas n j) (bas n i), hsym (bas n j) (Complex.I • bas n i),
    hsym (Complex.I • bas n j) (bas n i), hsym (Complex.I • bas n j) (Complex.I • bas n i)]
  ring

theorem macof_main (n : ℕ) : MACofStatement n := by
  intro U f hU hf y hy k
  have hg : ContDiffOn ℝ ∞ (fun w' => (f w' : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hf
  have hent : ∀ i l, ContDiffOn ℝ ∞ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) U :=
    fun i l => macof_wd_contDiffOn hU (macof_wdb_contDiffOn hU hg l) i
  have hd : ∀ i l, DifferentiableAt ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y :=
    fun i l => ((hent i l).contDiffAt (hU.mem_nhds hy)).differentiableAt (by first | simp | decide)
  have hwd : ∀ (j : Fin n) (F : V n → ℂ), wd n j F y =
      (fderiv ℝ F y (bas n j) - Complex.I * fderiv ℝ F y (Complex.I • bas n j)) / 2 :=
    fun j F => rfl
  have hdz : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n), (M.updateRow i 0).det = 0 :=
    fun M i => by rw [← macofRow_apply, map_zero]
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin n → Fin n → ℂ, ∀ i j, Z i j = if i = j then 0 else
      (((cHess n (fun w' => (f w' : ℂ)) y).updateRow j (Pi.single k 1)).updateRow i
        (fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y)).det :=
    ⟨_, fun _ _ => rfl⟩
  have hterm : ∀ j, wd n j (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) y =
      ∑ i, Z i j := by
    intro j
    have hfun : (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) =
        fun w => ((cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)).det := by
      funext w
      rw [Matrix.adjugate_apply]
    have hB : ∀ i l, HasFDerivAt
        (fun w => ((cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)) i l)
        (if i = j then 0 else fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y) y := by
      intro i l
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.updateRow_self, if_true]
        exact hasFDerivAt_const _ _
      · simp only [Matrix.updateRow_ne hij, if_neg hij]
        exact (hd i l).hasFDerivAt
    have hdet := macof_hasFDerivAt_det
      (fun w => (cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)) y _ hB
    try beta_reduce at hdet
    rw [hfun, hwd, hdet, hdet, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hZ]
    by_cases hij : i = j
    · simp only [if_pos hij, ContinuousLinearMap.zero_apply]
      simp only [← Pi.zero_def, hdz]
      first | ring | simp
    · simp only [if_neg hij]
      rw [← macofRow_apply, ← macofRow_apply, ← macofRow_apply]
      have hρ : (fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y) =
          (2 : ℂ)⁻¹ • ((fun l => fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y (bas n j)) -
            Complex.I • (fun l => fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y
              (Complex.I • bas n j))) := by
        funext l
        simp only [hwd, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [hρ, map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul]
      ring
  have hanti : ∀ i j, Z i j = -Z j i := by
    intro i j
    rw [hZ, hZ]
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
      have hc : (fun l => wd n i (fun w => cHess n (fun w' => (f w' : ℂ)) w j l) y) =
          fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y := by
        funext l
        exact wd_wd_comm_of_contDiffOn hU (macof_wdb_contDiffOn hU hg l) j i hy
      rw [hc, macof_swap _ hij, neg_neg]
  simp only [hterm]
  have hS : ∑ j, ∑ i, Z i j = -∑ j, ∑ i, Z i j := by
    calc ∑ j, ∑ i, Z i j = ∑ j, ∑ i, -Z j i :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hanti i j
      _ = -∑ j, ∑ i, Z j i := by simp only [Finset.sum_neg_distrib]
      _ = -∑ j, ∑ i, Z i j := by rw [Finset.sum_comm]
  linear_combination hS / 2

end

theorem maCof (n : ℕ) : MACofStatement n := macof_main n

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.TwistLeviA
section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

noncomputable section

def tlFlr (a b s : ℝ) : ℝ := s + Real.smoothTransition ((a - s) / (a - b)) * (a - s)

theorem tlFlr_contDiff (a b : ℝ) : ContDiff ℝ ∞ (tlFlr a b) := by
  unfold tlFlr
  fun_prop

theorem tlFlr_eq (a b s : ℝ) (hab : b < a) (h : a ≤ s) : tlFlr a b s = s := by
  unfold tlFlr
  have h1 : (a - s) / (a - b) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [Real.smoothTransition.zero_of_nonpos h1]; ring

theorem tlFlr_ge (a b s : ℝ) (hab : b < a) : b ≤ tlFlr a b s := by
  unfold tlFlr
  have hT0 := Real.smoothTransition.nonneg ((a - s) / (a - b))
  rcases le_total a s with h | h
  · nlinarith [Real.smoothTransition.le_one ((a - s) / (a - b))]
  · rcases le_total s b with h' | h'
    · have : 1 ≤ (a - s) / (a - b) := by rw [le_div_iff₀ (by linarith)]; linarith
      rw [Real.smoothTransition.one_of_one_le this]; linarith
    · nlinarith

theorem tl_eta_pos (s : ℝ) (hs : 9 / 10 ≤ s) : 0 < s + Real.log s := by
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < s by linarith)
  have : 0 < s + 1 - s⁻¹ := by
    have hs0 : 0 < s := by linarith
    have : s⁻¹ ≤ 10 / 9 := by rw [inv_le_comm₀ hs0 (by norm_num)]; linarith
    linarith
  linarith

def tlK (c t : ℝ) : ℝ :=
  -Real.log (tlFlr (19 / 20) (9 / 10) (c - t) + Real.log (tlFlr (19 / 20) (9 / 10) (c - t)))

theorem tlK_contDiff (c : ℝ) : ContDiff ℝ ∞ (tlK c) := by
  have hf : ContDiff ℝ ∞ (fun t => tlFlr (19 / 20) (9 / 10) (c - t)) :=
    (tlFlr_contDiff _ _).comp (contDiff_const.sub contDiff_id)
  have hge : ∀ t, 9 / 10 ≤ tlFlr (19 / 20) (9 / 10) (c - t) := fun t => tlFlr_ge _ _ _ (by norm_num)
  have hl : ContDiff ℝ ∞ (fun t => Real.log (tlFlr (19 / 20) (9 / 10) (c - t))) :=
    hf.log fun t => by linarith [hge t]
  have hs : ContDiff ℝ ∞ (fun t => tlFlr (19 / 20) (9 / 10) (c - t) + Real.log (tlFlr (19 / 20) (9 / 10) (c - t))) :=
    hf.add hl
  exact (hs.log fun t => (tl_eta_pos _ (hge t)).ne').neg

open Filter Topology

def tlKp (c t : ℝ) : ℝ := (1 + 1 / (c - t)) / ((c - t) + Real.log (c - t))

def tlKpp (c t : ℝ) : ℝ :=
  1 / ((c - t) ^ 2 * ((c - t) + Real.log (c - t))) + ((1 + 1 / (c - t)) / ((c - t) + Real.log (c - t))) ^ 2

theorem tlK_eventually (c t : ℝ) (ht : t < c - 19 / 20) :
    tlK c =ᶠ[𝓝 t] fun t => -Real.log ((c - t) + Real.log (c - t)) := by
  filter_upwards [Iio_mem_nhds ht] with y hy
  have : tlFlr (19 / 20) (9 / 10) (c - y) = c - y := tlFlr_eq _ _ _ (by norm_num) (by simp at hy; linarith)
  simp only [tlK, this]

theorem tl_hasDerivAt_k (c t : ℝ) (hs : 9 / 10 ≤ c - t) :
    HasDerivAt (fun t => -Real.log ((c - t) + Real.log (c - t))) (tlKp c t) t := by
  have hs0 : c - t ≠ 0 := by intro h; linarith
  have he := tl_eta_pos _ hs
  have hu : HasDerivAt (fun y => c - y) (-1) t := by simpa using (hasDerivAt_id t).const_sub c
  have hl := hu.log hs0
  have h2 := (hu.add hl).log he.ne'
  refine h2.neg.congr_deriv ?_
  unfold tlKp
  simp only [Pi.add_apply, Pi.div_apply]
  field_simp
  ring

theorem tl_hasDerivAt_kp (c t : ℝ) (hs : 9 / 10 ≤ c - t) : HasDerivAt (tlKp c) (tlKpp c t) t := by
  have hs0 : c - t ≠ 0 := by intro h; linarith
  have he := tl_eta_pos _ hs
  have hu : HasDerivAt (fun y => c - y) (-1) t := by simpa using (hasDerivAt_id t).const_sub c
  have hi := (hasDerivAt_const t (1 : ℝ)).div hu hs0
  have hk := (hasDerivAt_const t (1 : ℝ)).add hi
  have hl := hu.log hs0
  have h2 := hk.div (hu.add hl) he.ne'
  refine h2.congr_deriv ?_
  unfold tlKpp
  simp only [Pi.add_apply, Pi.div_apply]
  field_simp
  ring

theorem tl_deriv_k (c t : ℝ) (ht : t ≤ c - 1) :
    deriv (tlK c) t = tlKp c t ∧ deriv (deriv (tlK c)) t = tlKpp c t := by
  have ht' : t < c - 19 / 20 := by linarith
  have hE : deriv (tlK c) =ᶠ[𝓝 t] tlKp c := by
    filter_upwards [Iio_mem_nhds ht'] with y hy
    simp only [Set.mem_Iio] at hy
    exact ((tl_hasDerivAt_k c y (by linarith)).congr_of_eventuallyEq (tlK_eventually c y hy)).deriv
  refine ⟨hE.eq_of_nhds, ?_⟩
  exact ((tl_hasDerivAt_kp c t (by linarith)).congr_of_eventuallyEq hE).deriv

theorem tl_ev_nonneg {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (x : M) :
    0 ≤ ev n g ph r x := by
  unfold ev; positivity

theorem tl_ev_le_one {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (hr : 0 < r)
    (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) (x : M) :
    ev n g ph r x ≤ 1 := by
  unfold ev
  rw [div_le_one (by positivity)]
  exact hbd x

theorem tl_lw_le {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (hr : 0 < r)
    (hε : 0 < ε) (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) (x : M) :
    lw n g ph r ε x ≤ Real.log (1 + ε ^ 2) := by
  unfold lw
  have h0 := tl_ev_nonneg n g ph r x
  have h1 := tl_ev_le_one n g ph r hr hbd x
  exact Real.log_le_log (by positivity) (by linarith)

theorem tl_ev_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) :
    SmoothR n z (ev n g ph r) := by
  have hS : SmoothR n z (fun x => ∑ i, ‖g i x‖ ^ 2) :=
    smoothR_sum n z Finset.univ _ fun i _ => Smooth.normSq n z _ (Holo.smooth n z _ (hg i))
  have hE : SmoothR n z (fun x => Real.exp (-ph x)) :=
    SmoothR.comp n z (fun t => Real.exp (-t)) (Real.contDiff_exp.comp contDiff_neg) ph hph
  exact SmoothR.comp n z (fun t => t / r ^ 2) (contDiff_id.div_const _) _ (SmoothR.mul n z _ _ hS hE)

theorem tl_lw_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r δ : ℝ) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) (hδ : 0 < δ) :
    SmoothR n z (lw n g ph r δ) := by
  have hd : 0 < δ ^ 2 := by positivity
  have hL : ContDiff ℝ ∞ (fun t => Real.log (tlFlr (δ ^ 2) (δ ^ 2 / 2) t)) :=
    (tlFlr_contDiff _ _).log fun t => by
      have := tlFlr_ge (δ ^ 2) (δ ^ 2 / 2) t (by linarith)
      exact (show 0 < tlFlr (δ ^ 2) (δ ^ 2 / 2) t by linarith).ne'
  have h := SmoothR.comp n z _ hL (fun x => ev n g ph r x + δ ^ 2)
    (SmoothR.add n z _ _ (tl_ev_smoothR n z g ph r hg hph) (smoothR_const n z _))
  have heq : (fun x => Real.log (tlFlr (δ ^ 2) (δ ^ 2 / 2) (ev n g ph r x + δ ^ 2))) = lw n g ph r δ := by
    funext x
    unfold lw
    rw [tlFlr_eq _ _ _ (by linarith) (by linarith [tl_ev_nonneg n g ph r x])]
  rw [heq] at h
  exact h

theorem tl_twist_eq {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (hr : 0 < r)
    (hε : 0 < ε) (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) :
    twist n g ph r ε = fun x => tlK (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε x) := by
  funext x
  have h := tl_lw_le n g ph r ε hr hε hbd x
  unfold twist eta xx tlK
  rw [tlFlr_eq _ _ _ (by norm_num) (by linarith)]

theorem tl_levi_formula {M : Type*} [TopologicalSpace M] (n : ℕ) (hCh : ChainStatement n M)
    (z : M → V n) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (ε δ : ℝ)
    (hz : IsLocalHomeomorph z) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph)
    (hph2 : SmoothR n z ph2) (hr : 0 < r) (hε : 0 < ε) (hδ : 0 < δ)
    (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) (x : M) (ξ : Fin n → ℂ) :
    (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re =
      (Levi n z ph2 x ξ).re + ((n : ℝ) + j) * (Levi n z ph x ξ).re +
        (n : ℝ) * (Levi n z (lw n g ph r δ) x ξ).re +
        tlKp (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε x) * (Levi n z (lw n g ph r ε) x ξ).re +
        tlKpp (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε x) *
          ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 := by
  set c := 1 + Real.log (1 + ε ^ 2) with hc
  have hlε := tl_lw_smoothR n z g ph r ε hg hph hε
  have hlδ := tl_lw_smoothR n z g ph r δ hg hph hδ
  have hA : SmoothR n z (fun y => ph2 y + ((n : ℝ) + j) * ph y) :=
    SmoothR.add n z _ _ hph2 (SmoothR.mul n z _ _ (smoothR_const n z _) hph)
  have hBB : SmoothR n z (fun y => (n : ℝ) * lw n g ph r δ y) :=
    SmoothR.mul n z _ _ (smoothR_const n z _) hlδ
  have hwgt : SmoothR n z (wgt n g ph ph2 r j δ) := SmoothR.add n z _ _ hA hBB
  have htw_eq := tl_twist_eq n g ph r ε hr hε hbd
  have htw : SmoothR n z (twist n g ph r ε) := by
    rw [htw_eq]; exact SmoothR.comp n z _ (tlK_contDiff c) _ hlε
  have e1 : Levi n z (wgt n g ph ph2 r j δ) x ξ =
      Levi n z ph2 x ξ + (((n : ℝ) + j : ℝ) : ℂ) * Levi n z ph x ξ +
        ((n : ℝ) : ℂ) * Levi n z (lw n g ph r δ) x ξ := by
    have h1 := levi_add n z _ _ (SmoothR.ckR n z 2 _ hA) (SmoothR.ckR n z 2 _ hBB) x ξ
    have h2 := levi_add n z _ _ (SmoothR.ckR n z 2 _ hph2)
      (SmoothR.ckR n z 2 _ (SmoothR.mul n z _ _ (smoothR_const n z ((n : ℝ) + j)) hph)) x ξ
    have h3 := levi_const_mul n z ((n : ℝ) + j) ph (SmoothR.ckR n z 2 _ hph) x ξ
    have h4 := levi_const_mul n z (n : ℝ) _ (SmoothR.ckR n z 2 _ hlδ) x ξ
    change Levi n z (fun y => ph2 y + ((n : ℝ) + j) * ph y + (n : ℝ) * lw n g ph r δ y) x ξ = _
    rw [h1, h2, h3, h4]
  have hk : ContDiff ℝ 2 (tlK c) := contDiff_infty.1 (tlK_contDiff c) 2
  have e2 : Levi n z (twist n g ph r ε) x ξ =
      ((tlKp c (lw n g ph r ε x) : ℝ) : ℂ) * Levi n z (lw n g ph r ε) x ξ +
        ((tlKpp c (lw n g ph r ε x) : ℝ) : ℂ) *
          ((‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [htw_eq, hCh z hz (tlK c) (lw n g ph r ε) hk hlε x ξ]
    obtain ⟨d1, d2⟩ := tl_deriv_k c (lw n g ph r ε x) (by linarith [tl_lw_le n g ph r ε hr hε hbd x])
    rw [d1, d2]
  rw [levi_add n z _ _ (SmoothR.ckR n z 2 _ hwgt) (SmoothR.ckR n z 2 _ htw) x ξ, e1, e2]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  ring

end

end ReciprocityTheory.L2DbarEstimates.I
end

