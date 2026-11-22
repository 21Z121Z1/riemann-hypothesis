import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0100
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0102
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0108
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StokesOffDiscriminantWindow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceFormLelongCompactLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff Manifold

noncomputable section

namespace SliceFormLelongCompact

variable {n d : ℕ}

theorem ne_zero_of_mem_zeroSet {I : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hℓ : linForm ℓ - 1 ∈ I) {x : Fin n → ℂ} (hx : x ∈ zeroSet I) : x ≠ 0 := by
  rintro rfl
  have := hx _ hℓ
  simp [linForm] at this

theorem zeroSet_anti {I I' : Ideal (MvPolynomial (Fin n) ℂ)} (hle : I ≤ I') : zeroSet I' ⊆ zeroSet I :=
  fun _ hx p hp => hx p (hle hp)

theorem varInt_congr_weight {J : Ideal (MvPolynomial (Fin n) ℂ)} {f g : (Fin n → ℂ) → ℝ}
    (hfg : ∀ x ∈ zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) : varInt J d f φ = varInt J d g φ := by
  unfold varInt chartInt
  split_ifs with hA
  · rw [CutOffDominated.chartDens_congr_zeroSet hfg]
  · rfl

theorem exists_contDiff_eqOn {Z : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℝ} (hZ : IsClosed Z)
    (hf : SmoothNear Z f) (hfc : HasCompactSupport f) :
    ∃ g : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ Z, g x = f x := by
  obtain ⟨U, hU, hZU, hfU⟩ := hf
  have hK : IsCompact (Z ∩ tsupport f) := hfc.isCompact.inter_left hZ
  obtain ⟨V, hVo, hKV, hVU, -⟩ := exists_open_between_and_isCompact_closure hK hU
    (Set.inter_subset_left.trans hZU)
  obtain ⟨θ, hθ, -, h0, h1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed
    (I := 𝓘(ℝ, Fin n → ℂ)) (n := ⊤) hVo.isClosed_compl hK.isClosed
    (Set.disjoint_compl_left_iff_subset.2 hKV)
  have hθc : ContDiff ℝ ∞ θ := contMDiff_iff_contDiff.1 hθ
  have hsupp : tsupport θ ⊆ U := by
    refine (closure_mono fun y hy => ?_).trans hVU
    by_contra hyV
    exact hy ((h0 y).1 hyV)
  refine ⟨fun x => θ x * f x, contDiff_iff_contDiffAt.2 fun x => ?_, hfc.mul_left, fun x hx => ?_⟩
  · by_cases hxU : x ∈ U
    · exact hθc.contDiffAt.mul (hfU.contDiffAt (hU.mem_nhds hxU))
    · have hθ0 : θ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hxU (hsupp h)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hθ0] with y hy
      simp [hy]
  · show θ x * f x = f x
    by_cases hxf : x ∈ tsupport f
    · rw [(h1 x).1 ⟨hx, hxf⟩, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero]

theorem chartAbsDens_indicator_eq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (w : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {B : Set (Fin n → ℂ)} (i : Fin d)
    (hB : tsupport (ψ i) ⊆ B) : chartAbsDens J A (B.indicator w) ψ = chartAbsDens J A w ψ := by
  funext y
  unfold chartAbsDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  split_ifs with hs
  · by_cases hxB : x ∈ B
    · dsimp only
      rw [Set.indicator_of_mem hxB]
    · have hM := ChartMassCompact.maDens_eq_zero hs.choose_spec ψ i fun h => hxB (hB h)
      rw [hx.2] at hM
      simp [hM]
  · rfl

theorem integrable_chartDens {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {w : (Fin n → ℂ) → ℝ} {ψ : Fin d → (Fin n → ℂ) → ℝ}
    (hm : Measurable (chartDens J A w ψ)) (hi : Integrable (chartAbsDens J A w ψ)) :
    Integrable (chartDens J A w ψ) := by
  refine hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  rw [Real.norm_eq_abs]
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs <;> simp

theorem measurable_fsLogReg (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) : Measurable (fsLogReg h u ε) := by
  have hN : Measurable h.dualNorm := (SliceCut.continuous_dualNorm h).measurable
  have hL : Measurable fun y : Fin n → ℂ => ‖∑ j, u j * y j‖ := (by fun_prop : Continuous _).measurable
  unfold fsLogReg
  fun_prop

theorem abs_fsLogReg_le (h : HermNorm n) (u x : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : linEval u x ≠ 0) (hx : 0 < h.dualNorm x) :
    |fsLogReg h u ε x| ≤ 2 * |Real.log ‖linEval u x‖| + (2 * |Real.log (h.dualNorm x)| + 1) := by
  have ht : 0 < ‖linEval u x‖ := norm_pos_iff.2 hu
  have he : fsLogReg h u ε x = Real.log ((‖linEval u x‖ / h.dualNorm x) ^ 2 + ε) / 2 := by
    unfold fsLogReg linEval
    congr 2
    field_simp
  rw [he]
  refine (LelongRegularise.abs_half_log_le (div_pos ht hx) hε hε1).trans ?_
  rw [Real.log_mul two_ne_zero (div_pos ht hx).ne', Real.log_div ht.ne' hx.ne']
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
    linarith
  have h2' : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have a1 := abs_sub (Real.log ‖linEval u x‖) (Real.log (h.dualNorm x))
  have a2 := abs_add_le (Real.log 2) (Real.log ‖linEval u x‖ - Real.log (h.dualNorm x))
  rw [abs_of_nonneg h2'] at a2
  linarith

theorem tendsto_fsLogReg_sub (h : HermNorm n) (u x : Fin n → ℂ) (hu : linEval u x ≠ 0)
    (hx : 0 < h.dualNorm x) :
    Tendsto (fun ε => fsLogReg h u ε x) (𝓝[>] 0)
      (𝓝 (Real.log ‖linEval u x‖ - Real.log (h.dualNorm x))) := by
  have := (fsLogReg_tendsto h u x hx hu).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have e : Real.log (‖∑ j, u j * x j‖ / h.dualNorm x) =
      Real.log ‖linEval u x‖ - Real.log (h.dualNorm x) :=
    Real.log_div (norm_pos_iff.2 hu).ne' hx.ne'
  rwa [fsLog, e] at this

theorem norm_chartDens_fsLogReg_le (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℝ} (φ : Fin d → (Fin n → ℂ) → ℝ) {R : ℝ}
    (hR : tsupport f ⊆ Metric.closedBall 0 R) (h0 : ∀ x ∈ zeroSet J, x ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {y : Fin (d + 1) → ℂ} (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    ‖chartDens J A (fsLogReg h u ε) (vecCons f φ) y‖ ≤
      2 * chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖)
          (vecCons f φ) y +
        chartAbsDens J A (fun x => 2 * |Real.log (h.dualNorm x)| + 1) (vecCons f φ) y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs]
    by_cases hxB : x ∈ Metric.closedBall 0 R
    · have hb := abs_fsLogReg_le h u x hε hε1 (hy x hx) (h.dualNorm_pos (h0 x hx.1))
      have hpos : (0 : ℝ) ≤ 2 * |Real.log (h.dualNorm x)| + 1 := by positivity
      rw [Set.indicator_of_mem hxB, Real.norm_eq_abs]
      simp only [abs_mul]
      rw [abs_of_nonneg hpos]
      exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans (le_of_eq (by ring))
    · have hM := ChartMassCompact.maDens_eq_zero hs.choose_spec (vecCons f φ) 0
        (by simpa using fun h' => hxB (hR h'))
      rw [hx.2] at hM
      rw [hM]
      simp
  · simp only [dif_neg hs]
    simp

theorem tendsto_chartDens_fsLogReg (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : IsFiniteProjection J A) (u : Fin n → ℂ)
    (ψ : Fin d → (Fin n → ℂ) → ℝ) (h0 : ∀ x ∈ zeroSet J, x ≠ 0) {y : Fin d → ℂ}
    (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    Tendsto (fun ε => chartDens J A (fsLogReg h u ε) ψ y) (𝓝[>] 0)
      (𝓝 (chartDens J A (fun x => Real.log ‖linEval u x‖) ψ y -
        chartDens J A (fun x => Real.log (h.dualNorm x)) ψ y)) := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_sub_distrib]
  refine tendsto_finsetSum _ fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs, ← sub_mul]
    exact (tendsto_fsLogReg_sub h u x (hy x hx) (h.dualNorm_pos (h0 x hx.1))).mul_const _
  · simp only [dif_neg hs, sub_zero]
    exact tendsto_const_nhds

theorem tendsto_varInt_fsLogReg (hLI : LogIntegrable.Statement) (hCM : ChartMassCompact.Statement)
    (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ)) (hu : linForm u ∉ J)
    (h0 : ∀ x ∈ zeroSet J, x ≠ 0) (hf : SmoothNear (zeroSet J) f) (hfc : HasCompactSupport f)
    (hφ : ∀ i, SmoothNear (zeroSet J) (φ i)) :
    Tendsto (fun ε => varInt J (d + 1) (fsLogReg h u ε) (vecCons f φ)) (𝓝[>] 0)
      (𝓝 (varInt J (d + 1) (fun x => Real.log ‖linEval u x‖) (vecCons f φ) -
        varInt J (d + 1) (fun x => Real.log (h.dualNorm x)) (vecCons f φ))) := by
  unfold varInt
  split_ifs with hA
  swap
  · simp only [sub_zero]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
  have hAf := hA.choose_spec
  unfold chartInt
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Fin n → ℂ)
  have hψ : ∀ i, SmoothNear (zeroSet J) (vecCons f φ i) := fun i =>
    Fin.cases (by simpa using hf) (fun i => by simpa using hφ i) i
  have hcs : HasCompactSupport (vecCons f φ 0) := by simpa using hfc
  have hcN : ContinuousOn (fun x => Real.log (h.dualNorm x)) (zeroSet J) :=
    (contDiffOn_log_dualNorm h).continuousOn.mono fun x hx => h0 x hx
  have hmN : Measurable fun x : Fin n → ℂ => Real.log (h.dualNorm x) :=
    Real.measurable_log.comp (SliceCut.continuous_dualNorm h).measurable
  have hmU : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖ :=
    Real.measurable_log.comp (Continuous.measurable (by unfold linEval; fun_prop))
  have hmeas : ∀ w, Measurable w → Measurable (chartDens J hA.choose w (vecCons f φ)) := fun w hw =>
    (SheetSumMeasurable.proof n (d + 1) J hA.choose w _ hJ hdim hAf hw hψ).1
  have hI1 := hLI n (d + 1) J hA.choose u (vecCons f φ) R hJ hdim hAf hu hψ
  have hI2 := hCM n (d + 1) J hA.choose (fun x => 2 * |Real.log (h.dualNorm x)| + 1) (vecCons f φ) hJ hdim
    hAf ((hcN.abs.const_smul (2 : ℝ)).add continuousOn_const) hψ (Or.inr ⟨0, hcs⟩)
  have hIN := hCM n (d + 1) J hA.choose _ (vecCons f φ) hJ hdim hAf hcN hψ (Or.inr ⟨0, hcs⟩)
  have hIU : Integrable (chartAbsDens J hA.choose (fun x => Real.log ‖linEval u x‖) (vecCons f φ)) := by
    rwa [← chartAbsDens_indicator_eq _ _ 0 (by simpa using hR)]
  rw [← integral_sub (integrable_chartDens hAf (hmeas _ hmU) hIU)
    (integrable_chartDens hAf (hmeas _ hmN) hIN)]
  obtain ⟨P, hP, hPy⟩ := LelongRegularise.exists_poly_of_linEval_eq_zero hJ hAf hu
  have hgood : ∀ᵐ y : Fin (d + 1) → ℂ, ∀ x ∈ fibre J hA.choose y, linEval u x ≠ 0 := by
    filter_upwards [LelongRegularise.ae_eval_ne_zero P hP] with y hy x hx hx0
    exact hy (hPy y x hx hx0)
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ ((hI1.const_mul 2).add hI2) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε _
    exact (hmeas _ (measurable_fsLogReg h u ε)).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hgood] with y hy
    exact norm_chartDens_fsLogReg_le h hAf φ hR h0 hε.1 hε.2 hy
  · filter_upwards [hgood] with y hy
    exact tendsto_chartDens_fsLogReg h hAf u _ h0 hy

end SliceFormLelongCompact

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegTailMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

theorem SliceRegTailMass.proof (hMono : SliceRegMassMono.Statement) (hCont : SliceRegMassContinuous.Statement)
    (hLim : SliceRegMassLimit.Statement) (hSec : SliceSectionTailMass.Statement)
    (hReg : SliceRegCutTail.Statement) (hM : SliceCutTailMass.Statement) : SliceRegTailMass.Statement := by
  intro n e h W F u' ℓ hW hF hu hℓ hℓP δ hδ
  set Φ : ℕ → ℝ → ℝ := fun k ε =>
    varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - sliceCut h k x)
        (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - sliceCut h k x)
        (fun _ x => Real.log (h.dualNorm x)) with hΦ
  set L : ℕ → ℝ := fun k => ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
    varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fun x => 1 - sliceCut h k x)
      (fun _ x => Real.log (h.dualNorm x)) with hL
  set G : ℕ → ℝ → ℝ := fun k t => if 0 < t then Φ k t else L k with hG
  have hmeas : ∀ k, Measurable fun x => 1 - sliceCut h k x :=
    fun k => measurable_const.sub (SliceCut.measurable h k)
  have hlim : ∀ k, Tendsto (Φ k) (𝓝[>] 0) (𝓝 (L k)) := fun k =>
    hLim n e h W F u' ℓ (sliceCut h k) hW hF hu hℓ hℓP (SliceCut.contDiff h k) (SliceCut.hasCompactSupport h k)
  have hanti : ∀ ε, 0 < ε → Antitone fun k => Φ k ε := fun ε hε k m hkm =>
    hMono n e h W F u' ℓ ε _ _ hW hF hℓ hε (hmeas m) (hmeas k)
      (fun x => by linarith [(SliceCut.mem_Icc h m x).2])
      (fun x => by linarith [SliceCut.monotone h x hkm]) (fun x => by linarith [(SliceCut.mem_Icc h k x).1])
  have hantiL : Antitone L := fun k m hkm =>
    le_of_tendsto_of_tendsto (hlim m) (hlim k) (eventually_nhdsWithin_of_forall fun ε hε => hanti ε hε hkm)
  have hGpos : ∀ k t, 0 < t → G k t = Φ k t := fun k t ht => by simp only [hG, if_pos ht]
  have hG0 : ∀ k, G k 0 = L k := fun k => by simp only [hG, lt_irrefl, if_false]
  have hGcont : ∀ k, ContinuousOn (G k) (Set.Icc 0 1) := by
    intro k t ht
    rcases ht.1.eq_or_lt with h0 | hpos
    · subst h0
      refine ContinuousWithinAt.mono ?_ fun x hx => (Set.mem_Ici.mpr hx.1)
      rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hG0]
      exact (hlim k).congr' (eventually_nhdsWithin_of_forall fun ε hε => (hGpos k ε hε).symm)
    · have h1 := hCont n e h W F u' ℓ (fun x => 1 - sliceCut h k x) 1 hW hF hℓ (hmeas k) fun x => by
        rw [abs_le]; constructor <;> linarith [(SliceCut.mem_Icc h k x).1, (SliceCut.mem_Icc h k x).2]
      have h2 : ContinuousOn (Φ k) (Set.Ioi 0) := h1.add continuousOn_const
      have hc := h2.continuousAt (Ioi_mem_nhds hpos)
      exact (hc.congr (eventually_of_mem (Ioi_mem_nhds hpos) fun ε hε => (hGpos k ε hε).symm)).continuousWithinAt
  have hU := Antitone.tendstoUniformlyOn_of_forall_tendsto (f := fun _ => (0 : ℝ)) isCompact_Icc hGcont
    (fun t _ => by
      rcases lt_or_ge 0 t with hpos | hpos
      · simpa only [hGpos _ t hpos] using hanti t hpos
      · simpa only [hG, not_lt.mpr hpos, if_false] using hantiL)
    continuousOn_const
    (fun t ht => by
      rcases ht.1.eq_or_lt with h0 | hpos
      · subst h0
        simp only [hG0]
        have := tendsto_finsetSum (divCycle W u').support fun P hP =>
          (hSec n e h W F u' ℓ hW hF hu hℓ hℓP P hP).const_mul (((divCycle W u' P : ℕ) : ℝ))
        simpa only [mul_zero, Finset.sum_const_zero] using this
      · simp only [hGpos _ t hpos]
        simpa only [add_zero] using (hReg n e h W F u' ℓ t hW hF hℓ hpos).add (hM n e h W F ℓ hW hF hℓ))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hU δ hδ)
  refine ⟨K, fun k hk ε hε => ?_⟩
  have := hK k hk ε ⟨hε.1.le, hε.2⟩
  rw [hGpos k ε hε.1, Real.dist_eq, zero_sub, abs_neg] at this
  exact (le_abs_self _).trans this.le

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOffDiscriminant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets StokesOffDiscriminant
open scoped ContDiff Manifold

noncomputable section

theorem StokesOffDiscriminant.proof : StokesOffDiscriminant.Statement := by
  intro n d J A P _ _ _ _ hsheet F G φ hF hG hφ hFc ⟨U, hUo, hPU, hFU⟩
  set K := closure {x | x ∈ zeroSet J ∧ F x ≠ 0} with hKdef
  have hKZ : K ⊆ zeroSet J :=
    closure_minimal (fun x hx => hx.1) (SheetSumMeasurable.isClosed_zeroSet J)
  have hKU : K ⊆ Uᶜ :=
    closure_minimal (fun x hx hxU => hx.2 (hFU x ⟨hxU, hx.1⟩)) hUo.isClosed_compl
  have hKc : IsCompact K := hFc.of_isClosed_subset isClosed_closure (closure_mono fun x hx => hx.2)
  have hwin : ∀ x : K, ∃ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (V : Set (Fin (d + 1) → ℂ))
      (W : Set (Fin n → ℂ)), IsOpen V ∧ IsOpen W ∧ (x : Fin n → ℂ) ∈ W ∧ DifferentiableOn ℂ s V ∧
        (∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
        ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ V ∧ IsSheetAt J A x' s := by
    rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := hsheet x (hKZ hx) fun h => hKU hx (hPU h)
    exact ⟨s, window_of_sheet hs⟩
  choose s V W hVo hWo hxW hsd hsec hWs using hwin
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover W hWo fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin n → ℂ) isClosed_closure
    (fun i : t => W i.1) (fun i => hWo i.1) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  have hρs : ∀ i, ContDiff ℝ ∞ (ρ i) := fun i => contMDiff_iff_contDiff.1 (ρ i).contMDiff
  set f : t → (Fin n → ℂ) → ℝ := fun i x => ρ i x * F x with hfdef
  have hsum : ∀ x ∈ zeroSet J, F x = ∑ i, f i x := by
    intro x hxZ
    by_cases hK : x ∈ K
    · have h1 := ρ.sum_eq_one hK
      rw [finsum_eq_sum_of_fintype] at h1
      simp only [hfdef, ← Finset.sum_mul, h1, one_mul]
    · have hF0 : F x = 0 := by_contra fun h => hK (subset_closure ⟨hxZ, h⟩)
      simp [hfdef, hF0]
  have hfs : ∀ i, SmoothNear (zeroSet J) (f i) := by
    obtain ⟨O, hO, hZO, hFO⟩ := hF
    exact fun i => ⟨O, hO, hZO, (hρs i).contDiffOn.mul hFO⟩
  have hfW : ∀ i, tsupport (f i) ⊆ W i.1 := fun i => tsupport_mul_subset_left.trans (hρ i)
  have hpiece := fun i : t => window_stokes (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G φ
    (hfs i) hG hφ hFc.mul_left (hfW i)
  have hL : ∀ y, chartDens J A F (vecCons G φ) y = ∑ i, chartDens J A (f i) (vecCons G φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => f i x * ReciprocityTheory.AnForm.maDens (fun k => vecCons G φ k ∘ s') y) ?_
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_weight_window (hsec i.1) (hWs i.1) (f i) (hfW i) _ y)
    intro x hx s' _
    rw [hsum x hx.1, Finset.sum_mul]
  have hR : ∀ y, chartDens J A G (vecCons F φ) y = ∑ i, chartDens J A G (vecCons (f i) φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => G x * ReciprocityTheory.AnForm.maDens (fun k => vecCons (f i) φ k ∘ s') y) ?_
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_cons_window (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G (hfW i) φ y)
    rintro x ⟨-, rfl⟩ s' hs'
    rw [maDens_sheet_finset_sum Finset.univ F f φ hs' hsum fun i _ => hfs i, Finset.mul_sum]
  unfold chartInt
  simp only [hL, hR]
  rw [integral_finsetSum _ fun i _ => (hpiece i).2.1, integral_finsetSum _ fun i _ => (hpiece i).2.2]
  exact Finset.sum_congr rfl fun i _ => (hpiece i).1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

theorem measurable_poincareDeepWeight : Measurable poincareDeepWeight := by
  have hn : Measurable fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2).measurable
  exact Measurable.ite (measurableSet_lt hn.log measurable_const) (hn.mul (hn.log.pow_const 2)).inv
    measurable_const

theorem tubeDeep_term (hR : TubeDeepRankOne.Statement) {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} {P : MvPolynomial (Fin (d + 1)) ℂ} {R : ℝ} {y : Fin (d + 1) → ℂ}
    {x : Fin n → ℂ} {s : (Fin (d + 1) → ℂ) → Fin n → ℂ} (hx : x ∈ fibre J A y) (hs : IsSheetAt J A x s)
    (hy : logAbsSq P y < -Real.exp 1) :
    |(Metric.closedBall 0 R).indicator (fun x => tubeWeight P (A *ᵥ x)) x *
        ReciprocityTheory.AnForm.maDens
          (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y| =
      (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 *
          ((2 / Real.pi) ^ (d + 1) * poincareDeepWeight (deepMap P s I y 0)) := by
  obtain ⟨U, hU, hxU, hsd, -, hsec, -⟩ := hs
  have hAx : A *ᵥ x = y := hx.2
  rw [hAx] at hxU
  have hP : eval y P ≠ 0 := by
    intro h0
    simp only [logAbsSq, h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Real.log_zero] at hy
    linarith [Real.exp_pos 1]
  rw [hR n d A P U s y hU hxU hsd (fun y' hy' => (hsec y' hy').1) hP]
  have hw : ∀ I : Fin d → Fin n,
      poincareDeepWeight (deepMap P s I y 0) = (‖eval y P‖ ^ 2 * logAbsSq P y ^ 2)⁻¹ := by
    intro I
    simp only [deepMap, Matrix.cons_val_zero, poincareDeepWeight]
    exact if_pos hy
  have ht : tubeWeight P y = (logAbsSq P y ^ 2)⁻¹ :=
    if_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
  simp only [hw]
  by_cases hxR : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
  · rw [Set.indicator_of_mem hxR, Set.indicator_of_mem hxR, hAx, ht, one_mul]
    have hp : 0 < ‖eval y P‖ := norm_pos_iff.2 hP
    have hl : logAbsSq P y ≠ 0 := by linarith [Real.exp_pos 1]
    rw [abs_of_nonneg (by positivity), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    field_simp
  · simp [Set.indicator_of_notMem hxR]

theorem TubeDeepMass.proof (hR : TubeDeepRankOne.Statement) (hC : TubeDeepAreaCount.Statement)
    (hW : TubeDeepWeightMass.Statement) : TubeDeepMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  have hc0 : 0 ≤ (2 / Real.pi) ^ (d + 1) := by positivity
  set g : (Fin (d + 1) → ℂ) → ℝ := fun z => (2 / Real.pi) ^ (d + 1) * poincareDeepWeight (z 0) with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z =>
    mul_nonneg hc0 (by unfold poincareDeepWeight; split_ifs <;> positivity)
  have hgm : Measurable g :=
    measurable_const.mul (measurable_poincareDeepWeight.comp (measurable_pi_apply 0))
  have hl : Measurable (logAbsSq P) :=
    ((continuous_norm.comp (MvPolynomial.continuous_eval P)).pow 2).measurable.log
  have hF : ∀ y, {y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y =
      sheetSum J A (fun x s => (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y := by
    intro y
    by_cases hy : logAbsSq P y < -Real.exp 1
    · rw [Set.indicator_of_mem (show y ∈ {y | logAbsSq P y < -Real.exp 1} from hy), tubeDens, chartAbsDens, sheetSum, sheetSum]
      refine finsum_congr fun x => finsum_congr fun hx => ?_
      split_ifs with h
      · exact tubeDeep_term hR hx h.choose_spec hy
      · rfl
    · rw [Set.indicator_of_notMem (show y ∉ {y | logAbsSq P y < -Real.exp 1} from hy)]
      have hw0 : ∀ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (I : Fin d → Fin n), g (deepMap P s I y) = 0 := by
        intro s I
        simp only [hg, deepMap, Matrix.cons_val_zero, poincareDeepWeight]
        exact mul_eq_zero_of_right _ (if_neg hy)
      simp [sheetSum, hw0]
  obtain ⟨N, hN⟩ := hC n d J A P R hJ hdim hA
  refine ⟨((measurable_tubeDens hA P R _).indicator (measurableSet_lt hl measurable_const)).aestronglyMeasurable,
    ?_⟩
  have hnn : ∀ y, 0 ≤ {y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y :=
    fun y => Set.indicator_nonneg (fun y _ => tubeDens_nonneg J A P R _ y) y
  show ∫⁻ y, ‖{y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y‖ₑ < ⊤
  calc _ = ∫⁻ y, ENNReal.ofReal (sheetSum J A (fun x s =>
          (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
            ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y) :=
        lintegral_congr fun y => by rw [Real.enorm_eq_ofReal (hnn y), hF y]
    _ ≤ (N : ℝ≥0∞) * ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R}, ENNReal.ofReal (g z) :=
        hN g hgm hg0
    _ = (N : ℝ≥0∞) * (ENNReal.ofReal ((2 / Real.pi) ^ (d + 1)) *
          ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R},
            ENNReal.ofReal (poincareDeepWeight (z 0))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact congrArg _ (lintegral_congr fun z => ENNReal.ofReal_mul hc0)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top N)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hW d R))

end

end GroundTheory.Heights₂.Heights
end

