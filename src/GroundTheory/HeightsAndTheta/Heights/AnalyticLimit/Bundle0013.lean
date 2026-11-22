import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0003
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh IsPosPot IsSection logNormSec mInt
  MIntegrable maMeasure maMeasure_thm logNormIntegrable mIntegrableCont)

noncomputable section

theorem continuousAt_of_charts {e : ℕ} {X : Type} [TopologicalSpace X] {E : Type}
    [TopologicalSpace E] (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) (g : X → E)
    (hg : ∀ j, ContinuousOn (g ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {y : X} (hy : y ∈ U) : ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  set c := A.chart j
  have hopen : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.isOpen_inter_preimage_symm hU
  have hmem : c y ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hj, by
    show c.symm (c y) ∈ U
    rw [c.left_inv hj]
    exact hy⟩
  have h1 : ContinuousAt (g ∘ c.symm) (c y) := (hg j).continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((g ∘ c.symm) ∘ c) y := h1.comp (c.continuousAt hj)
  refine h2.congr ?_
  filter_upwards [c.open_source.mem_nhds hj] with z hz
  simp [Function.comp, c.left_inv hz]

theorem continuous_secNorm {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L) (hs : IsSection A L s) :
    Continuous (secNorm L s) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hsc : ContinuousAt (s x₀) x₀ := continuousAt_of_charts A (L.isOpen_U x₀) (s x₀)
    (fun j => (hs.1 x₀ j).continuousOn) (L.mem_U x₀)
  have hφc : ContinuousAt (L.φ x₀) x₀ := continuousAt_of_charts A (L.isOpen_U x₀) (L.φ x₀)
    (fun j => (hL.1 x₀ j).continuousOn) (L.mem_U x₀)
  have hf : ContinuousAt (fun y => ‖s x₀ y‖ * Real.exp (-L.φ x₀ y)) x₀ :=
    hsc.norm.mul (Real.continuous_exp.continuousAt.comp hφc.neg)
  refine hf.congr ?_
  filter_upwards [(L.isOpen_U x₀).mem_nhds (L.mem_U x₀)] with y hy
  exact hs.2 x₀ y y ⟨hy, L.mem_U y⟩

theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (hP : IsPosPot A P) : IsPsh A P := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (hP x j y hy w hw).le

theorem greenEp_nonneg {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (x : W) : 0 ≤ greenEp L s ε x := by
  unfold greenEp
  apply Real.log_nonneg
  have : 0 ≤ ε / secNorm L s x ^ 2 := div_nonneg hε (sq_nonneg _)
  linarith

theorem greenEp_le_one {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (x : W) : greenEp L s ε x ≤ greenEp L s 1 x := by
  unfold greenEp
  have h0 : 0 ≤ ε / secNorm L s x ^ 2 := div_nonneg hε (sq_nonneg _)
  apply Real.log_le_log (by linarith)
  have : ε / secNorm L s x ^ 2 ≤ 1 / secNorm L s x ^ 2 :=
    div_le_div_of_nonneg_right hε1 (sq_nonneg _)
  linarith

theorem greenEp_one_eq {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) (x : W) :
    greenEp L s 1 x = Real.log (secNorm L s x ^ 2 + 1) - 2 * logNormSec L s x := by
  have hl : logNormSec L s x = Real.log (secNorm L s x) := rfl
  unfold greenEp
  rw [hl]
  by_cases hN : secNorm L s x = 0
  · simp [hN]
  · have h2 : secNorm L s x ^ 2 ≠ 0 := pow_ne_zero 2 hN
    have h3 : secNorm L s x ^ 2 + 1 ≠ 0 := by positivity
    rw [show 1 + 1 / secNorm L s x ^ 2 = (secNorm L s x ^ 2 + 1) / secNorm L s x ^ 2 by
      field_simp, Real.log_div h3 h2, Real.log_pow]
    push_cast
    ring

theorem greenEp_tendsto_zero {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ)
    (x : W) : Tendsto (fun ε => greenEp L s ε x) (𝓝[>] 0) (𝓝 0) := by
  unfold greenEp
  set c := secNorm L s x ^ 2
  have hc : ContinuousAt (fun ε : ℝ => 1 + ε / c) 0 :=
    (continuous_const.add (continuous_id.div_const c)).continuousAt
  have hlog : ContinuousAt (fun ε : ℝ => Real.log (1 + ε / c)) 0 := hc.log (by simp)
  have ht := hlog.tendsto
  simp only [zero_div, add_zero, Real.log_one] at ht
  exact tendsto_nhdsWithin_of_tendsto_nhds ht

theorem GreenMassZero.proof : GreenMassZero.Statement := by
  intro D W _ _ _ S η hη
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  set Φ : Fin (D + 1) → LocPot W := fun _ => S.Om.pot with hΦdef
  have hΦ : ∀ i, IsPotential S.A (Φ i) := fun _ => S.Om.isPot
  have hΦpsh : ∀ i, IsPsh S.A (Φ i) := fun _ => isPsh_of_isPosPot S.A _ S.Om.pos
  obtain ⟨hfin, hμ⟩ := maMeasure_thm S.A Φ hΦ hΦpsh
  set μ := maMeasure S.A Φ
  have hN : Continuous (secNorm S.L S.s) := continuous_secNorm S.A S.L S.s S.L_pot S.s_sec
  have hmeas : ∀ ε, Measurable (greenEp S.L S.s ε) := fun ε =>
    ((hN.measurable.pow_const 2).const_div ε |>.const_add 1).log

  have hlogN : Integrable (logNormSec S.L S.s) μ := by
    have hm : Measurable (logNormSec S.L S.s) := hN.measurable.log
    exact ((hμ _ hm).1).1 (logNormIntegrable S.A S.L S.s S.mult S.comp S.L_pot S.s_sec S.s_snc Φ hΦ)
  have hh : Integrable (fun x => Real.log (secNorm S.L S.s x ^ 2 + 1)) μ := by
    have hc : Continuous fun x => Real.log (secNorm S.L S.s x ^ 2 + 1) :=
      ((hN.pow 2).add continuous_const).log fun x =>
        (by positivity : (0 : ℝ) < secNorm S.L S.s x ^ 2 + 1).ne'
    exact ((hμ _ hc.measurable).1).1 (mIntegrableCont S.A Φ hΦ _ hc)
  have hG1 : Integrable (greenEp S.L S.s 1) μ := by
    have : greenEp S.L S.s 1 = fun x =>
        Real.log (secNorm S.L S.s x ^ 2 + 1) - 2 * logNormSec S.L S.s x :=
      funext (greenEp_one_eq S.L S.s)
    rw [this]
    exact hh.sub (hlogN.const_mul 2)
  have hnorm : ∀ ε, 0 < ε → ε ≤ 1 → ∀ x, ‖greenEp S.L S.s ε x‖ ≤ greenEp S.L S.s 1 x :=
    fun ε hε hε1 x => by
      rw [Real.norm_of_nonneg (greenEp_nonneg S.L S.s hε.le x)]
      exact greenEp_le_one S.L S.s hε.le hε1 x

  have hJ : ∀ ε, 0 < ε → ε ≤ 1 → ∀ t, S.J 0 ε t = ∫ x, greenEp S.L S.s ε x ∂μ := by
    intro ε hε hε1 t
    have hmix : mixedForms S.Om.pot (S.T t) 0 = Φ := by
      funext i
      simp [mixedForms, hΦdef]
    have hint : Integrable (greenEp S.L S.s ε) μ :=
      hG1.mono' (hmeas ε).aestronglyMeasurable (ae_of_all _ (hnorm ε hε hε1))
    have hmi : MIntegrable S.A Φ (greenEp S.L S.s ε) := ((hμ _ (hmeas ε)).1).2 hint
    show mInt S.A (mixedForms S.Om.pot (S.T t) 0) (greenEp S.L S.s ε) = _
    rw [hmix]
    exact (hμ _ (hmeas ε)).2 hmi

  have hT : Tendsto (fun ε => ∫ x, greenEp S.L S.s ε x ∂μ) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0 : ℝ))
      (F := fun ε x => greenEp S.L S.s ε x) (f := fun _ => (0 : ℝ)) (greenEp S.L S.s 1)
      (Eventually.of_forall fun ε => (hmeas ε).aestronglyMeasurable)
      (eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun ε hε => ae_of_all _ (hnorm ε hε.1 hε.2))
      hG1 (ae_of_all _ fun x => greenEp_tendsto_zero S.L S.s x)
    simpa using this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ x, greenEp S.L S.s ε x ∂μ < η := (tendsto_order.1 hT).2 η hη
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨min (u / 2) 1, lt_min (by linarith) one_pos, fun ε hε hεle t => ?_⟩
  have hε1 : ε ≤ 1 := hεle.trans (min_le_right _ _)
  have hεu : ε < u := lt_of_le_of_lt (hεle.trans (min_le_left _ _)) (by linarith)
  rw [hJ ε hε hε1 t]
  exact (hsub ⟨hε, hεu⟩).le

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListProductMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt maMeasure isPotentialAdd
  isPotentialRsmul isPotential_ofFun isPshAdd maMeasureMono maMeasure_thm massIndep mIntegrableCont
  pot_contDiffAt_two)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_formNonneg {A : FinHolAtlas D X} {V : Set X} (hV : interior Vᶜ = ∅)
    {P : LocPot X} (hP : IsPotential A P) (hnn : FormNonneg A V P) : IsPsh A P := by
  intro x j y hy w
  by_contra hneg
  push Not at hneg
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  have h2 := pot_contDiffAt_two hP x j hy.1 hy.2
  have hc : ContinuousAt (fun z => levi (P.φ x ∘ (A.chart j).symm) z w) y := by
    have h0 := ((h2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt
    unfold levi
    exact (((h0.clm_apply continuousAt_const).clm_apply continuousAt_const).add
      ((h0.clm_apply continuousAt_const).clm_apply continuousAt_const)).div_const 4
  have hev : ∀ᶠ z in 𝓝 y, levi (P.φ x ∘ (A.chart j).symm) z w < 0 ∧
      z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
    (hc.eventually (eventually_lt_nhds hneg)).and (hO.mem_nhds hy)
  obtain ⟨N, hNsub, hNo, hyN⟩ := mem_nhds_iff.1 hev
  have himg : IsOpen ((A.chart j).symm '' N) :=
    (A.chart j).isOpen_image_symm_of_subset_target hNo fun z hz => (hNsub hz).2.1
  have hsub : (A.chart j).symm '' N ⊆ Vᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzV
    have h := hnn x j z ⟨(hNsub hz).2.1, hzV, (hNsub hz).2.2⟩ w
    linarith [(hNsub hz).1]
  have hmem : (A.chart j).symm y ∈ interior Vᶜ := interior_maximal hsub himg ⟨y, hyN, rfl⟩
  rw [hV] at hmem
  exact hmem

theorem isPsh_add_neg {A : FinHolAtlas D X} {P Q : LocPot X} (hQ : IsPotential A Q)
    (hP : IsPotential A P) (hle : LeviLe A Set.univ 1 P 1 Q) : IsPsh A (Q + P.rsmul (-1)) := by
  intro x j y hy w
  have hyQ : (A.chart j).symm y ∈ Q.U x := hy.2.1
  have hyP : (A.chart j).symm y ∈ P.U x := hy.2.2
  have hlev := hle x j y ⟨hy.1, ⟨⟨Set.mem_univ _, hyP⟩, hyQ⟩⟩ w
  have hadd := levi_add_smul (-1) (pot_contDiffAt_two hQ x j hy.1 hyQ)
    (pot_contDiffAt_two hP x j hy.1 hyP) w
  show 0 ≤ levi (fun z => (Q.φ x ∘ (A.chart j).symm) z + (-1) * (P.φ x ∘ (A.chart j).symm) z) y w
  rw [hadd]
  linarith

theorem mInt_congr_φ (A : FinHolAtlas D X) {Φ Ψ : Fin D → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ)
    (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  unfold mInt ReciprocityTheory.AnForm.M.integralWith ReciprocityTheory.AnForm.M.locDens
  simp only [h]

theorem ListProductMass.proof : ListProductMass.Statement := by
  intro D X _ _ _ A R Om C₁ th u hT
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  have hNull := (DivisorNull.proof A R).2
  let T : Fin D → LocPot X := fun i => potForm (th i) (u i)
  let Q : Fin D → LocPot X := fun i => Om.pot + (th i).rsmul (-1)
  have hTpot : ∀ i, IsPotential A (T i) := fun i =>
    isPotentialAdd A _ _ (hT i).1.th_pot (isPotential_ofFun A _ (hT i).2)
  have hTpsh : ∀ i, IsPsh A (T i) := fun i => isPsh_of_formNonneg hNull (hTpot i) (hT i).1.nonneg
  have hQpot : ∀ i, IsPotential A (Q i) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotentialRsmul A _ _ (hT i).1.th_pot)
  have hQpsh : ∀ i, IsPsh A (Q i) := fun i => isPsh_add_neg Om.isPot (hT i).1.th_pot (hT i).1.th_le
  have hSpot : ∀ i, IsPotential A (T i + Q i) := fun i => isPotentialAdd A _ _ (hTpot i) (hQpot i)
  have hSpsh : ∀ i, IsPsh A (T i + Q i) := fun i =>
    isPshAdd A _ _ (hTpot i) (hQpot i) (hTpsh i) (hQpsh i)
  have hmono := maMeasureMono A T Q hTpot hTpsh hQpot hQpsh
  obtain ⟨_, hT'⟩ := maMeasure_thm A T hTpot hTpsh
  obtain ⟨hfinS, hS'⟩ := maMeasure_thm A (fun i => T i + Q i) hSpot hSpsh
  have e1 : mInt A T (fun _ => 1) = (maMeasure A T).real Set.univ := by
    rw [(hT' _ measurable_const).2 (mIntegrableCont A T hTpot _ continuous_const), integral_const,
      smul_eq_mul, mul_one]
  have e2 : mInt A (fun i => T i + Q i) (fun _ => 1) =
      (maMeasure A (fun i => T i + Q i)).real Set.univ := by
    rw [(hS' _ measurable_const).2 (mIntegrableCont A _ hSpot _ continuous_const), integral_const,
      smul_eq_mul, mul_one]
  have e3 : mInt A (fun i => T i + Q i) (fun _ => 1) =
      mInt A (fun i => Om.pot + LocPot.ofFun (u i)) (fun _ => 1) := by
    refine mInt_congr_φ A (fun i => ?_) _
    funext x y
    show (th i).φ x y + u i y + (Om.pot.φ x y + -1 * (th i).φ x y) = Om.pot.φ x y + u i y
    ring
  have e4 : mInt A (fun i => Om.pot + LocPot.ofFun (u i)) (fun _ => 1) = Om.vol :=
    massIndep A (fun _ => Om.pot) u (fun _ => Om.isPot) (fun i => (hT i).2)
  have hle : (maMeasure A T).real Set.univ ≤ (maMeasure A (fun i => T i + Q i)).real Set.univ :=
    ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_iff'.1 hmono Set.univ)
  change mInt A T (fun _ => 1) ≤ Om.vol
  rw [e1, ← e4, ← e3, e2]
  exact hle

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PProductBounds
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable isPotentialAdd
  isPotential_ofFun mIntCongrNull massIndep mIntegrableCont)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem ProductBounds.proof (hM : ListProductMass.Statement) (hT : ListTailLogSmooth.Statement) :
    ProductBounds.Statement := by
  intro D X _ _ _ A R Om C₁
  obtain ⟨CE, hCE⟩ := hT A R Om C₁
  refine ⟨Om.vol, CE, fun th u hf => ⟨?_, hCE th u hf⟩⟩
  have hpot : ∀ i, IsPotential A (potForm (th i) (u i)) := fun i =>
    isPotentialAdd A _ _ (hf i).1.th_pot (isPotential_ofFun A _ (hf i).2)
  have hnull := DivisorNull.proof A R
  have hind : mInt A (fun i => potForm (th i) (u i)) (R.Yo.indicator 1) =
      mInt A (fun i => potForm (th i) (u i)) (fun _ => 1) :=
    mIntCongrNull A _ R.Yoᶜ hnull.1 hnull.2 _ _ fun x hx => by
      have hx' : x ∈ R.Yo := by simpa using hx
      simp [Set.indicator_of_mem hx']
  have hstokes : mInt A (fun i => potForm (th i) (u i)) (fun _ => 1) = mInt A th (fun _ => 1) :=
    massIndep A th u (fun i => (hf i).1.th_pot) (fun i => (hf i).2)
  refine ⟨?_, hind.trans hstokes, ?_⟩
  · intro j K hK hKc
    have h1 := mIntegrableCont A _ hpot (fun _ => (1 : ℝ)) continuous_const j K hK hKc
    have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo) :=
      (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target R.isOpen_Yo
    refine (h1.indicator hO.measurableSet).congr_fun (fun y hy => ?_) hKc.measurableSet
    by_cases hy' : (A.chart j).symm y ∈ R.Yo
    · have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo := ⟨hK hy, hy'⟩
      simp [Set.indicator_of_mem hyO, Set.indicator_of_mem hy']
    · have hyO : y ∉ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo := fun h => hy' h.2
      simp [Set.indicator_of_notMem hyO, Set.indicator_of_notMem hy']
  · rw [← hstokes]
    exact hM A R Om C₁ th u hf

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

