import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartLeviThGe
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListTailLog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot logNormSec)

theorem log_le_one_add_mul_log {a b B : ℝ} (ha : Real.exp 1 ≤ a) (hb : 0 < b) (hB : 0 ≤ B)
    (hab : b ≤ a + B) : Real.log b ≤ (1 + B) * Real.log a := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ha0 : 0 < a := by linarith
  have hla : 1 ≤ Real.log a := by
    have := Real.log_le_log (Real.exp_pos 1) ha
    rwa [Real.log_exp] at this
  have h1 : b ≤ a * (1 + B) := by nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ a by linarith) hB]
  have h2 : Real.log b ≤ Real.log a + Real.log (1 + B) := by
    rw [← Real.log_mul ha0.ne' (by linarith)]
    exact Real.log_le_log hb h1
  have h3 : Real.log (1 + B) ≤ B := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + B by linarith)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hla hB]

theorem ListTailLog.proof (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLog.Statement := by
  intro X _ _ _ D A R hr Om C₁
  obtain ⟨L, s, hL, hs, hs1, hYo, hden, hrc, hrEc, B, hB⟩ := hC D A R
  have hrE : ∀ x ∈ R.Yo, Real.exp 1 ≤ rSec L s x := fun x hx => by
    rw [← hYo] at hx
    have hpos : 0 < ‖s x x‖ * Real.exp (-L.φ x x) :=
      mul_pos (norm_pos_iff.2 hx) (Real.exp_pos _)
    have : logNormSec L s x ≤ 0 := Real.log_nonpos hpos.le (hs1 x)
    simp only [rSec]
    linarith
  have hC₁ : 0 ≤ max C₁ 0 * (1 + max B 0) :=
    mul_nonneg (le_max_right _ _) (by linarith [le_max_right B 0])
  obtain ⟨CE, hCE⟩ := hE D A Om L s hL hs (hYo ▸ hden) hs1 _ hC₁
  obtain ⟨CE', hCE'⟩ := hS D (max B 0) CE
  refine ⟨CE', fun th u hT => ?_⟩
  obtain ⟨hA, hpos, hmono⟩ := hM D A R.Yo R.r Om C₁ th u R.isOpen_Yo hT
  have hu : ∀ i, IsLemmaEPot A Om L s (max C₁ 0 * (1 + max B 0)) (u i) := fun i => by
    have hTi := hT i
    refine ⟨by rw [hYo]; exact hTi.u_smooth, by rw [hYo]; exact hA i,
      by rw [hYo]; exact hTi.u_nonpos, fun x hx => ?_, ?_⟩
    · rw [hYo] at hx
      have hl := log_le_one_add_mul_log (b := R.r x) (hrE x hx) (by linarith [hr x hx, Real.exp_pos 1])
        (le_max_right B 0) (by linarith [(abs_le.1 (hB x hx)).2, le_max_left B 0])
      have h0 : 0 ≤ Real.log (R.r x) :=
        Real.log_nonneg (by linarith [hr x hx, Real.add_one_le_exp (1 : ℝ)])
      have := mul_le_mul_of_nonneg_left hl (le_max_right C₁ 0)
      have := mul_le_mul_of_nonneg_right (le_max_left C₁ 0) h0
      have := hTi.le_u x hx
      nlinarith
    · rcases hTi.smooth_or_pole with h | h
      · exact Or.inl h
      · right
        rw [hYo]
        exact h
  have h2 : TailLogBound A R.Yo (rSec L s) (fun j => potForm (th j) (u j)) CE := by
    have h1 := hCE u hu
    rw [hYo] at h1
    intro R₀ hR₀
    obtain ⟨hi, hle⟩ := h1 R₀ hR₀
    obtain ⟨hi', hle'⟩ := hmono _
      (fun x => Set.indicator_nonneg (fun y hy => Real.log_nonneg
        (by linarith [hrE y hy.1, Real.add_one_le_exp (1 : ℝ)])) x)
      (fun x hx => Set.indicator_of_notMem (fun h => hx h.1) _) hi
    exact ⟨hi', hle'.trans hle⟩
  exact hCE' A R.Yo R.r (rSec L s) _ R.isOpen_Yo hrc hrEc hr hrE
    (fun x hx => (hB x hx).trans (le_max_left B 0)) hpos h2

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormHolo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem continuousOn_of_holoOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {W : Set X} {g : X → ℂ} (hg : A.HoloOn W g) : ContinuousOn g W := by
  intro x hx
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ W
      rw [(A.chart j).left_inv hj]; exact hx⟩
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) := (hg j _ hmem).continuousAt
  have h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp h1 ((A.chart j).continuousAt hj)
  have heq : (g ∘ (A.chart j).symm) ∘ A.chart j =ᶠ[nhds x] g := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
    simp [Function.comp, (A.chart j).left_inv hz]
  exact (h2.congr heq).continuousWithinAt

theorem logNormHolo_of_continuousOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {W : Set X} {g : X → ℂ} (hW : IsOpen W) (hg : A.HoloOn W g) (hgc : ContinuousOn g W)
    (hne : ∀ y ∈ W, g y ≠ 0) {y : X} (hy : y ∈ W) : ∃ V : Set X, IsOpen V ∧ y ∈ V ∧
      V ⊆ W ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ z ∈ V, Real.log ‖g z‖ = (G z).re := by
  have hc : g y ≠ 0 := hne y hy
  have hcn : 0 < ‖g y‖ := norm_pos_iff.2 hc

  have hslit : ∀ w ∈ Metric.ball (g y) ‖g y‖, w / g y ∈ Complex.slitPlane := by
    intro w hw
    apply Complex.ball_one_subset_slitPlane
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have : w / g y - 1 = (w - g y) / g y := by field_simp
    rw [this, norm_div, div_lt_one hcn]
    exact hw
  refine ⟨W ∩ g ⁻¹' Metric.ball (g y) ‖g y‖, hgc.isOpen_inter_preimage hW Metric.isOpen_ball,
    ⟨hy, by simpa using hcn⟩, Set.inter_subset_left,
    fun z => Complex.log (g z / g y) + (Real.log ‖g y‖ : ℂ), ?_, ?_⟩
  · intro j v hv
    have ha : AnalyticAt ℂ (g ∘ (A.chart j).symm) v := hg j v ⟨hv.1, hv.2.1⟩
    have hs : (g ∘ (A.chart j).symm) v / g y ∈ Complex.slitPlane := hslit _ hv.2.2
    exact ((ha.div analyticAt_const hc).clog hs).add analyticAt_const
  · intro z hz
    have hz0 : g z ≠ 0 := hne z hz.1
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re]
    rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 hc)]
    ring

theorem LogNormHolo.proof (hCC : ChartCont.Statement) : LogNormHolo.Statement := by
  intro X _ D A W g hW hg hne y hy
  exact logNormHolo_of_continuousOn A hW hg ((hCC D A W hW).2 g hg) hne hy

theorem LogNormHolo.full : LogNormHolo.Statement := by
  intro X _ D A W g hW hg hne y hy
  exact logNormHolo_of_continuousOn A hW hg (continuousOn_of_holoOn A hg) hne hy

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PNormSqSmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open scoped ContDiff

theorem NormSqSmooth.proof : NormSqSmooth.Statement := by
  intro X _ D A U g hg j
  have h1 : ContDiffOn ℝ ∞ (g ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    ((hg j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiff ℝ ∞ (fun w : ℂ => ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  exact h2.comp_contDiffOn h1

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegRCont
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open Filter Topology

theorem RegRCont.proof : RegRCont.Statement := by
  intro X _ D A R y hy
  set j := bdIdx R y
  have hyU : y ∈ bdDom R j := mem_bdDom_bdIdx R y
  let g : (Fin D → ℂ) → ℝ := fun z =>
    Real.exp 1 + R.f j z - ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)
  have key : ∀ y' ∈ bdDom R j ∩ R.Yo,
      R.ψ j y' ∉ coordDiv (R.S j) ∧ R.r y' = g (R.ψ j y') := by
    rintro y' ⟨⟨hs, hW⟩, hY⟩
    have hinv : (R.ψ j).symm (R.ψ j y') = y' := (R.ψ j).left_inv hs
    have hnot : R.ψ j y' ∉ coordDiv (R.S j) :=
      (R.mem_Yo_iff j _ hW).1 (by rw [hinv]; exact hY)
    refine ⟨hnot, ?_⟩
    have h := R.r_chart j (R.ψ j y') ⟨hW, hnot⟩
    rw [hinv] at h
    exact h
  have hg : ContinuousAt g (R.ψ j y) := by
    have hW : R.ψ j y ∈ R.W j := hyU.2
    have hnd := (key y ⟨hyU, hy⟩).1
    have hf : ContinuousAt (R.f j) (R.ψ j y) :=
      (R.f_cont j).continuousAt ((R.isOpen_kappaOpenNeighbourhood j).mem_nhds hW)
    refine (continuousAt_const.add hf).sub ?_
    refine tendsto_finsetSum (R.S j) fun i hi => ?_
    have hzi : R.ψ j y i ≠ 0 := fun h0 => hnd ⟨i, hi, h0⟩
    have hc : ContinuousAt (fun z : Fin D → ℂ => ‖z i‖ ^ 2) (R.ψ j y) :=
      ((continuous_apply i).norm.pow 2).continuousAt
    exact hc.log (pow_ne_zero 2 (norm_ne_zero_iff.2 hzi))
  have hO : IsOpen (bdDom R j ∩ R.Yo) := (isOpen_bdDom R j).inter R.isOpen_Yo
  have heq : g ∘ R.ψ j =ᶠ[𝓝 y] R.r :=
    Filter.eventually_of_mem (hO.mem_nhds ⟨hyU, hy⟩) fun y' h => ((key y' h).2).symm
  exact ((hg.comp ((R.ψ j).continuousAt hyU.1)).congr heq).continuousWithinAt

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection logNormSec)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem RegSection.proof (hDense : RegYoDense.Statement) (hRC : RegRCont.Statement)
    (hMet : BdMetric.Statement) (hProps : BdSectionProps.Statement)
    (hNorm : BdNormCont.Statement) (hCmp : BdComparison.Statement) : RegSection.Statement := by
  intro X _ _ _ D A R
  obtain ⟨φ, hφ⟩ := hMet D A R
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y : X,
      ‖bdSec R y y‖ * Real.exp (-(bdPot R φ 0).φ y y) ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_univ.image (hNorm D A R φ hφ 0)).bddAbove
    exact ⟨M, fun y => hM ⟨y, Set.mem_univ _, rfl⟩⟩
  have hM1 : (0 : ℝ) < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set c := Real.log (max M 1) with hc
  have hφc : ∀ y : X, (bdPot R φ c).φ y y = (bdPot R φ 0).φ y y + c := fun y => by
    simp [bdPot]
  obtain ⟨hPot, hSec, hOpen⟩ := hProps D A R φ hφ c
  have hle : ∀ y : X, ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y) ≤ 1 := by
    intro y
    rw [hφc, neg_add, Real.exp_add, ← mul_assoc, Real.exp_neg c, hc, Real.exp_log hM1,
      mul_inv_le_iff₀ hM1, one_mul]
    exact (hM y).trans (le_max_left _ _)
  refine ⟨bdPot R φ c, bdSec R, hPot, hSec, hle, hOpen, hDense D A R, hRC D A R, ?_,
    hCmp D A R φ hφ c⟩
  have hne : ∀ y ∈ R.Yo, ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y) ≠ 0 := by
    intro y hy
    rw [← hOpen] at hy
    exact mul_ne_zero (norm_ne_zero_iff.2 hy) (Real.exp_pos _).ne'
  have hlog : ContinuousOn (fun y => logNormSec (bdPot R φ c) (bdSec R) y) R.Yo :=
    (hNorm D A R φ hφ c).continuousOn.log hne
  exact continuousOn_const.sub (continuousOn_const.mul hlog)

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegYoDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)

theorem dense_compl_coordDiv {D : ℕ} (S : Finset (Fin D)) : Dense (coordDiv S)ᶜ := by
  have h : (coordDiv S)ᶜ = ⋂ i ∈ (S : Set (Fin D)), (fun z : Fin D → ℂ => z i) ⁻¹' ({0}ᶜ) := by
    ext z
    simp [coordDiv]
  rw [h]
  refine dense_biInter_of_isOpen (fun i _ => ?_) S.countable_toSet (fun i _ => ?_)
  · exact isOpen_compl_singleton.preimage (continuous_apply i)
  · exact (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval i)

theorem RegYoDense.proof : RegYoDense.Statement := by
  intro X _ D A R
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hxU⟩
  have hxj : x ∈ bdDom R (bdIdx R x) := mem_bdDom_bdIdx R x
  set j := bdIdx R x
  have hO : IsOpen ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))) :=
    (R.ψ j).isOpen_image_source_inter (hU.inter (isOpen_bdDom R j))
  have hne : ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))).Nonempty :=
    ⟨R.ψ j x, x, ⟨hxj.1, hxU, hxj⟩, rfl⟩
  obtain ⟨z, ⟨y, ⟨hys, hyU, hyD⟩, rfl⟩, hz⟩ :=
    (dense_compl_coordDiv (R.S j)).inter_open_nonempty _ hO hne
  have hYo := (R.mem_Yo_iff j (R.ψ j y) hyD.2).2 hz
  rw [(R.ψ j).left_inv hys] at hYo
  exact ⟨y, hyU, hYo⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StatementsPullback
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential HoloMap)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe (compat_chart levi_base_indep)

noncomputable section

structure IsPullbackData {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    {B : FinHolAtlas D Y} {A : FinHolAtlas E Z} (R' : RegChartData B) (R : RegChartData A)
    (f : Y → Z) : Prop where
  holo : HoloMap B A f
  Yo_eq : R'.Yo = f ⁻¹' R.Yo
  r_eq : ∀ y ∈ R'.Yo, R'.r y = R.r (f y)
  φ_eq : ∀ y ∈ R'.Yo, R'.φ y = R.φ (f y)
  θ_eq : ∀ (x x' : Y) (k : Fin B.n),
    ∀ y ∈ (B.chart k).target ∩ (B.chart k).symm ⁻¹' (R'.θ.U x ∩ f ⁻¹' R.θ.U (f x')),
    ∀ w : Fin D → ℂ, levi (R'.θ.φ x ∘ (B.chart k).symm) y w =
      levi ((fun z => R.θ.φ (f x') (f z)) ∘ (B.chart k).symm) y w
  om_le : ∃ K : ℝ, ∀ (x x' : Y) (k : Fin B.n),
    ∀ y ∈ (B.chart k).target ∩ (B.chart k).symm ⁻¹' (R'.om.U x ∩ f ⁻¹' R.om.U (f x')),
    ∀ w : Fin D → ℂ, levi ((fun z => R.om.φ (f x') (f z)) ∘ (B.chart k).symm) y w ≤
      K * levi (R'.om.φ x ∘ (B.chart k).symm) y w

def C2ConvOn {E : ℕ} {Z : Type} [TopologicalSpace Z] (A : FinHolAtlas E Z) (V : Set Z)
    (g : ℝ → Z → ℝ) (φ : Z → ℝ) : Prop :=
  ∀ (k : Fin A.n) (K : Set (Fin E → ℂ)), IsCompact K →
    K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V →
    TendstoUniformlyOn (fun t y => g t ((A.chart k).symm y)) (fun y => φ ((A.chart k).symm y))
        (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fderiv ℝ fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fderiv ℝ fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K

def C2ConvergencePullback.Statement : Prop :=
  ∀ {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] (B : FinHolAtlas D Y)
    (A : FinHolAtlas E Z) (f : Y → Z), HoloMap B A f →
    ∀ (V : Set Z), IsOpen V → ∀ (g : ℝ → Z → ℝ) (φ : Z → ℝ) (φ' : Y → ℝ),
      A.SmoothOn V φ → (∀ y ∈ f ⁻¹' V, φ' y = φ (f y)) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (g t)) →
      C2ConvOn A V g φ → C2ConvOn B (f ⁻¹' V) (fun t => g t ∘ f) φ'

def SystemPullback.Statement : Prop :=
  ∀ {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {B : FinHolAtlas D Y}
    {A : FinHolAtlas E Z} (R' : RegChartData B) (R : RegChartData A) (f : Y → Z),
    IsPullbackData R' R f → ∀ S : System R, ∃ S' : System R', ∀ t y, S'.ph t y = S.ph t (f y)

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TailBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

def TailBound.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (F : Family A), (∀ x ∈ F.Yo, Real.exp 1 ≤ F.r x) →
    ∃ CE : ℝ, ∀ (i : Fin D → Fin F.m) (τ : Fin D → ℝ),
      (∀ j, 0 < τ j ∧ (F.sys (i j)).ell₀ ≤ ell (τ j) ∧ errE (F.sys (i j)).C (τ j) ≤ 1) →
      TailLogBound A F.Yo F.r (fun j => (F.sys (i j)).curr (τ j)) CE

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem tailLogBound_congr {A : FinHolAtlas D X} {Yo : Set X} {r r' : X → ℝ}
    (h : ∀ x ∈ Yo, r x = r' x) {T : Fin D → LocPot X} {CE : ℝ}
    (hT : TailLogBound A Yo r T CE) : TailLogBound A Yo r' T CE := by
  intro R₀ hR₀
  have ht : tail Yo r R₀ = tail Yo r' R₀ := Set.ext fun x =>
    ⟨fun hx => ⟨hx.1, by rw [← h x hx.1]; exact hx.2⟩,
      fun hx => ⟨hx.1, by rw [h x hx.1]; exact hx.2⟩⟩
  have hi : (tail Yo r' R₀).indicator (fun x => Real.log (r' x)) =
      (tail Yo r R₀).indicator (fun x => Real.log (r x)) := by
    rw [ht]
    exact Set.indicator_congr fun x hx => by rw [h x hx.1]
  rw [hi]
  exact hT R₀ hR₀

theorem isBoundedPotForm_congr {A : FinHolAtlas D X} {Yo : Set X} {r r' : X → ℝ}
    (h : ∀ x ∈ Yo, r x = r' x) {Om : KaehlerForm A} {C₁ : ℝ} {th : LocPot X} {u : X → ℝ}
    (hT : IsBoundedPotForm A Yo r Om C₁ th u) : IsBoundedPotForm A Yo r' Om C₁ th u :=
  { hT with le_u := fun x hx => by rw [← h x hx]; exact hT.le_u x hx }

theorem isBoundedPotForm_mono {A : FinHolAtlas D X} {Yo : Set X} {r : X → ℝ}
    (hr : ∀ x ∈ Yo, Real.exp 1 ≤ r x) {Om : KaehlerForm A} {C₁ C₁' : ℝ} (hC : C₁ ≤ C₁')
    {th : LocPot X} {u : X → ℝ} (hT : IsBoundedPotForm A Yo r Om C₁ th u) :
    IsBoundedPotForm A Yo r Om C₁' th u :=
  { hT with
    le_u := fun x hx => by
      have h0 : 0 ≤ Real.log (r x) := Real.log_nonneg (le_trans (by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith) (hr x hx))
      have := mul_le_mul_of_nonneg_right hC h0
      have := hT.le_u x hx
      linarith }

theorem TailBound.proof (h₁ : ListTailLog.Statement) (h₂ : BoundingKaehler.Statement) :
    TailBound.Statement := by
  intro X _ _ _ D A F hr
  rcases Nat.eq_zero_or_pos F.m with hm | hm
  · rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      obtain ⟨CE, hCE⟩ := tailLogBound_dim_zero A F.Yo F.r Fin.elim0
      refine ⟨CE, fun i τ _ => ?_⟩
      have e : (fun j => (F.sys (i j)).curr (τ j)) = (Fin.elim0 : Fin 0 → LocPot X) :=
        funext fun j => j.elim0
      rw [e]
      exact hCE
    · exact ⟨0, fun i => absurd (i ⟨0, hD⟩).2 (by omega)⟩
  · set k : Fin F.m := ⟨0, hm⟩
    obtain ⟨Om, hOm⟩ := h₂ D A ⟨(F.R k).om, (F.R k).om_pot, (F.R k).om_pos⟩ F.m
      (fun i => thetaOmega (F.R i))
      (fun i => ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (F.R i).θ_pot (F.R i).om_pot)
    have hrk : ∀ x ∈ (F.R k).Yo, Real.exp 1 ≤ (F.R k).r x := fun x hx => by
      rw [F.Yo_eq k] at hx
      rw [F.r_eq k x hx]
      exact hr x hx
    obtain ⟨CE, hCE⟩ := h₁ D A (F.R k) hrk Om (∑ i, (|(F.R i).C| + |(F.sys i).C|))
    refine ⟨CE, fun i τ hτ => ?_⟩
    have h := hCE (fun j => thetaOmega (F.R (i j))) (fun j => (F.sys (i j)).uT (τ j)) fun j => by
      have hRi : ∀ x ∈ (F.R (i j)).Yo, Real.exp 1 ≤ (F.R (i j)).r x := fun x hx => by
        rw [F.Yo_eq] at hx
        rw [F.r_eq _ x hx]
        exact hr x hx
      have hT := ((F.sys (i j)).curr_isSmoothPotForm hRi Om (hOm (i j)).1 (hOm (i j)).2 (τ j)
        (hτ j).1 (hτ j).2.1 (hτ j).2.2).1
      have hCi : |(F.R (i j)).C| + |(F.sys (i j)).C| ≤ ∑ l, (|(F.R l).C| + |(F.sys l).C|) :=
        Finset.single_le_sum (f := fun l => |(F.R l).C| + |(F.sys l).C|)
          (fun _ _ => by positivity) (Finset.mem_univ _)
      have hT' := isBoundedPotForm_mono hRi hCi hT
      rw [F.Yo_eq] at hT' ⊢
      exact isBoundedPotForm_congr (fun x hx => by rw [F.r_eq _ x hx, F.r_eq k x hx]) hT'
    rw [F.Yo_eq k] at h
    exact tailLogBound_congr (fun x hx => F.r_eq k x hx) h

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

