import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005
import Development.WeilBound.CoreStatements.AmpleLineBundles.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricQuotientOfMultihomogPair
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Decay

open Filter Topology

theorem analyticAt_aeval {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {v : E → σ → ℂ} {z : E}
    (hv : ∀ p, AnalyticAt ℂ (fun w => v w p) z) (q : MvPolynomial σ ℤ) :
    AnalyticAt ℂ (fun w => (aeval (v w) q : ℂ)) z := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, aeval_X]
    exact hp.mul (hv i)

theorem continuousAt_of_chart {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
    (c : OpenPartialHomeomorph X E) {x : X} (hx : x ∈ c.source) {F : X → Y}
    (h : ContinuousAt (fun z => F (c.symm z)) (c x)) : ContinuousAt F x := by
  have h1 : ContinuousAt (fun y => F (c.symm (c y))) x :=
    ContinuousAt.comp (f := c) (g := fun z => F (c.symm z)) h (c.continuousAt hx)
  refine h1.congr ?_
  filter_upwards [c.open_source.mem_nhds hx] with y hy
  rw [c.left_inv hy]

theorem isOpen_multicone {K : Type*} [Finite K] {ι : K → Type*} :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem eventually_abs_le {X : Type*} [TopologicalSpace X] {u : X → ℝ} {x : X} (h : ContinuousAt u x) :
    ∀ᶠ y in 𝓝 x, |u y| ≤ |u x| + 1 :=
  (h.abs.eventually_lt (continuousAt_const (y := |u x| + 1)) (by linarith)).mono fun _ hy => hy.le

theorem section_zero {e : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) {x x' y : X} (hy : y ∈ L.U x ∩ L.U x') (h0 : s x y = 0) :
    s x' y = 0 := by
  have h := hs.2 x x' y hy
  rw [h0, norm_zero, zero_mul] at h
  exact norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right (Real.exp_ne_zero _))

theorem logNormSec_eq {e : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) {x y : X} (hy : y ∈ L.U x) (h0 : s x y ≠ 0) :
    logNormSec L s y = Real.log ‖s x y‖ - L.φ x y := by
  unfold logNormSec
  rw [hs.2 y x y ⟨L.mem_U y, hy⟩, Real.log_mul (norm_ne_zero_iff.2 h0) (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem log_ratio_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (Eh : HermLine ι)
    {dg dh : K → ℕ} {G Hf : MRing ι} (hG : IsMultiHomog G dg) (hH : IsMultiHomog Hf dh)
    (hdeg : ∀ k, (dg k : ℤ) = dh k + Eh.a k) (t : K → ℂ) (ht : ∀ k, t k ≠ 0) (w : (Σ k, ι k) → ℂ)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hGw : aeval w G ≠ (0 : ℂ)) (hHw : aeval w Hf ≠ (0 : ℂ)) :
    Real.log ‖(aeval w G : ℂ) / aeval w Hf‖ - Real.log (Eh.h w) =
      Real.log ‖(aeval (fun p => t p.1 * w p) G : ℂ) / aeval (fun p => t p.1 * w p) Hf‖ -
        Real.log (Eh.h fun p => t p.1 * w p) := by
  rw [aeval_scale hG, aeval_scale hH, Eh.smul t w ht]
  have hT : 0 < ∏ k, ‖t k‖ ^ Eh.a k := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (ht k)) _
  have hP : ‖∏ k, t k ^ dg k‖ = ‖∏ k, t k ^ dh k‖ * ∏ k, ‖t k‖ ^ Eh.a k := by
    simp only [norm_prod, norm_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, hdeg k, zpow_add₀ (norm_ne_zero_iff.2 (ht k)), zpow_natCast]
  have hPh : ‖∏ k, t k ^ dh k‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k))
  have hn : ‖((∏ k, t k ^ dg k) * aeval w G : ℂ) / ((∏ k, t k ^ dh k) * aeval w Hf)‖ =
      (∏ k, ‖t k‖ ^ Eh.a k) * ‖(aeval w G : ℂ) / aeval w Hf‖ := by
    rw [norm_div, norm_mul, norm_mul, hP, norm_div]
    field_simp
  have hq : ‖(aeval w G : ℂ) / aeval w Hf‖ ≠ 0 := norm_ne_zero_iff.2 (div_ne_zero hGw hHw)
  rw [hn, Real.log_mul hT.ne' hq, Real.log_mul hT.ne' (Eh.pos w hw).ne']
  ring

theorem decay_arith {N : ℕ} (hN : 0 < N) {Lf lh lg φ lC Bh Bφ : ℝ} (h1 : (N : ℝ) * Lf ≤ lC + lg)
    (h2 : |lh| ≤ Bh) (h3 : |φ| ≤ Bφ) :
    Lf - lh ≤ -(1 / (2 * (N : ℝ))) * (Real.exp 1 - 2 * (lg - φ)) +
      ((lC + Real.exp 1 / 2 + Bφ) / (N : ℝ) + Bh) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have e1 : Lf ≤ (lC + lg) / N := by
    rw [le_div_iff₀ hn]
    linarith
  have e2 : -(1 / (2 * (N : ℝ))) * (Real.exp 1 - 2 * (lg - φ)) + (lC + Real.exp 1 / 2 + Bφ) / N =
      (lC + lg) / N + (Bφ - φ) / N := by
    field_simp
    ring
  have e3 : 0 ≤ (Bφ - φ) / N := div_nonneg (by linarith [le_abs_self φ]) hn.le
  have e4 : -lh ≤ Bh := by linarith [neg_abs_le lh]
  linarith

theorem local_decay : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → (∀ y : R.X, aeval (R.lift y y) G ≠ (0 : ℂ) → aeval (R.lift y y) Hf ≠ (0 : ℂ) → π y ∈ S.open') → ∀ x₀ : R.X, aeval (R.lift x₀ x₀) Hf ≠ (0 : ℂ) → ∃ (V : Set R.X) (N : ℕ) (C : ℝ), IsOpen V ∧ x₀ ∈ V ∧ 0 < N ∧ ∀ y ∈ V, aeval (R.lift y y) Hf ≠ (0 : ℂ) ∧ (π y ∈ S.open' → aeval (R.lift y y) G ≠ (0 : ℂ) → Real.log ‖(aeval (R.lift y y) G : ℂ) / aeval (R.lift y y) Hf‖ - Real.log (Eh.h (R.lift y y)) ≤ -(1 / (2 * (N : ℝ))) * rW S.L S.s (π y) + C) := by
  intro K _ ι _ P J e R σ S π hπ Eh hEh dg dh G Hf hG hH hdeg hyp x₀ hx₀
  obtain ⟨j, hj⟩ := R.A.cover x₀
  obtain ⟨k, hk⟩ := S.A.cover (π x₀)
  have hz₀ : (R.A.chart j).symm (R.A.chart j x₀) = x₀ := (R.A.chart j).left_inv hj
  have hd₀ : (S.A.chart k).symm (S.A.chart k (π x₀)) = π x₀ := (S.A.chart k).left_inv hk
  have hcoord : ∀ p, AnalyticAt ℂ (fun z => R.lift x₀ ((R.A.chart j).symm z) p) (R.A.chart j x₀) := fun p =>
    R.holo x₀ p j _ ⟨(R.A.chart j).map_source hj, by
      show (R.A.chart j).symm (R.A.chart j x₀) ∈ R.U x₀
      rw [hz₀]; exact R.mem_U x₀⟩
  have hGa := analyticAt_aeval hcoord G
  have hHa := analyticAt_aeval hcoord Hf
  have hHc : ContinuousAt (fun y => (aeval (R.lift x₀ y) Hf : ℂ)) x₀ :=
    continuousAt_of_chart (R.A.chart j) hj hHa.continuousAt
  have hne : ∀ᶠ y in 𝓝 x₀, (aeval (R.lift x₀ y) Hf : ℂ) ≠ 0 := hHc.eventually_ne hx₀
  have hU : ∀ᶠ y in 𝓝 x₀, y ∈ R.U x₀ := (R.isOpen_U x₀).mem_nhds (R.mem_U x₀)
  have hS : ∀ᶠ y in 𝓝 x₀, y ∈ (R.A.chart j).source := (R.A.chart j).open_source.mem_nhds hj
  have hπc : ContinuousAt π x₀ := hπ.1.continuousAt
  have hπU : ∀ᶠ y in 𝓝 x₀, π y ∈ S.L.U (π x₀) :=
    hπc.eventually_mem ((S.L.isOpen_U _).mem_nhds (S.L.mem_U _))
  have hπk : ∀ᶠ y in 𝓝 x₀, π y ∈ (S.A.chart k).source :=
    hπc.eventually_mem ((S.A.chart k).open_source.mem_nhds hk)
  have tend : Tendsto (R.A.chart j).symm (𝓝 (R.A.chart j x₀)) (𝓝 x₀) := by
    have h := (R.A.chart j).continuousAt_symm ((R.A.chart j).map_source hj)
    rwa [ContinuousAt, hz₀] at h

  let f : (Fin e → ℂ) → ℂ := fun z =>
    (aeval (R.lift x₀ ((R.A.chart j).symm z)) G : ℂ) / aeval (R.lift x₀ ((R.A.chart j).symm z)) Hf
  let g : (Fin e → ℂ) → ℂ := fun z => S.s (π x₀) (π ((R.A.chart j).symm z))
  have hf : AnalyticAt ℂ f (R.A.chart j x₀) := hGa.div hHa (by simpa only [hz₀] using hx₀)
  have hg : AnalyticAt ℂ g (R.A.chart j x₀) := by
    have h1 : AnalyticAt ℂ ((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀) :=
      hπ.2 j k _ ⟨(R.A.chart j).map_source hj, by
        show π ((R.A.chart j).symm (R.A.chart j x₀)) ∈ (S.A.chart k).source
        rw [hz₀]; exact hk⟩
    have h2 : AnalyticAt ℂ (S.s (π x₀) ∘ (S.A.chart k).symm)
        (((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀)) := by
      have e1 : ((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀) = S.A.chart k (π x₀) := by
        simp only [Function.comp_apply, hz₀]
      rw [e1]
      exact S.sec.1 (π x₀) k _ ⟨(S.A.chart k).map_source hk, by
        show (S.A.chart k).symm (S.A.chart k (π x₀)) ∈ S.L.U (π x₀)
        rw [hd₀]; exact S.L.mem_U _⟩
    refine (h2.comp h1).congr ?_
    filter_upwards [tend.eventually hπk] with z hz
    simp only [Function.comp_apply, g, (S.A.chart k).left_inv hz]

  have hzero : ∀ᶠ z in 𝓝 (R.A.chart j x₀), g z = 0 → f z = 0 := by
    filter_upwards [tend.eventually hU, tend.eventually hπU, tend.eventually hne] with z h1 h2 h3 h0
    obtain ⟨t, ht, hlt⟩ := R.compat x₀ _ _ ⟨h1, R.mem_U ((R.A.chart j).symm z)⟩
    have hs := section_zero S.sec (x := π x₀) (x' := π ((R.A.chart j).symm z))
      ⟨h2, S.L.mem_U _⟩ h0
    have hHy : (aeval (R.lift ((R.A.chart j).symm z) ((R.A.chart j).symm z)) Hf : ℂ) ≠ 0 := by
      intro h00
      apply h3
      rw [hlt, aeval_scale hH, h00, mul_zero]
    have hGy : (aeval (R.lift ((R.A.chart j).symm z) ((R.A.chart j).symm z)) G : ℂ) = 0 := by
      by_contra hG0
      exact hyp _ hG0 hHy hs
    show (aeval (R.lift x₀ ((R.A.chart j).symm z)) G : ℂ) / _ = 0
    rw [hlt, aeval_scale hG, hGy, mul_zero, zero_div]
  obtain ⟨N, C₀, hN, hloj⟩ := GlobalTheory.T.lojasiewicz_inequality_analytic e f g _ hf hg hzero
  have hloj' : ∀ᶠ y in 𝓝 x₀, ‖f (R.A.chart j y)‖ ^ N ≤ C₀ * ‖g (R.A.chart j y)‖ :=
    ((R.A.chart j).continuousAt hj).eventually hloj

  have hφc : ContinuousAt (S.L.φ (π x₀)) (π x₀) :=
    continuousAt_of_chart (S.A.chart k) hk
      (((S.potL.1 (π x₀) k).continuousOn).continuousAt
        (((S.A.chart k).isOpen_inter_preimage_symm (S.L.isOpen_U _)).mem_nhds
          ⟨(S.A.chart k).map_source hk, by
            show (S.A.chart k).symm (S.A.chart k (π x₀)) ∈ S.L.U (π x₀)
            rw [hd₀]; exact S.L.mem_U _⟩))
  have hφb := eventually_abs_le (u := fun y => S.L.φ (π x₀) (π y)) (ContinuousAt.comp (g := S.L.φ (π x₀)) hφc hπc)
  have hℓ : ContinuousAt (fun y => R.lift x₀ y) x₀ :=
    continuousAt_pi.2 fun p => continuousAt_of_chart (R.A.chart j) hj (hcoord p).continuousAt
  have hmem : R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := (R.mem x₀ x₀ (R.mem_U x₀)).1
  have hhc : ContinuousAt Eh.h (R.lift x₀ x₀) :=
    (ContDiffOn.continuousOn hEh).continuousAt (isOpen_multicone.mem_nhds hmem)
  have hlogc : ContinuousAt (fun y => Real.log (Eh.h (R.lift x₀ y))) x₀ :=
    ContinuousAt.log (ContinuousAt.comp (g := Eh.h) hhc hℓ) (Eh.pos _ hmem).ne'
  have hhb := eventually_abs_le hlogc
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.1
    (hU.and (hS.and (hπU.and (hne.and (hloj'.and (hφb.and hhb))))))
  refine ⟨V, N, (Real.log (max C₀ 1) + Real.exp 1 / 2 + (|S.L.φ (π x₀) (π x₀)| + 1)) / (N : ℝ) +
    (|Real.log (Eh.h (R.lift x₀ x₀))| + 1), hVo, hxV, hN, fun y hy => ?_⟩
  obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := hV y hy
  obtain ⟨t, ht, hlt⟩ := R.compat x₀ y y ⟨y1, R.mem_U y⟩
  have hw : ∀ k, ∃ i, R.lift y y ⟨k, i⟩ ≠ 0 := (R.mem y y (R.mem_U y)).1
  have hHy : (aeval (R.lift y y) Hf : ℂ) ≠ 0 := by
    intro h00
    apply y4
    rw [hlt, aeval_scale hH, h00, mul_zero]
  refine ⟨hHy, fun hop hGy => ?_⟩
  have hs : S.s (π y) (π y) ≠ 0 := hop
  have hgne : S.s (π x₀) (π y) ≠ 0 := fun h0 => hs (section_zero S.sec ⟨y3, S.L.mem_U _⟩ h0)
  have hGl : (aeval (R.lift x₀ y) G : ℂ) ≠ 0 := by
    rw [hlt, aeval_scale hG]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)) hGy
  have hfy : f (R.A.chart j y) = (aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf := by
    simp only [f, (R.A.chart j).left_inv y2]
  have hgy : g (R.A.chart j y) = S.s (π x₀) (π y) := by
    simp only [g, (R.A.chart j).left_inv y2]
  rw [hfy, hgy] at y5
  have hfne : (aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf ≠ 0 := div_ne_zero hGl y4
  have key := log_ratio_scale Eh hG hH hdeg t ht (R.lift y y) hw hGy hHy
  rw [← hlt] at key
  rw [key, rW, logNormSec_eq S.sec y3 hgne]
  have hloglog : (N : ℝ) * Real.log ‖(aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf‖ ≤
      Real.log (max C₀ 1) + Real.log ‖S.s (π x₀) (π y)‖ := by
    have hC : 0 < max C₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hgp : 0 < ‖S.s (π x₀) (π y)‖ := norm_pos_iff.2 hgne
    have hle : ‖(aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf‖ ^ N ≤
        max C₀ 1 * ‖S.s (π x₀) (π y)‖ :=
      y5.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgp.le)
    have := Real.log_le_log (pow_pos (norm_pos_iff.2 hfne) N) hle
    rwa [Real.log_pow, Real.log_mul hC.ne' hgp.ne'] at this
  exact decay_arith hN hloglog y7 y6

end GlobalTheory.CompanionTheory.Ar.Small.Decay
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantOneRowExpansion
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem pderiv_fin_prod {σ : Type*} (k : σ) : ∀ (d : ℕ) (f : Fin (d + 1) → MvPolynomial σ ℝ),
    pderiv k (∏ r, f r) = ∑ r, pderiv k (f r) * ∏ s, f (r.succAbove s) := by
  intro d
  induction d with
  | zero => intro f; simp
  | succ d ih =>
    intro f
    rw [Fin.prod_univ_succ, Derivation.leibniz, ih (fun i => f i.succ),
      Fin.sum_univ_succ (fun r => pderiv k (f r) * ∏ s, f (r.succAbove s))]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · simp only [Fin.succAbove_zero]
      ring
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [Fin.prod_univ_succ (fun s => f (r.succ.succAbove s))]
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
      ring

theorem pderiv_row_weight (c v : ℝ) : pderiv (some 0 : Option (Fin 2)) (rowW ![c, 0] v) = C c := by
  simp [rowW, pderiv_X, Pi.single_apply]

theorem eval_row_weight (n : Fin 3 → ℝ) (c v : ℝ) :
    evalW n n (rowW ![c, 0] v) = lin4 (fun i => c * n i) + C v * X none := by
  have h : lin4 (fun i => c * n i) = C c * lin4 n := by
    simp only [lin4, lin3, map_sum, map_mul, rename_C, rename_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]
  simp [rowW, evalW, aeval_def, algebraMap_eq]

theorem extract_one : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (c : Fin (d + 1) → ℝ) (v : Fin (d + 1) → ℝ) (n : Fin 3 → ℝ) (e : ℂ),
      ((d + 1).factorial : ℂ) * mdisc (fun r => blk ((c r : ℂ) * e)
        ((∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H)) =
      e * L (evalW n n (pderiv (some 0) (∏ r, rowW ![c r, 0] (v r)))) := by
  intro d T H L hL c v n e
  have h1 := ((GlobalTheory.T.mixed_discriminant_cofactor_expansion d).1 (fun r => (c r : ℂ) * e)
    (fun r => (∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))
  refine h1.trans ?_
  rw [pderiv_fin_prod, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h3 := hL (fun s i => c (r.succAbove s) * n i) (fun s => v (r.succAbove s))
  rw [h3, pderiv_row_weight, map_mul (evalW n n), map_prod (evalW n n)]
  simp only [eval_row_weight]
  have h4 : evalW n n (C (c r)) = C (c r) := by simp [evalW, aeval_def, algebraMap_eq]
  rw [h4, C_mul', map_smul, Complex.real_smul]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantTwoRowExpansion
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem derivation_prod_erase_xt {σ ι : Type*} [DecidableEq ι]
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) (a : ι → MvPolynomial σ ℝ) (S : Finset ι) :
    D (∏ i ∈ S, a i) = ∑ i ∈ S, D (a i) * ∏ j ∈ S.erase i, a j := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, D.leibniz, ih, Finset.sum_insert hi, Finset.erase_insert hi,
      smul_eq_mul, smul_eq_mul, add_comm, mul_comm (∏ j ∈ S, a j), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Finset.erase_insert_of_ne hij,
      Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h))]
    ring

theorem derivation_prod_succAbove_xt {σ : Type*} {n : ℕ}
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) (a : Fin (n + 1) → MvPolynomial σ ℝ) :
    D (∏ r, a r) = ∑ r, D (a r) * ∏ s, a (r.succAbove s) := by
  rw [derivation_prod_erase_xt]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  rw [Fin.univ_succAbove _ r, Finset.cons_eq_insert, Finset.erase_insert (by simp), Finset.prod_map]
  rfl

theorem pderiv_rowW_zero_xt (u : Fin 2 → ℝ) (v : ℝ) : pderiv (some 0) (rowW u v) = C (u 0) := by
  simp [rowW, pderiv_X, Pi.single_apply, pderiv_C, Derivation.leibniz]

theorem pderiv_rowW_one_xt (u : Fin 2 → ℝ) (v : ℝ) : pderiv (some 1) (rowW u v) = C (u 1) := by
  simp [rowW, pderiv_X, Pi.single_apply, pderiv_C, Derivation.leibniz]

theorem pderiv_C_mul_xt {σ : Type*} [DecidableEq σ] (j : σ) (a : ℝ) (p : MvPolynomial σ ℝ) :
    pderiv j (C a * p) = C a * pderiv j p := by
  simp [Derivation.leibniz, pderiv_C]

theorem linear_form_linear_combination (a b : ℝ) (n m : Fin 3 → ℝ) :
    lin4 (fun i => a * n i + b * m i) = C a * lin4 n + C b * lin4 m := by
  simp only [lin4, lin3, map_sum, map_mul, rename_X, rename_C, Finset.mul_sum,
    ← Finset.sum_add_distrib, map_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem evalW_C_xt (n₀ n₁ : Fin 3 → ℝ) (a : ℝ) : evalW n₀ n₁ (C a) = C a := by
  simp [evalW]

theorem evalW_rowW_xt (n₀ n₁ : Fin 3 → ℝ) (u : Fin 2 → ℝ) (v : ℝ) :
    evalW n₀ n₁ (rowW u v) = lin4 (fun i => u 0 * n₀ i + u 1 * n₁ i) + C v * X none := by
  rw [linear_form_linear_combination]
  simp [evalW, rowW]

theorem mdisc_extract_two : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (u : Fin (d + 2) → Fin 2 → ℝ) (v : Fin (d + 2) → ℝ) (n₀ n₁ : Fin 3 → ℝ) (e₀ e₁ : ℂ),
      ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁)
        ((∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))) =
      e₀ * e₁ * L (evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))))) := by
  intro d T H L hL u v n₀ n₁ e₀ e₁
  have hLC : ∀ (a : ℝ) (p : MvPolynomial (Option (Fin 3)) ℝ), L (C a * p) = (a : ℂ) * L p := by
    intro a p
    rw [← smul_eq_C_mul, map_smul, Complex.real_smul]
  let M : Fin (d + 2) → Matrix (Fin d) (Fin d) ℂ := fun r =>
    (∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H
  have h1 : ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁) (M r))) =
      ∑ r, ((u r 0 : ℂ) * e₀) * (((d + 1).factorial : ℂ) *
        mdisc fun s => blk ((u (r.succAbove s) 1 : ℂ) * e₁) (M (r.succAbove s))) :=
    (GlobalTheory.T.mixed_discriminant_cofactor_expansion (d + 1)).1 (fun r => (u r 0 : ℂ) * e₀) (fun r => blk ((u r 1 : ℂ) * e₁) (M r))
  have h2 : ∀ r : Fin (d + 2), ((d + 1).factorial : ℂ) *
      mdisc (fun s => blk ((u (r.succAbove s) 1 : ℂ) * e₁) (M (r.succAbove s))) =
      ∑ s, ((u (r.succAbove s) 1 : ℂ) * e₁) * ((d.factorial : ℂ) *
        mdisc fun t => M (r.succAbove (s.succAbove t))) := fun r =>
    (GlobalTheory.T.mixed_discriminant_cofactor_expansion d).1 (fun s => (u (r.succAbove s) 1 : ℂ) * e₁) (fun s => M (r.succAbove s))
  have h3 : ∀ (r : Fin (d + 2)) (s : Fin (d + 1)),
      (d.factorial : ℂ) * mdisc (fun t => M (r.succAbove (s.succAbove t))) =
      L (∏ t, evalW n₀ n₁ (rowW (u (r.succAbove (s.succAbove t))) (v (r.succAbove (s.succAbove t))))) := by
    intro r s
    simp only [evalW_rowW_xt]
    exact hL (fun t i => u (r.succAbove (s.succAbove t)) 0 * n₀ i + u (r.succAbove (s.succAbove t)) 1 * n₁ i)
      (fun t => v (r.succAbove (s.succAbove t)))
  have h4 : pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))) =
      ∑ r, C (u r 0) * ∑ s, C (u (r.succAbove s) 1) *
        ∏ t, rowW (u (r.succAbove (s.succAbove t))) (v (r.succAbove (s.succAbove t))) := by
    rw [derivation_prod_succAbove_xt]
    simp only [pderiv_rowW_zero_xt, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pderiv_C_mul_xt, derivation_prod_succAbove_xt]
    simp only [pderiv_rowW_one_xt]
  show ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁) (M r))) = _
  rw [h1, h4]
  simp only [h2, h3, map_sum, map_mul, map_prod, evalW_C_xt, hLC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NearTriangularOfStepConditions
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepShape

theorem upper_of_steps : ∀ (N j : ℕ) (a b ca cb : Fin N) (C : Matrix (Fin N) (Fin N) ℂ), j ≤ N → (b : ℕ) = a + 1 →
    ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j C →
    (∀ i, IsProperStep N j i → i ≠ a → ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → C r c = 0) →
    ∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C r c = 0 := by
  intro N j a b ca cb C hj hb hcase hca hcb hbd hv r c hcr hne
  have hr := r.2
  have hc := c.2
  have ha := a.2
  have hb' := b.2
  have hcb' := cb.2
  have hlt : (c : ℕ) < r := hcr
  have hba : b ≠ a := by
    intro h
    rw [h] at hb
    omega
  unfold lastCol at hca
  by_cases hs : ((r : ℕ) < N - j ↔ (c : ℕ) < N - j)
  swap
  · exact hbd r c hs
  by_cases hW : N - j ≤ (c : ℕ)
  · obtain ⟨i, hi⟩ : ∃ i : Fin N, (i : ℕ) = c - (N - j) := ⟨⟨(c : ℕ) - (N - j), by omega⟩, rfl⟩
    by_cases hia : i = a
    · have hai : (a : ℕ) = c - (N - j) := by rw [← hia]; exact hi
      rw [if_pos (by omega)] at hca
      have hcc : c = ca := Fin.ext (by omega)
      have hrcb : (r : ℕ) ≠ cb := fun h => hne ⟨Fin.ext h, hcc⟩
      refine hv b ⟨by omega, by omega⟩ hba r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
    · refine hv i ⟨by omega, by omega⟩ hia r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
  · obtain ⟨i, hi⟩ : ∃ i : Fin N, (i : ℕ) = j + c := ⟨⟨j + (c : ℕ), by omega⟩, rfl⟩
    by_cases hia : i = a
    · have hai : (a : ℕ) = j + c := by rw [← hia]; exact hi
      rw [if_neg (by omega)] at hca
      have hcc : c = ca := Fin.ext (by omega)
      have hrcb : (r : ℕ) ≠ cb := fun h => hne ⟨Fin.ext h, hcc⟩
      refine hv b ⟨by omega, by omega⟩ hba r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega
    · refine hv i ⟨by omega, by omega⟩ hia r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega

end GlobalTheory.CompanionTheory.Ar.PB.StepShape
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SlopeBoundComparableMetric
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem basis_slope_degree_bound : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ) (b : Module.Basis (Fin r) (𝓞 K) E.carrier) (C : ℝ), 1 ≤ C → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ≤ C * ∑ a, ‖w a‖ ^ 2) → E.slopeMax ≤ ((Real.log C / 2 : ℝ) : EReal) ∧ |E.normDegree ⊤| ≤ r / 2 * Real.log C :=
  @CoverDenseAlt.slopeMax_le_of_comparable_metric

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedFlagDegreeLowerBoundStatement
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_flag_degree_lower_bound : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ) (Λ μ C : ℝ), (∀ τ, Antitone (lam τ)) → (∀ τ i, |lam τ i| ≤ Λ) → 0 ≤ μ → E.slopeMax ≤ (μ : EReal) → (∀ τ, |A.flatDeg τ| ≤ C) → -(Fintype.card Ψ * (2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C)) ≤ A.lamDeg lam := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower | exact GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower | (intros; apply GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower <;> assumption)
end

