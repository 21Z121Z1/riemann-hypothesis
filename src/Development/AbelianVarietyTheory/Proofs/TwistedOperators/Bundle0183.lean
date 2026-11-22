import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoefficientSpaceDualDiscreteSeriesModelPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffOfContinuousQuasiMultiplicativeSmoothDef
section
open MeasureTheory

open Metric Set Filter Topology Convolution

namespace GlobalTheory.FuncEqSmooth

theorem contDiff_of_func_eq (c : ℝ → ℂ) (E : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)) (hc : Continuous c)
    (hc0 : c 0 ≠ 0) (hU : IsOpen U) (hUs : ∀ s, (s, 0) ∈ U)
    (hE : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U)
    (hfe : ∀ p ∈ U, c (p.1 + p.2) = c p.1 * c p.2 * E p.1 p.2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
  have h00 : ((0:ℝ), (0:ℝ)) ∈ U := hUs 0
  have hw0 : c 0 * E 0 0 = 1 := by
    have h1 := hfe (0,0) h00
    simp only [add_zero] at h1
    have h2 : c 0 * (c 0 * E 0 0) = c 0 * 1 := by rw [mul_one, ← mul_assoc]; exact h1.symm
    exact mul_left_cancel₀ hc0 h2
  have hEcont : ContinuousAt (fun p : ℝ × ℝ => E p.1 p.2) (0,0) :=
    hE.continuousOn.continuousAt (hU.mem_nhds h00)
  have hwcont : ContinuousAt (fun v : ℝ => c v * E 0 v) 0 := by
    have h1 : ContinuousAt (fun v : ℝ => E (0:ℝ) v) 0 :=
      hEcont.comp (f := fun v : ℝ => ((0:ℝ), v)) (by fun_prop)
    exact hc.continuousAt.mul h1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ h00
  obtain ⟨δ, hδ, hwδ⟩ := Metric.continuousAt_iff.1 hwcont (1/2) (by norm_num)
  set r := min ε δ with hr
  have hr0 : 0 < r := lt_min hε hδ
  have hbox : ∀ a b : ℝ, |a| < r → |b| < r → (a, b) ∈ U := by
    intro a b ha hb
    apply hball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    simp only [Real.dist_eq, sub_zero]
    exact ⟨lt_of_lt_of_le ha (min_le_left _ _), lt_of_lt_of_le hb (min_le_left _ _)⟩

  let ψ : ContDiffBump (0:ℝ) := ⟨r/4, r/2, by positivity, by linarith⟩
  set φ : ℝ → ℝ := ψ.normed volume with hφdef
  have hφ0 : ∀ x : ℝ, r/2 ≤ |x| → φ x = 0 := by
    intro x hx
    rw [← Function.notMem_support, hφdef, ψ.support_normed_eq, mem_ball, Real.dist_eq, sub_zero]
    show ¬ |x| < r/2
    linarith
  have hφs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := ψ.contDiff_normed
  let φr : ℝ → ℂ := fun y => ((φ y : ℝ) : ℂ)
  have hφr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φr := Complex.ofRealCLM.contDiff.comp hφs
  have hφr0 : ∀ x : ℝ, r/2 ≤ |x| → φr x = 0 := by
    intro x hx; simp [φr, hφ0 x hx]

  let A : ℝ → ℂ := c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (fun y => φr (-y))
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    have hcs : HasCompactSupport (fun y => φr (-y)) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) (r/2)) (fun y hy => ?_)
      rw [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hy
      exact hφr0 _ (by rw [abs_neg]; exact hy.le)
    exact hcs.contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℂ) hc.locallyIntegrable
      (hφr.comp contDiff_neg)

  let G : ℝ → ℝ → ℂ := fun t y => φr (-y) * E t (-y)
  let h : ℝ → ℂ := fun t => (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G t) 0
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry G) (ball (0:ℝ) r ×ˢ univ) := by
    intro q hq
    apply ContDiffAt.contDiffWithinAt
    have hq1 : |q.1| < r := by
      have := hq.1; rw [mem_ball, Real.dist_eq, sub_zero] at this; exact this
    by_cases hq2 : |q.2| < r
    · have hmem : (q.1, -q.2) ∈ U := hbox _ _ hq1 (by rw [abs_neg]; exact hq2)
      have hEat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) (q.1, -q.2) :=
        hE.contDiffAt (hU.mem_nhds hmem)
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => E q.1 (-q.2)) q :=
        hEat.comp (f := fun q : ℝ × ℝ => (q.1, -q.2)) q (by fun_prop)
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => φr (-q.2)) q :=
        (hφr.comp (contDiff_snd.neg)).contDiffAt
      exact h1.mul h2
    · push_neg at hq2
      have hev : ∀ᶠ q' in 𝓝 q, r/2 < |q'.2| :=
        continuousAt_const.eventually_lt (by fun_prop) (by linarith)
      refine contDiffAt_const (c := (0:ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with q' hq'
      show φr (-q'.2) * E q'.1 (-q'.2) = 0
      rw [hφr0 _ (by rw [abs_neg]; exact hq'.le), zero_mul]
  have hparam := contDiffOn_convolution_right_with_param (μ := volume) (n := ⊤)
    (ContinuousLinearMap.mul ℝ ℂ) (f := c) (g := G) (s := ball (0:ℝ) r) (k := closedBall (0:ℝ) (r/2))
    isOpen_ball (isCompact_closedBall _ _)
    (fun p x _ hx => by
      rw [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
      show φr (-x) * E p (-x) = 0
      rw [hφr0 _ (by rw [abs_neg]; exact hx.le), zero_mul])
    hc.locallyIntegrable hG
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (ball (0:ℝ) r) := by
    have hemb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t, (0:ℝ))) (ball (0:ℝ) r) :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    have h3 := ContDiffOn.comp (g := fun q : ℝ × ℝ => (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G q.1) q.2)
      hparam hemb (fun t ht => ⟨ht, mem_univ _⟩)
    exact h3
  have hrδ : r ≤ δ := min_le_right _ _

  let cl : ℝ → ℝ := fun v => max (-(r/2)) (min v (r/2))
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hcl : ∀ v, cl v ∈ Icc (-(r/2)) (r/2) := fun v =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hclid : ∀ v, |v| ≤ r/2 → cl v = v := by
    intro v hv
    obtain ⟨h1, h2⟩ := abs_le.1 hv
    show max (-(r/2)) (min v (r/2)) = v
    rw [min_eq_left h2, max_eq_right h1]
  have hE0on : ContinuousOn (fun v : ℝ => E 0 v) (Icc (-(r/2)) (r/2)) := by
    have h3 := hE.continuousOn.comp (f := fun v : ℝ => ((0:ℝ), v))
      (by fun_prop : Continuous fun v : ℝ => ((0:ℝ), v)).continuousOn
      (fun v (hv : v ∈ Icc (-(r/2)) (r/2)) => hbox 0 v (by simp [hr0]) (abs_lt.2 ⟨by linarith [hv.1], by linarith [hv.2]⟩))
    exact h3
  let Ehat : ℝ → ℂ := fun v => E 0 (cl v)
  have hEhat : Continuous Ehat := hE0on.comp_continuous hclc hcl
  let g : ℝ → ℂ := fun x => c (-x) * Ehat (-x)
  have hgc : Continuous g := (hc.comp continuous_neg).mul (hEhat.comp continuous_neg)
  have hg0 : g 0 = 1 := by
    show c (-0) * E 0 (cl (-0)) = 1
    rw [neg_zero, hclid 0 (by simp; positivity), hw0]
  have hdist := ψ.dist_normed_convolution_le (μ := volume) (x₀ := 0) (ε := 1/2) hgc.aestronglyMeasurable
    (fun x hx => by
      have hx' : |x| < r/2 := by
        have h6 := hx; rw [mem_ball, Real.dist_eq, sub_zero] at h6; exact h6
      have e1 : g x = c (-x) * E 0 (-x) := by
        show c (-x) * E 0 (cl (-x)) = _
        rw [hclid _ (by rw [abs_neg]; exact hx'.le)]
      rw [e1, hg0, ← hw0]
      exact (hwδ (by rw [Real.dist_eq, sub_zero, abs_neg]; linarith)).le)
  have hconv : (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 0 = h 0 := by
    show _ = (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G 0) 0
    rw [convolution_def, convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.mul_apply', zero_sub, neg_neg, g, G, Ehat, φr]
    by_cases hu : |u| < r/2
    · rw [hclid u hu.le, Complex.real_smul]; ring
    · have hz : ψ.normed volume u = 0 := hφ0 u (not_lt.1 hu)
      have hz' : φ u = 0 := hφ0 u (not_lt.1 hu)
      rw [hz, hz']; simp
  have h0ne : h 0 ≠ 0 := by
    intro h0
    rw [hconv, hg0, h0] at hdist
    norm_num at hdist

  have hAh : ∀ t, |t| < r → A t = c t * h t := by
    intro t ht
    show (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (fun y => φr (-y))) t
      = c t * (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G t) 0
    rw [convolution_def, convolution_def, ← integral_const_mul,
      ← integral_add_right_eq_self (μ := volume)
        (fun u => (ContinuousLinearMap.mul ℝ ℂ) (c u) (φr (-(t - u)))) t]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [ContinuousLinearMap.mul_apply', G, zero_sub, neg_neg]
    have e : -(t - (s + t)) = s := by ring
    rw [e]
    by_cases hs : |s| < r/2
    · have h7 := hfe (t, s) (hbox t s ht (by linarith))
      simp only at h7
      rw [add_comm s t, h7]; ring
    · rw [hφr0 s (not_lt.1 hs)]; ring

  have hcont_h : ContinuousOn h (ball (0:ℝ) r) := hh.continuousOn
  set V := ball (0:ℝ) r ∩ h ⁻¹' {0}ᶜ with hV
  have hVo : IsOpen V := hcont_h.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have h0V : (0:ℝ) ∈ V := ⟨mem_ball_self hr0, h0ne⟩
  have hcV : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c V := by
    have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => A t * (h t)⁻¹) V :=
      hA.contDiffOn.mul ((hh.mono inter_subset_left).inv (fun t ht => ht.2))
    refine h4.congr (fun t ht => ?_)
    have ht1 : |t| < r := by
      have h8 := ht.1; rw [mem_ball, Real.dist_eq, sub_zero] at h8; exact h8
    have hne : h t ≠ 0 := ht.2
    show c t = A t * (h t)⁻¹
    rw [hAh t ht1, mul_inv_cancel_right₀ hne]

  rw [contDiff_iff_contDiffAt]
  intro t₀
  set W := (fun t : ℝ => (t₀, t)) ⁻¹' U ∩ V with hW
  have hWo : IsOpen W := (hU.preimage (by fun_prop)).inter hVo
  have h0W : (0:ℝ) ∈ W := ⟨hUs t₀, h0V⟩
  have hFW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) W := by
    have hE' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => E t₀ t) W :=
      hE.comp (f := fun t : ℝ => (t₀, t)) (contDiff_const.prodMk contDiff_id).contDiffOn (fun t ht => ht.1)
    have h5 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c t₀ * c t * E t₀ t) W :=
      (contDiffOn_const.mul (hcV.mono inter_subset_right)).mul hE'
    refine h5.congr (fun t ht => ?_)
    exact hfe (t₀, t) ht.1
  have hF0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) 0 := hFW.contDiffAt (hWo.mem_nhds h0W)
  have hsub : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => x - t₀) t₀ := (contDiff_id.sub contDiff_const).contDiffAt
  have hF0' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) ((fun x : ℝ => x - t₀) t₀) := by
    simpa using hF0
  have h9 := ContDiffAt.comp (f := fun x : ℝ => x - t₀) t₀ hF0' hsub
  convert h9 using 1
  funext x
  simp

end GlobalTheory.FuncEqSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open scoped ENNReal

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.Ker.HeisDeriv

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}
  {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} {f : WO V W → ℂ}

theorem dRho_dir_linear (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau) :
    (∀ z z' : Matrix (Fin W.rank) (Fin V.rank) ℂ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (z + z') f =
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f + Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z' f) ∧
    ∀ (t : ℝ) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ ((t : ℂ) • z) f =
      (t : ℂ) • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have hsm := GlobalTheory.OrientedHeis.theta_sm hσ hf
  have key : ∀ y : Matrix (Fin W.rank) (Fin V.rank) ℂ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f =
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W)
        (GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1)) f := fun y => by
    rw [GlobalTheory.OrientedHeis.dRho_eq_dLine, GlobalTheory.OrientedHeis.dLine_eq_hD hσ hψ (GlobalTheory.OrientedHeis.isRealDir_lineAt hθ τ y)]
  have hlin_add : ∀ u u' : GlobalTheory.FockCompare.RW W V,
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) (u + u') f =
        GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) u f +
        GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) u' f := by
    intro u u'
    funext w
    simp only [Pi.add_apply, GlobalTheory.FockCompare.hD_eq_fderiv _ _ _ f hsm, map_add]
    push_cast
    ring
  have hlin_smul : ∀ (t : ℝ) (u : GlobalTheory.FockCompare.RW W V),
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) (t • u) f =
        (t : ℂ) • GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V)
          (GlobalTheory.OrientedHeis.omO V W) u f := by
    intro t u
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.FockCompare.hD_eq_fderiv _ _ _ f hsm, map_smul, Complex.real_smul]
    push_cast
    ring
  have hadd_u : ∀ y y' : Matrix (Fin W.rank) (Fin V.rank) ℂ, GlobalTheory.FockCompare.piW θ W V (lineAt θ τ (y + y') 1) =
      GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1) + GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y' 1) := by
    intro y y'
    rw [GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ]
    exact Pi.single_add (f := fun _ => Matrix (Fin W.rank) (Fin V.rank) ℂ) τ y y'
  have hsmul_u : ∀ (t : ℝ) (y : Matrix (Fin W.rank) (Fin V.rank) ℂ),
      GlobalTheory.FockCompare.piW θ W V (lineAt θ τ ((t : ℂ) • y) 1) = t • GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1) := by
    intro t y
    rw [GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ]
    have e : ((t : ℂ) • y) = t • y := by
      ext a b
      simp [Complex.real_smul]
    rw [e]
    exact Pi.single_smul' τ t y
  refine ⟨fun y y' => ?_, fun t y => ?_⟩
  · rw [key, key, key, hadd_u, hlin_add]
  · rw [key, key, hsmul_u, hlin_smul]

theorem matrix_eq_sum_re_im {m n : ℕ} (z : Matrix (Fin m) (Fin n) ℂ) :
    z = ∑ i, ∑ j, ((((z i j).re : ℝ) : ℂ) • Matrix.single i j (1 : ℂ) +
      (((z i j).im : ℝ) : ℂ) • Matrix.single i j Complex.I) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single z]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul, smul_eq_mul, mul_one,
    Complex.re_add_im]

theorem dRho_eq_sum_heisDer (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f =
      ∑ i, ∑ j, ((((z i j).re : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, false) f +
        (((z i j).im : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, true) f) := by
  obtain ⟨hadd, hsm⟩ := dRho_dir_linear hψ hθ hf τ
  let L : Matrix (Fin W.rank) (Fin V.rank) ℂ →+ (WO V W → ℂ) :=
    AddMonoidHom.mk' (fun y => Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f) hadd
  have hL : ∀ y, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f = L y := fun _ => rfl
  rw [hL]
  conv_lhs => rw [matrix_eq_sum_re_im z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, ← hL, ← hL, hsm, hsm]
  simp [heisDer]

theorem theta_finsetSum {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ} (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) :
    IsThetaFunO ψ V W (∑ i ∈ s, g i) := by
  classical
  revert hg
  refine Finset.induction_on s (fun _ => by rw [Finset.sum_empty]; exact theta_zero) ?_
  intro a t ha ih hg
  rw [Finset.sum_insert ha]
  exact theta_add (hg a (Finset.mem_insert_self a t)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem sobO_sum_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ}
    (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (∑ i ∈ s, g i) ≤ ∑ i ∈ s, sobO ψ θ μ 𝓕 d (g i) := by
  classical
  revert hg
  refine Finset.induction_on s (fun _ => ?_) ?_
  · have h0 := sobO_smul (ψ := ψ) (θ := θ) (μ := μ) (𝓕 := 𝓕) (f := (0 : WO V W → ℂ)) d 0
    simp only [smul_zero, enorm_zero, zero_mul] at h0
    simp [h0]
  · intro a t ha ih hg
    have ha' : IsThetaFunO ψ V W (g a) := hg a (Finset.mem_insert_self a t)
    have ht : ∀ i ∈ t, IsThetaFunO ψ V W (g i) := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sobO_add_le hψ hθ ha' (theta_finsetSum t ht) d).trans (add_le_add le_rfl (ih ht))

theorem sobO_dRho_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) ≤
      ENNReal.ofReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)) * sobO ψ θ μ 𝓕 (d + 1) f := by
  classical
  have hD : ∀ a, IsThetaFunO ψ V W (heisDer ψ θ a f) := fun a => by
    simpa [wordAct] using theta_word hψ hθ [a] hf
  have hT : ∀ i j, IsThetaFunO ψ V W ((((z i j).re : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, false) f +
      (((z i j).im : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, true) f) := fun i j =>
    theta_add (theta_smul _ (hD _)) (theta_smul _ (hD _))
  have hre : ∀ r : ℝ, ‖(r : ℂ)‖ₑ = ENNReal.ofReal |r| := fun r => by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
  rw [dRho_eq_sum_heisDer hψ hθ hf τ z]
  refine (sobO_sum_le hψ hθ Finset.univ (fun i _ => theta_finsetSum Finset.univ fun j _ => hT i j) d).trans ?_
  calc _ ≤ ∑ i, ∑ j, (ENNReal.ofReal |(z i j).re| + ENNReal.ofReal |(z i j).im|) *
        sobO ψ θ μ 𝓕 (d + 1) f := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (sobO_sum_le hψ hθ Finset.univ (fun j _ => hT i j) d).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (sobO_add_le hψ hθ (theta_smul _ (hD _)) (theta_smul _ (hD _)) d).trans ?_
        rw [sobO_smul, sobO_smul, hre, hre, add_mul]
        gcongr <;> exact sobO_heisDer_le d _
    _ = _ := by
        simp_rw [← Finset.sum_mul]
        congr 1
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
        exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).symm

end GlobalTheory.Size

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigenOfLocalComponentsFiniteAdelicPair
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceProduct

theorem mix_orth {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {e f : A} (h : e * f = 0)
    (a : Matrix n n A) :
    (e • a + (1 - e) • (1 : Matrix n n A)) * (f • a + (1 - f) • (1 : Matrix n n A)) =
      (e + f) • a + (1 - (e + f)) • (1 : Matrix n n A) := by
  have h1 : e * (1 - f) = e := by linear_combination -h
  have h2 : (1 - e) * f = f := by linear_combination -h
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination h
  simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul]
  rw [h, h1, h2, h3, zero_smul, zero_add, add_smul]
  abel

theorem sum_idem {A ι : Type} [CommRing A] (e : ι → A) (h1 : ∀ i, e i * e i = e i)
    (h2 : ∀ i j, i ≠ j → e i * e j = 0) (B : Finset ι) : (∑ i ∈ B, e i) * (∑ i ∈ B, e i) = ∑ i ∈ B, e i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => h2 i j (Ne.symm hj)) (fun hn => absurd hi hn), h1]

theorem exists_components (D : D7) (V : HSp D) (g : GA D V)
    (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F) (hε : ∀ v, IsPlaceIdem D v (ε v)) :
    ∃ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V,
      (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      gs ∅ = 1 ∧ ∀ v B (h : v ∉ B), gs (Finset.cons v B h) = gs {v} * gs B := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hsum : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) = ∑ v ∈ A, algebraMap (AF D.host.F) (AE D) (ε v) :=
    fun A => map_sum _ _ _
  have hid : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) * algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) =
        algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) := by
    intro A
    rw [hsum]
    exact sum_idem (fun v => algebraMap (AF D.host.F) (AE D) (ε v))
      (fun v => GlobalTheory.IdemSupport.place_idem hΦ (hε v))
      (fun v w hvw => GlobalTheory.IdemSupport.place_orth hΦ (hε v) (hε w) hvw) A
  have hc := fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    GlobalTheory.IdemSupport.cA_algebraMap (D := D) (∑ v ∈ A, ε v)
  choose gs hgs using fun A => GlobalTheory.IdemSupport.exists_piece V (hid A) (hc A) g
  refine ⟨gs, hgs, ?_, ?_⟩
  · apply GlobalTheory.IdemSupport.mt_inj V
    rw [hgs, GlobalTheory.IdemSupport.mt_one, Finset.sum_empty, map_zero, zero_smul, sub_zero, one_smul, zero_add]
  · intro v B hvB
    apply GlobalTheory.IdemSupport.mt_inj V
    rw [GlobalTheory.IdemSupport.mt_mul, hgs, hgs, hgs, Finset.sum_cons, Finset.sum_singleton, map_add]
    refine (mix_orth ?_ _).symm
    rw [hsum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun w hw =>
      GlobalTheory.IdemSupport.place_orth hΦ (hε v) (hε w) (fun hvw => hvB (by rw [hvw]; exact hw))

theorem eigen_of_local_components : ∀ (D : D7) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), (∀ w, Continuous fun p : GA D S × GA D T => om p f w) → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) (s : HeightOneSpectrum (𝓞 D.host.F) → ℂ), (∀ v, v ∉ A → s v = 1) → (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (g' : GA D S) (h' : GA D T), Formalism.L2.Theta.mt S g' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt S g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → Formalism.L2.Theta.mt T h' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt T h + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → om (g', h') f = s v • f) → om (g, h) f = (∏ v ∈ A, s v) • f := by
  intro D S T om f hcont g hg h hh A s hs hloc
  choose ε hε using fun v : HeightOneSpectrum (𝓞 D.host.F) => GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  obtain ⟨gs, hgs, hgs0, hgsm⟩ := exists_components D S g ε hε
  obtain ⟨hs', hhs, hhs0, hhsm⟩ := exists_components D T h ε hε
  have key : ∀ B : Finset (HeightOneSpectrum (𝓞 D.host.F)), om (gs B, hs' B) f = (∏ v ∈ B, s v) • f := by
    intro B
    induction B using Finset.cons_induction with
    | empty =>
      rw [hgs0, hhs0, Finset.prod_empty, one_smul]
      show om 1 f = f
      rw [map_one]
      rfl
    | cons v B hvB ih =>
      have hv := hloc v (ε v) (hε v) (gs {v}) (hs' {v}) (by rw [hgs, Finset.sum_singleton])
        (by rw [hhs, Finset.sum_singleton])
      rw [hgsm v B hvB, hhsm v B hvB, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih, map_smul, hv,
        smul_smul, Finset.prod_cons, mul_comm]
  have hpair : Filter.Tendsto (fun B => (gs B, hs' B)) Filter.atTop (nhds (g, h)) :=
    (GlobalTheory.T.tendsto_placeComponents_finiteAdelicUnitary D S g hg ε hε gs hgs).prodMk_nhds (GlobalTheory.T.tendsto_placeComponents_finiteAdelicUnitary D T h hh ε hε hs' hhs)
  funext w
  rw [Pi.smul_apply, smul_eq_mul]
  have ht := ((hcont w).tendsto (g, h)).comp hpair
  refine tendsto_nhds_unique ht (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop A] with B hB
  show _ = om (gs B, hs' B) f w
  rw [key, Pi.smul_apply, smul_eq_mul, Finset.prod_subset hB fun v _ hv => hs v hv]

end GlobalTheory.PlaceProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfFiniteOrderUnipotentReductionLargePrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_finiteOrder_unipotentReduction_largePrime : ∀ (E R k : Type) [Field E] [NumberField E] [CommRing R] [CommRing k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) (p n : ℕ), p.Prime → CharP k p → Module.finrank ℚ E * n + 1 < p → ∀ (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S), IsOfFinOrder u → Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x → IsNilpotent ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) → u = 1 := by
  first | exact @GlobalTheory.UnipRed.eq_one_of_unipotent_reduction | exact GlobalTheory.UnipRed.eq_one_of_unipotent_reduction | (intros; apply GlobalTheory.UnipRed.eq_one_of_unipotent_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoefficientSpaceDualDiscreteSeriesModelPosStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientSpace_dual_discreteSeriesModel_posDef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∃ (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), c.Is ∧ IsDualPair θ M c pr ∧ Function.Surjective pr := by
  first | exact @GlobalTheory.DualCoef.exists_dual_coef | exact GlobalTheory.DualCoef.exists_dual_coef | (intros; apply GlobalTheory.DualCoef.exists_dual_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOneStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_detCharacter_of_irreducible_rank_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c : Type) [Fintype c] [DecidableEq c] [Subsingleton c] (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL c k) V), IsSmooth σ → σ.IsIrreducible → ∃ ψ : kˣ →* ℂˣ, IsSmoothChar ψ ∧ Nonempty (σ.Equiv (detRep c ψ)) := by
  first | exact @GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep | exact GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep | (intros; apply GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwarStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ f : SInf F κ, Rest (evI F) (⇑f) R := by
  first | exact @GlobalTheory.ArchRest.exists_rest_arch | exact GlobalTheory.ArchRest.exists_rest_arch | (intros; apply GlobalTheory.ArchRest.exists_rest_arch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlAdaptedBasisMonotoneSubspaceChainStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gl_adaptedBasis_monotoneSubspaceChain : ∀ {K : Type} [Field K] {n m : ℕ} (Y : Fin (m + 1) → Submodule K (Fin n → K)), Monotone Y → Y 0 = ⊥ → Y (Fin.last m) = ⊤ →
    ∃ (d : Fin m → ℕ) (h : ∑ j, d j = n) (g : GL (Fin n) K), ∀ (j : Fin (m + 1)) (y : Fin n → K),
      y ∈ Y j ↔ ∀ i : Fin n, (j : ℕ) ≤ ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) i : Fin m) : ℕ) →
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) i = 0 := by
  first | exact @GlobalTheory.Flag.exists_gl_adapted_chain | exact GlobalTheory.Flag.exists_gl_adapted_chain | (intros; apply GlobalTheory.Flag.exists_gl_adapted_chain <;> assumption)
end

