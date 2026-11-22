import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
import Mathlib
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyCutoffMulSectionLe
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.CutEnergy

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem wdb_bound (A : WeightedAtlas n Y ι La) (C : Cover A) (χ : Y → ℝ) (hχ : A.SmoothFn χ)
    (a : Fin C.m) : ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ closedBall (C.c a) (C.r a),
      (∑ j, ‖wdb n j (fun w => ((χ ((A.chart (C.idx a)).symm w) : ℝ) : ℂ)) v‖ ^ 2) ≤ K := by
  set e := A.chart (C.idx a)
  have hg : ContDiffOn ℝ ∞ (fun w => ((χ (e.symm w) : ℝ) : ℂ)) e.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ (C.idx a))
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ (fun w => ((χ (e.symm w) : ℝ) : ℂ))) e.target :=
    hg.fderiv_of_isOpen e.open_target (by simp)
  have hc : ContinuousOn (fun v => ∑ j, ‖wdb n j (fun w => ((χ (e.symm w) : ℝ) : ℂ)) v‖ ^ 2)
      e.target := by
    refine continuousOn_finset_sum _ fun j _ => ?_
    have : ContDiffOn ℝ ∞ (wdb n j (fun w => ((χ (e.symm w) : ℝ) : ℂ))) e.target :=
      ((hd.clm_apply contDiffOn_const).add
        (contDiffOn_const.mul (hd.clm_apply contDiffOn_const))).div_const 2
    exact (this.continuousOn.norm).pow 2
  obtain ⟨K, hK⟩ := (isCompact_closedBall (C.c a) (C.r a)).exists_bound_of_continuousOn
    (hc.mono (C.sub a))
  refine ⟨max K 0, le_max_right _ _, fun v hv => ?_⟩
  have := hK v hv
  exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _))

theorem pt_bound (A : WeightedAtlas n Y ι La) (C : Cover A) (χ : Y → ℝ) (hχ : A.SmoothFn χ)
    (a : Fin C.m) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ v ∈ closedBall (C.c a) (C.r a),
      (∑ j, ‖wdb n j (fun w => ((χ ((A.chart (C.idx a)).symm w) : ℝ) : ℂ)) v‖ ^ 2) ≤ K)
    (la : La) (W Z : Set Y) (h : ι → Y → ℂ) (hW : IsOpen W) (hsupp : tsupport χ ⊆ W)
    (hsec : A.IsSecOn (A.kap + la) W h)
    (hZ : ∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) (v : V n) (hv : v ∈ ball (C.c a) (C.r a)) :
    ENNReal.ofReal ((∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) (C.idx a) ∘
        (A.chart (C.idx a)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤
      ENNReal.ofReal K * ((Z ∩ W).indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y))
          ((A.chart (C.idx a)).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v)))) := by
  set i := C.idx a
  set e := A.chart i
  set y := e.symm v
  set g : V n → ℂ := fun w => ((χ (e.symm w) : ℝ) : ℂ)
  have hvt : v ∈ e.target := C.sub a (ball_subset_closedBall hv)
  have hys : y ∈ e.source := e.map_target hvt
  have hgs : ContDiffOn ℝ ∞ g e.target := Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ i)
  have hgd : DifferentiableAt ℝ g v :=
    (hgs.differentiableOn (by simp)).differentiableAt (e.open_target.mem_nhds hvt)

  have hzero : y ∉ Z ∩ W → ∀ j, wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v = 0 := by
    intro hy j
    by_cases hyW : y ∈ W
    · have hyZ : y ∉ Z := fun hz => hy ⟨hz, hyW⟩
      have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
      have hvU : v ∈ e.target ∩ e.symm ⁻¹' W := ⟨hvt, hyW⟩
      have hH : DifferentiableAt ℂ (h i ∘ e.symm) v :=
        (hsec.1 i).differentiableAt (hU.mem_nhds hvU)
      have hg0 : wdb n j g v = 0 := by
        have hev : g =ᶠ[𝓝 v] fun _ => ((χ y : ℝ) : ℂ) := by
          have := (e.continuousAt_symm hvt).eventually (hZ y hyZ)
          filter_upwards [this] with w hw
          simp only [g]; rw [hw]
        rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hev]
        exact wdb_of_differentiableAt (differentiableAt_const _)
      have hfun : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) = fun w => g w * (h i ∘ e.symm) w :=
        rfl
      rw [hfun, wdb_mul hgd (hH.restrictScalars ℝ), wdb_of_differentiableAt hH, hg0]
      ring
    · have hyt : y ∉ tsupport χ := fun ht => hyW (hsupp ht)
      have h0 := (notMem_tsupport_iff_eventuallyEq.mp hyt)
      have hev : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
        have := (e.continuousAt_symm hvt).eventually h0
        filter_upwards [this] with w hw
        simp only [Function.comp_apply, Pi.zero_apply] at hw ⊢
        rw [hw]; simp
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hev]
      exact wdb_of_differentiableAt (differentiableAt_const _)
  by_cases hy : y ∈ Z ∩ W
  · have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
    have hvU : v ∈ e.target ∩ e.symm ⁻¹' W := ⟨hvt, hy.2⟩
    have hH : DifferentiableAt ℂ (h i ∘ e.symm) v :=
      (hsec.1 i).differentiableAt (hU.mem_nhds hvU)
    have hfun : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) = fun w => g w * (h i ∘ e.symm) w :=
      rfl
    have hw : ∀ j, wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v = wdb n j g v * h i y := by
      intro j
      rw [hfun, wdb_mul hgd (hH.restrictScalars ℝ), wdb_of_differentiableAt hH]
      simp [y]
    have hsum : (∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v‖ ^ 2) =
        ‖h i y‖ ^ 2 * ∑ j, ‖wdb n j g v‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hw j, norm_mul, mul_pow]; ring
    have hnsq := api_nsq_eq A hsec hys hy.2
    rw [A.ph_add _ _ i y hys] at hnsq
    have hexp : Real.exp (-A.ph la i y) =
        Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [Set.indicator_of_mem hy, ← ENNReal.ofReal_mul (by unfold WeightedAtlas.nsq; positivity),
      ← ENNReal.ofReal_mul hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hsum, ← hnsq, hexp]
    have hS := hK v (ball_subset_closedBall hv)
    have h1 : 0 ≤ ‖h i y‖ ^ 2 * (Real.exp (-(A.ph A.kap i y + A.ph la i y)) *
        Real.exp (A.ph A.kap i y)) := by positivity
    calc ‖h i y‖ ^ 2 * (∑ j, ‖wdb n j g v‖ ^ 2) *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))
        = (∑ j, ‖wdb n j g v‖ ^ 2) * (‖h i y‖ ^ 2 *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))) := by ring
      _ ≤ K * (‖h i y‖ ^ 2 *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))) :=
          mul_le_mul_of_nonneg_right hS h1
      _ = K * (‖h i y‖ ^ 2 * Real.exp (-(A.ph A.kap i y + A.ph la i y)) *
          Real.exp (A.ph A.kap i y)) := by ring
  · have : (∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v‖ ^ 2) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hzero hy j]; simp
    rw [this, zero_mul, ENNReal.ofReal_zero]
    exact zero_le

end

end GlobalTheory.CutEnergy

namespace GlobalTheory.CutEnergy

theorem dbarEnergy_cutoff_mul_section_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (χ : Y → ℝ), A.SmoothFn χ → ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (W Z : Set Y) (h : ι → Y → ℂ), IsOpen W → tsupport χ ⊆ W → A.IsSecOn (A.kap + la) W h → MeasurableSet Z → (∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) → n1 C la (fun i y => (χ y : ℂ) * h i y) ≤ ENNReal.ofReal K * ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A C χ hχ
  choose K hK0 hK using fun a => wdb_bound A C χ hχ a
  refine ⟨∑ a, K a, Finset.sum_nonneg fun a _ => hK0 a, ?_⟩
  intro la W Z h hW hsupp hsec hZm hZ
  set G : Y → ℝ≥0∞ := (Z ∩ W).indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) with hGdef
  have hGm : Measurable G := by
    classical
    have h1 : Measurable (W.indicator fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) := by
      rw [← Set.piecewise_eq_indicator]
      exact ContinuousOn.measurable_piecewise
        (ENNReal.continuous_ofReal.comp_continuousOn (api_nsq_contOn A hW hsec))
        continuousOn_const hW.measurableSet
    have : G = Z.indicator (W.indicator fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) :=
      (Set.indicator_indicator _ _ _).symm
    rw [this]; exact h1.indicator hZm
  have hint : ∫⁻ y, G y ∂A.mu = ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu :=
    lintegral_indicator (hZm.inter hW.measurableSet) _
  rw [← hint, ENNReal.ofReal_sum_of_nonneg (fun a _ => hK0 a), Finset.sum_mul]
  unfold n1
  refine Finset.sum_le_sum fun a _ => ?_
  calc _ ≤ ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (K a) *
          (G ((A.chart (C.idx a)).symm v) *
            ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v)))) :=
        setLIntegral_mono' measurableSet_ball fun v hv =>
          pt_bound A C χ hχ a (K a) (hK0 a) (hK a) la W Z h hW hsupp hsec hZ v hv
    _ = ENNReal.ofReal (K a) * ∫⁻ v in ball (C.c a) (C.r a), G ((A.chart (C.idx a)).symm v) *
            ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
          gcongr
          exact A.aap_lintegral_chart_le _ G hGm _ (ball_subset_closedBall.trans (C.sub a))

end GlobalTheory.CutEnergy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseNonvanishingSetOfNeZeroOnComponents
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem nz_dense_of_ne_zero_on_components : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (T : Set Y), A.IsSec Λ τ →
    (∀ y, ∃ P ∈ T, P ∈ connectedComponent y) → (∀ P ∈ T, τ (A.pick P) P ≠ 0) →
    Dense (nz A τ) := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ T hs hT hP
  set Zs : Set Y := {y | τ (A.pick y) y = 0} with hZs
  have hc : (nz A τ)ᶜ = Zs := by
    ext y; simp [nz, Zs]

  have toI : ∀ i x, x ∈ (A.chart i).source → τ (A.pick x) x = 0 → τ i x = 0 := by
    intro i x hx h0
    rw [hs.2 i (A.pick x) x (Set.mem_univ _) hx (A.mem_pick x), h0, mul_zero]
  have toP : ∀ i x, x ∈ (A.chart i).source → τ i x = 0 → τ (A.pick x) x = 0 := by
    intro i x hx h0
    rw [hs.2 (A.pick x) i x (Set.mem_univ _) (A.mem_pick x) hx, h0, mul_zero]
  set Z := interior Zs with hZ
  have hZo : IsOpen Z := isOpen_interior
  have hZc : IsClosed Z := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    set i := A.pick y
    set e := A.chart i
    have hyv : e y ∈ e.target := e.map_source (A.mem_pick y)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e y) hyv
    set W : Set Y := e.source ∩ e ⁻¹' ball (e y) r
    have hWo : IsOpen W := e.isOpen_inter_preimage isOpen_ball
    have hyW : y ∈ W := ⟨A.mem_pick y, mem_ball_self hr⟩
    obtain ⟨x, hxW, hxZ⟩ := (mem_closure_iff.mp hy) W hWo hyW
    set F : V n → ℂ := τ i ∘ e.symm
    have hF : DifferentiableOn ℂ F (ball (e y) r) := by
      have := hs.1 i
      refine this.mono ?_
      intro w hw; exact ⟨hball hw, Set.mem_univ _⟩
    have hxs : e x ∈ ball (e y) r := hxW.2
    have hev : F =ᶠ[𝓝 (e x)] 0 := by
      have hxt : e x ∈ e.target := e.map_source hxW.1
      have h1 : ∀ᶠ w in 𝓝 (e x), e.symm w ∈ Z := by
        have hca : ContinuousAt e.symm (e x) := e.continuousAt_symm hxt
        have : e.symm (e x) = x := e.left_inv hxW.1
        refine hca.preimage_mem_nhds ?_
        rw [this]; exact hZo.mem_nhds hxZ
      have h2 : ∀ᶠ w in 𝓝 (e x), w ∈ e.target := e.open_target.mem_nhds hxt
      filter_upwards [h1, h2] with w hw1 hw2
      have hsrc : e.symm w ∈ e.source := e.map_target hw2
      exact toI i _ hsrc (interior_subset (s := Zs) hw1)
    have hEq := ReciprocityTheory.L2DbarEstimates.C.ident n (ball (e y) r) F (e x) isOpen_ball (convex_ball _ _) hF hxs hev
    have hWZs : W ⊆ Zs := by
      intro z hz
      have h0 : F (e z) = 0 := hEq hz.2
      have : τ i z = 0 := by
        simpa [F, e.left_inv hz.1] using h0
      exact toP i z hz.1 this
    exact interior_maximal hWZs hWo hyW
  have hempty : Z = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨P, hPT, hPc⟩ := hT y
    have hsub := (IsClopen.connectedComponent_subset ⟨hZc, hZo⟩ hy)
    exact hP P hPT (interior_subset (s := Zs) (hsub hPc))
  have hd := interior_eq_empty_iff_dense_compl.mp hempty
  rw [← hc, compl_compl] at hd
  exact hd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealSubstOfConstantCoeffZero
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.SubstDiff

variable {τ B : Type} [CommRing B]

def euler (j : τ) (g : MvPowerSeries τ B) : MvPowerSeries τ B :=
  fun γ => (γ j : B) * coeff γ g

theorem coeff_euler (j : τ) (g : MvPowerSeries τ B) (γ : τ →₀ ℕ) :
    coeff γ (euler j g) = (γ j : B) * coeff γ g := rfl

theorem euler_mul (j : τ) (x y : MvPowerSeries τ B) :
    euler j (x * y) = euler j x * y + x * euler j y := by
  classical
  ext γ
  rw [coeff_euler, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q.1 + q.2 = γ := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
  rw [coeff_euler, coeff_euler, ← hq', Finsupp.add_apply]
  push_cast
  ring

theorem euler_one (j : τ) : euler j (1 : MvPowerSeries τ B) = 0 := by
  classical
  ext γ
  rw [coeff_euler, coeff_one, map_zero]
  split_ifs with h
  · subst h; simp
  · simp

theorem euler_pow (j : τ) (x : MvPowerSeries τ B) (n : ℕ) :
    euler j (x ^ (n + 1)) = ((n + 1 : ℕ) : MvPowerSeries τ B) * x ^ n * euler j x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ x (n + 1), euler_mul, ih]
    push_cast
    ring

theorem euler_prod_mem {σ : Type} (j : τ) (u : σ → MvPowerSeries τ B) (α : σ → ℕ)
    (s : Finset σ) :
    euler j (∏ i ∈ s, u i ^ α i) ∈
      Ideal.span (Set.range fun i => ((α i : ℕ) : MvPowerSeries τ B)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, euler_one]; exact Ideal.zero_mem _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, euler_mul]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_left _ _ ih)
    rcases h : α a with _ | n
    · rw [pow_zero, euler_one]; exact Ideal.zero_mem _
    · rw [euler_pow]
      refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, ?_⟩))
      simp only [h]

variable {Q : Type} [CommRing Q] [Algebra B Q]

theorem smul_mem_of_mem_span {σ : Type} (N : Submodule B Q) (α : σ → ℕ) (c : Q)
    (hc : ∀ i, (α i : Q) * c ∈ N) (h : MvPowerSeries τ B)
    (hh : h ∈ Ideal.span (Set.range fun i => ((α i : ℕ) : MvPowerSeries τ B))) :
    ∀ e, coeff e h • c ∈ N := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    classical
    obtain ⟨i, rfl⟩ := hx
    intro e
    dsimp only
    rw [← map_natCast (C (σ := τ) (R := B)), coeff_C]
    split_ifs
    · rw [Algebra.smul_def, map_natCast]; exact hc i
    · rw [zero_smul]; exact N.zero_mem
  | zero => intro e; rw [map_zero, zero_smul]; exact N.zero_mem
  | add x y _ _ hx hy => intro e; rw [map_add, add_smul]; exact N.add_mem (hx e) (hy e)
  | smul r x _ hx =>
    classical
    intro e
    rw [smul_eq_mul, coeff_mul, Finset.sum_smul]
    refine N.sum_mem fun q _ => ?_
    rw [mul_smul]
    exact N.smul_mem _ (hx q.2)

end GlobalTheory.QLog.SubstDiff

open GlobalTheory.QLog.SubstDiff in
theorem GlobalTheory.QLog.dIn_subst_up : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → DIn N (subst (up Q u) f) ∧ (In N f → In N (subst (up Q u) f)) := by
  intro p _ B O Q _ _ _ _ θ _ σ τ _ N f u hD hu
  set NQ : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N with hNQ
  have memNQ : ∀ q : Q, q ∈ NQ ↔ ∃ b ∈ N, q = algebraMap B Q b := by
    intro q
    rw [hNQ, Submodule.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  have ha : HasSubst (up Q u) :=
    hasSubst_of_constantCoeff_zero fun i => by
      simp only [up]
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu i,
        map_zero]

  have hprod : ∀ d : σ →₀ ℕ, (d.prod fun s e => (up Q u s) ^ e) =
      map (algebraMap B Q) (∏ i, u i ^ d i) := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
    simp only [up, map_pow]
  have hcoeff : ∀ e, coeff e (subst (up Q u) f) =
      ∑ d ∈ (coeff_subst_finite ha f e).toFinset,
        algebraMap B Q (coeff e (∏ i, u i ^ d i)) * coeff d f := by
    intro e
    rw [coeff_subst ha, finsum_eq_sum _ (coeff_subst_finite ha f e)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hprod, coeff_map, smul_eq_mul, mul_comm]
  refine ⟨fun e j => ?_, fun hI e => ?_⟩
  · rw [← memNQ, hcoeff, Finset.mul_sum]
    refine NQ.sum_mem fun d _ => ?_
    have key := smul_mem_of_mem_span NQ (fun i => d i) (coeff d f)
      (fun i => (memNQ _).2 (by obtain ⟨b, hb, h⟩ := hD d i; exact ⟨b, hb, h⟩))
      _ (euler_prod_mem j u (fun i => d i) Finset.univ) e
    convert key using 1
    rw [coeff_euler, Algebra.smul_def, map_mul, map_natCast]
    ring
  · rw [← memNQ, hcoeff]
    refine NQ.sum_mem fun d _ => ?_
    rw [← Algebra.smul_def]
    exact NQ.smul_mem _ ((memNQ _).2 (by obtain ⟨b, hb, h⟩ := hI d; exact ⟨b, hb, h⟩))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in

theorem _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish (δ : DividedPowers J) (a : B) (N : ℕ)
    (h : ∀ n, N ≤ n → δ.dpow n a = 0) :
    _root_.GlobalTheory.Cris.dpExp δ a = ∑ n ∈ Finset.range N, δ.dpow n a := by
  unfold _root_.GlobalTheory.Cris.dpExp
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  exact hn (h n (not_lt.mp hlt))

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in

theorem _root_.GlobalTheory.Cris.IsNilDP.dpExp_add_eq_mul {δ : DividedPowers J}
    (h : _root_.GlobalTheory.Cris.IsNilDP δ) {a b : B} (ha : a ∈ J) (hb : b ∈ J) :
    _root_.GlobalTheory.Cris.dpExp δ (a + b) = _root_.GlobalTheory.Cris.dpExp δ a * _root_.GlobalTheory.Cris.dpExp δ b := by
  obtain ⟨N, hN⟩ := h
  have hvan : ∀ x ∈ J, ∀ n, N ≤ n → δ.dpow n x = 0 := by
    intro x hx n hn
    simpa using hN [(n, x)] (by simpa using hx) (by simpa using hn)
  have hpair : ∀ i j, N ≤ i + j → δ.dpow i a * δ.dpow j b = 0 := by
    intro i j hij
    simpa using hN [(i, a), (j, b)] (by simp [ha, hb]) (by simpa using hij)
  let F : ℕ × ℕ → B := fun p => δ.dpow p.1 a * δ.dpow p.2 b
  rw [_root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ (a + b) N (hvan _ (J.add_mem ha hb)),
    _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ a N (hvan a ha), _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ b N (hvan b hb),
    Finset.sum_mul_sum, ← Finset.sum_product' (f := fun i j => δ.dpow i a * δ.dpow j b)]
  have hfilter : ∑ p ∈ Finset.range N ×ˢ Finset.range N with p.1 + p.2 < N, F p =
      ∑ p ∈ Finset.range N ×ˢ Finset.range N, F p := by
    refine Finset.sum_filter_of_ne fun p _ hp => ?_
    by_contra hlt
    exact hp (hpair p.1 p.2 (not_lt.mp hlt))
  rw [← hfilter, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range N)
    (g := fun p : ℕ × ℕ => p.1 + p.2) (fun p hp => by simpa using (Finset.mem_filter.mp hp).2)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [δ.dpow_add ha hb]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ⟨i, j⟩
  simp only [Finset.mem_range] at hn
  simp only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  omega

theorem IsNilDP.map_dpExp_eq {δ : DividedPowers J} {δ' : DividedPowers J'} (h : IsNilDP δ)
    {f : B →+* B'} (hf : IsDPMorphism δ δ' f) {a : B} (ha : a ∈ J) :
    f (dpExp δ a) = dpExp δ' (f a) := by
  obtain ⟨N, hN⟩ := h.exists_dpow_eq_zero
  rw [dpExp_eq_sum_range_of_vanish δ a N fun n hn ↦ hN n hn a,
    dpExp_eq_sum_range_of_vanish δ' (f a) N fun n hn ↦ by
      rw [← hf.map_dpow ha, hN n hn a, map_zero], map_sum]
  exact Finset.sum_congr rfl fun n _ ↦ hf.map_dpow ha

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in

theorem _root_.GlobalTheory.Cris.dpExp_add_and_natural (B B' : Type) [CommRing B] [CommRing B'] (J : Ideal B) (J' : Ideal B')
    (δ : DividedPowers J) (δ' : DividedPowers J') (h : _root_.GlobalTheory.Cris.IsNilDP δ) :
    (∀ a ∈ J, ∀ b ∈ J, _root_.GlobalTheory.Cris.dpExp δ (a + b) = _root_.GlobalTheory.Cris.dpExp δ a * _root_.GlobalTheory.Cris.dpExp δ b) ∧
      (∀ f : B →+* B', IsDPMorphism δ δ' f → ∀ a ∈ J,
        f (_root_.GlobalTheory.Cris.dpExp δ a) = _root_.GlobalTheory.Cris.dpExp δ' (f a)) := by
  refine ⟨fun a ha b hb => h.dpExp_add_eq_mul ha hb, fun f hf a ha => ?_⟩
  obtain ⟨N, hN⟩ := h
  have hvan : ∀ n, N ≤ n → δ.dpow n a = 0 := by
    intro n hn
    simpa using hN [(n, a)] (by simpa using ha) (by simpa using hn)
  have hvan' : ∀ n, N ≤ n → δ'.dpow n (f a) = 0 := by
    intro n hn
    rw [← hf.map_dpow ha, hvan n hn, map_zero]
  rw [_root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ a N hvan, _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ' (f a) N hvan',
    map_sum]
  exact Finset.sum_congr rfl fun n _ => hf.map_dpow ha

end GlobalTheory.Cris
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualBasisCoordMemMaximalIdealOfForallApply
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dualBasis_coord_mem_maximalIdeal : ∀ (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (k : ℕ) (lb : Module.Basis (Fin k) O (Module.Dual O M)) (l : Module.Dual O M), (∀ w, l w ∈ IsLocalRing.maximalIdeal O) → ∀ j, lb.repr l j ∈ IsLocalRing.maximalIdeal O := by
  intro O _ _ M _ _ _ _ k lb l hl j
  haveI : Module.Free O M := Module.free_of_flat_of_isLocalRing
  let ε := Module.Free.chooseBasis O M
  have hsum : l = ∑ i, l (ε i) • ε.dualBasis i := by
    refine ε.ext fun a => ?_
    simp [Module.Basis.dualBasis_apply_self, Finset.sum_apply, LinearMap.sum_apply]
  rw [hsum, map_sum]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hl _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionRowOperatorsStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_restriction_rowOperators : GlobalTheory.LeviCut.ResDer := by
  first | exact @GlobalTheory.LeviCut.dualWeyl_resDer | exact GlobalTheory.LeviCut.dualWeyl_resDer | (intros; apply GlobalTheory.LeviCut.dualWeyl_resDer <;> assumption)
end

