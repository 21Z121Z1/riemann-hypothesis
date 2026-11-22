import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.Theta2Integral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0184
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0187
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0202
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0144
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffOnUncurryOfFrame
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp.Frame

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def eps (p : Bool × Fin n × Fin n) (A : Mat n) : ℝ :=
  if p.1 then (A p.2.1 p.2.2).re else (A p.2.1 p.2.2).im

theorem contDiff_eps (p : Bool × Fin n × Fin n) : ContDiff ℝ ∞ (eps p : Mat n → ℝ) := by
  obtain ⟨b, i, j⟩ := p
  cases b
  · have e : (eps (false, i, j) : Mat n → ℝ) = Complex.imCLM ∘ fun y : Mat n => y i j := by
      funext A; simp [eps]
    rw [e]
    exact Complex.imCLM.contDiff.comp (GlobalTheory.CompanionTheory.LengthGL.contDiff_ent i j)
  · have e : (eps (true, i, j) : Mat n → ℝ) = Complex.reCLM ∘ fun y : Mat n => y i j := by
      funext A; simp [eps]
    rw [e]
    exact Complex.reCLM.contDiff.comp (GlobalTheory.CompanionTheory.LengthGL.contDiff_ent i j)

theorem sum_eps (A : Mat n) : ∑ p, eps p A • (bs p : Mat n) = A := by
  ext a b
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, eps, bs, Matrix.sum_apply, Matrix.smul_apply]
  simp [Matrix.single_apply, Finset.sum_add_distrib, ite_and]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem fderiv_frame (f : Mat n → V) {x : Mat n} (hx : x ∈ GLs n) (ξ : Mat n) :
    fderiv ℝ f x ξ = ∑ p, eps p (ξ * x⁻¹) • fderiv ℝ f x (bs p * x) := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have e : ξ = ∑ p, eps p (ξ * x⁻¹) • (bs p * x) := by
    have : ξ * x⁻¹ * x = ξ := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    conv_lhs => rw [← this, ← sum_eps (ξ * x⁻¹), Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => smul_mul_assoc _ _ _
  conv_lhs => rw [e, map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

theorem contDiffOn_coeff (p : Bool × Fin n × Fin n) (ξ : Mat n) :
    ContDiffOn ℝ ∞ (fun x : Mat n => eps p (ξ * x⁻¹)) (GLs n) :=
  (contDiff_eps p).comp_contDiffOn
    ((GlobalTheory.CompanionTheory.RCalc.mulL ξ).contDiff.comp_contDiffOn GlobalTheory.CompanionTheory.LengthGL.contDiffOn_inv)

theorem contDiffOn_coeff' (p : Bool × Fin n × Fin n) (ξ : Mat n) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Mat n => eps p (ξ * z.2⁻¹)) (Set.univ ×ˢ GLs n) :=
  (contDiffOn_coeff p ξ).comp contDiff_snd.contDiffOn fun _ hz => hz.2

theorem isOpen_dom : IsOpen (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)) :=
  isOpen_univ.prod GlobalTheory.CompanionTheory.LengthGL.isOpen_GLs

theorem hasFDerivAt_uncurry {h h₀ : ℝ → Mat n → V} {hp : (Bool × Fin n × Fin n) → ℝ → Mat n → V}
    (c₀ : ContinuousOn (Function.uncurry h₀) (Set.univ ×ˢ GLs n))
    (cp : ∀ p, ContinuousOn (Function.uncurry (hp p)) (Set.univ ×ˢ GLs n))
    (ht : ∀ t, ∀ x ∈ GLs n, HasDerivAt (fun s => h s x) (h₀ t x) t)
    (hd : ∀ t, DifferentiableOn ℝ (h t) (GLs n))
    (hf : ∀ p t, ∀ x ∈ GLs n, fderiv ℝ (h t) x (bs p * x) = hp p t x)
    {t : ℝ} {x : Mat n} (hx : x ∈ GLs n) :
    HasFDerivAt (Function.uncurry h)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (h₀ t x)).coprod (fderiv ℝ (h t) x)) (t, x) := by
  have hn : (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)) ∈ nhds ((t, x) : ℝ × Mat n) :=
    isOpen_dom.mem_nhds ⟨trivial, hx⟩
  have c1 : ContinuousOn (Function.uncurry fun (t : ℝ) (x : Mat n) => (1 : ℝ →L[ℝ] ℝ).smulRight (h₀ t x))
      (Set.univ ×ˢ GLs n) := by
    rw [continuousOn_clm_apply]
    intro y
    refine ContinuousOn.congr (f := fun z : ℝ × Mat n => y • Function.uncurry h₀ z)
      ((continuousOn_const (c := y)).smul c₀) ?_
    rintro ⟨s, w⟩ -
    simp [Function.uncurry_def]
  have c2 : ContinuousOn (Function.uncurry fun (t : ℝ) (x : Mat n) => fderiv ℝ (h t) x)
      (Set.univ ×ˢ GLs n) := by
    refine continuousOn_clm_apply.2 fun ξ => ?_
    have h1 : ContinuousOn (fun z : ℝ × Mat n => ∑ p, eps p (ξ * z.2⁻¹) • hp p z.1 z.2)
        (Set.univ ×ˢ GLs n) :=
      continuousOn_finset_sum _ fun p _ => (contDiffOn_coeff' p ξ).continuousOn.smul (cp p)
    refine h1.congr ?_
    rintro ⟨s, y⟩ ⟨-, hy⟩
    have hy' : y ∈ GLs n := hy
    exact (fderiv_frame (h s) hy' ξ).trans (Finset.sum_congr rfl fun p _ => by rw [hf p s y hy'])
  have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := ((t, x) : ℝ × Mat n)) (f := h)
    (f₁ := fun t x => (1 : ℝ →L[ℝ] ℝ).smulRight (h₀ t x)) (f₂ := fun t x => fderiv ℝ (h t) x)
    ?_ ?_ (c1.continuousAt hn) (c2.continuousAt hn)
  · exact key.hasFDerivAt
  · filter_upwards [hn] with v hv
    exact (ht v.1 v.2 hv.2).hasFDerivAt
  · filter_upwards [hn] with v hv
    exact ((hd v.1 v.2 hv.2).differentiableAt (GlobalTheory.CompanionTheory.LengthGL.isOpen_GLs.mem_nhds hv.2)).hasFDerivAt

theorem contDiffOn_step (F : Set (ℝ → Mat n → V))
    (hc : ∀ h ∈ F, ContinuousOn (Function.uncurry h) (Set.univ ×ˢ GLs n))
    (hdt : ∀ h ∈ F, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, HasDerivAt (fun s => h s x) (h' t x) t)
    (hd : ∀ h ∈ F, ∀ t, DifferentiableOn ℝ (h t) (GLs n))
    (hfr : ∀ h ∈ F, ∀ p, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, fderiv ℝ (h t) x (bs p * x) = h' t x)
    (k : ℕ) (ih : ∀ h ∈ F, ContDiffOn ℝ k (Function.uncurry h) (Set.univ ×ˢ GLs n)) :
    ∀ h ∈ F, ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry h) (Set.univ ×ˢ GLs n) := by
  intro h hh
  obtain ⟨h₀, h₀F, ht⟩ := hdt h hh
  choose hp hpF hf using hfr h hh
  have hD : ∀ z ∈ (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)), HasFDerivAt (Function.uncurry h)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (h₀ z.1 z.2)).coprod (fderiv ℝ (h z.1) z.2)) z := fun z hz =>
    hasFDerivAt_uncurry (hc _ h₀F) (fun p => hc _ (hpF p)) ht (hd h hh) hf hz.2
  have e : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by norm_cast
  rw [e, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_dom]
  refine ⟨fun z hz => (hD z hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_clm_apply]
  rintro ⟨τ, ξ⟩
  have h1 : ContDiffOn ℝ k (fun z : ℝ × Mat n =>
      τ • h₀ z.1 z.2 + ∑ p, eps p (ξ * z.2⁻¹) • hp p z.1 z.2) (Set.univ ×ˢ GLs n) := by
    refine ContDiffOn.add (contDiffOn_const.smul (ih _ h₀F)) (ContDiffOn.sum fun p _ => ?_)
    exact ((contDiffOn_coeff' p ξ).of_le (by exact_mod_cast le_top)).smul (ih _ (hpF p))
  refine h1.congr ?_
  rintro ⟨s, y⟩ hz
  have e1 : fderiv ℝ (Function.uncurry h) (s, y) = _ := (hD _ hz).fderiv
  refine (congrArg (fun L => L (τ, ξ)) e1).trans ?_
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply]
  rw [fderiv_frame _ hz.2]
  simp only [ContinuousLinearMap.one_apply]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by rw [hf p s y hz.2]

theorem contDiffOn_uncurry_of_frame : ∀ {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (F : Set (ℝ → Mat n → V)), (∀ h ∈ F, ContinuousOn (Function.uncurry h) (Set.univ ×ˢ GLs n)) →
    (∀ h ∈ F, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, HasDerivAt (fun s => h s x) (h' t x) t) →
    (∀ h ∈ F, ∀ t, DifferentiableOn ℝ (h t) (GLs n)) →
    (∀ h ∈ F, ∀ p, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, fderiv ℝ (h t) x (bs p * x) = h' t x) →
    ∀ h ∈ F, ContDiffOn ℝ ∞ (Function.uncurry h) (Set.univ ×ˢ GLs n) := by
  intro n V _ _ F hc hdt hd hfr h hh
  rw [contDiffOn_infty]
  intro k
  induction k generalizing h with
  | zero =>
    have h0 : ContDiffOn ℝ 0 (Function.uncurry h) (Set.univ ×ˢ GLs n) := contDiffOn_zero.2 (hc h hh)
    simpa using h0
  | succ k ih => exact contDiffOn_step F hc hdt hd hfr k (fun h hh => ih h hh) h hh

end GlobalTheory.CompanionTheory.WaveCp.Frame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnOfIteratedFDerivZero
section
noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ParamInt

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] {ν : Measure X} [IsFiniteMeasureOnCompacts ν]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem continuousOn_of_iteratedFDeriv_zero {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set E} {F : X → E → W}
    (h : ContinuousOn (fun p : X × E => iteratedFDeriv ℝ 0 (F p.1) p.2) (univ ×ˢ U)) :
    ContinuousOn (fun p : X × E => F p.1 p.2) (univ ×ˢ U) := by
  have e : (fun p : X × E => F p.1 p.2) =
      fun p => ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) W (fun _ => 0)
        (iteratedFDeriv ℝ 0 (F p.1) p.2) := by
    funext p; simp
  rw [e]
  exact (ContinuousLinearMap.continuous _).comp_continuousOn h

theorem continuousOn_iteratedFDeriv_fderiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set E} {F : X → E → W} (m : ℕ)
    (h : ContinuousOn (fun p : X × E => iteratedFDeriv ℝ (m + 1) (F p.1) p.2) (univ ×ˢ U)) :
    ContinuousOn (fun p : X × E => iteratedFDeriv ℝ m (fderiv ℝ (F p.1)) p.2) (univ ×ˢ U) := by
  have e : (fun p : X × E => iteratedFDeriv ℝ m (fderiv ℝ (F p.1)) p.2) =
      fun p : X × E => continuousMultilinearCurryRightEquiv' ℝ m E W
        (iteratedFDeriv ℝ (m + 1) (F p.1) p.2) := by
    funext p
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [e]
  exact (LinearIsometryEquiv.continuous _).comp_continuousOn h

theorem integrable_bound {K : Set X} (hK : IsCompact K) (C : ℝ) :
    Integrable ((toMeasurable ν K).indicator fun _ => C) ν := by
  rw [integrable_indicator_iff (measurableSet_toMeasurable ν K)]
  refine integrableOn_const ?_
  rw [measure_toMeasurable]
  exact hK.measure_lt_top.ne

theorem le_bound {W : Type} [NormedAddCommGroup W] {K : Set X} {C : ℝ} {t : X} {w : W}
    (h1 : t ∈ K → ‖w‖ ≤ C) (h2 : t ∉ K → w = 0) :
    ‖w‖ ≤ (toMeasurable ν K).indicator (fun _ => max C 0) t := by
  by_cases ht : t ∈ K
  · rw [indicator_of_mem (subset_toMeasurable ν K ht)]
    exact (h1 ht).trans (le_max_left _ _)
  · rw [h2 ht, norm_zero]
    exact indicator_nonneg (fun _ _ => le_max_right _ _) _

theorem hasFDerivAt_integral {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U : Set E} (hU : IsOpen U) {F : X → E → V}
    (h1 : ∀ t, ContDiffOn ℝ ∞ (F t) U)
    (h0 : ContinuousOn (fun p : X × E => F p.1 p.2) (univ ×ˢ U))
    (hd : ContinuousOn (fun p : X × E => fderiv ℝ (F p.1) p.2) (univ ×ˢ U))
    (h3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0)
    {x₀ : E} (hx : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ t, F t x ∂ν) (∫ t, fderiv ℝ (F t) x₀ ∂ν) x₀ := by
  obtain ⟨U', hU', K, hK, hz⟩ := h3 x₀ hx
  have hN : U ∩ interior U' ∈ 𝓝 x₀ := inter_mem (hU.mem_nhds hx) (interior_mem_nhds.2 hU')
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hN
  have hBc : IsCompact (Metric.closedBall x₀ r) := isCompact_closedBall x₀ r
  have hKB := hK.prod hBc
  have hsub : K ×ˢ Metric.closedBall x₀ r ⊆ univ ×ˢ U :=
    fun p hp => ⟨mem_univ _, (hball hp.2).1⟩
  obtain ⟨C, hC⟩ := hKB.exists_bound_of_continuousOn (hd.mono hsub)
  obtain ⟨C₀, hC₀⟩ := hKB.exists_bound_of_continuousOn (h0.mono hsub)
  have hx₀B : x₀ ∈ Metric.closedBall x₀ r := Metric.mem_closedBall_self hr.le
  have hdz : ∀ t ∉ K, ∀ x ∈ Metric.closedBall x₀ r, fderiv ℝ (F t) x = 0 := by
    intro t ht x hxB
    have : F t =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isOpen_interior.mem_nhds (hball hxB).2] with y hy
      exact hz t ht y (interior_subset hy)
    rw [this.fderiv_eq]
    simp
  have hct : ∀ x ∈ U, Continuous fun t => F t x := fun x hxU =>
    h0.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hxU⟩
  have hcd : ∀ x ∈ U, Continuous fun t => fderiv ℝ (F t) x := fun x hxU =>
    hd.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hxU⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => F t x)
    (F' := fun x t => fderiv ℝ (F t) x) (s := Metric.closedBall x₀ r)
    (bound := (toMeasurable ν K).indicator fun _ => max C 0)
    (Metric.closedBall_mem_nhds x₀ hr) ?_ ?_ ?_ ?_ (integrable_bound hK _) ?_
  · filter_upwards [hU.mem_nhds hx] with x hxU
    exact (hct x hxU).aestronglyMeasurable
  · refine Integrable.mono' (integrable_bound (ν := ν) hK (max C₀ 0))
      (hct x₀ hx).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    exact le_bound (fun ht => hC₀ (t, x₀) ⟨ht, hx₀B⟩) (fun ht => hz t ht x₀ (interior_subset (hball hx₀B).2))
  · exact (hcd x₀ hx).aestronglyMeasurable
  · refine ae_of_all _ fun t x hxB => ?_
    exact le_bound (fun ht => hC (t, x) ⟨ht, hxB⟩) (fun ht => hdz t ht x hxB)
  · refine ae_of_all _ fun t x hxB => ?_
    exact (((h1 t).contDiffAt (hU.mem_nhds (hball hxB).1)).differentiableAt (by simp)).hasFDerivAt

theorem contDiffOn_integral_nat {U : Set E} (hU : IsOpen U) (m : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : X → E → V),
      (∀ t, ContDiffOn ℝ ∞ (F t) U) →
      (∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U)) →
      (∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) →
      ContDiffOn ℝ m (fun x => ∫ t, F t x ∂ν) U := by
  have key : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (F : X → E → V), (∀ t, ContDiffOn ℝ ∞ (F t) U) →
      (∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U)) →
      (∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) →
      ∀ x₀ ∈ U, HasFDerivAt (fun x => ∫ t, F t x ∂ν) (∫ t, fderiv ℝ (F t) x₀ ∂ν) x₀ := by
    intro V _ _ _ F h1 h2 h3 x₀ hx
    exact hasFDerivAt_integral hU h1 (continuousOn_of_iteratedFDeriv_zero (h2 0))
      (continuousOn_of_iteratedFDeriv_zero (F := fun t => fderiv ℝ (F t))
        (continuousOn_iteratedFDeriv_fderiv 0 (h2 1))) h3 hx
  induction m with
  | zero =>
    intro V _ _ _ F h1 h2 h3
    have : ContinuousOn (fun x => ∫ t, F t x ∂ν) U := fun x hx =>
      (key V F h1 h2 h3 x hx).continuousAt.continuousWithinAt
    have h : ContDiffOn ℝ 0 (fun x => ∫ t, F t x ∂ν) U := contDiffOn_zero.2 this
    simpa using h
  | succ m ih =>
    intro V _ _ _ F h1 h2 h3
    have hG1 : ∀ t, ContDiffOn ℝ ∞ (fderiv ℝ (F t)) U := fun t =>
      (h1 t).fderiv_of_isOpen hU (by simp)
    have hG2 : ∀ k : ℕ, ContinuousOn
        (fun p : X × E => iteratedFDeriv ℝ k (fderiv ℝ (F p.1)) p.2) (univ ×ˢ U) := fun k =>
      continuousOn_iteratedFDeriv_fderiv k (h2 (k + 1))
    have hG3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧
        ∀ t ∉ K, ∀ x ∈ U', fderiv ℝ (F t) x = 0 := by
      intro x₀ hx
      obtain ⟨U', hU', K, hK, hz⟩ := h3 x₀ hx
      refine ⟨interior U', interior_mem_nhds.2 hU', K, hK, fun t ht x hxU => ?_⟩
      have : F t =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [isOpen_interior.mem_nhds hxU] with y hy
        exact hz t ht y (interior_subset hy)
      rw [this.fderiv_eq]
      simp
    have hI := ih (E →L[ℝ] V) (fun t => fderiv ℝ (F t)) hG1 hG2 hG3
    have hcast : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (key V F h1 h2 h3 x hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    exact hI.congr fun x hx => (key V F h1 h2 h3 x hx).fderiv

theorem contDiffOn_integral {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U : Set E} (hU : IsOpen U) (F : X → E → V)
    (h1 : ∀ t, ContDiffOn ℝ ∞ (F t) U)
    (h2 : ∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U))
    (h3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ t, F t x ∂ν) U :=
  contDiffOn_infty.2 fun m => contDiffOn_integral_nat hU m V F h1 h2 h3

theorem intSmooth : PositivityTheory.RgBcC.VC.IntSmooth := by
  intro n X _ _ _ _ ν _ V _ _ _ F h1 h2 h3
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hU : IsOpen (PositivityTheory.RgBcC.GLs n) := by
    have h : Continuous fun g : PositivityTheory.RgTw.Mat n => g.det := Continuous.matrix_det continuous_id
    exact isOpen_ne_fun h continuous_const
  exact contDiffOn_integral hU F h1 h2 h3

end GlobalTheory.CompanionTheory.ParamInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSetIntegralOfContinuousUncurry
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.EisRk1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1Theta

variable {K : Type*} [Field K] [NumberField K]

theorem continuous_scal : Continuous (scal : IdeleGroup K → GL (Fin 2) 𝔸[K]) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;>
      simp [Function.comp_def, scal, borelElt_val] <;> first | exact Units.continuous_val | exact continuous_const
  · have hinv : Continuous fun a : IdeleGroup K ↦ ((a⁻¹ : IdeleGroup K) : 𝔸[K]) :=
      Units.continuous_val.comp continuous_inv
    refine continuous_matrix fun i j ↦ ?_
    fin_cases i <;> fin_cases j
    · exact hinv
    · simpa [scal, borelElt] using continuous_const
    · simpa [scal, borelElt] using continuous_const
    · exact hinv

theorem continuous_theta2 {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhat2 K) :
    Continuous (theta2 F) := by
  refine continuous_iff_continuousAt.2 fun h₀ ↦ ?_
  obtain ⟨C, hC, hh₀⟩ := exists_compact_mem_nhds h₀
  obtain ⟨u, hu, hFu⟩ := GlobalTheory.T.schwartz_bruhat_uniform_summable_majorant hF hC
  have hcont : ContinuousOn (theta2 F) C := by
    refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hFu h hh ξ
    refine (continuous_of_mem_schwartzBruhat2 hF).comp ?_
    exact continuous_const.matrix_vecMul Units.continuous_val
  exact hcont.continuousAt hh₀

theorem continuous_setIntegral_of_continuous_uncurry {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y)
    [IsFiniteMeasureOnCompacts ν] {E : Set Y} (hE : IsCompact (closure E)) (hν : ν E < ⊤)
    {f : X → Y → ℂ} (hf : Continuous (Function.uncurry f)) :
    Continuous fun x ↦ ∫ u in E, f x u ∂ν := by
  have hint : ∀ x, IntegrableOn (f x) E ν := fun x ↦ by
    have hc : Continuous (f x) := hf.comp (Continuous.prodMk_right x)
    exact (hc.continuousOn.integrableOn_compact hE).mono_set subset_closure
  refine continuous_iff_continuousAt.2 fun q ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  set m := ν.real E with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hδ : 0 < ε / (2 * (m + 1)) := by positivity
  obtain ⟨v, hv, hvu⟩ := hE.mem_uniformity_of_prod (f := f) (s := Set.univ) (q := q)
    hf.continuousOn (Set.mem_univ q) (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint q)]
  have hb : ‖∫ u in E, (f p u - f q u) ∂ν‖ ≤ ε / (2 * (m + 1)) * m := by
    refine norm_setIntegral_le_of_norm_le_const hν fun u hu ↦ ?_
    have := hvu p hp u (subset_closure hu)
    rw [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  refine hb.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

noncomputable def translatedIntegrand (w : InfinitePlace K) (Φ : (Fin 2 → 𝔸[K]) → ℂ)
    (μ : HeckeCharacter K) (p : {r : ℝ // 0 < r} × GL (Fin 2) 𝔸[K]) (u : normOneSubgroup K) : ℂ :=
  theta2 Φ (scal (moduleSection w p.1 * (u : IdeleGroup K)) * p.2) *
    (μ.toIdele (u : IdeleGroup K) : ℂ)

theorem continuous_translatedIntegrand (w : InfinitePlace K) {Φ : (Fin 2 → 𝔸[K]) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 K) (μ : HeckeCharacter K) :
    Continuous (Function.uncurry (translatedIntegrand w Φ μ)) := by
  have hu : Continuous fun x : ({r : ℝ // 0 < r} × GL (Fin 2) 𝔸[K]) × normOneSubgroup K ↦
      (x.2 : IdeleGroup K) := continuous_subtype_val.comp continuous_snd
  have hs : Continuous fun x : ({r : ℝ // 0 < r} × GL (Fin 2) 𝔸[K]) × normOneSubgroup K ↦
      moduleSection w x.1.1 :=
    (continuous_moduleSection w).comp (continuous_fst.comp continuous_fst)
  have hg : Continuous fun x : ({r : ℝ // 0 < r} × GL (Fin 2) 𝔸[K]) × normOneSubgroup K ↦
      x.1.2 := continuous_snd.comp continuous_fst
  exact ((continuous_theta2 hΦ).comp ((continuous_scal.comp (hs.mul hu)).mul hg)).mul
    (continuous_subtype_val.comp (μ.continuous_toIdele.comp hu))

end GlobalTheory.CompanionTheory.EisRk1Theta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverSystemCechPullNatural
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechLerayPull

theorem cechHEquiv_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) : ∀ (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : GroundTheory.Arith.SchemeCoh.cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : GroundTheory.Arith.SchemeCoh.cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : GroundTheory.Arith.SchemeCoh.cechH G.obj V n ≃+ Sheaf.H.{0} G n) x)
  | 0, G, G', _, _, φ, x => GlobalTheory.T.cech_h0_pull_compat f V hV U hU τ hτ φ x
  | 1, G, G', hG, hG', φ, x => by
      obtain ⟨α, rfl⟩ := GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift f φ
      exact GlobalTheory.T.cech_connecting_pull_natural f V hV U hU τ hτ (S := injectiveSequence G) (S' := injectiveSequence G')
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hCY V hVB G hG)
        (injectiveSequence_cechAcyclic G V) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hCX U hUB G' hG') (injectiveSequence_cechAcyclic G' U) α x
  | m + 2, G, G', hG, hG', φ, x => by
      obtain ⟨α, rfl⟩ := GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift f φ
      exact GlobalTheory.T.cech_sheaf_cohomology_pull_compat f V U τ hτ (S := injectiveSequence G) (S' := injectiveSequence G')
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hCY V hVB G hG)
        (injectiveSequence_cechAcyclic G V) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hCX U hUB G' hG') (injectiveSequence_cechAcyclic G' U) α m _ _
        (fun y => cechHEquiv_pull f hCY hCX V hV hVB U hU hUB τ hτ (m + 1) _ _ α.τ₃ y) x

end GlobalTheory.CompanionTheory.CechLerayPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfDerivLeMul
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd.GronwallZero

theorem eq_zero_of_deriv_le_mul :
    ∀ (e e' : ℝ → ℝ) (K t : ℝ), 0 ≤ t → (∀ s, HasDerivAt e (e' s) s) →
      (∀ s, e' s ≤ K * e s) → (∀ s, 0 ≤ e s) → e 0 = 0 → e t = 0 := by
  intro e e' K t ht hd hle hnn h0
  have hg : ∀ s, HasDerivAt (fun s => e s * Real.exp (-K * s))
      ((e' s - K * e s) * Real.exp (-K * s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-K * s)) (Real.exp (-K * s) * (-K)) s := by
      have h2 : HasDerivAt (fun s : ℝ => -K * s) (-K) s := by
        simpa using (hasDerivAt_id s).const_mul (-K)
      exact h2.exp
    have h5 : HasDerivAt (fun s => e s * Real.exp (-K * s))
        (e' s * Real.exp (-K * s) + e s * (Real.exp (-K * s) * (-K))) s := (hd s).mul h1
    exact h5.congr_deriv (by ring)
  have hanti : Antitone (fun s => e s * Real.exp (-K * s)) := by
    apply antitone_of_deriv_nonpos
    · exact fun s => (hg s).differentiableAt
    · intro s
      rw [(hg s).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hle s]) (Real.exp_pos _).le
  have h3 : e t * Real.exp (-K * t) ≤ e 0 * Real.exp (-K * 0) := hanti ht
  rw [h0, zero_mul] at h3
  have h4 : e t ≤ 0 := by
    by_contra hc
    exact absurd h3 (not_le.mpr (mul_pos (not_le.mp hc) (Real.exp_pos _)))
  exact le_antisymm h4 (hnn t)

end GlobalTheory.CompanionTheory.WaveSpd.GronwallZero
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullOWOverCompStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullO_comp_block_decomposition : ∀ (R : Type) [CommRing R] (X Y Z : Over (Sp R)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : HO1 Z.hom) (b : HO1 Y.hom) (c : HO1 X.hom), IsPullO (wOver g) a b → IsPullO (wOver f) b c →
    IsPullO (wOver (f ≫ g)) a c := by
  first | exact @GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp | exact GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp | (intros; apply GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHoldStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_function_facts_hold : PositivityTheory.RgBcC.LgFacts := by
  first | exact @GlobalTheory.CompanionTheory.LengthGL.lgFacts | exact GlobalTheory.CompanionTheory.LengthGL.lgFacts | (intros; apply GlobalTheory.CompanionTheory.LengthGL.lgFacts <;> assumption)
end

