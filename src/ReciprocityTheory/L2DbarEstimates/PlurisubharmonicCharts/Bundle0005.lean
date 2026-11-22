import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

noncomputable section

theorem leviV_const_mul {n : ℕ} {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (c d : ℝ)
    (ξ : Fin n → ℂ) :
    leviV n (fun y => ((c * f y + d : ℝ) : ℂ)) x ξ = c * leviV n (fun y => ((f y : ℝ) : ℂ)) x ξ := by
  have hk : ContDiffAt ℝ 2 (fun t : ℝ => c * t + d) (f x) :=
    ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
  have h := leviChain n (fun t : ℝ => c * t + d) f x ξ hf hk
  have hd : deriv (fun t : ℝ => c * t + d) = fun _ => c := by
    funext t; rw [deriv_add_const, deriv_const_mul_field', deriv_id'']; ring
  rw [h, hd]; simp

theorem contDiffAt_two_of_holo {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {v : V n} (hv : v ∈ U) : ContDiffAt ℂ 2 g v :=
  ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hv)).of_le (by norm_cast)

theorem contDiffOn_of_holo {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) : ContDiffOn ℝ ∞ g U :=
  (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).restrict_scalars ℝ

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

def psD {N : ℕ} (L : La) (w : Fin N → ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (ps1 : Y → ℝ)
    (η δ : ℝ) (y : Y) : ℝ :=
  ps1 y + η * Real.log (A.sqn L w y) + n * Real.log (A.sqn L s y + δ)

theorem aap_sqn_nonneg {N : ℕ} (la : La) (w : Fin N → ι → Y → ℂ) (y : Y) : 0 ≤ A.sqn la w y :=
  Finset.sum_nonneg fun k _ => by unfold nsq; positivity

theorem aap_sqn_pos {N : ℕ} {L : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (y : Y) : 0 < A.sqn L w y := by
  obtain ⟨k, hk⟩ := hD.no_common_zero y
  refine Finset.sum_pos' (fun j _ => by unfold nsq; positivity) ⟨k, Finset.mem_univ _, ?_⟩
  unfold nsq; have := norm_pos_iff.2 hk; positivity

theorem holo_chart {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s) (i : ι) :
    DifferentiableOn ℂ (s i ∘ (A.chart i).symm) (A.chart i).target := by
  have h := hs.1 i; simpa using h

theorem psD_smooth {N : ℕ} {L : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) {ps1 : Y → ℝ} (hps1 : A.SmoothFn ps1)
    (η : ℝ) {δ : ℝ} (hδ : 0 < δ) : A.SmoothFn (A.psD L w s ps1 η δ) := by
  intro i
  set φ := A.chart i
  have hb : ContDiffOn ℝ ∞ (fun v => A.ph L i (φ.symm v)) φ.target := A.smooth_ph L i
  have hn2 : ∀ {m : ℕ} (u : Fin m → ι → Y → ℂ), (∀ k, A.IsSec L (u k)) →
      ContDiffOn ℝ ∞ (fun v => (∑ k, ‖u k i (φ.symm v)‖ ^ 2) * Real.exp (-A.ph L i (φ.symm v)))
        φ.target := fun u hu =>
    (ContDiffOn.sum fun k _ => (contDiff_norm_sq ℝ).comp_contDiffOn
      (contDiffOn_of_holo φ.open_target (A.holo_chart (hu k) i))).mul
      (Real.contDiff_exp.comp_contDiffOn hb.neg)
  have heq : ∀ v ∈ φ.target, (A.psD L w s ps1 η δ ∘ φ.symm) v =
      ps1 (φ.symm v) + η * Real.log ((∑ k, ‖w k i (φ.symm v)‖ ^ 2) *
        Real.exp (-A.ph L i (φ.symm v))) + n * Real.log ((∑ k, ‖s k i (φ.symm v)‖ ^ 2) *
        Real.exp (-A.ph L i (φ.symm v)) + δ) := by
    intro v hv
    have hx := φ.map_target hv
    simp only [Function.comp, psD, A.sqn_chart L w hD.sec_w i hx, A.sqn_chart L s hD.sec_s i hx]
  refine ContDiffOn.congr ?_ heq
  refine ((hps1 i).add (contDiffOn_const.mul ((hn2 w hD.sec_w).log ?_))).add
    (contDiffOn_const.mul (((hn2 s hD.sec_s).add contDiffOn_const).log ?_))
  · intro v hv
    have hx := φ.map_target hv
    rw [← A.sqn_chart L w hD.sec_w i hx]; exact (A.aap_sqn_pos hD _).ne'
  · intro v hv
    have hx := φ.map_target hv
    rw [← A.sqn_chart L s hD.sec_s i hx]; have := A.aap_sqn_nonneg L s (φ.symm v); positivity

theorem exp_neg_psD {N : ℕ} {L : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (ps1 : Y → ℝ) (η : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (y : Y) : Real.exp (-A.psD L w s ps1 η δ y) =
      Real.exp (-ps1 y) * A.sqn L w y ^ (-η) * (A.sqn L s y + δ) ^ (-(n : ℝ)) := by
  have h1 := A.aap_sqn_pos hD y
  have h2 : 0 < A.sqn L s y + δ := by have := A.aap_sqn_nonneg L s y; linarith
  rw [Real.rpow_def_of_pos h1, Real.rpow_def_of_pos h2, ← Real.exp_add, ← Real.exp_add]
  congr 1; unfold psD; ring

theorem levi_psD {N : ℕ} {L la : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (hPosL : A.Pos L fun _ => 0)
    {ps1 : Y → ℝ} (hps1 : A.SmoothFn ps1) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hLevi : ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
      2 * η * A.leviAt i (A.ph L i) y ξ ≤
        A.leviAt i (fun x => A.ph (la - n • L) i x + ps1 x) y ξ)
    (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    η * A.leviAt i (A.ph L i) y ξ ≤
      A.leviAt i (fun x => A.ph la i x + A.psD L w s ps1 η δ x) y ξ := by
  set φ := A.chart i
  set v0 := φ y
  have hv0 : v0 ∈ φ.target := φ.map_source hy
  have hT : φ.target ∈ 𝓝 v0 := φ.open_target.mem_nhds hv0
  have hsy : φ.symm v0 = y := φ.left_inv hy
  set a : V n → ℝ := fun v => A.ph (la - n • L) i (φ.symm v) + ps1 (φ.symm v)
  set b : V n → ℝ := fun v => A.ph L i (φ.symm v)
  set W : V n → ℝ := fun v => ∑ k, Complex.normSq (w k i (φ.symm v))
  set Sv : V n → ℝ := fun v => Real.exp (b v + Real.log δ) + ∑ k, Complex.normSq (s k i (φ.symm v))
  have hwC : ∀ k, ContDiffAt ℂ 2 (w k i ∘ φ.symm) v0 := fun k =>
    contDiffAt_two_of_holo φ.open_target (A.holo_chart (hD.sec_w k) i) hv0
  have hsC : ∀ k, ContDiffAt ℂ 2 (s k i ∘ φ.symm) v0 := fun k =>
    contDiffAt_two_of_holo φ.open_target (A.holo_chart (hD.sec_s k) i) hv0
  have ha : ContDiffAt ℝ 2 a v0 :=
    (((A.smooth_ph (la - n • L) i).add (hps1 i)).contDiffAt hT).of_le (by norm_cast)
  have hb : ContDiffAt ℝ 2 b v0 := ((A.smooth_ph L i).contDiffAt hT).of_le (by norm_cast)
  have hW0 : 0 < W v0 := by
    have h := A.aap_sqn_pos hD y
    rw [A.sqn_chart L w hD.sec_w i hy] at h
    have h2 : 0 < ∑ k, ‖w k i y‖ ^ 2 := pos_of_mul_pos_left h (Real.exp_pos _).le
    simpa [W, hsy, Complex.normSq_eq_norm_sq] using h2
  have hS0 : 0 < Sv v0 := by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (s k i (φ.symm v0))
    have := Real.exp_pos (b v0 + Real.log δ); simp only [Sv]; linarith
  have hWC : ContDiffAt ℝ 2 W v0 := ContDiffAt.sum fun k _ => contDiffAt_normSq_comp (hwC k)
  have hbd : ContDiffAt ℝ 2 (fun v => b v + Real.log δ) v0 := hb.add contDiffAt_const
  have hSC : ContDiffAt ℝ 2 Sv v0 :=
    (Real.contDiff_exp.contDiffAt.comp v0 hbd).add
      (ContDiffAt.sum fun k _ => contDiffAt_normSq_comp (hsC k))
  have hlW : ContDiffAt ℝ 2 (fun v => Real.log (W v)) v0 := hWC.log hW0.ne'
  have hlS : ContDiffAt ℝ 2 (fun v => Real.log (Sv v)) v0 := hSC.log hS0.ne'

  have hLW : 0 ≤ (leviV n (fun v => ((Real.log (W v) : ℝ) : ℂ)) v0 ξ).re :=
    leviV_log_sum_nonneg (u := fun k v => Complex.normSq (w k i (φ.symm v)))
      (fun k => contDiffAt_normSq_comp (hwC k)) (fun k => logPshAt_normSq (hwC k)) hW0 ξ
  have hPb : ∀ ζ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((b v + Real.log δ : ℝ) : ℂ)) v0 ζ).re := by
    intro ζ
    have h1 : (fun v => ((b v + Real.log δ : ℝ) : ℂ)) = fun v => ((1 * b v + Real.log δ : ℝ) : ℂ) := by
      simp
    rw [h1, leviV_const_mul hb, Complex.ofReal_one, one_mul]
    have h2 := hPosL i y hy ζ
    simpa [leviAt] using h2
  have hLS : 0 ≤ (leviV n (fun v => ((Real.log (Sv v) : ℝ) : ℂ)) v0 ξ).re := by
    set u : Fin (n + 1) → V n → ℝ :=
      Fin.cons (fun v => Real.exp (b v + Real.log δ)) (fun k v => Complex.normSq (s k i (φ.symm v)))
    have hsum : (fun v => ((Real.log (Sv v) : ℝ) : ℂ)) = fun v => ((Real.log (∑ j, u j v) : ℝ) : ℂ) := by
      funext v; simp [u, Sv, Fin.sum_univ_succ]
    rw [hsum]
    refine leviV_log_sum_nonneg (fun j => ?_) (fun j => ?_) ?_ ξ
    · cases j using Fin.cases with
      | zero => exact Real.contDiff_exp.contDiffAt.comp v0 hbd
      | succ k => exact contDiffAt_normSq_comp (hsC k)
    · cases j using Fin.cases with
      | zero => exact logPshAt_exp hbd hPb
      | succ k => exact logPshAt_normSq (hsC k)
    · have : (∑ j, u j v0) = Sv v0 := by simp [u, Sv, Fin.sum_univ_succ]
      rw [this]; exact hS0

  have hev : (fun v => ((A.ph la i (φ.symm v) + A.psD L w s ps1 η δ (φ.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 v0]
      fun v => ((a v + ((-η) * b v + 0) + (η * Real.log (W v) + 0) + (n * Real.log (Sv v) + 0) : ℝ) : ℂ) := by
    filter_upwards [hT] with v hv
    have hx := φ.map_target hv
    have hWv : A.sqn L w (φ.symm v) = W v * Real.exp (-b v) := by
      rw [A.sqn_chart L w hD.sec_w i hx]; simp [W, b, Complex.normSq_eq_norm_sq]
    have hSv : A.sqn L s (φ.symm v) + δ = Real.exp (-b v) * Sv v := by
      rw [A.sqn_chart L s hD.sec_s i hx]
      simp only [Sv, b, Complex.normSq_eq_norm_sq, mul_add, Real.exp_add, Real.exp_log hδ]
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]; ring
    have hWp : 0 < W v := by
      have h := A.aap_sqn_pos hD (φ.symm v); rw [hWv] at h
      exact pos_of_mul_pos_left h (Real.exp_pos _).le
    have hSp : 0 < Sv v := by
      have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (s k i (φ.symm v))
      have := Real.exp_pos (b v + Real.log δ); simp only [Sv]; linarith
    unfold psD
    rw [hWv, hSv, Real.log_mul hWp.ne' (Real.exp_pos _).ne', Real.log_mul (Real.exp_pos _).ne' hSp.ne',
      Real.log_exp, A.ph_eq_sub_nsmul la L n i hx]
    simp only [a, b]; push_cast; ring
  set u4 : Fin 4 → V n → ℝ := ![a, fun v => (-η) * b v + 0,
      fun v => η * Real.log (W v) + 0, fun v => n * Real.log (Sv v) + 0]
  have hu4 : ∀ j, ContDiffAt ℝ 2 (u4 j) v0 := by
    intro j
    fin_cases j
    · exact ha
    · exact (contDiffAt_const.mul hb).add contDiffAt_const
    · exact (contDiffAt_const.mul hlW).add contDiffAt_const
    · exact (contDiffAt_const.mul hlS).add contDiffAt_const
  have hfun : (fun v => ((a v + ((-η) * b v + 0) + (η * Real.log (W v) + 0) +
      (n * Real.log (Sv v) + 0) : ℝ) : ℂ)) = fun v => ((∑ j, u4 j v : ℝ) : ℂ) := by
    funext v; simp [u4, Fin.sum_univ_four]
  have hL := hLevi i y hy ξ
  unfold leviAt at hL ⊢
  rw [leviV_congr hev, hfun, leviV_ofReal_sum hu4, Fin.sum_univ_four]
  have e1 : u4 0 = a := rfl
  have e2 : u4 1 = fun v => (-η) * b v + 0 := rfl
  have e3 : u4 2 = fun v => η * Real.log (W v) + 0 := rfl
  have e4 : u4 3 = fun v => n * Real.log (Sv v) + 0 := rfl
  rw [e1, e2, e3, e4, leviV_const_mul hb, leviV_const_mul hlW, leviV_const_mul hlS]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := mul_nonneg hη.le hLW
  have := mul_nonneg hn0 hLS
  change η * (leviV n (fun v => ((b v : ℝ) : ℂ)) v0 ξ).re ≤ _
  change 2 * η * (leviV n (fun v => ((b v : ℝ) : ℂ)) v0 ξ).re ≤ (leviV n (fun v => ((a v : ℝ) : ℂ)) v0 ξ).re at hL
  linarith

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeB
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

theorem aprb_complement {n d : ℕ} (Lm : V n →L[ℂ] V d) (hs : Function.Surjective Lm) :
    ∃ A : V n ≃L[ℂ] V d × V (n - d), ∀ v, (A v).1 = Lm v := by
  classical
  let K := LinearMap.ker (Lm : V n →ₗ[ℂ] V d)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl K
  let P : V n →ₗ[ℂ] K := Submodule.linearProjOfIsCompl K C hC
  have hrank : Module.finrank ℂ (V d) + Module.finrank ℂ K = Module.finrank ℂ (V n) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Lm : V n →ₗ[ℂ] V d)
    rwa [LinearMap.range_eq_top.mpr hs, finrank_top] at h1
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hrank
  have hK : Module.finrank ℂ K = n - d := by omega
  let eK : K ≃ₗ[ℂ] V (n - d) := LinearEquiv.ofFinrankEq K (V (n - d)) (by rw [hK]; simp)
  let T : V n →ₗ[ℂ] V d × V (n - d) := LinearMap.prod (Lm : V n →ₗ[ℂ] V d) (eK.toLinearMap ∘ₗ P)
  have hT : Function.Injective T := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun v hv => ?_)
    have h1 : Lm v = 0 := by simpa [T] using congrArg Prod.fst hv
    have h2 : P v = 0 := by simpa [T] using congrArg Prod.snd hv
    have hvK : v ∈ K := by simpa [K] using h1
    have h3 := Submodule.linearProjOfIsCompl_apply_left hC ⟨v, hvK⟩
    have h4 : (⟨v, hvK⟩ : K) = 0 := h3.symm.trans h2
    simpa using congrArg Subtype.val h4
  have hdim : Module.finrank ℂ (V n) = Module.finrank ℂ (V d × V (n - d)) := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    omega
  refine ⟨(LinearMap.linearEquivOfInjective T hT hdim).toContinuousLinearEquiv, fun v => ?_⟩
  rfl

theorem aprb_contDiffOn {n d : ℕ} {U : Set (V n)} (hU : IsOpen U) {p : V n → V d}
    (hp : DifferentiableOn ℂ p U) (k : ℕ) : ContDiffOn ℂ k p U := by
  rw [contDiffOn_euclidean]
  intro i
  have h1 : DifferentiableOn ℂ (fun x => p x i) U :=
    (EuclideanSpace.proj i : V d →L[ℂ] ℂ).differentiable.comp_differentiableOn hp
  exact (contDiffOn_of_differentiableOn n _ U hU h1).of_le (by exact_mod_cast le_top)

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeI
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ap_lintegral_chart (A : WeightedAtlas n Y ι La) (i : ι) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y in (A.chart i).source, g y ∂A.mu =
      ∫⁻ v in (A.chart i).target, g ((A.chart i).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) := by
  have htm : MeasurableSet (A.chart i).target := (A.chart i).open_target.measurableSet
  have hsm : MeasurableSet (A.chart i).source := (A.chart i).open_source.measurableSet
  have hsymm : AEMeasurable (A.chart i).symm (volume.restrict (A.chart i).target) :=
    (A.chart i).continuousOn_symm.aemeasurable htm
  have hρm : AEMeasurable (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))
      (volume.restrict (A.chart i).target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)).aemeasurable htm
  have hsymm' : AEMeasurable (A.chart i).symm ((volume.restrict (A.chart i).target).withDensity
      (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmeas : A.mu.restrict (A.chart i).source = Measure.map (A.chart i).symm
      ((volume.restrict (A.chart i).target).withDensity
        (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))) := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.map_apply_of_aemeasurable hsymm' hs,
      withDensity_apply' _ _, Measure.restrict_restrict' htm,
      A.mu_chart i _ (hs.inter hsm) Set.inter_subset_right, Set.inter_comm s (A.chart i).source,
      (A.chart i).image_source_inter_eq', Set.inter_comm (A.chart i).target]
  rw [hmeas, lintegral_map' hg.aemeasurable hsymm']
  refine (lintegral_withDensity_eq_lintegral_mul₀ hρm (hg.comp_aemeasurable hsymm)).trans
    (lintegral_congr fun v => ?_)
  simp only [Pi.mul_apply, Function.comp]
  ring

theorem ap_mu_compact (A : WeightedAtlas n Y ι La) (K : Set Y) (hK : IsCompact K) :
    A.mu K < ⊤ := by
  refine hK.measure_lt_top_of_nhdsWithin fun y _ => ?_
  set e := A.chart (A.pick y) with he
  have hys : y ∈ e.source := A.mem_pick y
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hys)
  have hδ : 0 < ε / 2 := by positivity
  have hcb : Metric.closedBall (e y) (ε / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hSo : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)) :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  have hyS : y ∈ e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2) := ⟨hys, Metric.mem_ball_self hδ⟩
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2),
    mem_nhdsWithin_of_mem_nhds (hSo.mem_nhds hyS), ?_⟩
  rw [A.mu_chart _ _ hSo.measurableSet Set.inter_subset_left]
  have himg : e '' (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)) ⊆ Metric.closedBall (e y) (ε / 2) := by
    rintro _ ⟨x, hx, rfl⟩
    exact Metric.ball_subset_closedBall hx.2
  have hcont : ContinuousOn (fun v => Real.exp (A.ph A.kap (A.pick y) (e.symm v)))
      (Metric.closedBall (e y) (ε / 2)) :=
    (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap (A.pick y)).continuousOn).mono hcb
  obtain ⟨M, hM⟩ := (isCompact_closedBall (e y) (ε / 2)).exists_bound_of_continuousOn hcont
  calc _ ≤ ∫⁻ v in Metric.closedBall (e y) (ε / 2),
          ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) (e.symm v))) := lintegral_mono_set himg
    _ ≤ ∫⁻ v in Metric.closedBall (e y) (ε / 2), ENNReal.ofReal M := by
        apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
        intro v hv
        apply ENNReal.ofReal_le_ofReal
        have h1 := hM v hv
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
        exact h1
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

theorem api_contOn_chart {E : Type*} [TopologicalSpace E] (A : WeightedAtlas n Y ι La)
    (φ : Y → E) {U : Set Y} (hU : IsOpen U)
    (h : ∀ i, ContinuousOn (φ ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) :
    ContinuousOn φ U := by
  intro x hx
  set e := A.chart (A.pick x) with he
  have hxs : x ∈ e.source := A.mem_pick x
  have hex : e x ∈ e.target := e.map_source hxs
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hmem : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨hex, ?_⟩
    show e.symm (e x) ∈ U
    rw [e.left_inv hxs]
    exact hx
  have h1 : ContinuousAt (φ ∘ e.symm) (e x) :=
    (h (A.pick x)).continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((φ ∘ e.symm) ∘ e) x := h1.comp (e.continuousAt hxs)
  have h3 : (φ ∘ e.symm) ∘ e =ᶠ[𝓝 x] φ := by
    filter_upwards [e.eventually_left_inverse hxs] with y hy
    simp [hy]
  exact (h2.congr h3).continuousWithinAt

theorem api_nsq_eq (A : WeightedAtlas n Y ι La) {la : La} {U : Set Y} {F : ι → Y → ℂ}
    (hFs : A.IsSecOn la U F) {i : ι} {x : Y}
    (hxs : x ∈ (A.chart i).source) (hxU : x ∈ U) :
    ‖F i x‖ ^ 2 * Real.exp (-A.ph la i x) = A.nsq la F x := by
  unfold WeightedAtlas.nsq
  have hj : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
  have hsec := hFs.2 i (A.pick x) x hxU hxs hj
  have hph := A.ph_trans la i (A.pick x) x hxs hj
  have hg := A.g_ne la i (A.pick x) x hxs hj
  have hgpos : 0 < ‖A.g la i (A.pick x) x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hg) 2
  rw [hsec, hph, norm_mul, mul_pow,
    show -(A.ph la i x - Real.log (‖A.g la i (A.pick x) x‖ ^ 2)) =
      Real.log (‖A.g la i (A.pick x) x‖ ^ 2) + -A.ph la i x by ring,
    Real.exp_add, Real.exp_log hgpos]
  ring

theorem api_nsq_contOn (A : WeightedAtlas n Y ι La) {la : La} {U : Set Y} (hU : IsOpen U)
    {F : ι → Y → ℂ} (hFs : A.IsSecOn la U F) : ContinuousOn (A.nsq la F) U := by
  apply api_contOn_chart A _ hU
  intro i
  set e := A.chart i with he
  have hF : ContinuousOn (F i ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) := (hFs.1 i).continuousOn
  have hph : ContinuousOn (A.ph la i ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) :=
    (A.smooth_ph la i).continuousOn.mono Set.inter_subset_left
  have hc : ContinuousOn (fun v => ‖F i (e.symm v)‖ ^ 2 * Real.exp (-A.ph la i (e.symm v)))
      (e.target ∩ e.symm ⁻¹' U) :=
    (hF.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  refine hc.congr ?_
  intro v hv
  exact (api_nsq_eq A hFs (e.map_target hv.1) hv.2).symm

end

end ReciprocityTheory.L2DbarEstimates.Y
end

