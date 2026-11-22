import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0097
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedBranchSameOrder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

namespace PuncturedBranchSameOrder

theorem const_mem_ball_iff (τ : ℂ) (r : ℝ) :
    (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r ↔ τ ∈ Metric.ball (0 : ℂ) r := by
  simp only [Metric.mem_ball, dist_zero_right, pi_norm_const]

theorem disc_props {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (b : VarBranch I 1 q) :
    DifferentiableOn ℂ (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.InjOn (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.MapsTo (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) (zeroSet I) ∧
    (b.toFun fun _ ↦ (0 : ℂ)) = q ∧
    ∀ x, x ∈ b.image ↔ ∃ σ ∈ Metric.ball (0 : ℂ) b.radius, (b.toFun fun _ ↦ σ) = x := by
  have hι : Differentiable ℂ (fun τ : ℂ ↦ fun _ : Fin 1 ↦ τ) := differentiable_pi.2 fun _ ↦ differentiable_id
  refine ⟨b.differentiableOn.comp hι.differentiableOn fun τ hτ ↦ (const_mem_ball_iff τ _).2 hτ,
    fun s hs t ht h ↦ congrFun (b.injOn ((const_mem_ball_iff s _).2 hs) ((const_mem_ball_iff t _).2 ht) h) 0,
    fun τ hτ ↦ b.mapsTo ((const_mem_ball_iff τ _).2 hτ), b.map_zero, fun x ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht, rfl⟩
    have ht' : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
    refine ⟨t 0, (const_mem_ball_iff _ _).1 ?_, by rw [ht']⟩
    rw [ht']
    exact ht
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, (const_mem_ball_iff σ _).2 hσ, rfl⟩

theorem factor_of_punctured {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {C D : ℂ → E} {ψ : ℂ → ℂ}
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hCd : DifferentiableOn ℂ C (Metric.ball 0 r)) (hCi : Set.InjOn C (Metric.ball 0 r))
    (hDd : DifferentiableOn ℂ D (Metric.ball 0 ρ)) (hDi : Set.InjOn D (Metric.ball 0 ρ)) (h0 : C 0 = D 0)
    (hψd : DifferentiableOn ℂ ψ (Metric.ball 0 ρ \ {0}))
    (hψ : ∀ τ ∈ Metric.ball (0 : ℂ) ρ \ {0}, ψ τ ∈ Metric.ball (0 : ℂ) r ∧ C (ψ τ) = D τ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (∀ᶠ τ in 𝓝 0, D τ = C (g τ)) ∧ 𝓝 0 ≤ map g (𝓝 0) := by
  obtain ⟨g, hg_def⟩ : ∃ g : ℂ → ℂ, g = Function.update ψ 0 (limUnder (𝓝[≠] (0 : ℂ)) ψ) := ⟨_, rfl⟩
  have hB : Metric.ball (0 : ℂ) ρ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hρ
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 ρ) := by
    rw [hg_def]
    refine Complex.differentiableOn_update_limUnder_of_bddAbove hB hψd ⟨r, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    exact (mem_ball_zero_iff.1 (hψ τ hτ).1).le
  have hgψ : ∀ τ, τ ≠ 0 → g τ = ψ τ := fun τ hτ ↦ by rw [hg_def]; exact Function.update_of_ne hτ _ _
  have hgc : ContinuousAt g 0 := (hgd.differentiableAt hB).continuousAt
  have hpunct : ∀ᶠ τ in 𝓝[≠] (0 : ℂ), τ ∈ Metric.ball (0 : ℂ) ρ \ {0} :=
    Filter.mem_of_superset (inter_mem_nhdsWithin _ hB) fun τ h ↦ ⟨h.2, h.1⟩
  have hpt : ∀ s : ℝ, 0 < s → s < ρ → (s : ℂ) ∈ Metric.ball (0 : ℂ) ρ \ {0} := fun s hs hsρ ↦
    ⟨by rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs.le]; exact hsρ, by simpa using hs.ne'⟩
  have hle : ‖g 0‖ ≤ r := by
    refine le_of_tendsto (hgc.norm.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)) ?_
    filter_upwards [hpunct] with τ hτ
    rw [hgψ τ hτ.2]
    exact (mem_ball_zero_iff.1 (hψ τ hτ).1).le
  have hlt : ‖g 0‖ < r := by
    refine lt_of_le_of_ne hle fun heq ↦ ?_
    have hmax : IsMaxOn (norm ∘ g) (Metric.ball 0 ρ) 0 := isMaxOn_iff.2 fun τ hτ ↦ by
      show ‖g τ‖ ≤ ‖g 0‖
      by_cases h : τ = 0
      · rw [h]
      · rw [hgψ τ h, heq]
        exact (mem_ball_zero_iff.1 (hψ τ ⟨hτ, h⟩).1).le
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : ℂ) ρ).isPreconnected
      Metric.isOpen_ball hgd (Metric.mem_ball_self hρ) hmax
    have h1 := hpt (ρ / 2) (by positivity) (by linarith)
    have h2 := hpt (ρ / 4) (by positivity) (by linarith)
    have e1 : D ((ρ / 2 : ℝ) : ℂ) = C (g 0) := by
      rw [← (hψ _ h1).2, ← hgψ _ h1.2]
      exact congrArg C (hconst h1.1)
    have e2 : D ((ρ / 4 : ℝ) : ℂ) = C (g 0) := by
      rw [← (hψ _ h2).2, ← hgψ _ h2.2]
      exact congrArg C (hconst h2.1)
    have := Complex.ofReal_injective (hDi h1.1 h2.1 (e1.trans e2.symm))
    linarith
  have hgr : g 0 ∈ Metric.ball (0 : ℂ) r := mem_ball_zero_iff.2 hlt
  have hCg0 : C (g 0) = D 0 := by
    have hC : ContinuousAt C (g 0) := (hCd.differentiableAt (Metric.isOpen_ball.mem_nhds hgr)).continuousAt
    have hD : ContinuousAt D 0 := (hDd.differentiableAt hB).continuousAt
    refine tendsto_nhds_unique_of_eventuallyEq ((hC.comp hgc).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0))
      (hD.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)) ?_
    filter_upwards [hpunct] with τ hτ
    rw [Function.comp_apply, hgψ τ hτ.2]
    exact (hψ τ hτ).2
  have hg0 : g 0 = 0 := hCi hgr (Metric.mem_ball_self hr) (hCg0.trans h0.symm)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), D τ = C (g τ) := by
    filter_upwards [hB] with τ hτ
    by_cases h : τ = 0
    · rw [h, hCg0]
    · rw [hgψ τ h]
      exact (hψ τ ⟨hτ, h⟩).2.symm
  have hga : AnalyticAt ℂ g 0 := hgd.analyticAt hB
  refine ⟨g, hga, hg0, hev, ?_⟩
  rcases hga.eventually_constant_or_nhds_le_map_nhds with hc | hc
  · exfalso
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 (hc.and hev)
    have hm : 0 < min ε ρ := lt_min hε hρ
    have hs : 0 < min ε ρ / 2 := half_pos hm
    have hsε : min ε ρ / 2 < ε := by have := min_le_left ε ρ; linarith
    have hsρ : min ε ρ / 2 < ρ := by have := min_le_right ε ρ; linarith
    have h1 := hpt _ hs hsρ
    obtain ⟨hgc1, hD1⟩ := hεb (by rw [dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hs.le]; exact hsε)
    exact h1.2 (hDi h1.1 (Metric.mem_ball_self hρ) (by rw [hD1, hgc1, hg0, h0]))
  · rwa [hg0] at hc

theorem punctured_factor (hcut : PuncturedCurveDiscInverse.Statement) {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    {q : Fin n → ℂ} (hI : IsRadicalAt I q) (hdim : ringKrullDim (curveLocalRing I q) = 1) (c d : VarBranch I 1 q)
    (ρ : ℝ) (hρ : 0 < ρ) (hcd : ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → d.toFun (fun _ ↦ τ) ∈ c.image) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (∀ᶠ τ in 𝓝 0, (d.toFun fun _ ↦ τ) = c.toFun fun _ ↦ g τ) ∧
      𝓝 0 ≤ map g (𝓝 0) := by
  obtain ⟨hCd, hCi, hCm, hC0, hCim⟩ := disc_props c
  obtain ⟨hDd, hDi, hDm, hD0, -⟩ := disc_props d
  obtain ⟨ε, hε, hcutε⟩ := hcut n I q hI hdim
  have hDc : ContinuousAt (fun τ : ℂ ↦ d.toFun fun _ ↦ τ) 0 :=
    (hDd.differentiableAt (Metric.ball_mem_nhds 0 d.radius_pos)).continuousAt
  obtain ⟨ρ₁, hρ₁, hρ₁ε⟩ := Metric.continuousAt_iff.1 hDc ε hε
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℝ, ρ' = min (min ρ ρ₁) d.radius := ⟨_, rfl⟩
  have hρ'pos : 0 < ρ' := hρ' ▸ lt_min (lt_min hρ hρ₁) d.radius_pos
  have hρ'ρ : ρ' ≤ ρ := hρ' ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hρ'1 : ρ' ≤ ρ₁ := hρ' ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hsub : Metric.ball (0 : ℂ) ρ' ⊆ Metric.ball 0 d.radius := Metric.ball_subset_ball (hρ' ▸ min_le_right _ _)
  let ψ : ℂ → ℂ := fun τ ↦
    Function.invFunOn (fun σ : ℂ ↦ c.toFun fun _ ↦ σ) (Metric.ball 0 c.radius) (d.toFun fun _ ↦ τ)
  have hψ : ∀ τ ∈ Metric.ball (0 : ℂ) ρ' \ {0},
      ψ τ ∈ Metric.ball (0 : ℂ) c.radius ∧ (c.toFun fun _ ↦ ψ τ) = d.toFun fun _ ↦ τ := by
    intro τ hτ
    have hex := (hCim _).1 (hcd τ (norm_pos_iff.2 hτ.2) (lt_of_lt_of_le (mem_ball_zero_iff.1 hτ.1) hρ'ρ))
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hopen : IsOpen (Metric.ball (0 : ℂ) ρ' \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hψd : DifferentiableOn ℂ ψ (Metric.ball 0 ρ' \ {0}) := by
    intro τ₀ hτ₀
    obtain ⟨hσ₀r, hσ₀⟩ := hψ τ₀ hτ₀
    have hδ : 0 < c.radius - ‖ψ τ₀‖ := sub_pos.2 (mem_ball_zero_iff.1 hσ₀r)
    have hballsub : Metric.ball (ψ τ₀) (c.radius - ‖ψ τ₀‖) ⊆ Metric.ball 0 c.radius :=
      Metric.ball_subset_ball' (by rw [dist_zero_right]; linarith)
    have hne : (d.toFun fun _ ↦ τ₀) ≠ q := fun h ↦
      hτ₀.2 (hDi (hsub hτ₀.1) (Metric.mem_ball_self d.radius_pos) (h.trans hD0.symm))
    have hε₀ : (d.toFun fun _ ↦ τ₀) ∈ Metric.ball q ε := by
      have := hρ₁ε (x := τ₀) (by rw [dist_zero_right]; exact lt_of_lt_of_le (mem_ball_zero_iff.1 hτ₀.1) hρ'1)
      rw [Metric.mem_ball]
      rwa [hD0] at this
    obtain ⟨U, hUo, hUx, Ψ, hΨd, hΨ⟩ := hcutε (fun σ ↦ c.toFun fun _ ↦ σ) (ψ τ₀) (c.radius - ‖ψ τ₀‖) hδ
      (hCd.mono hballsub) (hCi.mono hballsub) (fun σ hσ ↦ hCm (hballsub hσ))
      (by show (c.toFun fun _ ↦ ψ τ₀) ∈ Metric.ball q ε; rw [hσ₀]; exact hε₀)
      (by show (c.toFun fun _ ↦ ψ τ₀) ≠ q; rw [hσ₀]; exact hne)
    have hUD : (d.toFun fun _ ↦ τ₀) ∈ U := by
      have hUx' : (c.toFun fun _ ↦ ψ τ₀) ∈ U := hUx
      rwa [hσ₀] at hUx'
    have hDdiff : DifferentiableAt ℂ (fun τ : ℂ ↦ d.toFun fun _ ↦ τ) τ₀ :=
      hDd.differentiableAt (Metric.isOpen_ball.mem_nhds (hsub hτ₀.1))
    have hevU : ∀ᶠ τ in 𝓝 τ₀, (d.toFun fun _ ↦ τ) ∈ U :=
      hDdiff.continuousAt.preimage_mem_nhds (hUo.mem_nhds hUD)
    have heq : ψ =ᶠ[𝓝 τ₀] fun τ ↦ Ψ (d.toFun fun _ ↦ τ) := by
      filter_upwards [hevU, hopen.mem_nhds hτ₀] with τ hτU hτ
      obtain ⟨σ, hσ, hσz, hΨσ⟩ := hΨ (d.toFun fun _ ↦ τ) ⟨hDm (hsub hτ.1), hτU⟩
      rw [hΨσ]
      exact hCi (hψ τ hτ).1 (hballsub hσ) ((hψ τ hτ).2.trans hσz.symm)
    have hdiff : DifferentiableAt ℂ (fun τ ↦ Ψ (d.toFun fun _ ↦ τ)) τ₀ :=
      (hΨd.differentiableAt (hUo.mem_nhds hUD)).comp τ₀ hDdiff
    exact (hdiff.congr_of_eventuallyEq heq).differentiableWithinAt
  exact factor_of_punctured (C := fun σ : ℂ ↦ c.toFun fun _ ↦ σ) (D := fun τ : ℂ ↦ d.toFun fun _ ↦ τ)
    c.radius_pos hρ'pos hCd hCi (hDd.mono hsub) (hDi.mono hsub) (hC0.trans hD0.symm) hψd hψ

end PuncturedBranchSameOrder

theorem PuncturedBranchSameOrder.proof (hcut : PuncturedCurveDiscInverse.Statement) :
    PuncturedBranchSameOrder.Statement := by
  intro n I q c d ρ hI hdim hρ hcd f
  obtain ⟨g, hga, hg0, hev, hmap⟩ := PuncturedBranchSameOrder.punctured_factor hcut hI hdim c d ρ hρ hcd
  have hBd : Metric.ball (0 : ℂ) d.radius ∈ 𝓝 0 := Metric.ball_mem_nhds 0 d.radius_pos
  have hdc : ∃ ρ'' > 0, ∀ σ : ℂ, 0 < ‖σ‖ → ‖σ‖ < ρ'' → c.toFun (fun _ ↦ σ) ∈ d.image := by
    have hA : {τ : ℂ | τ ∈ Metric.ball 0 d.radius ∧ (d.toFun fun _ ↦ τ) = c.toFun fun _ ↦ g τ} ∈ 𝓝 0 :=
      Filter.Eventually.and hBd hev
    obtain ⟨ρ'', hρ'', hball⟩ := Metric.mem_nhds_iff.1 (hmap (Filter.image_mem_map hA))
    refine ⟨ρ'', hρ'', fun σ _ hσ ↦ ?_⟩
    obtain ⟨τ, ⟨hτd, hτeq⟩, rfl⟩ := hball (mem_ball_zero_iff.2 hσ)
    exact ((PuncturedBranchSameOrder.disc_props d).2.2.2.2 _).2 ⟨τ, hτd, hτeq⟩
  obtain ⟨ρ'', hρ'', hdc'⟩ := hdc
  obtain ⟨k, hka, hk0, hev', -⟩ := PuncturedBranchSameOrder.punctured_factor hcut hI hdim d c ρ'' hρ'' hdc'
  have hgt : Tendsto g (𝓝 0) (𝓝 0) := by
    have := hga.continuousAt.tendsto
    rwa [hg0] at this
  have hkt : Tendsto k (𝓝 0) (𝓝 0) := by
    have := hka.continuousAt.tendsto
    rwa [hk0] at this
  have hid : (fun τ ↦ k (g τ)) =ᶠ[𝓝 0] id := by
    filter_upwards [hgt.eventually hev', (hkt.comp hgt).eventually hBd, hev, hBd] with τ h1 h2 h3 h4
    exact (PuncturedBranchSameOrder.disc_props d).2.1 h2 h4 (h1.symm.trans h3.symm)
  have hgd : deriv g 0 ≠ 0 := by
    intro hz
    have hk' : HasDerivAt k (deriv k 0) (g 0) := by
      rw [hg0]
      exact hka.differentiableAt.hasDerivAt
    have e1 : HasDerivAt (fun τ ↦ k (g τ)) (deriv k 0 * deriv g 0) 0 :=
      hk'.comp 0 hga.differentiableAt.hasDerivAt
    have e2 : HasDerivAt (fun τ ↦ k (g τ)) 1 0 := (hasDerivAt_id 0).congr_of_eventuallyEq hid
    have := e1.unique e2
    rw [hz, mul_zero] at this
    exact zero_ne_one this
  have hcong : (fun τ : ℂ ↦ eval (d.toFun fun _ ↦ τ) f) =ᶠ[𝓝 0]
      (fun σ : ℂ ↦ eval (c.toFun fun _ ↦ σ) f) ∘ g := by
    filter_upwards [hev] with τ hτ
    rw [Function.comp_apply, hτ]
  show analyticOrderAt (fun τ : ℂ ↦ eval (c.toFun fun _ ↦ τ) f) 0 =
    analyticOrderAt (fun τ : ℂ ↦ eval (d.toFun fun _ ↦ τ) f) 0
  rw [analyticOrderAt_congr hcong, analyticOrderAt_comp_of_deriv_ne_zero hga hgd, hg0]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegBallMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegBallMass

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem chartDens_indicator_mono (hN : RegDensNonneg.Statement) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S S' : Set (Fin n → ℂ)} (hS : S ⊆ S') (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ∧
      chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ≤
        chartDens J A (S'.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  have key : ∀ x ∈ fibre J A y, ∀ h : ∃ s, IsSheetAt J A x s,
      0 ≤ ReciprocityTheory.AnForm.maDens (fun k => (vecCons (logReg u ε) fun _ => euclPot :
        Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ h.choose) y := by
    intro x hx h
    have := hN n d J A u ε x h.choose hε h.choose_spec
    rwa [hx.2] at this
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  constructor
  · refine Finset.sum_nonneg fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (key x hx h)
    · exact le_rfl
  · refine Finset.sum_le_sum fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right
        (Set.indicator_le_indicator_of_subset hS (fun _ => zero_le_one) x) (key x hx h)
    · exact le_rfl

theorem measurable_chartDens_indicator (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ)) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) :
    Measurable (chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot)) := by
  refine (SheetSumMeasurable.proof n (d + 1) J A _ _ hJ hdim hA (measurable_const.indicator hS)
    fun k => ?_).1
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
  · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_euclPot n)

end RegBallMass

open RegBallMass in

theorem RegBallMass.proof (hF : RegFixedBallMass.Statement) (hM : RegLelongMono.Statement)
    (hN : RegDensNonneg.Statement) : RegBallMass.Statement := by
  intro n d J A u K hJ hdim hA hu hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  set c : ℝ := Real.sqrt (n + 1) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  obtain ⟨M, hMb⟩ := hF n d J A u (R₀ + c) hJ hdim hA hu
  refine ⟨max M 0, le_max_right _ _, fun ε hε x hx r hr => ?_⟩
  set F : Set (Fin n → ℂ) → (Fin (d + 1) → ℂ) → ℝ := fun S =>
    chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) with hFdef
  have h1 : Metric.ball x r ⊆ euclBall x (c * r) := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hr.1] at hy
    show Real.sqrt (euclPot (y - x)) < c * r
    rw [Real.sqrt_lt' (mul_pos hc0 hr.1), mul_pow, hc2]
    calc euclPot (y - x) = ∑ j, ‖(y - x) j‖ ^ 2 := rfl
      _ ≤ ∑ _j : Fin n, r ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hy j).le 2
      _ = n * r ^ 2 := by simp
      _ < (n + 1) * r ^ 2 := by nlinarith [pow_pos hr.1 2]
  have h2 : euclBall x c ⊆ Metric.closedBall 0 (R₀ + c) := by
    intro y hy
    have hy' : euclPot (y - x) < c ^ 2 := (Real.sqrt_lt' hc0).1 hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hyx : ‖y - x‖ ≤ c := by
      refine (pi_norm_le_iff_of_nonneg hc0.le).2 fun j => ?_
      have hj : ‖(y - x) j‖ ^ 2 ≤ euclPot (y - x) :=
        Finset.single_le_sum (f := fun j => ‖(y - x) j‖ ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc0.le two_ne_zero).1 (by linarith)
    calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ R₀ + c := add_le_add (hR₀ x hx) hyx
  have h3 : euclBall x (c * r) ⊆ euclBall x c := fun y hy =>
    show Real.sqrt (euclPot (y - x)) < c from
      lt_of_lt_of_le (show Real.sqrt (euclPot (y - x)) < c * r from hy)
        (mul_le_of_le_one_right hc0.le hr.2)
  have hpos : ∀ {S S' : Set (Fin n → ℂ)}, S ⊆ S' → ∀ y, 0 ≤ F S y ∧ F S y ≤ F S' y :=
    fun hS y => chartDens_indicator_mono hN hA u hε.1 hS y
  have hEm : ∀ ρ, MeasurableSet (euclBall x ρ) := fun ρ =>
    (isOpen_lt (((contDiff_euclPot n).continuous.comp
      (continuous_id.sub continuous_const)).sqrt) continuous_const).measurableSet
  obtain ⟨hIR, hIRle⟩ := hMb ε hε
  have hint : ∀ S, MeasurableSet S → S ⊆ Metric.closedBall 0 (R₀ + c) → Integrable (F S) :=
    fun S hS hSR => hIR.mono' (measurable_chartDens_indicator hJ hdim hA u hε.1 hS).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpos hSR y).1]; exact (hpos hSR y).2)
  have hBI := hint _ Metric.isOpen_ball.measurableSet (h1.trans (h3.trans h2))
  refine ⟨hBI, ?_⟩
  have hmono := hM n d J A u ε x (c * r) c hJ hdim hA hε.1 (mul_pos hc0 hr.1)
    (mul_le_of_le_one_right hc0.le hr.2)
  have hI1 : ∫ y, F (Metric.ball x r) y ≤ ∫ y, F (euclBall x (c * r)) y :=
    integral_mono hBI (hint _ (hEm _) (h3.trans h2)) fun y => (hpos h1 y).2
  have hI2 : ∫ y, F (euclBall x c) y ≤ ∫ y, F (Metric.closedBall 0 (R₀ + c)) y :=
    integral_mono (hint _ (hEm _) h2) hIR fun y => (hpos h2 y).2
  have hI3 : ∫ y, F (euclBall x (c * r)) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := by
    have : c ^ (2 * d) * ∫ y, F (euclBall x (c * r)) y ≤
        c ^ (2 * d) * (r ^ (2 * d) * ∫ y, F (euclBall x c) y) := by
      rw [← mul_assoc, ← mul_pow]; exact hmono
    exact le_of_mul_le_mul_left this (pow_pos hc0 _)
  calc ∫ y, F (Metric.ball x r) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := hI1.trans hI3
    _ ≤ r ^ (2 * d) * max M 0 :=
      mul_le_mul_of_nonneg_left (hI2.trans (hIRle.trans (le_max_left _ _))) (pow_nonneg hr.1.le _)
    _ = max M 0 * r ^ (2 * d) := mul_comm _ _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetComass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace SheetComassAlt

theorem sheetJac_eq_norm_det {n d : ℕ} (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ)
    (hs : DifferentiableAt ℂ s y) :
    sheetJac s y = ‖((ReciprocityTheory.AnForm.A.jacC s y)ᴴ * ReciprocityTheory.AnForm.A.jacC s y).det‖ := by
  set S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
      ((fderiv ℂ s y : (Fin d → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ
        (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).toLinearMap with hS
  have hR : fderiv ℝ s y = (fderiv ℂ s y).restrictScalars ℝ := hs.fderiv_restrictScalars ℝ
  have e : (WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
      ((fderiv ℝ s y : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℝ] (Fin n → ℂ)) ∘ₗ
        (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap = S.restrictScalars ℝ := by
    ext v : 1
    simp [hS, hR]
  rw [sheetJac, e, FrameJacobianSumAlt.areaJacobian_restrictScalars,
    FrameJacobianSumAlt.det_adjoint_comp]
  congr 2
  ext i j
  simp [hS, Matrix.mul_apply, ReciprocityTheory.AnForm.A.jacC, PiLp.inner_apply, mul_comm]

end SheetComassAlt

theorem SheetComass.proof : SheetComass.Statement := by
  intro n d J A φ R hφ
  choose U hUo hZU hφU using hφ
  have hK : IsCompact (zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R) :=
    (isCompact_closedBall (0 : Fin n → ℂ) R).inter_left (SheetSumMeasurable.isClosed_zeroSet J)
  obtain ⟨c, hc, hb⟩ := TubeFormComparison.exists_hessC_bound φ _ hK U hUo
    (fun i => Set.inter_subset_left.trans (hZU i))
    (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  refine ⟨(d.factorial : ℝ) * (2 / Real.pi) ^ d * (3 ^ d * c ^ d), fun x hx s hs => ?_⟩
  obtain ⟨V, hV, hyV, hsd, hsx, -, -⟩ := hs
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hV hsd _ hyV
  have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
    rw [hsx]
    exact ((hφU i).contDiffAt ((hUo i).mem_nhds (hZU i hx.1))).of_le (WithTop.coe_le_coe.2 le_top)
  set Jc := ReciprocityTheory.AnForm.A.jacC s (A *ᵥ x) with hJc
  set B := Jc.map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = Jcᵀ := by
    ext a b
    simp [hB]
  have hA : ∀ i, hessC (φ i ∘ s) (A *ᵥ x) = Bᴴ * hessC (φ i) x * B := fun i => by
    have h := ReciprocityTheory.AnForm.A.hessC_comp (φ i) s _ hsa (hφx i)
    rw [hsx] at h
    rw [hBJ]
    exact h
  have hle : ∀ k, ((fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k -
      (fun k => hessC (φ k ∘ s) (A *ᵥ x)) k).PosSemidef := fun k => by
    have e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC (φ k) x * B =
        Bᴴ * (-hessC (φ k) x + (c : ℂ) • 1) * B := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      abel
    simp only [hA, e]
    exact (hb k x hx).2.conjTranspose_mul_mul_same B
  have hge : ∀ k, ((fun k => hessC (φ k ∘ s) (A *ᵥ x)) k +
      (fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k).PosSemidef := fun k => by
    have e : Bᴴ * hessC (φ k) x * B + (c : ℂ) • (Bᴴ * B) =
        Bᴴ * (hessC (φ k) x + (c : ℂ) • 1) * B := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    simp only [hA, e]
    exact (hb k x hx).1.conjTranspose_mul_mul_same B
  have key := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le _ _ hle hge
  rw [ReciprocityTheory.AnForm.A.mdisc_const, Matrix.det_smul, Fintype.card_fin] at key
  have hconj : Bᴴ * B = (Jcᴴ * Jc).map (starRingEnd ℂ) := by
    rw [hBJ, hB]
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  have hdet : ‖(Bᴴ * B).det‖ = sheetJac s (A *ᵥ x) := by
    have hm : ((Jcᴴ * Jc).map (starRingEnd ℂ)).det = starRingEnd ℂ (Jcᴴ * Jc).det :=
      (RingHom.map_det _ _).symm
    rw [SheetComassAlt.sheetJac_eq_norm_det s _ (hsd.differentiableAt (hV.mem_nhds hyV)), hconj, hm,
      Complex.norm_conj]
  have hre : (((c : ℂ) ^ d * (Bᴴ * B).det).re) ≤ c ^ d * sheetJac s (A *ᵥ x) := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc, hdet]
  have hm : |(mdisc fun k => hessC (φ k ∘ s) (A *ᵥ x)).re| ≤ 3 ^ d * (c ^ d * sheetJac s (A *ᵥ x)) :=
    (Complex.abs_re_le_norm _).trans (key.trans (mul_le_mul_of_nonneg_left hre (by positivity)))
  unfold maDens
  rw [abs_mul, abs_of_nonneg (by positivity), mul_assoc _ (3 ^ d * c ^ d), mul_assoc (3 ^ d)]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def BranchLift.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (M : NormalModel J)
    (γ : GroundTheory.Heights₂.Heights.VarBranch J k p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) →
    ∃ Γ : (Fin k → ℂ) → Fin n ⊕ Fin M.m → ℂ,
      DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) ∧
      (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ τ) = γ.toFun τ) ∧
      ∀ V ⊆ Metric.ball 0 γ.radius, IsOpen V →
        ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ Γ '' V = zeroSetIn M.ideal ∩ O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMParameterQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

def CMParameterQuotient.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (d : ℕ) (x : Fin d → B),
    (∀ i, x i ∈ maximalIdeal B) →
    ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B →
      IsCohenMacaulayLocalRing (B ⧸ Ideal.span (Set.range x))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeBranchDimOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def PrimeBranchDimOne.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch J 1 q),
    J.IsPrime → ringKrullDim (curveLocalRing J q) ≤ 1 →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)

end GroundTheory.Heights₂.Heights
end

