import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCentredDiscCoverCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Matrix

noncomputable section

theorem centredDiscCover_punctured_branch (hPCC : PuncturedCoverCycles.Statement)
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) :
    ∃ (δ : ℝ) (k : ℕ) (φ : ℂ → σ → ℂ), 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ k ∧
      DifferentiableOn ℂ φ (ball 0 δ \ {0}) ∧ Set.InjOn φ (ball 0 δ \ {0}) ∧
      ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k := by
  obtain ⟨hwY, hN, hmaps, huniq, hcard, -, hsec⟩ := hY
  have hρ : 0 < ρ := dist_nonneg.trans_lt (hmaps hwY)
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let Φ : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ e).toContinuousLinearEquiv
  let L : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
    ContinuousLinearMap.pi fun _ => p.comp (Φ : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ))
  let A : Matrix (Fin (0 + 1)) (Fin (Fintype.card σ)) ℂ :=
    LinearMap.toMatrix' (L : (Fin (Fintype.card σ) → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))
  have hA : ∀ z, A *ᵥ z = fun _ => p (Φ z) := fun z => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hpT : ∀ z, p (w + Φ z) = p w + p (Φ z) := fun z => map_add p w (Φ z)
  have hT : ∀ x, w + Φ (Φ.symm (x - w)) = x := fun x => by simp
  have hone : ∀ (y : Fin (0 + 1) → ℂ) (t : ℂ), t = y 0 → (fun _ => t) = y := fun y t ht => by
    funext i
    rw [show i = 0 from Subsingleton.elim (α := Fin 1) _ _, ht]
  let X : Set (Fin (Fintype.card σ) → ℂ) := {z | w + Φ z ∈ Y ∧ p (Φ z) ≠ 0}
  obtain ⟨m, ord, ψ, δ, hδ, hδ1, hsum, hord, hdiff, hmap, hinj, -, -⟩ :=
    hPCC (Fintype.card σ) 0 N A 0 ρ X hρ rfl
      (fun x hx => by
        rw [hA, dist_zero_right, pi_norm_const]
        refine ⟨?_, hx.2⟩
        have := hmaps hx.1
        rwa [mem_ball, dist_eq_norm, hpT, add_sub_cancel_left] at this)
      (fun y hy hy0 => by
        have hyρ : p w + y 0 ∈ ball (p w) ρ := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
          exact (norm_le_pi_norm y 0).trans_lt (by rwa [dist_zero_right] at hy)
        rw [← hcard _ hyρ (by simpa using hy0), ← ((add_right_injective w).comp Φ.injective).injOn.encard_image]
        congr 1
        ext x
        constructor
        · rintro ⟨z, ⟨⟨hzY, -⟩, hzy⟩, rfl⟩
          refine ⟨hzY, ?_⟩
          rw [Function.comp_apply, hpT, ← congrFun ((hA z).symm.trans hzy) 0]
        · rintro ⟨hxY, hxp⟩
          refine ⟨Φ.symm (x - w), ⟨⟨by rwa [hT], ?_⟩, ?_⟩, hT x⟩
          · simpa [hxp] using hy0
          · rw [hA]
            exact hone y _ (by simp [hxp]))
      (fun x hx => by
        obtain ⟨O₀, V₀, g₀, hO₀, hV₀, hxV₀, hg₀, hpg₀, hYV⟩ :=
          hsec (w + Φ x) hx.1 (by rw [hpT]; simpa using hx.2)
        have hsec' : ∀ z, w + Φ z ∈ Y ∩ V₀ → p w + p (Φ z) ∈ O₀ ∧ g₀ (p w + p (Φ z)) = w + Φ z := by
          intro z hz
          rw [hYV] at hz
          obtain ⟨t, ht, hgt⟩ := hz
          have : t = p w + p (Φ z) := by rw [← hpT, ← hgt, hpg₀ t ht]
          subst this
          exact ⟨ht, hgt⟩
        obtain ⟨hxO, hgx⟩ := hsec' x ⟨hx.1, hxV₀⟩
        refine ⟨{y | p w + y 0 ∈ O₀ ∧ y 0 ≠ 0}, {z | w + Φ z ∈ V₀ ∧ p (Φ z) ≠ 0},
          fun y => Φ.symm (g₀ (p w + y 0) - w),
          (hO₀.preimage (continuous_const.add (continuous_apply 0))).inter
            (isOpen_ne_fun (continuous_apply 0) continuous_const),
          by rw [hA]; exact ⟨hxO, hx.2⟩,
          (hV₀.preimage (continuous_const.add Φ.continuous)).inter
            (isOpen_ne_fun (p.continuous.comp Φ.continuous) continuous_const),
          ⟨hxV₀, hx.2⟩, ?_, by rw [hA]; simp [hgx], fun y hy => ?_, ?_⟩
        · exact Φ.symm.differentiable.comp_differentiableOn
            ((hg₀.comp ((differentiableOn_const _).add (differentiable_apply 0).differentiableOn)
              fun y hy => hy.1).sub_const w)
        · rw [hA]
          refine hone y _ ?_
          simp [hpg₀ _ hy.1]
        · ext z
          constructor
          · rintro ⟨⟨hzY, hz0⟩, hzV, -⟩
            obtain ⟨hzO, hgz⟩ := hsec' z ⟨hzY, hzV⟩
            exact ⟨fun _ => p (Φ z), ⟨hzO, hz0⟩, by simp [hgz]⟩
          · rintro ⟨y, ⟨hyO, hy0⟩, rfl⟩
            have hw : w + Φ (Φ.symm (g₀ (p w + y 0) - w)) = g₀ (p w + y 0) := hT _
            have hp : p (Φ (Φ.symm (g₀ (p w + y 0) - w))) = y 0 := by simp [hpg₀ _ hyO]
            have hmem : g₀ (p w + y 0) ∈ Y ∩ V₀ := by rw [hYV]; exact ⟨_, hyO, rfl⟩
            show (w + Φ (Φ.symm (g₀ (p w + y 0) - w)) ∈ Y ∧ p (Φ (Φ.symm (g₀ (p w + y 0) - w))) ≠ 0) ∧
              (w + Φ (Φ.symm (g₀ (p w + y 0) - w)) ∈ V₀ ∧ p (Φ (Φ.symm (g₀ (p w + y 0) - w))) ≠ 0)
            rw [hw, hp]
            exact ⟨⟨hmem.1, hy0⟩, hmem.2, hy0⟩)
  obtain ⟨b⟩ : Nonempty (Fin m) := by
    rcases m with _ | m
    · simp at hsum
      omega
    · exact ⟨0⟩
  have hpunct : ∀ s ∈ ball (0 : ℂ) δ \ {0},
      (fun _ => s) ∈ ball (0 : Fin (0 + 1) → ℂ) δ ∩ {t | t 0 ≠ 0} := fun s hs =>
    ⟨by rw [mem_ball, dist_zero_right, pi_norm_const]; exact mem_ball_zero_iff.1 hs.1, hs.2⟩
  refine ⟨δ, ord b, fun s => w + Φ (ψ b fun _ => s), hδ, hδ1, hord b, ?_, ?_, fun s hs => ?_⟩
  · exact (differentiableOn_const w).add (Φ.differentiable.comp_differentiableOn
      ((hdiff b).comp (differentiable_pi.2 fun _ => differentiable_id).differentiableOn hpunct))
  · intro s hs s' hs' hss'
    have := hinj b (hpunct s hs) (hpunct s' hs') (Φ.injective (add_left_cancel hss'))
    exact congrFun this 0
  · obtain ⟨hX, hAψ⟩ := hmap b _ (hpunct s hs)
    refine ⟨hX.1, ?_⟩
    rw [hpT]
    have := congrFun ((hA _).symm.trans hAψ) 0
    simp only [Function.update_self] at this
    rw [this]

theorem centredDiscCover_extend_across_centre
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) {δ : ℝ} {k : ℕ} {φ : ℂ → σ → ℂ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 1 ≤ k) (hφd : DifferentiableOn ℂ φ (ball 0 δ \ {0})) (hφi : Set.InjOn φ (ball 0 δ \ {0}))
    (hφY : ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k) :
    ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
      DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) Y := by
  obtain ⟨hwY, -, hmaps, huniq, -, hprop, -⟩ := hY
  have hρ : 0 < ρ := dist_nonneg.trans_lt (hmaps hwY)
  set r := min δ (ρ / 2) with hr
  have hr0 : 0 < r := lt_min hδ (half_pos hρ)
  have hrδ : ball (0 : ℂ) r \ {0} ⊆ ball 0 δ \ {0} :=
    Set.sdiff_subset_sdiff_left (ball_subset_ball (min_le_left _ _))
  have hK : IsCompact {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} :=
    hprop _ (closedBall_subset_ball (half_lt_self hρ)) (isCompact_closedBall _ _)
  have hφK : ∀ s ∈ ball (0 : ℂ) r \ {0}, φ s ∈ {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} := by
    intro s hs
    obtain ⟨hY', hp⟩ := hφY s (hrδ hs)
    refine ⟨hY', ?_⟩
    rw [mem_closedBall, hp, dist_eq_norm, add_sub_cancel_left, norm_pow]
    have h1 : ‖s‖ < r := mem_ball_zero_iff.1 hs.1
    calc ‖s‖ ^ k ≤ ‖s‖ :=
          pow_le_of_le_one (norm_nonneg _) (h1.le.trans ((min_le_left _ _).trans hδ1)) (by omega)
      _ ≤ ρ / 2 := h1.le.trans (min_le_right _ _)
  have hbdd : BddAbove (norm ∘ φ '' (ball 0 r \ {0})) := by
    refine (hK.image continuous_norm).bddAbove.mono ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨φ s, hφK s hs, rfl⟩
  have hF := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hr0) (hφd.mono hrδ) hbdd
  set ℓ := limUnder (𝓝[≠] (0 : ℂ)) φ with hℓdef
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ∈ ball (0 : ℂ) r \ {0} := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds 0 hr0)] with s h1 h2
    exact ⟨h2, h1⟩
  have hlim : Tendsto φ (𝓝[≠] 0) (𝓝 ℓ) := by
    have hc := (hF.continuousOn.continuousAt (ball_mem_nhds 0 hr0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    rw [Function.update_self] at hc
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact Function.update_of_ne hs _ _
  have hℓK : ℓ ∈ {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} :=
    hK.isClosed.mem_of_tendsto hlim (hev.mono hφK)
  have hpℓ : p ℓ = p w := by
    have h1 : Tendsto (fun s => p (φ s)) (𝓝[≠] 0) (𝓝 (p ℓ)) := (p.continuous.tendsto ℓ).comp hlim
    have h2 : Tendsto (fun s : ℂ => p w + s ^ k) (𝓝[≠] 0) (𝓝 (p w)) := by
      have : Tendsto (fun s : ℂ => p w + s ^ k) (𝓝 0) (𝓝 (p w + 0 ^ k)) :=
        (continuous_const.add (continuous_pow k)).tendsto 0
      rw [zero_pow (by omega), add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (h1.congr' ?_) h2
    filter_upwards [hev] with s hs
    exact (hφY s (hrδ hs)).2
  have hℓ : ℓ = w := huniq ℓ hℓK.1 hpℓ
  refine ⟨r, hr0, Function.update φ 0 w, ?_, ?_, Function.update_self _ _ _, ?_⟩
  · rw [← hℓ]
    exact hF
  · have hoff : ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → Function.update φ 0 w s ≠ w := by
      intro s hs h0 heq
      rw [Function.update_of_ne h0] at heq
      have := (hφY s (hrδ ⟨hs, h0⟩)).2
      rw [heq] at this
      exact pow_ne_zero k h0 (by linear_combination -this)
    intro s hs s' hs' hss'
    by_cases h0 : s = 0 <;> by_cases h0' : s' = 0
    · rw [h0, h0']
    · subst h0
      rw [Function.update_self] at hss'
      exact absurd hss'.symm (hoff s' hs' h0')
    · subst h0'
      rw [Function.update_self] at hss'
      exact absurd hss' (hoff s hs h0)
    · rw [Function.update_of_ne h0, Function.update_of_ne h0'] at hss'
      exact hφi (hrδ ⟨hs, h0⟩) (hrδ ⟨hs', h0'⟩) hss'
  · intro s hs
    by_cases h0 : s = 0
    · subst h0
      rw [Function.update_self]
      exact hwY
    · rw [Function.update_of_ne h0]
      exact (hφY s (hrδ ⟨hs, h0⟩)).1

theorem CentredDiscCoverCurve.proof (hPCC : PuncturedCoverCycles.Statement) :
    CentredDiscCoverCurve.Statement := by
  intro σ _ Y w p ρ N hY
  obtain ⟨δ, k, φ, hδ, hδ1, hk, hφd, hφi, hφY⟩ := centredDiscCover_punctured_branch hPCC hY
  exact centredDiscCover_extend_across_centre hY hδ hδ1 hk hφd hφi hφY

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffShape
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology
open scoped ContDiff

noncomputable section

private def cutProfile (k : ℕ) (w : ℝ) : ℝ :=
  if w = 0 then 0 else if 1 ≤ w then 1 else cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1))

private theorem cutStep_small (k : ℕ) {w : ℝ} (h0 : w ≠ 0) (hw : |w| < cutLevel k) :
    cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1)) = 0 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : Real.log w < -Real.exp ((k : ℝ) + 1) := by
    rw [← Real.log_abs, ← Real.log_exp (-Real.exp _)]
    exact Real.log_lt_log (abs_pos.2 h0) hw
  have h2 : (k : ℝ) + 1 < Real.log (-Real.log w) := by
    rw [← Real.log_exp ((k : ℝ) + 1)]
    exact Real.log_lt_log (Real.exp_pos _) (by linarith)
  have h3 : 1 < Real.log (-Real.log w) / ((k : ℝ) + 1) := (one_lt_div hk).2 h2
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem cutStep_large (k : ℕ) {w : ℝ} (hw : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < w)
    (h1 : w < 1) : cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1)) = 1 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hw0 : 0 < w := (Real.exp_pos _).trans hw
  have hl : -Real.exp (((k : ℝ) + 1) / 2) < Real.log w := by
    rw [← Real.log_exp (-Real.exp _)]
    exact Real.log_lt_log (Real.exp_pos _) hw
  have hneg : 0 < -Real.log w := neg_pos.2 (Real.log_neg hw0 h1)
  have h2 : Real.log (-Real.log w) < ((k : ℝ) + 1) / 2 := by
    rw [← Real.log_exp (((k : ℝ) + 1) / 2)]
    exact Real.log_lt_log hneg (by linarith)
  have h3 : Real.log (-Real.log w) / ((k : ℝ) + 1) < 1 / 2 := by
    rw [div_lt_iff₀ hk]; linarith
  exact Real.smoothTransition.one_of_one_le (by linarith)

private theorem cutProfile_contDiffOn (k : ℕ) :
    ContDiffOn ℝ ∞ (cutProfile k) (Set.Ioi (-cutLevel k)) := by
  obtain ⟨hc0, hc1⟩ := cutLevel_mem k
  set c' := Real.exp (-Real.exp (((k : ℝ) + 1) / 2))
  have hc'1 : c' < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _))
  refine (isOpen_Ioi.contDiffOn_iff).2 fun x hx => ?_
  rcases lt_or_ge x (cutLevel k) with hxc | hxc
  ·
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (Set.mem_Ioi.1 hx) hxc] with w hw
    have hwa : |w| < cutLevel k := abs_lt.2 hw
    unfold cutProfile
    split_ifs with h0 h1
    · rfl
    · exact absurd (h1.trans_lt (hw.2.trans hc1)) (lt_irrefl _)
    · exact cutStep_small k h0 hwa
  rcases lt_or_ge c' x with hxc' | hxc'
  ·
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hxc'] with w hw
    have hw0 : 0 < w := (Real.exp_pos _).trans hw
    unfold cutProfile
    split_ifs with h0 h1
    · exact absurd h0 hw0.ne'
    · rfl
    · exact cutStep_large k hw (not_le.1 h1)
  ·
    have hx0 : 0 < x := hc0.trans_le hxc
    have hx1 : x < 1 := hxc'.trans_lt hc'1
    have hform : ContDiffAt ℝ ∞ (fun w => cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1))) x := by
      have hlog : ContDiffAt ℝ ∞ (fun w => Real.log (-Real.log w)) x :=
        ((Real.contDiffAt_log.2 hx0.ne').neg).log (neg_ne_zero.2 (Real.log_neg hx0 hx1).ne)
      exact Real.smoothTransition.contDiffAt.comp x
        (contDiffAt_const.sub (contDiffAt_const.mul (hlog.div_const _)))
    refine hform.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx0 hx1] with w hw
    simp [cutProfile, hw.1.ne', not_le.2 hw.2]

theorem CutOffShape.proof : CutOffShape.Statement := by
  intro m Q
  have hF : ∀ k, logLogCut Q k = cutProfile k ∘ fun y => ‖eval y Q‖ ^ 2 := fun k => rfl
  have hstep : ∀ t, cutStep t ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨fun k => ⟨?_, fun y => ?_, fun y hy => ?_⟩, fun y hy => ?_⟩
  · rw [hF]
    have hw : ContDiff ℝ ∞ fun y : Fin m → ℂ => ‖eval y Q‖ ^ 2 :=
      contDiff_norm_sq ℝ |>.comp
        (((AnalyticOnNhd.eval_mvPolynomial Q).contDiff (n := ∞)).restrict_scalars ℝ)
    exact (cutProfile_contDiffOn k).comp_contDiff hw fun y =>
      (neg_neg_of_pos (cutLevel_mem k).1).trans_le (by positivity)
  · unfold logLogCut; split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hstep _
  · have h1 := (cutLevel_mem k).2
    unfold logLogCut logAbsSq; split_ifs with h0 h1'
    · rfl
    · exact absurd (h1'.trans_lt (hy.trans h1)) (lt_irrefl _)
    · exact cutStep_small k h0 (by rwa [abs_of_nonneg (by positivity)])
  · have hw0 : ‖eval y Q‖ ^ 2 ≠ 0 := by positivity
    by_cases hw1 : 1 ≤ ‖eval y Q‖ ^ 2
    · simp [logLogCut, hw0, hw1]
    refine tendsto_const_nhds.congr' ?_
    set L := Real.log (-Real.log (‖eval y Q‖ ^ 2))
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * |L|)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hk' : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
    have h3 : L / ((k : ℝ) + 1) < 1 / 2 := by
      rw [div_lt_iff₀ hk']; linarith [le_abs_self L]
    simp only [logLogCut, logAbsSq, hw0, hw1, if_false]
    exact (Real.smoothTransition.one_of_one_le (by linarith)).symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDerivationMinorOfDetection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem DerivationMinorOfDetection.proof : DerivationMinorOfDetection.Statement := by
  intro T _ P _ h f hfP hind hdet
  let A := Localization.AtPrime P
  let K := ResidueField A
  let π : T →+* K := (residue A).comp (algebraMap T A)
  have hπ : ∀ x, π x = 0 ↔ x ∈ P := fun x => by
    show residue A (algebraMap T A x) = 0 ↔ x ∈ P
    rw [residue_eq_zero_iff]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff A P x
  let v : Derivation ℤ T T → Fin h → K := fun D i => π (D (f i))
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφv : ∀ w : Fin h → K, φ w = ∑ i, w i * φ (Pi.single i 1) := fun w => by
      conv_lhs => rw [pi_eq_sum_univ w]
      simp only [map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    choose a ha using fun i => residue_surjective (R := A) (φ (Pi.single i 1))
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples P.primeCompl Finset.univ a
    choose b hb using fun i => hs i (Finset.mem_univ i)
    have hπb : ∀ i, π (b i) = π s * φ (Pi.single i 1) := fun i => by
      simp only [π, RingHom.comp_apply, hb i, Algebra.smul_def, map_mul, ha]
    have hsq := hdet (∑ i, b i * f i) (Ideal.sum_mem _ fun i _ => P.mul_mem_left _ (hfP i)) fun D => by
      have h1 : ∑ i, b i * D (f i) ∈ P := by
        have hD : φ (v D) = 0 := hφ (Submodule.subset_span ⟨D, rfl⟩)
        rw [hφv] at hD
        rw [← hπ, map_sum]
        simp only [map_mul, hπb]
        rw [show ∑ i, π s * φ (Pi.single i 1) * π (D (f i)) = π s * ∑ i, v D i * φ (Pi.single i 1) by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [v]; ring, hD, mul_zero]
      have hl : ∀ i, D (b i * f i) = b i * D (f i) + f i * D (b i) := fun i => by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      rw [map_sum]
      simp only [hl, Finset.sum_add_distrib]
      exact P.add_mem h1 (Ideal.sum_mem _ fun i _ => P.mul_mem_right _ (hfP i))
    have hbP : ∀ i, b i ∈ P := fun i => (IsLocalization.AtPrime.to_map_mem_maximal_iff A P _).1
      (hind (fun i => algebraMap T A (b i)) (by simpa only [map_sum, map_mul] using hsq) i)
    have hsP : π s ≠ 0 := fun h0 => s.2 ((hπ s).1 h0)
    have he : ∀ i, φ (Pi.single i 1) = 0 := fun i => by
      have := (hπ (b i)).2 (hbP i)
      rw [hπb] at this
      exact (mul_eq_zero.1 this).resolve_left hsP
    exact hφ0 (LinearMap.ext fun w => by simp [hφv w, he])
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent'.{0} K v
  let bas := Module.Basis.mk hli (by rw [hsp, hspan])
  have hfin : Finite κ := Module.Finite.finite_basis bas
  have hκ : Nat.card κ = h := by rw [← Module.finrank_eq_nat_card_basis bas, Module.finrank_fin_fun]
  let e : Fin h ≃ κ := (finCongr hκ.symm).trans (Finite.equivFin κ).symm
  refine ⟨fun j => a (e j), fun hmem => ?_⟩
  have hunit : IsUnit (Matrix.of fun i j => v (a (e j)) i) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e e.injective
  have hne : π (Matrix.of fun i j => a (e j) (f i)).det ≠ 0 := by
    rw [RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
  exact hne ((hπ _).2 hmem)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGreenFromLelong
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology

theorem GreenFromLelong.proof (hS : FormIntSymm.Statement) (hP : FormIntPos.Statement)
    (hL : FormIntLelong.Statement) (hD : RegConeLimit.Statement)
    (hCh : ChowFormSectionAlgClosed.Statement) : GreenFromLelong.Statement := by
  intro _ _ _ _ _ _ n e h W u u' hW hg hu hu' hadm
  obtain ⟨g, hgc⟩ := hg

  have comps : ∀ v v' : Fin n → ℂ, linForm v ∉ W →
      (∀ W' ∈ (divCycle W v).support, linForm v' ∉ W') →
      Tendsto (fun δ => cycleIntegral h (divCycle W v) e (fsLogReg h v' δ)) (𝓝[>] 0)
        (𝓝 (cycleIntegral h (divCycle W v) e (fsLog h v'))) := by
    intro v v' hv hv'
    obtain ⟨c, -, gW, hgW, -⟩ := hCh ℂ n (e + 1) W g v hW hgc hv
    unfold cycleIntegral
    refine tendsto_finsetSum _ fun W' hW' => ?_
    exact (hD n e h W' v' (DivCyclePrime.proof n W v hW W' hW') ⟨gW W', hgW W' hW'⟩
      (hv' W' hW')).const_mul _
  have hadm' : ∀ W' ∈ (divCycle W u').support, linForm u ∉ W' :=
    ProperSymm.proof n W u u' hW hu hu' hadm
  have hg2 : ∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g := ⟨g, hgc⟩
  have hg1 : ∃ g : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℂ, IsChowForm W (e + 1 + 1) g := ⟨g, hgc⟩
  refine (iterLim_eq_of_monotone
    (T := fun ε δ => formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε) +
      coneIntegral h W (e + 1) (fsLogReg h u δ) + coneIntegral h W (e + 1) (fsLogReg h u' ε))
    (A := fun δ => cycleIntegral h (divCycle W u') e (fsLogReg h u δ) +
      coneIntegral h W (e + 1) (fsLog h u'))
    (B := fun ε => cycleIntegral h (divCycle W u) e (fsLogReg h u' ε) +
      coneIntegral h W (e + 1) (fsLog h u)) ?_ ?_ ?_ ?_ ?_ ?_).symm
  ·
    intro δ hδ ε hε ε' hεε'
    have h1 := hP n e h W u' u δ ε ε' hW hg2 hδ hε hεε'
    rw [← hS n e h W u u' ε δ hW hg2 hε hδ, ← hS n e h W u u' ε' δ hW hg2 (hε.trans_le hεε') hδ] at h1
    linarith
  · intro ε hε δ hδ δ' hδδ'
    have h1 := hP n e h W u u' ε δ δ' hW hg2 hε hδ hδδ'
    linarith
  · intro δ hδ
    have := ((hL n e h W u u' δ hW hg2 hu' hδ).add_const
      (coneIntegral h W (e + 1) (fsLogReg h u δ))).add (hD n (e + 1) h W u' hW hg1 hu')
    convert this using 2
    ring
  · intro ε hε
    have := ((hL n e h W u' u ε hW hg2 hu hε).add (hD n (e + 1) h W u hW hg1 hu)).add_const
      (coneIntegral h W (e + 1) (fsLogReg h u' ε))
    refine Tendsto.congr' ?_ (by convert this using 2; ring)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp only [hS n e h W u u' ε δ hW hg2 hε hδ]
  · exact (comps u' u hu' hadm').add_const _
  · exact (comps u u' hu hadm).add_const _

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreSumInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.AnForm.A

noncomputable section

theorem abs_det_fderiv_real_mul_eq_normSq {d : ℕ} {Ω : Set (Fin d → ℂ)} {τ : (Fin d → ℂ) → Fin d → ℂ}
    (hΩ : IsOpen Ω) (hτ : DifferentiableOn ℂ τ Ω) (H : (Fin d → ℂ) → ℝ) :
    Set.EqOn (fun t => |(fderiv ℝ τ t).det| * H t) (fun t => Complex.normSq (jacC τ t).det * H t) Ω := by
  intro t ht
  simp only
  rw [det_fderiv_real_eq_normSq τ t (hτ.differentiableAt (hΩ.mem_nhds ht)),
    abs_of_nonneg (Complex.normSq_nonneg _)]

theorem HolomorphicFibreSumInt.proof (h : WeightedAreaFormula.Statement) :
    HolomorphicFibreSumInt.Statement := by
  intro d Ω τ H hΩ hτ hfin hint
  have heq := abs_det_fderiv_real_mul_eq_normSq hΩ hτ H
  have hint' : IntegrableOn (fun t => |(fderiv ℝ τ t).det| * H t) Ω :=
    (integrableOn_congr_fun heq hΩ.measurableSet).2 hint
  obtain ⟨h1, h2⟩ := h (Fin d → ℂ) volume Ω τ H hΩ (hτ.restrictScalars ℝ) hfin hint'
  exact ⟨h1, h2.trans (setIntegral_congr_fun hΩ.measurableSet heq)⟩

end

end GroundTheory.Heights₂.Heights
end

