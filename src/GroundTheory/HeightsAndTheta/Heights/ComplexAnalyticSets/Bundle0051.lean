import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolGermPointIdealSpan
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem hadamard_decomposition {σ : Type} [Fintype σ] {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f w) :
    ∃ g : σ → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (g i) w) ∧
      ∀ᶠ z in 𝓝 w, f z = f w + ∑ i, (z i - w i) * g i z := by
  classical
  obtain ⟨p, r, hp⟩ := hf
  have hrad : p.shift.radius = p.radius := FormalMultilinearSeries.radius_shift p
  have hq : 0 < p.shift.radius := by rw [hrad]; exact lt_of_lt_of_le hp.r_pos hp.r_le
  have hG : HasFPowerSeriesOnBall p.shift.sum p.shift 0 p.shift.radius :=
    p.shift.hasFPowerSeriesOnBall hq
  refine ⟨fun i z => p.shift.sum (z - w) (Pi.single i 1), fun i => ?_, ?_⟩
  · have h2 : AnalyticAt ℂ (fun z : σ → ℂ => z - w) w := analyticAt_id.sub analyticAt_const
    have h3 : AnalyticAt ℂ p.shift.sum ((fun z : σ → ℂ => z - w) w) := by
      simpa using hG.analyticAt
    exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ))).analyticAt _).comp
      (AnalyticAt.comp (g := p.shift.sum) (f := fun z : σ → ℂ => z - w) h3 h2)
  · filter_upwards [Metric.eball_mem_nhds w hp.r_pos] with z hz
    set y := z - w with hy
    have hy0 : y ∈ Metric.eball (0 : σ → ℂ) r := by
      rw [Metric.mem_eball] at hz ⊢
      rwa [edist_zero_right, hy, ← edist_eq_enorm_sub]
    have hy1 : y ∈ Metric.eball (0 : σ → ℂ) p.shift.radius :=
      Metric.eball_subset_eball (hrad ▸ hp.r_le) hy0
    have h1 := hp.hasSum hy0
    have h2 := hG.hasSum hy1
    rw [zero_add] at h2
    have h3 := (ContinuousLinearMap.apply ℂ ℂ y).hasSum h2
    have h4 : ∀ n, (ContinuousLinearMap.apply ℂ ℂ y) (p.shift n fun _ => y) =
        p (n + 1) fun _ => y := by
      intro n
      simp only [ContinuousLinearMap.apply_apply, FormalMultilinearSeries.shift,
        ContinuousMultilinearMap.curryRight_apply]
      congr 1
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    simp only [h4, ContinuousLinearMap.apply_apply] at h3
    have h5 := (hasSum_nat_add_iff' 1).mpr h1
    simp only [Finset.range_one, Finset.sum_singleton, hp.coeff_zero] at h5
    have e := h5.unique h3
    have hwz : w + y = z := by rw [hy]; abel
    rw [hwz] at e
    have e2 : p.shift.sum y y = ∑ i, (z i - w i) * p.shift.sum y (Pi.single i 1) := by
      have hyy : p.shift.sum y y = p.shift.sum y (∑ i, Pi.single i (y i)) := by
        rw [Finset.univ_sum_single]
      rw [hyy, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (Pi.single i (y i) : σ → ℂ) = y i • Pi.single i 1 by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h], map_smul, smul_eq_mul, hy, Pi.sub_apply]
    rw [← e2, ← e]
    ring

theorem HolGermPointIdealSpan.proof : HolGermPointIdealSpan.Statement := by
  intro σ _ w
  apply le_antisymm
  · rintro ⟨_, f, hf, rfl⟩ hφ
    have hfw : f w = 0 := hφ
    obtain ⟨g, hg, hfg⟩ := hadamard_decomposition hf
    have key : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) =
        ∑ i, polyGerm w (X i - C (w i)) * ⟨(g i : Germ (𝓝 w) ℂ), g i, hg i, rfl⟩ := by
      apply Subtype.ext
      change (f : Germ (𝓝 w) ℂ) = (holGerms w).subtype (∑ i, _)
      rw [map_sum]
      simp only [map_mul, Subring.coe_subtype]
      have hsum : ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) =
          ∑ i, ((fun z : σ → ℂ => z i - w i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) * (g i : Germ (𝓝 w) ℂ) := by
        change Germ.coeRingHom (𝓝 w) (fun z => ∑ i, (z i - w i) * g i z) = _
        rw [show (fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) =
            ∑ i, (fun z : σ → ℂ => z i - w i) * g i by
          funext z; simp [Finset.sum_apply], map_sum]
        rfl
      have hfe : (f : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) :=
        Germ.coe_eq.mpr (hfg.mono fun z hz => by rw [hz, hfw, zero_add])
      rw [hfe, hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      change _ = ((fun z : σ → ℂ => eval z (X i - C (w i)) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      simp
    rw [key]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change holGermValue w (polyGerm w (X i - C (w i))) = 0
    rw [holGermValue_polyGerm]
    simp

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImplicitCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Topology Metric

noncomputable section

namespace ImplicitCurve

theorem analyticOnNhd_of_differentiableOn {m p : ℕ} {U : Set (Fin m → ℂ)}
    {Φ : (Fin m → ℂ) → Fin p → ℂ} (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U) :
    AnalyticOnNhd ℂ Φ U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => Φ t j) U := differentiableOn_pi.1 hΦ j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn
    fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => Φ t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]; exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem proof : ImplicitCurve.Statement := by
  intro n k γ R L s hγ hs hbij
  set F : (Fin (k + 1) → ℂ) → Fin (k + 1) → ℂ := fun t => vecCons (t 0) (L *ᵥ γ t) with hF
  have hFd : DifferentiableOn ℂ F (ball 0 R) := by
    refine differentiableOn_pi.2 fun i => Fin.cases ?_ (fun j => ?_) i
    · simpa [hF] using (differentiableOn_pi.1 (differentiableOn_id (s := ball (0 : Fin (k + 1) → ℂ) R)) 0)
    · simp only [hF, cons_val_succ, mulVec, dotProduct]
      exact DifferentiableOn.fun_sum fun l _ => (differentiableOn_pi.1 hγ l).const_mul _
  have hFa := analyticOnNhd_of_differentiableOn isOpen_ball hFd
  set e := (LinearEquiv.ofBijective
    (fderiv ℂ F s : (Fin (k + 1) → ℂ) →ₗ[ℂ] Fin (k + 1) → ℂ) hbij).toContinuousLinearEquiv
  have he : (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) = fderiv ℂ F s := by ext1 x; rfl
  have hst : HasStrictFDerivAt F (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) s := by
    rw [he]; exact (hFa s hs).hasStrictFDerivAt
  have hV : ∀ᶠ t in 𝓝 s, (t ∈ ball (0 : Fin (k + 1) → ℂ) R ∧ fderiv ℂ F t ∈
      Set.range ((↑) : ((Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ)) → _)) ∧
      t ∈ (hst.toOpenPartialHomeomorph F).source :=
    (Filter.Eventually.and (isOpen_ball.mem_nhds hs) ((hFa s hs).fderiv.continuousAt.preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨e, he⟩))).and
      ((hst.toOpenPartialHomeomorph F).open_source.mem_nhds hst.mem_toOpenPartialHomeomorph_source)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  set Ψ := (hst.toOpenPartialHomeomorph F).restrOpen (ball s ε) isOpen_ball
  have hΨs : Ψ.source = (hst.toOpenPartialHomeomorph F).source ∩ ball s ε :=
    OpenPartialHomeomorph.restrOpen_source _ _ _
  have hsΨ : s ∈ Ψ.source := hΨs ▸ ⟨hst.mem_toOpenPartialHomeomorph_source, mem_ball_self hε⟩
  have hsrc : ∀ t ∈ Ψ.source, t ∈ ball 0 R ∧
      ∃ e' : (Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ), HasFDerivAt Ψ (e' : _ →L[ℂ] _) t := by
    intro t ht
    obtain ⟨⟨htR, e', he'⟩, -⟩ := hεV (hΨs ▸ ht).2
    refine ⟨htR, e', ?_⟩
    rw [he']; exact (hFa t htR).differentiableAt.hasFDerivAt
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 Ψ.open_target (F s) (Ψ.map_source hsΨ)
  set p : (Fin 1 → ℂ) → Fin (k + 1) → ℂ := fun τ => vecCons (s 0 + τ 0) (L *ᵥ γ s) with hp
  have hpT : ∀ τ ∈ ball (0 : Fin 1 → ℂ) r, p τ ∈ Ψ.target := by
    intro τ hτ
    refine hrT ((dist_pi_lt_iff hr).2 fun i => Fin.cases ?_ (fun j => ?_) i)
    · simpa [hp, hF, dist_eq_norm] using (norm_le_pi_norm τ 0).trans_lt (mem_ball_zero_iff.1 hτ)
    · simpa [hp, hF] using hr
  refine ⟨r, hr, fun τ => Ψ.symm (p τ), fun τ hτ => ?_, ?_, fun τ hτ => ?_, ?_⟩
  · have hpd : Differentiable ℂ p := differentiable_pi.2 fun i => Fin.cases
      (by simpa [hp] using (differentiable_const (s 0)).add (differentiable_pi.1 differentiable_id 0))
      (fun j => by simp [hp]) i
    obtain ⟨-, e', he'⟩ := hsrc _ (Ψ.map_target (hpT τ hτ))
    exact ((Ψ.hasFDerivAt_symm (hpT τ hτ) he').differentiableAt.comp τ
      (hpd τ)).differentiableWithinAt
  · have h0 : p 0 = F s := by simp [hp, hF]
    show Ψ.symm (p 0) = s
    rw [h0]; exact Ψ.left_inv hsΨ
  · have h2 : F (Ψ.symm (p τ)) = p τ := Ψ.right_inv (hpT τ hτ)
    refine ⟨(hsrc _ (Ψ.map_target (hpT τ hτ))).1, ?_, ?_⟩
    · simpa [hF, hp] using congrFun h2 0
    · simpa [hF, hp] using congrArg Fin.tail h2
  · refine ⟨Ψ.source ∩ {t | ‖t 0 - s 0‖ < r}, Filter.inter_mem (Ψ.open_source.mem_nhds hsΨ)
      ((isOpen_lt ((continuous_apply 0).sub continuous_const).norm continuous_const).mem_nhds
        (by simpa using hr)), ?_⟩
    rintro t ⟨ht, htr⟩ hL
    refine ⟨fun _ => t 0 - s 0, by simpa [pi_norm_const] using htr, ?_⟩
    have hpt : p (fun _ => t 0 - s 0) = F t := by simp [hp, hF, hL]
    dsimp only
    rw [hpt]; exact Ψ.left_inv ht

end ImplicitCurve

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicInverse
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

namespace InjectiveHolomorphicInverse

theorem analyticAt_of_differentiableOn {k : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin k → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : Fin k → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  refine AnalyticAt.pi fun i => ?_
  refine analyticOnNhd_of_continuousOn_of_separately hU
    ((continuous_apply i).comp_continuousOn hf.continuousOn) (fun z hz j => ?_) x hx
  have hfz : DifferentiableAt ℂ (fun w => f w i) z :=
    differentiableAt_pi.mp (hf.differentiableAt (hU.mem_nhds hz)) i
  have hu : DifferentiableAt ℂ (Function.update z j) (z j) :=
    (hasFDerivAt_update z (z j)).differentiableAt
  have hfz' : DifferentiableAt ℂ (fun w => f w i) (Function.update z j (z j)) := by
    rwa [Function.update_eq_self]
  exact hfz'.comp (z j) hu

theorem exists_equiv (hJ : InjectiveHolomorphicJacobianNeZero.Statement) {k : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin k → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    {x : Fin k → ℂ} (hx : x ∈ U) :
    ∃ e : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ), HasStrictFDerivAt f (e : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) x := by
  have hdet := hJ k U f hU hf hinj x hx
  refine ⟨(LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv, ?_⟩
  have he : ((LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv :
      (Fin k → ℂ) →L[ℂ] Fin k → ℂ) = fderiv ℂ f x := by
    ext1 v
    rfl
  rw [he]
  exact (analyticAt_of_differentiableOn hU hf hx).hasStrictFDerivAt

theorem proof (hJ : InjectiveHolomorphicJacobianNeZero.Statement) : InjectiveHolomorphicInverse.Statement := by
  intro k U f hU hf hinj
  have hleft : ∀ z ∈ U, Function.invFunOn f U (f z) = z := fun z hz =>
    hinj (Function.invFunOn_mem ⟨z, hz, rfl⟩) hz (Function.invFunOn_eq ⟨z, hz, rfl⟩)
  refine ⟨?_, Function.invFunOn f U, ?_, hleft⟩
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    rw [← he.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hU.mem_nhds hx)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    refine (he.to_local_left_inverse ?_).differentiableAt.differentiableWithinAt
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hleft z hz

end InjectiveHolomorphicInverse

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreLocalUnbranched
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

private theorem germ_zero_of_mul_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {y : E}
    (hf : AnalyticAt ℂ f y) (hg : AnalyticAt ℂ g y) (hfg : ∀ᶠ z in 𝓝 y, f z * g z = 0) :
    (∀ᶠ z in 𝓝 y, f z = 0) ∨ (∀ᶠ z in 𝓝 y, g z = 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  by_cases hf0 : ∀ z ∈ Metric.ball y r, f z = 0
  · exact Or.inl (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hf0)
  · right
    push Not at hf0
    obtain ⟨p, hp, hfp⟩ := hf0
    have hgp : g =ᶠ[𝓝 p] 0 := by
      filter_upwards [(hball hp).1.1.continuousAt.eventually_ne hfp, Metric.isOpen_ball.mem_nhds hp]
        with z hz1 hz2
      exact (mul_eq_zero.1 (hball hz2).2).resolve_left hz1
    have hgan : AnalyticOnNhd ℂ g (Metric.ball y r) := fun z hz => (hball hz).1.2
    have hzero := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y r).isPreconnected hp hgp
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => by simpa using hzero hz

private theorem germ_factor_zero_of_prod_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (h : ι → E → ℂ) {y : E} (s : Finset ι) (han : ∀ i ∈ s, AnalyticAt ℂ (h i) y)
    (hprod : ∀ᶠ z in 𝓝 y, ∏ i ∈ s, h i z = 0) : ∃ i ∈ s, ∀ᶠ z in 𝓝 y, h i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hprod.exists
    simp at hz
  | insert a s ha ih =>
    have hg : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) y :=
      Finset.analyticAt_fun_prod s fun i hi => han i (Finset.mem_insert_of_mem hi)
    have hprod' : ∀ᶠ z in 𝓝 y, h a z * ∏ i ∈ s, h i z = 0 := by
      filter_upwards [hprod] with z hz
      rwa [Finset.prod_insert ha] at hz
    rcases germ_zero_of_mul_zero (han a (Finset.mem_insert_self a s)) hg hprod' with h1 | h1
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨i, hi, h2⟩ := ih (fun i hi => han i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, h2⟩

private theorem isOpen_diff_of_zeroSet {σ : Type} [Fintype σ] {Y N : Set (σ → ℂ)} {k : ℕ}
    {φ : Fin k → (σ → ℂ) → ℂ} (hN : IsOpen N) (hφ : ∀ m, AnalyticOnNhd ℂ (φ m) N)
    (hY : Y ∩ N = {z | z ∈ N ∧ ∀ m, φ m z = 0}) : IsOpen (N \ Y) := by
  have hEq : N \ Y = ⋃ m, N ∩ φ m ⁻¹' {0}ᶜ := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzN, hzY⟩
      by_contra hcon
      push Not at hcon
      have hz : z ∈ Y ∩ N := by
        rw [hY]
        exact ⟨hzN, fun m => hcon m hzN⟩
      exact hzY hz.1
    · rintro ⟨m, hzN, hzm⟩
      refine ⟨hzN, fun hzY => hzm ?_⟩
      have hz : z ∈ Y ∩ N := ⟨hzY, hzN⟩
      rw [hY] at hz
      exact hz.2 m
  rw [hEq]
  exact isOpen_iUnion fun m => (hφ m).continuousOn.isOpen_inter_preimage hN isOpen_compl_singleton

theorem IsolatedFibreLocalUnbranched.proof (hcomp : OpenProjectionDominantComponents.Statement)
    (hmeet : IrreducibleGermMeetOverHypersurface.Statement)
    (hprim : IrreducibleGermPrimitiveForm.Statement)
    (hsheet : PrimitiveFormSheetedOffDiscriminant.Statement) :
    IsolatedFibreLocalUnbranched.Statement := by
  classical
  intro σ _ X B k f d A hB hf hXB hopen w hw hiso
  obtain ⟨n, Y, hY, hsepY, W0, hW0, hXW0⟩ := hcomp σ X B k f d A hB hf hXB hopen w hw
  obtain ⟨W, hW, hWiso⟩ := hiso

  have hisoY : ∀ i, ∃ W' ∈ 𝓝 w, ∀ x ∈ Y i ∩ W', A x = A w → x = w := fun i =>
    ⟨W ∩ W0, inter_mem hW hW0, fun x hx hAx => by
      have hxX : x ∈ X ∩ B ∩ W0 := by
        rw [hXW0]
        exact ⟨Set.mem_iUnion.2 ⟨i, hx.1⟩, hx.2.2⟩
      exact hWiso x ⟨hxX.1, hx.2.1⟩ hAx⟩

  have hsh : ∀ i, ∃ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) ∧
      ∃ M ∈ 𝓝 w, ∀ y ∈ Y i ∩ M, δ (A y) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
        (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ t ∈ O, A (g t) = t) ∧ Y i ∩ V = g '' O := by
    intro i
    obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hP, hsep, hQ⟩ :=
      hprim σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2
    exact ⟨δ, hδ, hδ0,
      hsheet σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2 ℓ N a δ q ha hδ hq hδ0 hP hsep hQ⟩
  choose δ hδa hδ0 M hM hMsh using hsh

  have hsp : ∀ i j, ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
      (i ≠ j → ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j → e (A z) = 0) := by
    intro i j
    by_cases hij : i = j
    · refine ⟨fun _ => 1, analyticAt_const, fun h => ?_, fun h => absurd hij h⟩
      obtain ⟨y, hy⟩ := h.exists
      exact one_ne_zero hy
    · obtain ⟨e, he, he0, hez⟩ :=
        hmeet σ (Y i) (Y j) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY j).1 (hsepY i j hij)
      exact ⟨e, he, he0, fun _ => hez⟩
  choose e hea he0 hez using hsp

  have hYa : ∀ j, ∃ (N : Set (σ → ℂ)) (kk : ℕ) (φ : Fin kk → (σ → ℂ) → ℂ), IsOpen N ∧ w ∈ N ∧
      (∀ m, AnalyticOnNhd ℂ (φ m) N) ∧ Y j ∩ N = {z | z ∈ N ∧ ∀ m, φ m z = 0} := fun j => (hY j).1
  choose N kk φ hNo hwN hφ hYN using hYa
  have hfac : ∀ i, AnalyticAt ℂ (fun y => δ i y * ∏ j, e i j y) (A w) := fun i =>
    (hδa i).mul (Finset.analyticAt_fun_prod _ fun j _ => hea i j)
  refine ⟨interior W0 ∩ (⋂ i, M i) ∩ (⋂ j, N j) ∩
      {z | ∀ i j, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0},
    fun y => ∏ i, (δ i y * ∏ j, e i j y), ?_, Finset.analyticAt_fun_prod _ fun i _ => hfac i, ?_, ?_⟩
  · refine inter_mem (inter_mem (inter_mem (interior_mem_nhds.2 hW0) (iInter_mem.2 hM))
      (iInter_mem.2 fun j => (hNo j).mem_nhds (hwN j))) ?_
    have hev : ∀ i j, ∀ᶠ z in 𝓝 w, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0 := fun i j => by
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      · filter_upwards [hez i j hij] with z hz _ using hz
    exact eventually_all.2 fun i => eventually_all.2 fun j => hev i j
  · intro hg0
    obtain ⟨i, -, hi⟩ := germ_factor_zero_of_prod_zero (fun i y => δ i y * ∏ j, e i j y) Finset.univ
      (fun i _ => hfac i) hg0
    rcases germ_zero_of_mul_zero (hδa i) (Finset.analyticAt_fun_prod _ fun j _ => hea i j) hi with h1 | h1
    · exact hδ0 i h1
    · obtain ⟨j, -, hj⟩ := germ_factor_zero_of_prod_zero (e i) Finset.univ (fun j _ => hea i j) h1
      exact he0 i j hj
  · intro x hx hgx
    obtain ⟨hxXB, ⟨⟨hxW0, hxM⟩, hxN⟩, hxe⟩ := hx
    simp only [Set.mem_iInter] at hxM hxN
    have hgx' : ∀ i, δ i (A x) ≠ 0 ∧ ∀ j, e i j (A x) ≠ 0 := by
      intro i
      have hi := (Finset.prod_ne_zero_iff.1 hgx) i (Finset.mem_univ i)
      exact ⟨left_ne_zero_of_mul hi,
        fun j => (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hi)) j (Finset.mem_univ j)⟩
    have hxU : x ∈ (⋃ i, Y i) ∩ W0 := by
      rw [← hXW0]
      exact ⟨hxXB, interior_subset hxW0⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxU.1
    have hxnot : ∀ j, j ≠ i → x ∉ Y j := fun j hji hxj =>
      (hgx' i).2 j (hxe i j (Ne.symm hji) hxi hxj)

    let U : Set (σ → ℂ) := interior W0 ∩ ⋂ j, (if j = i then Set.univ else N j \ Y j)
    have hUo : IsOpen U := by
      refine isOpen_interior.inter (isOpen_iInter_of_finite fun j => ?_)
      split_ifs
      · exact isOpen_univ
      · exact isOpen_diff_of_zeroSet (hNo j) (hφ j) (hYN j)
    have hxUm : x ∈ U := by
      refine ⟨hxW0, Set.mem_iInter.2 fun j => ?_⟩
      split_ifs with hji
      · trivial
      · exact ⟨hxN j, hxnot j hji⟩
    have hXU : X ∩ B ∩ U = Y i ∩ U := by
      ext z
      constructor
      · rintro ⟨hzXB, hzU⟩
        have hzW : z ∈ (⋃ i, Y i) ∩ W0 := by
          rw [← hXW0]
          exact ⟨hzXB, interior_subset hzU.1⟩
        obtain ⟨j, hzj⟩ := Set.mem_iUnion.1 hzW.1
        by_cases hji : j = i
        · rw [hji] at hzj
          exact ⟨hzj, hzU⟩
        · have hzj' := Set.mem_iInter.1 hzU.2 j
          rw [if_neg hji] at hzj'
          exact absurd hzj hzj'.2
      · rintro ⟨hzi, hzU⟩
        have hzW : z ∈ X ∩ B ∩ W0 := by
          rw [hXW0]
          exact ⟨Set.mem_iUnion.2 ⟨i, hzi⟩, interior_subset hzU.1⟩
        exact ⟨hzW.1, hzU⟩

    obtain ⟨O, V, h, hO, hV, hxV, hh, hAh, hYV⟩ := hMsh i x ⟨hxi, hxM i⟩ (hgx' i).1
    refine ⟨O ∩ h ⁻¹' U, V ∩ U, h, hh.continuousOn.isOpen_inter_preimage hO hUo, hV.inter hUo,
      ⟨hxV, hxUm⟩, hh.mono Set.inter_subset_left, fun t ht => hAh t ht.1, ?_⟩
    rw [Set.image_inter_preimage, ← hYV]
    ext z
    constructor
    · rintro ⟨hzXB, hzV, hzU⟩
      have hz : z ∈ Y i ∩ U := by
        rw [← hXU]
        exact ⟨hzXB, hzU⟩
      exact ⟨⟨hz.1, hzV⟩, hzU⟩
    · rintro ⟨⟨hzi, hzV⟩, hzU⟩
      have hz : z ∈ X ∩ B ∩ U := by
        rw [hXU]
        exact ⟨hzi, hzU⟩
      exact ⟨hz.1, hzV, hzU⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartChangeSheetNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def ChartChangeSheetNull.Statement : Prop :=
  ∀ (n d : ℕ) (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (u u' : Fin n → ℂ) (U U' : Set (Fin n → ℂ)) (Φ Ψ : (Fin n → ℂ) → Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    J'.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') = d →
    linForm u ∉ J → linForm u' ∉ J' → IsFiniteProjection J A → IsFiniteProjection J' A' →
    IsOpen U → IsOpen U' → zeroSet J \ {x | linEval u x = 0} ⊆ U →
    zeroSet J' \ {x | linEval u' x = 0} ⊆ U' →
    DifferentiableOn ℂ Φ U' → DifferentiableOn ℂ Ψ U →
    Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}) →
    Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}) →
    (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x) →
    (∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x) →
      volume ((fun x => A *ᵥ x) ''
        {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧
          ¬ (linEval u x ≠ 0 ∧ ∃ s', IsSheetAt J' A' (Ψ x) s')}) = 0

namespace ChartChange

def inv1 (x : Fin 1 → ℂ) : Fin 1 → ℂ := fun _ => (x 0)⁻¹

end ChartChange

end

end GroundTheory.Heights₂.Heights
end

