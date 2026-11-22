import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0084
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialEqZeroOfEventually

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.ContAtOfHoloOn
section
noncomputable section

namespace RootFieldNumerics

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace Desc

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem contAt_of_holoOn (A : FinHolAtlas e X) {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) :
    ContinuousAt f x := by
  obtain ⟨k, hk⟩ := A.cover x
  have h1 := (hf k (A.chart k x) ⟨(A.chart k).map_source hk, by
    show (A.chart k).symm (A.chart k x) ∈ U
    rwa [(A.chart k).left_inv hk]⟩).continuousAt
  have h2 := h1.comp ((A.chart k).continuousAt hk)
  refine h2.congr ?_
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with x' hx'
  simp [(A.chart k).left_inv hx']

theorem analytic_off {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} {S U : Set X} {f : Y → ℂ}
    (hh : HoloMap B A h) (hd : IsDegreeOff A B h 1 S) (hf : B.HoloOn (h ⁻¹' U) f) (σ : X → Y)
    (hσ : ∀ x ∉ S, h (σ x) = x) (hσ' : ∀ y, h y ∉ S → σ (h y) = y) (k : Fin A.n) {q : Fin e → ℂ}
    (hq : q ∈ (A.chart k).target) (hU : (A.chart k).symm q ∈ U) (hS : (A.chart k).symm q ∉ S) :
    AnalyticAt ℂ (fun t => f (σ ((A.chart k).symm t))) q := by
  have hSc : IsClosed S := isClosed_of_isAnalyticSubset' A hd.1
  set x := (A.chart k).symm q with hx
  obtain ⟨j, hj⟩ := B.cover (σ x)
  set p := B.chart j (σ x) with hp
  have hpt : p ∈ (B.chart j).target := (B.chart j).map_source hj
  have hsp : (B.chart j).symm p = σ x := (B.chart j).left_inv hj
  have hxs : x ∈ (A.chart k).source := (A.chart k).map_target hq
  have hhs : h ((B.chart j).symm p) ∈ (A.chart k).source := by rw [hsp, hσ x hS]; exact hxs
  let φ : (Fin e → ℂ) → Fin e → ℂ := A.chart k ∘ h ∘ (B.chart j).symm
  have hφ : AnalyticAt ℂ φ p := hh.2 j k p ⟨hpt, hhs⟩
  have hφp : φ p = q := by
    show A.chart k (h ((B.chart j).symm p)) = q
    rw [hsp, hσ x hS, hx, (A.chart k).right_inv hq]
  have hdet := hd.2.2.2.2.2 j k p hpt (by
    show h ((B.chart j).symm p) ∉ S
    rwa [hsp, hσ x hS]) hhs
  let L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ) := (fderiv ℂ φ p).toContinuousLinearEquivOfDetNeZero hdet
  have hL : HasFDerivAt φ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) p := by
    have := hφ.differentiableAt.hasFDerivAt
    simpa [L] using this
  have hc : ContDiffAt ℂ ⊤ φ p := hφ.contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  let ψ := hc.localInverse hL hn
  have hψ : AnalyticAt ℂ ψ q := by
    have := (hc.to_localInverse hL hn).analyticAt
    rwa [hφp] at this
  have hψq : ψ q = p := by
    rw [← hφp]
    exact hc.localInverse_apply_image hL hn
  have hri : ∀ᶠ t in 𝓝 q, φ (ψ t) = t := by
    have := (hc.hasStrictFDerivAt' hL hn).eventually_right_inverse
    rw [hφp] at this
    exact this
  have hfa : AnalyticAt ℂ (f ∘ (B.chart j).symm) (ψ q) := by
    rw [hψq]
    refine hf j p ⟨hpt, ?_⟩
    show h ((B.chart j).symm p) ∈ U
    rwa [hsp, hσ x hS]
  refine (hfa.comp hψ).congr ?_
  have c1 : ContinuousAt (fun t => h ((B.chart j).symm (ψ t))) q :=
    hh.1.continuousAt.comp (ContinuousAt.comp (by rw [hψq]; exact (B.chart j).continuousAt_symm hpt) hψ.continuousAt)
  have e1 : ∀ᶠ t in 𝓝 q, h ((B.chart j).symm (ψ t)) ∈ (A.chart k).source ∩ Sᶜ :=
    c1.eventually_mem (((A.chart k).open_source.inter hSc.isOpen_compl).mem_nhds (by
      show h ((B.chart j).symm (ψ q)) ∈ _
      rw [hψq, hsp, hσ x hS]
      exact ⟨hxs, hS⟩))
  filter_upwards [hri, e1] with t h1 h2
  have h3 : (A.chart k).symm t = h ((B.chart j).symm (ψ t)) := by
    rw [← (A.chart k).left_inv h2.1]
    exact congrArg _ h1.symm
  show f ((B.chart j).symm (ψ t)) = f (σ ((A.chart k).symm t))
  rw [h3, hσ' _ h2.2]

theorem local_ext {A : FinHolAtlas e X} {S U : Set X} {u : X → ℂ} (hS : A.IsAnalyticSubset S) (hi : interior S = ∅)
    (hU : IsOpen U) (k : Fin A.n)
    (ha : ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → (A.chart k).symm q ∉ S →
      AnalyticAt ℂ (fun t => u ((A.chart k).symm t)) q)
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ x' in 𝓝 x, x' ∉ S → ‖u x'‖ ≤ C) {q : Fin e → ℂ} (hq : q ∈ (A.chart k).target)
    (hqU : (A.chart k).symm q ∈ U) :
    ∃ w : (Fin e → ℂ) → ℂ, AnalyticAt ℂ w q ∧ ∀ᶠ t in 𝓝 q, (A.chart k).symm t ∉ S → w t = u ((A.chart k).symm t) := by
  by_cases hqS : (A.chart k).symm q ∈ S
  swap
  · exact ⟨_, ha q hq hqU hqS, Eventually.of_forall fun _ _ => rfl⟩
  obtain ⟨W, hW, hqW, hWc, φ, hφ, ⟨w₀, hw₀, hw₀'⟩, hz⟩ := analyticSubset_chart_local A hS hi k (z := q)
    ⟨_, ⟨hqS, (A.chart k).map_target hq⟩, (A.chart k).right_inv hq⟩
  let U' := W ∩ ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U)
  have hU' : IsOpen U' := hW.inter ((A.chart k).isOpen_inter_preimage_symm hU)
  have hns : ∀ b ∈ U', φ b ≠ 0 → (A.chart k).symm b ∉ S := fun b hb h0 hs =>
    h0 (hz b ⟨⟨_, ⟨hs, (A.chart k).map_target hb.2.1⟩, (A.chart k).right_inv hb.2.1⟩, hb.1⟩)
  have hden : U' ⊆ closure {b ∈ U' | φ b ≠ 0} := fun b hb => by
    by_contra hn
    have h1 : ∀ᶠ b' in 𝓝 b, b' ∉ {b ∈ U' | φ b ≠ 0} := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with b' hb' h using hb' (subset_closure h)
    have h2 : φ =ᶠ[𝓝 b] 0 := by
      filter_upwards [h1, hU'.mem_nhds hb] with b' h h'
      by_contra h0
      exact h ⟨h', h0⟩
    exact hw₀' (hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hWc hb.1 h2 hw₀)
  obtain ⟨u', hu', he⟩ := GlobalTheory.LogExt.riemann_extension_log _ U' φ (fun t => u ((A.chart k).symm t)) hU'
    (hφ.differentiableOn.mono Set.inter_subset_left)
    (fun b hb => (ha b hb.1.2.1 hb.1.2.2 (hns b hb.1 hb.2)).differentiableAt.differentiableWithinAt) hden
    (fun b hb' => by
      obtain ⟨C, hC⟩ := hb _ hb'.2.2
      refine ⟨C, 0, ?_⟩
      filter_upwards [((A.chart k).continuousAt_symm hb'.2.1).eventually hC, hU'.mem_nhds hb'] with t h1 h2 h0
      simpa using h1 (hns t h2 h0))
  have hq' : q ∈ U' := ⟨hqW, hq, hqU⟩
  refine ⟨u', GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU' hu' q hq', ?_⟩
  filter_upwards [hU'.mem_nhds hq'] with t ht hts
  have : (𝓝[{b ∈ U' | φ b ≠ 0}] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hden ht)
  refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[{b ∈ U' | φ b ≠ 0}] t)
    ((hu'.continuousOn.continuousAt (hU'.mem_nhds ht)).tendsto.mono_left nhdsWithin_le_nhds)
    ((ha t ht.2.1 ht.2.2 hts).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with b hb using he hb

theorem ext_manifold {A : FinHolAtlas e X} {S U : Set X} {u : X → ℂ} (hS : A.IsAnalyticSubset S) (hi : interior S = ∅)
    (hU : IsOpen U)
    (ha : ∀ k, ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → (A.chart k).symm q ∉ S →
      AnalyticAt ℂ (fun t => u ((A.chart k).symm t)) q)
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ x' in 𝓝 x, x' ∉ S → ‖u x'‖ ≤ C) :
    ∃ F : X → ℂ, A.HoloOn U F ∧ ∀ x ∈ U, x ∉ S → F x = u x := by
  have hden : Dense Sᶜ := interior_eq_empty_iff_dense_compl.1 hi
  let F : X → ℂ := fun x => limUnder (𝓝[Sᶜ] x) u
  have key : ∀ k, ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → ∃ w : (Fin e → ℂ) → ℂ, AnalyticAt ℂ w q ∧
      (∀ᶠ t in 𝓝 q, (A.chart k).symm t ∉ S → w t = u ((A.chart k).symm t)) ∧
      ∀ᶠ t in 𝓝 q, w t = F ((A.chart k).symm t) := fun k q hq hqU => by
    obtain ⟨w, hw, he⟩ := local_ext hS hi hU k (ha k) hb hq hqU
    refine ⟨w, hw, he, ?_⟩
    filter_upwards [he.eventually_nhds, hw.eventually_analyticAt, (A.chart k).open_target.mem_nhds hq] with t h1 h2 h3
    have hs := (A.chart k).map_target h3
    have hr := (A.chart k).right_inv h3
    have : (𝓝[Sᶜ] ((A.chart k).symm t)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hden _)
    have hc : Tendsto (A.chart k) (𝓝 ((A.chart k).symm t)) (𝓝 t) := by
      have := ((A.chart k).continuousAt hs).tendsto
      rwa [hr] at this
    refine (Tendsto.limUnder_eq ?_).symm
    refine ((h2.continuousAt.tendsto.comp hc).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds (hc.eventually h1), nhdsWithin_le_nhds ((A.chart k).open_source.mem_nhds hs),
      self_mem_nhdsWithin] with x h4 h5 h6
    have h7 : (A.chart k).symm (A.chart k x) ∉ S → w (A.chart k x) = u ((A.chart k).symm (A.chart k x)) := h4
    rw [(A.chart k).left_inv h5] at h7
    exact h7 h6
  refine ⟨F, fun k q hq => ?_, fun x hx hxS => ?_⟩
  · obtain ⟨w, hw, -, he⟩ := key k q hq.1 hq.2
    exact hw.congr he
  · obtain ⟨k, hk⟩ := A.cover x
    have hl := (A.chart k).left_inv hk
    obtain ⟨w, -, h1, h2⟩ := key k _ ((A.chart k).map_source hk) (by rwa [hl])
    have h3 := h1.self_of_nhds
    have h4 := h2.self_of_nhds
    rw [hl] at h3 h4
    rw [← h4, h3 hxS]

end Desc

open Desc in
theorem descend : Descend := by
  intro e X Y _ _ _ _ _ _ A B h S U f hh hd hU hf
  classical
  rcases isEmpty_or_nonempty Y with hY | hY
  · refine ⟨0, fun k => ?_, fun y => isEmptyElim y⟩
    exact analyticOnNhd_const
  have hex : ∀ x, ∃ y, x ∉ S → h ⁻¹' {x} = {y} := fun x => by
    by_cases hx : x ∈ S
    · exact ⟨hY.some, fun h' => (h' hx).elim⟩
    · obtain ⟨y, hy⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 x hx)
      exact ⟨y, fun _ => hy⟩
  choose σ hσ₀ using hex
  have hσ : ∀ x ∉ S, h (σ x) = x := fun x hx => by
    have : σ x ∈ h ⁻¹' {x} := by rw [hσ₀ x hx]; rfl
    exact this
  have hσ' : ∀ y, h y ∉ S → σ (h y) = y := fun y hy => by
    have : y ∈ h ⁻¹' {h y} := rfl
    rw [hσ₀ _ hy] at this
    exact this.symm
  have hfc : ContinuousOn f (h ⁻¹' U) := fun y hy => (contAt_of_holoOn B hf hy).continuousWithinAt
  obtain ⟨F, hF, he⟩ := ext_manifold (u := fun x => f (σ x)) hd.1 hd.2.1 hU
    (fun k q hq h1 h2 => analytic_off hh hd hf σ hσ hσ' k hq h1 h2) (fun x hx => by
      obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds (hU.mem_nhds hx)
      have hc : IsCompact (h ⁻¹' K) := (hKc.isClosed.preimage hh.1).isCompact
      obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (hfc.mono (Set.preimage_mono hKU))
      refine ⟨C, ?_⟩
      filter_upwards [hK] with x' h1 h2
      exact hC _ (by show h (σ x') ∈ K; rwa [hσ x' h2]))
  refine ⟨F, hF, fun y hy => ?_⟩
  have hden : Dense (h ⁻¹' S)ᶜ := interior_eq_empty_iff_dense_compl.1 hd.2.2.2.1
  have ho : IsOpen (h ⁻¹' U) := hU.preimage hh.1
  refine Set.EqOn.of_subset_closure (f := fun y => F (h y)) (g := f) (s := h ⁻¹' U ∩ (h ⁻¹' S)ᶜ) (t := h ⁻¹' U)
    (fun y' hy' => ?_) (fun y' hy' => ?_) hfc Set.inter_subset_left (hden.open_subset_closure_inter ho) hy
  · show F (h y') = f y'
    rw [he _ hy'.1 hy'.2, hσ' _ hy'.2]
  · exact ((contAt_of_holoOn A hF hy').comp hh.1.continuousAt).continuousWithinAt

end RootFieldNumerics
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.ExistsInverse
section
noncomputable section

namespace RootFieldNumerics.Bh

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo

theorem contAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X} {f : X → ℂ}
    (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 := (hf j (A.chart j x) ⟨(A.chart j).map_source hj, by
    show (A.chart j).symm (A.chart j x) ∈ U
    rwa [(A.chart j).left_inv hj]⟩).continuousAt
  have h2 := h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem surj_of_degree {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [CompactSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} {S : Set X} (hc : Continuous h) (hd : IsDegreeOff A B h 1 S) :
    Function.Surjective h := by
  have h1 : IsClosed (Set.range h) := (isCompact_range hc).isClosed
  have h2 : Dense Sᶜ := interior_eq_empty_iff_dense_compl.1 hd.2.1
  have h3 : Sᶜ ⊆ Set.range h := fun x hx => by
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (s := h ⁻¹' {x}) (by rw [hd.2.2.2.2.1 x hx]; exact one_ne_zero)
    exact ⟨y, hy⟩
  rw [← Set.range_eq_univ, ← h1.closure_eq]
  exact (h2.mono h3).closure_eq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem SO_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => by rw [inv_mul_cancel_left₀ (hc _)]⟩

theorem SO_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  exact ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), funext fun p => (mul_assoc _ _ _).symm⟩

theorem SO_ne {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (q : Σ k, ι k) : z q ≠ 0 ↔ z' q ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  simp [hc q.1]

theorem isOpen_lift_ne {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (q : Σ k, ι k) :
    IsOpen {w : R.X | R.lift w w q ≠ 0} := by
  refine isOpen_iff_mem_nhds.2 fun w hw => ?_
  filter_upwards [(R.isOpen_U w).mem_nhds (R.mem_U w),
    (contAt_of_holoOn (R.holo w q) (R.mem_U w)).eventually_ne hw] with w' h1 h2
  exact (SO_ne (R.compat w' w w' ⟨R.mem_U w', h1⟩) q).2 h2

theorem exists_inverse {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (hJ : J = ⊤) {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (π : R.X → X) (hs : Function.Surjective π)
    (key : ∀ w₁, ∃ (O : Set X) (μ : X → (Σ k, ι k) → ℂ), IsOpen O ∧ π w₁ ∈ O ∧ (∀ q, A.HoloOn O fun x => μ x q) ∧
      ∀ w, π w ∈ O → SameOrbit (R.lift w w) (μ (π w))) :
    ∃ ψ : X → R.X, HoloMap A R.A ψ ∧ (∀ x, π (ψ x) = x) ∧ ∀ w, ψ (π w) = w := by
  have hinj : Function.Injective π := fun w w₁ e₀ => by
    obtain ⟨O, μ, -, h1, -, h2⟩ := key w₁
    have a1 := h2 w (e₀ ▸ h1)
    rw [e₀] at a1
    refine R.inj w w₁ (fun h => ?_) (SO_trans a1 (SO_symm (h2 w₁ h1)))
    simpa using h.2 1 (hJ ▸ Submodule.mem_top)
  let ψ := Function.surjInv hs
  have r : ∀ x, π (ψ x) = x := Function.surjInv_eq hs
  have loc : ∀ j, ∀ t ∈ (A.chart j).target, ∃ V, IsOpen V ∧ t ∈ V ∧ ContinuousOn (ψ ∘ (A.chart j).symm) V ∧
      ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ (ψ ∘ (A.chart j).symm)) (V ∩ (ψ ∘ (A.chart j).symm) ⁻¹' (R.A.chart k).source) := by
    intro j t ht
    obtain ⟨O, μ, hO, h1, h2, h3⟩ := key (ψ ((A.chart j).symm t))
    rw [r] at h1
    have hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' O) := (A.chart j).isOpen_inter_preimage_symm hO
    refine ⟨_, hV, ⟨ht, h1⟩, GlobalTheory.T.lift_to_log_resolution_analytic K ι P J e e R hJ _ (fun u => μ ((A.chart j).symm u)) _ hV (fun q => h2 q j)
      fun u hu => ?_⟩
    have := h3 (ψ ((A.chart j).symm u)) (by rw [r]; exact hu.2)
    rwa [r] at this
  refine ⟨ψ, ⟨continuous_iff_continuousAt.2 fun x => ?_, fun j k t ht => ?_⟩, r, fun w => hinj (r _)⟩
  · obtain ⟨j, hj⟩ := A.cover x
    obtain ⟨V, hV, h1, h2, -⟩ := loc j _ ((A.chart j).map_source hj)
    refine ((h2.continuousAt (hV.mem_nhds h1)).comp ((A.chart j).continuousAt hj)).congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  · obtain ⟨V, -, h1, -, h2⟩ := loc j t ht.1
    exact h2 k t ⟨h1, ht.2⟩

end RootFieldNumerics.Bh
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.NeZeroOfHasVal
section
noncomputable section

namespace RootFieldNumerics.Bh

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_poly (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (hn : IsNormalScheme X)
    (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : Ω} (ha : a ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ p : MRing J, aeval (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) p = a := by
  classical
  have hc0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hle : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ chartRingZ y c := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩ ∈ chartRingZ y c
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
  have hge : chartRingZ y c ≤ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨Function.update c k i, ?_⟩
    show (∏ k', y ⟨k', Function.update c k i k'⟩) / ∏ k, y ⟨k, c k⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · rw [Function.update_self]
    · intro k' _ h
      rw [Function.update_of_ne h, div_self (hc k')]
    · simp
  have hmem : a ∈ chartRingZ y c := by
    refine hle ((T.ring c hc0 a).2 fun q hq => ?_)
    obtain ⟨h1, -, h3⟩ := GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ T.gen q
    have h4 := h3 (hn q.1).2
    let φ : chartRingZ y c →+* regAt ξ q :=
      (algebraMap (chartRingZ y c) Ω).codRestrict _ fun r => (T.ring c hc0 r).1 (hge r.2) q hq
    have h5 : IsIntegral (regAt ξ q) a := IsIntegral.map_of_comp_eq φ (RingHom.id Ω) rfl ha
    obtain ⟨r, rfl⟩ := (isIntegrallyClosed_iff Ω).1 h4 h5
    exact r.2
  unfold chartRingZ at hmem
  rw [Algebra.adjoin_range_eq_range_aeval] at hmem
  exact hmem

variable {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ}

theorem val_ratio (h : CoordsAt ξ y z w) (k : K) (i c : J k) (hc : w ⟨k, c⟩ ≠ 0) :
    ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c⟩) (w ⟨k, i⟩ / w ⟨k, c⟩) := by
  obtain ⟨r, hr, e⟩ := (h.2 k c (IsUnit.mk0 _ hc)).2 i
  rwa [e, mul_div_cancel_right₀ _ hc]

theorem val_prod (hz : genPt ξ ⤳ centre z) {a : K → Ω} {r : K → ℂ} (h : ∀ k, ValAt ξ z (a k) (r k)) :
    ValAt ξ z (∏ k, a k) (∏ k, r k) := by
  classical
  have : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, a k) (∏ k ∈ s, r k) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact CxVal.mul (h k) ih
  exact this _

theorem val_pow (hz : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using CxVal.one hz
  | succ n ih => rw [pow_succ, pow_succ]; exact CxVal.mul ih h

def fn (y : (Σ k, J k) → Ω) (s : Ω) (m : ℕ) (k₀ : K) (i₀ : J k₀) (c : (k : K) → J k) : Ω :=
  s * (∏ k, y ⟨k, c k⟩) / y ⟨k₀, i₀⟩ ^ m

theorem val_fn (hz : genPt ξ ⤳ centre z) (h : CoordsAt ξ y z w) {s : Ω} {m : ℕ} {k₀ : K} (i₀ : J k₀) (c c' : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c' k⟩ ≠ 0) (hi : w ⟨k₀, i₀⟩ ≠ 0) {p : MRing J}
    (hp : aeval (fun q : Σ k, J k => y q / y ⟨q.1, c' q.1⟩) p = fn y s m k₀ (c' k₀) c') :
    ValAt ξ z (fn y s m k₀ i₀ c) (aeval (fun q : Σ k, J k => w q / w ⟨q.1, c' q.1⟩) p * (∏ k, w ⟨k, c k⟩ / w ⟨k, c' k⟩) *
      (w ⟨k₀, c' k₀⟩ / w ⟨k₀, i₀⟩) ^ m) := by
  have h1 := CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c' q.1) (hc q.1)) p
  have h2 := val_prod hz fun k => val_ratio h k (c k) (c' k) (hc k)
  have h3 := val_pow hz (val_ratio h k₀ (c' k₀) i₀ hi) m
  have hy := fun k => (h.2 k (c' k) (IsUnit.mk0 _ (hc k))).1
  have hy0 := (h.2 k₀ i₀ (IsUnit.mk0 _ hi)).1
  have hP : (∏ k, y ⟨k, c' k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have hk := hy k₀
  convert CxVal.mul (CxVal.mul h1 h2) h3 using 1
  have hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c' q.1⟩) p = fn y s m k₀ (c' k₀) c' := hp
  rw [hp', Finset.prod_div_distrib, div_pow]
  unfold fn
  field_simp

theorem fn_eq [DecidableEq K] {s : Ω} {m : ℕ} {k₀ : K} {a : K → ℤ} (ha : a k₀ = 1 ∧ ∀ k, k ≠ k₀ → a k = 0)
    (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    s * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k - 1)) = fn y s m k₀ (c k₀) c := by
  have e : ∀ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k - 1)) = y ⟨k, c k⟩ / y ⟨k, c k⟩ ^ ((m : ℤ) * a k) := fun k => by
    rw [neg_sub, zpow_sub₀ (hc k), zpow_one]
  simp only [e, Finset.prod_div_distrib]
  rw [Finset.prod_eq_single k₀ (f := fun k => y ⟨k, c k⟩ ^ ((m : ℤ) * a k))]
  · rw [ha.1, mul_one, zpow_natCast, fn, mul_div_assoc]
  · intro k _ h
    rw [ha.2 k h, mul_zero, zpow_zero]
  · simp

theorem ne_zero_of_hasVal (hz : genPt ξ ⤳ centre z) (h : CoordsAt ξ y z w) {s : Ω} {a : K → ℤ} (c : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) {p : MRing J}
    (hp : aeval (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) p = s * ∏ k, y ⟨k, c k⟩ ^ (-a k)) {v : ℂ} (hv : v ≠ 0)
    (hs : Small.HasVal y a s w v) : aeval (fun q : Σ k, J k => w q / w ⟨q.1, c q.1⟩) p ≠ 0 := by
  obtain ⟨dg, dh, g, h', hg, hh, hd, e1, hne, e2⟩ := hs
  have hy := fun k => (h.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  have V := fun f : MRing J => CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c q.1) (hc q.1)) f
  have ey : y = fun q => y ⟨q.1, c q.1⟩ * (y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) :=
    funext fun q => (mul_div_cancel₀ _ (hy q.1)).symm
  have ew : w = fun q => w ⟨q.1, c q.1⟩ * (w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩) :=
    funext fun q => (mul_div_cancel₀ _ (hc q.1)).symm
  have g1 := aeval_blockScale hg (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩
  have g2 := aeval_blockScale hh (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩
  have g3 := aeval_blockScale hg (fun k => w ⟨k, c k⟩) fun q => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩
  rw [← ey] at g1 g2
  rw [← ew] at g3
  have key : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) g =
      aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p *
        aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) h' := by
    have hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p = s * ∏ k, y ⟨k, c k⟩ ^ (-a k) := hp
    have h0 : (∏ k, y ⟨k, c k⟩ ^ dg k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
    have h1 : (∏ k, y ⟨k, c k⟩ ^ dg k) * ∏ k, y ⟨k, c k⟩ ^ (-a k) = ∏ k, y ⟨k, c k⟩ ^ dh k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), hd k]
      congr 1
      ring
    refine mul_left_cancel₀ h0 ?_
    rw [← g1, e1, g2, hp', ← h1]
    ring
  have e3 := CxVal.unique (key ▸ V g) (CxVal.mul (V p) (V h'))
  intro h0
  have h0' : aeval (fun q : Σ k, J k => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩) p = 0 := h0
  rw [h0', zero_mul] at e3
  rw [e3, mul_zero, e2] at g3
  exact mul_ne_zero hv hne g3

end RootFieldNumerics.Bh
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.RankLem
section
namespace RootFieldNumerics

theorem rankLem : RankLem := fun _ _ _ _ hV hne hΦ hc =>
  GlobalTheory.CountableFibres.exists_injective_fderiv hV hne (fun z hz => (hΦ z hz).contDiffAt) hc

end RootFieldNumerics
end

