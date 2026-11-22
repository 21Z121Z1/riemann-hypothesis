import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PJetOfMonomialSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

namespace JetOfMonomialSum

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}

theorem analyticAt_fderiv_apply {f : E → ℂ} (hf : AnalyticAt ℂ f x) (w : E) :
    AnalyticAt ℂ (fun y => fderiv ℂ f y w) x :=
  ((ContinuousLinearMap.apply ℂ ℂ w).analyticAt _).comp hf.fderiv

theorem vanish_one {f : E → ℂ} (h : f x = 0) : ∀ k < 1, iteratedFDeriv ℂ k f x = 0 := by
  intro k hk
  obtain rfl : k = 0 := by omega
  ext m
  simp [iteratedFDeriv_zero_apply, h]

theorem vanish_mul {f g : E → ℂ} (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) {a b : ℕ}
    (hfa : ∀ k < a, iteratedFDeriv ℂ k f x = 0) (hgb : ∀ k < b, iteratedFDeriv ℂ k g x = 0) :
    ∀ k < a + b, iteratedFDeriv ℂ k (fun y => f y * g y) x = 0 := by
  intro k hk
  obtain ⟨s, hs, hso, hxs⟩ :=
    eventually_nhds_iff.1 (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  have hfs : ContDiffOn ℂ ⊤ f s := fun y hy => (hs y hy).1.contDiffAt.contDiffWithinAt
  have hgs : ContDiffOn ℂ ⊤ g s := fun y hy => (hs y hy).2.contDiffAt.contDiffWithinAt
  have key := norm_iteratedFDerivWithin_mul_le hfs hgs hso.uniqueDiffOn hxs (n := k) le_top
  rw [iteratedFDerivWithin_of_isOpen k hso hxs] at key
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDerivWithin ℂ i f s x‖ *
      ‖iteratedFDerivWithin ℂ (k - i) g s x‖ = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hik := Finset.mem_range.1 hi
    rw [iteratedFDerivWithin_of_isOpen i hso hxs, iteratedFDerivWithin_of_isOpen (k - i) hso hxs]
    rcases lt_or_ge i a with h | h
    · simp [hfa i h]
    · simp [hgb (k - i) (by omega)]
  rw [hsum] at key
  exact norm_le_zero_iff.1 key

theorem top_mul {f g : E → ℂ} (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) {a : ℕ}
    (hfa : ∀ k < a, iteratedFDeriv ℂ k f x = 0) :
    iteratedFDeriv ℂ a (fun y => f y * g y) x = g x • iteratedFDeriv ℂ a f x := by
  have hg' : AnalyticAt ℂ (fun y => g y - g x) x := hg.sub analyticAt_const
  have e : (fun y => f y * g y) = (fun y => f y * (g y - g x)) + (fun y => g x • f y) := by
    funext y
    simp only [Pi.add_apply, smul_eq_mul]
    ring
  rw [e, iteratedFDeriv_add_apply (hf.fun_mul hg').contDiffAt
      (analyticAt_const.fun_smul hf).contDiffAt,
    vanish_mul hf hg' hfa (vanish_one (by simp)) a (by omega), zero_add]
  exact iteratedFDeriv_const_smul_apply' hf.contDiffAt

theorem iteratedFDeriv_fderiv_apply {f : E → ℂ} (hf : AnalyticAt ℂ f x) (w : E) (k : ℕ)
    (m : Fin k → E) :
    iteratedFDeriv ℂ k (fun y => fderiv ℂ f y w) x m =
      iteratedFDeriv ℂ (k + 1) f x (Fin.snoc m w : Fin (k + 1) → E) := by
  rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  have := (ContinuousLinearMap.apply ℂ ℂ w).iteratedFDeriv_comp_left
    (hf.fderiv.contDiffAt (n := ⊤)) (i := k) le_top
  exact congrArg (fun L => L m) this

theorem snoc_const {F : Type*} (k : ℕ) (w : F) :
    (Fin.snoc (fun _ : Fin k => w) w : Fin (k + 1) → F) = fun _ => w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem iteratedFDeriv_fderiv_diag {f : E → ℂ} (hf : AnalyticAt ℂ f x) (w : E) (k : ℕ) :
    iteratedFDeriv ℂ k (fun y => fderiv ℂ f y w) x (fun _ => w) =
      iteratedFDeriv ℂ (k + 1) f x (fun _ => w) := by
  rw [iteratedFDeriv_fderiv_apply hf, snoc_const]

theorem step {g v : E → ℂ} (hg : AnalyticAt ℂ g x) (hv : AnalyticAt ℂ v x) {a : ℕ}
    (hga : ∀ k < a, iteratedFDeriv ℂ k g x = 0) (w : E) :
    iteratedFDeriv ℂ (a + 1) (fun y => g y * v y) x (fun _ => w) =
      fderiv ℂ v x w * iteratedFDeriv ℂ a g x (fun _ => w) +
        iteratedFDeriv ℂ a (fun y => v y * fderiv ℂ g y w) x (fun _ => w) := by
  have hgv : AnalyticAt ℂ (fun y => g y * v y) x := hg.fun_mul hv
  rw [← iteratedFDeriv_fderiv_diag hgv]
  have heq : (fun y => fderiv ℂ (fun y => g y * v y) y w) =ᶠ[𝓝 x]
      fun y => g y * fderiv ℂ v y w + v y * fderiv ℂ g y w := by
    filter_upwards [hg.eventually_analyticAt, hv.eventually_analyticAt] with y hgy hvy
    rw [fderiv_fun_mul hgy.differentiableAt hvy.differentiableAt]
    simp [smul_eq_mul]
  have h1 := analyticAt_fderiv_apply hv w
  have h2 := analyticAt_fderiv_apply hg w
  rw [(heq.iteratedFDeriv ℂ a).eq_of_nhds,
    fun_iteratedFDeriv_add_apply (hg.fun_mul h1).contDiffAt (hv.fun_mul h2).contDiffAt,
    top_mul hg h1 hga]
  simp [smul_eq_mul]

theorem order_one {v : E → ℂ} (hv : AnalyticAt ℂ v x) (hv0 : v x = 0) (w : E) :
    ∀ (a : ℕ) (g : E → ℂ), AnalyticAt ℂ g x → (∀ k < a, iteratedFDeriv ℂ k g x = 0) →
      iteratedFDeriv ℂ (a + 1) (fun y => g y * v y) x (fun _ => w) =
        ((a : ℂ) + 1) * iteratedFDeriv ℂ a g x (fun _ => w) * fderiv ℂ v x w := by
  intro a
  induction a with
  | zero =>
    intro g hg _
    rw [step hg hv (fun k hk => absurd hk (Nat.not_lt_zero k)) w]
    simp [iteratedFDeriv_zero_apply, hv0]
    ring
  | succ a ih =>
    intro g hg hga
    have hdg := analyticAt_fderiv_apply hg w
    have hdga : ∀ k < a, iteratedFDeriv ℂ k (fun y => fderiv ℂ g y w) x = 0 := by
      intro k hk
      ext m
      rw [iteratedFDeriv_fderiv_apply hg, hga (k + 1) (by omega)]
      simp
    have e : (fun y => v y * fderiv ℂ g y w) = fun y => fderiv ℂ g y w * v y := by
      funext y
      ring
    rw [step hg hv hga w, e, ih _ hdg hdga, iteratedFDeriv_fderiv_diag hg]
    push_cast
    ring

theorem mul_pow_jet {v : E → ℂ} (hv : AnalyticAt ℂ v x) (hv0 : v x = 0) (w : E)
    {g : E → ℂ} (hg : AnalyticAt ℂ g x) {c : ℕ} (hgc : ∀ k < c, iteratedFDeriv ℂ k g x = 0)
    {G : ℂ} (hG : iteratedFDeriv ℂ c g x (fun _ => w) = c.factorial * G) (m : ℕ) :
    (∀ k < c + m, iteratedFDeriv ℂ k (fun y => g y * v y ^ m) x = 0) ∧
      iteratedFDeriv ℂ (c + m) (fun y => g y * v y ^ m) x (fun _ => w) =
        (c + m).factorial * G * fderiv ℂ v x w ^ m := by
  induction m with
  | zero => simpa using ⟨hgc, hG⟩
  | succ m ih =>
    have hgm : AnalyticAt ℂ (fun y => g y * v y ^ m) x := hg.fun_mul (hv.fun_pow m)
    have e : (fun y => g y * v y ^ (m + 1)) = fun y => (g y * v y ^ m) * v y := by
      funext y
      ring
    rw [e, ← add_assoc]
    refine ⟨vanish_mul hgm hv ih.1 (vanish_one hv0), ?_⟩
    rw [order_one hv hv0 w (c + m) _ hgm ih.1, ih.2, Nat.factorial_succ]
    push_cast
    ring

theorem prod_pow_jet {p : ℕ} (u : Fin p → E → ℂ) (hu : ∀ i, AnalyticAt ℂ (u i) x)
    (hu0 : ∀ i, u i x = 0) (α : Fin p → ℕ) (w : E) (s : Finset (Fin p)) :
    AnalyticAt ℂ (fun y => ∏ i ∈ s, u i y ^ α i) x ∧
    (∀ k < ∑ i ∈ s, α i, iteratedFDeriv ℂ k (fun y => ∏ i ∈ s, u i y ^ α i) x = 0) ∧
    iteratedFDeriv ℂ (∑ i ∈ s, α i) (fun y => ∏ i ∈ s, u i y ^ α i) x (fun _ => w) =
      (∑ i ∈ s, α i).factorial * ∏ i ∈ s, fderiv ℂ (u i) x w ^ α i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, fun k hk => by simp at hk, ?_⟩
    · simp only [Finset.prod_empty]
      exact analyticAt_const
    · simp only [Finset.sum_empty, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, mul_one]
      exact iteratedFDeriv_zero_apply _
  | insert j s hj ih =>
    obtain ⟨ha, hv, hd⟩ := ih
    have e : (fun y => ∏ i ∈ insert j s, u i y ^ α i) =
        fun y => (∏ i ∈ s, u i y ^ α i) * u j y ^ α j := by
      funext y
      rw [Finset.prod_insert hj, mul_comm]
    have := mul_pow_jet (hu j) (hu0 j) w ha hv (G := ∏ i ∈ s, fderiv ℂ (u i) x w ^ α i) hd (α j)
    rw [e, Finset.sum_insert hj, Finset.prod_insert hj, add_comm (α j)]
    refine ⟨ha.fun_mul ((hu j).fun_pow _), this.1, ?_⟩
    rw [this.2]
    ring

theorem proof : Statement := by
  intro n p u h z₀ a hu hu0 hh
  have hP : ∀ α ∈ Finset.Nat.antidiagonalTuple p a,
      AnalyticAt ℂ (fun z => ∏ i, u i z ^ α i) z₀ ∧
      (∀ k < a, iteratedFDeriv ℂ k (fun z => ∏ i, u i z ^ α i) z₀ = 0) ∧
      ∀ w, iteratedFDeriv ℂ a (fun z => ∏ i, u i z ^ α i) z₀ (fun _ => w) =
        a.factorial * ∏ i, fderiv ℂ (u i) z₀ w ^ α i := by
    intro α hα
    rw [Finset.Nat.mem_antidiagonalTuple] at hα
    obtain ⟨h1, h2, -⟩ := prod_pow_jet u hu hu0 α 0 Finset.univ
    refine ⟨h1, hα ▸ h2, fun w => ?_⟩
    have := (prod_pow_jet u hu hu0 α w Finset.univ).2.2
    rwa [hα] at this
  have h2 : iteratedFDeriv ℂ a
      (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀ =
      ∑ α ∈ Finset.Nat.antidiagonalTuple p a,
        h α z₀ • iteratedFDeriv ℂ a (fun z => ∏ i, u i z ^ α i) z₀ := by
    rw [iteratedFDeriv_fun_sum_apply (fun α hα => ((hP α hα).1.fun_mul (hh α)).contDiffAt)]
    exact Finset.sum_congr rfl fun α hα => top_mul (hP α hα).1 (hh α) (hP α hα).2.1
  refine ⟨fun k hk => ?_, h2, fun w => ?_⟩
  · rw [iteratedFDeriv_fun_sum_apply (fun α hα => ((hP α hα).1.fun_mul (hh α)).contDiffAt)]
    exact Finset.sum_eq_zero fun α hα =>
      vanish_mul (hP α hα).1 (hh α) (hP α hα).2.1 (b := 0)
        (fun k hk => absurd hk (Nat.not_lt_zero k)) k (by omega)
  · rw [h2, sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [smul_apply, (hP α hα).2.2 w, smul_eq_mul]
    ring

end JetOfMonomialSum

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PShareCore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Filter Topology

noncomputable section

variable {n : ℕ} {MS : Type} [TopologicalSpace MS]

theorem HolomorphicAlong.analyticOnNhd {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) (e : OpenPartialHomeomorph MS (Fin n → ℂ))
    (hz : ∀ q ∈ e.source, z q = e q) : AnalyticOnNhd ℂ (u ∘ e.symm) e.target := by
  intro x hx
  have hq : e.symm x ∈ e.source := e.map_target hx
  obtain ⟨e', hq', hz', han⟩ := hu (e.symm x)
  have hex : e' (e.symm x) = x := by rw [← hz' _ hq', hz _ hq, e.right_inv hx]
  have hx' : x ∈ e'.target := hex ▸ e'.map_source hq'
  refine (han x hx').congr ?_
  have h1 : ∀ᶠ x' in 𝓝 x, x' ∈ e.target := e.open_target.mem_nhds hx
  have h2 : ∀ᶠ x' in 𝓝 x, e.symm x' ∈ e'.source :=
    (e.continuousAt_symm hx).preimage_mem_nhds (e'.open_source.mem_nhds hq')
  filter_upwards [h1, h2] with x' h1 h2
  have h3 : e' (e.symm x') = x' := by rw [← hz' _ h2, hz _ (e.map_target h1), e.right_inv h1]
  have h4 : e'.symm x' = e.symm x' := by
    calc e'.symm x' = e'.symm (e' (e.symm x')) := by rw [h3]
      _ = e.symm x' := e'.left_inv h2
  simp only [Function.comp_apply, h4]

theorem HolomorphicAlong.continuous {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) : Continuous u := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨e, hp, -, han⟩ := hu p
  have hc : ContinuousAt ((u ∘ e.symm) ∘ e) p :=
    (han (e p) (e.map_source hp)).continuousAt.comp (e.continuousAt hp)
  refine hc.congr ?_
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  simp [e.left_inv hq]

theorem HolomorphicAlong.mul {z : MS → (Fin n → ℂ)} {u v : MS → ℂ}
    (hu : HolomorphicAlong z u) (hv : HolomorphicAlong z v) :
    HolomorphicAlong z (fun p => u p * v p) := by
  intro p
  obtain ⟨e, hp, hz, -⟩ := hu p
  exact ⟨e, hp, hz, (hu.analyticOnNhd e hz).mul (hv.analyticOnNhd e hz)⟩

theorem HolomorphicAlong.pow {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) (k : ℕ) : HolomorphicAlong z (fun p => u p ^ k) := by
  intro p
  obtain ⟨e, hp, hz, -⟩ := hu p
  exact ⟨e, hp, hz, (hu.analyticOnNhd e hz).pow k⟩

theorem HolomorphicAlong.eq_zero_of_eventually [ConnectedSpace MS] {z : MS → (Fin n → ℂ)}
    {u : MS → ℂ} (hu : HolomorphicAlong z u) {p₀ : MS} (h₀ : u =ᶠ[𝓝 p₀] 0) : u = 0 := by
  set A : Set MS := {p | u =ᶠ[𝓝 p] 0} with hA
  have hAo : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hAc : IsClosed A := by
    refine isClosed_of_closure_subset fun p hp => ?_
    obtain ⟨e, hpe, hz, -⟩ := hu p
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_target (e p) (e.map_source hpe)
    have hV : e.source ∩ e ⁻¹' Metric.ball (e p) ε ∈ 𝓝 p :=
      inter_mem (e.open_source.mem_nhds hpe)
        ((e.continuousAt hpe).preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
    obtain ⟨q, ⟨hqs, hqb⟩, hqA⟩ := mem_closure_iff_nhds.1 hp _ hV
    have han : AnalyticOnNhd ℂ (u ∘ e.symm) (Metric.ball (e p) ε) :=
      (hu.analyticOnNhd e hz).mono hball
    have hev : (u ∘ e.symm) =ᶠ[𝓝 (e q)] 0 := by
      have ht : Tendsto e.symm (𝓝 (e q)) (𝓝 q) := by
        have := (e.continuousAt_symm (e.map_source hqs)).tendsto
        rwa [e.left_inv hqs] at this
      exact ht.eventually hqA
    have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (e p) ε).isPreconnected hqb hev
    show u =ᶠ[𝓝 p] 0
    filter_upwards [hV] with q' ⟨hq's, hq'b⟩
    have := hzero hq'b
    simpa [e.left_inv hq's] using this
  have huniv : A = Set.univ := IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨p₀, h₀⟩
  funext p
  have hp : p ∈ A := huniv ▸ Set.mem_univ p
  exact hp.self_of_nhds

theorem HolomorphicAlong.eq_zero_of_mul_eq_zero [ConnectedSpace MS] {z : MS → (Fin n → ℂ)}
    {g h : MS → ℂ} (hg : HolomorphicAlong z g) (hh : HolomorphicAlong z h)
    (hgh : ∀ p, g p * h p = 0) (hg0 : g ≠ 0) : h = 0 := by
  obtain ⟨p, hp⟩ : ∃ p, g p ≠ 0 := by
    by_contra H
    exact hg0 (funext fun p => by_contra fun hp => H ⟨p, hp⟩)
  have hne : ∀ᶠ q in 𝓝 p, g q ≠ 0 := hg.continuous.continuousAt.eventually_ne hp
  refine hh.eq_zero_of_eventually (p₀ := p) ?_
  filter_upwards [hne] with q hq
  exact (mul_eq_zero.1 (hgh q)).resolve_left hq

theorem eventually_norm_le_of_continuous {u : MS → ℂ} (hu : Continuous u) (p : MS) :
    ∀ᶠ q in 𝓝 p, ‖u q‖ ≤ ‖u p‖ + 1 := by
  have : ∀ᶠ q in 𝓝 p, ‖u q‖ < ‖u p‖ + 1 :=
    hu.norm.continuousAt.preimage_mem_nhds (Iio_mem_nhds (lt_add_one _))
  filter_upwards [this] with q hq using hq.le

theorem ShareCore.proof (hNorm : NormLemma.Statement) : ShareCore.Statement := by
  intro n MS _ _ _ _ De z δ f θ τ C e a hDe hcov hf hθ hτ hθ0 hτ0 hbound hord
  have hτa : HolomorphicAlong z (fun p => τ p ^ a) := hτ.pow a
  have hg : HolomorphicAlong z (fun p => θ p * τ p ^ a) := hθ.mul hτa
  have hg0 : (fun p => θ p * τ p ^ a) ≠ 0 := by
    intro H
    have h0 : (fun p => τ p ^ a) = 0 :=
      hθ.eq_zero_of_mul_eq_zero hτa (fun p => congrFun H p) hθ0
    exact hτ0 (funext fun p => eq_zero_of_pow_eq_zero (congrFun h0 p))
  have hu : HolomorphicAlong z (fun p => f p * θ p * τ p ^ a) := (hf.mul hθ).mul hτa
  have horder : ∀ p, z p = 0 → OrderGT z (fun p => f p * θ p * τ p ^ a) p e := by
    intro p hp
    obtain ⟨Cf, hCf⟩ := hord p hp
    refine ⟨Cf * ((‖θ p‖ + 1) * (‖τ p‖ + 1) ^ a), ?_⟩
    filter_upwards [hCf, eventually_norm_le_of_continuous hθ.continuous p,
      eventually_norm_le_of_continuous hτ.continuous p] with q hq1 hq2 hq3
    rw [norm_mul, norm_mul, norm_pow]
    have hr : 0 ≤ Cf * Real.sqrt (normSq (z q - z p)) ^ (e + 1) := (norm_nonneg _).trans hq1
    calc ‖f q‖ * ‖θ q‖ * ‖τ q‖ ^ a
        ≤ (Cf * Real.sqrt (normSq (z q - z p)) ^ (e + 1)) * (‖θ p‖ + 1) * (‖τ p‖ + 1) ^ a := by
          gcongr
      _ = Cf * ((‖θ p‖ + 1) * (‖τ p‖ + 1) ^ a) * Real.sqrt (normSq (z q - z p)) ^ (e + 1) := by
          ring
  have hu0 := hNorm n MS De z δ _ C e hDe hcov hu hbound horder
  exact hg.eq_zero_of_mul_eq_zero hf (fun p => by
    have := congrFun hu0 p
    simp only [Pi.zero_apply] at this
    linear_combination this) hg0

theorem ShareNumbers.proof : ShareNumbers.Statement := by
  intro D N T hD hN hT
  have h11 : 11 * D ≤ T := by nlinarith
  refine ⟨?_, ?_, ?_⟩ <;> omega

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PShellPolar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set

noncomputable section

theorem finrank_real_euclideanSpace_complex (D : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin D)) = 2 * D := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin D)), Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]

theorem volume_sum_normSq_lt_one (D : ℕ) :
    volume {w : Fin D → ℂ | ∑ i, ‖w i‖ ^ 2 < 1} =
      ENNReal.ofReal (Real.pi ^ D / (D.factorial : ℝ)) := by
  have h := Complex.volume_sum_rpow_lt_one (ι := Fin D) (p := 2) one_le_two
  simp only [Real.rpow_two] at h
  rw [h]
  congr 1
  have h2 : (2 : ℝ) / 2 + 1 = 2 := by norm_num
  have h3 : 2 * (Fintype.card (Fin D) : ℝ) / 2 + 1 = (D : ℝ) + 1 := by
    rw [Fintype.card_fin]; ring
  rw [h2, h3, Real.Gamma_two, Real.Gamma_nat_eq_factorial, mul_one, Fintype.card_fin]

theorem ShellPolar.proof : ShellPolar.Statement := by
  intro D hD a b ha hab
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hdim := finrank_real_euclideanSpace_complex D
  have : Nontrivial (EuclideanSpace ℂ (Fin D)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; omega)
  set L : (Fin D → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin D) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin D => ℂ)).symm with hL
  set e : (Fin D → ℂ) ≃ᵐ EuclideanSpace ℂ (Fin D) := L.toHomeomorph.toMeasurableEquiv with he
  set μ : Measure (EuclideanSpace ℂ (Fin D)) := Measure.map e volume with hμ
  have : μ.IsAddHaarMeasure := L.isAddHaarMeasure_map volume
  have hnorm : ∀ w : Fin D → ℂ, ‖e w‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_sq_eq]
    rfl

  set f : ℝ → ℝ := fun r => if a ≤ r ^ 2 ∧ r ^ 2 ≤ b then ((r ^ 2) ^ D)⁻¹ else 0 with hf
  have hS : MeasurableSet {w : Fin D → ℂ | a ≤ ∑ i, ‖w i‖ ^ 2 ∧ ∑ i, ‖w i‖ ^ 2 ≤ b} := by
    have hc : Continuous fun w : Fin D → ℂ => ∑ i, ‖w i‖ ^ 2 := by fun_prop
    exact (isClosed_le continuous_const hc).measurableSet.inter
      (isClosed_le hc continuous_const).measurableSet
  rw [← lintegral_indicator hS]
  have hpt : ∀ w : Fin D → ℂ,
      {w : Fin D → ℂ | a ≤ ∑ i, ‖w i‖ ^ 2 ∧ ∑ i, ‖w i‖ ^ 2 ≤ b}.indicator
        (fun w => ENNReal.ofReal (((∑ i, ‖w i‖ ^ 2) ^ D)⁻¹)) w =
        ENNReal.ofReal (f ‖e w‖) := by
    intro w
    simp only [hf, hnorm, indicator, mem_ofPred_eq]
    split_ifs <;> simp
  simp_rw [hpt]

  have hrad : EqOn (fun y : ℝ => y ^ (Module.finrank ℝ (EuclideanSpace ℂ (Fin D)) - 1) • f y)
      ((Icc (Real.sqrt a) (Real.sqrt b)).indicator fun y => y⁻¹) (Ioi 0) := by
    intro y hy
    have hy : 0 < y := hy
    have hmem : y ∈ Icc (Real.sqrt a) (Real.sqrt b) ↔ a ≤ y ^ 2 ∧ y ^ 2 ≤ b := by
      rw [mem_Icc, Real.sqrt_le_left hy.le, Real.le_sqrt' hy]
    simp only [hf, indicator, hmem, smul_eq_mul, hdim]
    split_ifs
    · have hk : 2 * D - 1 + 1 = 2 * D := by omega
      have hp : (y ^ 2) ^ D = y ^ (2 * D - 1) * y := by
        rw [← pow_mul, ← pow_succ, hk]
      rw [hp]
      field_simp
    · simp
  have hcont : IntegrableOn (fun y : ℝ => y⁻¹) (Icc (Real.sqrt a) (Real.sqrt b)) := by
    refine ContinuousOn.integrableOn_Icc (continuousOn_id.inv₀ fun y hy => ?_)
    exact (lt_of_lt_of_le (Real.sqrt_pos.2 ha) hy.1).ne'
  have hIoi : IntegrableOn
      (fun y : ℝ => y ^ (Module.finrank ℝ (EuclideanSpace ℂ (Fin D)) - 1) • f y) (Ioi 0) :=
    (integrableOn_congr_fun hrad measurableSet_Ioi).2
      ((integrable_indicator_iff measurableSet_Icc).2 hcont).integrableOn
  have hint_μ : Integrable (fun x : EuclideanSpace ℂ (Fin D) => f ‖x‖) μ :=
    (integrable_fun_norm_addHaar μ).2 hIoi
  have hint : Integrable (fun w : Fin D → ℂ => f ‖e w‖) volume :=
    (integrable_map_equiv e (fun x => f ‖x‖)).1 hint_μ
  have hnn : 0 ≤ᵐ[volume] fun w : Fin D → ℂ => f ‖e w‖ := by
    refine Filter.Eventually.of_forall fun w => ?_
    simp only [hf, Pi.zero_apply]
    split_ifs <;> positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  have h1 : ∫ w, f ‖e w‖ = ∫ x, f ‖x‖ ∂μ := (integral_map_equiv e (fun x => f ‖x‖)).symm

  have h2 : ∫ y in Ioi (0 : ℝ),
      y ^ (Module.finrank ℝ (EuclideanSpace ℂ (Fin D)) - 1) • f y = Real.log (b / a) / 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hrad, setIntegral_indicator measurableSet_Icc,
      inter_eq_right.2 (show Icc (Real.sqrt a) (Real.sqrt b) ⊆ Ioi 0 from
        fun y hy => lt_of_lt_of_le (Real.sqrt_pos.2 ha) hy.1),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
        (Real.sqrt_le_sqrt hab), integral_inv_of_pos (Real.sqrt_pos.2 ha) (Real.sqrt_pos.2 hb),
      ← Real.sqrt_div hb.le, Real.log_sqrt (div_pos hb ha).le]

  have h3 : μ.real (Metric.ball 0 1) = Real.pi ^ D / (D.factorial : ℝ) := by
    rw [Measure.real, hμ, Measure.map_apply e.measurable Metric.isOpen_ball.measurableSet]
    have hpre : e ⁻¹' Metric.ball 0 1 = {w : Fin D → ℂ | ∑ i, ‖w i‖ ^ 2 < 1} := by
      ext w
      simp only [mem_preimage, mem_ball_zero_iff, mem_ofPred_eq]
      rw [← hnorm w, sq_lt_one_iff₀ (norm_nonneg _)]
    rw [hpre, volume_sum_normSq_lt_one, ENNReal.toReal_ofReal (by positivity)]
  rw [h1, integral_fun_norm_addHaar μ, h2, h3, hdim, nsmul_eq_mul, smul_eq_mul]
  have hfac : (D.factorial : ℝ) = D * ((D - 1).factorial : ℝ) := by
    rw [← Nat.mul_factorial_pred (by omega : D ≠ 0)]; push_cast; ring
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  rw [hfac]
  field_simp
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsShareBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Filter Topology

noncomputable section

def shareExp (e : ℕ) : ℕ := (e + 15) / 16

def ShareBound.Statement : Prop :=
  ∀ (n : ℕ) (MS : Type) [TopologicalSpace MS] [T2Space MS] [SecondCountableTopology MS]
    [ConnectedSpace MS] (De : MvPolynomial (Fin n) ℂ) (z : MS → (Fin n → ℂ)) (δ : ℕ)
    (e : ℕ) (f τ w₀ : MS → ℂ) (s : Fin n → MS → ℂ) (hF hθ hτ hW wn rh : MS → ℝ)
    (κ Cf Cτ cw CompactFixesLatticeTheory K : ℝ),
    MvPolynomial.eval 0 De ≠ 0 →
    IsCoveringOfDegree z (complementOf De) δ →
    HolomorphicAlong z f → HolomorphicAlong z τ → HolomorphicAlong z w₀ →
    (∀ p, w₀ p ≠ 0) → (∀ p i, s i p = z p i * w₀ p) →
    (∀ p, 0 < hF p) → (∀ p, 0 < hθ p) → (∀ p, 0 < hτ p) → (∀ p, 0 < hW p) → 0 < κ →
    (∀ p, hF p * hθ p * hτ p ^ shareExp e = κ * hW p ^ e) →
    (∀ p, ‖f p‖ * hF p ≤ Cf) →
    (∃ (θ : MS → ℂ) (Cθ : ℝ), HolomorphicAlong z θ ∧ θ ≠ 0 ∧ ∀ p, ‖θ p‖ * hθ p ≤ Cθ) →
    τ ≠ 0 →
    (∀ p, ‖τ p‖ * hτ p ≤ Cτ * Real.exp (-(4 * rh p))) →
    0 < cw → (∀ p, 0 ≤ wn p) → (∀ p, cw * Real.exp (-(rh p / 2)) ≤ wn p ^ 2) →
    (∀ p, -K ≤ rh p) →
    (∀ p, wn p ≤ CompactFixesLatticeTheory * (hW p * Real.sqrt (‖w₀ p‖ ^ 2 + ∑ i, ‖s i p‖ ^ 2))) →
    f = 0 ∨ ∃ p, z p = 0 ∧ ¬ OrderGT z f p e

section Inhabitant

end Inhabitant

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

