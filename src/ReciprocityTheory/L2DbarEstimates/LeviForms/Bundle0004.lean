import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.Bergman
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff NNReal

noncomputable section

section
variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M]

def bgDens (ps : M → ℝ) (x : M) : ℝ≥0 := Real.toNNReal (Real.exp (-ps x))

def bgMeas (n : ℕ) (z : M → V n) (ps : M → ℝ) : Measure M :=
  (vol n z).withDensity (fun x => (bgDens ps x : ℝ≥0∞))

theorem bg_wint_eq_lintegral (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ) :
    wint n z f ps = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂bgMeas n z ps := by
  have hm : Measurable (fun x => (bgDens ps x : ℝ≥0∞)) :=
    ((Real.measurable_exp.comp hps.neg).real_toNNReal).coe_nnreal_ennreal
  unfold bgMeas wint
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
    (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, bgDens]
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two, mul_comm (‖f x‖ ^ 2), ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

theorem bg_eLpNorm_two_eq (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ) :
    eLpNorm f 2 (bgMeas n z ps) = wint n z f ps ^ (1/(2:ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), bg_wint_eq_lintegral n z ps hps f,
    ENNReal.toReal_ofNat]

theorem bg_memLp_of_wint (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ)
    (hf : AEStronglyMeasurable f (bgMeas n z ps)) (h : wint n z f ps < ⊤) :
    MemLp f 2 (bgMeas n z ps) := by
  refine ⟨hf, ?_⟩
  rw [bg_eLpNorm_two_eq n z ps hps f]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

theorem bg_wint_lt_top_of_memLp (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ)
    (hf : MemLp f 2 (bgMeas n z ps)) : wint n z f ps < ⊤ := by
  have h := hf.2
  rw [bg_eLpNorm_two_eq n z ps hps f] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h

end

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]

def bgHoloSub (n : ℕ) (z : M → V n) (ps : M → ℝ) : Submodule ℂ (Lp ℂ 2 (bgMeas n z ps)) where
  carrier := {f | ∃ G, Holo n z G ∧ (f : M → ℂ) =ᵐ[bgMeas n z ps] G}
  add_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    refine ⟨F + G, fun e he => (hF e he).add (hG e he), ?_⟩
    filter_upwards [Lp.coeFn_add f g, hf, hg] with x h1 h2 h3
    rw [h1, Pi.add_apply, Pi.add_apply, h2, h3]
  zero_mem' := ⟨0, fun e _ => differentiableOn_const (0 : ℂ), Lp.coeFn_zero _ _ _⟩
  smul_mem' := by
    rintro c f ⟨F, hF, hf⟩
    refine ⟨c • F, fun e he => (hF e he).const_smul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c f, hf] with x h1 h2
    rw [h1, Pi.smul_apply, Pi.smul_apply, h2]

theorem bgHoloSub_closed (n : ℕ) (X : EtaleStein n M) (ps : M → ℝ) (hps : SmoothR n X.z ps)
    (hpsm : Measurable ps) (hC : HoloClosedNeed n M) :
    IsClosed (bgHoloSub n X.z ps : Set (Lp ℂ 2 (bgMeas n X.z ps))) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨F, hFS, hF⟩ := mem_closure_iff_seq_limit.1 hf
  have hFS' : ∀ k, ∃ G, Holo n X.z G ∧ (F k : M → ℂ) =ᵐ[bgMeas n X.z ps] G := fun k => hFS k
  choose G hG hGe using hFS'
  have hfa := Lp.aestronglyMeasurable f
  have hf0m : Measurable (hfa.mk (f : M → ℂ)) := hfa.stronglyMeasurable_mk.measurable
  have hf0 : (f : M → ℂ) =ᵐ[bgMeas n X.z ps] hfa.mk (f : M → ℂ) := hfa.ae_eq_mk
  have hw : ∀ k, wint n X.z (fun x => G k x - hfa.mk (f : M → ℂ) x) ps =
      (eLpNorm (⇑(F k) - ⇑f) 2 (bgMeas n X.z ps)) ^ (2 : ℝ) := by
    intro k
    have h1 := bg_eLpNorm_two_eq n X.z ps hpsm (fun x => G k x - hfa.mk (f : M → ℂ) x)
    have h2 : eLpNorm (fun x => G k x - hfa.mk (f : M → ℂ) x) 2 (bgMeas n X.z ps) =
        eLpNorm (⇑(F k) - ⇑f) 2 (bgMeas n X.z ps) := by
      apply eLpNorm_congr_ae
      filter_upwards [hGe k, hf0] with x h3 h4
      rw [Pi.sub_apply, h3, h4]
    rw [← h2, h1, ← ENNReal.rpow_mul]
    norm_num
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F f).1 hF
  have hw0 : Tendsto (fun k => wint n X.z (fun x => G k x - hfa.mk (f : M → ℂ) x) ps) atTop (𝓝 0) := by
    simp_rw [hw]
    have := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp ht
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    exact this
  obtain ⟨G0, hG0, hfe⟩ := hC X ps G (hfa.mk (f : M → ℂ)) hps hG hf0m hw0
  show ∃ G, Holo n X.z G ∧ (f : M → ℂ) =ᵐ[bgMeas n X.z ps] G
  refine ⟨G0, hG0, hf0.trans ?_⟩
  exact (withDensity_absolutelyContinuous (vol n X.z) _ : bgMeas n X.z ps ≪ vol n X.z).ae_eq hfe

theorem bergmanExists (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : HoloClosedNeed n M) : BergmanExistsStatement n M := by
  intro X ps F0 hps hF0 hw
  have hpsc : Continuous ps := by
    have := Smooth.continuous n X.z X.isLocalHomeomorph _ hps
    exact (Complex.continuous_re.comp this).congr fun x => by simp
  have hpsm : Measurable ps := hpsc.measurable
  have hF0L : MemLp F0 2 (bgMeas n X.z ps) :=
    bg_memLp_of_wint n X.z ps hpsm F0 hF0.aestronglyMeasurable hw
  have hK : IsClosed (bgHoloSub n X.z ps : Set (Lp ℂ 2 (bgMeas n X.z ps))) :=
    bgHoloSub_closed n X ps hps hpsm hC
  haveI : CompleteSpace (bgHoloSub n X.z ps) := hK.completeSpace_coe
  set K := bgHoloSub n X.z ps with hKdef
  set P : Lp ℂ 2 (bgMeas n X.z ps) := (K.orthogonalProjection (hF0L.toLp F0) : Lp ℂ 2 (bgMeas n X.z ps))
    with hPdef
  have hPK : ∃ G, Holo n X.z G ∧ (P : M → ℂ) =ᵐ[bgMeas n X.z ps] G :=
    (K.orthogonalProjection (hF0L.toLp F0)).2
  obtain ⟨G, hG, hPG⟩ := hPK
  refine ⟨G, hG, bg_wint_lt_top_of_memLp n X.z ps hpsm G (MemLp.ae_eq hPG (Lp.memLp P)), ?_⟩
  intro H hH hwH
  have hHc : Continuous H := Smooth.continuous n X.z X.isLocalHomeomorph H (Holo.smooth n X.z H hH)
  have hHL : MemLp H 2 (bgMeas n X.z ps) :=
    bg_memLp_of_wint n X.z ps hpsm H hHc.aestronglyMeasurable hwH
  have hHK : hHL.toLp H ∈ K := show ∃ G, Holo n X.z G ∧ _ from ⟨H, hH, hHL.coeFn_toLp⟩
  have horth : inner ℂ (hHL.toLp H : Lp ℂ 2 (bgMeas n X.z ps)) (hF0L.toLp F0 - P) = 0 := by
    first
    | exact Submodule.inner_right_of_mem_orthogonal hHK (K.sub_starProjection_mem_orthogonal _)
    | exact Submodule.inner_right_of_mem_orthogonal hHK (K.sub_orthogonalProjection_mem_orthogonal _)
    | exact Submodule.inner_right_of_mem_orthogonal hHK (sub_orthogonalProjection_mem_orthogonal _)
    | exact orthogonalProjection_inner_eq_zero _ _ hHK
  rw [MeasureTheory.L2.inner_def] at horth
  have hint : ∫ a, inner ℂ ((hHL.toLp H : Lp ℂ 2 (bgMeas n X.z ps)) a)
      ((hF0L.toLp F0 - P : Lp ℂ 2 (bgMeas n X.z ps)) a) ∂(bgMeas n X.z ps) =
      ∫ a, (starRingEnd ℂ) (H a) * (F0 a - G a) ∂(bgMeas n X.z ps) := by
    refine integral_congr_ae ?_
    filter_upwards [hHL.coeFn_toLp, hF0L.coeFn_toLp, Lp.coeFn_sub (hF0L.toLp F0) P, hPG] with a h1 h2 h3 h4
    rw [h3, Pi.sub_apply, h1, h2, h4]
    simp [RCLike.inner_apply]
    try ring
  have hdm : Measurable (bgDens ps) := (Real.measurable_exp.comp hpsm.neg).real_toNNReal
  have key : ∫ x, (F0 x - G x) * (starRingEnd ℂ) (H x) * (Real.exp (-ps x) : ℂ) ∂vol n X.z =
      ∫ a, (starRingEnd ℂ) (H a) * (F0 a - G a) ∂(bgMeas n X.z ps) := by
    rw [bgMeas, integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [bgDens, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, Complex.real_smul]
    ring
  rw [key, ← hint]
  exact horth

end

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.LocallyCompactSpaceOfIsLocalHomeomorph
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem holo_continuous_of_isLocalHomeomorph {M : Type*} [TopologicalSpace M] (n : ℕ)
    (z : M → V n) (hz : IsLocalHomeomorph z) (f : M → ℂ) (hf : Holo n z f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hx' : e x ∈ e.target := e.map_source hx
  have h1 : ContinuousAt (f ∘ e.symm) (e x) :=
    (hf e he).continuousOn.continuousAt (e.open_target.mem_nhds hx')
  have h3 : ContinuousAt ((f ∘ e.symm) ∘ e) x := h1.comp (e.continuousAt hx)
  refine h3.congr ?_
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  show f (e.symm (e y)) = f y
  rw [e.left_inv hy]

theorem locallyCompactSpace_of_isLocalHomeomorph {M : Type*} [TopologicalSpace M] (n : ℕ)
    (z : M → V n) (hz : IsLocalHomeomorph z) : LocallyCompactSpace M := by
  have : ∀ x : M, ∃ e : OpenPartialHomeomorph M (V n), x ∈ e.source := fun x =>
    let ⟨e, hx, _⟩ := hz x; ⟨e, hx⟩
  choose c hc using this
  have hb : ∀ x : M, (𝓝 x).HasBasis
      (fun s ↦ s ∈ 𝓝 (c x x) ∧ IsCompact s ∧ s ⊆ (c x).target)
      fun s ↦ (c x).symm '' s := fun x ↦ by
    rw [← (c x).symm_map_nhds_eq (hc x)]
    exact ((compact_basis_nhds (c x x)).hasBasis_self_subset
      ((c x).open_target.mem_nhds ((c x).map_source (hc x)))).map _
  refine .of_hasBasis hb ?_
  rintro x s ⟨_, h₂, h₃⟩
  exact h₂.image_of_continuousOn ((c x).continuousOn_symm.mono h₃)

theorem ev_pos_of_not_mem_zeroSet {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ)
    (r : ℝ) (hr : 0 < r) (x : M) (hx : x ∉ zeroSet n g) : 0 < ev n g ph r x := by
  simp only [zeroSet, Set.mem_ofPred_eq, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  have hs : 0 < ∑ i, ‖g i x‖ ^ 2 :=
    Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  exact div_pos (mul_pos hs (Real.exp_pos _)) (pow_pos hr 2)

theorem localData (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] : LocalStatement n M := by
  intro z g ph r N hz hg hph hr hS _hJ hN
  have := locallyCompactSpace_of_isLocalHomeomorph n z hz
  obtain ⟨U, hU, hUd⟩ := hS.t2_separation
  have hex : ∀ p ∈ zeroSet n g, ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ closure V ⊆ N p ∩ U p ∧
      IsCompact (closure V) := by
    intro p hp
    obtain ⟨V, hVo, hpV, hcl, hcpt⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := p)) ((hN p hp).1.inter (hU p).2)
      (Set.singleton_subset_iff.mpr ⟨(hN p hp).2, (hU p).1⟩)
    exact ⟨V, hVo, hpV (Set.mem_singleton p), hcl, hcpt⟩
  choose! W hWo hpW hWcl hWc using hex
  have hgc : ∀ i, Continuous (g i) := fun i =>
    holo_continuous_of_isLocalHomeomorph n z hz _ (hg i)
  have hphc : Continuous ph :=
    (Complex.continuous_re.comp (Smooth.continuous n z hz _ hph)).congr (fun x => by simp)
  have hevc : Continuous (ev n g ph r) := by
    unfold ev
    fun_prop
  have hfr : ∀ p ∈ zeroSet n g, ∀ x ∈ frontier (W p), x ∉ zeroSet n g := by
    intro p hp x hx hxS
    have hxU : x ∈ U p := (hWcl p hp (frontier_subset_closure hx)).2
    by_cases hxp : x = p
    · rw [hxp, (hWo p hp).frontier_eq] at hx
      exact hx.2 (hpW p hp)
    · exact Set.disjoint_left.mp (hUd hxS hp hxp) (hU x).1 hxU
  have hK : IsCompact (⋃ p ∈ zeroSet n g, frontier (W p)) :=
    hS.isCompact_biUnion fun p hp =>
      (hWc p hp).of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hpos : ∀ x ∈ ⋃ p ∈ zeroSet n g, frontier (W p), 0 < ev n g ph r x := by
    intro x hx
    obtain ⟨p, hp, hxf⟩ := Set.mem_iUnion₂.mp hx
    exact ev_pos_of_not_mem_zeroSet n g ph r hr x (hfr p hp x hxf)
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' hevc.continuousOn hpos
  refine ⟨W, m, ⟨hm, fun p hp => ⟨hWo p hp, hpW p hp, hWc p hp,
    fun x hx => hmK x (Set.mem_biUnion hp hx), fun q hq hqp => ?_⟩⟩,
    fun p hp x hx => (hWcl p hp (subset_closure hx)).1⟩
  exact Disjoint.mono (fun x hx => (hWcl p hp hx).2) (fun x hx => (hWcl q hq hx).2)
    (hUd hp hq hqp.symm)

end ReciprocityTheory.L2DbarEstimates.I
end

