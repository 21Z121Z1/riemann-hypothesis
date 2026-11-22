import Development.WeilBound.ThetaLifts.SmallCones.RightOfCompact
import Development.WeilBound.CoreStatements.ThetaDilations.Nuabs
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.WeilBound.CoreStatements.ThetaDilations.ContinuousPm

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.UnfAbs
section
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise

namespace PositivityTheory.ThKCT.Unf

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {N : Type} [TopologicalSpace N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  {T : Type} [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]

structure Par (μN : Measure N) (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0) : Prop where
  cn : Continuous nn
  ci : Continuous ι
  cm : Continuous mm
  cχ : Continuous χ
  emb : IsClosedEmbedding fun z : N × H × T => nn z.1 * ι z.2.1 * mm z.2.2
  h1 : ∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)
  h2 : ∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u
  h3 : ∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t
  h4 : ∀ u t, mm t * ι u = ι u * mm t
  ne : μN ≠ 0

variable {μN : Measure N} [SigmaFinite μN] [IsFiniteMeasureOnCompacts μN] {nn : N → G} {ι : H →* G} {mm : T →* G} {χ : T →* ℝ≥0}
  (ν : Measure G) [ν.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure] (μT : Measure T) [μT.IsHaarMeasure]

theorem haar_eq (h : Par μN nn ι mm χ) {K : Subgroup G} (hK : IsCompact (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure]
    (hG : ∀ g, ∃ p u t, ∃ k ∈ K, g = nn p * ι u * mm t * k) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      c * ∫⁻ g, φ g ∂ν = ∫⁻ k, ∫⁻ t, (∫⁻ u, ∫⁻ p, φ (nn p * ι u * mm t * k.1) ∂μN ∂μH) * χ t ∂μT ∂μK := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := right_of_compact μK
  have cn := h.cn.measurable
  have ci := h.ci.measurable
  have cm := h.cm.measurable
  have hχ : Measurable fun s => (χ s : ℝ≥0∞) := h.cχ.measurable.coe_nnreal_ennreal
  set wd := μT.withDensity fun s => (χ s : ℝ≥0∞) with hwd
  haveI : IsLocallyFiniteMeasure wd := IsLocallyFiniteMeasure.withDensity_coe h.cχ
  set ρ := μN.prod (μH.prod wd) with hρ
  have hΨ := h.emb.continuous.measurable
  set l := ρ.map fun z : N × H × T => nn z.1 * ι z.2.1 * mm z.2.2 with hl
  have hmul : Measurable fun z : G × K => z.1 * z.2.1 := by fun_prop
  set m := (l.prod μK).map fun z : G × K => z.1 * z.2.1 with hm
  haveI : IsFiniteMeasureOnCompacts m := ⟨fun C hC => by
    rw [hm, Measure.map_apply hmul hC.measurableSet]
    have hc := hC.mul hK.inv
    refine (measure_mono (t := (C * (K : Set G)⁻¹) ×ˢ univ) fun z hz => ⟨⟨_, hz, z.2.1⁻¹, by simp, by simp⟩, trivial⟩).trans_lt ?_
    rw [Measure.prod_prod, hl, Measure.map_apply hΨ hc.measurableSet]
    exact ENNReal.mul_lt_top (h.emb.isCompact_preimage hc).measure_lt_top (measure_lt_top _ _)⟩
  obtain ⟨c, hc, e⟩ := eq_smul ν m (P := {g | ∃ p u t, g = nn p * ι u * mm t}) (K := K) (by
      rintro _ ⟨p, u, t, rfl⟩
      have := PositivityTheory.PlacePermOperatorBicommutantSpan.nuabs G N H T μN μH μT nn ι mm χ cn ci cm h.cχ.measurable h.h1 h.h2 h.h3 h.h4 p u t
      have e := (MeasurePreserving.prod ⟨measurable_const_mul _, this⟩ (MeasurePreserving.id μK)).map_eq
      rw [hm, Measure.map_map (measurable_const_mul _) hmul]
      conv_rhs => rw [← e, Measure.map_map hmul ((measurable_const_mul _).prodMap measurable_id)]
      exact congrArg (fun f => Measure.map f _) (funext fun z => (mul_assoc _ _ _).symm))
    (fun k hk => by
      have e := (MeasurePreserving.prod (MeasurePreserving.id l) (measurePreserving_mul_right μK ⟨k, hk⟩)).map_eq
      rw [hm, Measure.map_map (measurable_mul_const _) hmul]
      conv_rhs => rw [← e, Measure.map_map hmul (measurable_id.prodMap (measurable_mul_const _))]
      exact congrArg (fun f => Measure.map f _) (funext fun z => mul_assoc _ _ _))
    hK fun g => by
      obtain ⟨p, u, t, k, hk, rfl⟩ := hG g
      exact ⟨_, ⟨p, u, t, rfl⟩, k, hk, rfl⟩
  refine ⟨c, fun h0 => ?_, hc, fun φ hφ => ?_⟩
  · have := congrArg (fun m : Measure G => m univ) e
    simp only [h0, zero_smul, Measure.coe_zero, Pi.zero_apply] at this
    rw [hm, Measure.map_apply hmul MeasurableSet.univ, preimage_univ, ← univ_prod_univ, Measure.prod_prod, hl,
      Measure.map_apply hΨ MeasurableSet.univ, preimage_univ, ← univ_prod_univ, Measure.prod_prod, ← univ_prod_univ,
      Measure.prod_prod] at this
    refine mul_ne_zero (mul_ne_zero (Measure.measure_univ_ne_zero.2 h.ne) (mul_ne_zero
      (isOpen_univ.measure_ne_zero μH univ_nonempty) fun h1 => ?_)) (isOpen_univ.measure_ne_zero μK univ_nonempty) this
    rw [hwd, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_eq_zero_iff hχ] at h1
    have := congrFun ((Continuous.ae_eq_iff_eq μT (ENNReal.continuous_coe.comp h.cχ) continuous_zero).1 h1) 1
    simp at this
  · rw [← smul_eq_mul, ← lintegral_smul_measure, ← e, hm, lintegral_map hφ hmul,
      lintegral_prod_symm _ (Measurable.aemeasurable (by fun_prop))]
    refine lintegral_congr fun k => ?_
    rw [hl, lintegral_map (by fun_prop) hΨ, hρ, lintegral_prod_symm _ (Measurable.aemeasurable (by fun_prop)),
      lintegral_prod_symm _ (Measurable.aemeasurable (by fun_prop)), hwd,
      lintegral_withDensity_eq_lintegral_mul _ hχ (by fun_prop)]
    exact lintegral_congr fun t => mul_comm _ _

omit [T2Space G] [LocallyCompactSpace G] in
theorem exists_cut (Q : Subgroup G) [Countable Q] [DiscreteTopology Q] :
    ∃ 𝓖 : Set G, MeasurableSet 𝓖 ∧ (∀ x, ∑' q : Q, 𝓖.indicator (1 : G → ℝ≥0∞) (q.1 * x) = 1) ∧
      ∀ μ : Measure G, IsFundamentalDomain Q 𝓖 μ := by
  obtain ⟨𝓖, h1, h2⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Q
  refine ⟨𝓖, h1, fun x => ?_, fun μ => IsFundamentalDomain.mk' h1.nullMeasurableSet h2⟩
  obtain ⟨q, hq, hu⟩ := h2 x
  exact (tsum_eq_single q fun q' h => indicator_of_notMem (fun h' => h (hu q' h')) _).trans (indicator_of_mem hq _)

theorem fold (h : Par μN nn ι mm χ) {Q ΓN : Subgroup G} [Countable Q] [DiscreteTopology Q] {Γ₁ : Subgroup H} [Countable Γ₁]
    (hN : ΓN ≤ Q) (hNn : ∀ δ ∈ ΓN, ∃ p, δ = nn p) (h₁ : ∀ γ ∈ Γ₁, ι γ ∈ Q)
    (hb : ∀ q ∈ Q, ∃! z : Γ₁ × ΓN, q = ι z.1 * z.2) {C : Set N} (hC : IsCompact C)
    (hcov : ∀ p, ∃ δ ∈ ΓN, ∃ p' ∈ C, δ * nn p = nn p') {D₁ : Set H} (hD₁ : IsFundamentalDomain Γ₁ D₁ μH) :
    ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ⊤ ∧ ∀ β : G → ℝ≥0∞, Measurable β → (∀ x, ∑' q : Q, β (q.1 * x) = 1) →
      ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ p g, φ (nn p * g) = φ g) → (∀ q ∈ Q, ∀ g, φ (q * g) = φ g) → ∀ y,
      ∫⁻ u, ∫⁻ p, β (nn p * ι u * y) * φ (nn p * ι u * y) ∂μN ∂μH = a * ∫⁻ u in D₁, φ (ι u * y) ∂μH := by
  have cn := h.cn.measurable
  have ci := h.ci.measurable
  haveI : Countable ΓN := (Subgroup.inclusion_injective hN).countable
  haveI : DiscreteTopology ΓN := DiscreteTopology.of_continuous_injective
    (continuous_inclusion hN) (Subgroup.inclusion_injective hN)
  obtain ⟨𝓕, f1, -, f3⟩ := exists_cut ΓN
  set l := μN.map nn with hl
  haveI : SMulInvariantMeasure ΓN G l := ⟨fun δ s hs => by
    obtain ⟨p, hp⟩ := hNn δ δ.2
    obtain ⟨L, a1, a2⟩ := h.h1 p
    have e : Measurable fun x : G => δ • x := measurable_const_mul δ.1
    rw [hl, Measure.map_apply cn (e hs), Measure.map_apply cn hs, ← a1.measure_preimage (cn hs).nullMeasurableSet]
    congr 1
    ext x
    simp only [mem_preimage, ← a2, ← hp]
    rfl⟩
  have fd := f3 l
  refine ⟨l 𝓕, fd.measure_ne_zero ?_, ne_top_of_le_ne_top (b := l (nn '' C)) ?_ ?_, fun β hβ hβ1 φ hφ i1 i2 y => ?_⟩
  · rw [hl, Ne, Measure.map_eq_zero_iff cn.aemeasurable]; exact h.ne
  · have hc := hC.image h.cn
    have : IsCompact (nn ⁻¹' (nn '' C)) := by
      have h2 := (h.emb.isCompact_preimage hc).image continuous_fst
      refine h2.of_isClosed_subset (hc.isClosed.preimage h.cn) fun p hp => ⟨(p, 1, 1), by simpa using hp, rfl⟩
    rw [hl, Measure.map_apply cn hc.measurableSet]
    exact this.measure_lt_top.ne
  · have hm := (hC.image h.cn).measurableSet
    rw [fd.measure_eq_tsum' (nn '' C)]
    have hS : MeasurableSet (⋃ δ : ΓN, δ • (nn '' C)) := MeasurableSet.iUnion fun δ => hm.const_smul δ
    have e : l 𝓕 = l (𝓕 ∩ ⋃ δ : ΓN, δ • (nn '' C)) := by
      rw [hl, Measure.map_apply cn f1, Measure.map_apply cn (f1.inter hS)]
      congr 1
      ext p
      refine ⟨fun hp => ⟨hp, ?_⟩, fun hp => hp.1⟩
      obtain ⟨δ, h1, p', h2, h3⟩ := hcov p
      exact mem_iUnion.2 ⟨⟨δ, h1⟩⁻¹, mem_smul_set_iff_inv_smul_mem.2 ⟨p', h2, by simpa using h3.symm⟩⟩
    rw [e, inter_iUnion]
    refine (measure_iUnion_le _).trans (le_of_eq ?_)
    rw [← (Equiv.inv ΓN).tsum_eq]
    refine tsum_congr fun δ => ?_
    rw [← measure_smul l δ, smul_set_inter, Equiv.inv_apply, smul_inv_smul, inter_comm]
  · let e : Γ₁ × ΓN ≃ Q := Equiv.ofBijective (fun z => ⟨ι z.1 * z.2, Q.mul_mem (h₁ _ z.1.2) (hN z.2.2)⟩)
      ⟨fun z z' hz => (hb _ (Q.mul_mem (h₁ _ z.1.2) (hN z.2.2))).unique rfl (congrArg Subtype.val hz), fun q => by
        obtain ⟨z, hz, -⟩ := hb q q.2
        exact ⟨z, Subtype.ext hz.symm⟩⟩
    have inner : ∀ x, ∑' γ : Γ₁, ∫⁻ p, β (nn p * ι γ * x) ∂μN = l 𝓕 := fun x => by
      have e1 : ∀ γ : Γ₁, ∫⁻ p, β (nn p * ι γ * x) ∂μN = ∑' δ : ΓN, ∫⁻ g in 𝓕, β (ι γ * δ * (g * x)) ∂l := fun γ => by
        obtain ⟨L, a1, a2⟩ := h.h2 γ
        rw [← a1.lintegral_comp (f := fun p => β (nn p * ι γ * x)) (by fun_prop)]
        simp only [← a2]
        rw [← lintegral_map (f := fun g => β (ι γ * g * x)) (by fun_prop) cn, ← hl, fd.lintegral_eq_tsum'']
        simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
      simp only [e1]
      rw [← ENNReal.tsum_prod, ← lintegral_tsum fun z => Measurable.aemeasurable (by fun_prop)]
      have : ∀ g, ∑' z : Γ₁ × ΓN, β (ι z.1 * z.2 * (g * x)) = 1 := fun g => by
        rw [← hβ1 (g * x), ← e.tsum_eq]; rfl
      simp only [this, lintegral_one, Measure.restrict_apply_univ]
    have e2 : ∀ u, ∫⁻ p, β (nn p * ι u * y) * φ (nn p * ι u * y) ∂μN = (∫⁻ p, β (nn p * ι u * y) ∂μN) * φ (ι u * y) :=
      fun u => by
        simp only [mul_assoc _ (ι u), i1]
        rw [lintegral_mul_const _ (by fun_prop)]
    simp only [e2]
    rw [hD₁.lintegral_eq_tsum'', ← lintegral_tsum fun γ => Measurable.aemeasurable (by fun_prop),
      ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_congr fun u => ?_
    simp only [Subgroup.smul_def, smul_eq_mul, map_mul, mul_assoc, i2 _ (h₁ _ (Subtype.prop _))]
    rw [ENNReal.tsum_mul_right, ← inner (ι u * y)]
    simp only [mul_assoc]

end PositivityTheory.ThKCT.Unf
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.UnfPar
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology PositivityTheory.PlacePermOperatorBicommutantSpan
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.ThKCT.Unf

set_option maxHeartbeats 1600000 in
theorem par2 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ (nn : (Fin 1 → Fin M → AF F ⊗[F] E) × AF F → HA (AF F) σ (hypJ J)) (ι : HA (AF F) σ J →* HA (AF F) σ (hypJ J)) (mm : (AF F ⊗[F] E)ˣ →* HA (AF F) σ (hypJ J)) (c : (Fin 1 → Fin M → AF F ⊗[F] E) → (Fin 1 → Fin M → AF F ⊗[F] E) → AF F), (∀ p u (a : (AF F ⊗[F] E)ˣ), ∃ b r, (nn p * ι u * mm a).1.val = pm (a : AF F ⊗[F] E) b r (sigR (AF F) σ (a⁻¹ : (AF F ⊗[F] E)ˣ)) (sigR (AF F) σ (a⁻¹ : (AF F ⊗[F] E)ˣ) • p.1 0) u.1.val ∧ (p = (0, 0) → b = 0 ∧ r = 0)) ∧ IsClosedEmbedding (fun z : ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) × HA (AF F) σ J × (AF F ⊗[F] E)ˣ => nn z.1 * ι z.2.1 * mm z.2.2) ∧ Continuous nn ∧ Continuous ι ∧ Continuous mm ∧ (Continuous fun p : (Fin 1 → Fin M → AF F ⊗[F] E) × (Fin 1 → Fin M → AF F ⊗[F] E) => c p.1 p.2) ∧ nn (0, 0) = 1 ∧ (∀ w s w' s', nn (w, s) * nn (w', s') = nn (w + w', s + s' + c w w')) ∧ (∀ w, c 0 w = 0) ∧ (∀ u w s, ι u * nn (w, s) = nn (actW (AF F) σ J u w, s) * ι u) ∧ (∀ (a : (AF F ⊗[F] E)ˣ) w s, mm a * nn (w, s) = nn (sigR (AF F) σ (a : AF F ⊗[F] E) • w, Algebra.norm (AF F) (a : AF F ⊗[F] E) * s) * mm a) ∧ (∀ u a, mm a * ι u = ι u * mm a) ∧ (∀ p u (a : (AF F ⊗[F] E)ˣ), actW (AF F) σ _ (nn p * ι u * mm a) (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ (∀ (h : HA (AF F) σ (hypJ J)) (a : (AF F ⊗[F] E)ˣ), actW (AF F) σ _ h (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1) → ∃ p u, h = nn p * ι u * mm a) ∧ (∀ (w : Fin 1 → Fin M → E) (s : F), HA.mat (AF F) σ (hypJ J) (nn (ratTup (AF F) w, algebraMap F (AF F) s)) ∈ HFin (AF F) σ (hypJ J)) ∧ (∀ u, HA.mat (AF F) σ J u ∈ HFin (AF F) σ J → HA.mat (AF F) σ (hypJ J) (ι u) ∈ HFin (AF F) σ (hypJ J)) ∧ ∀ (l : Eˣ) (a : (AF F ⊗[F] E)ˣ), (a : AF F ⊗[F] E) = inclR (AF F) (l : E) → HA.mat (AF F) σ (hypJ J) (mm a) ∈ HFin (AF F) σ (hypJ J) := by
  intro F E _ _ _ _ _ σ hcm M J hJ
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, -, -, _, hsc, htc, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  obtain ⟨δ, hδ0, hδ⟩ := exists_anti hcm
  set s := sigR (AF F) σ with hsdef
  have hs : ∀ x, s (s x) = x := GlobalTheory.GaussMean.OneVec.sigR_sigR (AF F) hcm
  have hsa : ∀ t : AF F, s (algebraMap _ _ t) = algebraMap _ _ t := GlobalTheory.GaussMean.OneVec.sigR_algebraMap (AF F)
  have hsi : ∀ x : E, s (inclR (AF F) x) = inclR (AF F) (σ x) := fun x => by simp [hsdef, sigR, inclR]
  have hJc := cT_JR (AF F) hJ
  have hJi : JR (F := F) (AF F) J⁻¹ * JR (F := F) (AF F) J = 1 := by
    rw [JR, JR, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ.2), Matrix.map_one _ (map_zero _) (map_one _)]
  have hH : JR (F := F) (AF F) (hypJ J) = hypJ (JR (F := F) (AF F) J) := hypJ_map _ J
  have hHi : hypJ (JR (F := F) (AF F) J⁻¹) * JR (F := F) (AF F) (hypJ J) = 1 := by rw [hH]; exact hyp_inv hJi
  set κ : AF F ⊗[F] E := inclR (AF F) (1 / 2 : E) with hκ
  set dl : AF F ⊗[F] E := inclR (AF F) δ with hdl
  set di : AF F ⊗[F] E := inclR (AF F) δ⁻¹ with hdi
  have hκ2 : 2 * κ = 1 := by rw [hκ, ← map_ofNat (inclR (F := F) (E := E) (AF F)) 2, ← map_mul]; norm_num
  have hκs : s κ = κ := by rw [hκ, hsi, map_div₀, map_one, map_ofNat]
  have hdls : s dl = -dl := by rw [hdl, hsi, hδ, map_neg]
  have hdis : s di = -di := by rw [hdi, hsi, map_inv₀, hδ, inv_neg, map_neg]
  have hdd : di * dl = 1 := by rw [hdi, hdl, ← map_mul, inv_mul_cancel₀ hδ0, map_one]
  set sc : AF F ⊗[F] E → AF F := fun y => algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) _ (di * y) with hsc'
  have hscc : Continuous sc := continuous_const.mul (htc.comp (continuous_const.mul continuous_id))
  have sc1 : ∀ y, s y = -y → algebraMap _ _ (sc y) * dl = y := fun y hy => by
    have : algebraMap _ _ (sc y) = di * y :=
      GlobalTheory.GaussMean.OneVec.fixed_eq (AF F) hcm (show s (di * y) = di * y by rw [map_mul, hdis, hy, neg_mul_neg])
    rw [this, mul_right_comm, hdd, one_mul]
  have sc2 : ∀ t : AF F, sc (algebraMap _ _ t * dl) = t := fun t => by
    simp only [hsc', mul_left_comm di, hdd, mul_one]
    exact GlobalTheory.GaussMean.OneVec.half_trace (AF F) hcm t
  set hf := hform s (JR (AF F) J) with hhf
  have hfc : ∀ x y, s (hf x y) = hf y x := hform_conj hs hJc
  set z : (Fin 1 → Fin M → AF F ⊗[F] E) × AF F → AF F ⊗[F] E :=
    fun p => -(κ * hf (p.1 0) (p.1 0)) + algebraMap _ _ p.2 * dl with hz
  have hzu : ∀ p, z p + s (z p) + hf (p.1 0) (p.1 0) = 0 := fun p => by
    simp only [hz, map_add, map_neg, map_mul, hκs, hfc, hsa, hdls]
    linear_combination (-hf (p.1 0) (p.1 0)) * hκ2
  have ext : ∀ g g' : HA (AF F) σ (hypJ J), g.1.val = g'.1.val → g = g' := fun g g' h =>
    Subtype.ext (Units.ext h)
  let nn : (Fin 1 → Fin M → AF F ⊗[F] E) × AF F → HA (AF F) σ (hypJ J) := fun p =>
    mkU s hHi (nM s (JR (AF F) J) (p.1 0) (z p)) (by rw [hH]; exact nM_unit hs hJc (hzu p))
  let ι : HA (AF F) σ J →* HA (AF F) σ (hypJ J) :=
    { toFun := fun u => mkU s hHi (pm 1 0 0 1 0 u.1.val) (by rw [hH]; exact iM_unit u.2)
      map_one' := ext _ _ pm_one
      map_mul' := fun u v => ext _ _ (by
        show pm 1 0 0 1 0 (u.1.val * v.1.val) = pm 1 0 0 1 0 u.1.val * pm 1 0 0 1 0 v.1.val
        simp [pm_mul]) }
  let mm : (AF F ⊗[F] E)ˣ →* HA (AF F) σ (hypJ J) :=
    { toFun := fun a => mkU s hHi (pm (a : AF F ⊗[F] E) 0 0 (s (a⁻¹ : (AF F ⊗[F] E)ˣ)) 0 1) (by rw [hH]; exact mM_unit hs a)
      map_one' := ext _ _ (by
        show pm _ 0 0 (s _) 0 1 = 1
        rw [inv_one, Units.val_one, map_one, pm_one])
      map_mul' := fun a b => ext _ _ (by
        show pm _ 0 0 (s _) 0 1 = pm _ 0 0 (s _) 0 1 * pm _ 0 0 (s _) 0 1
        simp [pm_mul, mul_comm]) }
  have hval : ∀ p u a, (nn p * ι u * mm a).1.val = pm (a : AF F ⊗[F] E) (z p * s (a⁻¹ : (AF F ⊗[F] E)ˣ))
      (-(((s ∘ p.1 0) ᵥ* JR (AF F) J) ᵥ* u.1.val)) (s (a⁻¹ : (AF F ⊗[F] E)ˣ))
      (s (a⁻¹ : (AF F ⊗[F] E)ˣ) • p.1 0) u.1.val := fun p u a => nim _ _ _ _ _
  have I1 : IsInducing fun g : HA (AF F) σ J => g.1.val := continuous_UJ hsc hJi
  have I2 : IsInducing fun g : HA (AF F) σ (hypJ J) => g.1.val := continuous_UJ hsc hHi
  have hfC : Continuous fun p : (Fin M → AF F ⊗[F] E) × (Fin M → AF F ⊗[F] E) => hf p.1 p.2 := by
    simp only [hhf, hform]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hsc.comp ((continuous_apply i).comp continuous_fst)).mul continuous_const).mul
        ((continuous_apply j).comp continuous_snd)
  have halg : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) := by
    have := GlobalTheory.GaussMean.OneVec.isModTop (F := F) (E := E) (AF F)
    have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  have c0 : Continuous fun p : (Fin 1 → Fin M → AF F ⊗[F] E) × AF F => p.1 0 := (continuous_apply 0).comp continuous_fst
  have hzc : Continuous z :=
    (continuous_const.mul (hfC.comp (c0.prodMk c0))).neg.add ((halg.comp continuous_snd).mul continuous_const)
  have hvm : ∀ A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E), Continuous fun w : Fin M → AF F ⊗[F] E => (s ∘ w) ᵥ* A :=
    fun A => (continuous_pi fun i => hsc.comp (continuous_apply i)).matrix_vecMul continuous_const
  have cn : Continuous nn := I2.continuous_iff.2 (continuous_pm continuous_const hzc ((hvm _).comp c0).neg
    continuous_const c0 continuous_const)
  have ci : Continuous ι := I2.continuous_iff.2 (continuous_pm continuous_const continuous_const continuous_const
    continuous_const continuous_const I1.continuous)
  have cm : Continuous mm := I2.continuous_iff.2 (continuous_pm Units.continuous_val continuous_const continuous_const
    (hsc.comp Units.continuous_coe_inv) continuous_const continuous_const)
  have dec : ∀ h : HA (AF F) σ (hypJ J), (∀ i : Fin (M + 1), h.1.val i.succ 0 = 0) →
      ∃ p u a, h = nn p * ι u * mm a := fun h h0 => by
    obtain ⟨w, y, U, a, e1, e2, e3⟩ := par_dec hs (J := JR (AF F) J) (by rw [← hH]; exact h.2) h0
    have e4 : z (fun _ => w, sc (y + κ * hf w w)) = y := by
      simp only [hz]
      rw [sc1 _ (by rw [map_add, map_mul, hκs, hfc]; linear_combination e1 + hf w w * hκ2)]; ring
    exact ⟨(fun _ => w, sc (y + κ * hf w w)), mkU s hJi U e2, a, ext _ _ (e3.trans (congrArg (fun y => nM s (JR (AF F) J) w y *
      pm 1 0 0 1 0 U * pm (a : AF F ⊗[F] E) 0 0 (s (a⁻¹ : (AF F ⊗[F] E)ˣ)) 0 1) e4.symm))⟩
  have act : ∀ (h : HA (AF F) σ (hypJ J)) i, actW (AF F) σ _ h (eOne _ (M + 1)) 0 i = h.1.val i 0 :=
    fun h i => by simp [actW, actTup, eOne, HA.mat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have rat : ∀ (g : Matrix (Fin (M + 2)) (Fin (M + 2)) E) (h : HA (AF F) σ (hypJ J)),
      cT (σ : E →+* E) g * hypJ J * g = hypJ J → h.1.val = g.map (inclR (AF F)) →
      HA.mat (AF F) σ (hypJ J) h ∈ HFin (AF F) σ (hypJ J) := fun g h hg e =>
    ⟨_, (mkU (σ : E →+* E) (hyp_inv (Matrix.nonsing_inv_mul _ (Ne.isUnit hJ.2))) g hg).2, Units.ext e.symm⟩
  have hss : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := GlobalTheory.GaussMean.OneVec.sigma_sigma hcm
  have hJE : cT (σ : E →+* E) J = J := by ext i j; exact hJ.1 i j
  refine ⟨nn, ι, mm, fun w w' => sc (-(κ * (hf (w 0) (w' 0) - hf (w' 0) (w 0)))), fun p u a => ⟨_, _, hval p u a, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, cn, ci, cm, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    have z0 : (s : _ → _) ∘ (0 : Fin M → AF F ⊗[F] E) = 0 := funext fun _ => map_zero s
    simp [hz, hhf, hform, z0]
  · let G : Matrix (Fin (M + 2)) (Fin (M + 2)) (AF F ⊗[F] E) → ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) ×
        Matrix (Fin M) (Fin M) (AF F ⊗[F] E) × (AF F ⊗[F] E) × (AF F ⊗[F] E)ᵐᵒᵖ := fun g =>
      ((fun _ i => s (g 0 0) * g i.succ.succ 1, sc (g 0 1 * s (g 0 0) +
        κ * hf (fun i => s (g 0 0) * g i.succ.succ 1) (fun i => s (g 0 0) * g i.succ.succ 1))),
        Matrix.of fun i j => g i.succ.succ j.succ.succ, g 0 0, MulOpposite.op (s (g 1 1)))
    have e0 : ∀ i j, Continuous fun g : Matrix (Fin (M + 2)) (Fin (M + 2)) (AF F ⊗[F] E) => g i j :=
      fun i j => continuous_id.matrix_elem i j
    have e1 : Continuous fun (g : Matrix (Fin (M + 2)) (Fin (M + 2)) (AF F ⊗[F] E)) (i : Fin M) =>
        s (g 0 0) * g i.succ.succ 1 := continuous_pi fun i => (hsc.comp (e0 _ _)).mul (e0 _ _)
    have hG : Continuous G := ((continuous_pi fun _ => e1).prodMk (hscc.comp (((e0 _ _).mul (hsc.comp (e0 _ _))).add
      (continuous_const.mul (hfC.comp (e1.prodMk e1)))))).prodMk ((continuous_matrix fun i j => e0 _ _).prodMk
      ((e0 _ _).prodMk (MulOpposite.continuous_op.comp (hsc.comp (e0 _ _)))))
    have := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).1
    refine IsInducing.of_comp (I2.continuous_iff.2 ?_) (hG.comp I2.continuous) ?_
    · exact ((I2.continuous.comp (cn.comp continuous_fst)).matrix_mul
        (I2.continuous.comp (ci.comp continuous_snd.fst))).matrix_mul (I2.continuous.comp (cm.comp continuous_snd.snd))
    · have h3 := IsInducing.id (X := (Fin 1 → Fin M → AF F ⊗[F] E) × AF F) |>.prodMap
        (I1.prodMap (Units.isInducing_embedProduct (M := AF F ⊗[F] E)))
      refine (congrArg IsInducing (funext fun ⟨p, u, a⟩ => ?_)).mp h3
      have h1 : s a * s (a⁻¹ : (AF F ⊗[F] E)ˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      have h2 : (fun i => s a * (s (a⁻¹ : (AF F ⊗[F] E)ˣ) • p.1 0) i) = p.1 0 := by
        funext i; rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, h1, one_mul]
      show _ = G (nn p * ι u * mm a).1.val
      rw [hval]
      refine Prod.ext (Prod.ext (funext fun i => ?_) ?_) (Prod.ext rfl (Prod.ext rfl (congrArg MulOpposite.op (hs _).symm)))
      · rw [Subsingleton.elim i 0]; exact h2.symm
      · show p.2 = sc (z p * s _ * s a + κ * hf (fun i => s a * (s _ • p.1 0) i) (fun i => s a * (s _ • p.1 0) i))
        rw [h2, mul_assoc, mul_comm (s _) (s a), h1, mul_one, hz]
        simp only [neg_add_cancel_comm, sc2]
  · rintro ⟨p, u, a⟩ ⟨p', u', a'⟩ h
    have h1 := (hval p u a).symm.trans ((congrArg (fun g : HA (AF F) σ (hypJ J) => g.1.val) h).trans
      (hval p' u' a'))
    obtain ⟨e1, e2, -, -, -, -, -, e3, e4⟩ := blk_inj h1
    obtain rfl : a = a' := Units.ext e1
    have hu : IsUnit (s (a⁻¹ : (AF F ⊗[F] E)ˣ)) := (Units.isUnit _).map s
    have e5 : p.1 0 = p'.1 0 := hu.smul_left_cancel.1 e3
    have e6 := hu.mul_right_cancel e2
    simp only [hz, e5, add_right_inj] at e6
    have e7 : p.2 = p'.2 := by rw [← sc2 p.2, e6, sc2]
    exact Prod.ext (Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; exact e5) e7)
      (Prod.ext (Subtype.ext (Units.ext e4)) rfl)
  · have e : Set.range (fun y : ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) × HA (AF F) σ J × (AF F ⊗[F] E)ˣ =>
        nn y.1 * ι y.2.1 * mm y.2.2) = ⋂ i : Fin (M + 1), {h | h.1.val i.succ 0 = 0} := by
      ext h
      rw [Set.mem_iInter]
      refine ⟨?_, fun h0 => ?_⟩
      · rintro ⟨⟨p, u, a⟩, rfl⟩ i
        show (nn p * ι u * mm a).1.val i.succ 0 = 0
        rw [hval]
        exact Fin.cases rfl (fun _ => rfl) i
      · obtain ⟨p, u, a, e⟩ := dec h h0
        exact ⟨(p, u, a), e.symm⟩
    exact e ▸ isClosed_iInter fun i => isClosed_eq (I2.continuous.matrix_elem _ _) continuous_const
  · have c1 : Continuous fun p : (Fin 1 → Fin M → AF F ⊗[F] E) × (Fin 1 → Fin M → AF F ⊗[F] E) => p.1 0 :=
      (continuous_apply 0).comp continuous_fst
    have c2 : Continuous fun p : (Fin 1 → Fin M → AF F ⊗[F] E) × (Fin 1 → Fin M → AF F ⊗[F] E) => p.2 0 :=
      (continuous_apply 0).comp continuous_snd
    exact hscc.comp (continuous_const.mul ((hfC.comp (c1.prodMk c2)).sub (hfC.comp (c2.prodMk c1)))).neg
  · refine ext _ _ ?_
    show nM s _ 0 (z (0, 0)) = 1
    have z0 : (s : _ → _) ∘ (0 : Fin M → AF F ⊗[F] E) = 0 := funext fun _ => map_zero s
    simp [nM, hz, hhf, hform, z0, pm_one]
  · intro w t w' t'
    refine ext _ _ ((nM_mul _ _ _ _).trans (congrArg (nM s _ _) ?_))
    have := sc1 (-(κ * (hf (w 0) (w' 0) - hf (w' 0) (w 0)))) (by simp only [map_neg, map_mul, map_sub, hκs, hfc]; ring)
    simp only [hz, map_add, add_mul, Pi.add_apply, hhf, hform_add] at this ⊢
    linear_combination (hform s (JR (AF F) J) (w 0) (w' 0)) * hκ2 - this
  · intro w
    simp [hsc', hhf, hform]
  · intro u w t
    refine ext _ _ ((iM_nM u.2 _ _).trans (congrArg (fun y => nM s _ _ y * _) ?_))
    exact congrArg (fun y => -(κ * y) + _) (hform_U u.2 _).symm
  · intro a w t
    refine ext _ _ ((mM_nM hs a _ _).trans (congrArg (fun y => nM s _ _ y * _) ?_))
    have e : (s : _ → _) ∘ (s a • w 0) = (a : AF F ⊗[F] E) • (s ∘ w 0) := by funext i; simp [hs]
    simp only [hz, map_mul, norm_sigR _ hcm, Pi.smul_apply, hhf, hform_eq, e, Matrix.smul_vecMul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  · intro u a
    refine ext _ _ ?_
    show pm _ 0 0 (s _) 0 1 * pm 1 0 0 1 0 _ = pm 1 0 0 1 0 _ * pm _ 0 0 (s _) 0 1
    simp [pm_mul]
  · intro p u a
    funext k i
    rw [Subsingleton.elim k 0, act, hval]
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;> simp [pm, blk, eOne]
  · intro h a ha
    obtain ⟨p, u, a', e⟩ := dec h fun i => by rw [← act, ha]; simp [eOne]
    have : a' = a := Units.ext (by
      have h1 := act h 0
      rw [ha, e, hval] at h1
      simpa [eOne, pm, blk] using h1.symm)
    exact ⟨p, u, this ▸ e⟩
  · intro w t
    refine rat (nM (σ : E →+* E) J (w 0) (-(1 / 2 * hform (σ : E →+* E) J (w 0) (w 0)) + algebraMap F E t * δ)) _
      (nM_unit hss hJE ?_) ?_
    · simp only [map_add, map_neg, map_mul, hform_conj hss hJE, RingHom.coe_coe, AlgHom.commutes, hδ, map_div₀, map_one,
        map_ofNat]
      ring
    · show nM s _ _ (z _) = _
      rw [nM, nM, pm_map, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
      congr 1
      · simp only [hz, hhf, hform, map_add, map_neg, map_mul, map_sum, ratTup, hsi, JR, Matrix.map_apply, hκ, hdl]
        congr 2
        exact ((Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes t).symm
      · funext i
        simp [Matrix.vecMul, dotProduct, ratTup, hsi, JR]
  · rintro u ⟨g, hg, e⟩
    refine rat (pm 1 0 0 1 0 g.val) _ (iM_unit hg) ?_
    have e' : u.1.val = g.val.map (inclR (AF F)) := (congrArg Units.val e).symm
    show pm 1 0 0 1 0 u.1.val = _
    rw [pm_map, e', map_one, map_zero]
    congr 1 <;> exact funext fun _ => (map_zero _).symm
  · intro l a ha
    refine rat _ _ (mM_unit hss l) ?_
    have e : ((a⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (AF F) ((l⁻¹ : Eˣ) : E) :=
      Units.inv_eq_of_mul_eq_one_right (by rw [ha, ← map_mul, Units.mul_inv, map_one])
    show pm _ 0 0 (s _) 0 1 = _
    rw [pm_map, e, ha, hsi, map_zero, Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1 <;> exact funext fun _ => (map_zero _).symm

end PositivityTheory.ThKCT.Unf
end
end

