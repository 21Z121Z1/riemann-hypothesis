import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityUnfoldSubgroup
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GenUnfold

theorem covol_eq_of_strict {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) (hμ : ∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) {F : Set G}
    (hF : MeasurableSet F) (h : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) :
    covol (Γ : Set G) μ Set.univ = μ F := by
  classical
  have hmeas : ∀ a : G, Measurable (fun y : G => a * y) := fun a => measurable_const_mul a
  unfold covol
  apply le_antisymm
  · refine iInf_le_of_le F (iInf_le_of_le hF (iInf_le_of_le ?_ le_rfl))
    intro x _
    obtain ⟨γ, hγ, -⟩ := h x
    exact ⟨γ, γ.2, hγ⟩
  · refine le_iInf fun D => le_iInf fun hD => le_iInf fun hcov => ?_

    have hsub : F ⊆ ⋃ γ : Γ, F ∩ (fun y => (γ : G) * y) ⁻¹' D := by
      intro x hx
      obtain ⟨γ, hγ, hxD⟩ := hcov x trivial
      exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, hx, hxD⟩

    have hpiece : ∀ γ : Γ, μ (F ∩ (fun y => (γ : G) * y) ⁻¹' D) =
        μ ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := by
      intro γ
      have hS : MeasurableSet ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := (hmeas _ hF).inter hD
      have e : (μ.map (fun y => (γ : G) * y)) ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) =
          μ ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := by rw [hμ γ γ.2]
      rw [Measure.map_apply (hmeas _) hS] at e
      rw [← e]
      congr 1
      ext y
      simp [inv_mul_cancel_left]

    have hdisj : Pairwise (Function.onFun Disjoint
        fun γ : Γ => (fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := by
      intro γ₁ γ₂ hne
      refine Set.disjoint_left.2 fun y hy₁ hy₂ => hne ?_
      obtain ⟨δ, -, huniq⟩ := h y
      have e₁ := huniq γ₁⁻¹ (by simpa using hy₁.1)
      have e₂ := huniq γ₂⁻¹ (by simpa using hy₂.1)
      exact inv_injective (e₁.trans e₂.symm)
    calc μ F ≤ μ (⋃ γ : Γ, F ∩ (fun y => (γ : G) * y) ⁻¹' D) := measure_mono hsub
      _ ≤ ∑' γ : Γ, μ (F ∩ (fun y => (γ : G) * y) ⁻¹' D) := measure_iUnion_le _
      _ = ∑' γ : Γ, μ ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := tsum_congr hpiece
      _ = μ (⋃ γ : Γ, (fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) :=
          (measure_iUnion hdisj fun γ => (hmeas _ hF).inter hD).symm
      _ ≤ μ D := measure_mono (Set.iUnion_subset fun _ => Set.inter_subset_right)

theorem isInvInvariant {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hUo : IsOpen (interior K) := isOpen_interior
  have hUpos : μ (interior K) ≠ 0 :=
    (hUo.measure_pos μ ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have hUfin : μ (interior K) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono interior_subset) hK.measure_lt_top).ne
  have hc := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  set c := Measure.haarScalarFactor μ.inv μ
  have key : ∀ s : Set G, MeasurableSet s → μ (Inv.inv ⁻¹' s) = (c : ENNReal) * μ s := by
    intro s hs
    have e : μ.inv s = (c • μ) s := by rw [← hc]
    rw [Measure.inv_def, Measure.map_apply measurable_inv hs, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul] at e
    exact e
  have h1 := key (interior K) hUo.measurableSet
  have h2 := key (Inv.inv ⁻¹' interior K) (hUo.measurableSet.preimage measurable_inv)
  have hUU : (Inv.inv ⁻¹' (Inv.inv ⁻¹' interior K) : Set G) = interior K := by
    ext x
    simp
  rw [hUU, h1, ← mul_assoc] at h2
  have hcc : (c : ENNReal) * c = 1 :=
    (ENNReal.mul_left_inj hUpos hUfin).1 (h2.symm.trans (one_mul _).symm)
  have hc1 : c = 1 := by
    have hnn : c * c = 1 := by exact_mod_cast hcc
    have hr : (c : ℝ) * c = 1 := by exact_mod_cast hnn
    have h0 : (0 : ℝ) ≤ c := c.2
    exact NNReal.eq (by push_cast; nlinarith)
  constructor
  rw [hc, hc1, one_smul]

private lemma exists_nhds_one_inter_discrete_subgroup_eq_one {H : Type} [Group H] [TopologicalSpace H] (Γ : Subgroup H)
    [DiscreteTopology Γ] : ∃ V ∈ nhds (1 : H), ∀ γ ∈ Γ, γ ∈ V → γ = 1 := by

  have ho : IsOpen ({1} : Set Γ) := isOpen_discrete _
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.1 ho
  have h1 : (1 : Γ) ∈ (Subtype.val ⁻¹' t : Set Γ) := by
    rw [hpre]
    exact Set.mem_singleton _
  refine ⟨t, ht.mem_nhds h1, fun γ hγ hγt => ?_⟩
  have h2 : (⟨γ, hγ⟩ : Γ) ∈ (Subtype.val ⁻¹' t : Set Γ) := hγt
  rw [hpre] at h2
  have h3 : (⟨γ, hγ⟩ : Γ) = 1 := h2
  simpa using congrArg Subtype.val h3

theorem exists_nhds_map {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsEmbedding j) (Γ : Subgroup H) [DiscreteTopology Γ] :
    ∃ U ∈ nhds (1 : G), ∀ γ ∈ Γ.map j, γ ∈ U → γ = 1 := by
  obtain ⟨V, hV, hVΓ⟩ := exists_nhds_one_inter_discrete_subgroup_eq_one Γ
  rw [hj.isInducing.nhds_eq_comap (1 : H), map_one] at hV
  obtain ⟨U, hU, hUV⟩ := Filter.mem_comap.1 hV
  refine ⟨U, hU, fun γ hγ hγU => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hγ
  rw [hVΓ x hx (hUV hγU), map_one]

theorem covol_withDensity_eq : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (Γ : Subgroup H) [DiscreteTopology Γ] (Φ b : G → ENNReal), Measurable Φ → Measurable b → (∀ h g, Φ (j h * g) = Φ g) → (∀ g, ∫⁻ h, b (j h * g) ∂ν = 1) → covol ((Γ.map j : Subgroup G) : Set G) (μ.withDensity Φ) Set.univ = covol (Γ : Set H) ν Set.univ * ∫⁻ g, Φ g * b g ∂μ := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ j hj Γ _ Φ b hΦ hb hΦinv hb1
  classical
  have hjc : Continuous j := hj.continuous
  have : ν.IsInvInvariant := isInvInvariant ν

  obtain ⟨hcnt, F, hFm, hF⟩ := GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete G
    (Γ.map j) (exists_nhds_map j hj.toIsEmbedding Γ)
  have := hcnt
  have hcntH : Countable Γ :=
    Function.Injective.countable
      (f := fun γ : Γ => (⟨j γ, Subgroup.mem_map_of_mem j γ.2⟩ : Γ.map j))
      (fun a b hab => Subtype.ext (hj.injective (congrArg Subtype.val hab)))

  have hL : covol ((Γ.map j : Subgroup G) : Set G) (μ.withDensity Φ) Set.univ =
      ∫⁻ g in F, Φ g ∂μ := by
    rw [covol_eq_of_strict (Γ.map j) (μ.withDensity Φ) ?_ hFm hF, withDensity_apply _ hFm]
    intro γ hγ
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hγ
    ext s hs
    rw [Measure.map_apply (measurable_const_mul _) hs,
      withDensity_apply _ (measurable_const_mul _ hs), withDensity_apply _ hs,
      ← lintegral_indicator (measurable_const_mul _ hs), ← lintegral_indicator hs,
      ← lintegral_mul_left_eq_self (s.indicator Φ) (j x)]
    refine lintegral_congr fun y => ?_
    simp only [Set.indicator_apply, Set.mem_preimage, hΦinv]

  have hfib : ∀ g : G, ν {x : H | (j x)⁻¹ * g ∈ F} = covol (Γ : Set H) ν Set.univ := by
    intro g
    have hT : MeasurableSet {x : H | j x * g ∈ F} :=
      hFm.preimage (hjc.mul continuous_const).measurable
    have e₁ : {x : H | (j x)⁻¹ * g ∈ F} = Inv.inv ⁻¹' {x : H | j x * g ∈ F} := by
      ext x
      simp [map_inv]
    rw [e₁, Measure.measure_preimage_inv,
      covol_eq_of_strict Γ ν (fun γ _ => map_mul_left_eq_self ν γ) hT]
    intro x
    obtain ⟨δ, hδ, huniq⟩ := hF (j x * g)
    obtain ⟨γ, hγ, hδe⟩ := Subgroup.mem_map.1 δ.2
    refine ⟨⟨γ, hγ⟩, ?_, ?_⟩
    · show j (γ * x) * g ∈ F
      rw [map_mul, mul_assoc, hδe]
      exact hδ
    · rintro ⟨γ', hγ'⟩ h'
      have h'' : ((⟨j γ', Subgroup.mem_map_of_mem j hγ'⟩ : Γ.map j) : G) * (j x * g) ∈ F := by
        have h3 : j (γ' * x) * g ∈ F := h'
        simpa [map_mul, mul_assoc] using h3
      have e₂ := huniq _ h''
      apply Subtype.ext
      apply hj.injective
      show j γ' = j γ
      rw [hδe]
      exact congrArg Subtype.val e₂
  have hm₁ : Measurable (fun p : G × H => j p.2 * p.1) :=
    ((hjc.comp continuous_snd).mul continuous_fst).measurable
  have hm₂ : Measurable (fun p : H × G => (j p.1)⁻¹ * p.2) :=
    ((hjc.comp continuous_fst).inv.mul continuous_snd).measurable
  have hm₃ : ∀ g : G, Measurable (fun x : H => (j x)⁻¹ * g) :=
    fun g => (hjc.inv.mul continuous_const).measurable
  have hbm : ∀ g : G, Measurable (fun x : H => b (j x * g)) :=
    fun g => hb.comp (hjc.mul continuous_const).measurable
  have hI : Measurable (F.indicator (1 : G → ENNReal)) := measurable_one.indicator hFm
  rw [hL]
  calc ∫⁻ g in F, Φ g ∂μ
      = ∫⁻ g, F.indicator 1 g * Φ g * ∫⁻ x, b (j x * g) ∂ν ∂μ := by
        rw [← lintegral_indicator hFm]
        refine lintegral_congr fun g => ?_
        rw [hb1 g, mul_one]
        by_cases hg : g ∈ F <;> simp [hg]
    _ = ∫⁻ g, ∫⁻ x, F.indicator 1 g * Φ g * b (j x * g) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul _ (hbm g)]
    _ = ∫⁻ x, ∫⁻ g, F.indicator 1 g * Φ g * b (j x * g) ∂μ ∂ν := by
        apply lintegral_lintegral_swap
        exact (((hI.comp measurable_fst).mul (hΦ.comp measurable_fst)).mul
          (hb.comp hm₁)).aemeasurable
    _ = ∫⁻ x, ∫⁻ g, F.indicator 1 ((j x)⁻¹ * g) * Φ g * b g ∂μ ∂ν := by
        refine lintegral_congr fun x => ?_
        have e := lintegral_mul_left_eq_self (μ := μ)
          (fun g => F.indicator 1 ((j x)⁻¹ * g) * Φ g * b g) (j x)
        simpa only [inv_mul_cancel_left, hΦinv] using e
    _ = ∫⁻ g, ∫⁻ x, F.indicator 1 ((j x)⁻¹ * g) * Φ g * b g ∂ν ∂μ := by
        apply lintegral_lintegral_swap
        exact (((hI.comp hm₂).mul (hΦ.comp measurable_snd)).mul
          (hb.comp measurable_snd)).aemeasurable
    _ = ∫⁻ g, ν {x : H | (j x)⁻¹ * g ∈ F} * (Φ g * b g) ∂μ := by
        refine lintegral_congr fun g => ?_
        have hmg : MeasurableSet {x : H | (j x)⁻¹ * g ∈ F} := hFm.preimage (hm₃ g)
        simp_rw [mul_assoc]
        rw [lintegral_mul_const (f := fun x => F.indicator 1 ((j x)⁻¹ * g)) _ (hI.comp (hm₃ g)),
          ← lintegral_indicator_one hmg]
        rfl
    _ = ∫⁻ g, covol (Γ : Set H) ν Set.univ * (Φ g * b g) ∂μ := by
        simp_rw [hfib]
    _ = covol (Γ : Set H) ν Set.univ * ∫⁻ g, Φ g * b g ∂μ :=
        lintegral_const_mul _ (hΦ.mul hb)

end GlobalTheory.GenUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntries
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellLieAlg

theorem mem_lieE_iff {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (P : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ))
    (hP : ∀ X, X ∈ lieOf S ↔ X ∈ P) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    x ∈ lieE S ↔ unrealify x ∈ P := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨X, hX, rfl⟩ := hy
      have e : unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
        ext i j; rfl
      show unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) ∈ P
      rw [e]; exact (hP X).1 hX
    | zero =>
      have e : unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.zero_mem
    | add x y _ _ hx hy =>
      have e : unrealify (x + y) = unrealify x + unrealify y := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.add_mem hx hy
    | smul c x _ hx =>
      have e : unrealify (c • x) = c • unrealify x := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.smul_mem c hx
  · intro hx
    refine Submodule.subset_span ⟨unrealify x, (hP _).2 hx, ?_⟩
    ext ⟨i, j, b⟩
    cases b <;> rfl

open scoped Matrix.Norms.Operator in
theorem mem_lieOf_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) (X : Matrix (Fin N) (Fin N) ℂ) :
    X ∈ lieOf (UH H) ↔ Xᴴ * H + H * X = 0 := by
  constructor
  · intro h
    have hc : (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * H * NormedSpace.exp (t • X)) = fun _ => H := by
      funext t
      have h1 : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := h t
      rw [← Matrix.exp_conjTranspose, Complex.coe_smul, Matrix.conjTranspose_smul, star_trivial] at h1
      exact h1
    have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * H * NormedSpace.exp (t • X)) _ 0 :=
      ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ 0).mul_const H).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
    rw [hc] at hd
    have := hd.unique (hasDerivAt_const _ _)
    simpa using this
  · intro hX t
    set Y : Matrix (Fin N) (Fin N) ℂ := (t : ℂ) • X with hYdef
    have hY : Yᴴ * H + H * Y = 0 := by
      rw [hYdef, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, ← smul_add, hX, smul_zero]
    have hinv : H⁻¹ = H := Matrix.inv_eq_right_inv hH
    have hu : IsUnit H := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse hH)
    have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
      have e : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
      calc Yᴴ = Yᴴ * (H * H) := by rw [hH, Matrix.mul_one]
        _ = (Yᴴ * H) * H := by rw [Matrix.mul_assoc]
        _ = _ := by rw [e, hinv, Matrix.mul_neg]
    have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
      rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hu, hinv]
    have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
        NormedSpace.exp_zero]
    show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
    rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH,
      Matrix.mul_one, Matrix.mul_assoc, hc, Matrix.mul_one]

open scoped Matrix.Norms.Operator in
theorem exp_mul_eq_iff {N : ℕ} (X E : Matrix (Fin N) (Fin N) ℂ) :
    (∀ t : ℝ, NormedSpace.exp (t • X) * E = E) ↔ X * E = 0 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * E)
      (NormedSpace.exp (t • X) * X * E) t := fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).mul_const E
  constructor
  · intro h
    have h0 := hd 0
    rw [show (fun t : ℝ => NormedSpace.exp (t • X) * E) = fun _ => E from funext h] at h0
    simpa using h0.unique (hasDerivAt_const _ _)
  · intro h t
    have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => by rw [(hd t).deriv, Matrix.mul_assoc, h, Matrix.mul_zero]) t 0
    simpa using this

theorem mul_single_eq_iff {N : ℕ} (g h : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    g * Matrix.single j j (1 : ℂ) = h * Matrix.single j j (1 : ℂ) ↔ g *ᵥ bvec j = h *ᵥ bvec j := by
  simp only [bvec, Matrix.mulVec_single_one]
  constructor
  · intro e
    funext i
    simpa using congrFun (congrFun e i) j
  · intro e
    ext i l
    by_cases hl : l = j
    · subst hl
      simpa using congrFun e i
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, Matrix.mul_single_apply_of_ne _ _ _ _ _ hl]

theorem exp_fix_iff {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j = bvec j) ↔ ∀ i, X i j = 0 := by
  have h1 := exp_mul_eq_iff X (Matrix.single j j (1 : ℂ))
  have h2 := mul_single_eq_iff X 0 j
  rw [Matrix.zero_mul] at h2
  rw [h2] at h1
  have h3 : X *ᵥ bvec j = (0 : Matrix (Fin N) (Fin N) ℂ) *ᵥ bvec j ↔ ∀ i, X i j = 0 := by
    simp [bvec, funext_iff]
  rw [← h3, ← h1]
  refine forall_congr' fun t => ?_
  have h4 := mul_single_eq_iff (NormedSpace.exp (t • X)) 1 j
  rw [Matrix.one_mul, Matrix.one_mulVec] at h4
  rw [h4, Complex.coe_smul]

theorem rows_zero {k r : ℕ} {X : Mat k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0)
    (hc : ∀ j : Fin (2 * r + k + 1), ¬ (r ≤ j.val ∧ j.val ≤ r + k) → ∀ i, X i j = 0)
    (i : Fin (2 * r + k + 1)) (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) (j : Fin (2 * r + k + 1)) : X i j = 0 := by
  have hil := i.isLt
  let i' : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hv : i'.val = 2 * r + k - i.val := rfl
  have h := congrFun (congrFun hX i') j
  have h1 : (Xᴴ * Hpk k r) i' j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.conjTranspose_apply, hc i' (by omega) l, star_zero, zero_mul]
  have h2 : (Hpk k r * X) i' j = X i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · have : Hpk k r i' i = 1 := by
        unfold Hpk
        split_ifs with a b c d <;> first | rfl | (exfalso; omega)
      rw [this, one_mul]
    · intro l _ hl
      have hl' : l.val ≠ i.val := fun e => hl (Fin.ext e)
      have : Hpk k r i' l = 0 := by
        unfold Hpk
        split_ifs with a b c d <;> first | rfl | (exfalso; omega)
      rw [this, zero_mul]
    · simp
  rw [Matrix.add_apply, h1, h2, zero_add] at h
  exact h

theorem mem_lieOf_UWb (k r : ℕ) (X : Mat k r) :
    X ∈ lieOf (Formalism.FourierDecayAlt.B2.UWb k r) ↔ (Xᴴ * Hpk k r + Hpk k r * X = 0 ∧ ∀ i j : Fin (2 * r + k + 1),
      ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → X i j = 0) := by
  have hH := (hpkFacts k r).2.1
  constructor
  · intro h
    have hX := (mem_lieOf_UH _ hH X).1 fun t => (h t).1
    have hc : ∀ j : Fin (2 * r + k + 1), ¬ (r ≤ j.val ∧ j.val ≤ r + k) → ∀ i, X i j = 0 := by
      intro j hj
      have hjl := j.isLt
      by_cases hr : j.val < r
      · exact (exp_fix_iff X j).1 fun t => ((h t).2 ⟨j.val, hr⟩).1
      · have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
          apply Fin.ext; simp only [esI]; omega
        rw [← e]
        exact (exp_fix_iff X _).1 fun t => ((h t).2 _).2
    refine ⟨hX, fun i j hij => ?_⟩
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · exact hc j (fun hj => hij ⟨hi, hj⟩) i
    · exact rows_zero hX hc i hi j
  · rintro ⟨hX, h0⟩ t
    refine ⟨(mem_lieOf_UH _ hH X).2 hX t, fun a => ⟨?_, ?_⟩⟩
    · refine (exp_fix_iff X _).2 (fun i => h0 i _ fun h => ?_) t
      have := h.2.1; have := a.isLt
      simp only [eI] at *; omega
    · refine (exp_fix_iff X _).2 (fun i => h0 i _ fun h => ?_) t
      have := h.2.2; have := a.isLt
      simp only [esI] at *; omega

def skewSub {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : Submodule ℝ (Matrix (Fin N) (Fin N) ℂ) where
  carrier := {X | Xᴴ * H + H * X = 0}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    have ha' : aᴴ * H + H * a = 0 := ha
    have hb' : bᴴ * H + H * b = 0 := hb
    show (a + b)ᴴ * H + H * (a + b) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, ha', hb', add_zero]
  smul_mem' c a ha := by
    have ha' : aᴴ * H + H * a = 0 := ha
    show (c • a)ᴴ * H + H * (c • a) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ha', smul_zero]

def midSub (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | ∀ i j : Fin (2 * r + k + 1),
      ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → X i j = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' {a b} ha hb := fun i j h => by rw [Matrix.add_apply, ha i j h, hb i j h, add_zero]
  smul_mem' c a ha := fun i j h => by rw [Matrix.smul_apply, ha i j h, smul_zero]

theorem lie_entries : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (GG k r) ↔ (unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → unrealify x i j = 0)) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) → NormedSpace.exp (unrealify x) ∈ Formalism.FourierDecayAlt.B2.UWb k r) := by
  intro k r x
  have h2 := mem_lieE_iff (S := Formalism.FourierDecayAlt.B2.UWb k r) (skewSub (Hpk k r) ⊓ midSub k r) (mem_lieOf_UWb k r) x
  refine ⟨mem_lieE_iff (skewSub (Hpk k r)) (mem_lieOf_UH _ (hpkFacts k r).2.1) x, h2, fun hx => ?_⟩
  have h := (mem_lieOf_UWb k r _).2 (h2.1 hx) 1
  simpa using h

end GlobalTheory.CellLieAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantMomentBoundBothSides
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.MomBoth

def swapW {k r : ℕ} (W : LocW k r) : LocW k r where
  Wp := W.Wq
  Wq := W.Wp
  π := W.π'
  π' := W.π
  z := W.z'
  z' := W.z
  μG := W.μG
  μW := W.μW'
  μW' := W.μW
  μN := W.μN
  νS := W.νS'
  νS' := W.νS

def swapS {k r : ℕ} {W : LocW k r} (A : LocS W) : LocS (swapW W) where
  H := A.H
  σ := A.σ
  B := A.B'
  B' := A.B
  v0 := A.v0
  cN := A.cN
  deg := A.deg

theorem goodW_swap {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (h : GoodW D τ w w' θ W) : GoodW D τ w' w θ (swapW W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h2, h1, h4, h3, h6, h5, h7, h10, h11, h8, h9, h12, h14, h13⟩

theorem goodS_swap {D : D7} {W : LocW D.R.k D.R.rS} {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (h : GoodS D lam A) : GoodS D lam (swapS A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h4, h3, h5, h6, h7, h8, h10, h9, h11⟩

theorem hypTT_swap {D : D7} {w w' : D.what₂.Word} (h : HypTT D w w') : HypTT D w' w := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h2, h1, h4, h3, h5.symm⟩

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)

theorem momBd_one (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 CMo : ℝ) (hm : 4 ≤ D.R.m)
    (hM : MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo) (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0)
    (τ : D.what₂.Tau) (w w' : D.what₂.Word) (hT : HypTT D w w') (θ : ℝ) (hθ : normWin D large₂ C1 θ)
    (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (hl : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3) (S : LocS W) (hS : GoodS D lam' S) :
    MomBd W.z W.νS S.Φ (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) := by
  intro a
  have hr : 1 ≤ D.R.rS := by unfold Ranks.rS; omega
  have hr3 : (1 : ℝ) ≤ (D.R.rS : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hr)
  have hb := one_le_b large₂.sc
  have h := hM hZ τ w w' hT θ hθ W hW lam' hl S hS a (24 * D.R.rS ^ 3 + 1) (by push_cast; linarith)
  refine h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hb ?_
  have h1 : CMo ≤ max CMo 0 := le_max_left _ _
  have h2 : (0 : ℝ) ≤ (D.R.m : ℝ) * ((24 * D.R.rS ^ 3 + 1 : ℕ) : ℝ) := by positivity
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  rw [Nat.cast_mul 2, Nat.cast_ofNat]
  nlinarith

theorem momBd_both : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 CMo : ℝ), 4 ≤ D.R.m →
    MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S →
      MomBd W.z W.νS S.Φ (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) ∧
      MomBd W.z' W.νS' S.Φ' (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) := by
  intro D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm hM hZ τ w w' hT θ hθ W hW lam' hl S hS
  exact ⟨momBd_one D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm hM hZ τ w w' hT θ hθ W hW lam' hl S hS,
    momBd_one D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm hM hZ τ w' w (hypTT_swap hT) θ hθ (swapW W)
      (goodW_swap hW) lam' hl (swapS S) (goodS_swap hS)⟩

end GlobalTheory.Amp.MomBoth
end
end

