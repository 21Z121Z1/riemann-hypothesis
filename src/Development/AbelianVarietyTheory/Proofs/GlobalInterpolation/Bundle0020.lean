import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarSubgroupQuotientIntegralFormula
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal NNReal

namespace GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

theorem fibreIntegral_smul (c : ℝ≥0) (ν : Measure H) [ν.IsMulLeftInvariant]
    [(c • ν).IsMulLeftInvariant] (f : G → ℝ≥0∞) :
    fibreIntegral H (c • ν) f = fun q => (c : ℝ≥0∞) * fibreIntegral H ν f q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [fibreIntegral_mk, fibreIntegral_mk, lintegral_smul_measure]
  rfl

theorem quotientFormula_smul [MeasurableSpace (G ⧸ H)] (c : ℝ≥0) (dg : Measure G)
    (ν : Measure H) [ν.IsMulLeftInvariant] [(c • ν).IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) : QuotientFormula H (c • dg) (c • ν) μ := by
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  rw [fibreIntegral_smul]
  refine ⟨h1.const_mul _, ?_⟩
  rw [lintegral_const_mul _ h1, lintegral_smul_measure, h2]
  rfl

theorem eq_of_quotientFormula [MeasurableSpace (G ⧸ H)] {dg dg' : Measure G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) (h' : QuotientFormula H dg' ν μ) : dg = dg' := by
  ext s hs
  have hm : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (h _ hm).2, (h' _ hm).2]

end

theorem normaliseSubgroupClause : NormaliseSubgroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ dg _ μ hμ
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H :=
    inferInstanceAs (SecondCountableTopology (H : Set G))
  have key : ∀ (ν ν' : Measure H) [ν.IsHaarMeasure] [ν'.IsHaarMeasure],
      QuotientFormula H dg ν μ → QuotientFormula H dg ν' μ → ν' = ν := by
    intro ν ν' _ _ h h'
    obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν' = c • ν := ⟨_, Measure.isMulLeftInvariant_eq_smul ν' ν⟩
    subst hc
    have h1 := eq_of_quotientFormula H _ μ (quotientFormula_smul H c dg ν μ h) h'
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
    have hK0 : dg K ≠ 0 :=
      (Measure.measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'
    have hKt : dg K ≠ ∞ := K.isCompact.measure_lt_top.ne
    have h2 : (c : ℝ≥0∞) * dg K = 1 * dg K := by
      rw [one_mul]
      have := congrArg (fun m : Measure G => m K) h1
      simpa using this
    have h3 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hK0 hKt).mp h2
    have h4 : c = 1 := by exact_mod_cast h3
    rw [h4, one_smul]
  obtain ⟨dg₀, ⟨_, h₀⟩, -⟩ := GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH (Measure.haar : Measure H) μ hμ
  have hc : dg = Measure.haarScalarFactor dg dg₀ • dg₀ :=
    Measure.isMulLeftInvariant_eq_smul dg dg₀
  have hpos : Measure.haarScalarFactor dg dg₀ ≠ 0 :=
    (Measure.haarScalarFactor_pos_of_isHaarMeasure dg dg₀).ne'
  haveI hν : (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)).IsHaarMeasure :=
    Measure.IsHaarMeasure.nnreal_smul _ hpos
  have h₁ : QuotientFormula H dg
      (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)) μ := by
    have := quotientFormula_smul H (Measure.haarScalarFactor dg dg₀) dg₀ _ μ h₀
    rwa [← hc] at this
  refine ⟨_, ⟨hν, h₁⟩, ?_⟩
  rintro ν ⟨_, h⟩
  exact key _ _ h₁ h

end GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroWindow

theorem finsum_mem_le_of_subset {S T : Set ℂ} (hT : T.Finite) (h : S ⊆ T) (f : ℂ → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ∑ᶠ x ∈ S, f x ≤ ∑ᶠ x ∈ T, f x := by
  rw [finsum_mem_eq_finite_toFinset_sum f hT, finsum_mem_eq_finite_toFinset_sum f (hT.subset h)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hf i
  intro x hx
  simp only [Set.Finite.mem_toFinset] at hx ⊢
  exact h hx

theorem norm_sub_le {ρ : ℂ} {t : ℝ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (h2 : |ρ.im - t| ≤ 1) :
    ‖ρ - (2 + t * I)‖ ≤ 7 / 2 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have a : (ρ - (2 + t * I)).re = ρ.re - 2 := by simp
  have b : (ρ - (2 + t * I)).im = ρ.im - t := by simp
  rw [a, b]
  have : |ρ.re - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  linarith

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma norm_sub_two_add_le_of_mem_strip {ρ : ℂ} {t : ℝ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ht : |ρ.im - t| ≤ 1) : ‖ρ - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (ρ - (2 + (t : ℂ) * I)).re = ρ.re - 2 := by simp
  have him : (ρ - (2 + (t : ℂ) * I)).im = ρ.im - t := by simp
  rw [hre, him, abs_of_neg (by linarith)]
  linarith

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma finsum_mem_le_of_subset_of_nonneg {S D : Set ℂ} (f : ℂ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hD : D.Finite) (hSD : S ⊆ D) :
    ∑ᶠ x ∈ S, f x ≤ ∑ᶠ x ∈ D, f x := by
  rw [finsum_mem_eq_finite_toFinset_sum f (hD.subset hSD), finsum_mem_eq_finite_toFinset_sum f hD]
  exact Finset.sum_le_sum_of_subset_of_nonneg (by simpa using hSD) (fun x _ _ => hf x)

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in

theorem _root_.GlobalTheory.ZeroWindow.count_zeros_window : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0}.Finite ∧
    ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) ≤ C * Real.log (N * (|t| + 2)) := by
  obtain ⟨C1, hC1, hL⟩ := _root_.GlobalTheory.LWide.logDeriv_LFunction_strip
  obtain ⟨C2, hC2, hZ⟩ := _root_.GlobalTheory.ZetaWide.main
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, fun N _ χ hχ t => ?_⟩
  set s : ℂ := 2 + (t : ℂ) * I with hs
  have hsre : s.re = 2 := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  by_cases h1χ : χ = 1
  · have hN : N = 1 := by
      have h := hχ
      rw [DirichletCharacter.isPrimitive_def, h1χ, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN
    have hLz : LFunction χ = riemannZeta := LFunction_modOne_eq
    have hs1 : s ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hsre] at this
      norm_num at this
    obtain ⟨hfin, hsum, -⟩ := hZ s (by rw [hsre]; norm_num) (by rw [hsre]) hs1
      (riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; norm_num))
    rw [hsim] at hfin hsum
    have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0} ⊆
        {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0} := by
      rintro ρ ⟨h0, h1, h2, h3⟩
      refine ⟨norm_sub_two_add_le_of_mem_strip h0 h1 h2, ?_, by rwa [hLz] at h3⟩
      rintro rfl
      simp at h1
    refine ⟨hfin.subset hsub, ?_⟩
    calc ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ)
        ≤ ∑ᶠ ρ ∈ {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0},
          ((analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := by
          rw [hLz]
          exact finsum_mem_le_of_subset_of_nonneg _ (fun _ => Nat.cast_nonneg _) hfin
            (by rw [hLz] at hsub; exact hsub)
      _ ≤ C2 * Real.log (|t| + 2) := hsum
      _ ≤ max C1 C2 * Real.log (((1 : ℕ) : ℝ) * (|t| + 2)) := by
          rw [Nat.cast_one, one_mul]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.log_nonneg (by linarith))
  · have hLs : LFunction χ s ≠ 0 :=
      LFunction_ne_zero_of_one_le_re χ (Or.inl h1χ) (by rw [hsre]; norm_num)
    obtain ⟨hfin, hsum, -⟩ := hL N χ h1χ s (by rw [hsre]; norm_num) (by rw [hsre]) hLs
    rw [hsim] at hfin hsum
    have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0} ⊆
        {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ LFunction χ w = 0} := by
      rintro ρ ⟨h0, h1, h2, h3⟩
      exact ⟨norm_sub_two_add_le_of_mem_strip h0 h1 h2, h3⟩
    refine ⟨hfin.subset hsub, ?_⟩
    calc ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ)
        ≤ ∑ᶠ ρ ∈ {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ LFunction χ w = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) :=
          finsum_mem_le_of_subset_of_nonneg _ (fun _ => Nat.cast_nonneg _) hfin hsub
      _ ≤ C1 * Real.log (N * (|t| + 2)) := hsum
      _ ≤ max C1 C2 * Real.log (N * (|t| + 2)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.log_nonneg (by nlinarith))

end GlobalTheory.ZeroWindow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HaarDisintegrationAveragedFibreMeasures
section
open MeasureTheory Topology
open scoped Pointwise ENNReal NNReal

namespace GlobalTheory.QuadFibre

theorem exists_map_div_eq_smul {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsAddHaarMeasure] {a : K} (ha : a ≠ 0) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ Measure.map (fun t : K => t / a) ν = c • ν := by
  refine ⟨distribHaarChar K (Units.mk0 a ha), (distribHaarChar_pos).ne', ?_⟩
  ext S hS
  have hpre : (fun t : K => t / a) ⁻¹' S = (Units.mk0 a ha) • S := by
    ext t
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, Units.val_inv_eq_inv_val,
      Units.val_mk0, smul_eq_mul, div_eq_inv_mul]
  have hf : Measurable (fun t : K => t / a) := (continuous_id.div_const a).measurable
  rw [Measure.map_apply hf hS, hpre, ← distribHaarChar_mul ν,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

theorem avg_div_eq {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsAddHaarMeasure] {a : K} (ha : a ≠ 0)
    {U : Set K} (hU : MeasurableSet U) {g : K → ℝ≥0∞} (hg : Measurable g) :
    (ν {r | r / a ∈ U})⁻¹ * ∫⁻ t, g (t / a) ∂ν = (ν U)⁻¹ * ∫⁻ u, g u ∂ν := by
  obtain ⟨c, hc0, hc⟩ := exists_map_div_eq_smul ν ha
  have hf : Measurable (fun t : K => t / a) := (continuous_id.div_const a).measurable
  have hcU : ν {r | r / a ∈ U} = c * ν U := by
    have h : (Measure.map (fun t : K => t / a) ν) U = (c • ν) U := by rw [hc]
    rwa [Measure.map_apply hf hU, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hcI : ∫⁻ t, g (t / a) ∂ν = c * ∫⁻ u, g u ∂ν := by
    rw [← lintegral_map hg hf, hc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  have hc0' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  have hcc : (c : ℝ≥0∞)⁻¹ * c = 1 := ENNReal.inv_mul_cancel hc0' ENNReal.coe_ne_top
  rw [hcU, hcI, ENNReal.mul_inv (Or.inl hc0') (Or.inl ENNReal.coe_ne_top)]
  calc (c : ℝ≥0∞)⁻¹ * (ν U)⁻¹ * (c * ∫⁻ u, g u ∂ν)
      = (ν U)⁻¹ * (∫⁻ u, g u ∂ν) * ((c : ℝ≥0∞)⁻¹ * c) := by ring
    _ = (ν U)⁻¹ * ∫⁻ u, g u ∂ν := by rw [hcc, mul_one]

theorem disintegration (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K)
    (hq : Continuous q) (hq2 : ∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x)
    (U : Set K) (s : K → K) (hU : IsSqrtOn U s)
    (hμ : ∀ c : K, ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ)
    (h0 : μ {x | q x = 0} = 0) (φ : V → ENNReal) (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂μ = ∫⁻ t, ∫⁻ x, φ x ∂(fibOf μ ν q U s t) ∂ν := by
  obtain ⟨hUo, hUc, h1U, hmulU, hinvU, hnormU, hs, hsq⟩ := hU
  have hUm : MeasurableSet U := hUo.measurableSet
  have hνU0 : ν U ≠ 0 := hUo.measure_ne_zero ν ⟨1, h1U⟩
  have hνUt : ν U ≠ ∞ := hUc.measure_lt_top.ne
  have hqm : Measurable q := hq.measurable
  have hsm : Measurable s := hs.measurable
  have h0U : (0 : K) ∉ U := fun h => by simpa using hnormU 0 h
  have hdiv : Measurable (fun p : K × K => p.1 / p.2) := by
    simp_rw [div_eq_mul_inv]
    exact measurable_fst.mul measurable_snd.inv
  have hself : ∀ t : K, t ∈ t • U := fun t => by simpa using Set.smul_mem_smul_set (a := t) h1U

  have hstab : ∀ u ∈ U, u • U = U := by
    intro u hu
    have hu0 : u ≠ 0 := fun h => h0U (h ▸ hu)
    ext v
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hu0, smul_eq_mul]
    constructor
    · intro h
      have := hmulU _ hu _ h
      rwa [← mul_assoc, mul_inv_cancel₀ hu0, one_mul] at this
    · intro h
      exact hmulU _ (hinvU _ hu) _ h
  have hshift : ∀ t : K, ∀ t' ∈ t • U, t' • U = t • U := by
    intro t t' ht'
    obtain ⟨u, hu, rfl⟩ := ht'
    change (t • u) • U = t • U
    rw [smul_eq_mul, ← smul_smul, hstab u hu]
  have hmem : ∀ t : K, t ≠ 0 → ∀ y : K, y ∈ t • U ↔ t / y ∈ U := by
    intro t ht y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht, smul_eq_mul]
    constructor
    · intro h
      have := hinvU _ h
      rwa [mul_inv, inv_inv, ← div_eq_mul_inv] at this
    · intro h
      have := hinvU _ h
      rwa [inv_div, div_eq_inv_mul] at this
  have hpos : ∀ t : K, t ≠ 0 → ν (t • U) ≠ 0 := fun t ht =>
    (hUo.smul₀ ht).measure_ne_zero ν ⟨t, hself t⟩

  have hmeas : Measurable (fun t : K => ν (t • U)) := by
    refine measurable_of_continuousOn_compl_singleton 0 ?_
    intro t ht
    have ht0 : t ≠ 0 := ht
    refine ContinuousAt.continuousWithinAt ?_
    have hnb : t • U ∈ 𝓝 t := (hUo.smul₀ ht0).mem_nhds (hself t)
    have hev : (fun _ : K => ν (t • U)) =ᶠ[𝓝 t] fun t' => ν (t' • U) := by
      filter_upwards [hnb] with t' ht'
      rw [hshift t t' ht']
    exact continuousAt_const.congr hev

  have hGm : Measurable (fun p : K × V => (ν (p.1 • U))⁻¹ *
      {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) p) := by
    refine (hmeas.comp measurable_fst).inv.mul (Measurable.indicator ?_ ?_)
    · exact hφ.comp ((hsm.comp (hdiv.comp (measurable_fst.prodMk (hqm.comp measurable_snd)))).smul
        measurable_snd)
    · exact (hdiv.comp (measurable_fst.prodMk (hqm.comp measurable_snd))) hUm

  have hA : ∀ t : K, ∫⁻ x, φ x ∂(fibOf μ ν q U s t) = ∫⁻ x, (ν (t • U))⁻¹ *
      {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂μ := by
    intro t
    by_cases ht : t = 0
    · subst ht
      rw [fibOf_zero, lintegral_zero_measure]
      simp [h0U]
    · have hfm : Measurable (fun x : V => s (t / q x) • x) :=
        (hsm.comp (hdiv.comp (measurable_const.prodMk hqm))).smul measurable_id
      have hSm : MeasurableSet (q ⁻¹' (t • U)) := hqm (hUo.smul₀ ht).measurableSet
      rw [fibOf_ne μ ν q U s ht, lintegral_smul_measure, smul_eq_mul, lintegral_map hφ hfm,
        ← lintegral_indicator hSm, ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (hpos t ht))]
      refine lintegral_congr fun x => ?_
      by_cases h : t / q x ∈ U
      · rw [Set.indicator_of_mem (show x ∈ q ⁻¹' (t • U) from (hmem t ht (q x)).mpr h),
          Set.indicator_of_mem (show (t, x) ∈ {p : K × V | p.1 / q p.2 ∈ U} from h)]
      · rw [Set.indicator_of_notMem (show x ∉ q ⁻¹' (t • U) from fun h' => h ((hmem t ht (q x)).mp h')),
          Set.indicator_of_notMem (show (t, x) ∉ {p : K × V | p.1 / q p.2 ∈ U} from h)]

  have hC : ∀ x : V, q x ≠ 0 → ∫⁻ t, (ν (t • U))⁻¹ *
      {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂ν =
      (ν U)⁻¹ * ∫⁻ u, U.indicator (fun u => φ (s u • x)) u ∂ν := by
    intro x hx
    have hset : {r : K | r / q x ∈ U} = q x • U := by
      ext r
      rw [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem₀ hx, smul_eq_mul, div_eq_inv_mul]
    have hpt : ∀ t : K, (ν (t • U))⁻¹ *
        {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) =
        (ν {r : K | r / q x ∈ U})⁻¹ * U.indicator (fun u => φ (s u • x)) (t / q x) := by
      intro t
      by_cases h : t / q x ∈ U
      · have ht' : t ∈ q x • U := by
          rw [Set.mem_smul_set_iff_inv_smul_mem₀ hx, smul_eq_mul, ← div_eq_inv_mul]
          exact h
        rw [Set.indicator_of_mem (show (t, x) ∈ {p : K × V | p.1 / q p.2 ∈ U} from h),
          Set.indicator_of_mem h, hset, hshift (q x) t ht']
      · rw [Set.indicator_of_notMem (show (t, x) ∉ {p : K × V | p.1 / q p.2 ∈ U} from h),
          Set.indicator_of_notMem h, mul_zero, mul_zero]
    have hgm : Measurable (U.indicator (fun u => φ (s u • x))) :=
      (hφ.comp (hsm.smul measurable_const)).indicator hUm
    have hne : ν {r : K | r / q x ∈ U} ≠ 0 := by
      rw [hset]
      exact hpos _ hx
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hne)]
    exact avg_div_eq ν hx hUm hgm

  have hunit : ∀ u ∈ U, ∫⁻ x, φ (s u • x) ∂μ = ∫⁻ x, φ x ∂μ := by
    intro u hu
    have hn : ‖s u‖ = 1 := by
      have h := congrArg norm (hsq u hu)
      rw [norm_pow, hnormU u hu] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
    calc ∫⁻ x, φ (s u • x) ∂μ = ∫⁻ x, φ x ∂(Measure.map (fun x : V => s u • x) μ) :=
          (lintegral_map hφ (measurable_const_smul (s u))).symm
      _ = ∫⁻ x, φ x ∂μ := by rw [hμ _ hn]
  have hae : ∀ᵐ x ∂μ, q x ≠ 0 := by
    rw [ae_iff]
    simpa using h0
  have hM2 : Measurable (Function.uncurry fun (u : K) (x : V) => U.indicator (fun u => φ (s u • x)) u) := by
    have : (Function.uncurry fun (u : K) (x : V) => U.indicator (fun u => φ (s u • x)) u) =
        (Prod.fst ⁻¹' U).indicator (fun p : K × V => φ (s p.1 • p.2)) := by
      funext p
      by_cases h : p.1 ∈ U
      · rw [Function.uncurry_apply_pair, Set.indicator_of_mem h,
          Set.indicator_of_mem (show p ∈ Prod.fst ⁻¹' U from h)]
      · rw [Function.uncurry_apply_pair, Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show p ∉ Prod.fst ⁻¹' U from h)]
    rw [this]
    exact (hφ.comp ((hsm.comp measurable_fst).smul measurable_snd)).indicator (measurable_fst hUm)
  calc ∫⁻ x, φ x ∂μ = (ν U)⁻¹ * (ν U * ∫⁻ x, φ x ∂μ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hνU0 hνUt, one_mul]
    _ = (ν U)⁻¹ * ∫⁻ u, U.indicator (fun _ => ∫⁻ x, φ x ∂μ) u ∂ν := by
        rw [lintegral_indicator_const hUm, mul_comm (ν U)]
    _ = (ν U)⁻¹ * ∫⁻ u, ∫⁻ x, U.indicator (fun u => φ (s u • x)) u ∂μ ∂ν := by
        congr 1
        refine lintegral_congr fun u => ?_
        by_cases hu : u ∈ U
        · simp [hu, hunit u hu]
        · simp [hu]
    _ = (ν U)⁻¹ * ∫⁻ x, ∫⁻ u, U.indicator (fun u => φ (s u • x)) u ∂ν ∂μ := by
        rw [lintegral_lintegral_swap hM2.aemeasurable]
    _ = ∫⁻ x, (ν U)⁻¹ * ∫⁻ u, U.indicator (fun u => φ (s u • x)) u ∂ν ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hνU0)]
    _ = ∫⁻ x, ∫⁻ t, (ν (t • U))⁻¹ *
          {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂ν ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with x hx
        exact (hC x hx).symm
    _ = ∫⁻ t, ∫⁻ x, (ν (t • U))⁻¹ *
          {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂μ ∂ν :=
        (lintegral_lintegral_swap hGm.aemeasurable).symm
    _ = ∫⁻ t, ∫⁻ x, φ x ∂(fibOf μ ν q U s t) ∂ν := lintegral_congr fun t => (hA t).symm

end GlobalTheory.QuadFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPointStatement
section
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFibreFamily_eq_at_continuity_point : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℝ) (O U U' : Set V) (B B' : Set ℝ) (fib fib' : ℝ → Measure V) (β : ℝ), Measurable f → IsOpen O → O ⊆ U → O ⊆ U' → f ⁻¹' {β} ⊆ O → IsOpen B → IsOpen B' → β ∈ B → β ∈ B' → IsFibreFamily μ f id U (volume : Measure ℝ) B fib → IsFibreFamily μ f id U' (volume : Measure ℝ) B' fib' → fib β = fib' β := by
  first | exact @GlobalTheory.IsFibreFamily_eq_at | exact GlobalTheory.IsFibreFamily_eq_at | (intros; apply GlobalTheory.IsFibreFamily_eq_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyUnivOfNullConeStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFibreFamily_univ_of_null_cone' : ∀ (K V : Type) [NormedField K] [IsUltrametricDist K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) (q : V → K), Continuous q → μ {x | q x = 0} = 0 → ∀ (U : Set V) (B : Set K) (fib : K → Measure V), {x | q x ≠ 0} ⊆ U → {t | t ≠ 0} ⊆ B → IsFibreFamily μ q id U ν B fib → IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib := by
  first | exact @GlobalTheory.isFibreFamily_univ_of_null_cone | exact GlobalTheory.isFibreFamily_univ_of_null_cone | (intros; apply GlobalTheory.isFibreFamily_univ_of_null_cone <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInertStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_adicCompletion_tensor_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime → IsField (v.adicCompletion F ⊗[F] E) := by
  first | exact @GlobalTheory.InertField.isField_of_inert | exact GlobalTheory.InertField.isField_of_inert | (intros; apply GlobalTheory.InertField.isField_of_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsPadicIntMatrixChange
section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.MomN

def zcHom (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zc_eq_zcHom {q : ℕ} [Fact q.Prime] (x : ℤ_[q]) : zc x = zcHom q x := rfl

theorem zc_continuous' {q : ℕ} [Fact q.Prime] : Continuous (zc : ℤ_[q] → ℂ_[q]) :=
  (continuous_algebraMap ℚ_[q] ℂ_[q]).comp continuous_subtype_val

def linZ {q : ℕ} [Fact q.Prime] {κ κ' : Type} [Fintype κ] (a : κ' → κ → ℤ_[q]) :
    C(κ → ℤ_[q], κ' → ℤ_[q]) :=
  ⟨fun x i => ∑ j, a i j * x j, by fun_prop⟩

def pullCLM {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) : C(Y, ℂ_[q]) →L[ℂ_[q]] C(X, ℂ_[q]) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.comp A
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } 1 (fun f => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
        exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => f.norm_coe_le_norm (A x))

theorem pullCLM_norm_le {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) : ‖(pullCLM (q := q) A)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem pullCLM_apply {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) (f : C(Y, ℂ_[q])) : pullCLM A f = f.comp A := rfl

def monoC {q : ℕ} [Fact q.Prime] {κ : Type} {k : ℕ} (σ : Fin k → κ) : C(κ → ℤ_[q], ℂ_[q]) :=
  ⟨fun x => ∏ l, zc (x (σ l)), by
    refine continuous_finset_prod _ fun l _ => zc_continuous'.comp (continuous_apply (σ l))⟩

theorem momInt_push (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (v : κ → V) (w : κ' → V) (c : κ' → κ → ℂ) (a : κ' → κ → ℤ_[q])
    (G : V → ℂ) (hc : ∀ i j, ι (c i j) = zc (a i j)) (hw : ∀ i, w i = ∑ j, c i j • v j) (h : MomInt ι v G) :
    MomInt ι w G := by
  classical
  obtain ⟨μ, hμ, hm⟩ := h
  refine ⟨μ.comp (pullCLM (linZ a)), ?_, ?_⟩
  · calc ‖μ.comp (pullCLM (linZ a))‖ ≤ ‖μ‖ * ‖pullCLM (q := q) (linZ a)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hμ (pullCLM_norm_le _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro k j f hf
    have hfe : pullCLM (linZ a) f = ∑ σ : Fin k → κ, (∏ l, zc (a (j l) (σ l))) • monoC σ := by
      ext x
      rw [pullCLM_apply, ContinuousMap.comp_apply, hf]
      simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        monoC, ContinuousMap.coe_mk, linZ]
      simp only [zc_eq_zcHom, map_sum, map_mul]
      rw [Finset.prod_univ_sum]
      simp [Fintype.piFinset_univ, Finset.prod_mul_distrib]
    have hd : iteratedFDeriv ℂ k G 0 (fun l => w (j l)) =
        ∑ σ : Fin k → κ, (∏ l, c (j l) (σ l)) • iteratedFDeriv ℂ k G 0 (fun l => v (σ l)) := by
      simp only [hw]
      rw [ContinuousMultilinearMap.map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      exact ContinuousMultilinearMap.map_smul_univ _ _ _
    rw [ContinuousLinearMap.comp_apply, hfe, hd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_eq_mul, map_mul, map_prod, map_smul, smul_eq_mul, ← hm k σ (monoC σ) (fun _ => rfl)]
    simp only [hc]

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivDirichletLFunctionLocalZeroSumStatement
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDeriv_dirichletLFunction_local_zero_sum : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}.Finite ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|t| + 2)) := by
  first | exact @GlobalTheory.LLocal.logDeriv_LFunction_local | exact GlobalTheory.LLocal.logDeriv_LFunction_local | (intros; apply GlobalTheory.LLocal.logDeriv_LFunction_local <;> assumption)
end

