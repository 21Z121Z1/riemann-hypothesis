import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import GroundTheory.AutomorphicForms.AnisotropicUnitaryCompact
import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeRhamFiniteAndFiltrationBounded
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0486
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0154
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalDecompositionOfCompact
section
noncomputable section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspGL

theorem cuspDiscreteDecompositionGL_of_compact
    (hc : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f →
      IsCompactOperator (repOp (Rcusp μ) μ f)) :
    GlobalTheory.Published.CuspDiscreteDecompositionGL := by
  intro E _ _ _ a μ _ _
  have : BorelSpace (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.borelSpace_GA E a
  have : LocallyCompactSpace (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E a
  have : T2Space (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E a
  have : CompleteSpace (L2cusp μ) := GlobalTheory.CuspRep.CuspidalL2GL.completeSpace_L2cusp μ
  have hU := GlobalTheory.CuspRep.CuspidalL2GL.isUnitaryRep_Rcusp μ
  refine GlobalTheory.CuspSpectrum.isDiscreteSum_of_repOp hU μ fun v hv => ?_
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have cc : Continuous fun g => inner ℂ v ((Rcusp μ g) v) := continuous_const.inner (hU.continuous_apply v)
  have h1pos : 0 < (inner ℂ v ((Rcusp μ 1) v)).re := by
    rw [map_one, ContinuousLinearMap.one_apply]
    have h3 : RCLike.re (inner ℂ v v) = ‖v‖ ^ 2 := inner_self_eq_norm_sq v
    have h4 : (inner ℂ v v).re = ‖v‖ ^ 2 := h3
    rw [h4]
    exact pow_pos hpos 2
  have hN : {g | 0 < (inner ℂ v ((Rcusp μ g) v)).re} ∈ 𝓝 (1 : GA E a) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp cc)).mem_nhds h1pos
  obtain ⟨φ, hφc, hφs, hφ0, hφ1, hφN⟩ := GlobalTheory.CompanionTheory.Bump.exists_nonneg_bump (1 : GA E a) _ hN
  have hfc : Continuous fun g => (φ g : ℂ) := Complex.continuous_ofReal.comp hφc
  have hfs : HasCompactSupport fun g => (φ g : ℂ) := hφs.comp_left Complex.ofReal_zero
  refine ⟨fun g => (φ g : ℂ), hfc, hfs, hc E a μ _ hfc hfs, fun h0 => ?_⟩
  have key := hU.inner_repOp (μ := μ) hfc hfs v v
  rw [h0, inner_zero_right] at key
  have hint : Integrable (fun g => (φ g : ℂ) * inner ℂ v ((Rcusp μ g) v)) μ :=
    (hfc.mul cc).integrable_of_hasCompactSupport hfs.mul_right
  have h8 := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul] at h8
  rw [← key, Complex.zero_re] at h8
  have h9 : 0 < ∫ g, φ g * (inner ℂ v ((Rcusp μ g) v)).re ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (hφc.mul (Complex.continuous_re.comp cc)) hφs.mul_right (fun g => ?_) (mul_ne_zero hφ1 h1pos.ne')
    by_cases hg : φ g = 0
    · simp [hg]
    · exact mul_nonneg (hφ0 g) (hφN hg).le
  linarith

end GlobalTheory.CompanionTheory.CuspGL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfL2CuspidalMem
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspL2

theorem exists_lintegral_enorm_lift_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {C : Set G} (hC : IsCompact C) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ F : L2 Γ μ, ∫⁻ g in C, ‖lift Γ F g‖ₑ ∂μ ≤ M * ‖F‖ₑ := by
  have hS : {γ : Γ | (γ : G) ∈ C * C⁻¹}.Finite := finite_mem_compact (hC.mul hC.inv)
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ≥0∞, N = ({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℝ≥0∞) := ⟨_, rfl⟩
  have hN : N ≠ ∞ := by simpa [hNdef] using hS
  have hfin : μ C ≠ ∞ := hC.measure_lt_top.ne
  refine ⟨N ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ), ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hN)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin), fun F => ?_⟩
  have hm : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have h2 : ∫⁻ g in C, ‖lift Γ F g‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ ≤
      N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ≥0∞).toReal ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
    rw [← lintegral_indicator hC.measurableSet,
      lintegral_eq_lintegral_tsum (Γ := Γ) ((hm.enorm.pow_const _).indicator hC.measurableSet),
      ← lintegral_const_mul' _ _ hN]
    refine lintegral_mono fun q => ?_
    rw [hNdef]
    refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (GlobalTheory.AutomorphicL2Local.tsum_indicator_le Γ C q.out _)
    by_cases hγ : (γ : G) * q.out ∈ C
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ]
      simp only [GlobalTheory.AutomorphicL2Unitary.lift, mk_mul, Quotient.out_eq]
    · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem hγ]
  have h3 : eLpNorm (lift Γ F) 2 (μ.restrict C) ≤ N ^ (1 / 2 : ℝ) * ‖F‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (f := F) (by simp) (by simp)]
    refine (ENNReal.rpow_le_rpow h2 (by simp)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp)]
    simp
  have h4 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict C) (p := 1) (q := 2) (by norm_num) hm.restrict
  have e : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [eLpNorm_one_eq_lintegral_enorm, e, Measure.restrict_apply_univ] at h4
  calc _ ≤ N ^ (1 / 2 : ℝ) * ‖F‖ₑ * μ C ^ (1 / 2 : ℝ) := h4.trans (by gcongr)
    _ = _ := by ring

section Adelic

variable {E : Type} [Field E] [NumberField E] {a r : ℕ}

theorem exists_mem_apply_unip_eq {X : Type*} {u : GA E a → X} (hl : ∀ γ g, u (ratGL E a γ * g) = u g)
    {K : Set (BlockIx a r → Ad E)} (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K) (x : BlockIx a r → Ad E) :
    ∃ k ∈ K, ∀ g, u (unip x * g) = u (unip k * g) := by
  obtain ⟨_, ⟨y, rfl⟩, hk⟩ := hcov x
  refine ⟨_, hk, fun g => ?_⟩
  rw [unip_add, mul_assoc]
  exact ((congrArg (fun v => u (v * _)) (unip_algebraMap y)).trans (hl _ _)).symm

variable [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]

theorem lintegral_constTerm_le [IsTotallyComplex E] (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (ν : Measure (BlockIx a r → Ad E)) {𝓕 : Set (BlockIx a r → Ad E)} (hν𝓕 : ν 𝓕 ≠ ∞)
    {K : Set (BlockIx a r → Ad E)} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K) {C : Set (GA E a)}
    (hC : IsCompact C) {u : GA E a → ℂ} (hc : Continuous u) (hl : ∀ γ g, u (ratGL E a γ * g) = u g) :
    ∫⁻ g in C, ‖∫ x in 𝓕, u (unip x * g) ∂ν‖ₑ ∂μ ≤ ν 𝓕 * ∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 hν𝓕
  haveI : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  have hC' : IsCompact ((unip '' K) * C) := (hK.image continuous_unip).mul hC
  have hb : ∀ x, ∫⁻ g in C, ‖u (unip x * g)‖ₑ ∂μ ≤ ∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ := fun x => by
    obtain ⟨k, hk, e⟩ := exists_mem_apply_unip_eq hl hcov x
    simp only [e]
    rw [← (measurePreserving_mul_left μ (unip k)).setLIntegral_comp_preimage hC'.measurableSet
      hc.enorm.measurable]
    exact lintegral_mono_set fun g hg => Set.mul_mem_mul ⟨k, hk, rfl⟩ hg
  have hj : Continuous fun p : GA E a × (BlockIx a r → Ad E) => ‖u (unip p.2 * p.1)‖ₑ :=
    (hc.comp ((continuous_unip.comp continuous_snd).mul continuous_fst)).enorm
  calc ∫⁻ g in C, ‖∫ x in 𝓕, u (unip x * g) ∂ν‖ₑ ∂μ
      ≤ ∫⁻ g in C, ∫⁻ x in 𝓕, ‖u (unip x * g)‖ₑ ∂ν ∂μ :=
        lintegral_mono fun g => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x in 𝓕, ∫⁻ g in C, ‖u (unip x * g)‖ₑ ∂μ ∂ν := lintegral_lintegral_swap hj.aemeasurable
    _ ≤ ∫⁻ x in 𝓕, (∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ) ∂ν := lintegral_mono hb
    _ = _ := by rw [setLIntegral_const, mul_comm]

theorem continuous_constTerm [IsTotallyComplex E] (ν : Measure (BlockIx a r → Ad E)) {𝓕 : Set (BlockIx a r → Ad E)}
    (hν𝓕 : ν 𝓕 ≠ ∞) {K : Set (BlockIx a r → Ad E)} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K)
    {u : GA E a → ℂ} (hc : Continuous u) (hl : ∀ γ g, u (ratGL E a γ * g) = u g) :
    Continuous fun g => ∫ x in 𝓕, u (unip x * g) ∂ν := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 hν𝓕
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g₀
  obtain ⟨B, hB⟩ := ((hK.image continuous_unip).mul hC).exists_bound_of_continuousOn hc.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => B)
    (.of_forall fun g => (hc.comp (continuous_unip.mul continuous_const)).aestronglyMeasurable) ?_
    (integrable_const _) (.of_forall fun x => (hc.comp (continuous_const.mul continuous_id)).continuousAt)
  filter_upwards [hg] with g hg'
  refine .of_forall fun x => ?_
  obtain ⟨k, hk, e⟩ := exists_mem_apply_unip_eq hl hcov x
  rw [e]
  exact hB _ (Set.mul_mem_mul ⟨k, hk, rfl⟩ hg')

end Adelic

theorem isCuspidal_of_toL2_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : GA E a → ℂ), Continuous φ →
    (∀ γ g, φ (ratGL E a γ * g) = φ g) → (∀ t g, φ (splitCentre E a t * g) = φ g) →
    ∀ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ L2cusp μ → IsCuspidal φ := by
  intro E _ _ _ a μ _ _ φ hc hl hs h hF r h0 h1 _ _ ν 𝓕 hν h𝓕 g
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.ConstNotCusp.discreteTopology_ratN E a r
  haveI : Countable (ratN E a r) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  have hν𝓕 : ν 𝓕 ≠ ∞ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK hcov ν h𝓕).ne
  have hcont := continuous_constTerm ν hν𝓕 hK hcov hc hl
  have key : ∀ C : Set (GA E a), IsCompact C → ∫⁻ g in C, ‖∫ x in 𝓕, φ (unip x * g) ∂ν‖ₑ ∂μ = 0 := fun C hC => by
    obtain ⟨M, hM, hb⟩ := exists_lintegral_enorm_lift_le (latticeGL E a) μ ((hK.image continuous_unip).mul hC)
    have step : ∀ F' ∈ cuspContinuousL2 μ, ∫⁻ g in C, ‖∫ x in 𝓕, φ (unip x * g) ∂ν‖ₑ ∂μ ≤ ν 𝓕 * (M * ‖h.toL2 - F'‖ₑ) := by
      rintro F' ⟨ψ, hψ, e⟩
      have hcomp : ∀ g, ∫ x in 𝓕, (φ (unip x * g) - ψ (unip x * g)) ∂ν = ∫ x in 𝓕, φ (unip x * g) ∂ν := fun g => by
        rw [integral_sub (integrableOn_unip hc hl ν h𝓕 g) (integrableOn_unip hψ.1 hψ.2.1 ν h𝓕 g),
          hψ.2.2.2 r h0 h1 ν 𝓕 hν h𝓕 g, sub_zero]
      have h2 := lintegral_constTerm_le μ ν hν𝓕 hK hcov hC (u := fun g => φ g - ψ g) (hc.sub hψ.1)
        (fun γ g => by rw [hl, hψ.2.1])
      simp only [hcomp] at h2
      have e' : lift (latticeGL E a) (h.toL2 - F') =ᵐ[μ] fun g => φ g - ψ g :=
        Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_sub h.toL2 F')) (h.lift_toL2_ae_eq.sub e)
      refine h2.trans ?_
      gcongr
      refine le_trans (le_of_eq (lintegral_congr_ae (ae_restrict_of_ae ?_))) (hb (h.toL2 - F'))
      exact e'.mono fun g eg => by rw [eg]
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (show h.toL2 ∈ closure (cuspContinuousL2 μ : Set _) from hF)
    have ht : Filter.Tendsto (fun n => ν 𝓕 * (M * ‖h.toL2 - u n‖ₑ)) Filter.atTop (𝓝 0) := by
      have h3 : Filter.Tendsto (fun n => h.toL2 - u n) Filter.atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := h.toL2)).sub hlim
      have h4 : Filter.Tendsto (fun n => ‖h.toL2 - u n‖ₑ) Filter.atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto _).comp h3
      simpa using ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul h4 (Or.inr hM)) (Or.inr hν𝓕)
    exact le_antisymm (ge_of_tendsto' ht fun n => step _ (hu n)) zero_le
  have hae : (fun g => ∫ x in 𝓕, φ (unip x * g) ∂ν) =ᵐ[μ] 0 := by
    have h5 : ∀ n, ∀ᵐ g ∂μ.restrict (compactCovering (GA E a) n), ∫ x in 𝓕, φ (unip x * g) ∂ν = 0 := fun n => by
      have := (lintegral_eq_zero_iff' hcont.enorm.aemeasurable).1 (key _ (isCompact_compactCovering _ n))
      exact this.mono fun g eg => by simpa using eg
    have h6 := ae_restrict_iUnion_iff _ _ |>.2 h5
    rwa [iUnion_compactCovering, Measure.restrict_univ] at h6
  exact congrFun ((Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hae) g

end GlobalTheory.CompanionTheory.CuspL2

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective
section
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.Bridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

variable (F E n) in

abbrev dimN : ℕ := Fintype.card (Fin n × Fin (Module.finrank F E))

def trG : GAd σ J →* GL (Fin (dimN F E n)) (AF F) :=
  (trHom (ι := Fin n) (Module.finBasis F E) (AF F)).comp (matHom (AF F) σ J)

variable (F) in

def cvec (v : Fin n → E) : Fin (dimN F E n) → F := fun p =>
  (Module.finBasis F E).repr (v ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
    ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2

theorem cvec_injective : Function.Injective (cvec F : (Fin n → E) → Fin (dimN F E n) → F) := by
  intro u v h
  funext i
  apply (Module.finBasis F E).repr.injective
  ext k
  simpa [cvec] using congrFun h (Fintype.equivFin (Fin n × Fin (Module.finrank F E)) (i, k))

theorem cvec_surjective : Function.Surjective (cvec F : (Fin n → E) → Fin (dimN F E n) → F) := by
  intro x
  refine ⟨fun i => (Module.finBasis F E).equivFun.symm fun k => x (Fintype.equivFin _ (i, k)), ?_⟩
  funext p
  simp [cvec, Module.Basis.equivFun_symm_apply, Finsupp.single_apply]

theorem cvec_ne_zero {v : Fin n → E} (hv : v ≠ 0) : cvec F v ≠ 0 := by
  intro h
  apply hv
  apply cvec_injective (F := F)
  rw [h]
  funext p
  simp [cvec]

theorem ratVec_cvec (v : Fin n → E) :
    Reduction.ratVec (cvec F v) = resVec (ι := Fin n) (Module.finBasis F E) (AF F) (ratV F v) := by
  funext p
  simp only [Reduction.ratVec, cvec, resVec, Function.comp_apply, coordsVec, coords, ratV, inclR]
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem hv_eq (ξ : Fin n → AF F ⊗[F] E) :
    hv ξ = Reduction.adelicNorm (resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ) := rfl

theorem hgt_eq (g : GAd σ J) (v : Fin n → E) : hgt σ J g v = Reduction.height (trG σ J g) (cvec F v) := by
  rw [Reduction.height, ratVec_cvec, trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hgt, hv_eq, map_inv]

section Top

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

theorem continuous_trG : Continuous (trG σ J) :=
  (continuous_trHom (ι := Fin n) (Module.finBasis F E) (AF F)).comp (isEmbedding_matHom (AF F) σ J).continuous

end Top

theorem exists_hgt_le {C : Set (GAd σ J)} (hC : IsCompact C) {v : Fin n → E} (hv : v ≠ 0) :
    ∃ B : ℝ, ∀ c ∈ C, hgt σ J c v ≤ B := by
  obtain ⟨P, -, hP⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hC.image (continuous_trG σ J))
  refine ⟨P * Reduction.adelicNorm (Reduction.ratVec (cvec F v)), fun c hc => ?_⟩
  rw [hgt_eq]
  exact hP _ ⟨c, hc, rfl⟩ _ (Reduction.hasFiniteContent_ratVec (cvec_ne_zero hv))

end GlobalTheory.CompanionTheory.RedCov.Bridge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeRhamFiniteAndFiltrationBoundedStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_finite_and_filtration_bounded : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.KIso → KH.GrAff → KH.GrCechFin → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] (j : ℕ),
    FiniteDimensional K (HdR q j) ∧ ∀ x ∈ FilR q j (j + 1), x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KFin.main | exact GlobalTheory.CompanionTheory.KFin.main | (intros; apply GlobalTheory.CompanionTheory.KFin.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHoldsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_jacquet_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k := by
  first | exact @GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main | exact GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main | (intros; apply GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscrNormConductorEqDFOfUnramified
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem discrNormConductor_eq_dF_of_unramified :
    ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
      standardOpenSubgroup F ≤ χ.toIdele.ker → χ.discrNormConductor = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F := by
  intro F _ _ χ hχ
  have htop : χ.conductor = ⊤ := by
    have h := (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1
      ((map_idealLevel_le_standardOpenSubgroup ⊤).trans hχ)
    rw [Ideal.dvd_iff_le, top_le_iff] at h
    exact h
  rw [HeckeCharacter.discrNormConductor, htop, Ideal.absNorm_top, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF]
  simp

end GlobalTheory.CompanionTheory.PartialZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPointsStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_rational_points : PositivityTheory.GramSchwartzFunctions.EC.RatPts := by
  first | exact @GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn | exact GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn | (intros; apply GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSiegelParabolicInvarianceStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_siegel_parabolic_invariance : PositivityTheory.GramSchwartzFunctions.EC.PInv := by
  first | exact @GlobalTheory.CompanionTheory.EisCellsPInv.pInv | exact GlobalTheory.CompanionTheory.EisCellsPInv.pInv | (intros; apply GlobalTheory.CompanionTheory.EisCellsPInv.pInv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspProdIrr
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.Ysupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSubquotient_of_prod₂_equiv {r t : ℕ} {U W A B C D : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    [AddCommGroup D] [Module ℂ D] {σ : Representation ℂ (GL (Fin r) k) U} {ρ : Representation ℂ (GL (Fin t) k) W}
    {α : Representation ℂ (GL (Fin r) k) A} {β : Representation ℂ (GL (Fin t) k) B}
    {γ : Representation ℂ (GL (Fin (r + t)) k) C} {δ : Representation ℂ (GL (Fin (r + t)) k) D}
    (hα : IsSmooth α) (hβ : IsSmooth β) (h₁ : IsSubquotient σ α) (h₂ : IsSubquotient ρ β)
    (E : (prod₂ σ ρ).Equiv δ) (F : (prod₂ α β).Equiv γ) : IsSubquotient δ γ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective).trans
    ((GlobalTheory.CompanionTheory.ProdSubquot.prod₂_isSubquotient k r t U A W B σ α ρ β hα hβ h₁ h₂).trans
      (.of_injective F.toIntertwiningMap F.toLinearEquiv.injective))

theorem nonempty_prod₂_equiv_prodIrr_succ {c : ℕ} (y : Fin (c + 1) → IrrGL k)
    (hd : ∑ a, (y a).1 = (y 0).1 + ∑ a : Fin c, (y a.succ).1) :
    Nonempty ((prod₂ (y 0).rep (prodIrr (fun a : Fin c => y a.succ) rfl)).Equiv (prodIrr y hd)) := by
  have := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := k) (fun a => (y a).1) hd fun a => (y a).rep
  exact this

end GlobalTheory.CompanionTheory.Ysupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenIntegralSubgroupStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_integral_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) →
  ∃ U : Subgroup (AdelicGLn.integralFiniteGL E N), IsOpen (U : Set (AdelicGLn.integralFiniteGL E N)) ∧ ∀ u : U, ∃ k ∈ L,
    finEmb E N ((u : AdelicGLn.integralFiniteGL E N) : AdelicGLn.FiniteAdelicGL E N) = finGL E N k := by
  first | exact @GlobalTheory.CompanionTheory.Conc.LevelU.exists_level | exact GlobalTheory.CompanionTheory.Conc.LevelU.exists_level | (intros; apply GlobalTheory.CompanionTheory.Conc.LevelU.exists_level <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameBlockZeroStabilizesFlagStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_block_zero_stabilizes_flag : ∀ (E : Type) [Field E] (S : E →+* E) (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E), cT S Y * J * X = 1 → ∀ (g : Matrix (Fin n) (Fin n) E) (j : Fin r), (∀ α β : FrameIx r, frameLev j α < 2 → frameLev j β = 2 → frameIdem S J X Y α * g * frameIdem S J X Y β = 0) → ∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, g *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.stabilises_flag_span | exact GlobalTheory.CompanionTheory.RapidDecay.stabilises_flag_span | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.stabilises_flag_span <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCechCohomologyFiniteStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_cech_cohomology_finite : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ),
    Module.Finite O ((cechH (sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
      (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) r).cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.GrCech.main_thm | exact GlobalTheory.CompanionTheory.GrCech.main_thm | (intros; apply GlobalTheory.CompanionTheory.GrCech.main_thm <;> assumption)
end

