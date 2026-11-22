import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0654
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0669
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle0001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0693
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0663
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosocles
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0659
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormulaStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joined_block_formula : JnBl := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.jnBl | exact GlobalTheory.CompanionTheory.ColumnSplitting.jnBl | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.jnBl <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedProjectionFormulaStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joined_projection_formula : JnPi := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds | exact GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionEquicontinuous
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral

open scoped Pointwise

theorem sq_lintegral_mul_le {X : Type*} [MeasurableSpace X] (ν : Measure X) {a b : X → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) :
    (∫⁻ w, a w * b w ∂ν) ^ 2 ≤ (∫⁻ w, a w ∂ν) * ∫⁻ w, a w * b w ^ 2 ∂ν :=
  _root_.UpperTheory.Reformulated.B.P6.r96a.GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral.sq_lintegral_mul_le ν ha hb

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem eventually_lintegral_translate_le [LocallyCompactSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {α : G → ℂ} (hα : Continuous α) (hs : HasCompactSupport α)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 (1 : G), ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ε := by
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  have hC : IsCompact (V * tsupport α) := hVc.mul hs
  set C : Set G := V * tsupport α with hCdef
  have hfin : μ C ≠ ∞ := hC.measure_lt_top.ne
  have hc : 0 < ε / (μ C + 1) :=
    ENNReal.div_pos hε.ne' (by simp [hfin])
  set c : ℝ≥0∞ := ε / (μ C + 1) with hcdef
  have hunif : ∀ᶠ y in 𝓝 (1 : G), ∀ w ∈ C, ‖α (y⁻¹ * w) - α w‖ₑ < c := by
    refine hC.eventually_forall_of_forall_eventually fun w _ => ?_
    have hcont : Continuous fun z : G × G => ‖α (z.1⁻¹ * z.2) - α z.2‖ₑ := by
      fun_prop
    have h0 : ‖α ((1 : G)⁻¹ * w) - α w‖ₑ < c := by simpa using hc
    exact hcont.continuousAt.eventually_lt continuousAt_const h0
  filter_upwards [hunif, hV] with y hy hyV
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hle : ∀ w, ‖α (y⁻¹ * w) - α w‖ₑ ≤ C.indicator (fun _ => c) w := by
    intro w
    by_cases hw : w ∈ C
    · rw [Set.indicator_of_mem hw]
      exact (hy w hw).le
    · rw [Set.indicator_of_notMem hw]
      have h1 : α w = 0 := by
        by_contra h
        exact hw (Set.mem_mul.2 ⟨1, mem_of_mem_nhds hV, w, subset_tsupport _ h, one_mul w⟩)
      have h2 : α (y⁻¹ * w) = 0 := by
        by_contra h
        exact hw (Set.mem_mul.2 ⟨y, hyV, y⁻¹ * w, subset_tsupport _ h, by group⟩)
      simp [h1, h2]
  calc ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ∫⁻ w, C.indicator (fun _ => c) w ∂μ := lintegral_mono hle
    _ = c * μ C := lintegral_indicator_const hCm c
    _ ≤ c * (μ C + 1) := by gcongr; exact le_self_add
    _ = ε := ENNReal.div_mul_cancel (by simp) (by simp [hfin])

variable [LocallyCompactSpace G] [SecondCountableTopology G]

theorem enorm_translate_sub_le (μ : Measure G) [μ.IsHaarMeasure] {α ψ : G → ℂ} (hα : Continuous α)
    (hs : HasCompactSupport α) (hψ : Continuous ψ) {s : ℂ}
    (hrep : ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) (x y : G) :
    ‖s‖ₑ * ‖ψ (x * y) - ψ x‖ₑ ≤ ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ * ‖ψ (x * w)‖ₑ ∂μ := by
  have h1 : s * ψ (x * y) = ∫ w, α (y⁻¹ * w) * ψ (x * w) ∂μ := by
    rw [← hrep (x * y), ← integral_mul_left_eq_self (fun w => α (y⁻¹ * w) * ψ (x * w)) y]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp [mul_assoc]
  have hcs : HasCompactSupport fun w => α (y⁻¹ * w) := hs.comp_homeomorph (Homeomorph.mulLeft y⁻¹)
  have hi1 : Integrable (fun w => α (y⁻¹ * w) * ψ (x * w)) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hcs.mul_right
  have hi2 : Integrable (fun w => α w * ψ (x * w)) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hs.mul_right
  have h3 : s * (ψ (x * y) - ψ x) = ∫ w, (α (y⁻¹ * w) - α w) * ψ (x * w) ∂μ := by
    rw [mul_sub, h1, ← hrep x, ← integral_sub hi1 hi2]
    exact integral_congr_ae (ae_of_all _ fun w => by ring)
  rw [← enorm_mul, h3]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  exact lintegral_congr fun w => enorm_mul _ _

theorem lintegral_right_translate (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {ψ : G → ℂ}
    (hl : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (w : G) :
    ∫⁻ x in F, ‖ψ (x * w)‖ₑ ^ 2 ∂μ = ∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ := by
  have hF' : IsFundamentalDomain Γ (MulOpposite.op w • F) μ := hF.smul_of_comm (MulOpposite.op w)
  have himg : (fun x => x * w) '' F = MulOpposite.op w • F := rfl
  have h1 := (measurePreserving_mul_right μ w).setLIntegral_comp_emb
    (MeasurableEquiv.mulRight w).measurableEmbedding (fun x => ‖ψ x‖ₑ ^ 2) F
  rw [h1, himg]
  refine hF'.setLIntegral_eq hF _ fun γ x => ?_
  simp only [Subgroup.smul_def, smul_eq_mul]
  rw [hl _ γ.2]

theorem sq_mean_translate_le (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {α ψ : G → ℂ}
    (hα : Continuous α) (hs : HasCompactSupport α) (hψ : Continuous ψ)
    (hl : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) {s : ℂ}
    (hrep : ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x)
    (hn : (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1) (y : G)
    (hA : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≠ ∞) :
    ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ (∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ) ^ 2 := by
  set a : G → ℝ≥0∞ := fun w => ‖α (y⁻¹ * w) - α w‖ₑ with ha_def
  have hac : Continuous a := by fun_prop
  have ha : Measurable a := hac.measurable
  have hjm : Measurable fun z : G × G => a z.2 * ‖ψ (z.1 * z.2)‖ₑ ^ 2 := by
    have hc : Continuous fun z : G × G => ‖ψ (z.1 * z.2)‖ₑ := by fun_prop
    exact (ha.comp measurable_snd).mul (hc.measurable.pow_const 2)
  calc ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ
      = ∫⁻ x in F, (‖s‖ₑ * ‖ψ (x * y) - ψ x‖ₑ) ^ 2 ∂μ := by
        rw [← lintegral_const_mul' _ _ (by simp)]
        exact lintegral_congr fun x => (mul_pow _ _ _).symm
    _ ≤ ∫⁻ x in F, (∫⁻ w, a w * ‖ψ (x * w)‖ₑ ∂μ) ^ 2 ∂μ :=
        lintegral_mono fun x => by
          gcongr
          exact enorm_translate_sub_le μ hα hs hψ hrep x y
    _ ≤ ∫⁻ x in F, (∫⁻ w, a w ∂μ) * ∫⁻ w, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ :=
        lintegral_mono fun x => sq_lintegral_mul_le μ ha (by
          have : Continuous fun w => ‖ψ (x * w)‖ₑ := by fun_prop
          exact this.measurable)
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ x in F, ∫⁻ w, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ :=
        lintegral_const_mul' _ _ hA
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ w, ∫⁻ x in F, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ := by
        rw [lintegral_lintegral_swap hjm.aemeasurable]
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ w, a w ∂μ := by
        congr 1
        refine lintegral_congr fun w => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_right_translate μ Γ hF hl w, hn, mul_one]
    _ = (∫⁻ w, a w ∂μ) ^ 2 := (sq _).symm

theorem exists_nhds_sq_mean_le (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {α : G → ℂ} {δ : ℝ} {F : Set G}
    (hα : Continuous α) (hs : HasCompactSupport α) (hδ : 0 < δ) (hF : IsFundamentalDomain Γ F μ)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ U ∈ 𝓝 (1 : G), ∀ ψ : G → ℂ, Continuous ψ → (∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) →
      (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) →
      (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 → ∀ y ∈ U, ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  set d : ℝ≥0∞ := ENNReal.ofReal δ with hd
  have hd0 : d ≠ 0 := by simpa [hd] using hδ
  have hdt : d ≠ ∞ := ENNReal.ofReal_ne_top
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd0
  have hd2t : d ^ 2 ≠ ∞ := ENNReal.pow_ne_top hdt
  set ε : ℝ≥0∞ := min 1 (η * d ^ 2) with hε
  have hε0 : 0 < ε := lt_min one_pos (ENNReal.mul_pos hη.ne' hd2)
  have hε1 : ε ≤ 1 := min_le_left _ _
  refine ⟨_, eventually_lintegral_translate_le μ hα hs hε0, ?_⟩
  rintro ψ hψ hl ⟨s, hsδ, hrep⟩ hn y hy
  have hy' : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ε := hy
  have hA : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≠ ∞ := (hy'.trans hε1).trans_lt ENNReal.one_lt_top |>.ne
  have hb := sq_mean_translate_le μ Γ hF hα hs hψ hl hrep hn y hA
  have hds : d ≤ ‖s‖ₑ := by
    rw [hd, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal hsδ
  have hεε : ε ^ 2 ≤ η * d ^ 2 := by
    calc ε ^ 2 = ε * ε := sq ε
      _ ≤ 1 * ε := by gcongr
      _ = ε := one_mul ε
      _ ≤ η * d ^ 2 := min_le_right _ _
  have hfin : d ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ d ^ 2 * η := by
    calc d ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ
        ≤ ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ := by gcongr
      _ ≤ (∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ) ^ 2 := hb
      _ ≤ ε ^ 2 := by gcongr
      _ ≤ η * d ^ 2 := hεε
      _ = d ^ 2 * η := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_right hd2 hd2t).1 hfin

end GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral

theorem GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∀ η : ℝ≥0∞, 0 < η → ∃ U ∈ 𝓝 (1 : GA E N), ∀ ψ : GA E N → ℂ, Continuous ψ →
  (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) → (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) →
  (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 → ∀ y ∈ U, ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  intro E _ _ _ N _ _ μ _ α δ F hα hs hδ hF η hη
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.haar_right_invariant_totally_complex E N μ
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  exact GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral.exists_nhds_sq_mean_le μ (latticeGL E N) hα hs hδ hF hη
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccurs
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.ZWordL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decW_eq_decWord (Γ : Segment k) : decW Γ = Cos.decWord Γ := by
  apply List.ext_getElem
  · simp [decW, Cos.decWord]
  · intro n h1 h2
    simp only [decW, Cos.decWord, List.getElem_ofFn, List.getElem_reverse, List.length_ofFn, Fin.rev]
    congr 2
    omega

theorem isCusp_of_mem_decWord (Γ : Segment k) : ∀ w ∈ Cos.decWord Γ, w.IsCusp := by
  intro w hw
  simp only [Cos.decWord, List.mem_reverse, List.mem_ofFn] at hw
  obtain ⟨a, rfl⟩ := hw
  exact Γ.isCusp_term a

theorem sum_get_decWord (Γ : Segment k) : ∑ a, ((Cos.decWord Γ).get a).1 = Γ.deg := by
  have hc : ∀ a, ((Cos.decWord Γ).get a).1 = Γ.d := fun a => by
    have hm := List.get_mem (Cos.decWord Γ) a
    simp only [Cos.decWord, List.mem_reverse, List.mem_ofFn] at hm
    obtain ⟨i, hi⟩ := hm
    show ((List.ofFn Γ.term).reverse.get a).1 = Γ.d
    rw [← hi]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hc a), Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp [Cos.decWord, Segment.deg]

theorem nontrivial_of_isIrreducible {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (h : σ.IsIrreducible) : Nontrivial W := by
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  haveI : IsSimpleOrder (Subrepresentation σ) := h
  exact bot_ne_top (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _) :
    (⊥ : Subrepresentation σ) = ⊤)

theorem wd_wtW_of_isL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → ∀ (𝔪 : Multiset (Segment k)) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL 𝔪 π → ∀ (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 → Wd π (wtW Δ) := by
  intro k _ _ _ _ hA hS hJ 𝔪 N V _ _ π hπ h Δ hΔ
  have hmem : ∀ i, Δ i ∈ 𝔪 := fun i => hΔ.1 ▸ Multiset.mem_map_of_mem Δ (Finset.mem_univ i)
  choose x hx using fun i => SumProd.exists_isLSeg_of_isL hπ (hmem i)
  have hF : LFactors 𝔪 x := ⟨Δ, hΔ, hx⟩
  have hd0 : ∑ a, (x a).1 = N := (SumProd.sum_fst_of_lFactors hF).trans (SumProd.deg_of_isL hπ)
  have hd : ∑ a, (x (Fin.rev a)).1 = N := (Equiv.sum_comp Fin.revPerm (fun a => (x a).1)).trans hd0
  obtain ⟨hirr, f, hfinj, -⟩ := hS 𝔪 h N x hd hF π hπ
  obtain ⟨h', x', hd', hF', hcos⟩ := hπ
  have hsm : IsSmooth π := IsSubquotient.isSmooth (IsCosocle.isSubquotient hcos) (isSmooth_prodIrr _ _)
  have hfl : HasFiniteLength π := hasFiniteLength_of_isIrreducible hirr
  haveI := nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 : 1 ≤ jm (x ∘ Fin.rev) hd π :=
    GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x ∘ Fin.rev) hd π hsm f
      ⟨v, fun h0 => hv (hfinj (h0.trans (map_zero f).symm))⟩
  have hW : ∀ b, ∑ a, ((Cos.decWord (Δ (Fin.rev b))).get a).1 = ((x ∘ Fin.rev) b).1 := fun b =>
    (sum_get_decWord _).trans (hx (Fin.rev b)).deg_eq
  have h2 := GlobalTheory.T.jacquet_multiplicity_transitive_le hA (x ∘ Fin.rev) hd (fun b => Cos.decWord (Δ (Fin.rev b))) π hsm hfl hW
  have h3 : ∀ b, Cos.jmL (Cos.decWord (Δ (Fin.rev b))) ((x ∘ Fin.rev) b).rep = 1 := fun b =>
    (GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Δ (Fin.rev b)) _ (hx (Fin.rev b)) _ (isCusp_of_mem_decWord _)).1 rfl
  rw [Finset.prod_congr rfl (fun b _ => h3 b), Finset.prod_const_one, mul_one] at h2
  have h4 := h1.trans h2
  have hw : (List.ofFn fun b => Cos.decWord (Δ (Fin.rev b))).flatten = wtW Δ := by
    simp only [wtW, decW_eq_decWord]
  rw [hw] at h4
  unfold Cos.jmL at h4
  split_ifs at h4 with hdw
  · exact ⟨hdw, fun h0 => by rw [h0] at h4; simp at h4⟩
  · simp at h4

end GlobalTheory.CompanionTheory.ZWordL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.LSocle

section General

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSmooth_of_surjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : IsSmooth σ := by
  intro w
  obtain ⟨v, rfl⟩ := hf w
  let S : Subgroup G :=
    { carrier := {g | σ g (f v) = f v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : σ a⁻¹ (σ a (f v)) = f v := by
          rw [← Module.End.mul_apply, ← map_mul]; simp
        rwa [ha] at h1 }
  let T : Subgroup G :=
    { carrier := {g | ρ g v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ρ a⁻¹ (ρ a v) = v := by
          rw [← Module.End.mul_apply, ← map_mul]; simp
        rwa [ha] at h1 }
  have hT : IsOpen (T : Set G) := hρ v
  have hTS : T ≤ S := fun g hg => by
    have hg' : ρ g v = v := hg
    show σ g (f v) = f v
    rw [← f.isIntertwining, hg']
  exact Subgroup.isOpen_mono hTS hT

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thetaW_surjective (N : ℕ) : Function.Surjective (thetaW k N) :=
  fun g => ⟨thetaW k N g, GlobalTheory.T.transpose_inverse_involution_apply N g⟩

theorem comp_thetaW_thetaW {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) : (π.comp (thetaW k N)).comp (thetaW k N) = π :=
  MonoidHom.ext fun g => by
    show π (thetaW k N (thetaW k N g)) = π g
    rw [GlobalTheory.T.transpose_inverse_involution_apply N g]

theorem isCosocle_comp_thetaW {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin N) k) W} {π : Representation ℂ (GL (Fin N) k) V}
    (h : IsCosocle σ (π.comp (thetaW k N))) : IsCosocle (σ.comp (thetaW k N)) π := by
  apply GlobalTheory.FieldTransport.isCosocle_of_comp (thetaW_surjective N)
  show IsCosocle ((σ.comp (thetaW k N)).comp (thetaW k N)) _
  rw [comp_thetaW_thetaW σ]
  exact h

theorem equiv_contra_comp_thetaW (hGK : GKLocal k) {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin N) k) W) (hs : IsSmooth (σ.comp (thetaW k N)))
    (hi : Representation.IsIrreducible (σ.comp (thetaW k N))) : Nonempty (σ.Equiv (contra (σ.comp (thetaW k N)))) := by
  have E := GlobalTheory.T.gelfand_kazhdan_contragredient hGK N (σ.comp (thetaW k N)) hs hi
  rwa [comp_thetaW_thetaW σ] at E

theorem prodIrr_congr {h N : ℕ} {x y : Fin h → IrrGL k} (e : x = y) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

set_option maxHeartbeats 2000000 in

theorem isSocle_rev_of_isCosocle (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x y : Fin h → IrrGL k) (hd0 : ∑ a, (x a).1 = N) (hd : ∑ a, ((x ∘ Fin.rev) a).1 = N) (hdy : ∑ a, (y a).1 = N)
    (e3 : (fun a => dualCl (y (Fin.rev a))) = x) (e6 : (fun a => dualCl (y a)) = x ∘ Fin.rev)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hc : IsCosocle π (prodIrr x hd0)) : IsSocle π (prodIrr (x ∘ Fin.rev) hd) := by
  obtain ⟨hd2, ⟨E2⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK y hdy
  obtain ⟨E3⟩ := prodIrr_congr e3 hd2 hd0
  have hc1 : IsCosocle π ((prodIrr y hdy).comp (thetaW k N)) :=
    hc.of_equiv (Representation.Equiv.refl _) (E2.trans E3).symm
  have hc2 : IsCosocle (π.comp (thetaW k N)) (prodIrr y hdy) := isCosocle_comp_thetaW hc1
  have hs : IsSmooth (π.comp (thetaW k N)) := by
    obtain ⟨-, f, hf, -⟩ := hc2
    exact isSmooth_of_surjective (isSmooth_prodIrr y hdy) f hf
  have hsoc := GlobalTheory.T.cosocle_contragredient_socle hA (π.comp (thetaW k N)) (prodIrr y hdy) (isSmooth_prodIrr y hdy)
    (GlobalTheory.T.product_irreducible_finite_length hA y hdy) hc2
  obtain ⟨E4⟩ := equiv_contra_comp_thetaW hGK π hs hc2.1
  obtain ⟨hd5, ⟨E5⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA y hdy
  obtain ⟨E6⟩ := prodIrr_congr e6 hd5 hd
  exact hsoc.of_equiv E4.symm (E5.trans E6)

theorem lSocleGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k → LOrderFree k → LSocleGL k := by
  intro k _ _ _ _ hA hGK hLO 𝔪 h N x hd hx V _ _ π hπ
  have hd0 : ∑ a, (x a).1 = N := by
    rw [← hd]
    exact (Equiv.sum_comp Fin.revPerm (fun a => (x a).1)).symm
  have hc := hLO 𝔪 h N x hd0 hx π hπ
  obtain ⟨hdy, -⟩ := GlobalTheory.T.contragredient_product_irreducible hA (x ∘ Fin.rev) hd
  exact isSocle_rev_of_isCosocle hA hGK x (fun a => dualCl ((x ∘ Fin.rev) a)) hd0 hd hdy
    (funext fun a => by
      simp only [Function.comp_apply, Fin.rev_rev]
      exact GlobalTheory.T.dual_class_involutive hA (x a))
    (funext fun a => GlobalTheory.T.dual_class_involutive hA (x (Fin.rev a))) π hc

end GlobalTheory.CompanionTheory.LSocle
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCharacterIntegralValueStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_character_integral_value : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) →
  ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ =
    (((Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.latchar1 | exact GlobalTheory.CompanionTheory.LFUDom.latchar1 | (intros; apply GlobalTheory.CompanionTheory.LFUDom.latchar1 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCharacterIntegralZeroStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_character_integral_zero : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (¬ ∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) →
  ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.integral_lattice_char_eq_zero | exact GlobalTheory.CompanionTheory.LFUDom.integral_lattice_char_eq_zero | (intros; apply GlobalTheory.CompanionTheory.LFUDom.integral_lattice_char_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeGlTwoTranslateStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_volume_gl_two_translate : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} = (modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ)⁻¹ * (Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]} := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.latvol | exact GlobalTheory.CompanionTheory.LFUDom.latvol | (intros; apply GlobalTheory.CompanionTheory.LFUDom.latvol <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeafBoundStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leaf_bound_alt : GlobalTheory.CompanionTheory.EGlue.DiscInf → GlobalTheory.CompanionTheory.EGlue.TopInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.LeafBound := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound | exact GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound | (intros; apply GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiePowerL2FactorialBoundStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_power_l2_factorial_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E a)), IsStable W → (∀ φ ∈ W, IsAutForm φ ∧ MemL2Quotient (latticeGL E a) μ φ.1) → ∀ φ ∈ W, ∀ X : GlobalTheory.CuspRep.Lie E a, ∃ M C : ℝ, ∀ (k : ℕ) (h : MemL2Quotient (latticeGL E a) μ (((lie E a X) ^ k) φ).1), ‖h.toL2‖ ≤ M * C ^ k * (k.factorial : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.AnalyticBound.factorial_bound | exact GlobalTheory.CompanionTheory.AnalyticBound.factorial_bound | (intros; apply GlobalTheory.CompanionTheory.AnalyticBound.factorial_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalConditionsOfEquivStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_conditions_of_equiv : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → LocConds θ' K' (e d) f' → LocConds θ K d f := by
  first | exact @GlobalTheory.CompanionTheory.TransportLoc.locConds_of_equiv | exact GlobalTheory.CompanionTheory.TransportLoc.locConds_of_equiv | (intros; apply GlobalTheory.CompanionTheory.TransportLoc.locConds_of_equiv <;> assumption)
end

