import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0093
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CompactPartIntegralsTendsto
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0084
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0015
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0094
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereRegularizationLogLogBound
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0095
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetric
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSetStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mInt_eq_integral_maMeasure : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) → (∀ i, IsPotential A (P i)) → IsPotential A Θ → IsPsh A Θ → (∀ i, A.SmoothOn U (f i)) → (∀ i, IsPshOn A U (P i + LocPot.ofFun (f i) + Θ)) → ∀ g : X → ℝ, ContinuousOn g U → Integrable g (maMeasure A fun i => P i + LocPot.ofFun (f i) + Θ) → MIntegrable A (fun i => P i + LocPot.ofFun (f i) + Θ) g ∧ mInt A (fun i => P i + LocPot.ofFun (f i) + Θ) g = ∫ y, g y ∂(maMeasure A fun i => P i + LocPot.ofFun (f i) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null | exact GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyRegularizationBound
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem maMeasure_bdry_eq_zero {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hS : IsSection A L s) (hSNC : IsSNC A L s m W)
    (Φ : Fin e → LocPot X) : maMeasure A Φ (bdry s) = 0 := by
  have hB := LeviFormBoundaryTopology.isClosed_bdry hS
  have hAn : A.IsAnalyticSubset (bdry s) := by
    intro x
    refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩
  have hInt : interior (bdry s) = ∅ := LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC
  unfold maMeasure
  split_ifs with h
  · simp only [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hT := (A.chart j).open_target.measurableSet
    rw [Measure.map_apply_of_aemeasurable (((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac
      (withDensity_absolutelyContinuous _ _)) hB.measurableSet]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' hT]
    have := analyticNull A (bdry s) hAn hInt j
    rw [Set.inter_comm, (A.chart j).image_source_inter_eq'] at this
    rwa [Set.inter_comm]
  · simp

theorem tail_lintegral_le_of_eventually {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (hL : IsPotential A L) (hS : IsSection A L s) (Φ : Fin e → LocPot X)
    (ΦT : ℝ → Fin e → LocPot X)
    (hc : ∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ))
    (hpot : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (ΦT t i))
    (hunif : ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K →
      TendstoUniformlyOn (fun t => locDens A (ΦT t) j) (locDens A Φ j) (𝓝[>] 0) K)
    (g : X → ℝ) (hgm : Measurable g) (hgc : ContinuousOn g (bdry s)ᶜ)
    (R B : ℝ)
    (hg1 : ∀ y ∉ bdry s, R ≤ rW L s y → 0 ≤ g y)
    (hB : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (g y)
      ∂maMeasure A (ΦT t) ≤ ENNReal.ofReal B) :
    ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (g y) ∂maMeasure A Φ ≤
      ENNReal.ofReal B := by
  have hU : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl
  obtain ⟨hbm, hrm⟩ := TailBoundAlt.bdry_rW_meas A L s hL hS
  let Es : ℕ → Set X := fun N => ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) ∩ {y | rW L s y ≤ (N : ℝ)}
  have hun : (bdry s)ᶜ ∩ {y | R ≤ rW L s y} = ⋃ N, Es N := by
    ext y
    constructor
    · intro h
      obtain ⟨N, hN⟩ := exists_nat_ge (rW L s y)
      exact Set.mem_iUnion.2 ⟨N, h, hN⟩
    · intro h
      obtain ⟨N, hN⟩ := Set.mem_iUnion.1 h
      exact hN.1
  have hmono : Monotone Es := fun a b hab y hy =>
    ⟨hy.1, show rW L s y ≤ (b : ℝ) from
      le_trans (show rW L s y ≤ (a : ℝ) from hy.2) (Nat.cast_le.2 hab)⟩
  rw [hun, setLIntegral_iUnion_of_directed _ hmono.directed_le]
  refine iSup_le fun N => ?_
  have hEm : MeasurableSet (Es N) :=
    (hbm.compl.inter (measurableSet_le measurable_const hrm)).inter
      (measurableSet_le hrm measurable_const)
  have hKU : {y | y ∉ bdry s ∧ rW L s y ≤ (N : ℝ)} ⊆ (bdry s)ᶜ := fun y hy => hy.1
  have hEK : Es N ⊆ {y | y ∉ bdry s ∧ rW L s y ≤ (N : ℝ)} := fun y hy => ⟨hy.1.1, hy.2⟩
  obtain ⟨-, hint, hlim⟩ := compact_part_integrals_tendsto A (bdry s)ᶜ Φ ΦT hU hc hpot hunif g
    (fun _ => g) (fun _ => hgc)
    (fun u hu x _ => ⟨Set.univ, Filter.univ_mem,
      Eventually.of_forall fun t y _ => refl_mem_uniformity hu⟩)
    _ (Es N) (isCompact_rW_sublevel A L s hL hS (N : ℝ)) hKU hEm hEK
  have hnn : ∀ μ : Measure X, 0 ≤ᵐ[μ.restrict (Es N)] g := fun μ =>
    (ae_restrict_iff' hEm).2 (Eventually.of_forall fun y hy => hg1 y hy.1.1 hy.1.2)
  have hle : ∫ y in Es N, g y ∂maMeasure A Φ ≤ max B 0 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [hB] with t ht
    rw [integral_eq_lintegral_of_nonneg_ae (hnn _) hgm.aestronglyMeasurable,
      ← ENNReal.toReal_ofReal']
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((lintegral_mono_set (fun y hy => hy.1)).trans ht)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.mono_set hEK) (hnn _)]
  refine (ENNReal.ofReal_le_ofReal hle).trans (le_of_eq ?_)
  rcases le_total B 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

theorem limit_measure_tail : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) → IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) ∧ ∃ K : ℝ, ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  intro hTB e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR hC2
  obtain ⟨K, t₁, ht₁, -, hT⟩ :=
    tail_uniform hTB A Θ L s m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR
  have hB := LeviFormBoundaryTopology.isClosed_bdry hS
  obtain ⟨-, hrm⟩ := TailBoundAlt.bdry_rW_meas A L s hL hS
  have hrc := (rW_open A L s hL hS).1
  have hge := rW_ge L s hnorm
  have hc := locDens_add_ofFun_continuousOn A (bdry s)ᶜ th ph Θ hB.isOpen_compl
    (fun i => (hW i).1) hΘ (fun i => (hW i).2.1)
  have hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, A.Smooth (phT i t) := eventually_all.2 fun i => by
    filter_upwards [Ioc_mem_nhdsGT (hR i).1] with t ht
    exact ((hR i).2.2 t ht.1 ht.2).1
  have hunif := conv_dens A Θ s th ph phT hB hΘ (fun i => (hW i).1) (fun i => (hW i).2.1) hsm hC2
  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioc 0 t₁ := Ioc_mem_nhdsGT ht₁
  have hpot : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (th i + LocPot.ofFun (phT i t) + Θ) := by
    filter_upwards [hbd] with t ht
    exact fun i => ((hT (fun _ => t) fun _ => ht).1 i).1
  have tail1 : ∀ R : ℝ, Real.exp 1 ≤ R →
      maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) ≤
        ENNReal.ofReal (K * Real.log R / R) := by
    intro R hRe
    have h := tail_lintegral_le_of_eventually A L s hL hS
      (fun i => th i + LocPot.ofFun (ph i) + Θ) (fun t i => th i + LocPot.ofFun (phT i t) + Θ)
      hc hpot hunif (fun _ => 1) measurable_const continuousOn_const
      R (K * Real.log R / R)
      (fun _ _ _ => zero_le_one) (by
        filter_upwards [hbd] with t ht
        have h1 := ((hT (fun _ => t) fun _ => ht).2 R hRe).1
        simp only [ENNReal.ofReal_one, lintegral_const, one_mul, Measure.restrict_apply,
          MeasurableSet.univ, Set.univ_inter]
        exact (measure_mono fun y hy => Or.inr hy.2).trans h1)
    simpa using h
  have tail : ∀ R : ℝ, Real.exp 1 ≤ R →
      maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤
        ENNReal.ofReal (K * Real.log R / R) := by
    intro R hRe
    refine (measure_mono (t := bdry s ∪ ((bdry s)ᶜ ∩ {y | R ≤ rW L s y})) ?_).trans
      ((measure_union_le _ _).trans ?_)
    · rintro y (hy | hy)
      · exact Or.inl hy
      · by_cases hb : y ∈ bdry s
        · exact Or.inl hb
        · exact Or.inr ⟨hb, hy⟩
    · rw [maMeasure_bdry_eq_zero A L s m W hS hSNC, zero_add]
      exact tail1 R hRe
  refine ⟨⟨?_⟩, K, fun R hRe => ⟨tail R hRe, ?_⟩⟩
  · refine lt_of_le_of_lt ((measure_mono fun y _ => Or.inr (hge y)).trans (tail _ le_rfl))
      ENNReal.ofReal_lt_top
  · refine tail_lintegral_le_of_eventually A L s hL hS
      (fun i => th i + LocPot.ofFun (ph i) + Θ) (fun t i => th i + LocPot.ofFun (phT i t) + Θ)
      hc hpot hunif (fun y => Real.log (rW L s y)) hrm.log ?_
      R _ ?_ ?_
    · exact hrc.log fun y hy => ((Real.exp_pos 1).trans_le (hge y)).ne'
    · intro y _ _
      exact Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (hge y))
    · filter_upwards [hbd] with t ht
      exact ((hT (fun _ => t) fun _ => ht).2 R hRe).2

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyUniformBound
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.AnalyticLimit

theorem tailLogBound_of_φ_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Yo : Set X) (r : X → ℝ) {Φ Ψ : Fin e → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ) (CE : ℝ)
    (H : TailLogBound A Yo r Φ CE) : TailLogBound A Yo r Ψ CE := by
  have hd : ∀ j y, ReciprocityTheory.AnForm.M.locDens A Φ j y = ReciprocityTheory.AnForm.M.locDens A Ψ j y := by
    intro j y
    simp only [ReciprocityTheory.AnForm.M.locDens, h]
  have hM : ∀ g, ReciprocityTheory.AnForm.M.MIntegrable A Φ g ↔ ReciprocityTheory.AnForm.M.MIntegrable A Ψ g := by
    intro g
    simp only [ReciprocityTheory.AnForm.M.MIntegrable, hd]
  have hI : ∀ g, ReciprocityTheory.AnForm.M.mInt A Φ g = ReciprocityTheory.AnForm.M.mInt A Ψ g := by
    intro g
    simp only [ReciprocityTheory.AnForm.M.mInt, ReciprocityTheory.AnForm.M.integralWith, hd]
  intro R₀ hR
  rw [← hM, ← hI]
  exact H R₀ hR

theorem tailLogProducts : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → ∀ (P : Fin e → LocPot X) (C : ℝ), (∀ i, IsPotential A (P i)) → ∃ CE : ℝ, ∀ f : Fin e → X → ℝ, (∀ i, A.Smooth (f i)) → (∀ i, IsPsh A (P i + LocPot.ofFun (f i))) → (∀ i, ∀ x ∈ R.Yo, |f i x| ≤ C + C * Real.log (R.r x)) → (∀ i, ∀ x ∈ R.Yo, f i x ≤ C) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => P i + LocPot.ofFun (f i)) CE := by
  intro e X _ _ _ A R Θ hΘ hΘp P C hP
  have hSmooth : ListTailLogSmooth.Statement :=
    ListTailLogSmooth.proof
      (GroundTheory.Heights₂.Heights.ForSecondHalf.ListTailLog.of_lemmaETailMass lemmaETailMass)
  let R₁ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.RegChartData.ofRegular R Θ hΘ hΘp
  let R' := regChartShift R₁
  have hconst : A.Smooth (fun _ : X => C) := fun j => contDiffOn_const
  let th : Fin e → LocPot X := fun i => P i + LocPot.ofFun (fun _ => C)
  have hth : ∀ i, IsPotential A (th i) := fun i =>
    isPotentialAdd A _ _ (hP i) (isPotential_ofFun A _ hconst)
  obtain ⟨Om, hOm⟩ := BoundingKaehler.full e A ⟨Θ, hΘ, hΘp⟩ e th hth
  obtain ⟨CE, hCE⟩ := hSmooth A R' Om (3 * |C|)
  refine ⟨CE, fun f hf hpsh habs hle => ?_⟩
  let u : Fin e → X → ℝ := fun i x => f i x - C
  have hu : ∀ i, A.Smooth (u i) := fun i j => (hf i j).sub contDiffOn_const
  have hφ : ∀ i, (potForm (th i) (u i)).φ = (P i + LocPot.ofFun (f i)).φ := by
    intro i
    funext x y
    show (P i).φ x y + C + (f i y - C) = (P i).φ x y + f i y
    ring
  have hnn : ∀ i, FormNonneg A R.Yo (P i + LocPot.ofFun (f i)) := fun i x k y hy w =>
    hpsh i x k y ⟨hy.1, hy.2.2⟩ w
  have hform : ∀ i, IsSmoothPotForm A R'.Yo R'.r Om (3 * |C|) (th i) (u i) := by
    intro i
    refine ⟨⟨hth i, (hOm i).1, (hOm i).2, ?_, ?_, ?_, ?_, Or.inl (hu i)⟩, hu i⟩
    · exact fun j => (hu i j).mono fun y hy => ⟨hy.1, trivial⟩
    · intro x hx
      have := hle i x hx
      show f i x - C ≤ 0
      linarith
    · intro x hx
      have hx' : x ∈ R.Yo := hx
      have h1 : 1 ≤ R.r x := R.one_le_r x hx'
      have he : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have hL : Real.log (R.r x) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
        Real.log_le_log (by linarith) (by linarith)
      have hL1 : 1 ≤ Real.log (R.r x + (Real.exp 1 - 1)) := by
        have h2 : Real.log (Real.exp 1) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
          Real.log_le_log (Real.exp_pos 1) (by linarith)
        rwa [Real.log_exp] at h2
      have hL0 := Real.log_nonneg h1
      have hf' : -(C + C * Real.log (R.r x)) ≤ f i x := by
        have := (neg_abs_le (f i x))
        linarith [habs i x hx']
      have hc1 : C * Real.log (R.r x) ≤ |C| * Real.log (R.r x + (Real.exp 1 - 1)) :=
        mul_le_mul (le_abs_self C) hL hL0 (abs_nonneg C)
      have hc2 : |C| ≤ |C| * Real.log (R.r x + (Real.exp 1 - 1)) :=
        le_mul_of_one_le_right (abs_nonneg _) hL1
      have hc3 := le_abs_self C
      show -(3 * |C| * Real.log (R.r x + (Real.exp 1 - 1))) ≤ f i x - C
      linarith
    · intro x k y hy w
      have := hnn i x k y ⟨hy.1, hy.2.1, hy.2.2.1⟩ w
      rw [hφ i]
      exact this
  have hB := hCE th u hform
  have hpot : ∀ i, IsPotential A (P i + LocPot.ofFun (f i)) := fun i =>
    isPotentialAdd A _ _ (hP i) (isPotential_ofFun A _ (hf i))
  have hB' : TailLogBound A R.Yo R'.r (fun i => P i + LocPot.ofFun (f i)) CE :=
    tailLogBound_of_φ_eq A _ _ hφ CE hB
  exact tailLogBound_of_le (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.isOpen_Yo_regular R)
    (regChartData_continuousOn_r R₁) (r' := R'.r)
    (fun x _ => by
      show R.r x ≤ R.r x + (Real.exp 1 - 1)
      linarith [Real.add_one_le_exp (1 : ℝ)])
    hpot hnn hB'

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralRegularizedConvergenceStatement
section
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_integral_regularized_convergence : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (G : X → ℝ) (GT : ℝ → X → ℝ) (C CE : ℝ), IsPotential A Θ → (∀ i, IsPotential A (th i)) → (∀ i, A.SmoothOn R.Yo (ph i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, A.Smooth (phT i t)) ∧ (∀ i, IsPsh A (th i + LocPot.ofFun (phT i t) + Θ)) ∧ GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => th i + LocPot.ofFun (phT i t) + Θ) CE) → (∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT i t ∘ (A.chart j).symm))) (fderiv ℝ (fderiv ℝ (ph i ∘ (A.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable X ℝ (borel X) _ (R.Yo.indicator (GT t)) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → ∀ (j : Fin A.n) (S : Set (Fin e → ℂ)) (c : X → ℝ), S ⊆ (A.chart j).target → IsCompact S → @Measurable X ℝ (borel X) _ c → (∀ x, 0 ≤ c x ∧ c x ≤ 1) → (∀ y ∈ (A.chart j).target, y ∉ S → c ((A.chart j).symm y) = 0) → IntegrableOn (fun y => c ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y) (A.chart j).target ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IntegrableOn (fun y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (A.chart j).target) ∧ Tendsto (fun t => ∫ y in (A.chart j).target, c ((A.chart j).symm y) * GT t ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (𝓝[>] 0) (𝓝 (∫ y in (A.chart j).target, c ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.conv_chart_integral | exact GlobalTheory.CompanionTheory.Ar.Giv.conv_chart_integral | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.conv_chart_integral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelMonomialWeightProductStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_monomial_weight_product : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (Φ : Type) [Field Φ] (y : K₀ ⊕ StepIx Ψ p q → Φ), (∀ k, y k ≠ 0) → ∀ (τ : Ψ) (i : Fin (p + q)), (∀ h1 : (i : ℕ) < p, ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (((i : ℕ) + 1) * m (.inl τ)) / y (.inr ⟨.inl τ, ⟨i, h1⟩⟩)) ∧ (∀ h1 : p ≤ (i : ℕ), ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (p * m (.inl τ) + ((i : ℕ) - p + 1) * m (.inr τ)) / ((if h0 : 0 < p then y (.inr ⟨.inl τ, ⟨p - 1, by show _ < p; omega⟩⟩) else 1) * y (.inr ⟨.inr τ, ⟨(i : ℕ) - p, by have := i.2; show _ < q; omega⟩⟩))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial.step_monomial | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial.step_monomial | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial.step_monomial <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereRegularizationLogLogBoundStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_regularization_log_log_bound : ConvergenceRateStatement → ∀ (e : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ), 0 < S.t₀ → ∃ C' t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ S.t₀ ∧ ∀ t t', 0 < t' → t' ≤ t → t ≤ t₁ → ∀ (a : σ) (w : Fin e → σ) (c : Fin e → Bool), |mInt S.A (fun i => S.potT (w i) (if c i then t else t')) (fun x => S.phT a t x - S.phT a t' x)| ≤ C' * Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.signed_rate | exact GlobalTheory.CompanionTheory.Ar.PB.signed_rate | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.signed_rate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NzEqNzOfAndPosStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nz_eq_nzOf_and_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) (r : ℕ) (y : Fin r → Λ), IsCMFam σ → IsIsoSub R.form I → (∀ a, y a ∈ I) → LinearIndependent (𝓞 E) y → (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 → R.nz σ I = R.nzOf σ I y ∧ 0 < R.nz σ I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.NzCase.nz_eq_nzOf_of_family | exact GlobalTheory.CompanionTheory.Ar.Cusp.NzCase.nz_eq_nzOf_of_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.NzCase.nz_eq_nzOf_of_family <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Slots
variable {X : Type} [TopologicalSpace X] {e : ℕ}

def positionPot (th Pn : LocPot X) (f : X → ℝ) (i : ℕ) : Fin e → LocPot X :=
  fun j => (if (j : ℕ) < i then th else Pn) + LocPot.ofFun (if (j : ℕ) < i then f else fun _ => 0)

end Slots

section Lines
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W}

def muVert (Hd : HodgeData D) (B : ℕ) : HermLine J :=
  hermOfFun J (muTwDeg Hd B) fun z => (muLine Hd).h z * ∏ p ∈ D.SB B, D.vertFactor p z

def limTop (Hd : HodgeData D) (B : ℕ) (Nb : HermLine J) : ℝ :=
  II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) -
    ∑ i ∈ Finset.range (D.n + 1), ptsIntegral (mCoordIdeal D.y)
      (pot fun j : Fin D.n => if (j : ℕ) < i then muVert Hd B else Nb)
      (fun z => Real.log (Nb.h z) - Real.log ((muVert Hd B).h z))

end Lines
end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProdXbPowEqXcOfPowStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_xb_pow_eq_xcOf_pow : ∀ {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type}
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (r : Ψ × Fin (p + q)),
    ∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k' =
      xcOf x₀ c ^ (rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1)) *
        (if p ≤ (r.2 : ℕ) + 1 then (zOf A c (.inl r.1))⁻¹ else 1) *
        (if (r.2 : ℕ) + 1 = p + q then (zOf A c (.inr r.1))⁻¹ else 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.prod_xb_zpow_bF | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.prod_xb_zpow_bF | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.prod_xb_zpow_bF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetricStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_function_as_degree_zero_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D) (u : R.X → ℝ), R.A.Smooth u → ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ x, Real.log (B.h (R.lift x x)) = u x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth | exact GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionLocalChartPolynomial
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem proj_diag_ne_zero_iff (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    SncRes.proj z ⟨k, (i, i)⟩ ≠ 0 ↔ z ⟨k, i⟩ ≠ 0 := by
  simp only [SncRes.proj]
  constructor
  · intro h h0
    apply h
    simp [h0]
  · intro h
    have hn : (0 : ℝ) < ‖z ⟨k, i⟩‖ := norm_pos_iff.2 h
    have hpos : (0 : ℝ) < ∑ j, ‖z ⟨k, j⟩‖ ^ 2 := by
      refine lt_of_lt_of_le (pow_pos hn 2) ?_
      exact Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have hden : ((∑ j, ‖z ⟨k, j⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact div_ne_zero (mul_ne_zero h ((map_ne_zero _).2 h)) hden

theorem isOpen_alt_bis (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    IsOpen (SncRes.src P p) := by
  have h : SncRes.src P p = ⋂ k, {x : SncRes.Pts P | x.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
    ext x
    simp only [SncRes.src, Set.mem_setOf_eq, Set.mem_iInter]
    refine forall_congr' fun k => ?_
    rw [← SncRes.proj_rep x]
    exact (proj_diag_ne_zero_iff _ k (p k)).symm
  rw [h]
  refine isOpen_iInter_of_finite fun k => ?_
  have hc : Continuous fun x : SncRes.Pts P => x.1 ⟨k, (p k, p k)⟩ :=
    (continuous_apply _).comp continuous_subtype_val
  exact isOpen_ne_fun hc continuous_const

theorem chart_coord_ratio : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ p' : (k : K) → ι k, (∀ k, eval (SncRes.coord P p x) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O, (∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ∧ eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q ≠ 0 ∧ ∀ l, SncRes.coord P p y l * eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q = eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) (F l) := by
  intro K _ ι _ P _ p x hx p' hp'
  classical
  have key : ∀ y ∈ SncRes.src P p,
      ((∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ↔ y ∈ SncRes.src P p') := by
    intro y hy
    simp only [SncRes.eval_lift p y hy, ReciprocityTheory.AnForm.R.affCoord]
    constructor
    · intro h k h0
      exact h k (by simp [h0])
    · intro h k
      exact div_ne_zero (h k) (hy k)
  refine ⟨SncRes.src P p ∩ SncRes.src P p', (isOpen_alt_bis P p).inter (isOpen_alt_bis P p'),
    ⟨hx, (key x hx).1 hp'⟩, Set.inter_subset_left, ∏ k, X ⟨k, p k⟩,
    fun l => X ((Fintype.equivFin (Σ k, ι k)).symm l) *
      ∏ k ∈ Finset.univ.erase ((Fintype.equivFin (Σ k, ι k)).symm l).1, X ⟨k, p k⟩, ?_⟩
  rintro y ⟨hy, hy'⟩
  have hw : (fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) =
      ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) := funext (SncRes.eval_lift p y hy)
  simp only [hw]
  have hone : ∀ k, ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p k⟩ = 1 := fun k => by
    simp [ReciprocityTheory.AnForm.R.affCoord, hy k]
  have hne : ∀ k, ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p' k⟩ ≠ 0 := fun k =>
    div_ne_zero (hy' k) (hy k)
  have ha : ∀ k, ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩ ≠ 0 := by
    intro k
    have : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩ =
        1 / ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p' k⟩ := by
      rw [← hone k]; rfl
    rw [this]
    exact div_ne_zero one_ne_zero (hne k)
  refine ⟨(key y hy).2 hy', ?_, fun l => ?_⟩
  · rw [map_prod]
    simp only [eval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => ha k
  · set q := (Fintype.equivFin (Σ k, ι k)).symm l with hq
    have hcoord : SncRes.coord P p y l = ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) q := rfl
    rw [map_mul, map_prod, map_prod, hcoord]
    simp only [eval_X]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k => ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩)
      (Finset.mem_univ q.1), ← mul_assoc]
    congr 1
    have h1 : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨q.1, p q.1⟩ =
        1 / ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨q.1, p' q.1⟩ := by
      rw [← hone q.1]; rfl
    have h2 : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) q =
        ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) q /
          ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨q.1, p' q.1⟩ := rfl
    rw [h1, h2, mul_one_div]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TMatBlockDiagDetFactorsStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tMat_blockDiag_det_factors : ∀ {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω]
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ),
    IsBlockDiag p (tMat Ts τ) ∧ (tMat Ts τ).det = (Ts (.inr τ)).det * (Ts (.inl τ)).det ∧
      ∀ i : Fin (p + q), detFac p i (tMat Ts τ) =
        (if p ≤ (i : ℕ) + 1 then (Ts (.inl τ)).det else 1) * (if (i : ℕ) + 1 = p + q then (Ts (.inr τ)).det else 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.tMat_main | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.tMat_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.tMat_main <;> assumption)
end

