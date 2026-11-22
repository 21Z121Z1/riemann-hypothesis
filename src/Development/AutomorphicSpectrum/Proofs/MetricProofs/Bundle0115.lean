import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0107
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedMeasureConvergenceSnc
import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0108
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0106
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0109
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0032
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0099
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0110
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinimalPrimesOfMultihomogSupStatement
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_primes_of_multihomog_sup : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), IsMultiHomogIdeal P → IsMultiHomogIdeal D → ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup | exact GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedMeasureConvergenceSncStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_measure_convergence_snc : GroundTheory.Heights₂.Heights.AnalyticLimit.UniformIntegrability.Statement → TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas (e + 1) X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X), IsPotential A L' → IsSection A L' v → IsSNC A L' v ![1] ![Dg] → IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg) → ∀ (th : Fin (e + 1) → LocPot X) (ph : Fin (e + 1) → X → ℝ) (phT : Fin (e + 1) → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → ∀ η : ℝ, 0 < η → ∃ ε₀ t₁ : ℝ, 0 < ε₀ ∧ 0 < t₁ ∧ ∀ ε t : ℝ, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ → Integrable (GroundTheory.Heights₂.Heights.AnalyticLimit.greenEp L' v ε) (maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)) ∧ ∫ y, GroundTheory.Heights₂.Heights.AnalyticLimit.greenEp L' v ε y ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.green_small_uniform | exact GlobalTheory.CompanionTheory.Ar.Giv.green_small_uniform | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.green_small_uniform <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NefOnFibresAddNonnegStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_on_fibres_add_nonneg : PB.Inputs → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (a a' : K → ℤ) (p q : ℕ), NefOnFibres P a → (∀ k, 0 ≤ a' k) → NefOnFibres P ((q : ℤ) • a + (p : ℤ) • a') := by
  first | exact @GlobalTheory.CompanionTheory.Relay.nef_on_fibres_add_nonneg | exact GlobalTheory.CompanionTheory.Relay.nef_on_fibres_add_nonneg | (intros; apply GlobalTheory.CompanionTheory.Relay.nef_on_fibres_add_nonneg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NefPolarizationStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_polarization : NefPol := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.nefPol | exact GlobalTheory.CompanionTheory.Ar.PB.nefPol | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.nefPol <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.packing' : PackingStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.packing | exact GlobalTheory.CompanionTheory.Ar.Small.packing | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.packing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibilityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_hermitian_type_compatibility : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ty P → Hm.IsHermitian → (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) → (∀ j k, ty j ≠ ty k → Hm j k = 0) ∧ (∀ (τ : E →+* ℂ) x y, hermForm Hm (tyPart ty τ (P x)) (tyPart ty τ (P y)) - star (hermForm Hm (tyPart ty (ComplexEmbedding.conjugate τ) (P x)) (tyPart ty (ComplexEmbedding.conjugate τ) (P y))) = 2 * Complex.I * τ (sesq D x y)) ∧ ∀ (r : ℕ) (I : Type) [Fintype I] [DecidableEq I] (e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → (Matrix.of fun m n => sesq D (e m) (e n)).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component | exact GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetric
section
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

section FactorChange

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem snoc_update_comp_swap {D : ℕ} (W : Fin D → HermLine ι) (m : Fin D) (X B : HermLine ι) :
    (Fin.snoc (Function.update W m X) B : Fin (D + 1) → HermLine ι) ∘
        Equiv.swap m.castSucc (Fin.last D) =
      Fin.snoc (Function.update W m B) X := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Function.comp_apply, Equiv.swap_apply_right, Fin.snoc_castSucc, Function.update_self, Fin.snoc_last]
  · by_cases hi : i = m
    · subst hi
      rw [Function.comp_apply, Equiv.swap_apply_left, Fin.snoc_last, Fin.snoc_castSucc, Function.update_self]
    · have h1 : i.castSucc ≠ m.castSucc := fun h => hi (Fin.castSucc_injective _ h)
      have h2 : i.castSucc ≠ Fin.last D := (Fin.castSucc_lt_last i).ne
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.snoc_castSucc, Fin.snoc_castSucc,
        Function.update_of_ne hi, Function.update_of_ne hi]

theorem smooth_update {D : ℕ} {W : Fin D → HermLine ι} (hW : ∀ j, IsSmoothHerm (W j)) (m : Fin D)
    {X : HermLine ι} (hX : IsSmoothHerm X) (j : Fin D) : IsSmoothHerm (Function.update W m X j) := by
  by_cases hj : j = m
  · subst hj
    simpa using hX
  · simpa [Function.update_of_ne hj] using hW j

theorem smooth_snoc {D : ℕ} {W : Fin D → HermLine ι} (hW : ∀ j, IsSmoothHerm (W j)) {X : HermLine ι}
    (hX : IsSmoothHerm X) (j : Fin (D + 1)) :
    IsSmoothHerm ((Fin.snoc W X : Fin (D + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    exact hX
  · rw [Fin.snoc_castSucc]
    exact hW i

theorem position_change (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) {D : ℕ} (hP : IsArithVar P (D + 1))
    (W : Fin D → HermLine ι) (hW : ∀ j, IsSmoothHerm (W j)) (m : Fin D) (A A' B : HermLine ι)
    (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (hB : IsSmoothHerm B) (hab : A'.a = A.a)
    (hloc : ∀ z ∈ mcPts P, ∃ c : ℝ, B.h =ᶠ[𝓝 z] fun _ => c) :
    I P (D + 1) (Fin.snoc (Function.update W m A) B) =
      I P (D + 1) (Fin.snoc (Function.update W m A') B) := by
  have hM := smooth_update hW m hB
  have hswap : ∀ X : HermLine ι, IsSmoothHerm X →
      I P (D + 1) (Fin.snoc (Function.update W m X) B) = I P (D + 1) (Fin.snoc (Function.update W m B) X) := by
    intro X hX
    rw [← snoc_update_comp_swap W m X B]
    exact (hI.1 P (D + 1) _ _ hP (smooth_snoc (smooth_update hW m hX) hB)).symm
  rw [hswap A hA, hswap A' hA',
    GlobalTheory.CompanionTheory.Ar.Tele.step GroundTheory.Heights₂.Heights.ForSecondHalf.MetricLocal.full I hI P D _ A A' hP hM hA hA' hab,
    GlobalTheory.T.points_integral_zero_of_locally_constant K ι P D (pot (Function.update W m B)) _ m ?_, sub_zero]
  intro z hz
  obtain ⟨c, hc⟩ := hloc z hz
  refine ⟨Real.log c, ?_⟩
  filter_upwards [hc] with x hx
  simp [pot, hx]

theorem word_change (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) {D : ℕ} (hP : IsArithVar P (D + 1))
    (L L' : Fin D → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (hL' : ∀ j, IsSmoothHerm (L' j))
    (ha : ∀ j, (L j).a = (L' j).a) (B : HermLine ι) (hB : IsSmoothHerm B)
    (hloc : ∀ z ∈ mcPts P, ∃ c : ℝ, B.h =ᶠ[𝓝 z] fun _ => c) :
    I P (D + 1) (Fin.snoc L B) = I P (D + 1) (Fin.snoc L' B) := by
  let Wd : ℕ → Fin D → HermLine ι := fun m j => if (j : ℕ) < m then L' j else L j
  have hWd : ∀ m j, IsSmoothHerm (Wd m j) := by
    intro m j
    by_cases h : (j : ℕ) < m
    · simpa [Wd, h] using hL' j
    · simpa [Wd, h] using hL j
  have key : ∀ m, m ≤ D → I P (D + 1) (Fin.snoc L B) = I P (D + 1) (Fin.snoc (Wd m) B) := by
    intro m
    induction m with
    | zero =>
      intro _
      have : Wd 0 = L := by
        funext j
        simp [Wd]
      rw [this]
    | succ m ih =>
      intro hm
      let i : Fin D := ⟨m, hm⟩
      have e0 : Function.update (Wd m) i (L i) = Wd m := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [Wd, i]
        · simp [Function.update_of_ne hj]
      have e1 : Function.update (Wd m) i (L' i) = Wd (m + 1) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [Wd, i]
        · have hne : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
          have hiff : (j : ℕ) < m + 1 ↔ (j : ℕ) < m := by omega
          simp [Function.update_of_ne hj, Wd, hiff]
      rw [ih (by omega), ← e1]
      conv_lhs => rw [← e0]
      exact position_change I hI P hP (Wd m) (hWd m) i (L i) (L' i) B (hL i) (hL' i) hB (ha i).symm hloc
  have hD : Wd D = L' := by
    funext j
    simp [Wd]
  rw [key D le_rfl, hD]

end FactorChange

theorem mass_eq_of_degrees : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L L' : Fin D → HermLine ι) (sg : F →+* ℂ), IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, (L j).a = (L' j).a) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L') ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hA hInt K _ ι _ Ω _ F _ _ _ y D L L' sg hP hL hL' ha hex
  classical
  obtain ⟨II, hII, -⟩ := hA
  let Λ : (F →+* ℂ) → ℝ := fun s => if s = sg then Real.exp 1 else 1
  have hΛ : ∀ s, 0 < Λ s := by
    intro s
    by_cases h : s = sg
    · simp [Λ, h, Real.exp_pos]
    · simp [Λ, h]
  obtain ⟨B, hB0, hBs, hBloc⟩ :=
    exists_smooth_weight_const_near_embeddings K ι Ω F y Λ hΛ hex
  have mass : ∀ M : Fin D → HermLine ι, (∀ j, IsSmoothHerm (M j)) →
      II K ι (mCoordIdeal y) (D + 1) (Fin.snoc M B) =
        ptsIntegral (mCoordIdeal y) (pot M) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
    intro M hM
    rw [intersection_locConst_trivial hInt K ι Ω F y D M B Λ II hII hP hM hB0 hBs hex hBloc,
      Finset.sum_eq_single sg]
    · simp [Λ]
    · intro s _ hs
      simp [Λ, hs]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  rw [← mass L hL, ← mass L' hL']
  refine word_change (II K ι) (hII K ι) _ hP L L' hL hL' ha B hBs ?_
  intro z hz
  obtain ⟨s, hs, -⟩ := hex z hz
  exact ⟨Λ s, hBloc z hz s hs⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshDoublePositivePotentialStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psh_double_positive_potential : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → IsPsh A (Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularSystemOfParametersLocalRingAltBis
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_system_of_parameters_local_ring_alt : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∀ i ∈ Jf, (SncRes.Par.chPrime I t (r i)).IsPrime ∧ I ≤ SncRes.Par.chPrime I t (r i) ∧ SncRes.Par.chPrime I t (r i) ≤ ptIdeal t ∧ Dc ≤ SncRes.Par.chPrime I t (r i) ∧ r i ∈ SncRes.Par.chPrime I t (r i) ∧ (∀ j ∈ Jf, j ≠ i → r j ∉ SncRes.Par.chPrime I t (r i)) ∧ ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → r i ∈ 𝔮 → SncRes.Par.chPrime I t (r i) ≤ 𝔮 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularSystemOfParametersLocalRingStatement
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_radical_locally_eq_span_prod : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ h : MvPolynomial (Fin m) ℂ, eval t h ≠ 0 ∧ h * ∏ l ∈ Jf, r l ∈ Dc.radical ∧ ∀ g ∈ Dc.radical, h * g ∈ Ideal.span {∏ l ∈ Jf, r l} ⊔ I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params | exact GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricFormulaStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_hodge_metric_formula : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ), ∀ z ∈ mcPts (mCoordIdeal D.y), (muReg X.H X.S B t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBoundsStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_weight_psh_and_bounds : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B) (Θ : LocPot M.Xc), S.IsTied → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → ReciprocityTheory.AnForm.P.IsPshOn M.atlas S.R.Yo (S.R.th + LocPot.ofFun S.R.ph) ∧ (∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧ ∀ x ∈ S.R.Yo, S.R.ph x ≤ S.regWeight t x ∧ S.regWeight t x ≤ C) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsPsh M.atlas (S.R.th + LocPot.ofFun (S.regWeight t) + Θ.rsmul ε) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tied_regularisation_weak | exact GlobalTheory.CompanionTheory.Ar.Giv.tied_regularisation_weak | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tied_regularisation_weak <;> assumption)
end

