import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0001
import Formalism.GelfandTransference.HadamardGelfand.Highest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0443
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0560
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0562
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0564
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundByRecursion
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.DensityIter

theorem bounded_density_of_iterated
    (H ι : Type) [MeasurableSpace H] (ν : Measure H) (D : Set H → ℝ≥0∞) (Dtot : ℝ≥0∞)
    (hDtot : Dtot ≠ ⊤) (hD : ∀ Y, MeasurableSet Y → D Y ≤ Dtot)
    (I : Finset ι) (α β : ι → ℝ≥0) (C₀ : ℝ≥0)
    (hit : ∀ Y, MeasurableSet Y → ∃ Z : ι → Set H,
      (∀ i ∈ I, MeasurableSet (Z i) ∧ ν (Z i) = β i * ν Y) ∧
        D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i))
    (hρ : ∑ i ∈ I, α i * β i < 1) (hr : ∑ i ∈ I, α i < 1) :
    ∃ C : ℝ≥0, ∀ Y, MeasurableSet Y → D Y ≤ C * ν Y := by
  set ρ : ℝ≥0 := ∑ i ∈ I, α i * β i with hρdef
  set r : ℝ≥0 := ∑ i ∈ I, α i with hrdef
  set K : ℝ≥0 := C₀ / (1 - ρ) with hK
  have hKeq : C₀ + K * ρ = K := by
    have h1 : K * (1 - ρ) = C₀ := div_mul_cancel₀ C₀ (tsub_pos_of_lt hρ).ne'
    calc C₀ + K * ρ = K * (1 - ρ) + K * ρ := by rw [h1]
      _ = K * (1 - ρ + ρ) := by rw [mul_add]
      _ = K := by rw [tsub_add_cancel_of_le hρ.le, mul_one]
  have hKeq' : (C₀ : ℝ≥0∞) + K * ρ = K := by exact_mod_cast hKeq
  have hρc : (ρ : ℝ≥0∞) = ∑ i ∈ I, (α i : ℝ≥0∞) * β i := by
    simp only [hρdef, ENNReal.coe_finset_sum, ENNReal.coe_mul]
  have hrc : (r : ℝ≥0∞) = ∑ i ∈ I, (α i : ℝ≥0∞) := by
    simp only [hrdef, ENNReal.coe_finset_sum]
  have key : ∀ n : ℕ, ∀ Y, MeasurableSet Y → D Y ≤ K * ν Y + (r : ℝ≥0∞) ^ n * Dtot := by
    intro n
    induction n with
    | zero =>
      intro Y hY
      rw [pow_zero, one_mul]
      exact le_add_left (hD Y hY)
    | succ n ih =>
      intro Y hY
      obtain ⟨Z, hZ, hDY⟩ := hit Y hY
      have e1 : ∑ i ∈ I, (α i : ℝ≥0∞) * (K * ((β i : ℝ≥0∞) * ν Y)) = K * ρ * ν Y := by
        rw [hρc, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ i ∈ I, (α i : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n * Dtot) = (r : ℝ≥0∞) ^ (n + 1) * Dtot := by
        rw [← Finset.sum_mul, ← hrc]
        ring
      calc D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i) := hDY
        _ ≤ C₀ * ν Y + ∑ i ∈ I, (α i : ℝ≥0∞) * (K * ((β i : ℝ≥0∞) * ν Y) + (r : ℝ≥0∞) ^ n * Dtot) := by
          gcongr with i hi
          rw [← (hZ i hi).2]
          exact ih _ (hZ i hi).1
        _ = C₀ * ν Y + (K * ρ * ν Y + (r : ℝ≥0∞) ^ (n + 1) * Dtot) := by
          simp only [mul_add, Finset.sum_add_distrib, e1, e2]
        _ = K * ν Y + (r : ℝ≥0∞) ^ (n + 1) * Dtot := by
          rw [← add_assoc, ← add_mul, hKeq']
  refine ⟨K, fun Y hY => ?_⟩
  have hr1 : (r : ℝ≥0∞) < 1 := by exact_mod_cast hr
  have ht : Filter.Tendsto (fun n : ℕ => (K : ℝ≥0∞) * ν Y + (r : ℝ≥0∞) ^ n * Dtot) Filter.atTop
      (nhds ((K : ℝ≥0∞) * ν Y + 0 * Dtot)) :=
    tendsto_const_nhds.add
      (ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1) (Or.inr hDtot))
  rw [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht fun n => key n Y hY

end GlobalTheory.CompanionTheory.DensityIter
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityChartIntegralFormula
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem onePiece {Y : Type} {D : ℕ} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (m : Measure Y) (e : OpenPartialHomeomorph Y (Fin D → ℂ)) (r : (Fin D → ℂ) → ℝ)
    (hr : ContinuousOn r e.target)
    (hm : m.restrict e.source = ((volume.restrict e.target).withDensity fun v =>
      ENNReal.ofReal (r v)).map e.symm)
    (S : Set Y) (hS : MeasurableSet S) (hSs : S ⊆ e.source) (K : Y → ℝ)
    (hK : IntegrableOn K S m) :
    Integrable ((e '' S).indicator fun v => K (e.symm v) * max (r v) 0) ∧
      ∫ y in S, K y ∂m = ∫ v, (e '' S).indicator (fun v => K (e.symm v) * max (r v) 0) v := by
  classical
  set ν0 : Measure (Fin D → ℂ) := volume.restrict e.target with hν0
  set d : (Fin D → ℂ) → ENNReal := fun v => ENNReal.ofReal (r v) with hd
  have htm : MeasurableSet e.target := e.open_target.measurableSet
  have hsm : MeasurableSet e.source := e.open_source.measurableSet
  have hdm : AEMeasurable d ν0 :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hr.aemeasurable htm)
  have hdlt : ∀ᵐ v ∂ν0, d v < ⊤ := Filter.Eventually.of_forall fun v => ENNReal.ofReal_lt_top
  have hsy0 : AEMeasurable e.symm ν0 := e.continuousOn_symm.aemeasurable htm
  have hsy : AEMeasurable e.symm (ν0.withDensity d) :=
    hsy0.mono_ac (withDensity_absolutelyContinuous _ _)
  set K' : Y → ℝ := S.indicator K with hK'
  have hK1 : Integrable K' m := (integrable_indicator_iff hS).2 hK
  have hK2 : Integrable K' ((ν0.withDensity d).map e.symm) := by
    rw [← hm]; exact hK1.restrict
  have hK3 : Integrable (K' ∘ e.symm) (ν0.withDensity d) :=
    (integrable_map_measure hK2.aestronglyMeasurable hsy).1 hK2
  have hK4 : Integrable (fun v => (d v).toReal • (K' ∘ e.symm) v) ν0 :=
    (integrable_withDensity_iff_integrable_smul₀' hdm hdlt).1 hK3
  have hfun : (e '' S).indicator (fun v => K (e.symm v) * max (r v) 0) =
      e.target.indicator (fun v => (d v).toReal • (K' ∘ e.symm) v) := by
    funext v
    by_cases hv : v ∈ e '' S
    · obtain ⟨y, hy, rfl⟩ := hv
      have hyt : e y ∈ e.target := e.map_source (hSs hy)
      have hinv : e.symm (e y) = y := e.left_inv (hSs hy)
      rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hy), Set.indicator_of_mem hyt]
      simp [hinv, hK', hy, hd, ENNReal.toReal_ofReal', mul_comm]
    · rw [Set.indicator_of_notMem hv]
      by_cases hvt : v ∈ e.target
      · have hns : e.symm v ∉ S := fun h => hv ⟨_, h, e.right_inv hvt⟩
        rw [Set.indicator_of_mem hvt]; simp [hK', hns]
      · rw [Set.indicator_of_notMem hvt]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (integrable_indicator_iff htm).2 hK4
  · rw [hfun, integral_indicator htm]
    calc ∫ y in S, K y ∂m = ∫ y, K' y ∂m := (integral_indicator hS).symm
      _ = ∫ y in e.source, K' y ∂m := by
          refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
          intro y hy
          exact Set.indicator_of_notMem (fun h => hy (hSs h)) _
      _ = ∫ y, K' y ∂((ν0.withDensity d).map e.symm) := by rw [hm]
      _ = ∫ v, (K' ∘ e.symm) v ∂(ν0.withDensity d) :=
          integral_map hsy hK2.aestronglyMeasurable
      _ = ∫ v, (d v).toReal • (K' ∘ e.symm) v ∂ν0 :=
          integral_withDensity_eq_integral_toReal_smul₀ hdm hdlt _

theorem exists_partition {Y ι : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [Countable ι] (U : ι → Set Y) (hU : ∀ l, IsOpen (U l)) (G : Set Y) (hG : MeasurableSet G)
    (hGs : G ⊆ ⋃ l, U l) :
    ∃ S : ι → Set Y, (∀ l, MeasurableSet (S l)) ∧ (∀ l, S l ⊆ U l) ∧
      Pairwise (Function.onFun Disjoint S) ∧ ⋃ l, S l = G := by
  classical
  haveI := Encodable.ofCountable ι
  refine ⟨fun l => (G ∩ U l) \ ⋃ (k : ι) (_ : Encodable.encode k < Encodable.encode l), U k,
    fun l => ?_, fun l y hy => hy.1.2, ?_, ?_⟩
  · exact (hG.inter (hU l).measurableSet).diff
      (isOpen_iUnion fun k => isOpen_iUnion fun _ => hU k).measurableSet
  · have key : ∀ l k : ι, Encodable.encode k < Encodable.encode l →
        Disjoint ((G ∩ U k) \ ⋃ (j : ι) (_ : Encodable.encode j < Encodable.encode k), U j)
          ((G ∩ U l) \ ⋃ (j : ι) (_ : Encodable.encode j < Encodable.encode l), U j) := by
      intro l k hlt
      refine Set.disjoint_left.2 fun y hyk hyl => hyl.2 ?_
      exact Set.mem_iUnion₂.2 ⟨k, hlt, hyk.1.2⟩
    intro l k hne
    rcases lt_trichotomy (Encodable.encode l) (Encodable.encode k) with h | h | h
    · exact key k l h
    · exact absurd (Encodable.encode_injective h) hne
    · exact (key l k h).symm
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun l y hy => hy.1.1
    · intro y hy
      have hex : ∃ n, ∃ l : ι, Encodable.encode l = n ∧ y ∈ U l := by
        obtain ⟨l, hl⟩ := Set.mem_iUnion.1 (hGs hy)
        exact ⟨_, l, rfl, hl⟩
      obtain ⟨l, hl, hyl⟩ := Nat.find_spec hex
      refine Set.mem_iUnion.2 ⟨l, ⟨hy, hyl⟩, fun hmem => ?_⟩
      obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 hmem
      exact Nat.find_min hex (hl ▸ hk) ⟨k, rfl, hyk⟩

theorem abs_eq_max_add_max (a : ℝ) : |a| = max a 0 + max (-a) 0 := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring

theorem integral_pieces : ∀ {Y ι : Type} {D : ℕ} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Countable ι]
    (μ : ℤˣ → Measure Y) (e : ι → OpenPartialHomeomorph Y (Fin D → ℂ)) (ρ : ι → (Fin D → ℂ) → ℝ),
    (∀ l, ContinuousOn (ρ l) (e l).target) →
    (∀ l (ε : ℤˣ), (μ ε).restrict (e l).source = ((volume.restrict (e l).target).withDensity fun v =>
      ENNReal.ofReal (((ε : ℤ) : ℝ) * ρ l v)).map (e l).symm) →
    ∀ (G : Set Y), MeasurableSet G → G ⊆ ⋃ l, (e l).source → ∀ F : Y → ℝ, (∀ ε, IntegrableOn F G (μ ε)) →
    ∃ S : ι → Set Y, (∀ l, MeasurableSet (S l)) ∧ (∀ l, S l ⊆ (e l).source) ∧ Pairwise (Function.onFun Disjoint S) ∧
      ⋃ l, S l = G ∧ ∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1) =
        ∫ v, ∑' l, ((e l) '' S l).indicator (fun v => F ((e l).symm v) * ρ l v) v := by
  intro Y ι D _ _ _ _ μ e ρ hρ hμ G hG hGs F hF
  obtain ⟨S, hSm, hSs, hSd, hSu⟩ := exists_partition (fun l => (e l).source)
    (fun l => (e l).open_source) G hG hGs
  refine ⟨S, hSm, hSs, hSd, hSu, ?_⟩
  have hSG : ∀ l, S l ⊆ G := fun l => hSu ▸ Set.subset_iUnion S l
  have piece : ∀ (l : ι) (ε : ℤˣ) (K : Y → ℝ), IntegrableOn K (S l) (μ ε) →
      Integrable ((e l '' S l).indicator fun v => K ((e l).symm v) * max (((ε : ℤ) : ℝ) * ρ l v) 0) ∧
      ∫ y in S l, K y ∂μ ε =
        ∫ v, (e l '' S l).indicator (fun v => K ((e l).symm v) * max (((ε : ℤ) : ℝ) * ρ l v) 0) v :=
    fun l ε K hK => onePiece (μ ε) (e l) (fun v => ((ε : ℤ) : ℝ) * ρ l v)
      (continuousOn_const.mul (hρ l)) (hμ l ε) (S l) (hSm l) (hSs l) K hK
  set Φ : ι → (Fin D → ℂ) → ℝ := fun l =>
    (e l '' S l).indicator (fun v => F ((e l).symm v) * ρ l v) with hΦ
  have hΦsub : ∀ l, Φ l =
      (e l '' S l).indicator (fun v => F ((e l).symm v) * max ((((1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) -
      (e l '' S l).indicator (fun v => F ((e l).symm v) * max ((((-1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) := by
    intro l
    funext v
    by_cases hv : v ∈ e l '' S l
    · simp only [hΦ, Pi.sub_apply, Set.indicator_of_mem hv]
      have h := max_zero_sub_max_neg_zero_eq_self (ρ l v)
      simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
      rw [← mul_sub, h]
    · simp [hΦ, Set.indicator_of_notMem hv]
  have hΦnorm : ∀ l v, ‖Φ l v‖ =
      (e l '' S l).indicator (fun v => ‖F ((e l).symm v)‖ * max ((((1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) v +
      (e l '' S l).indicator (fun v => ‖F ((e l).symm v)‖ * max ((((-1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) v := by
    intro l v
    by_cases hv : v ∈ e l '' S l
    · simp only [hΦ, Set.indicator_of_mem hv]
      simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
      rw [norm_mul, ← mul_add, Real.norm_eq_abs (ρ l v), abs_eq_max_add_max]
    · simp [hΦ, Set.indicator_of_notMem hv]
  have hFS : ∀ l ε, IntegrableOn F (S l) (μ ε) := fun l ε => (hF ε).mono_set (hSG l)
  have hFnS : ∀ l ε, IntegrableOn (fun y => ‖F y‖) (S l) (μ ε) := fun l ε => (hFS l ε).norm
  have hΦint : ∀ l, Integrable (Φ l) := by
    intro l
    rw [hΦsub l]
    exact (piece l 1 F (hFS l 1)).1.sub (piece l (-1) F (hFS l (-1))).1
  have hΦval : ∀ l, ∫ v, Φ l v = ∫ y in S l, F y ∂μ 1 - ∫ y in S l, F y ∂μ (-1) := by
    intro l
    rw [hΦsub l, (piece l 1 F (hFS l 1)).2, (piece l (-1) F (hFS l (-1))).2]
    exact integral_sub (piece l 1 F (hFS l 1)).1 (piece l (-1) F (hFS l (-1))).1
  have hΦnval : ∀ l, ∫ v, ‖Φ l v‖ =
      ∫ y in S l, ‖F y‖ ∂μ 1 + ∫ y in S l, ‖F y‖ ∂μ (-1) := by
    intro l
    simp only [hΦnorm l]
    rw [(piece l 1 _ (hFnS l 1)).2, (piece l (-1) _ (hFnS l (-1))).2]
    exact integral_add (piece l 1 _ (hFnS l 1)).1 (piece l (-1) _ (hFnS l (-1))).1
  have hU : ∀ ε, IntegrableOn F (⋃ l, S l) (μ ε) := fun ε => by rw [hSu]; exact hF ε
  have hsumN : ∀ ε, Summable fun l => ∫ y in S l, ‖F y‖ ∂μ ε := fun ε =>
    (hasSum_integral_iUnion hSm hSd (hU ε).norm).summable
  have h1 : HasSum (fun l => ∫ v, Φ l v) (∫ v, ∑' l, Φ l v) :=
    hasSum_integral_of_summable_integral_norm hΦint
      (by simp only [hΦnval]; exact (hsumN 1).add (hsumN (-1)))
  have h2 : HasSum (fun l => ∫ y in S l, F y ∂μ 1 - ∫ y in S l, F y ∂μ (-1))
      (∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1)) := by
    have a := hasSum_integral_iUnion hSm hSd (hU 1)
    have b := hasSum_integral_iUnion hSm hSd (hU (-1))
    rw [hSu] at a b
    exact a.sub b
  simp only [hΦval] at h1
  exact h2.unique h1

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.UnitaryContraction

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_zpow (x : Lˣ) (k : ℤ) : ordL ((x ^ k : Lˣ) : L) = k * ordL (x : L) := by
  have h0 : Valued.v (x : L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 h0
  have hk : Valued.v ((x ^ k : Lˣ) : L) = ((a ^ k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, WithZero.coe_zpow]
  rw [UnitaryCorrection.ordL_of_eq hk, UnitaryCorrection.ordL_of_eq ha.symm, toAdd_zpow]
  simp

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem diagT_mem_iwGL (w : Pl E) (n : ℕ) (s : Fin n → (w.adicCompletion E)ˣ)
    (hs : ∀ i, Valued.v (s i : w.adicCompletion E) = 1) :
    GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s ∈ iwGL n w := by
  have hle : ∀ t : Fin n → (w.adicCompletion E)ˣ, (∀ i, Valued.v (t i : w.adicCompletion E) = 1) →
      ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) t).val i j) ≤ 1 := by
    intro t ht i j
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, ht]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]
      exact zero_le_one
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1]
  refine ⟨hle s hs, ?_, ?_⟩
  · rw [← map_inv]
    refine hle _ fun i => ?_
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hs, inv_one]
  · intro i j hij
    rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]
    exact zero_lt_one

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, fU n w b ϖ l γ ≠ 0 → ∃ m ∈ iwU n w b, ∃ u : Fin n → (w.adicCompletion E)ˣ, (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (m⁻¹ * γ * m).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl hyp γ hγ
  obtain ⟨-, hcc, hcv, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨hW1, hW2, -, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  obtain ⟨hanti, hrev⟩ := GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl
  have hγ' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b,
      γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := by
    by_contra h
    exact hγ (if_neg h)
  obtain ⟨x, hx, z, hz, e⟩ := hγ'
  obtain ⟨δ, hδ⟩ : ∃ δ : GLw n w, δ = b⁻¹ * γ.1 * b := ⟨_, rfl⟩
  have hγδ : γ.1 = b * δ * b⁻¹ := by rw [hδ]; group
  have hδd : dcos n w (tdiag ϖ (wexp n l)) δ ≠ 0 := by
    have h : ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, δ = x * tdiag ϖ (wexp n l) * z :=
      ⟨_, (hW2 x).1 hx, _, (hW2 z).1 hz, by rw [hδ, e]; group⟩
    simp only [dcos, if_pos h]
    exact one_ne_zero
  have hδU : δ ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) :=
    (hW1 δ).1 (by rw [← hγδ]; exact γ.2)
  obtain ⟨m0, hm0, τ, ⟨hτ0, hτ1⟩, hmτ⟩ := hyp (wexp n l) hanti δ hδd
  have hne : ∀ i, τ.val i i ≠ 0 := fun i h => by
    have := hτ1 i
    rw [h, map_zero] at this
    exact zero_ne_one this
  obtain ⟨v, hv⟩ : ∃ v : Fin n → (w.adicCompletion E)ˣ, ∀ i, (v i : w.adicCompletion E) = τ.val i i :=
    ⟨fun i => Units.mk0 _ (hne i), fun i => rfl⟩
  have hτv : τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) v := by
    apply Units.ext
    rw [GlobalTheory.SmGL.val_diagT]
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, hv]
    · rw [Matrix.diagonal_apply_ne _ h, hτ0 i j h]
  obtain ⟨u, hu⟩ : ∃ u : Fin n → (w.adicCompletion E)ˣ, u = fun i => ϖ ^ wexp n l i * v i := ⟨_, rfl⟩
  have htu : tdiag ϖ (wexp n l) * τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by
    rw [hτv, hu, tdiag, ← map_mul]
    rfl
  have hord : ∀ i, ordL (u i : w.adicCompletion E) = wexp n l i := by
    intro i
    rw [hu]
    simp only [Units.val_mul]
    rw [UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _), ordL_zpow, hϖ.1,
      UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hv, hτ1, map_one]),
      UnitaryCorrection.ordL_one]
    simp
  have hm0e := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n m0).1.1 hm0
  have hδe : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * m0⁻¹ = δ := by
    rw [← htu, ← hmτ]
    group
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.CompanionTheory.UnitaryCorrection.main (w.adicCompletion E) (cj w) hcc hcv
    (GlobalTheory.T.norm_one_unit_hilbert_ninety E hU w hw) n (wexp n l) hanti.injective hrev u hord m0 hm0e.1 hm0e.2.1
    (by rw [hδe]; exact hδU)
  have hm1 : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s ∈ iwGL n w :=
    mul_mem hm0 (diagT_mem_iwGL w n s hs1)
  have hcomm : (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s)⁻¹ *
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp [mul_comm]
  refine ⟨⟨b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹, (hW1 _).2 hs2⟩,
    (hW2 _).2 ?_, u, hord, ?_⟩
  · have : b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b =
        m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s := by group
    change b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b ∈ iwGL n w
    rw [this]
    exact hm1
  · change (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹)⁻¹ * γ.1 *
      (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) = _
    rw [hγδ]
    have hd : m0⁻¹ * δ * m0 = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by rw [hmτ, htu]
    calc _ = b * ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s)⁻¹ * (m0⁻¹ * δ * m0) *
          GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹ := by group
      _ = _ := by rw [hd, hcomm]

end GlobalTheory.CompanionTheory.UnitaryContraction
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableCoeffRowAct
section
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem differentiable_entry {r : ℕ} (a b : Fin r) :
    Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => M a b :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)).differentiable

theorem differentiable_det {r : ℕ} :
    Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => M.det := by
  simp only [Matrix.det_apply']
  refine Differentiable.fun_sum fun σ _ => Differentiable.const_mul ?_ _
  have h : ∀ t : Finset (Fin r), Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => ∏ i ∈ t, M (σ i) i := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (differentiable_entry (σ a) a).mul ih
  exact h Finset.univ

theorem differentiable_coeff_rowAct {r m : ℕ} (f : MvPolynomial (Fin r × Fin m) ℂ) :
    ∀ s : (Fin r × Fin m) →₀ ℕ, Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ =>
      MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro s
    simpa [MvPolynomial.algebraMap_eq] using
      (differentiable_const (MvPolynomial.coeff s (MvPolynomial.C a : MvPolynomial (Fin r × Fin m) ℂ)) :
        Differentiable ℂ fun _ : Matrix (Fin r) (Fin r) ℂ => _)
  | add p q hp hq =>
    intro s
    simp only [map_add, MvPolynomial.coeff_add]
    exact (hp s).add (hq s)
  | mul_X p v hp =>
    intro s
    have key : ∀ M : Matrix (Fin r) (Fin r) ℂ,
        MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ (p * MvPolynomial.X v)) =
        ∑ b : Fin r, M b v.1 * (if (b, v.2) ∈ s.support then
          MvPolynomial.coeff (s - Finsupp.single (b, v.2) 1) (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ p) else 0) := by
      intro M
      have hX : Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ (MvPolynomial.X v) =
          ∑ b : Fin r, MvPolynomial.C (M b v.1) * MvPolynomial.X (b, v.2) := by
        simp [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      rw [map_mul, hX, Finset.mul_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']
    simp only [key]
    refine Differentiable.fun_sum fun b _ => ?_
    refine (differentiable_entry b v.1).mul ?_
    split_ifs
    · exact hp _
    · exact differentiable_const _

theorem detPow_nonsingInvUnit {n : ℕ} {x : Mat n} (h : IsUnit x.det) (c : ℤ) :
    Formalism.BasicNotions.detPow ℂ n (Matrix.nonsingInvUnit x h) c = x.det ^ c := by
  have e : ((Matrix.GeneralLinearGroup.det (Matrix.nonsingInvUnit x h) : ℂˣ) : ℂ) = x.det := rfl
  rw [Formalism.BasicNotions.detPow, Units.val_zpow_eq_zpow_val, e]

theorem holRm (n : ℕ) (lam : Fin n → ℤ) : HolRm lam := by
  intro i j g hg
  obtain ⟨S, c, hc⟩ := GlobalTheory.CompanionTheory.WInfCont.exists_finset_factor (Formalism.BasicNotions.nablaSq ℂ n (dw lam)) ((wb lam).coord i)
  have hev : (fun x : Mat n => Rm lam x i j) =ᶠ[𝓝 g] fun x : Mat n =>
      ∑ s : S, c s * (x.det ^ (dw lam).detShift *
        MvPolynomial.coeff s.1 (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) xᵀ (wb lam j).1)) := by
    filter_upwards [isOpen_GLs.mem_nhds hg] with x hx
    have hu := isUnit_det_of_mem hx
    rw [Rm_of_unit lam hu, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, hc]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [GlobalTheory.Branching.sqRep_coe, Formalism.BasicNotions.sqAct, MvPolynomial.coeff_smul, smul_eq_mul,
      detPow_nonsingInvUnit hu]
    rfl
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  refine DifferentiableAt.fun_sum fun s _ => DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.mul ?_ (differentiable_coeff_rowAct _ _ _)
  exact (differentiable_det g).zpow (Or.inl hg)

end GlobalTheory.CompanionTheory.RmHol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHermitianIntegralUnfoldingStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_hermitian_integral_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (r s : ℕ) (μr : Measure (Mx D V.rank r))
    (𝓕r : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μr 𝓕r →
    ∀ (c : Matrix (Fin r) (Fin (r + s)) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsCompl c a →
    ∀ (b : HermE D r) (Φ : Mx D V.rank (r + s) → ℂ),
      ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr = J ψ V μr (pull c Φ) b := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J | exact GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCompactBoundStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_volume_compact_bound : ∀ (V K : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ P : Set V, IsCompact P → IsOpen P → P ⊆ Z → ∃ c : ℝ≥0, ∀ S : Set K, MeasurableSet S → μ (P ∩ Q ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound.compactOpen_mass_le | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound.compactOpen_mass_le | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound.compactOpen_mass_le <;> assumption)
end

