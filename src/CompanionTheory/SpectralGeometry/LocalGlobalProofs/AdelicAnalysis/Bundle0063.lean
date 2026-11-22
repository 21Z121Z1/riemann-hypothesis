import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0039
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
import GroundTheory.GlobalFields.LocalAtPlace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCount
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0061
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummable

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardLocalHaarProperties
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Vol

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isCompact_integers : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
  isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)

theorem isOpen_integers : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_valuationSubring _

def mulAdd (c : Fv F v) (hc : c ≠ 0) : Fv F v ≃+ Fv F v where
  toFun t := c * t
  invFun t := c⁻¹ * t
  left_inv t := by simp [hc]
  right_inv t := by simp [hc]
  map_add' := mul_add c

theorem mulAdd_continuous (c : Fv F v) (hc : c ≠ 0) : Continuous (mulAdd v c hc) :=
  continuous_const.mul continuous_id

theorem mulAdd_symm_continuous (c : Fv F v) (hc : c ≠ 0) : Continuous (mulAdd v c hc).symm :=
  continuous_const.mul continuous_id

theorem vol_lt_one (lam : Measure (Fv F v)) (h : IsStdV v lam) :
    lam {t | Valued.v t < 1} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have key := GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v (Fv F v) lam Unit
    (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm {0}
  have e1 : {x : Fv F v | ∃ y : Unit → v.adicCompletionIntegers F,
      (∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm x i = (y i : Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈
        ({0} : Set (Unit → IsLocalRing.ResidueField (v.adicCompletionIntegers F)))} =
      {t | Valued.v t < 1} := by
    ext x
    simp only [Set.mem_setOf_eq, ← GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff v x]
    constructor
    · rintro ⟨y, h1, h2⟩
      exact ⟨y (), h1 (), congrFun h2 ()⟩
    · rintro ⟨y, h1, h2⟩
      exact ⟨fun _ => y, fun _ => h1, funext fun _ => h2⟩
  have e2 : {x : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm x i ∈
      v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext x
    simp
  rw [e1, e2, GroundTheory.Global.natCard_residueField_adicCompletionIntegers v] at key
  simp only [Fintype.card_unit, pow_one, Set.ncard_singleton, Nat.cast_one, one_mul] at key
  have hO : lam.real (v.adicCompletionIntegers F : Set (Fv F v)) = 1 := by
    simp [measureReal_def, h.2]
  rw [hO] at key
  have hfin : lam {t | Valued.v t < 1} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := lam (v.adicCompletionIntegers F : Set (Fv F v))) ?_ ?_
    · rw [h.2]; exact ENNReal.one_ne_top
    · exact measure_mono fun t (ht : Valued.v t < 1) => (le_of_lt ht : Valued.v t ≤ 1)
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  refine (ENNReal.toReal_eq_one_iff _).1 ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  exact key

theorem absNorm_ne_zero : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast this

theorem map_unit (lam : Measure (Fv F v)) (h : IsStdV v lam) (u : Fv F v) (hu : Valued.v u = 1) :
    lam.map (fun t => u * t) = lam := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨_, hl, hs, ht, _⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  refine (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open (Fv F v) (Fv F v) lam lam (mulAdd v u hu0) (mulAdd_continuous v u hu0)
    (mulAdd_symm_continuous v u hu0)).2 (v.adicCompletionIntegers F : Set (Fv F v))
    (v.adicCompletionIntegers F : Set (Fv F v)) (isCompact_integers v) (isOpen_integers v)
    ⟨0, zero_mem _⟩ (fun x => ?_) rfl
  change Valued.v (u * x) ≤ 1 ↔ Valued.v x ≤ 1
  rw [map_mul, hu, one_mul]

theorem exp_neg_one_mul_lt_one_iff (a : WithZero (Multiplicative ℤ)) :
    WithZero.exp (-1 : ℤ) * a < 1 ↔ a ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [← WithZero.exp_log ha, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp,
      WithZero.exp_le_exp]
    omega

theorem map_unif (lam : Measure (Fv F v)) (h : IsStdV v lam) (π : Fv F v)
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    lam.map (fun t => π * t) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨_, hl, hs, ht, _⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hq0 := absNorm_ne_zero v
  have hqt : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  haveI : ((Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul lam hq0 hqt
  refine (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open (Fv F v) (Fv F v) lam ((Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam)
    (mulAdd v π hπ0) (mulAdd_continuous v π hπ0) (mulAdd_symm_continuous v π hπ0)).2
    (v.adicCompletionIntegers F : Set (Fv F v)) {t | Valued.v t < 1} (isCompact_integers v)
    (isOpen_integers v) ⟨0, zero_mem _⟩ (fun x => ?_) ?_
  · change Valued.v (π * x) < 1 ↔ Valued.v x ≤ 1
    rw [map_mul, hπ]
    exact exp_neg_one_mul_lt_one_iff _
  · rw [h.2, Measure.smul_apply, vol_lt_one v lam h, smul_eq_mul, ENNReal.mul_inv_cancel hq0 hqt]

theorem volumes_in_completion : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → lam {t | Valued.v t < 1} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ∧ (∀ π : Fv F v, Valued.v π = WithZero.exp (-1 : ℤ) → lam.map (fun t => π * t) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam) ∧ (∀ u : Fv F v, Valued.v u = 1 → lam.map (fun t => u * t) = lam) ∧ Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal :=
  fun F _ _ v lam h => ⟨vol_lt_one v lam h, map_unif v lam h, map_unit v lam h,
    GroundTheory.Global.natCard_residueField_adicCompletionIntegers v⟩

end GlobalTheory.CompanionTheory.SW.Vol
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCountStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_theta_average_le_of_countData : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ κ t : ℝ, 0 < κ → 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) → (∀ v w, κ * (τ w).im ≤ (τ v).im) → (∀ x, Measurable fun ω => thTerm B ρ P (gf ω) (gi ω) φ τ x) ∧ ENNReal.ofReal (wt M τ) * ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr ≤ ENNReal.ofReal C := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.ThetaBound.theta_integral_bound | exact GlobalTheory.CompanionTheory.SW.Core.ThetaBound.theta_integral_bound | (intros; apply GlobalTheory.CompanionTheory.SW.Core.ThetaBound.theta_integral_bound <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureIntegralFormulaStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_integral_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → ∫⁻ Y, Φ Y ∂(thetaMeas σ J μ 𝓕 S) = (μ 𝓕)⁻¹ * cntI σ J μ 𝓕 S Φ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaCnt.lintegral_thetaMeas | exact GlobalTheory.CompanionTheory.SW.ThetaCnt.lintegral_thetaMeas | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaCnt.lintegral_thetaMeas <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummableStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_summable : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (∀ φ : (ι → A F) → ℂ, SB φ → Summable fun x => ‖thTerm B ρ P gf gi φ τ x‖) ∧ ∃ φ : (ι → A F) → ℂ, SB φ ∧ theta B ρ P gf gi φ τ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaSum.theta_summable_and_ne_zero | exact GlobalTheory.CompanionTheory.SW.ThetaSum.theta_summable_and_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaSum.theta_summable_and_ne_zero <;> assumption)
end

