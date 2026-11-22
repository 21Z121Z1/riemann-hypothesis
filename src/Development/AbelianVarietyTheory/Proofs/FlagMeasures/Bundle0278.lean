import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0274
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialWedgeDecompositionDiscreteSeriesLargeGaps
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0011
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0002
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionInjectiveParameters
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0241
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0271
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightsOfExtension

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentIntegralDiscreteSeriesVanishStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realUnipotent_integral_discreteSeries_vanish : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  first | exact @GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf | exact GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf | (intros; apply GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeConst

theorem gauge_exists_pos_unique :
    ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ IsGauge ε c ∧ ∀ c', IsGauge ε c' → c' = c :=
  GlobalTheory.GaugeConst.exists_unique_isGauge

end GlobalTheory.GaugeConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeWholeGroup
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeWhole

private theorem pos_of_isGauge' {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  by_contra hc
  push_neg at hc
  have hle : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc ENNReal.toReal_nonneg)
      (pow_nonneg (le_of_lt hr) _)
  have := le_of_tendsto h' hle
  linarith

theorem isGaugeSub_univ {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) :
    0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε) := by
  have hc := pos_of_isGauge' h
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨hc, ?_⟩
  unfold IsGaugeSub
  refine ⟨by simp, fun s _ => ?_, ?_⟩
  · rw [Measure.map_smul, map_mul_left_eq_self]
  · rw [← ENNReal.ofReal_toReal hfin]
    refine (ENNReal.tendsto_ofReal h').congr' ?_
    filter_upwards [h'.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    have hμ : Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
      intro htop
      rw [htop] at hr
      simp at hr
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos (pow_pos hr0' _),
      ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal hμ]

theorem gauge_whole : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ c : ℝ, IsGauge ε c → 0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε)) ∧ ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ (Set.univ : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := by
  intro n ε
  refine ⟨fun c hc => isGaugeSub_univ hc, ?_⟩
  obtain ⟨E, hE, horth, hexp⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  refine ⟨⊤, E, fun _ _ _ _ => Submodule.mem_top, horth, fun X => ?_, ?_⟩
  · constructor
    · rintro ⟨-, hX⟩
      rw [hexp X hX]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hs : ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • E i = (((X * (E i)ᴴ).trace).re : ℝ) • E i := by
        ext a b
        simp [Complex.real_smul]
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro hX
      refine ⟨Submodule.mem_top, ?_⟩
      have hle : Submodule.span ℝ (Set.range E) ≤ GlobalTheory.GaugeConst.lieJ ε := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact GlobalTheory.GaugeConst.mem_lieJ.mpr (hE i).1
      exact GlobalTheory.GaugeConst.mem_lieJ.mp (hle hX)
  · ext g
    simp

end GlobalTheory.GaugeWhole
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOnGroupOfSpecialStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_on_group_of_special : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, f (z • g) = z ^ m * f' g) → SmoothS ε f' → SmoothOnG ε f := by
  first | exact @GlobalTheory.SmoothCentral.smooth_of_central | exact GlobalTheory.SmoothCentral.smooth_of_central | (intros; apply GlobalTheory.SmoothCentral.smooth_of_central <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtensionStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_integrable_iff_extension : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → IsURepOn (UJset ε) π → (IsSqIntOn ε π ↔ IsSqIntS ε π') := by
  first | exact @GlobalTheory.SqIntSU.sqInt_iff | exact GlobalTheory.SqIntSU.sqInt_iff | (intros; apply GlobalTheory.SqIntSU.sqInt_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFreeDerivCongrOnUnitaryGroup
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.DSSU.Local

variable {n : ℕ}

theorem trace_traceFreeMatrixUnit_eq_zero (a b : Fin n) : (E0 a b).trace = 0 := by
  have hn : (n : ℂ) ≠ 0 := by
    have : 0 < n := Fin.pos a
    exact_mod_cast this.ne'
  unfold E0
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  by_cases h : a = b
  · subst h
    simp [hn]
  · simp [h, Matrix.trace_single_eq_of_ne _ _ _ h]

theorem trace_theta (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.trace = 0) :
    (Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε).trace = 0 := by
  rw [Matrix.trace_mul_cycle, Formalism.REAL.Jm_mul_self, Matrix.one_mul, Matrix.trace_conjTranspose, hZ, star_zero]

theorem trace_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.trace = 0) :
    (cpart1 ε Z).trace = 0 := by
  unfold cpart1
  rw [Matrix.trace_smul, Matrix.trace_sub, trace_theta ε Z hZ, hZ, sub_zero, smul_zero]

theorem trace_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.trace = 0) :
    (cpart2 ε Z).trace = 0 := by
  unfold cpart2
  rw [Matrix.trace_smul, Matrix.trace_add, trace_theta ε Z hZ, hZ, add_zero, smul_zero]

theorem mul_exp_mem (ε : Fin n → Bool) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (h0 : X.trace = 0)
    (hg : g ∈ SUset ε) (t : ℝ) : g * NormedSpace.exp ((t : ℂ) • X) ∈ SUset ε := by
  refine ⟨indefinite_unitary_mul_mem ε hg.1 (exp_indefinite_unitary_holds n ε X hX t), ?_⟩
  rw [Matrix.det_mul, hg.2, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, h0, smul_zero, Complex.exp_zero, one_mul]

theorem rd_congr (ε : Fin n → Bool) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (h0 : X.trace = 0)
    {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g ∈ SUset ε, G₁ g = G₂ g) (hg : g ∈ SUset ε) :
    Rd X G₁ g = Rd X G₂ g := by
  unfold Rd
  congr 1
  funext t
  exact h _ (mul_exp_mem ε hX h0 hg t)

theorem matrix_unit_action_congr : ∀ (n : ℕ) (ε : Fin n → Bool) (G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ) (a b : Fin n),
    (∀ g ∈ SUset ε, G₁ g = G₂ g) → ∀ g ∈ SUset ε, Ec ε (E0 a b) G₁ g = Ec ε (E0 a b) G₂ g := by
  intro n ε G₁ G₂ a b h g hg
  obtain ⟨h1, h2, -⟩ := complex_parts_mem_lie_algebra_holds n ε (E0 a b)
  unfold Ec
  rw [rd_congr ε h1 (trace_cpart1 ε _ (trace_traceFreeMatrixUnit_eq_zero a b)) h hg, rd_congr ε h2 (trace_cpart2 ε _ (trace_traceFreeMatrixUnit_eq_zero a b)) h hg]

end GlobalTheory.DSSU.Local
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialWedgeDecompositionDiscreteSeriesLargeGapsStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivialWedgeDecomposition_discreteSeries_largeGaps : BranchingSupport.HypsG → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (F F' : (Fin (2 * r + k + 1) → ℤ) → BranchingSupport.Rep k r) (ν : Fin (2 * r + k + 1) → ℤ), BranchingSupport.Num k r lam u b bv ga h q0 → BranchingSupport.IsFamG lam q0 F → BranchingSupport.IsFamG lam q0 F' → BranchingSupport.n1 ν + 2 ≤ q0 → ∃ io pr ep, BranchingSupport.TensH (BranchingSupport.cmp 0) (BranchingSupport.cmp 0 (Formalism.QuantumDeterminants.Hpk k r)) (F ν) (fun I : BranchingSupport.Sub (2 * r + k + 1) 0 => F' (ν + BranchingSupport.eZ I.1)) io pr ep := by
  first | exact @GlobalTheory.TrivWedge.tensH_trivial | exact GlobalTheory.TrivWedge.tensH_trivial | (intros; apply GlobalTheory.TrivWedge.tensH_trivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoLeRootDiscriminantAndSplitArithmeticCondition
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem two_le_rdE_and_arithmeticConditionsS0 : ∀ D : D7, 2 ≤ D.host.rdE ∧ ArithmeticConditionsOfDatum D := fun D =>
  ⟨S.root_discriminant_ge_two _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _),
    fun u => S.splitsCompl_of_ncard _ _ (D.mem u).A.T_prime
      (Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.split_clause _ Formalism.L2.SG.ResidEvFree.cycSplit_holds _ (D.mem u).A.T_prime (S.level_norm_one_mod_conductor _ u)).2,
    Formalism.L2.SG.ResidEvFree.splitsE_g _ 0, Formalism.L2.SG.ResidEvFree.splitsE_g _ 1, S.discriminant_eq_base_sq _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupUJHaarRightInvariant
section
open MeasureTheory

noncomputable section

open scoped ENNReal NNReal

namespace GlobalTheory.UJUnimod

variable {n : ℕ}

def Bd (a : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) : Prop := ∀ i j, ‖a i j‖ ≤ R

theorem Bd.mul {a b : Matrix (Fin n) (Fin n) ℂ} {R R' : ℝ} (ha : Bd a R) (hb : Bd b R') :
    Bd (a * b) ((n : ℝ) * (R * R')) := by
  intro i j
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ (Finset.univ : Finset (Fin n)), ‖a i l * b l j‖ ≤ R * R' := fun l _ => by
    rw [norm_mul]
    exact mul_le_mul (ha i l) (hb l j) (norm_nonneg _) ((norm_nonneg _).trans (ha i l))
  simpa using Finset.sum_le_card_nsmul _ _ _ this

theorem bd_pow {g : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} (hg : (g - 1) ^ m = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, Bd (g ^ j) (B * ((j : ℝ) + 1) ^ (m + 1)) := by
  set X := g - 1 with hX
  have e : g = X + 1 := by simp [hX]
  refine ⟨∑ l ∈ Finset.range m, ∑ i, ∑ j, ‖(X ^ l) i j‖, by positivity, fun p i j => ?_⟩
  set B := ∑ l ∈ Finset.range m, ∑ i, ∑ j, ‖(X ^ l) i j‖ with hB
  have hB0 : 0 ≤ B := by positivity
  rw [e, (Commute.one_right X).add_pow, Matrix.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ Finset.range (p + 1), ‖(X ^ l * 1 ^ (p - l) * (p.choose l : Matrix (Fin n) (Fin n) ℂ)) i j‖ ≤
      B * ((p : ℝ) + 1) ^ m := fun l _ => by
    by_cases hl : l < m
    · have h1 : ‖(X ^ l) i j‖ ≤ B :=
        ((Finset.single_le_sum (f := fun j => ‖(X ^ l) i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i => ∑ j, ‖(X ^ l) i j‖) (fun _ _ => by positivity)
            (Finset.mem_univ i))).trans
          (Finset.single_le_sum (f := fun l => ∑ i, ∑ j, ‖(X ^ l) i j‖) (fun _ _ => by positivity)
            (Finset.mem_range.2 hl))
      have h2 : (p.choose l : ℝ) ≤ ((p : ℝ) + 1) ^ m := by
        have h3 : (p.choose l : ℝ) ≤ (p : ℝ) ^ l := by exact_mod_cast Nat.choose_le_pow p l
        have h4 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        exact h3.trans ((pow_le_pow_left₀ h4 (by linarith) l).trans (pow_le_pow_right₀ (by linarith) hl.le))
      rw [one_pow, mul_one, ← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul, norm_mul, Complex.norm_natCast,
        mul_comm]
      exact mul_le_mul h1 h2 (Nat.cast_nonneg _) hB0
    · rw [pow_eq_zero_of_le (not_lt.1 hl) hg]
      simp only [zero_mul, Matrix.zero_apply, norm_zero]
      positivity
  refine (Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)
  simp only [Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.UJUnimod

namespace GlobalTheory.UJUnimod

theorem unimodular_of_unipotent : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ) (S : Subgroup (Formalism.REAL.UJ ε)),
    IsClosed (S : Set (Formalism.REAL.UJ ε)) → (∀ g ∈ S, (Formalism.MainNotions.S.uMat g - 1) ^ m = 0) →
    ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ →
    ∀ s ∈ S, μ.map (fun x => x * s) = μ := by
  intro n ε m S hS hu μ hμ
  obtain ⟨hσ, h0, hc, hl⟩ := hμ
  have hce : Topology.IsClosedEmbedding S.subtype := hS.isClosedEmbedding_subtypeVal
  have hφ : MeasurableEmbedding S.subtype := hce.measurableEmbedding
  haveI : LocallyCompactSpace S := hce.locallyCompactSpace
  haveI : SecondCountableTopology S := hce.isEmbedding.secondCountableTopology
  have h2 : (μ.comap S.subtype).map S.subtype = μ := by
    rw [hφ.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : Set.range S.subtype = (S : Set (Formalism.REAL.UJ ε)) := Subtype.range_coe
    rw [this]
    exact hc
  set ν : Measure S := μ.comap S.subtype with hν
  haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : Formalism.REAL.UJ ε => (g : Formalism.REAL.UJ ε) * x := measurable_const_mul _
    rw [Measure.map_map hφ.measurable (measurable_const_mul g), h2]
    conv_rhs => rw [← hl g g.2, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsHaarMeasure :=
    GlobalTheory.SnMass.ProdQuot.isHaarMeasure_of_sigmaFinite ν fun h => h0 (by rw [← h2, h, Measure.map_zero])
  have hfin : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [← h2, hφ.map_apply]
    exact (hce.isCompact_preimage hK).measure_lt_top⟩

  have hmod : ∀ s : S, μ.map (fun x => x * (s : Formalism.REAL.UJ ε)) =
      (Measure.modularCharacter s : ℝ≥0∞) • μ := by
    intro s
    have e1 : ν.map (· * s) = (Measure.modularCharacter s : ℝ≥0∞) • ν := by
      rw [show (Measure.modularCharacter s : ℝ≥0) = Measure.modularCharacterFun s from rfl,
        Measure.modularCharacterFun_eq_haarScalarFactor ν s]
      exact Measure.isMulLeftInvariant_eq_smul _ ν
    conv_lhs => rw [← h2]
    rw [Measure.map_map (measurable_mul_const _) hφ.measurable]
    have : (fun x : Formalism.REAL.UJ ε => x * (s : Formalism.REAL.UJ ε)) ∘ S.subtype = S.subtype ∘ (· * s) := by
      funext x; rfl
    rw [this, ← Measure.map_map hφ.measurable (measurable_mul_const _), e1, Measure.map_smul, h2]

  have key : ∀ s : S, Measure.modularCharacter s ≤ 1 := by
    intro s
    set Δ := Measure.modularCharacter s with hΔ
    obtain ⟨C, D, hgr⟩ := GlobalTheory.T.unitaryJ_haar_entryBounded_polynomial_growth ε S hS μ ⟨hσ, h0, hc, hl⟩ hfin
    obtain ⟨B, hB, hpow⟩ := bd_pow (hu _ (S.inv_mem s.2))
    let Bx : ℝ → Set (Formalism.REAL.UJ ε) := fun R => {g | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R}
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, μ (Bx ((ρ : ℝ) + 1)) ≠ 0 := by
      by_contra! h
      apply h0
      rw [← Measure.measure_univ_eq_zero]
      have : (Set.univ : Set (Formalism.REAL.UJ ε)) = ⋃ ρ : ℕ, Bx ((ρ : ℝ) + 1) := by
        ext g
        simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
        obtain ⟨N, hN⟩ := exists_nat_ge (∑ i, ∑ j, ‖Formalism.MainNotions.S.uMat g i j‖)
        refine ⟨N, fun i j => ?_⟩
        have := (Finset.single_le_sum (f := fun j => ‖Formalism.MainNotions.S.uMat g i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖Formalism.MainNotions.S.uMat g i j‖)
          (fun _ _ => by positivity) (Finset.mem_univ i))
        linarith
      rw [this]
      exact measure_iUnion_null h
    set ρ' : ℝ := (ρ : ℝ) + 1 with hρ'
    have hρ1 : 1 ≤ ρ' := by rw [hρ']; linarith [Nat.cast_nonneg (α := ℝ) ρ]
    obtain ⟨C', hC', hgr'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ R : ℝ, 1 ≤ R → (μ (Bx R)).toReal ≤ C' * R ^ D ∧ μ (Bx R) < ⊤ := by
      refine ⟨max C 0, le_max_right _ _, fun R hR => ?_⟩
      have h1 : μ (Bx R) ≤ ENNReal.ofReal (max C 0 * R ^ D) :=
        (hgr R hR).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
      refine ⟨?_, h1.trans_lt ENNReal.ofReal_lt_top⟩
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hv : 0 < (μ (Bx ρ')).toReal := ENNReal.toReal_pos hρ (hgr' ρ' hρ1).2.ne
    set K : ℝ := ((n : ℝ) + 1) * ρ' * (B + 1) with hK
    have hK1 : 1 ≤ K := by
      rw [hK]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have h2 : (1 : ℝ) ≤ B + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    have hU : ∀ (a : Formalism.REAL.UJ ε) (j : ℕ), Formalism.MainNotions.S.uMat (a ^ j) = Formalism.MainNotions.S.uMat a ^ j := fun a j =>
      map_pow ((Units.coeHom (Matrix (Fin n) (Fin n) ℂ)).comp (Formalism.REAL.UJ ε).subtype) a j
    have em : ∀ j : ℕ, μ.map (fun x => x * ((s : Formalism.REAL.UJ ε) ^ j)) = ((Δ : ℝ≥0∞) ^ j) • μ := by
      intro j
      have := hmod (s ^ j)
      rw [map_pow] at this
      simpa using this
    have key2 : ∀ j : ℕ, (Δ : ℝ) ^ j * (μ (Bx ρ')).toReal ≤ C' * K ^ D * ((j : ℝ) + 1) ^ ((m + 1) * D) := by
      intro j
      have ht : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ (m + 1) := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])
      have hme : MeasurableEmbedding (fun x : Formalism.REAL.UJ ε => x * ((s : Formalism.REAL.UJ ε) ^ j)) :=
        (Homeomorph.mulRight ((s : Formalism.REAL.UJ ε) ^ j)).measurableEmbedding
      have h1 : (((Δ : ℝ≥0∞) ^ j) • μ) (Bx ρ') ≤ μ (Bx (K * ((j : ℝ) + 1) ^ (m + 1))) := by
        rw [← em, hme.map_apply]
        refine measure_mono fun x hx => ?_
        have hx' : x = (x * (s : Formalism.REAL.UJ ε) ^ j) * ((s : Formalism.REAL.UJ ε)⁻¹) ^ j := by
          rw [mul_assoc, inv_pow, mul_inv_cancel, mul_one]
        have h2 := (show Bd (Formalism.MainNotions.S.uMat (x * (s : Formalism.REAL.UJ ε) ^ j)) ρ' from hx).mul (hpow j)
        have h3 : Formalism.MainNotions.S.uMat x = Formalism.MainNotions.S.uMat (x * (s : Formalism.REAL.UJ ε) ^ j) *
            Formalism.MainNotions.S.uMat (((s : S)⁻¹ : S) : Formalism.REAL.UJ ε) ^ j := by
          rw [← hU]
          conv_lhs => rw [hx']
          rfl
        intro i k
        rw [h3]
        refine (h2 i k).trans ?_
        rw [hK]
        have hB' : B ≤ B + 1 := by linarith
        have hn' : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
        have h0ρ : 0 ≤ ρ' := by linarith
        calc (n : ℝ) * (ρ' * (B * ((j : ℝ) + 1) ^ (m + 1))) = (n : ℝ) * ρ' * B * ((j : ℝ) + 1) ^ (m + 1) := by ring
          _ ≤ ((n : ℝ) + 1) * ρ' * (B + 1) * ((j : ℝ) + 1) ^ (m + 1) := by gcongr
      have hR1 : 1 ≤ K * ((j : ℝ) + 1) ^ (m + 1) := by nlinarith
      have h2 := (ENNReal.toReal_mono (hgr' _ hR1).2.ne h1).trans (hgr' _ hR1).1
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, mul_pow, ← pow_mul,
        ← mul_assoc] at h2
      simpa using h2
    by_contra! h1
    have h2 : 1 < (Δ : ℝ) := by exact_mod_cast h1
    have h3 := ((tendsto_pow_const_div_const_pow_of_one_lt ((m + 1) * D) h2).comp
      (Filter.tendsto_add_atTop_nat 1)).const_mul (C' * K ^ D * (Δ : ℝ))
    rw [mul_zero] at h3
    obtain ⟨j, hj⟩ := (h3.eventually (gt_mem_nhds hv)).exists
    have h4 := key2 j
    have h5 : 0 < (Δ : ℝ) ^ j := by positivity
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hj
    have h6 : C' * K ^ D * (Δ : ℝ) * (((j : ℝ) + 1) ^ ((m + 1) * D) / (Δ : ℝ) ^ (j + 1)) =
        C' * K ^ D * ((j : ℝ) + 1) ^ ((m + 1) * D) / (Δ : ℝ) ^ j := by
      have : (Δ : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [h6, div_lt_iff₀ h5] at hj
    linarith
  intro s hs
  have e1 := key ⟨s, hs⟩
  have e2 := key (⟨s, hs⟩ : S)⁻¹
  have e3 : Measure.modularCharacter (⟨s, hs⟩ : S) = 1 := by
    have := map_mul Measure.modularCharacter (⟨s, hs⟩ : S) (⟨s, hs⟩ : S)⁻¹
    rw [mul_inv_cancel, map_one] at this
    refine le_antisymm e1 ?_
    calc (1 : ℝ≥0) = _ := this
      _ ≤ Measure.modularCharacter (⟨s, hs⟩ : S) * 1 := mul_le_mul_of_nonneg_left e2 zero_le
      _ = _ := mul_one _
  have := hmod ⟨s, hs⟩
  rw [e3] at this
  simpa using this

end GlobalTheory.UJUnimod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem record_facts : ∀ (D : D7) (u : D.what₂.Word), SplitsIn D.host.E (D.mem u).A.T ∧ (∀ i, SplitsIn D.host.E (D.host.g i)) ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ D.R.N 0 = D.R.k ∧ IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧ (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  intro D u
  refine ⟨(GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (D.T_mod_cond u)).1,
    D.nd.g_split, D.T_ne_g u, ?_, D.R.N_zero, ?_,
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D 0 (Nat.zero_le _)).ne_zero⟩
  · rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
    ring
  · let _ := D.host.cmStar
    have h := D.sp.baseGram_isHermitian
    refine Matrix.ext fun i j => ?_
    exact congrFun (congrFun h (Fin.cast D.R.N_zero i)) (Fin.cast D.R.N_zero j)

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocalStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_to_special_unitary_local : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool), (∀ g ∈ UJset ε, ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ g₀ ∈ SUset ε, g = z • g₀ ∧ (g ∈ Kset ε ↔ g₀ ∈ KS ε)) ∧ (∀ z : ℂ, ‖z‖ = 1 → ∀ g₀ ∈ SUset ε, z • g₀ ∈ UJset ε ∧ (g₀ ∈ KS ε → z • g₀ ∈ Kset ε)) ∧ ∀ g ∈ UJset ε, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (ζ : Matrix (Fin n) (Fin n) ℂ → ℂ), IsOpen U ∧ g ∈ U ∧ ContinuousOn ζ U ∧ ∀ x ∈ U, x ∈ UJset ε → ‖ζ x‖ = 1 ∧ (ζ x)⁻¹ • x ∈ SUset ε := by
  first | exact @GlobalTheory.SUSplit.unit_scalar_split | exact GlobalTheory.SUSplit.unit_scalar_split | (intros; apply GlobalTheory.SUSplit.unit_scalar_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightsOfExtensionStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weights_of_extension : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → (∀ (μ : Fin n → ℝ) (v : H), v ≠ 0 → (IsWtOn (Kset ε) π μ v ↔ ∑ a, μ a = (m : ℝ) ∧ IsWtS π' (fun a => μ a - (m : ℝ) / n) v)) ∧ ∀ (lam Λ : Fin n → ℝ) (c : ℝ) (S : Submodule ℂ H), IsKTypeU ε lam π Λ S ↔ ∑ a, Λ a = (m : ℝ) ∧ IsKTypeS ε (fun a => lam a - c) π' (fun a => Λ a - (m : ℝ) / n) S := by
  first | exact @GlobalTheory.SUWt.wt_ktype_ext | exact GlobalTheory.SUWt.wt_ktype_ext | (intros; apply GlobalTheory.SUWt.wt_ktype_ext <;> assumption)
end

