import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0040
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilFormulaIntegrableComplex

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorColumnExpansionUnderLinearMapStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantumMinor_column_expansion_under_linearMap : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → b0 ∉ Set.range a → (∀ j v, l (E (a j) b0 v) = (if a j = a0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' (u - 1) v) := by
  first | exact @GlobalTheory.CapStepCol.cap_step_col | exact GlobalTheory.CapStepCol.cap_step_col | (intros; apply GlobalTheory.CapStepCol.cap_step_col <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorEqUnitSmulOfRangeEqStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantumMinor_eq_unit_smul_of_range_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a a₂ b b₂ : Fin t → Fin n), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective a₂ → Function.Injective b → Function.Injective b₂ → Set.range a = Set.range a₂ → Set.range b = Set.range b₂ → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u, Formalism.REAL.qminor E a b u = e • Formalism.REAL.qminor E a₂ b₂ u := by
  first | exact @GlobalTheory.qminor_eq_smul_of_range_eq | exact GlobalTheory.qminor_eq_smul_of_range_eq | (intros; apply GlobalTheory.qminor_eq_smul_of_range_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsComplexDerivedActionCayleyTransportStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothVectors_complexDerivedAction_cayleyTransport : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (R : Rep k r) (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → (∀ v ∈ R.sm, v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) (fun g => R.σ (Q⁻¹ * g * Q))) ∧ ∀ Y v, PI.DSInfCharCap.dsigC ε (fun g => R.σ (Q⁻¹ * g * Q)) Y v = R.dC (Q⁻¹ * Y * Q) v := by
  first | exact @GlobalTheory.CayleyTransport.smooth_and_dsigC_transport | exact GlobalTheory.CayleyTransport.smooth_and_dsigC_transport | (intros; apply GlobalTheory.CayleyTransport.smooth_and_dsigC_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueOnDualTensorSummandStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCasimir_eigenvalue_on_dualTensor_summand : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (Ns : Type) [AddCommGroup Ns] [Module ℂ Ns] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (F : Fin n → Fin n → Module.End ℂ Ns) (io : Ns →ₗ[ℂ] (Fin n → M)) (mu : Fin n → ℝ) (s : Fin n), (∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w) → (∀ y, Formalism.REAL.Cas F y = (casG (mu - Pi.single s 1) : ℂ) • y) → (∀ a b y, io (F a b y) = dualTens E a b (io y)) → ∀ y, splitCas E (io y) = ((-mu s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • io y := by
  first | exact @GlobalTheory.splitCas_on_summand | exact GlobalTheory.splitCas_on_summand | (intros; apply GlobalTheory.splitCas_on_summand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLevelTailMulLogPrimesLe
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory.TailPrimeSum

theorem thBounds : ThBounds := by
  intro k l hk hl
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨-, h3, hlt, he⟩ := GlobalTheory.LevelsOrbits.thlEq k l hk hl
  refine ⟨?_, ?_, fun h => ?_⟩
  · rw [he]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) h3)
  · rw [he]
    exact inv_strictAnti₀ (by positivity) hlt
  · have h1 : (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ 3 := by
      calc (k : ℝ) ^ ((3 : ℝ) / 2) < ((l : ℝ) ^ 2) ^ ((3 : ℝ) / 2) :=
            Real.rpow_lt_rpow (by positivity) h (by norm_num)
        _ = (l : ℝ) ^ 3 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
            norm_num
    have h2 : i0 k l ≤ 3 := Nat.sInf_le ⟨⟨1, by norm_num⟩, le_rfl, h1⟩
    rw [he, le_antisymm h2 h3]

lemma sum_log_le (Q : Finset ℕ) (x : ℝ) (hx : 0 ≤ x) (hQ : ∀ p ∈ Q, p.Prime)
    (hle : ∀ p ∈ Q, (p : ℝ) ≤ x) : ∑ p ∈ Q, Real.log p ≤ 3 / 2 * x := by
  have h1 : ∑ p ∈ Q, Real.log p ≤ Chebyshev.theta x := by
    unfold Chebyshev.theta
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
      (fun p _ _ => Real.log_natCast_nonneg p)
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨(hQ p hp).pos, Nat.le_floor (hle p hp)⟩, hQ p hp⟩
  have h2 := Chebyshev.theta_le_log4_mul_x hx
  have h3 : Real.log 4 ≤ 3 / 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have := mul_le_mul_of_nonneg_right h3 hx
  linarith

lemma tail_le (N : ℕ) : ∀ (Q : Finset ℕ) (Y : ℝ), 0 < Y → (∀ p ∈ Q, p.Prime) →
    (∀ p ∈ Q, Y < p ∧ (p : ℝ) ≤ 2 ^ N * Y) →
    ∑ p ∈ Q, ((p : ℝ) ^ 3)⁻¹ * Real.log p ≤ 4 / Y ^ 2 := by
  induction N with
  | zero =>
    intro Q Y hY _ h
    have : Q = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
      have := h p hp
      simp only [pow_zero, one_mul] at this
      linarith [this.1, this.2]
    rw [this, Finset.sum_empty]
    positivity
  | succ N ih =>
    intro Q Y hY hQ h
    rw [← Finset.sum_filter_add_sum_filter_not Q (fun p : ℕ => (p : ℝ) ≤ 2 * Y)]
    have h1 : ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ 2 * Y), ((p : ℝ) ^ 3)⁻¹ * Real.log p
        ≤ (Y ^ 3)⁻¹ * (3 / 2 * (2 * Y)) := by
      calc _ ≤ ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ 2 * Y), (Y ^ 3)⁻¹ * Real.log p := by
            refine Finset.sum_le_sum fun p hp => ?_
            have := (h p (Finset.mem_filter.1 hp).1).1
            refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
            exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hY.le this.le 3)
        _ ≤ _ := by
            rw [← Finset.mul_sum]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_log_le _ _ (by positivity) (fun p hp => hQ p (Finset.mem_filter.1 hp).1)
              (fun p hp => (Finset.mem_filter.1 hp).2)
    have h2 := ih (Q.filter (fun p : ℕ => ¬ (p : ℝ) ≤ 2 * Y)) (2 * Y) (by positivity)
      (fun p hp => hQ p (Finset.mem_filter.1 hp).1) (fun p hp => by
        obtain ⟨a, b⟩ := Finset.mem_filter.1 hp
        refine ⟨not_le.1 b, ?_⟩
        have := (h p a).2
        rw [pow_succ, mul_assoc] at this
        exact this)
    have h3 : (Y ^ 3)⁻¹ * (3 / 2 * (2 * Y)) + 4 / (2 * Y) ^ 2 = 4 / Y ^ 2 := by
      field_simp
      ring
    linarith

theorem main : Formalism.UnitaryBoundIntegral.ThBounds ∧ ∀ (k : ℕ) (Q : Finset ℕ), 1 ≤ k → (∀ p ∈ Q, p.Prime) →
    ∑ p ∈ Q, thl k p * Real.log p ≤ 20 / k := by
  refine ⟨thBounds, fun k Q hk hQ => ?_⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set Y : ℝ := Real.sqrt k with hYdef
  have hY1 : 1 ≤ Y := Real.one_le_sqrt.2 hk'
  have hY : 0 < Y := by linarith
  have hY2 : Y ^ 2 = k := Real.sq_sqrt (by positivity)
  have hY3 : (k : ℝ) ^ ((3 : ℝ) / 2) = Y ^ 3 := by
    rw [← hY2, ← Real.rpow_natCast, ← Real.rpow_mul hY.le, ← Real.rpow_natCast]
    norm_num
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun p : ℕ => (p : ℝ) ≤ Y)]
  have h1 : ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ Y), thl k p * Real.log p
      ≤ (Y ^ 3)⁻¹ * (3 / 2 * Y) := by
    calc _ ≤ ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ Y), (Y ^ 3)⁻¹ * Real.log p := by
          refine Finset.sum_le_sum fun p hp => ?_
          refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
          rw [← hY3]
          exact (thBounds k p hk (hQ p (Finset.mem_filter.1 hp).1).two_le).2.1.le
      _ ≤ _ := by
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_log_le _ _ hY.le (fun p hp => hQ p (Finset.mem_filter.1 hp).1)
            (fun p hp => (Finset.mem_filter.1 hp).2)
  have h2 : ∑ p ∈ Q.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y), thl k p * Real.log p ≤ 4 / Y ^ 2 := by
    calc _ ≤ ∑ p ∈ Q.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y), ((p : ℝ) ^ 3)⁻¹ * Real.log p := by
          refine Finset.sum_le_sum fun p hp => ?_
          refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
          exact (thBounds k p hk (hQ p (Finset.mem_filter.1 hp).1).two_le).1
      _ ≤ _ := by
          refine tail_le (Q.sup id) _ Y hY (fun p hp => hQ p (Finset.mem_filter.1 hp).1)
            (fun p hp => ?_)
          obtain ⟨a, b⟩ := Finset.mem_filter.1 hp
          refine ⟨not_le.1 b, ?_⟩
          have h3 : p ≤ Q.sup id := Finset.le_sup (f := id) a
          have h4 : p ≤ 2 ^ (Q.sup id) := h3.trans Nat.lt_two_pow_self.le
          have h5 : (p : ℝ) ≤ 2 ^ (Q.sup id) := by exact_mod_cast h4
          exact h5.trans (le_mul_of_one_le_right (by positivity) hY1)
  have h3 : (Y ^ 3)⁻¹ * (3 / 2 * Y) + 4 / Y ^ 2 = (11 / 2) / Y ^ 2 := by
    field_simp
    ring
  have h4 : (11 / 2 : ℝ) / Y ^ 2 ≤ 20 / k := by
    rw [hY2]
    gcongr
    norm_num
  linarith

end GlobalTheory.TailPrimeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqHermTranslatesOrthonormalStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_norm_sq_herm_translates_orthonormal : ∀ (k r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : Mx k r → Matrix ι ι ℂ) (Γ U : Matrix ι ι ℂ) (d : ℕ) (om : ι → ℂ), IsFRep ρ Γ d → U ∈ Matrix.unitaryGroup ι ℂ → ∀ g ∈ GG k r, ∑ e, ‖Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ (fun c => U e c)) om‖ ^ 2 = ∑ i, ‖(ρ g⁻¹ *ᵥ om) i‖ ^ 2 := by
  first | exact @GlobalTheory.MomentParseval.sum_herm_sq | exact GlobalTheory.MomentParseval.sum_herm_sq | (intros; apply GlobalTheory.MomentParseval.sum_herm_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlProjectionLevelSumSqLeStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGl_projection_level_sum_sq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, (∀ s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w))) ∧ ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.lev_proj_and_sum_sq_le | exact GlobalTheory.lev_proj_and_sum_sq_le | (intros; apply GlobalTheory.lev_proj_and_sum_sq_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightCompactDominanceOfMemHighestWeightSpanStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_compactDominance_of_mem_highestWeightSpan : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (E : Fin k → Fin k → Module.End ℂ W) (Λ μ : Fin k → ℝ) (x v : W), Formalism.REAL.GlRel E → Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E → Formalism.REAL.KHighest (PI.UpqRep.allPos k) E Λ x → v ∈ Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x → v ≠ 0 → Formalism.REAL.IsWeight E μ v → PI.UpqRep.CDom (PI.UpqRep.allPos k) μ Λ := by
  first | exact @GlobalTheory.weight_cdom_of_mem_kSpan | exact GlobalTheory.weight_cdom_of_mem_kSpan | (intros; apply GlobalTheory.weight_cdom_of_mem_kSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilFormulaIntegrableComplexStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_integrable_complex : ∀ (k r : ℕ) (μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)) [SFinite μS] (f : Formalism.QuantumDeterminants.Mt k r → ℂ), PI.BesselPeriodGGP.IsQuotMeas μG μS νq → Measurable f → Integrable f μG → (∀ᵐ x ∂νq, Integrable (fun s => f (fun i j => (Matrix.of s * Matrix.of x) i j)) μS) ∧ Integrable (fun x => ∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) νq ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂νq := by
  first | exact @GlobalTheory.weil_formula_integrable | exact GlobalTheory.weil_formula_integrable | (intros; apply GlobalTheory.weil_formula_integrable <;> assumption)
end

