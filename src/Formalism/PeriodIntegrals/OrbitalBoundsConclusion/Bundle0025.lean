import Mathlib
import Formalism.PeriodIntegrals.Bundle0028
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocLift
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IndexCalculation.DvIdxCalcMain
import Formalism.PeriodIntegrals.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupChords.FormalGroupChordFactor
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.Bundle0002
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0024
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0022
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.MirabolicBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerUnipotentSplit.SecondFactorMemLowerTriangular
import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdaptedCharacterForm.SecondCapelliMinorStandardBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroLevelGeneralLinear.GlevZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelImageArithmetic.GlevImageOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftQuantumMinor.QuantumMinorLeftHermitian
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylCellRange.ReflectionMultiplicationOnBigCell

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK
section
theorem adelic_compact_finite_places : PI.AdBridgeSteps.FinK :=
  PI.FinKW.finK_of PI.FinKW.LocTo.mem_local_lattice_iff (PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective)
    PI.FinKW.local_vector_lift
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvIdxCalc
section
theorem division_index_calc : PI.Dv.IdxCalc := PI.Dv.IdxW.dvIdxCalc_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglChordFactor
section
theorem fglChordFactor : PI.FglChordFactor.Lemma := PI.FglChordFactor.Wk.formal_group_chord_factor
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMatBound
section
theorem gg_matrix_bound : Formalism.L2.SG.GGMirabolic.GGMatrixBoundOfLit :=
  PI.GGMatBoundW.ggMatrixBoundOfLit_of PI.GGMatBoundW.matrix_coefficient_equation PI.GGMatBoundW.totally_hermitian_form
    (PI.GGMatBoundW.eigBound_of PI.GGMatBoundW.local_place_bound PI.GGMatBoundW.joint_eigenvector_exists
      PI.GGMatBoundW.prod_formula')
    PI.GGMatBoundW.spectrum_positive_semidefinite convolution_scalar generic_ratio_bound mirabolic_card_unipotent
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMirBound
section
theorem mirabolic_bound : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  PI.GGMirBoundW.mirabolicBound
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
section
theorem highest_weight_irreducible : PI.HwIrred :=
  PI.WHw.hwIrred_of PI.WHw.stable_subspace_closed PI.WHw.fixed_vectors_killed PI.WHw.highest_weight_in_closure
    PI.WHw.closure_eq_nabla
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LowUniSplit
section
theorem lowUniSplit : Formalism.FourierDecayAlt.C2.LowSplit := PI.LowUniSplit.lowSplit
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnAdapted
section
theorem contraction_adapted : Formalism.FourierDecayAlt.Q.ContractionsCovariant → Formalism.FourierDecayAlt.Q.ChatAdapted ∧ Formalism.FourierDecayAlt.Q.Chat2Adapted := by
  intro hcov
  exact ⟨Formalism.FourierDecayAlt.Q.Adapted.chatAdapted_of hcov, Formalism.FourierDecayAlt.Q.Adapted.chat2Adapted_of hcov⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnFFZero
section
theorem quantum_ff_zero : Formalism.FourierDecayAlt.Q.FFZero := PI.UnitaryGroupMassFormula.QnFFZero.ffZero
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnGlevImage
section
theorem gl_level_image : Formalism.QuantumDeterminants.LevHom → Formalism.QuantumDeterminants.LevUH → Formalism.FourierDecayAlt.Q.GlevImage :=
  QnGlevImageW.glevImage_of
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnMinorLeft
section
private theorem eabH_comp_mul_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H h : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.EabH H a b (fun x => f (h * x)) = fun x => Formalism.QuantumDeterminants.EabH H a b f (h * x) := by
  funext g
  simp only [Formalism.QuantumDeterminants.EabH, Formalism.REAL.RdV, mul_assoc]

private theorem qdTop_eabH_comp_mul_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H h : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) u a b (fun x => f (h * x)) =
      fun x => Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) u a b f (h * x) := by
  funext g
  simp only [Formalism.QuantumDeterminants.Top, eabH_comp_mul_left]

private theorem foldr_apply_comp_mul_left_of_forall_mem {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : Matrix (Fin n) (Fin n) ℂ) (L : List ((Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)))
    (hL : ∀ T ∈ L, ∀ f : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f (h * x)) = fun x => T f (h * x))
    (f : Matrix (Fin n) (Fin n) ℂ → E) :
    L.foldr (fun T g => T g) (fun x => f (h * x)) = fun x => L.foldr (fun T g => T g) f (h * x) := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    simp only [List.foldr_cons]
    rw [ih (fun T' hT' => hL T' (by simp [hT']))]
    exact hL T (by simp) _

theorem qnMinorLeft : Formalism.FourierDecayAlt.Q.QMinorLeftH := by
  intro E _ _ n t H f a b u h
  funext x
  simp only [Formalism.QuantumDeterminants.qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hL : ∀ T ∈ List.ofFn (fun k : Fin t =>
      Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)),
      ∀ f' : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f' (h * x)) = fun x => T f' (h * x) := by
    intro T hT f'
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hT
    exact qdTop_eabH_comp_mul_left H h _ _ _ f'
  rw [foldr_apply_comp_mul_left_of_forall_mem h _ hL f]

theorem quantum_minor_left : Formalism.FourierDecayAlt.Q.QMinorLeftH := qnMinorLeft
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnWCell
section
theorem quantum_w_big_cell : Formalism.FourierDecayAlt.Q.WCellBigCell :=
  fun k r c μ => PI.QnWCellW.main k r c μ
end

