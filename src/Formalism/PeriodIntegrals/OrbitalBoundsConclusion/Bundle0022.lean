import Mathlib
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Formalism.PeriodIntegrals.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalPointsComparison.BridgeApplyEqOfComp
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.MassRatio
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.SubMemDifferentIdeal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.FibreShapeOf
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianGroupLattices.IsCMFormEOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCardinality.UniMatUpper
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GenericRatioBound.GenericRatioOfBound
import Formalism.PeriodIntegrals.Bundle0026
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorSpanning.TensSpans
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.QmBorderFullOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0021
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0016
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019
import Formalism.PeriodIntegrals.Bundle0027
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation
import Formalism.PeriodIntegrals.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoveringRadius.CoverRad

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgValsFin
section
theorem algebraic_values_finite (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  PI.AlgValsFin.W.algValsFin_main L

theorem algValsFin (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  algebraic_values_finite L
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BeConjNorm
section
theorem conjugate_norm_bound : PI.BeConjNorm.BeConjNorm :=
  PI.BeConjNormW.beConjNorm_of_intInv PI.BeConjNormW.inverse_integral_padic
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRatPts
section
theorem adelic_rational_points : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeGF I :=
  Formalism.L2.SG.AdBridge.adBridgeGF_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMDiscSq
section
theorem Formalism.L2.SG.MassRatio.cm_discriminant_square : Formalism.L2.SG.MassRatio.DiscSq :=
  PIW.CMDiscSq.discSq_of PIW.CMDiscSq.relDiffTop PIW.CMDiscSq.relDegTwo
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMEulerEq
section
theorem Formalism.L2.SG.MassRatio.mass_ratio_euler_eq : Formalism.L2.SG.MassRatio.EulerEq :=
  CMEul.eulerEq_of_fib (CMEulFib.stepFib_of CMEul.euler_factor_conjugate)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvGLatHerm
section
theorem g_lattice_hermitian : PI.Dv.GLatHerm := PI.Dv.GLatHermW.glatHerm
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGCardUni
section
theorem mirabolic_card_unipotent : Formalism.L2.SG.GGMirabolic.CardUni := PI.GGCardUniWork.cardUni
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGGenRatio
section
theorem generic_ratio_bound : Formalism.L2.SG.GGMirabolic.GenericRatioOfBound := by
  unfold Formalism.L2.SG.GGMirabolic.GenericRatioOfBound
  intro hMir hCard
  unfold Formalism.L2.SG.GGMirabolic.GenericRatio
  intro F _ _ k ψ₀ hψ V _ _ _ π hirr hgen
  have hb := hMir F k ψ₀ hψ V π hirr hgen
  rw [hCard F k]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqR : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hx : ∀ i ∈ Finset.Ico 1 k, (1 : ℝ) < (Fintype.card F : ℝ) ^ i := by
    intro i hi
    have hi1 : i ≠ 0 := by
      simp only [Finset.mem_Ico] at hi
      omega
    exact one_lt_pow₀ hqR hi1
  have hsum : ∑ i ∈ Finset.Ico 1 k, i = k * (k - 1) / 2 := by
    rw [← Finset.sum_range_id]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
      simp
  have hP : 0 < ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) :=
    Finset.prod_pos fun i hi => sub_pos.mpr (hx i hi)
  have hcast : ((∏ i ∈ Finset.Ico 1 k, (Fintype.card F ^ i - 1) : ℕ) : ℝ)
      = ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hPD : ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) ≤ (Module.finrank ℂ V : ℝ) := by
    rw [← hcast]
    exact_mod_cast hb
  have hR : ∏ i ∈ Finset.Ico 1 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)⁻¹
      = (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have h1 := hx i hi
    have h0 : (Fintype.card F : ℝ) ^ i ≠ 0 := (lt_trans one_pos h1).ne'
    have h2 : (Fintype.card F : ℝ) ^ i - 1 ≠ 0 := (sub_pos.mpr h1).ne'
    field_simp
  rw [hR, Nat.cast_pow]
  gcongr
  all_goals first
    | exact hPD
    | exact hP.le
    | exact hP
    | positivity
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerTens
section
theorem kernel_tensor_spans : PI.KerTens.TensSpans := PI.KerTens.W.tensSpans
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderFull
section
theorem quantum_minor_border_full : PI.QmBorderFull :=
  PI.qmBorderFull_of quantum_minor_border_es quantum_minor_column_expansion quantum_minor_row_expansion quantum_minor_skip
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScPsiExists
section
theorem sc_psi_exists : PI.ScPsiExists.Target :=
  PI.ScPsiExists.UnitaryGroupMassFormula.norm_units_of_calculation
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCoveringDivisor
section
theorem transference_covering_divisor : PI.TransferenceCoverDiv := PI.Tr2.coverDiv
end

