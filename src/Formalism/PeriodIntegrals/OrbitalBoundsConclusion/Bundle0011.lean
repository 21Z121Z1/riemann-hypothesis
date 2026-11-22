import Formalism.PeriodIntegrals.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.Bundle0001
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOfHorn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.NormDetConjExp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.ExpCongruenceExtendsToSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.MinusPartOfMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockWeightDegree.ExistsMonomialWeight
import Formalism.PeriodIntegrals.Bundle0018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MultiplicityMeasurability.MeasurableMult
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingIdentity.FoldUnfoldMain
import Formalism.PeriodIntegrals.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.IsoDerivB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle0001
import Formalism.PeriodIntegrals.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ExistsDenomBackward
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FourSquareQuaternions.FourSqOfFromDiag
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualDifferent.SelfDualOfDiff

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExpIntW
section
theorem expIntegralWitt : PI.ExpIntW :=
  PI.ExpIntWProof.expIntW_of_key PI.ExpIntWProof.stepI PI.ExpIntWProof.keyW
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExpTri
section
theorem exp_triangle_inequality : PI.ExpTri := PI.ET.expTri_of_horn (PI.ET.horn_of PI.ET.kyFanDet)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglPhSplit
section
namespace PI.Final.FglPhSplit

theorem norm_units_of_calculation : PI.FglPhSplit.Target :=
  PI.FglPhSplit.Wk.target_of PI.FglPhSplit.Wk.orthogonalSplitPolarizationVanishes PI.FglPhSplit.Wk.addPreservesExpCongruence
    PI.FglPhSplit.Wk.expCongruenceExtendsToSum

end PI.Final.FglPhSplit
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockHarmSplit
section
theorem harmonicSplitting_holds : PI.FockDegreeTwoParts.HarmSplit := PI.FHS.harmSplit
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockWtDeg
section
theorem highestWeightDegree_le : PI.FockDegreeTwoParts.WtDeg := PI.FockWtDegWork.wtDeg
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldMult
section
open PI.FoldMult.UnitaryGroupMassFormula

theorem overlapMultiplicityProperties : PI.FoldMult.FoldMult := by
  intro G _ _ _ _ _ _ _ Γ hΓ Ω hΩ h1
  exact ⟨fun x => one_le_mult Γ Ω h1 x, fun x => mult_lt_top Γ Ω hΩ x,
    fun γ hγ x => mult_mul_left Γ Ω γ hγ x, measurable_mult Γ Ω hΩ⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
section
theorem lintegralTransversalSum : PI.FoldUnfold.FoldUnfold :=
  PI.FoldUnfold.UnitaryGroupMassFormula.foldUnfold_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoDerivB
section
theorem isometry_derivative_bound : PI.IsoDerivB.IsoDerivB := PI.IsoDerivBFintype.isoDerivB
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.JetsPhW
section
theorem jets_high_generation : PI.JetsPhW.HighG :=
  PI.JetsPhW.W.highG_of PI.JetsPhW.W.derivative_chain_rule PI.JetsPhW.W.derivative_self
    PI.JetsPhW.W.pderiv_subst_ne PI.JetsPhW.W.pderiv_subst_self PI.JetsPhW.W.evaluation_at_zero
    PI.JetsPhW.W.jet_derivative_integrality PI.JetsPhW.W.log_derivative_integral_jet_integrality PI.JetsPhW.W.derivative_integral

theorem jets_phase_weights : PI.JetsPhW.Target :=
  PI.JetsPhW.W.glue_holds_var PI.JetsPhW.Inv.inverse_omega_holds jets_high_generation
    PI.JetsPhW.Low.firstJetIntegralGeneral_holds PI.JetsPhW.Low.secondJetIntegralGeneral_holds

theorem jets_high : PI.JetsPhW.High :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).1

theorem jets_one : PI.JetsPhW.One :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.1

theorem jets_two : PI.JetsPhW.Two :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.2
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerDetFin
section
theorem ordRelativeDet_finite : PI.KerIso.DetOrdFin := PI.KerDetFinW.detOrdFin
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerFourSq
section
theorem kernel_four_squares : PI.KerIso.FourSq :=
  PI.KerIso.FourSqW.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerSelfDual
section
theorem kernel_self_dual_of_different : PI.KerIso.SelfDualOfDiff := PI.UnitaryGroupMassFormula.KerSelfDual.selfDualOfDiff
end

