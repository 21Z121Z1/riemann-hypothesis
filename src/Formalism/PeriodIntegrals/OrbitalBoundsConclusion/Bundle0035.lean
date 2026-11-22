import Formalism.PeriodIntegrals.Bundle0029
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.ContinuousRootCoords
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRootJac
section
theorem amplifier_root_jacobian : PI.AmpRoot.RootJac := PI.AmpRootJacW.rootJac
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BetaLUniq
section
theorem beta_l_unique : PI.BetaLUniq :=
  PI.UnitaryGroupMassFormula.BetaLUniq.betaLUniq_of_aniso_eigen PI.UnitaryGroupMassFormula.BetaLUniq.weight_space_anisotropic
    PI.UnitaryGroupMassFormula.BetaLUniq.eigenvalue_last_line_eq_one
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FlagRelevScalar
section
theorem flagRelevScalar (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Algebra K E] : Formalism.L2.SG.IdCell.RelevScalar E K :=
  PI.FRS.relevScalar_of PI.FRS.dualExists PI.FRS.coefAdd PI.FRS.coefSmul PI.FRS.coefE
    PI.FRS.coefLow E K
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasWCore
section
theorem weil_measure_compat : Formalism.L2.SG.Pf.MeasCore.MWCore :=
  PI.UnitaryGroupMassFormula.MeasWCore.measWCore_main
end

