import Mathlib
import Formalism.PeriodIntegrals.Bundle0028
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealFieldComparison.JmMulApply
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.CGIntegral
import Formalism.PeriodIntegrals.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.CcPrEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitPowerNormScale.NormUnitsZpowSq

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRealK
section
theorem adelic_compact_real_places : PI.AdBridgeSteps.RealK := PI.UnitaryGroupMassFormula.BridgeRealK.realK
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvGLatProj
section
theorem g_lattice_projection : PI.Dv.GLatProj := PI.Dv.GLP.glatProj
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglTriFactor
section
theorem formal_group_tri_factor : PI.FglTriFactor.Lemma := PI.FglTriFactor.Wk.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTCoefTop
section
theorem gelfand_tsetlin_top_coeff : PI.GTCoefTop := PI.GTNum.gTCoefTop_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTScale
section
theorem gelfand_tsetlin_scaling : PI.GTScale := PI.GTS.gTScale
end

