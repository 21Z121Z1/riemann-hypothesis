import Mathlib
import Formalism.PeriodIntegrals.Bundle0012
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.VacuumEntire.AnalyticAtHfLeft
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylProduct.WeylProd
import Formalism.PeriodIntegrals.Bundle0013
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionEvaluation.LsumEqOfSubset
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.InstFintypeColChoice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorExpansion.WwMinorExpandMain

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VacEntire
section
theorem entireStatements_holds : PI.VacEntire.Target :=
  ⟨PI.VacEntire.UnitaryGroupMassFormula.iopEntire, PI.VacEntire.UnitaryGroupMassFormula.tensEntire⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylProd
section
theorem weyl_product_formula : PI.WeylProd := PI.WeylProdWork.weylProd
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwEval
section
theorem minor_evaluation : PI.WwEval.WwEval := PI.WwEvalWork.wwEval
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwInjective
section
theorem wwInjective_of (h : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective :=
  PI.WwInjectiveWork.wwInjective_of h
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwMinorExpand
section
theorem minor_expansion : PI.WwMinorExpand.WwMinorExpand := PI.WwMinorExpandWork.wwMinorExpand_main
end

