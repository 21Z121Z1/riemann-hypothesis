import Mathlib
import Formalism.LocalToGlobal.AdelicCompactOpens.UniROfUniRT
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualUniqueness.Imports
import Formalism.PeriodIntegrals.Bundle0021
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.IdxStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGroupIntegrability.IsPositiveDefiniteMatrixCoefficientOfMemAlgA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderSignIdentity.SkipOneEqSuccAbove
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0016
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.IsCompactInterUnitBox
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0003
import Formalism.PeriodIntegrals.Bundle0026
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaUnitary.NatWCastReal

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgWtDualUniq
section
theorem algebraic_weight_dual_unique (L : Type) [Field L] [NumberField L] [NumberField.IsCMField L] (n : ℕ) : Formalism.L2.Props.DualUnique L n :=
  PI.UnitaryGroupMassFormula.AlgWtDualUniq.main L n
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ParahoricIdxZ
section
theorem parahoric_index_int : PI.ParahoricIdxZ :=
  PI.ParahoricIdxZ.W.parahoricIdxZ_of PI.ParahoricIdxZ.W.idxStep PI.ParahoricIdxZ.W.cardStep
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PolyCoef
section
theorem polynomial_coefficients : PI.PolyCoef := PI.UnitaryGroupMassFormula.PolyCoef.polyCoef
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderES
section
theorem quantum_minor_border_es : PI.QmBorderES := PI.UnitaryGroupMassFormula.QmBorderES.qmBorderES_of quantum_minor_column_expansion quantum_minor_row_expansion
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU
section
open PI.QuotSetU.UnitaryGroupMassFormula in
theorem quotient_measure_unitary_group : PI.QuotSetU :=
  quotSetU_of unitary_hermitian_group siegel_set_subset (SW.sGroup_of unitary_weyl_compact) exists_modular_function unitary_group_modular_function_trivial
    (SW.trivS_of (SW.sGroup_of unitary_weyl_compact) unitary_weyl_compact SW.nilpotent_subgroup SW.unipotent_radical_contracting)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForU
section
theorem weylForU_of : PI.ModelIso → PI.NablaDim → PI.WeylForU := PI.WeylForUWork.weylForU_of
end

