import Mathlib
import Formalism.PeriodIntegrals.Bundle0016
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.RpowQuarterPowFour
import Formalism.PeriodIntegrals.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardCharacterTrace.SumEmbeddingEqTrace
import Formalism.PeriodIntegrals.Bundle0012
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.UnitaryScalars
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittEndomorphism.WfEndOfLog
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0016

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqfRootsInj
section
theorem squarefree_roots_injective : PI.SqfRootsInj.Claim :=
  PI.SqfRootsInj.W.claim_of PI.SqfRootsInj.W.counted_labels_have_witness PI.SqfRootsInj.W.local_orbit_count
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StdCharTR
section
theorem stdCharTR : PI.StdCharTR.Target :=
  PI.StdCharTRWork.stdCharTR_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitDetRoot
section
theorem unit_det_root_of_unity : PI.UnitDetRoot :=
  PI.UnitaryGroupMassFormula.UnitDetRoot.unitDetRoot_of_global PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryApproxFin
section
theorem unitary_approximation_finite : PI.UnitaryApproxFin.UnitaryApproxFin :=
  PI.UnitaryApproxFinWork.unitaryApproxFin_of PI.UnitaryApproxFinWork.topStep
    PI.UnitaryApproxFinWork.cayleyStep PI.UnitaryApproxFinWork.approxEStep
    PI.UnitaryApproxFinWork.weak_approximation_finite_unitary PI.UnitaryApproxFinWork.bounded_rational_unitary
    PI.UnitaryApproxFinWork.unitary_scalars PI.UnitaryApproxFinWork.eigenvalue_avoidance
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittFrobeniusEnd
section
theorem witt_pairing : PI.PairW := PI.WfEndProof.pairW

theorem witt_frobenius_end : PI.WfEnd := PI.WfEndProof.wfEnd_of_log witt_logarithm

theorem wfEnd_of : PI.WfRing → PI.WfSubst → PI.WfLog → PI.WfEnd := PI.WfEndProof.wfEnd_of
end

