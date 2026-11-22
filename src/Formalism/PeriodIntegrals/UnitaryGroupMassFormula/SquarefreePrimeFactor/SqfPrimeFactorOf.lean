import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.SquarefreeCountEstimate

namespace PI.SqfPrimeFactor.W

theorem sqfPrimeFactor_of (hRS : PI.PrimesDyadicRS.Claim) : PI.SqfPrimeFactor.Claim :=
  claim_of squarefree_count_estimate irreducible_count_lower_bound (analytic_of hRS)

end PI.SqfPrimeFactor.W
