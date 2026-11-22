import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Partial
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPow

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

theorem indexEq_of_traceInt (h : TraceInt) : PI.AdIndexEq.IndexEq :=
  indexEq_of_open gl_character (qReflPow_of h)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
