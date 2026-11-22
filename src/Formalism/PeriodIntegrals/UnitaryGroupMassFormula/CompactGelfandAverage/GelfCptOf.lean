import Mathlib
import Formalism.PeriodIntegrals.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.AvgStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.Bundle0001

namespace PI.UnitaryGroupMassFormula.GelfCpt

theorem gelfCpt_of : PI.UMultOne.IntSpan → PI.UMultOne.ConvComm → PI.UMultOne.GelfandCompact :=
  gelfCpt_of_steps avgStep mulStep

end PI.UnitaryGroupMassFormula.GelfCpt
