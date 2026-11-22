import Mathlib
import Formalism.PeriodIntegrals.Bundle0013
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Bundle0001

theorem zerosWindow_of : PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow :=
  fun hL hZ hI => PI.ZW.zerosWindow_of_transfer PI.ZW.transfer hL hZ hI
