import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.CardNonzero

namespace PI.GGMirBoundW

theorem mirabolicBound : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  mirabolicBound_of_steps baseProp stepOf blkFacts colFacts conjCol rowExists charOrth sepLemma

end PI.GGMirBoundW
