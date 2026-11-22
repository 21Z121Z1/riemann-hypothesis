import Mathlib
import Formalism.PeriodIntegrals.Bundle0010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.Bundle0002

noncomputable section

namespace PI.SelfDualLoc.W

theorem selfDualLoc_of_steps (hN : Nondeg) (hL : LocBasis) : PI.SelfDualLoc :=
  selfDualLoc_of sigInt hN (spanTop_of hN) hL dualBasis unitLoc

theorem selfDualLoc_of_locBasis (hL : LocBasis) : PI.SelfDualLoc :=
  selfDualLoc_of_steps nondeg hL

end PI.SelfDualLoc.W
