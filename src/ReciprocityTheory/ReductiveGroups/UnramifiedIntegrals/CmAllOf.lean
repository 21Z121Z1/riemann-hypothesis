import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedStatus
import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0015
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0027
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0034
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0030

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

theorem cm2 (hH : _root_.Neutral.HilbertClassField.Statement) (hC : ChebOmSt) : CM2 :=
  goodReduction_of_integral_unramified jInt (jUnram hH hC)

end ReciprocityTheory.ChartRestriction.L1
