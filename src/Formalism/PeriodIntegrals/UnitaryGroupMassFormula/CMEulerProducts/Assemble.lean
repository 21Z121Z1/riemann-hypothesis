import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.Bundle0001

namespace CMEul

theorem eulerEq_of_fib (hF : StepFib) : Formalism.L2.SG.MassRatio.EulerEq :=
  eulerEq_of hF _root_.euler_factors_multipliable euler_factor_local euler_product_regroup

end CMEul
