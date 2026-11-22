import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.Bundle0002

namespace PI.IsoInvMetricW

theorem isoInvMetric_of_hw (hW : HW) : PI.IsoInvMetric.IsoInvMetric :=
  isoInvMetric_of (unit_of metric_mul) (invK_of metric_mul) (stab_of hermitian_vector_map)
    (hvCols_of hermitian_vector_map) norm1' (gen_of quotient_rank hermitian_vector_map) hW

end PI.IsoInvMetricW
