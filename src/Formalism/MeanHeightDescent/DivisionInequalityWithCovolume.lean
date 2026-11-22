import Formalism.MeanHeightDescent.AverageDegreeBounds.Bundle0001
import Formalism.MeanHeightDescent.AverageDegreeBounds.Bundle0002
import Mathlib
import Formalism.MeanHeightDescent.StatementJ
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0006
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeFullAssemblyHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.GoodBadCut
import Formalism.MeanHeightDescent.AverageDegreeBounds.Bundle0003
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeIntoDivisionHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.CombinedAverageDegreeBoundOf
import Formalism.MeanHeightDescent.Bundle0001
import Formalism.MeanHeightDescent.AverageDegreeBounds.SumComponents
import Formalism.MeanHeightDescent.AverageDegreeBounds.TwistLower

namespace Formalism.ExtensionFiltration

theorem lcvMu : LcvMu := log_covolume_slope_mu
theorem descentSlope : DescentSlope := descent_slope
theorem spanMuMin : SpanMuMin := span_min_slope
theorem goodBadCut : GoodBadCut := good_bad_split
theorem twistLower : TwistLower := twist_lower_bound
theorem muMaxMinkowski : MuMaxMinkowski := max_slope_minkowski
theorem mean_height_sum_bound : CombinedAverageDegreeBound := mean_height_sum_bound_holds

end Formalism.ExtensionFiltration
