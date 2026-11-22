import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundDiscreteSeriesCoefficients
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Formalism.HermitianCurvature.Bundle0004
open BpJoin Formalism.FourierDecayAlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwiseBound_discreteSeries_coefficients : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ThmBpDS := by
  first | exact @GlobalTheory.BpDiscreteSeriesTwoInputs.pointwise_bound_discreteSeries | exact GlobalTheory.BpDiscreteSeriesTwoInputs.pointwise_bound_discreteSeries | (intros; apply GlobalTheory.BpDiscreteSeriesTwoInputs.pointwise_bound_discreteSeries <;> assumption)
