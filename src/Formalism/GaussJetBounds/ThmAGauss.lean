import Formalism.GaussJetBounds.GaussJetProofs.ThmAGaussOf
import Formalism.GaussJetBounds.GaussJetProofs.Bundle0004
import Formalism.GaussJetBounds.GaussJetProofs.FJEval

namespace Formalism.DworkPowerSeriesWeights

theorem thmAGauss : ThmAGauss :=
  thmAGauss_of admissibleTransfer frame_jet_evaluation labelsExist_statement gauss_sum_powers

end Formalism.DworkPowerSeriesWeights
