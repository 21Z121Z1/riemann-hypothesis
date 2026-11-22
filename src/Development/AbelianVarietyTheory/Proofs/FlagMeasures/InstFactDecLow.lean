import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0154

namespace GlobalTheory.DecTransport

theorem decLow_main : Formalism.FourierDecayAlt.ThreeDimData.DecLow := decLow_holds

instance instFactDecLow : Fact (Formalism.FourierDecayAlt.ThreeDimData.DecLow) := ⟨decLow_main⟩

end GlobalTheory.DecTransport
