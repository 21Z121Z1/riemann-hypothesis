import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SphericalFunctionLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059

namespace GlobalTheory.HCXi

theorem xiExists_of_besselXiIntegrable : BesselXiIntegrable → Formalism.FourierDecayAlt.B.XiExists := fun h => h

end GlobalTheory.HCXi
