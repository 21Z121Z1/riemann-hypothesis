import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0005
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0004

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Theta

structure AllTied (D : D7) (X : ThetaX D) (A : TH.ProvA) where

  T : ThetaTied D X

  sm : ThetaSmoothnessCondition T

  ty : TypTied T

  W : WeilTied D X T
  unr : WeilUnramifiedCondition W

  kf : KfinTied W

  phiUp : PhiYupTied W

  B : BesselTied D X T W

  real : RealTied D

  prov : ProvisionCompatibility D A

end Formalism.L2.Theta

end
