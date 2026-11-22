import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinRight
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0065
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0056

namespace PositivityTheory.Xgn.A_s_joinright

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem fibreVarieties : FibreVarieties.Statement.{0} :=
  FibreVarieties.proof GenericFibProps.full GenericDimBound.full GenericDimGe.proof SpecialIdealCorresp.full
    SpecialIdealMultiHomog.full SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialQuotDim.full
    ComponentDim.proof

theorem pairNumRelabel : PairNumberRelabelAlt.Statement :=
  PairNumberRelabelAlt.proof (VerticalComponentFibre.proof fibreVarieties)

theorem of_pullback (h : PairNumberPullback.Statement) : FlagModelJoinRightAlt.Statement :=
  FlagModelJoinRightAlt.proof JoinVerticalDivisor.proof (FlagPairJoinRight.proof JoinVerticalDivisorRight.proof)
    (PairNumberJoinRight.proof
      (PairNumberJoinLeft.proof h JoinVerticalDivisorLeft.proof BirationalJoin.proof)
      JoinVerticalDivisorRight.proof pairNumRelabel)

end PositivityTheory.Xgn.A_s_joinright
