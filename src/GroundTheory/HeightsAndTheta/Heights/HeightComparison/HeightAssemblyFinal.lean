import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightAssemblyClosed
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMax
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMult
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlaceCentredSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0002
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem HeightAsIntersection.full : HeightAsIntersection.Statement :=
  have hM : OrbitChartMax.Statement := OrbitChartMax.proof
  have hQ : OrbitChartQuot.Statement := OrbitChartQuot.proof
  have hIff : OrbitCenterMemIff.Statement := OrbitCenterMemIff.proof
  HeightAsIntersection.of_chart_and_centre OrbitChartRing.proof hM
    (OrbitChartResidue.proof hM hQ (OrbitChartDehom.proof hM hQ))
    OrbitChartMult.proof
    (LocalLengthPlaces.proof LocalQuotCard.proof CentredPlacesFinite.proof
      (LocalQuotCentred.proof CentredRingNormal.proof LocalNormalIndex.proof) PlacesRingQuot.proof)
    OrbitCenterChart.proof PlaceCentredSum.proof OrbitChartTerm.proof OrbitCenterLe.proof hIff
    (OrbitCenterDivSupp.proof hIff (OrbitCenterPrime.proof hIff) SubringPrimeMaximal.proof)

end GroundTheory.Heights₂.Heights
