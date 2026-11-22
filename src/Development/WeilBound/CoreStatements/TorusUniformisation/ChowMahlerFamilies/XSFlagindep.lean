import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreClosureNumber
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0079

namespace PositivityTheory.Xgn.A_s_flagindep

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem closureModel : GenericProjClosureModel.Statement :=
  GenericProjClosureModel.proof TwistedDualGensExist.proof
    (GenericProjClosureDim.proof DvrConeDimTrdeg.proof
      (PairBundleTrdeg.proof AdjoinTrdegAdd.proof PairConeLinesIndep.proof PairConeAlg.proof))
    (GenericProjClosureDivisor.proof TwistedDualGensExpress.proof)

theorem flagClosureModel : SegreFlagClosureModel.Statement :=
  SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)

theorem of_items (hC2 : VerticalDivisorsCommute.Statement.{0}) (hPull : PairNumberPullback.Statement)
    (hCut : SegreFlagClosureCut.Statement) : FlagIndependence.Statement := by
  have hPE := PairNumberExpansionIndependence.proof hC2
  have hSP := SegreFlagClosurePullback.proof hPull hPE flagClosureModel PairNumberRelabel.proof
    VerticalDivisorJoinPullback.proof SegreFlagClosureBirational.proof
  have hSCN := SegreClosureNumber.proof hPE flagClosureModel hCut hSP
  exact FlagIndependence.proof hPE (HsymmPairFlagIndependence.proof hPE closureModel hSCN)
    SymmetricSpanHsymm.proof

end PositivityTheory.Xgn.A_s_flagindep
