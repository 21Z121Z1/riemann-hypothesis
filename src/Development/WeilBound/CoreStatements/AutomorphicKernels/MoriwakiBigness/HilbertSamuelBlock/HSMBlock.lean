import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyConditional
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0116
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0109
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0114
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHSMTransport
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0094
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0090
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0115
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockPieceIndex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulePieceHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0089
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometric
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0061
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0119
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0144
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0154
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029

namespace PositivityTheory.LocalParametersCuspidal.MB.HSM

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4
  ReciprocityTheory.ChartRestriction.G.AI.I1

theorem theoremHSMBlock (hAIS : ArithIntersectionSystemStatement) (hResK : ResK.ResKStatement) :
    TheoremHSMBlock.Statement := by
  have hGr : GraphStatement := GlobalTheory.T.graph_statement_holds
  have hAI3 : Inter.PushforwardArithIntersection.Statement := GlobalTheory.T.generic_degree_of_arith_system hAIS
  have hRes : ResExistsStatement := GlobalTheory.T.resolution_exists_of_resolution_statement hResK
  have hPts : PtsIntegrableStatement := GlobalTheory.T.points_integrable_of_resolution_statement hResK
  have hPF : PFCoordStatement := (GlobalTheory.T.degree_and_coordinates_of_resolution hRes).2
  have hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι := Targets.existsUniqueAll
  have hGF : GenFibreExistsStatement := Targets.genFibreExists
  have hIso : IsomInvariance.Statement := IsomInvariance.proof (Inter.RatR.proof hPts)
  have hCM : ChangeOfModelStatement :=
    Targets.ChangeOfModel.of_found hAI3 hGr hIso GraphIsometric.proof
  have hDim : FibreDimStatement := GlobalTheory.CompanionTheory.Ar.Giv.fibreDim
  have hDG : Inter.DegreeGeneric.Statement :=
    GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS)
  have hAbs : Inter.PtsAbsIntegrable.Statement :=
    Inter.PtsAbsIntegrable.proof hPts (Inter.PtsAbsMeasurable.proof hRes)
  have h6 : ProjFrameGraphDeg.Statement :=
    ProjFrameGraphDeg.proof hEU ProjFrameFibrePt.full ProjFrameFibreDeg.full
  have h15 : GraphChangeOfModel.Statement :=
    GraphChangeOfModel.proof hAI3 hGr hGF hEU hIso GraphIsometricForms.full
  have h16 : BlockGraphDeg.Statement :=
    BlockGraphDeg.proof hGr BlockGraphImage.full hGF hDim hEU Closed.Inter.ChartRankAdjoin
      BlockGraphFibreRatio.full
  have h18 : VeroneseGraphDeg.Statement :=
    VeroneseGraphDeg.proof hGr VeroneseGraphImage.full hDim hEU
  exact TheoremHSMBlock.of_open TwoBlockPieceIndex.proof TwoBlockModuleFinite.proof
    ModulePieceHilbert.proof TwoBlockModuleCycle.proof hPF hCM h6
    (HSMTransport.proof KrullDimMatAct.proof)
    (ResolutionDegree.proof PullFSExtension.full ProjFSMass.proof) ResolutionMixedBridge.full
    (BlockResolutionImageSup.proof ChartSupBound.full)
    (BlockResolutionDegreeIntegral.proof (GenDegGeomDeg.proof hDG)) BlockResolutionMixedBridge.full
    hAbs BlockImageInverse.proof h15 h16 VeroneseGramMono.proof h18

end PositivityTheory.LocalParametersCuspidal.MB.HSM
