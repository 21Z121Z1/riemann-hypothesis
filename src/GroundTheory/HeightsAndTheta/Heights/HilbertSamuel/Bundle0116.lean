import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAnResToAnalyticRes
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageChi
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMonomialDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0114
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjectionBounds
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFSExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealGramComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResChiBounds
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResChiIndex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseMonoBasis
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0094
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0107
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Assembly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem AnResToAnalyticRes.full : GroundTheory.Heights₂.Heights.HilbertSamuel.AnResToAnalyticRes.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.AnResToAnalyticRes.proof NonvanishingDense.full

theorem BlockImageChi.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.proof

theorem ResChiBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.proof ResolutionSupBound.full

theorem ProjectionBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.proof ResChiBounds.full

theorem PullFSExtension.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.proof ProjFrameBasePtFree.full

theorem ProjFSMass.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFSMass.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFSMass.proof

theorem RealGramComparison.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.proof ResolutionSupBound.full ProjectionBounds.full PullFSExtension.full

theorem MonomialDegree.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MonomialDegree.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MonomialDegree.proof

theorem ResChiIndex.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.proof

theorem VeroneseMonoBasis.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem BlockResolutionMixedBridge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.proof

theorem BlockResolutionMixedIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedIntegral.proof BlockResolutionMixedBridge.full BlockResolutionInterpIntegral.full

theorem ResolutionMixedBridge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.proof

theorem ResolutionMixedIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof ResolutionMixedBridge.full ResolutionInterpIntegral.full

theorem Closed.Inter.pullbackPushforward_holds : GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.proof Closed.Inter.BlockGenFinite Closed.Inter.FibreIsolFinite

theorem Closed.Inter.pullbackDensity_holds : GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.proof

theorem Closed.ReciprocityTheory.ChartRestriction.G.Geo.ResBridge : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.resBridge

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

