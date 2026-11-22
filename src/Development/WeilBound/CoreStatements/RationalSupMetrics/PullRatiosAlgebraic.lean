import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0088
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0080
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0070
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0097
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAvoidFormFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormMax
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0099
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0098
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomCharpolyForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0105
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0100
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0111
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0102
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0113
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0110
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0112
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0023
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0054

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

namespace MultiProjectiveCoordinates

theorem pull_ratios_algebraic : PullRatiosAlgebraic.Statement :=
  PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof

theorem pull_forms_generic : PullFormsGeneric.Statement := PullFormsGeneric.proof pull_ratios_algebraic

theorem fibre_pull_integral : FibreNormPullback.Statement :=
  FibreNormPullback.proof_dehom pull_forms_generic
    (FibreNormDehomCharpoly.proof pull_forms_generic pull_ratios_algebraic PullSectionIntegral.proof
      DehomCharpolyForms.proof)
    (FibreNormDehomIntegral.proof FibreNormBadPrimesFinite.proof
      (FibreNormGoodPrimeIntegral.proof GlobalTheory.T.pullback_cone_null_mod_p_holds PullConeDegreeInt.proof PullSectionIntegralInt.proof
        DehomNormPIntegral.proof)
      (FibreNormPrimeBound.proof pull_forms_generic GlobalTheory.T.norm_form_gauss_bound_holds ChartPrimePowerInverse.proof))
    FibreNormDehomRoots.full

theorem grid_separation : GridSeparation.Statement :=
  GridSeparation.proof NormalLocusRep.proof
    (FibreNormBound.proof (ProjAvoidingForm.proof SegreArith.proof)
      (FibreRepresentatives.proof AvoidFormFinite.proof)
      (FibreNormMax.proof fibre_pull_integral) MetricMaxComparison.proof)
    RootGridLower.proof

end MultiProjectiveCoordinates

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology in
theorem MultiProjectiveCoordinates.packing_statement : PackingStatement :=
  SmallPacking.proof
    (NmSectionsRankBound.proof (NmSectionsFinite.proof (Conductor.proof SecEq.proof)) SecMRankBound.full)
    (SmallSectionsSeparated.proof MultiProjectiveCoordinates.grid_separation)
