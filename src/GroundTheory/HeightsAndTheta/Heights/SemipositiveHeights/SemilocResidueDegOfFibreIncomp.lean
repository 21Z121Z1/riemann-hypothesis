import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0057
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

theorem projDeg_all :
    ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι' := by
  intro F _ K _ ι _ K' _ ι' _
  exact GroundTheory.Heights₂.Heights.Targets.ProjDeg.of_found
    (GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.proof
        GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe.proof
        GroundTheory.Heights₂.Heights.NumbersDVR.DivPushForwardLocalZero))
    GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg.proof F ι ι'

theorem semilocMaxIdeals_of_fibreIncomp (hFI : FibreIncomp.Statement) : SemilocMaxIdeals.Statement :=
  SemilocMaxIdeals.proof (FibreOverFinite.proof hFI) hFI SemilocIntegral.full LocRingDimOne.full

theorem semilocResidueDeg_of_fibreIncomp (hFI : FibreIncomp.Statement) (hFD : FibreDimStatement) :
    SemilocResidueDeg.Statement :=
  SemilocResidueDeg.proof (SemilocResidueFibreDim.proof (FibreDivSupp.proof hFI) hFD FibreDimensionZero.full)
    (SemilocResidueAdjoin.proof
      (SemilocResidueFrac.proof SemilocFinite.full (semilocMaxIdeals_of_fibreIncomp hFI))
      ChartScalingIndep.full)

end GroundTheory.Heights₂.Heights.ForSecondHalf
