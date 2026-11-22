import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0086

namespace PositivityTheory.MbHsUse

open GroundTheory.Heights₂.Heights.HilbertSamuel

def HSUse : Prop :=
  ArithKleiman.Statement ∧ G7.Statement ∧ ArithmeticVolumeNef.Statement

theorem HSUse.g7 (h : HSUse) : G7.Statement := h.2.1

theorem HSUse.g7p (h : HSUse) : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticHilbertSamuelUpperBound := h.2.2

theorem HSUse.z1 (h : HSUse) : ReciprocityTheory.ChartRestriction.G.Geo.SuccessiveMinimaLowerBound :=
  G5.proof' h.1 CurvePointsFinite.proof

end PositivityTheory.MbHsUse

namespace GlobalTheory.CompanionTheory.Ar.Giv

end GlobalTheory.CompanionTheory.Ar.Giv

namespace GlobalTheory.CompanionTheory.Ar.Small

end GlobalTheory.CompanionTheory.Ar.Small
