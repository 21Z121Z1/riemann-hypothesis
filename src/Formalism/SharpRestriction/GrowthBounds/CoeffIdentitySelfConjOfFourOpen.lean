import Formalism.SharpRestriction.GrowthBounds.Bundle0004
import Formalism.SharpRestriction.GrowthBounds.ConstantCoeffUnshiftLogarithm
import Formalism.SharpRestriction.GrowthBounds.R1sExpLowHolds
import Formalism.LocalToGlobal.CharacterGerms.Bundle0034
import Formalism.LocalToGlobal.CharacterGerms.Bundle0035

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem r1sFrob_holds : PowerSeriesFrobeniusCongruence := frobPow_smul

theorem r1sRoots_holds : RootsOfUnityProductCongruence := fun C _ V ζ hζ j f hf μ => rootsProd C V ζ hζ j f hf μ

theorem coeffIdentity_selfConj_of_four_open (hHL : GaugeLeadingTermLinear) (hHR : GaugeRescalingSymmetry) (hHI : IntegralUnitFamilies) (hGe : GenericPointUnitCongruence) : CoefficientIdentitySelfConjugate :=
  coeffIdentity_selfConj_of_four good_curve_closed r1sRestB_holds
    (r1sRestC_of r1sFrob_holds r1sRoots_holds r1sExpLow_holds hHL hHR hHI hGe) biadditive_on_columns

end Formalism.L2.FormalSeriesBounds
