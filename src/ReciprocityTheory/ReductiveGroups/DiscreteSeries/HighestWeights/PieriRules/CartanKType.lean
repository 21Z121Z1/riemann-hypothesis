import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle0003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle0002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylSum
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.CountNotTwoOfFinrankLeOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle0004

namespace ReciprocityTheory.ChartRestriction.DS.HW

theorem pieriCount : PieriCountStatement := pieriCount_of compRed kRepRel

theorem pieriStd : PieriStdStatement := pieriStd_of compRed kRepRel

theorem pieriDual : PieriDualStatement := pieriDual_of compRed kRepRel

theorem pPlus : PPlusStatement :=
  pPlus_of_parts pieriCount tensHW kTypeIntDom weylSumP
    (fun _ ε β => ⟨pRho ε β, pDRho ε β, pRho_continuous ε β,
      fun X hX γ hγ i j => pRho_hasDerivAt ε β X hX γ hγ i j, fun a b => pDRho_single ε β a b⟩)
    (fun _ ε β => pAdM_kRel ε β)

end ReciprocityTheory.ChartRestriction.DS.HW
