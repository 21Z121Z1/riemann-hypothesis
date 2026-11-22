import Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjOfFourOpen
import Formalism.SharpRestriction.GrowthBounds.PsOfIntS
import Formalism.SharpRestriction.GrowthBounds.RescaleInV
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0002
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0009
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SourcePrimitiveIntegrality

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjOfTwo
section
noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem r1sHInt_holds : IntegralUnitFamilies :=
  fun C _ _ V d I _ κ _ X _ hBi ζ hζ n hn γ δ c hγ hδ hc hN => SelfConjGauge.hInt_core V X hBi ζ hζ n hn γ δ c hγ hδ hc hN

theorem r1sHResc_holds : GaugeRescalingSymmetry := r1sHResc

theorem coeffIdentity_selfConj_of_two (hHL : GaugeLeadingTermLinear) (hGe : GenericPointUnitCongruence) : CoefficientIdentitySelfConjugate :=
  coeffIdentity_selfConj_of_four_open hHL r1sHResc_holds r1sHInt_holds hGe

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ScaleEdges
section
noncomputable section

namespace Formalism.MainNotions.Pf14

theorem theorem_II_of_edge_bound (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hR : RestEdge D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_edge_bound_constants D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 manyEdges s7 asm num hA h14a h14b hR

theorem prvE_degree_five_of_adm_sources_realisable (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hR3 : SourcesRealisable D CLa Ck Crk Cdeg CLa' CD Csz)
    (hRC : RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_edge_bound D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restEdge_of D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hR3 hRC)

theorem theorem_II_of_cloud_bound (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hRC : RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  prvE_degree_five_of_adm_sources_realisable D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b (sources_realisable_holds D CLa Ck Crk Cdeg CLa' CD Csz) hRC

theorem theorem_II_of_cloud_bound_X (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hRC : RestCloudX D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_cloud_bound D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restCloud_of_X D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hRC)

theorem theorem_II_of_cloud_bound_Y (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hRC : RestCloudY D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_cloud_bound_X D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restCloudX_of_Y D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hRC)

theorem theorem_II_of_split_cloud_bounds (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (h6a : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg) (h6b : RemainingInputsAfter D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_cloud_bound_Y D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restCloudY_of D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 h6a h6b)

end Formalism.MainNotions.Pf14
end
end

