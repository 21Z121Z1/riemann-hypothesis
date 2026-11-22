import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0058

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem cartHyp_of_formalBiextension : CartFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p
  exact GlobalTheory.T.cartHyp_of_integralGaugedFormalGroupLaw C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p)
    (GlobalTheory.T.hasGaugeAdjointLieProjectors_pairData C V O dd Y d I p) (GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_pair_places C V O dd Y d I p)

end GlobalTheory
