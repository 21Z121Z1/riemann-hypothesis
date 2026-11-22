import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.PInsertNth

namespace PositivityTheory.KB

theorem sStokes_of : SStokes := by
  intro V _ _ U hU hUc q ω hω y hy
  exact StokesSlices.asm StokesSlices.subAlt StokesSlices.subHyp StokesSlices.subSlice U hU hUc q ω hω y hy

end PositivityTheory.KB
