import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegelSmall
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0013

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem model_existence_of_siegel (hG : SiegelSmall) : ModelEx := model_existence_of_siegel_small hG (smallS_of' chartFacts sliceFacts)

end PositivityTheory.SiegelWeilFormula.Ald

end
