import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0005
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0004

namespace PositivityTheory.KCo

theorem so_coinvariants_of_bernstein (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (hK : GlobalTheory.ThK.KFin) : PositivityTheory.ThKF.SoCoinv :=
  soCoinv_of hB dictionary_statement hK

end PositivityTheory.KCo
