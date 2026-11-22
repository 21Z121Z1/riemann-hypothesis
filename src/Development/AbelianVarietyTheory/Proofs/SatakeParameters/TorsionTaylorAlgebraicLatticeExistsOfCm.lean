import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0248
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0035
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0030

namespace GlobalTheory.CurveThetaInert

theorem torsionTaylorAlgebraic_latticeExists_of_cm (h2 : Formalism.L2.Th1.CM.CM2) :
    Formalism.L2.KerInert.AlgTAll ∧ Formalism.L2.KerInert.GenusOneModelExistsLattice ∧ Formalism.L2.KerInert.Rep.CurveDict :=
  ⟨GlobalTheory.ThLoc.algTAll,
    GlobalTheory.InertGenusOne.datum_exists_lattice h2 ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree ReciprocityTheory.ChartRestriction.L1.cm4,
    GlobalTheory.CurveDictionary.curveDict_of_cm h2 ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree ReciprocityTheory.ChartRestriction.L1.cm4⟩

end GlobalTheory.CurveThetaInert
