import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairData
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystem
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLawStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecond

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem germs_deriv_kernel_of_formal : IntegralGermIndependentAllCharts ∧ CEqFBSt ∧ IndependenceBoundAllCharts :=
  ⟨fun C _ _ V O _ _ dd Y d _ I _ p H =>
      _root_.GlobalTheory.RowLaw.intGerm_indep_of_rlaw C V d I (Fin dd) (Y.raw p) (_root_.GlobalTheory.RowLawPair.rLaw_pairData C V O dd Y d I p) H,
    fun C _ _ V O _ _ dd Y d _ I _ p _ H =>
      GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw C V d I (Fin dd) (Y.raw p) (_root_.GlobalTheory.RowLawPair.rLaw_pairData C V O dd Y d I p) H,
    fun C _ _ V O _ _ dd Y d _ I _ p hr H h2 =>
      _root_.GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition C V d I (Fin dd) (Y.raw p) (_root_.GlobalTheory.RowLawPair.rLaw_pairData C V O dd Y d I p) hr H h2⟩

end GlobalTheory.RowLaw
