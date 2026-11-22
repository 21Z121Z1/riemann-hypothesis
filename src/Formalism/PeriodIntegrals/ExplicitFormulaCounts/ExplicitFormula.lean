import Formalism.PeriodIntegrals.ExplicitFormulaCounts.AnalyticInputs
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ZerosWindow
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019

theorem zerosWindow_closed : PI.ZerosWindow :=
  zerosWindow_of chk_lBoundRight chk_zetaBoundRight chk_lInvRight

theorem explicitFormula_closed : PI.ExplicitFormula :=
  explicitFormula_of zerosWindow_closed chk_discFactor chk_discLog chk_lBoundRight chk_zetaBoundRight
    chk_lInvRight
