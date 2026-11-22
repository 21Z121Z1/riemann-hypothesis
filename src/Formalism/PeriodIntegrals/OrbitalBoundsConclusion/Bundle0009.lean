import Formalism.PeriodIntegrals.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.TwChrOneMain
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryConjugation.Bundle0001
import Formalism.PeriodIntegrals.Bundle0012
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.Bundle0001
import Formalism.PeriodIntegrals.Bundle0013
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.WittUnramMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CauchyBinet.WwCauchyBinetMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.InfinitePadicComplex
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.Bundle0001

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwChrOne
section
theorem TwChrOne : PI.TwChrOne.TwChrOne := PI.TwChrOne.Pf.twChrOne_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UConjT
section
theorem unitary_conj_transpose : PI.UMultOne.ConjTranspose :=
  PI.UConjT.conjTranspose_of PI.UConjT.onbReal PI.UConjT.transferStep PI.UConjT.blockStep
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeakApproxDVR
section
theorem weak_approximation_dvr : PI.WeakApproxDVR :=
  PI.WA.weakApproxDVR_of PI.WA.big_existence_holds PI.WA.rho_projection_assembly
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittUnram
section
theorem witt_unramified : PI.WittUnram :=
  PI.WittUnramWork.wittUnram_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
section
theorem cauchy_binet_minors : PI.WwCauchyBinet.WwCauchyBinet := PI.WwCauchyBinetWork.wwCauchyBinet_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwMain
section
theorem minor_identity : PI.WwMain.WwMain :=
  PI.WwMainW.wwMain_of PI.WwMainW.evalH PI.WwMainW.lH PI.WwMainW.lLin
    (PI.WwMainW.deXCB_of PI.WwMainW.cbSorted)
end

