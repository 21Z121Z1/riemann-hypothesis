import Formalism.PeriodIntegrals.Bundle0023
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.SiegelMeasureDefinition
import Mathlib
import Formalism.PeriodIntegrals.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramDifferenceRenaming.SDiffGramMain
import Formalism.PeriodIntegrals.Bundle0006
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.SigmaStarEx
import Formalism.PeriodIntegrals.Bundle0010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.TwistedEisensteinOfRemaining
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.TestFunctionPeriodicity

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK
section
theorem quotient_product_compact : PI.QuotProdK.QuotProdK :=
  QPK.quotProdK_of QPK.weil_quotient_global_assumptions QPK.haar_measure_uniqueness
    (QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition QPK.bruhat_decomposition'
      QPK.local_weil_representation)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SDiffGram
section
namespace PI.Final.SDiffGram

theorem s_difference_gram : PI.SDiffGram.SDiffGram := PI.UnitaryGroupMassFormula.SDiffGram.sDiffGram_main

end PI.Final.SDiffGram
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarEx
section
theorem sigma_star_exists : PI.SigmaStarEx := PI.SSE.sigmaStarEx
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCover
section
theorem transference_covering : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
section
theorem transference_successive_minima : PI.TransferenceMinima :=
  PI.Tr.transferenceMinima_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwistedEisensteinNonvanishing
section
theorem TwistedEisensteinNonvanishing : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing :=
  PI.TwistedEisensteinNonvanishing.W.twisted_eisenstein_of_remaining PI.TwistedEisensteinNonvanishing.W.test_function_support PI.TwistedEisensteinNonvanishing.W.test_function_periodicity PI.TwistedEisensteinNonvanishing.W.bounded_matrix_entries
end

