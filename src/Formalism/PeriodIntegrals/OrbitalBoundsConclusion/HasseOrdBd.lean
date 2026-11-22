import Formalism.PeriodIntegrals.HasseOrdBd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.Bundle0001

theorem hasse_order_bound : PI.HasseOrdBd :=
  PI.HasseOrdBdW.hasseOrdBd_of PI.HasseOrdBdW.compositionalInverseSymm PI.HasseOrdBdW.orthogonalSplitPolarizationVanishes PI.HasseOrdBdW.addPreservesExpCongruence
    PI.HasseOrdBdW.expCongruenceExtendsToSum
