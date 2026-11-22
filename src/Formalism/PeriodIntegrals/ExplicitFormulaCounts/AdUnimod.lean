import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0032
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.Bundle0002

theorem adUnimod_closed : PI.AdUnimod :=
  PI.WAU.adUnimod_of PI.WAU.kg_subgroup PI.WAU.maximal_compact_isCompact PI.WAU.compact_countable PI.adelic_index_eq
