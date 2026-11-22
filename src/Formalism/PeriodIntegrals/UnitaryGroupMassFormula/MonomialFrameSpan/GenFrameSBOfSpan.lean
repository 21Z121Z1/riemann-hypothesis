import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.Bundle0002

namespace GenFrameSpan

theorem stepSat : StepSat := stepSat_of projZ

theorem genFrameSB_of_span (hs : StepSpan) : CutKW.KWsb := genFrameSB_of stepBack hs stepSat

end GenFrameSpan
