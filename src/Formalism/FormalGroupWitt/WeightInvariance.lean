import Formalism.FormalGroupWitt.FormalGroupWittProofs.Bundle0001
import Formalism.FormalGroupWitt.FormalGroupWittProofs.GroupV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.FunctionalEquationHomVector
import Formalism.FormalGroupWitt.FormalGroupWittProofs.CongrV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.ShiftAsm
import Formalism.FormalGroupWitt.FormalGroupWittProofs.HeightV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.Bundle0003

namespace Formalism.FG

universe u v w

theorem addLawExample : AddLawExample := additive_law_example
theorem notLawExample : NotLawExample := not_a_law_example
theorem funEqHomV : FunEqHomV.{u, v, w} := functional_equation_hom_vector

end Formalism.FG
