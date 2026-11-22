import ReciprocityTheory.SemistableReduction.SemiDeg
import ReciprocityTheory.SemistableReduction.Bundle0019
import ReciprocityTheory.SemistableReduction.Bundle0029

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem semiPoint : SemiPointStatement := semiDeg_holds degAdd

theorem semistable : SemistableStatement := semiContract_holds semiPoint degAdd

end ReciprocityTheory.MultiplicativeHeights.Closed
