import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0018

namespace Formalism.L2.Th1.H

theorem kappaExists : KappaExists := unit_det_root_of_unity

theorem quadraticSemicharacters_of_localStandard (hL : LocalStandard) : quadraticSemicharacterIdentityReformulated := quadraticSemicharacters_of_fact hL kappaExists

end Formalism.L2.Th1.H
