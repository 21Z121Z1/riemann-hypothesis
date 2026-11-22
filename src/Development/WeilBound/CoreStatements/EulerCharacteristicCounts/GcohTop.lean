import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0001
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0003

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

theorem top_tate : Formalism.GaloisCohomology.LocalTateDualityK := tate_of gcRep gc0 gc1 gc2 gcField gcMu

theorem top_locfin : Formalism.GaloisCohomology.LocalFinitenessK := locfin_of gcField

end PositivityTheory.LocalTateOrthogonality.Gcoh
