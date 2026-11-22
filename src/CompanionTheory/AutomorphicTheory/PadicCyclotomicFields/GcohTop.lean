import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.Bundle0002
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.Bundle0001
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.Bundle0003

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

theorem top_tate : Formalism.GaloisCohomology.LocalTateDualityK := tate_of gcRep gc0 gc1 gc2 gcField gcMu

theorem top_locfin : Formalism.GaloisCohomology.LocalFinitenessK := locfin_of gcField

end CompanionTheory.LocalTateOrthogonality.Gcoh
