import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.DivisionOneGeometricRepresentation
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.SeedFinOddOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0005
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSatConj

namespace UpperTheory.Gal.Int.Div

theorem seedFinOdd_of_geoOne (h : UpperTheory.Gal.Int.Geo.GeoOne) : GlobalTheory.CongL.SeedFinOdd :=
  seedFinOdd_of divAll_holds cplMem_of (sameOr_of cplMem_of) (satConj_of locIso_of) (tyConj_of locIso_of) (lacConj_of cplMem_of)
    gapLac_of dGenMul_of h

end UpperTheory.Gal.Int.Div
