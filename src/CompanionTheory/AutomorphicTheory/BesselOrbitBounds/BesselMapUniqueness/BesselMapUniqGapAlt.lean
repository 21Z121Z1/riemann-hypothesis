import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.Bundle0001
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.OrbitMult
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0035
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0037
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0036
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.ProdNormLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0038

namespace CompanionTheory.Bmu

theorem bounded : Bounded :=
  bounded_of (GlobalTheory.T.quotient_bound_of_factor_reduce_chart GlobalTheory.T.factorization' (GlobalTheory.T.reduction_of_derived_series GlobalTheory.T.DerivedSeriesLinear GlobalTheory.T.DerivedSeriesAdjoint GlobalTheory.T.DerivedSeriesDerivation) GlobalTheory.T.ChartExistence)
    (absBound_of GlobalTheory.T.factorization' GlobalTheory.T.DerivedSeriesAdjoint GlobalTheory.T.DerivedSeriesDerivation (GlobalTheory.T.word_length_bound_of_linear GlobalTheory.T.DerivedSeriesLinear)) GlobalTheory.T.AdaptedBasisExistsAlt
    (GlobalTheory.T.decomposition_of_iwasawa_levi_cartan GlobalTheory.T.AdaptedBasisExistsAlt GlobalTheory.T.IwasawaDecomposition GlobalTheory.T.LeviDecomposition GlobalTheory.T.CartanDecomposition) GlobalTheory.T.torBound' GlobalTheory.T.SpanGenerators
    GlobalTheory.T.ExponentialMembership GlobalTheory.T.RootVectors

theorem besselMapUniqGap : BesselMapUniqGap :=
  uniq_of bounded (GlobalTheory.T.truncated_derivation_limit GlobalTheory.T.factorization' GlobalTheory.T.TruncatedDerivation) GlobalTheory.T.TorusConjugacy GlobalTheory.T.DerivedSeriesAdjoint GlobalTheory.T.factorization'

end CompanionTheory.Bmu
