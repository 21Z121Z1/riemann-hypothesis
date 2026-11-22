import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AdaptExists
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecomposition
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0027
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ChartExistence
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfIwasawaLeviCartan
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0029

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AdaptExistsStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.AdaptedBasisExistsAlt : AdaptExists := by
  first | exact @GlobalTheory.CompanionTheory.BmuAdapt.adaptExists | exact GlobalTheory.CompanionTheory.BmuAdapt.adaptExists | (intros; apply GlobalTheory.CompanionTheory.BmuAdapt.adaptExists <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CartanDecomposition : CartanQ := by
  first | exact @GlobalTheory.CompanionTheory.BesselCartan.cartanQ | exact GlobalTheory.CompanionTheory.BesselCartan.cartanQ | (intros; apply GlobalTheory.CompanionTheory.BesselCartan.cartanQ <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplittingStatement
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CasimirSplitting : CasSplit := by
  first | exact @GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit | exact GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit | (intros; apply GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ChartExistenceStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ChartExistence : ChartExists := by
  first | exact @GlobalTheory.CompanionTheory.ProdExChart.chartExists | exact GlobalTheory.CompanionTheory.ProdExChart.chartExists | (intros; apply GlobalTheory.CompanionTheory.ProdExChart.chartExists <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBoundStatement
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CountingBound : Count := by
  first | exact @GlobalTheory.CompanionTheory.ZuckCount.count | exact GlobalTheory.CompanionTheory.ZuckCount.count | (intros; apply GlobalTheory.CompanionTheory.ZuckCount.count <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfIwasawaLeviCartanStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_of_iwasawa_levi_cartan : AdaptExists → IwaQ → LeviQ → CartanQ → Decomp := by
  first | exact @GlobalTheory.CompanionTheory.BmuDecomp.decomp | exact GlobalTheory.CompanionTheory.BmuDecomp.decomp | (intros; apply GlobalTheory.CompanionTheory.BmuDecomp.decomp <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLawsStatement
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_of_tensor_from_hom_laws : HomCat → MatHom → TensHom → HomLie → OKTriv → DecTens := by
  first | exact @GlobalTheory.CompanionTheory.ZuckDecTens.decTens | exact GlobalTheory.CompanionTheory.ZuckDecTens.decTens | (intros; apply GlobalTheory.CompanionTheory.ZuckDecTens.decTens <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTraceStatement
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DecompositionOfTrace : DecOfTrace := by
  first | exact @GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace | exact GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace | (intros; apply GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesAdjointStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DerivedSeriesAdjoint : DsAd := by
  first | exact @GlobalTheory.CompanionTheory.BmuDsAd.dsAd | exact GlobalTheory.CompanionTheory.BmuDsAd.dsAd | (intros; apply GlobalTheory.CompanionTheory.BmuDsAd.dsAd <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesDerivationStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DerivedSeriesDerivation : DsDer := by
  first | exact @GlobalTheory.CompanionTheory.BmuDsDer.dsDer | exact GlobalTheory.CompanionTheory.BmuDsDer.dsDer | (intros; apply GlobalTheory.CompanionTheory.BmuDsDer.dsDer <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesLinearStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DerivedSeriesLinear : DsLin := by
  first | exact @GlobalTheory.CompanionTheory.BesselMapSm.dsLin | exact GlobalTheory.CompanionTheory.BesselMapSm.dsLin | (intros; apply GlobalTheory.CompanionTheory.BesselMapSm.dsLin <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsFactorStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorization' : Factor := by
  first | exact @GlobalTheory.CompanionTheory.BmuFactor.factor | exact GlobalTheory.CompanionTheory.BmuFactor.factor | (intros; apply GlobalTheory.CompanionTheory.BmuFactor.factor <;> assumption)
end

