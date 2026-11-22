import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembership
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVSmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecKapMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalK
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssembly
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGeneration

namespace PositivityTheory.RgEis.MG

theorem mirGen : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen :=
  fun hS hG hB hC hM hT hSph =>
    have hO := _root_.GlobalTheory.CompanionTheory.MirSides.sideOf hG hB
    have hZ := _root_.GlobalTheory.CompanionTheory.ZetaAlongK.zetaK hC
    _root_.GlobalTheory.CompanionTheory.EisMir.mirGen_of_core hS hSph _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem (_root_.GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem) hO (_root_.GlobalTheory.CompanionTheory.EisTestK.testK hG hB hT)
      (_root_.GlobalTheory.CompanionTheory.EisCore.wall_core hM _root_.GlobalTheory.CompanionTheory.RgEisDGood.dGood (_root_.GlobalTheory.CompanionTheory.RgEisMG.master _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem _root_.GlobalTheory.CompanionTheory.RgEisDGood.dGood _root_.GlobalTheory.CompanionTheory.RgEisHGood.hGood _root_.GlobalTheory.CompanionTheory.RgEisLeft.bGood) hO _root_.GlobalTheory.CompanionTheory.RgEisTerm.term hZ
        (_root_.GlobalTheory.CompanionTheory.RgEisSide.sideUnfold hC (_root_.GlobalTheory.CompanionTheory.RgEisUnfold.unfold hS _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem) _root_.GlobalTheory.CompanionTheory.RgEisLines.lines _root_.GlobalTheory.CompanionTheory.RgEisTerm.term hZ) (_root_.GlobalTheory.CompanionTheory.RgEisSide.sideConv hC hSph _root_.GlobalTheory.CompanionTheory.RgEisLines.lines _root_.GlobalTheory.CompanionTheory.RgEisTerm.term) (_root_.GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain hM))

end PositivityTheory.RgEis.MG
