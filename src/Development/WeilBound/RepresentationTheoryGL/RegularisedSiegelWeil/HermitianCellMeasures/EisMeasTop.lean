import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralLeOfMinor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0766
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0685
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0826
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0704
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisMeas

namespace PositivityTheory.Rg.Rsw.Em

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

theorem eisMeas : IdemEx → BumpEx → Major → FixW → FixTh → ThProd → MuCell → FibEx → RCell → PosExt → ApproxId → EisMeas :=
  fun hI hB hM hW hT hP hC hF hR hE hA =>
  have hX := GlobalTheory.CompanionTheory.RswEmTop.topX
  have hRi := GlobalTheory.CompanionTheory.AlgRich.algRich hI hB hX
  have hS := GlobalTheory.CompanionTheory.SigL.main hI hX
  GlobalTheory.CompanionTheory.EisE.eisMeas hI hB hM hW hT hP hC hF hR hX hRi hS
    (GlobalTheory.CompanionTheory.OrbExist.orbEx hI hA (GlobalTheory.CompanionTheory.EisDens.dens_main hE) hX hRi (GlobalTheory.CompanionTheory.AlgStab.algStab hI) hS (GlobalTheory.CompanionTheory.HermSc.hermScale_main hI hX))

end PositivityTheory.Rg.Rsw.Em
