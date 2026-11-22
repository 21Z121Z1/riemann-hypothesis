import Development.WeilBound.CoreStatements.RegularisedThetaMirabolic.CuspidalMirabolic.CuspidalRestrictsToInduced
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026

namespace PositivityTheory.Mirab

theorem cuspidalMirabolic : GlobalTheory.Published.CuspidalMirabolic :=
  ⟨GlobalTheory.CompanionTheory.Hypotheses₂.cuspidalExists_holds, PositivityTheory.Mirab.Restr.cuspidalRestrictsToInduced⟩

end PositivityTheory.Mirab
