import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.Bundle0002
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.LocalToAdelic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013

namespace PositivityTheory.EqVol

theorem indexEq : IndexEq := indexEq_of (coSA saOpen) divisible

theorem levelIndexEq : LevelIndexEq :=
  levelIndexEq_of indexEq (levelCO hatCompactOpen) levelConj (levelRat hatRat)

end PositivityTheory.EqVol
