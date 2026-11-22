import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0008
import Development.WeilBound.CoreStatements.VolumeEquality.BallVolStdZ
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0013
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0007

namespace SheetDecomposition

theorem famVol : FamVol := famVol_of moebVol (stdModel_of stdZ) arithIdx levelDict

theorem ballVolEq : BallVolEq := ballVolEq_of famVol

end SheetDecomposition
