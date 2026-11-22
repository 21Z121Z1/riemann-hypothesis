import Development.WeilBound.CoreStatements.VolumeEquality.DegPushAsm
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0008
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPullB
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushUnit
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0013
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0010
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0015
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFib
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0014
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMass
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0009
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMuLink

namespace SheetDecomposition

theorem degPush : DegPush :=
  have hEq : NumEq := numEq ptDim numPull (unitZero ptDim)
  degPush_of hEq (geoPF ptDim) (fibNum hEq) trdegU testRelabel geoTest numMap muMass fieldJoin genIso
    (fibLink chartVal centre coordLat) (muLink chartVal centre coordLat)

end SheetDecomposition
