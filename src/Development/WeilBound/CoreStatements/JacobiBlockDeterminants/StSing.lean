import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.DetInvNe
import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.Bundle0001
import Development.WeilBound.CoreStatements.MultihomogeneousSquares.Bundle0002
import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SameOrbitTrans

theorem HeightCancellation.stSing : SquareStatements.StSing :=
  SquareStatements.Sing.stSing_of SquareStatements.Sing.c0 HeightCancellation.G.c1 HeightCancellation.c2 SquareStatements.Sing.c5 HeightCancellation.G.c3w HeightCancellation.G.c3o HeightCancellation.c4
