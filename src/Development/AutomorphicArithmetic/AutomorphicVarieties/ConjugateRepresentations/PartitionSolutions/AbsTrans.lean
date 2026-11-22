import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0002

namespace UpperTheory.V.Cj

theorem A.absTrans : A.AbsTrans :=
  A.absTrans_of A.hdFacts A.zigFwd A.zigBwd A.bwdLast A.zigFormal A.pullOp A.pullAct A.zigMap A.coverEx A.satClosed A.satFacts

theorem partA : PartA := A.partA_of A.absTrans A.suppFwd A.suppBwd A.levCorr

end UpperTheory.V.Cj
