import Formalism.FockGram.FockGramProofs.Bundle0002
import Formalism.FockGram.FockGramProofs.Bundle0001
import Mathlib
import Formalism.FockGram.StatementSymPos
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Positive

namespace Formalism.E

theorem fockHerm : FockHerm := fischerInnerConjSymm_holds

theorem subIndexNorm : SubIndexNorm := indexEqNormDet

theorem hermDual : HermDual := hermDual_of subIndexNorm

end Formalism.E
