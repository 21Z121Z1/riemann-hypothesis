import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PPrimesLogSum
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.LineFIsHomogeneous
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Filter Topology

theorem KaPSplit.full : KaPSplit.Statement := KaPSplit.proof

theorem KaPInert.full : KaPInert.Statement := KaPInert.proof

theorem KaPBound.full : KaPBound.Statement := KaPBound.proof

theorem RestPBound.full : RestPBound.Statement := RestPBound.proof

theorem RestSummable.full : RestSummable.Statement := RestSummable.proof RestPBound.full

theorem HeightSumIdentity.full : HeightSumIdentity.Statement := HeightSumIdentity.proof

theorem ShTotIndependent.full : ShTotIndependent.Statement :=
  ShTotIndependent.proof ShOfPower.proof TotOfPower.proof DegPolyEval.proof CFlPos.proof

theorem ShTotInvertiblePair.full : ShTotInvertiblePair.Statement :=
  ShTotInvertiblePair.proof ShTotIndependent.full

theorem LimitsExist.full : LimitsExist.Statement :=
  LimitsExist.proof HeightSumIdentity.full ShTotInvertiblePair.full RestSummable.full

theorem HeightTauIdentity.full : HeightTauIdentity.Statement :=
  HeightTauIdentity.proof HeightSumIdentity.full RestSummable.full

theorem HeightEvaluation.full : HeightEvaluation.Statement := HeightEvaluation.proof HeightTauIdentity.full

theorem HeightLimitIdentity.full : HeightLimitIdentity.Statement :=
  HeightLimitIdentity.proof HeightTauIdentity.full ShFormula.full TotFormula.full

theorem CBounds.full : CBounds.Statement := CBounds.proof

theorem NormUbar.full : NormUbar.Statement := NormUbar.proof

theorem TermA.full : TermA.Statement := TermA.proof

theorem TermB.full : TermB.Statement := TermB.proof

theorem TermC.full : TermC.Statement := TermC.proof HeightLimitIdentity.full

theorem TermD.full : TermD.Statement := TermD.proof

theorem TheoremTUpper.full : TheoremTUpper.Statement :=
  TheoremTUpper.proof LimitsExist.full HeightEvaluation.full CBounds.full NormUbar.full TermA.full
    TermB.full TermC.full TermD.full PrimesLogSum.fullNat HomDecompExists.proof

theorem LimitTheorem.full : LimitTheorem.Statement := LimitTheorem.proof

theorem TheoremTLower.full : TheoremTLower.Statement := TheoremTLower.proof LimitTheorem.full

namespace EndSample

end EndSample

end GroundTheory.Heights₂.Heights.TheoremB
