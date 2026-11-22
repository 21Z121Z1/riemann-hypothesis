import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PClassMean
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PMeanOverEmbeddings
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PLevelOneQExpansion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian

theorem KroneckerLimit.full : KroneckerLimit.Statement :=
  KroneckerLimit.proof KroneckerSplit.proof PowerIntegral.proof ShiftedSumIntegral.proof
    CotangentSum.proof LogEta.proof GammaZetaLimit.proof

theorem PhTau.full : PhTau.Statement :=
  PhTau.proof DeltaEta.proof

theorem ClassMean.full {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]
    (S : PrimeDiscriminant K) : ClassMean.Statement S :=
  ClassMean.proof S KroneckerLimit.full (ClassEpstein.proof S) (ZetaFactor.proof S) PhTau.full
    PhScale.proof

section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
