import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PAmbChart
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PUnitaryInv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem LinChange.full : LinChange.Statement := LinChange.proof
theorem Radial.full : Radial.Statement := Radial.proof
theorem AmbChart.full : AmbChart.Statement := AmbChart.proof LinChange.full Radial.full
theorem AmbEq.full : AmbEq.Statement := AmbEq.proof AmbChart.full
theorem ChartIndep.full : ChartIndep.Statement := ChartIndep.proof AmbChart.full
theorem AmbUnitary.full : AmbUnitary.Statement := AmbUnitary.proof LinChange.full
theorem UnitaryInv.full : UnitaryInv.Statement := UnitaryInv.proof AmbEq.full AmbUnitary.full
theorem FormIntegral.full : FormIntegral.Statement := FormIntegral.proof ChartIndep.full
theorem PairMk.full : PairMk.Statement := PairMk.proof
theorem InnerSelf.full : InnerSelf.Statement := InnerSelf.proof
theorem Sesq.full : Sesq.Statement := Sesq.proof PairMk.full
theorem Orth.full : Orth.Statement := Orth.proof UnitaryInv.full PairMk.full
theorem Parseval.full : Parseval.Statement := Parseval.proof Orth.full Sesq.full InnerSelf.full
theorem Definite.full : Definite.Statement := Definite.proof Parseval.full InnerSelf.full

end FSInv

namespace CP

variable {N : ℕ}

end CP

end

end GroundTheory.Heights₂.Heights
