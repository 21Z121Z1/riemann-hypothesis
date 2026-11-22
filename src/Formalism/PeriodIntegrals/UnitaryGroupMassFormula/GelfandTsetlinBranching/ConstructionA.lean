import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFactsProofA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FixedLineProofA

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem extremalFacts_of (_h : PI.HwIrred) : ExtremalFacts :=
  extremalFacts_proof_A

theorem fixed_line_exists : FixedLine :=
  fixedLine_proof_A

end PI.WGB
