import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodsOnLineOfInvLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankInvFunBranch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodsInvariantFunctional

open GlobalTheory.RowClaim GlobalTheory.RowReal

theorem GlobalTheory.RowReal.periodsOnLine_big : Big fun ch => PeriodsOnLine ch :=
  big_mono (fun ch h => periodsOnLine_of_invLine GlobalTheory.OneFunctional.oneLine ch h) _root_.GlobalTheory.RowReal.invLine_big
