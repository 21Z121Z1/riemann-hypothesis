import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RUEval
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RFamMatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.EvaluationCombinedTestFunction
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.NormTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.SatComb
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm PositivityTheory.Rg.BcB.G8

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem cuspReadI : CuspReadI :=
  cuspReadI_of levShrink (cuspCaseJ cuspMem cuspFin normTw normUniq satComb absInf mtoLaws)
    (ctCaseJ (stepT (iwaT levShrink typeSat) sliceT stabT) splitLim satComb cdAddG absInf mtoLaws)

theorem asmTh : AsmTh :=
  asmTh_of (rChoice places levelFn regFn) (fun h => rUEval h places exAct splitLine inertLine uConj)
    (fun h1 h3 => rFamMatch h1 h3 places exAct exHecke2 ctEx muConj) ends (twDataT cdAddG muInf mwAt dualWt) (regOf mwAt dualWt)
    unStable muInf (csdInert GOne.csdSat) (rSep places) regCt trAvg places

theorem runTh_of (hU : GlobalTheory.BCT.USide) (hG : G2s) (hM : MuEx) (h1 : MatchUnit) (h3 : MatchSplit) (hS : StUnit) (hE : EndoBlockG)
    (hB : StableBlockG) : RunTh :=
  asmTh hU hG hM h1 h3 (endoS (enlarge hS hecke_eigenvalues_unitary_one_factor unitary_one_characters_separated_by_eigenvalues places) places hE) (stableS (enlarge hS hecke_eigenvalues_unitary_one_factor unitary_one_characters_separated_by_eigenvalues places) places hB)

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
