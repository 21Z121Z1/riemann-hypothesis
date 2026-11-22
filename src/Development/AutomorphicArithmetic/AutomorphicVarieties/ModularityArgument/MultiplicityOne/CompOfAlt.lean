import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.Bundle0002
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F

theorem UpperTheory.V.Z.Mult.compOf' (hW : UpperTheory.V.Z.Tf.GaloisFromTraceFormula.GalWeak 4) : UpperTheory.V.Z.Mult.CompOf :=
  UpperTheory.V.Z.Mult.compOf (Desc.bcOut_of_N UpperTheory.BaseChangeIdentities.baseChangeN Rig.weightEx (Rig.rThetaN Rig.strSat)) hW
