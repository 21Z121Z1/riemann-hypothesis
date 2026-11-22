import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0007
import Development.WeilBound.ThetaLifts.CartanFactorisation.KillInf
import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0008
import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0009
import Development.WeilBound.ThetaLifts.CartanFactorisation.RealTrans
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0002
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
import Development.WeilBound.CoreStatements.LocalThetaKernels.Bundle0003
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0005
import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0002
import Development.WeilBound.ThetaLifts.CartanFactorisation.CuspidalClassOfWeilConvergence
import Development.WeilBound.ThetaLifts.FrameEstimates.WeilConv
import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairU
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0004
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0005

noncomputable section

namespace PositivityTheory.ThKF

open GlobalTheory.ThK

theorem iLeft (hT : ThetaBasic) : ILeft := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp _ hΦ g =>
  I_left unimodularity_holds hT hp hΦ g

theorem kCoinv (h : KP) : KCoinv := PositivityTheory.KCo.kCoinv_of_dict h.base.bernsteinUnitaryProductIrreducible PositivityTheory.KCo.dictionary_statement

end PositivityTheory.ThKF

end
