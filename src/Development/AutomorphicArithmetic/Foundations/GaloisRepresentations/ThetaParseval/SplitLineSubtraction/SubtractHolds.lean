import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle0003
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0830
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.WeilBound.CoreStatements.PublishedTheorems.HeckeLAdicCharacters.Outright
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity

namespace UpperTheory.Gal.TP.Sub

theorem pstOfDR : PstOfDR := pstOfDR_holds GlobalTheory.deRham_potentiallySemistable

theorem frobSub : FrobSub := frobSub_holds cpFacts_holds

theorem clConj : ClConj := clConj_holds cpFacts_holds contLeft_holds pstOfDR

theorem clSub : ClSub := clSub_holds frobSub sumDR_holds pstOfDR wDFacts_holds

theorem clTw : ClTw := clTw_holds frobSub twLoc_holds twJumps_holds pstOfDR wDFacts_holds contLeft_holds

theorem peelAll : PeelAll :=
  peelAll_holds (peelOne_holds dgFacts_holds cpFacts_holds eigTransfer_holds eigSum_holds splitLine_holds sSLeft_holds)
    contLeft_holds clConj clSub

theorem charEx : CharEx :=
  charEx_holds PositivityTheory.Stage1.PM.heckeLAdicCharacter charFrob_holds
    (charAbove_holds PositivityTheory.Stage1.PM.heckeLAdicCharacter HodgeLocalDeRhamField.HLdR.field_outright
      (UpperTheory.Lit.CharWD.algebraicCharacterWD GlobalTheory.globalArtinReciprocity_holds HodgeLocalDeRhamField.HLdR.field_outright GlobalTheory.deRham_potentiallySemistable) pstOfDR
      contLeft_holds) charInj_holds

theorem weakIso : WeakIso := weakIso_holds satAE_holds

theorem atPlace : AtPlace :=
  atPlace_holds charEx satAE_holds (frobId_holds (denseId_holds cpFacts_holds dgFacts_holds) cpFacts_holds) peelAll clTw
    clAway_holds contLeft_holds sSLeft_holds

theorem subtract_holds : Subtract := subtract_of atPlace splitEx_holds weakIso clConj

end UpperTheory.Gal.TP.Sub
