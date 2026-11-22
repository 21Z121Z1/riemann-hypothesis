import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0013
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PairDoubleCosetFiniteSupport
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0008
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.IsOpenChiMu
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0007
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0011
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PCandSb
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0012
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.ReadingModuleHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.ReadSplitOfJoin
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.LocOp3
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandPlug
section
namespace PositivityTheory.Rg.BcB.F.CandPlug

open PositivityTheory.Rg.BcB.F

theorem readT : Tail.ReadT := Tail.rReadT RS.reading_module_holds
theorem expRead : Tail.ExpRead := Tail.rExpRead PositivityTheory.Rg.BcB.N3.Final.n3
theorem readLev : Tail.ReadLev := GlobalTheory.T.real_read_levi RS.reading_module_holds RS.join_module_holds
theorem readS : Tail.ReadS := Tail.rReadS_c RS.reading_module_holds RS.join_module_holds PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3

theorem candT : CandT := fun hR E _ _ _ hE n _ π _ S T F₀ F _ i s₁ s₂ Pa Pb D A G hc hG hl hne w hw hu hs =>
  PCandLh.inert_d readT expRead RS.joinSat_holds hR E hE n π S T F₀ F i s₁ s₂ Pa Pb D A G hc hG hl hne w (F.T_le w hw hu hs)

theorem candTOut : CandTOut :=
  candTOut_of (candS_of readS) candT (PCandLh.candLev_of readLev readT expRead RS.joinSat_holds)

end PositivityTheory.Rg.BcB.F.CandPlug
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandTOutHolds2
section
namespace PositivityTheory.Rg.BcB.F

theorem candTOut_holds2 : CandTOut :=
  candTOut_of (candS_of (Tail.rReadS_c RS.reading_module_holds RS.join_module_holds fun E _ _ _ => PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 E))
    (candT_of (Tail.rReadT RS.reading_module_holds) (Tail.rExpRead' N3.Final.n3) RS.joinSat_holds)
    (PCandLh.candLev_of (GlobalTheory.T.real_read_levi RS.reading_module_holds RS.join_module_holds) (Tail.rReadT RS.reading_module_holds)
      (Tail.rExpRead' N3.Final.n3) RS.joinSat_holds)

end PositivityTheory.Rg.BcB.F
end

