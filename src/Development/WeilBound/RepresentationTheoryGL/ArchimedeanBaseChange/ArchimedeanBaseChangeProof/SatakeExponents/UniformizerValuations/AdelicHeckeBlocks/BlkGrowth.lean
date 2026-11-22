import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.WdValAppend
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.RStabApply
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IntegrableCut

namespace PositivityTheory.Rg.BcB.F.BlockFiniteConvolution

open PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.D1

theorem finConv' : FinConv := finConv intHint hintProd slots

theorem fmAlg' : FmAlg := fmAlg finConv' slots

theorem fmTr' : FmTr := fmTr slots

theorem rtAlg' : RtAlg := rtAlg sizeBasic

theorem adelRep' : AdelRep := adelRep fmAlg' fmTr' rtAlg'

theorem blkOp' (h : MultAlg) : BlockOperatorsProductAdjoint := blkOp E1.opEx_holds h tensTest tensMul

theorem blkComm' (h : MultAlg) : BlockPureTensorsCommute := blkComm E1.opEx_holds h tensTest tensMul

theorem blkWord' (h : MultAlg) : BlockWordOperators := blkWord (blkOp' h)

theorem pTTest' (h : KerEx) : PTTest := pTTest regOf finConv' fmTr' h

theorem blkGrowth' (h : MultAlg) (h' : D4.EllFormula2J) : BlockEllipticGrowth := blkGrowth (blkOp' h) (blkWord' h) blkSum (ellLin h')

end PositivityTheory.Rg.BcB.F.BlockFiniteConvolution
