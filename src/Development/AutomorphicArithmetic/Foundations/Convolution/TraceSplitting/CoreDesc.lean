import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0004
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0005
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0006
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T in
theorem UpperTheory.ConvolutionTheory.T.coreDesc :
    UpperTheory.ConvolutionTheory.CI → UpperTheory.ConvolutionTheory.GM.GM → UpperTheory.ConvolutionTheory.T.CoreDesc :=
  coreDesc_of absLast pullBack unitTrace oneTerm sideSum pickS pickInf tyEx termE goodEx places C.occursBasics L1.eigBasic
