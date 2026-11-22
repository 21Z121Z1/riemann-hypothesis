import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0006
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDesc
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0007
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0008

theorem UpperTheory.ConvolutionTheory.T.cbcc_of_core (hC : UpperTheory.ConvolutionTheory.CI) (hG : UpperTheory.ConvolutionTheory.GM.GM) : UpperTheory.V.Z.Bc.CBCc :=
  have a := liftStep (coreLift hC hG)
  have b := liftAll a
  have c := descStep (coreDesc hC hG) b
  cbcc places a b c (splitStrong c)
