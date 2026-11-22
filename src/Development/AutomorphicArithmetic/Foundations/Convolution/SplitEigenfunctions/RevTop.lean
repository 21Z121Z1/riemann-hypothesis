import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0004
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0006
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0007
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanZero
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianStandardVector
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0008
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0005
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Dens
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MomKill
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CoefPer

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

theorem maj_holds : Maj := maj latSum decE

theorem meanZero_holds : MeanZero := meanZero decE

theorem thetaConstantTerm_eq : ThetaLiftEqAnisotropicPart := f0Eq maj_holds thCont meanZero_holds (rank1 decE maj_holds orb1)

theorem rev_holds : Rev :=
  rev thetaConstantTerm_eq (coef maj_holds thCont) (thetaPairing_constantTerm_cuspidal maj_holds thCont thetaConstantTerm_eq (coef maj_holds thCont)) dens (fub maj_holds thCont)
    (coefPer decE maj_holds orbS momKill (orbFn orbS))

end UpperTheory.ConvolutionTheory.RankTwoDescent
