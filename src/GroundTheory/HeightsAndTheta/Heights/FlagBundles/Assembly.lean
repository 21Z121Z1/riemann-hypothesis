import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereHeightUniform
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereLongitudeCoordinates
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalHeightReduction
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreConstantClosedForm
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreIntegralInvariant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

theorem UnipotentLeadingMinor.full : UnipotentLeadingMinor.Statement :=
  UnipotentLeadingMinor.proof

theorem PluckerFrameChange.full : PluckerFrameChange.Statement :=
  PluckerFrameChange.proof

theorem GramSumOfMinors.full : GramSumOfMinors.Statement :=
  GramSumOfMinors.proof PluckerFrameChange.full

theorem OmitStepPolynomial.full : OmitStepPolynomial.Statement :=
  OmitStepPolynomial.proof

theorem LineQuotientDeterminant.full : LineQuotientDeterminant.Statement :=
  LineQuotientDeterminant.proof

theorem SectionLocalEquation.full : SectionLocalEquation.Statement :=
  SectionLocalEquation.proof

theorem DiagonalQuotient.full : DiagonalQuotient.Statement :=
  DiagonalQuotient.proof

theorem DiagonalLocalDVR.full : DiagonalLocalDVR.Statement :=
  DiagonalLocalDVR.proof DiagonalQuotient.full

theorem BlochOverlap.full : BlochOverlap.Statement :=
  BlochOverlap.proof

theorem SectionNormLog.full : SectionNormLog.Statement :=
  SectionNormLog.proof BlochOverlap.full

theorem GKernelIdentity.full : GKernelIdentity.Statement :=
  GKernelIdentity.proof

theorem MixedCoefficient.full : MixedCoefficient.Statement :=
  MixedCoefficient.proof

theorem ZonalKernel.full : ZonalKernel.Statement :=
  ZonalKernel.proof

theorem SphereLongitudeCoordinates.full : SphereLongitudeCoordinates.Statement :=
  SphereLongitudeCoordinates.proof

theorem ZonalHeightReduction.full : ZonalHeightReduction.Statement :=
  ZonalHeightReduction.proof SphereLongitudeCoordinates.full ZonalKernel.full

theorem ZonalKernelPairing.full : ZonalKernelPairing.Statement :=
  ZonalKernelPairing.proof

theorem ZonalBilinearFormula.full : ZonalBilinearFormula.Statement :=
  ZonalBilinearFormula.proof ZonalHeightReduction.full ZonalKernelPairing.full

theorem GHatIdentity.full : GHatIdentity.Statement :=
  GHatIdentity.proof GKernelIdentity.full

theorem FibreConstantClosedForm.full : FibreConstantClosedForm.Statement :=
  FibreConstantClosedForm.proof ZonalBilinearFormula.full GHatIdentity.full

theorem fibreConstant_eq (k : ℕ) :
    fibreConstant k = -(1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1) :=
  FibreConstantClosedForm.full.1 k

theorem FibreIntegralInvariant.full : FibreIntegralInvariant.Statement :=
  FibreIntegralInvariant.proof FibreConstantClosedForm.full

theorem CompactPairCurveForm.full : CompactPairCurveForm.Statement :=
  CompactPairCurveForm.proof

theorem BarCurveForm.full : BarCurveForm.Statement :=
  BarCurveForm.proof

theorem TorusInvariantDiagonal.full : TorusInvariantDiagonal.Statement :=
  TorusInvariantDiagonal.proof

theorem TopPowerDiagonal.full : TopPowerDiagonal.Statement :=
  TopPowerDiagonal.proof

theorem PolarisationDegreeD.full : PolarisationDegreeD.Statement :=
  PolarisationDegreeD.proof

end GroundTheory.Heights₂.Heights.FlagBundles
