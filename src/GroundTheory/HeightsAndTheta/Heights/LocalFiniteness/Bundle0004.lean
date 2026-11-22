import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelGrowthOffHypersurfacePolynomial
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0083
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PUnbranchedPartConnected
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0100
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0112
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0089
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0113
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0126
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.IsolatedPointsCountPrime
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0125
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0048
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosPartLocal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0027

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelUnbranchedPartConnected
section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFinite.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFinite.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFinite.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalIntegral GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_LocalIntegralClosureFinite GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocNoetherian

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalFlat.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalFlat.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalFlat.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConePolyLocalization

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_DivCycleHomLoc.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualCompare.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ResidualComparison.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ResidualComparison.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces GroundTheory.Heights₂.Heights.NumbersDVR.ResidualDisjoint.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualContraction

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadIsoLoc : GroundTheory.Heights₂.Heights.Model.SpreadIsoLoc.Statement :=
  @GroundTheory.Heights₂.Heights.Model.SpreadIsoLoc.proof GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadHomLoc GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadHomInjLoc

theorem GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement :=
  @GroundTheory.Heights₂.Heights.TubeEuclMass.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.TubeCollarMass GroundTheory.Heights₂.Heights.AutoClose.TubeDeepMass
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.RegularLocusIdentityHolds
section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadicalAway : GroundTheory.Heights₂.Heights.GenericFibreRadicalAway.Statement :=
  @GroundTheory.Heights₂.Heights.GenericFibreRadicalAway.proof GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadical

theorem GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffCentre : GroundTheory.Heights₂.Heights.CurveRegularOffCentre.Statement :=
  @GroundTheory.Heights₂.Heights.CurveRegularOffCentre.proof GroundTheory.Heights₂.Heights.CurveGermComponents.proof GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffFinite GroundTheory.Heights₂.Heights.CurveProperClosedFinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LengthTransverseSlice : GroundTheory.Heights₂.Heights.LengthTransverseSlice.Statement :=
  @GroundTheory.Heights₂.Heights.LengthTransverseSlice.proof GroundTheory.Heights₂.Heights.AutoClose.CMLengthParameters GroundTheory.Heights₂.Heights.LocalizeQuotientStages.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.CMGeneralPoint : GroundTheory.Heights₂.Heights.CMGeneralPoint.Statement :=
  @GroundTheory.Heights₂.Heights.CMGeneralPoint.proof GroundTheory.Heights₂.Heights.AutoClose.CMLocusOpen

theorem GroundTheory.Heights₂.Heights.AutoClose.UniformiserBranchSimpleZero : GroundTheory.Heights₂.Heights.UniformiserBranchSimpleZero.Statement :=
  @GroundTheory.Heights₂.Heights.UniformiserBranchSimpleZero.proof GroundTheory.Heights₂.Heights.AutoClose.UniformiserLocallyInjective GroundTheory.Heights₂.Heights.InjectiveHolomorphicDerivNeZero.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.CMHeightOneGeneral : GroundTheory.Heights₂.Heights.CMHeightOneGeneral.Statement :=
  @GroundTheory.Heights₂.Heights.CMHeightOneGeneral.proof GroundTheory.Heights₂.Heights.AutoClose.CMLocusOpen

theorem GroundTheory.Heights₂.Heights.AutoClose.regular_locus_identity_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularLocusIdentity.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularLocusIdentity.proof GroundTheory.Heights₂.Heights.AutoClose.regular_off_hypersurface_holds
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjGenericRank
section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.PtsPosPartProjIndep : GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.proof GroundTheory.Heights₂.Heights.AutoClose.PtsSheetSimpleNull GroundTheory.Heights₂.Heights.AutoClose.PtsSheetOnlyNull GroundTheory.Heights₂.Heights.PtsPosPartLocal.proof GroundTheory.Heights₂.Heights.PtsPosDensMeasurable.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.DefectAverage : GroundTheory.Heights₂.Heights.DefectAverage.Statement :=
  @GroundTheory.Heights₂.Heights.DefectAverage.proof GroundTheory.Heights₂.Heights.AutoClose.MahlerAverageSplit GroundTheory.Heights₂.Heights.AutoClose.CycleAverage

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.proof GroundTheory.Heights₂.Heights.AutoClose.ConeSliceSheetParam GroundTheory.Heights₂.Heights.AutoClose.ConeMapArea
end

