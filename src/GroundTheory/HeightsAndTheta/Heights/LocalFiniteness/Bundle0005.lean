import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelGrowthOffHypersurfacePolynomial
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0102
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0122
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0119
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBundleRadicalAway
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0104
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0083
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTransverseSliceGeneral
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0134
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0026
import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalLength.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalFlat

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFiniteRank.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFiniteRank.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.FibreFinite.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFinite GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocFrac.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpExcessDrop.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpExcessDecreases.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpExcessDecreases.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.ExcessPositive.full GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualCompare GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ExceptionalCompare

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadStep : GroundTheory.Heights₂.Heights.Model.SpreadStep.Statement :=
  @GroundTheory.Heights₂.Heights.Model.SpreadStep.proof GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadIsoLoc GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadGlue

theorem GroundTheory.Heights₂.Heights.AutoClose.CutOffLimit : GroundTheory.Heights₂.Heights.CutOffLimit.Statement :=
  @GroundTheory.Heights₂.Heights.CutOffLimit.of_open GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SheetImageAreaSet GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass

theorem GroundTheory.Heights₂.Heights.AutoClose.StokesOnVariety : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement :=
  @GroundTheory.Heights₂.Heights.StokesOnVariety.of_open GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SheetImageAreaSet GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.KleimanFibreHilbertFlat
section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.BranchImageNhdOffCentre : GroundTheory.Heights₂.Heights.BranchImageNhdOffCentre.Statement :=
  @GroundTheory.Heights₂.Heights.BranchImageNhdOffCentre.proof GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffCentre

theorem GroundTheory.Heights₂.Heights.AutoClose.CurveCoordinateGraph : GroundTheory.Heights₂.Heights.CurveCoordinateGraph.Statement :=
  @GroundTheory.Heights₂.Heights.CurveCoordinateGraph.proof GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffCentre
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjRegularDens
section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.MahlerSectionOfConst : GroundTheory.Heights₂.Heights.MahlerSectionOfConst.Statement :=
  @GroundTheory.Heights₂.Heights.MahlerSectionOfConst.proof GroundTheory.Heights₂.Heights.AutoClose.DefectAverage GroundTheory.Heights₂.Heights.AutoClose.AdmissibleAENrm GroundTheory.Heights₂.Heights.BallVolume.proof
end

