import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmISymm
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSwapCycles
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0061
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Stokes
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvdOfForallEmultiplicityLe
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSegreChartFibreSum
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapAreaOne
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0112
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0125
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0131
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0123
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosPartLocal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0034

namespace GlobalTheory.CompanionTheory.Ar.Pub

open GroundTheory.Heights₂.Heights

theorem Seg.GoodChartDim : GroundTheory.Heights₂.Heights.GoodChartDim.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartDim.proof GroundTheory.Heights₂.Heights.ConeVanishingHomog.proof GroundTheory.Heights₂.Heights.ConeSliceIdeal.proof GroundTheory.Heights₂.Heights.ChartDehomogPrime.proof

theorem Seg.GoodChartModel : GroundTheory.Heights₂.Heights.GoodChartModel.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartModel.proof GroundTheory.Heights₂.Heights.GoodChartZeroSet.proof Seg.GoodChartDim

theorem Seg.PtsGenericCount : GroundTheory.Heights₂.Heights.PtsGenericCount.Statement :=
  @GroundTheory.Heights₂.Heights.PtsGenericCount.proof Seg.GoodChartModel GroundTheory.Heights₂.Heights.ComponentsGenericCount.proof GroundTheory.Heights₂.Heights.SheetLift.proof

theorem Seg.PtsSheetSimpleNull : GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.proof Seg.PtsGenericCount

theorem Seg.PtsSheetOnlyNull : GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.proof GroundTheory.Heights₂.Heights.CriticalFibreInfinite.proof

theorem Seg.PtsPosPartProjIndep : GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.proof Seg.PtsSheetSimpleNull Seg.PtsSheetOnlyNull GroundTheory.Heights₂.Heights.PtsPosPartLocal.proof GroundTheory.Heights₂.Heights.PtsPosDensMeasurable.proof

theorem Seg.PtsSegreChartFibreSum : GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof

theorem Seg.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem Seg.ConeSliceSheetParam : GroundTheory.Heights₂.Heights.ConeSliceSheetParam.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSliceSheetParam.proof Seg.DiscriminantSheetCover

theorem Seg.AreaFormulaInjSet : GroundTheory.Heights₂.Heights.AreaFormulaInjSet.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInjSet.proof GroundTheory.Heights₂.Heights.AreaFormulaLocal.proof

theorem Seg.AreaFormulaInj : GroundTheory.Heights₂.Heights.AreaFormulaInj.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInj.proof Seg.AreaFormulaInjSet

theorem Seg.ConeMapAreaOne : GroundTheory.Heights₂.Heights.ConeMapAreaOne.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapAreaOne.proof Seg.AreaFormulaInj

theorem Seg.ConeMapArea : GroundTheory.Heights₂.Heights.ConeMapArea.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapArea.proof Seg.ConeMapAreaOne

theorem Seg.ConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.proof Seg.ConeSliceSheetParam Seg.ConeMapArea

theorem Seg.SliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.SliceMassFinite.proof' Seg.ConeSheetGramLintegral GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionPerfect.coneDimOfChowForm_full

theorem Seg.SegreChartAbsIntegrable : GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.proof Seg.SliceMassFinite GroundTheory.Heights₂.Heights.SegreChartSheetCompare.proof

theorem Seg.PtsSemiPosMassFinite : GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.proof Seg.PtsPosPartProjIndep Seg.PtsSegreChartFibreSum Seg.SegreChartAbsIntegrable

theorem Seg.PtsPosDensIntegrable : GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.proof Seg.PtsSemiPosMassFinite

theorem Seg.PtsIntegralProjIndep : GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.proof Seg.PtsPosDensIntegrable Seg.PtsPosPartProjIndep

theorem Seg.PtsIntegralSegreChartProj : GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof Seg.SegreChartAbsIntegrable Seg.PtsSegreChartFibreSum

theorem Seg.SegreChartIntegral : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartIntegral.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SegreCoordGoodProj Seg.PtsIntegralProjIndep Seg.PtsIntegralSegreChartProj

theorem Seg.SegreChart : GroundTheory.Heights₂.Heights.SegreChart.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChart.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SegreChartDim Seg.SegreChartIntegral

theorem thmIExists (hPL : PoincareLelong) (hE : ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  have hInt : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement := ForSecondHalf.PtsIntegrable.of_resExists hE
  have hAbs : Inter.PtsAbsIntegrable.Statement :=
    Inter.PtsAbsIntegrable.proof hInt (Inter.PtsAbsMeasurable.proof hE)
  have hBil : PtsBilinear.Statement := PtsBilinear.proof hAbs PtsSumMeasurable.proof
  have hSt : ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement :=
    StokesStatement.of_found hBil HilbertSamuel.Closed.SegrePartition Seg.SegreChart
      AutoClose.StokesOnVariety
  have hLe : Inter.DeLeSemiPos.Statement :=
    Inter.DeLeSemiPos.proof hPL hSt (Inter.PtsAddFirst.proof hInt) (Inter.PtsRegLimit.proof hInt hAbs)
      (Inter.PtsMonoSemiPos.of_remaining hInt) Inter.RegCurvBound.full Inter.HorizNotMem.full
  have hPL2 : ReciprocityTheory.ChartRestriction.G.Geo.SectionSpaceSymmetry :=
    Inter.ProjectiveLineTwo.proof (Inter.DeSlotAdd.proof hE) Inter.SemiPosTwist.full hLe
  have hSwap : Inter.Swap.Statement := Inter.Swap.proof Inter.SwapCycles.full Inter.GeoNumCut.full hPL2
  have hRS : Inter.RPositionAdd.Statement := Inter.RPositionAdd.of_remaining hInt
  have hSymm : Inter.ThmISymm.Statement :=
    Inter.ThmISymm.proof hSwap hRS fibreComp
      (fun p _ K _ ι _ => Targets.ExistsUnique.full (ZMod p) ι)
      (fun p _ K _ ι _ => Targets.SymmStatement.of_type (ZMod p) ι)
      (fun K _ ι _ => GroundTheory.Heights₂.Heights.geoNumStatement ι)
  exact Inter.ThmIExists.proof AutoClose.Inter_R1Indep (Inter.RMul.proof hInt)
    (Inter.WellDefined.proof hSwap hRS) hSymm

end GlobalTheory.CompanionTheory.Ar.Pub
