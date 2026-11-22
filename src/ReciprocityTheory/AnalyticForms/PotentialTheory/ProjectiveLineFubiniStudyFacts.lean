import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0009
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0011
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

namespace ReciprocityTheory.AnForm.M

theorem layerM :
    IsPotentialAddStatement ∧
    IsPotentialZsmulStatement ∧
    IsPotentialRsmulStatement ∧
    IsPotentialPullbackStatement ∧
    IsPshAddStatement ∧
    IsPshRsmulStatement ∧
    PshShiftStatement ∧
    RegularAtlasStatement ∧
    SNCInducedAtlasStatement ∧
    ExistsPartitionStatement ∧
    LocDensBaseStatement ∧
    LocDensContStatement ∧
    LocDensChartStatement ∧
    IntegralWithIndepStatement ∧
    MIntEqStatement ∧
    MIntAtlasIndepStatement ∧
    MIntegrableContStatement ∧
    MIntSymmStatement ∧
    MIntAddStatement ∧
    MIntZsmulStatement ∧
    MIntRsmulStatement ∧
    MIntLinearStatement ∧
    MIntNonnegStatement ∧
    MIntMeasureStatement ∧
    MaMeasureStatement ∧
    MaMeasureMonoStatement ∧
    LocDensPosStatement ∧
    AnalyticNullStatement ∧
    MIntCongrNullStatement ∧
    StokesStatement ∧
    ByPartsSymmStatement ∧
    ByPartsNonposStatement ∧
    MassIndepStatement ∧
    LogNormIntegrableStatement ∧
    PoincareLelongCurveStatement ∧
    PoincareLelongStatement ∧
    PushForwardStatement ∧
    LocDensPullbackStatement ∧
    RankDropStatement ∧
    DegreeFormulaStatement ∧
    DegreeFormulaIntStatement :=
  ⟨isPotentialAdd,
   isPotentialZsmul,
   isPotentialRsmul,
   isPotentialPullback,
   isPshAdd,
   isPshRsmul,
   pshShift,
   regularAtlas,
   sncInducedAtlas,
   existsPartition,
   locDensBase,
   locDensCont,
   locDensChart,
   integralWithIndep,
   mIntEq,
   mIntAtlasIndep,
   mIntegrableCont,
   mIntSymm,
   mIntAdd,
   mIntZsmul,
   mIntRsmul,
   mIntLinear,
   mIntNonneg,
   mIntMeasure,
   maMeasure_thm,
   maMeasureMono,
   locDensPos,
   analyticNull,
   mIntCongrNull,
   stokes,
   byPartsSymm,
   byPartsNonpos,
   massIndep,
   logNormIntegrable,
   plCurve,
   poincareLelong,
   pushForward,
   locDensPullback,
   rankDrop,
   degreeFormula,
   degreeFormulaInt⟩

theorem projectiveLine_fubiniStudy_facts :
    IsPotential p1 fsPot ∧ IsPsh p1 fsPot ∧ Nonempty (ChartPartition p1) ∧
      IsSection p1 fsPot projectiveLinePairSection ∧ IsSNC p1 fsPot projectiveLinePairSection ![1] ![{OnePoint.infty}] :=
  ⟨projLine_isSmoothPotential, projLine_isPlurisubharmonic, projLine_partition, projLine_isHolomorphicSection, projLine_isSimpleNormalCrossing⟩

end ReciprocityTheory.AnForm.M
