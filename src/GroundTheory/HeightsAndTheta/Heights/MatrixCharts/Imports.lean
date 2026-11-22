import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPivotInvDiag
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0002
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LogDetGramContinuous.full : LogDetGramContinuous.Statement := LogDetGramContinuous.proof

theorem LogDetGramSubmean.full : LogDetGramSubmean.Statement :=
  LogDetGramSubmean.proof LogDetGramContinuous.full

theorem InvEntryBound.full : InvEntryBound.Statement := InvEntryBound.proof

theorem InvEntryDeriv.full : InvEntryDeriv.Statement := InvEntryDeriv.proof InvEntryBound.full

theorem LogDetGramDeriv.full : LogDetGramDeriv.Statement :=
  LogDetGramDeriv.proof InvEntryBound.full InvEntryDeriv.full MatrixDetDeriv.proof
    GramEntryDeriv.proof

theorem AnalyticDerivBound.full : AnalyticDerivBound.Statement := AnalyticDerivBound.proof

theorem ChartFrameDeriv.full : ChartFrameDeriv.Statement :=
  ChartFrameDeriv.proof AnalyticDerivBound.full

theorem ChartImagDeriv.full : ChartImagDeriv.Statement :=
  ChartImagDeriv.proof AnalyticDerivBound.full CuspTimeDeriv.proof

theorem PeriodHermValue.full : PeriodHermValue.Statement := PeriodHermValue.proof

theorem PeriodGramPosDef.full : PeriodGramPosDef.Statement :=
  PeriodGramPosDef.proof PeriodHermValue.full

theorem PivotInvDiag.full : PivotInvDiag.Statement :=
  PivotInvDiag.proof LeadMinorLeading.proof LeadMinorBasic.proof

theorem PivotLast.full : PivotLast.Statement := PivotLast.proof PivotInvDiag.full

theorem PivotBounds.full : PivotBounds.Statement :=
  PivotBounds.proof LeadMinorLeading.proof LeadMinorBasic.proof PivotInvDiag.full PivotLast.full

theorem PivotProductBound.full : PivotProductBound.Statement :=
  PivotProductBound.proof LeadMinorBasic.proof

theorem GramPivotProduct.full : GramPivotProduct.Statement :=
  GramPivotProduct.proof LeadMinorLeading.proof LeadMinorBasic.proof PivotLast.full
    UnimodularLast.proof SchurDetBound.proof IntGramQf.proof IntGramUnimodular.proof
    IntGramDropLast.proof IntGramSubLast.proof

theorem CuspCoordinateBound.full : CuspCoordinateBound.Statement :=
  CuspCoordinateBound.proof ChartPeriodImPos.proof ChartLowerBlockBound.proof PeriodGramPosDef.full

theorem ChartBounds.full : ChartBounds.Statement := ChartBounds.proof

theorem ChartGradient.full : ChartGradient.Statement :=
  ChartGradient.proof LogDetGramDeriv.full ChartFrameDeriv.full ChartImagDeriv.full
    ChartBounds.full

theorem LogDetGramPsh.full : LogDetGramPsh.Statement :=
  LogDetGramPsh.proof LogDetGramContinuous.full LogDetGramSubmean.full

theorem ChartPotentialPsh.full : ChartPotentialPsh.Statement :=
  ChartPotentialPsh.proof LogDetGramContinuous.full LogDetGramSubmean.full
    ChartImagContinuous.proof ChartImagMean.proof

theorem SchurQuotient.full : SchurQuotient.Statement := MCSchur.schurQuotient

theorem SchurQuotientPeriod.full : SchurQuotientPeriod.Statement := MCPeriod.schurQuotientPeriod

theorem CuspLattice.full : CuspLattice.Statement :=
  CuspLattice.proof
    (CuspShortVectors.proof ChartPeriodImPos.proof ChartLowerBlockBound.proof PeriodHermValue.full)
    (CuspLeadingMinima.proof ChartPeriodImPos.proof)
    (CuspCovolume.proof ChartPeriodImPos.proof PeriodGramPosDef.full CuspCoordinateBound.full
      PivotBounds.full GramPivotProduct.full PivotProductBound.full
      PeriodLatticeCovolume.proof LeadingCovolume.proof)

end GroundTheory.Heights₂.Heights
