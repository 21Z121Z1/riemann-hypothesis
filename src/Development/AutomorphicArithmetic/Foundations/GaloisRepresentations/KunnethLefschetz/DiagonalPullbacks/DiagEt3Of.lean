import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.Bundle0005
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.EtaleChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.LineUnitCm
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma

namespace UpperTheory.Gal.KunnethLefschetz.Di

theorem steps : Steps :=
  ⟨ringL_holds, geoPB_holds, geoM_holds, first_chern_class_isBaseChange, rootNat_holds, powRoot_holds, untw_holds, pBLim_holds, pBQOf_holds,
    diagSq_holds, clear_holds, G.blowBC, G.blowE, G.pBE⟩

theorem diagEt2_of (hI : In) (hQ : QDiag) : CrystallineSemistableComparison.Onto.DiagEt2 := steps.diagEt2 hI hQ

theorem diagEt3_of (hI : In) (hQ : QDiag) : CrystallineSemistableComparison.Onto.DiagEt3 := CrystallineSemistableComparison.Onto.diagEt3_of (diagEt2_of hI hQ)

end UpperTheory.Gal.KunnethLefschetz.Di
