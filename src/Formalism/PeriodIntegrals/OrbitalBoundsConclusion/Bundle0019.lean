import Mathlib
import Formalism.PeriodIntegrals.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.AddIntGTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.AntitoneStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.MassRatio
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDegreeEquality.FinrankEqTwo
import Formalism.PeriodIntegrals.Bundle0003
import Formalism.PeriodIntegrals.Bundle0013
import Formalism.PeriodIntegrals.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalLemmaOfHelpers
import Formalism.PeriodIntegrals.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianLatticeFiniteness.HermLatFinMain
import Formalism.PeriodIntegrals.Bundle0021
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0017
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalProductFormula.LocProdFormulaOf
import Formalism.PeriodIntegrals.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.OkpInertMain
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsOfCalculation
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ComplexDoubleCosets.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantVectorMove.SumPermsSignSquared
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowExpansionMinor.FirstColumnSplitBijective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerProductCast.OfFnProdIntCast

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AddIntG
section
theorem additive_integral_generation : PI.AddIntG.Target := PI.AddIntG.Wk.addIntG_top
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BlockRatReal
section
theorem blockRatReal : PI.BlockRatReal.Stmt :=
  PI.BlockRatReal.stmt_of PI.BlockRatReal.UnitaryGroupMassFormula.evenStep PI.BlockRatReal.UnitaryGroupMassFormula.Odd.oddStep
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMDegEq
section
theorem Formalism.L2.SG.MassRatio.cm_degree_eq : Formalism.L2.SG.MassRatio.DegEq := CMDeg.degEq
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExplicitFormula
section
theorem explicitFormula_of : PI.ZerosWindow → PI.DiscFactor → PI.DiscLog → PI.LBoundRight →
    PI.ZetaBoundRight → PI.LInvRight → PI.ExplicitFormula :=
  PI.EF.explicitFormula_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HermLatFin
section
theorem hermitian_lattice_finite : PI.HermLatFin.HermLatFin :=
  PI.HermLatFin.UnitaryGroupMassFormula.hermLatFin_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocProdFormula
section
theorem local_product_formula : PI.LocProdFormula :=
  PI.LocProdFormulaW.locProdFormula_of product_formula_e
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OkpInert
section
theorem integers_inert_prime : PI.OkpInert := PI.OkpW.okpInert_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormUnits
section
theorem phase_norm_units : PI.PhNormUnits.Target := PI.PhNormUnits.UnitaryGroupMassFormula.norm_units_of_calculation
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesInner
section
theorem fold_l2_bound_c (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesInner G μ :=
  PI.PoincareSeriesInner.W.fold_L2_complex_of PI.PoincareSeriesInner.W.complex_double_coset G μ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmMove
section
theorem quantum_minor_move : PI.QmMove := ⟨PI.UnitaryGroupMassFormula.QmMove.move_operator_vector, PI.UnitaryGroupMassFormula.QmMove.move_operator_covariance⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowExp
section
theorem quantum_minor_row_expansion : PI.QmRowExp := PI.qmRowExp_of_rowForm quantum_minor_row_form
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmStar
section
theorem quantum_minor_star : PI.QmStar :=
  PI.UnitaryGroupMassFormula.QmStar.qmStar_of quantum_minor_row_form
end

