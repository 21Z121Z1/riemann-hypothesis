import Mathlib
import Formalism.PeriodIntegrals.Bundle0010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.SelfDualLocOfLocBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.Bundle0003
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SigmaStarUniqOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitZeroClosedness.SplitZeroGBd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitZeroClosedness.IsClosedSimeqZero
import Formalism.PeriodIntegrals.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairGluing.SqPairGlueMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.Bundle0001
import Formalism.PeriodIntegrals.Bundle0021
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LargeStabilizerInverse.GLeftInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SandwichOfOfCharts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.ChartZeroEqOneOfLongWeylSq
import Formalism.PeriodIntegrals.Bundle0006
import Formalism.PeriodIntegrals.Bundle0016
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TranslationInvariantLattice.TransInvLatMain
import Formalism.PeriodIntegrals.Bundle0023
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittSubstitution.CoeffMapMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WhittakerFunctionalDual.StableOfIrreducible
import Formalism.PeriodIntegrals.Bundle0013
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.WittOf

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SelfDualLoc
section
theorem self_dual_local : PI.SelfDualLoc :=
  PI.SelfDualLoc.W.selfDualLoc_of_locBasis PI.SelfDualLoc.W.locBasis
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarUniq
section
theorem sigma_star_unique : PI.SigmaStarUniq := PI.SSU.sigmaStarUniq_of area_lattice_formula
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitZeroG
section
theorem split_zero_g : PI.SplitZeroG.SplitZeroG :=
  PI.SZGW.splitZeroG_of PI.SZGW.zpSimeq_holds PI.SZGW.zpInt_holds PI.SZGW.zcFacts_holds
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqPairGlue
section
theorem square_pair_glue : PI.SqPair.PLocalAll → Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen :=
  PI.SqPairW.sqPairGlue_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqfDivDeg
section
theorem squarefree_div_degree : PI.SqfDivDeg.Claim :=
  PI.SqfDivDeg.W.sqfDivDeg_of_rootDense PI.SqfDivDeg.W.rootDense
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StabBig
section
theorem stabilizer_large : PI.StabBig := PI.StabBigW.stabBig
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwSandwichOf
section
theorem sandwich_of_chart : PI.SwSand.SandwichOf :=
  PI.SwSandwichOfWork.sandwichOf_of_charts PI.SwSandwichOfWork.normRL PI.SwSandwichOfWork.logG
    PI.SwSandwichOfWork.chartFwd PI.SwSandwichOfWork.chartBwd PI.SwSandwichOfWork.sideB
    PI.SwSandwichOfWork.sideA
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransInvLat
section
theorem translation_invariant_lattice : PI.TransInvLat := PI.TransInvLatW.transInvLat_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJUnimod
section
theorem unitary_unimodular_right_inv : PI.UJUnimod.UJRightInv :=
  fun n ε => ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfSubst
section
theorem witt_substitution : PI.WfSubst := PI.WfSubstProof.wfSubst
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WhitFunctDual
section
theorem whittaker_functional_dual : PI.WhitFunctDual := PI.WhitFunctDualWork.whitFunctDual_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
section
theorem witt_extension_theorem : PI.WittExtension :=
  PI.Witt.witt_of PI.Witt.one_vector_holds PI.Witt.anisotropic'
end

