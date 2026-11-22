import Mathlib
import Formalism.PeriodIntegrals.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselLeviAction.MulVecBvecApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditivePadicLinear.Bundle0001
import Formalism.PeriodIntegrals.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.CoeffMulCharIdem
import Formalism.PeriodIntegrals.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ClassNumberIntegrality.HalfIntegral
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.CoordBaseChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.FinrankIInfKerEquiv
import Formalism.PeriodIntegrals.Bundle0014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.FiberCardHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ClassAct
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FixedDimensionCount.ExistsSemidirectDecomposition
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NonzeroDiscriminants.DiscMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.EfRankSumMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.ContinuousLmulM

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdjointTensorOfSingleValid
section
theorem adjointTensorOfSingle_valid : PI.TenOp :=
  PI.TOW.tenOp_of_steps PI.TOW.DegW.stepDeg
    (PI.TOW.stepPure_of PI.TOW.LiftW.stepLift PI.TOW.MonoW.stepMonoFactor) PI.TOW.stepSpan
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BesselLevi
section
theorem bessel_levi_formula : PI.BesselLevi.BesselLevi :=
  PI.UnitaryGroupMassFormula.BesselLevi.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BiaddZpLin
section
theorem biadditive_zp_linear : PI.BiaddZpLin.Target :=
  PI.BiaddZpLinW.biaddZpLin_of PI.BiaddZpLinW.biadditive_continuous_padic
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
section
theorem orthogonalCentral : PI.CharIdem.CharIdem :=
  PI.CharIdemW.charIdem_of PI.CharIdemW.central PI.CharIdemW.scalar
    (PI.CharIdemW.mulEq_of PI.CharIdemW.scalar)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ClassNumImQInt
section
theorem imag_quadratic_integral_basis : PI.ClassNumImQ.IntBasis :=
  PI.UnitaryGroupMassFormula.ClassNumImQInt.intBasis
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CoefExt
section
theorem coefficient_crystal_generation : Formalism.MainNotions.N.GlobalTheory.CoefCrysGen :=
  PI.CoefExt.coefCrysGen_of PI.CoefExt.invBaseChange
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DefPosDef
section
theorem positive_definite_form : PI.DefPosDef :=
  PI.DefPosDefWork.defPosDef_of PI.DefPosDefWork.splitting_of_extension PI.DefPosDefWork.positive_definite_second
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DensSplit
section
theorem bilinearDensityFormula : Formalism.L2.SG.DensExact.DensExactSplit :=
  PI.DensSplitW.densExactSplit_of PI.DensSplitW.fiberCard_holds
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiaFixDim
section
theorem diagonal_fixed_dimension : Formalism.L2.SG.ClassAct.FixedDim := PI.UnitaryGroupMassFormula.DiaFixDim.Main.fixedDim
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiscrNe
section
theorem discrNe' : PI.DiscrNe := DiscrNeWork.discrNe_all
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EfRankSum
section
theorem ramificationDegreeSum : PI.EfRankSum := PI.UnitaryGroupMassFormula.EfRankSum.efRankSum_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExistsGaugeNormalizedStabilizer
section
theorem exists_gaugeNormalizedStabilizer : PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank := fun r => ⟨PI.ExistsGaugeMeasureForEachRank.W.μG r, PI.ExistsGaugeMeasureForEachRank.W.gauge r⟩
end

