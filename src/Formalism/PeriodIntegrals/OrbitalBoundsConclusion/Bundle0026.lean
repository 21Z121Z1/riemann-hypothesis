import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroLevelIndex.SecondMinorZeroLevelFormula
import Formalism.PeriodIntegrals.ScPiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.FrameHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0002
import Formalism.PeriodIntegrals.Bundle0025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NilpotentVolumeOne.VolumeDegenerateRankOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.DimStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Formula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylConjugationFixedColumn.ReflectionScalarDualIsotropic

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnZeroLevel
section
theorem capelli_zero_level : Formalism.FourierDecayAlt.Q.CapLZero ∧ Formalism.FourierDecayAlt.Q.TLZero :=
  PI.QnZeroLevelWork.qnZeroLevel
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScPiFrame
section
theorem sc_pi_frame : PI.ScPiExists.Frame := PI.ScPiFrameW.frame_holds
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolumeUnipotentOne
section
theorem volumeUnipotentOne : PI.VolNzeroOne.VolumeUnipotentOneFrom := PI.VolNzeroOne.W.volume_degenerate_rank_one
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForK
section
theorem weylForK_of : PI.WeylForU → PI.WeylForK :=
  PI.WeylForKWork.weylForK_of_leaves PI.WeylForKWork.block_reindex_holds PI.WeylForKWork.block_diagonal_torus_holds
    PI.WeylForKWork.torus_weight_exists PI.WeylForKWork.weight_unique_holds PI.WeylForKWork.minimal_irreducible_exists
    PI.WeylForKWork.dominant_restriction_holds PI.WeylForKWork.dimension_induction_holds PI.WeylForKWork.weyl_formula_compact
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylLevelElementProperties
section
theorem weyl_level_element_properties' : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts :=
  PI.IsotropicReflections.isotropic_reflection_properties
end

