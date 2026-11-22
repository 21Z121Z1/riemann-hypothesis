import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.IndexEqOfTraceInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0003
import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.Bundle0028
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.DvTransferIdxOfIdxCalc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0025
import Formalism.PeriodIntegrals.GZeroLogBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GeneralLinearCardBound.ZeroLogBound
import Formalism.PeriodIntegrals.Bundle0025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.HermitianAlgebraGeneration
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0030
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0027
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0028
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0029
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSmoothness.SecondCapelliMinorContinuousLinear
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0031
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.RadialDecompositionOfParts
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.IdCell
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootsOfUnityModPrime.RootUnitModPMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitNormRoot.UnitNormRootMain

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdIndexEq
section
noncomputable section

namespace PI

theorem adelic_index_eq : PI.AdIndexEq.IndexEq :=
  PI.UnitaryGroupMassFormula.AdIndexEq.indexEq_of_traceInt PI.UnitaryGroupMassFormula.AdIndexEq.trace_integral'

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvTransferIdx
section
theorem division_transfer_indices : ∃ C : ℝ, PI.Dv.Conclusion4b C := PI.Dv.TIW.dvTransferIdx_of_idxCalc division_index_calc
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GZeroLogBound
section
theorem GZeroLogBound : PI.GZeroLogBound.Target := PI.GZeroLogBound.UnitaryGroupMassFormula.target
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit
section
theorem level_s_all_split : PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.Top6.levelSplitting_of_heisenberg_levi PI.LevelKSplit.W.NCH.heisenberg_parabolic_all
    PI.LevelKSplit.W.NCL.levi_part_all
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnHermHaar
section
theorem qnHermHaar : Formalism.FourierDecayAlt.Q.HermHaar :=
  PI.QnHermHaar.qnHermHaar_of_alg PI.QnHermHaar.hermitian_algebra_generation qnRdSkew quantum_minor_star
    (PI.contractionsCovariant_iff.2
      ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩)
    quantum_minor_move.1 quantum_minor_move.2 qnYLeibniz qnEabGl qnEabPres
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTPres
section
theorem qnTPres : Formalism.FourierDecayAlt.Q.TPreservesFF := Formalism.FourierDecayAlt.Q.TPresMain.qnTPres_of qnTInv
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RadialDecompositionOfParts
section
theorem radial_decomposition_of_parts : Formalism.FourierDecayAlt.Q.RadialDecompositionOfParts := Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.radial_decomposition_of_parts'
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RootUnitModP
section
theorem rootUnitModP (E : Type) [Field E] [NumberField E] : Formalism.L2.SG.IdCell.RootModP E :=
  PI.RootUnitModP.W.rootOfUnity_eq_one_mod_prime E

theorem root_of_unity_mod_p (E : Type) [Field E] [NumberField E] : Formalism.L2.SG.IdCell.RootModP E :=
  rootUnitModP E
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitNormRoot
section
theorem unitNormRoot (E : Type) [Field E] [NumberField E] [StarRing E] : Formalism.L2.SG.IdCell.NormRoot E :=
  PI.UnitNormRootW.unitNormRoot_main
end

