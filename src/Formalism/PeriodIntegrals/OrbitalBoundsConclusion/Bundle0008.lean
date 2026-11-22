import Mathlib
import Formalism.PeriodIntegrals.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.ConvProjOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.Bundle0001
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.PrimeLogOverPTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS
import Formalism.PeriodIntegrals.Bundle0013
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.Weight
import Formalism.PeriodIntegrals.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Bundle0002
import Formalism.PeriodIntegrals.Bundle0010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialCoefficientSeries.CoeffExpMvEqTs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmithNormalForm.ExistsMoveRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitPrimeIntegers.ExistsUnitDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaussianUniqueness.GaussUniqMain
import Formalism.PeriodIntegrals.Bundle0016
import Formalism.PeriodIntegrals.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SymmetricDistance.SymDistOf
import Formalism.PeriodIntegrals.Bundle0014
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactTensorDensity.TensCpctDenOf

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhConvProj
section
theorem convolution_projection : PI.PhConvProj.ConvProj :=
  PI.UnitaryGroupMassFormula.PhConvProj.Defs.convProj_of PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.selfAdj PI.UnitaryGroupMassFormula.PhConvProj.Sand.sand
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PowBddInt
section
theorem power_bounded_integral : PI.PowBddInt :=
  PI.PowBddIntWork.powBddInt_of PI.PowBddIntWork.stepA PI.PowBddIntWork.stepB
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeLogOverP
section
theorem sum_log_p_over_p : PI.PrimeLogOverP := PI.PrimeLogOverPWork.sum_log_div_prime_le
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotInv
section
theorem quotient_invariant : PI.QuotInv := PI.QuotInvW.quotInv
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq
section
namespace PI

theorem wqUnique : PI.WeilQuotMeas.WqUnique :=
  PI.QuotMeasUniqW.wqUnique_of PI.QuotMeasUniqW.qmuWeight PI.QuotMeasUniqW.qmuLift

end PI
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RowLetter
section
theorem row_letter_rule : PI.RowLetter :=
  PI.RL.W.rowLetter_of PI.RL.W.chainRule PI.RL.W.vecX PI.RL.W.keyCov PI.RL.W.hdHom
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SimeqPdInt
section
theorem simeq_pd_integral : PI.SimeqPdInt.Target := PI.UnitaryGroupMassFormula.SimeqPdInt.target
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SmithMat
section
theorem smith_normal_form_theory.{u} : PI.SmithMat.{u} := by
  intro R _ _ _ n A
  obtain ⟨d, ⟨U, V, hU, hV, h⟩, hd⟩ := PI.SmithWork.smith n A
  exact ⟨U, V, d, hU, hV, h, hd⟩

theorem smith_diagonal_entries.{u} : PI.SmithDiag.{u} := by
  intro R _ _ _ n A
  obtain ⟨U, V, d, hU, hV, h, -⟩ := smith_normal_form_theory R n A
  exact ⟨U, V, d, hU, hV, h⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
section
theorem split_integral_local : PI.SplitIntLoc := PI.SplitIntLoc.Proof.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwGaussUniq
section
theorem gauss_sum_unique : PI.SwBig.GaussUniq := PI.SwBig.GU.gaussUniq_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SymDist
section
theorem symDist_of : PI.ExpTri → PI.SymDist := PI.SymDistWork.symDist_of
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TensCpctDen
section
theorem tensor_compact_dense : PI.TensCpctDen := PI.tensCpctDen_of compactBounded
end

