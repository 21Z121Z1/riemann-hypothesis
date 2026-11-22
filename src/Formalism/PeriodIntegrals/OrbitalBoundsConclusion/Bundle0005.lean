import Mathlib
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PrimeLogarithmTail.SumLogDivSqLeDiv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientSigmaFiniteness.SigmaFiniteOfWeil
import Formalism.PeriodIntegrals.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowWeightSpan.RowWtSpanOfBideterminant
import Formalism.PeriodIntegrals.Bundle0010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SpectralGapLarge.ScGapBigMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarDegree.ScalDegMain
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurUnitaryInner.UnitaryInner
import Formalism.PeriodIntegrals.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BigCellConjugation.Monomial
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PhiDerivative.StarinvDeriv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PhiBigCellForm.BigCellEqW0BMulTM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TaylorInversePower.SumMultinomialSub
import Formalism.PeriodIntegrals.ArtSch
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TiltedDivisibility.TiltDivOfGeneral
import Formalism.PeriodIntegrals.Bundle0012
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentValuation.VwIntEqZero

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeLogOverPSqTail
section
theorem prime_log_over_sq_tail : PI.PrimeLogOverPSqTail :=
  fun X hX Q hQ => PI.TailWork.sum_log_div_sq_le_div X hX Q hQ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotNuSigma
section
theorem quotient_sigma_finite : PI.QuotNuSigma.Target :=
  fun _ _ _ _ _ _ _ _ _ μG _ A B μA μB ν hA hB hW =>
    PI.UnitaryGroupMassFormula.QuotNuSigma.sigmaFinite_of_weil μG A B μA μB ν hA hB hW
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RowWtSpan
section
theorem rowWtSpan_of (h1 : PI.RW.BideterminantMem) (h2 : PI.RW.BideterminantSpan) : PI.RowWtSpan :=
  PI.RWS.rowWtSpan_of_bideterminant h1 h2
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScGapBig
section
theorem scGapBig : PI.ScGapBig.ScGapBig := PI.UnitaryGroupMassFormula.ScGapBig.scGapBig_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalDeg
section
theorem scalar_degree : PI.ScalDeg.ScalDeg := PI.UnitaryGroupMassFormula.ScalDeg.scalDeg_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SchurClosable
section
theorem schur_closable : Formalism.IndefR.Leaf.SchurClosable :=
  PI.UnitaryGroupMassFormula.SchurClosable.Main.schurClosable
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwBigCellG
section
theorem big_cell_g : PI.SwBig.BigCellG := PI.SwBig.BigCellGProof.bigCellG
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiDeriv
section
theorem phiDeriv_of (hW : PI.SwBig.LongWeylElementSquare) : PI.SwBig.PhiDeriv :=
  fun k r => PI.SwBig.PhiDerivW.main k r hW
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiForm
section
theorem phi_form' : PI.SwBig.PhiForm := PI.SwBig.PhiFormProof.phiForm
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TayInvPow
section
theorem coeffInversePowerFacts.{u, v} : PI.TayInvPow.{u, v} := PI.UnitaryGroupMassFormula.TayInvPow.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TiltDivisibility
section
theorem tilt_divisibility : PI.ArtSch.TiltDiv := PI.ArtSch.tiltDiv_of_general
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnipVal
section
theorem unipVal : PI.UnipVal.UnipVal := fun _ _ _ w =>
  ⟨fun n hn => PI.UnitaryGroupMassFormula.UnipVal.Main.part1 w n hn,
    fun g₁ g₂ a h1 h2 h12 => PI.UnitaryGroupMassFormula.UnipVal.Main.part2 w g₁ g₂ a h1 h2 h12⟩
end

