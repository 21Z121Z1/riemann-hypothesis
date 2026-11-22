import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TermIdIffInSOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds
import Formalism.PeriodIntegrals.Bundle0018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianOrder.LocJacOrdClosed
import Formalism.PeriodIntegrals.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.LocJacTypClosed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.MeasInfXferOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.ConstantCoeffZeroOfBoundGeneral
import Formalism.PeriodIntegrals.Bundle0031
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.SizeDel
import Development.AutomorphicArithmetic.OrbitLabellings.SzEatIFree

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdCellInS
section
theorem term_id_iff_in_s (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermIdIffInS D u u' :=
  PI.UnitaryGroupMassFormula.IdCellInSW.termIdIffInS_of D (PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D) u u'
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocJacOrd
section
theorem locJacOrd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    PI.LocJacOrd.LocJacOrd (E := E) ψ v :=
  PI.LocJacOrd.W.locJacOrd_closed ψ v
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocJacTyp
section
theorem locJacTyp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    PI.LocJacTyp.LocJacTyp σ ψ v :=
  PI.UnitaryGroupMassFormula.LocJacTyp.locJacTyp_closed σ ψ v
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasInfXfer
section
theorem infinite_measure_transfer : Formalism.L2.SG.Pf.MeasInf.InfTransfer :=
  Formalism.L2.SG.Pf.MeasInfW.measInfXfer_of Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity
    Formalism.L2.SG.Pf.MeasInfW.nilpotent_measure_recursion Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion
    Formalism.L2.SG.Pf.MeasInfW.nilpotent_measure_closed_form Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_closed_form
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbAddUp
section
theorem PI.OrbAddUp : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddLowerBound E :=
  PI.OrbJet.AU.orbAddUp_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalarPairDr
section
theorem scalar_pair_dr (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalarPairDr.ScalarDr D u u' :=
  PI.ScalarPairDr.W.scalarDr D u u'
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SzEatI
section
theorem sz_eat_identity : PI.SzEatI.SzEatI := UpperTheory.G2.szEatI_of_stepA PI.SzEatI.W.stepA
end

