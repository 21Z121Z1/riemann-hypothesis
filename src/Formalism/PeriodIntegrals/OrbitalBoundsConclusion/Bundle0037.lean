import Mathlib
import Formalism.PeriodIntegrals.Bundle0031
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds
import Formalism.PeriodIntegrals.EntAtD
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.EntAtDOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.LapForms
import Formalism.PeriodIntegrals.Bundle0028
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0025
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0036
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0034
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.GTLowerOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagClassConstancy.FlagOfInSFRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelevantCarrierNonempty.InSCarrierNonempty
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGeneral.ScalarFactorEqOneOfLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGenerators.ScalarEquivOfGen
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.Bundle0001
import Formalism.PeriodIntegrals.Bundle0025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UnitaryClassMass

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DCRelEquiv
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_eq_iff_relation (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermEqIff D u u' := by
  intro F0 Λ _
  exact PI.DCRelEquiv.UnitaryGroupMassFormula.eqIffAll_holds _ _ _ _ _ _ _ _
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EntAtD
section
theorem jet_bound_ramified_prime : PI.EntAtD.EntAtD :=
  PI.EntAtD.W.entAtD_of PI.EntAtD.W.pExpCoeff PI.EntAtD.W.pBridge PI.EntAtD.W.pLapComm
    PI.EntAtD.W.pMinorAff PI.EntAtD.W.pSDegMul PI.EntAtD.W.pLapForms
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTLower
section
theorem gTLower_of (h2 : Formalism.BasicNotions.FactDelDualNabla) : PI.GTLower :=
  PI.WGL.gTLower_of h2 highest_weight_irreducible gelfand_tsetlin_branching schur_fock
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSClassConst
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem in_s_class_constant (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermInSFun D u u' :=
  fun _ Λ _ => PI.InSClassConstW.inSFun_all Λ _ _
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSRelevant
section
theorem in_s_relevant (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermInSRel D u u' :=
  PI.UnitaryGroupMassFormula.InSRelevantW.termInSRel_main D u u'
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalEquivGen
section
theorem scalar_equiv_general : PI.ScalPairs.ScalarEquivG :=
  PI.UnitaryGroupMassFormula.ScalEquivGen.scalarEquivG_holds
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalarEquivalenceHermitianSpace
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scalar_equiv_of_general (h : PI.ScalPairs.ScalarEquivG) (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) :
    PI.ScalPairs.ScalarEquiv D u u' :=
  PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace.scalarEquiv_of_gen h D u u'
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StdSlopeLow
section
theorem standard_slope_lower : PI.StdSlopeLow :=
  PI.SlopeSteps.stdSlopeLow_of PI.SlopeSteps.nabla_gram_lower_bound PI.SlopeSteps.gram_matrix_duality
    PI.SlopeSteps.nabla_operator_basis
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryClassMassHermitian
section
theorem unitary_class_mass_hermitian : PI.UJClassMass2.UJClassMass :=
  PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass
end

