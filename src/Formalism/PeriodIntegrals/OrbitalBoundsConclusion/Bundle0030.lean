import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.GoodMonoProd
import Mathlib
import Formalism.PeriodIntegrals.ContractionsCovariantIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.QnCovHat2OfLin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.MXMulVecMid
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.HermitianOrthogonalProjectionVector
import Formalism.PeriodIntegrals.Bundle0027
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.MeasureContractionFormula
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0029
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0027
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Analytic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.LeftMultiplicationRule
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.TargetOfWframe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PrincipalIdealRingAtPrime
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WeilBasisExistence
import Formalism.PeriodIntegrals.UJClassFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.AdelicBounds
import Formalism.PeriodIntegrals.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.Bridge
import Formalism.HermitianCurvature.StatementU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZDeriv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle0004

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CCRuleC
section
theorem cCRuleC : Formalism.FourierDecayAlt.C2.RuleC := CCRuleCW.ruleC
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CovariantHatSqOfLin
section
theorem covariant_hat_sq_of_lin : PI.QnCovLin → PI.QnCovHat2 := PI.QnCovHat2W.qnCovHat2_of_lin
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EichlerTau
section
theorem eichlerTau : Formalism.FourierDecayAlt.C2.TauMem :=
  PI.PolynomialProperness.tauMem_of PI.PolynomialProperness.mxFacts PI.PolynomialProperness.TauN.neFacts
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsotropicNormalFormPartial
section
theorem isotropic_normal_form_partial : Formalism.FourierDecayAlt.C3.IsotropicNormalFormPartial := NFOne.normFormOne
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NMeasInv
section
namespace PI

theorem n_measure_invariant : PI.NMeasInv.Target :=
  PI.NMeasInv.UnitaryGroupMassFormula.nMeasInv_of PI.NMeasInv.UnitaryGroupMassFormula.measure_contraction_formula

end PI
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmCapComm
section
theorem qmCapComm_of : Formalism.FourierDecayAlt.Q.EabPres → Formalism.FourierDecayAlt.Q.EabGlLev → Formalism.FourierDecayAlt.Q.CapCommute :=
  fun hP hG => QmCapCommW.capelli_operator_transfer QmCapCommW.capelli_operator_congruence QmCapCommW.quantum_determinant_commutes hP hG

theorem qmCapComm_of_gl : Formalism.FourierDecayAlt.Q.EabGlLev → Formalism.FourierDecayAlt.Q.CapCommute :=
  qmCapComm_of qnEabPres

theorem capelli_det_commute : Formalism.FourierDecayAlt.Q.CapCommute :=
  qmCapComm_of_gl qnEabGl
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRdSkew
section
theorem qnRdSkew : Formalism.FourierDecayAlt.Q.RdSkew :=
  QnRdSkewW.rdSkew_of QnRdSkewW.skew_reduction_group QnRdSkewW.skew_reduction_analytic
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleLeft
section
theorem qnRuleLeft : Formalism.FourierDecayAlt.Q.RuleLeft := Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.left_multiplication_rule
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScRefExists
section
theorem sc_reference_exists : PI.ScRefExists.Target :=
  PI.ScRefExists.Top.target_of_wframe
    (PI.ScRefExists.WF.wFrame_of PI.ScRefExists.ApP.principal_ideal_ring_at_prime PI.ScRefExists.WB.weil_basis_existence)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJClassFin
section
theorem unitary_class_set_finite : PI.UJClassFin.UJClassFin :=
  PI.UnitaryGroupMassFormula.UJClassFin.uJClassFin_of_latFin PI.UnitaryGroupMassFormula.UJClassFin.posDefOfDefiniteSignature_holds
    PI.UnitaryGroupMassFormula.UJClassFin.adelic_bounds PI.UnitaryGroupMassFormula.UJClassFin.lattice_classes_finite_refinement
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnimodGenus
section
theorem unimodular_genus_unique : PI.UnimodGenus :=
  PI.UG.W.unimodGenus_of PI.UG.W.unimodLocal PI.UG.W.isomLocStd
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCost
section
theorem operator_word_cost : Formalism.FourierDecayAlt.U.DerivativeCostFromComponents :=
  PI.UnitaryGroupMassFormula.UsCost.unitarySum_cost_of_parts PI.UnitaryGroupMassFormula.UsCost.wordsId PI.UnitaryGroupMassFormula.UsCost.letterSize PI.UnitaryGroupMassFormula.UsCost.starScale
    PI.UnitaryGroupMassFormula.UsCost.commLR PI.UnitaryGroupMassFormula.UsCost.offK PI.UnitaryGroupMassFormula.UsCost.zSmooth
    (PI.UnitaryGroupMassFormula.UsCost.zCost_of PI.UnitaryGroupMassFormula.UsCost.zSmooth PI.UnitaryGroupMassFormula.UsCost.zDeriv PI.UnitaryGroupMassFormula.UsCost.dirSize)
end

