import Formalism.PeriodIntegrals.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubicExponentialFactor.ExpMvAddC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.EqZeroOfFockInnerSelfRe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle0004
import Mathlib
import Formalism.PeriodIntegrals.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.KerLocIsoOfNormOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.Bundle0004
import Formalism.PeriodIntegrals.Bundle0020
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.LocDualGenOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.UnramifiedDualGenerator
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.CoreFgOfLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZeroAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.EntryEmbedMatrix
import Formalism.PeriodIntegrals.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualGramSubstitution.PhDualGramMain
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFactorIdentity.ExpMvEq
import Formalism.PeriodIntegrals.Bundle0021
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowFormPermutationSplit.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.CountD
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.Bundle0002

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CubicExponentialFactor
section
theorem thetaCube_triple_relation : PI.CubicExponentialFactor.Lemma := PI.CubicExponentialFactor.Wk.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockOneDeg
section
theorem fock_degree_one : PI.FockDegreeTwoParts.OneDeg :=
  PI.FockOneDegW.oneDeg_of
    (PI.FockOneDegW.Core.hwHarmDeg_of PI.FockOneDegW.fock_operators_kernel PI.FockOneDegW.harmIff)
    (PI.FockOneDegW.reduction_of PI.FockOneDegW.fock_inner_facts PI.FockOneDegW.kernel_highest_weight
      PI.FockOneDegW.kernel_harmonic PI.FockOneDegW.highest_weight_harmonic PI.FockOneDegW.harmonic_submodule
      PI.FockOneDegW.fock_kernel_adjoint PI.FockOneDegW.hwExist)
    PI.FockOneDegW.Swap.fock_swap_groups
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerLocIso
section
theorem kernel_local_iso : PI.KerIso.LocIso := PI.KLW.kerLocIso_of_normOne PI.KLW.normOne
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocDualGen
section
theorem local_dual_generation : PI.LocDualGen.Stmt :=
  PI.LocDualGen.Of.locDualGen_of PI.LocDualGen.FpU.unramified_dual_generator
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocGlue
section
theorem local_hermitian_glue : PI.LocHerm.LocGlue :=
  PI.LocHerm.Glue.locGlue_of projectiveOverOrder
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocLatEq
section
theorem eq_iff_locallyEq : PI.LocLatEq.Stmt :=
  PI.LocLatEq.W.locLatEq_of PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP
    (PI.LocLatEq.W.coreP_of_unitP_avoidP_intP PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP PI.LocLatEq.W.intP)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OneCosetSharp
section
theorem support_oneCoset : PI.OneCosetSharp.OneCosetSharp :=
  PI.OneCosetSharp.W.oneCosetSharp_of_patClosed PI.OneCosetSharp.W.patClosed PI.OneCosetSharp.W.kappaZero
    PI.OneCosetSharp.W.nElem PI.OneCosetSharp.W.gaStep PI.OneCosetSharp.W.C2.claim2
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhDualGram
section
namespace PI.Final.PhDualGram

theorem phase_dual_gram : PI.FglGram.PhDualGram := PI.UnitaryGroupMassFormula.PhDualGram.phDualGram_main

end PI.Final.PhDualGram
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhiCubeOfFactor
section
theorem phiCubeOfFactor : PI.PhiCubeOfFactor.Lemma := PI.PhiCubeOfFactor.Wk.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ProdFormulaE
section
theorem product_formula_e : PI.ProdFormulaE.ProdFormulaE :=
  PI.ProdFormulaE.Assemble.prodFormulaE_of_haar PI.ProdFormulaE.HaarAlgP.haarScaling
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
section
theorem quantum_minor_row_form : PI.QmRowForm :=
  PI.UnitaryGroupMassFormula.QmRowForm.qmRowForm_of PI.UnitaryGroupMassFormula.QmRowForm.double_row_decreasing PI.UnitaryGroupMassFormula.QmRowForm.double_row_increasing
    PI.UnitaryGroupMassFormula.QmRowForm.double_row_permutation
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqfRootShift
section
theorem squarefree_root_shift : PI.SqfRootShift.Claim :=
  PI.SqfRootShift.W.claim_of PI.SqfRootShift.W.countP PI.SqfRootShift.W.arithP
end

