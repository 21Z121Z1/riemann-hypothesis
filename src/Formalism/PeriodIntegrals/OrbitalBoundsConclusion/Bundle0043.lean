import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.T2SpaceOfNonarchimedeanLocalField
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.NormGOfLocDiff
import Formalism.PeriodIntegrals.Bundle0034
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseDerivativeFiltration.HasseMemHfr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GenericityConstantDoubleCosets

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CntNotInt
section
theorem count_not_integral : PI.CntLocalParts.NotIntAll :=
  have hD : PI.CntNotIntW.LocDiff :=
    PI.CntNotIntW.locDiff_of PI.CntNotIntW.trace_dual_lattice
      (PI.CntNotIntW.dualApprox_of PI.CntNotIntW.small_powers_bound PI.CntNotIntW.tensorLiftSurjective)
      PI.CntNotIntW.small_powers_bound
  PI.CntNotIntW.notIntAll_of_loc (PI.CntNotIntW.locGen_of hD PI.CntNotIntW.dual_lattice_powers)
    (PI.CntNotIntW.normG_of_locDiff hD)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HassePresH
section
theorem hasse_presentation : PI.HassePresH := PI.UnitaryGroupMassFormula.HassePresH.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermAttrConst
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_function_const (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermFun D u u' :=
  PI.TermAttrConst.UnitaryGroupMassFormula.termFun_of PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u'

theorem termAttrConst_gFun (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word)
    (F0 : Formalism.MainNotions.S.FlagG (Formalism.MainNotions.S.VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.VS D).V) (hΛ : Formalism.MainNotions.S.IsRowLat D F0 Λ) :
    Formalism.L2.SG.TermDef.GFun Λ (Formalism.MainNotions.S.lf D F0) (Formalism.L2.SG.TermDef.PD D Λ (Formalism.MainNotions.S.lf D F0) u') :=
  PI.TermAttrConst.UnitaryGroupMassFormula.termGFun_holds D u u' F0 Λ hΛ
end

