import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv
import Mathlib
import Formalism.PeriodIntegrals.Bundle0025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Assembly

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormChiNBi
section
theorem chi_n_bilinear {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Formalism.L2.SG.NormCut.ChiNBi X :=
  PIW.NormChiNBi.chiNBi_holds X
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolStabSW
section
theorem volume_stabilizer_from_siegel_weil : PI.VolFromSW.VolStabFromSW :=
  PI.VolStabSW.Assembly.volStabFromSW_holds
end

