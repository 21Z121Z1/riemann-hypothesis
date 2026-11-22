import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MajorantVanishing.MajAtZeroRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.QBuild
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Bundle0001
import Formalism.PeriodIntegrals.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSpanComplement.RenameInitMinor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusInvariance.QnTInvOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0025
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0027
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0029
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0030
import Formalism.PeriodIntegrals.Bundle0025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjRat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CoordAll

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvProjB
section
theorem projection_degree_bound : PI.Dv.ProjB := PI.Dv.ProjBW.projB
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd
section
theorem frameInd : Formalism.FourierDecayAlt.C2.GramIndependentSignature :=
  PI.FrameInd.frame_induction_of PI.FrameInd.signStep (PI.FrameInd.UPosW.uPos_of PI.FrameInd.negative_bound)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinorSpanCompl
section
theorem minor_span_complement : PI.MinorSpanCompl := PI.MSC.minorSpanCompl
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTInv
section
theorem qnTInv : Formalism.FourierDecayAlt.Q.TInvariant :=
  Formalism.FourierDecayAlt.Q.TInvW.qnTInv_of
    (PI.contractionsCovariant_iff.2
      ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩)
    qnEabPres qnEabGl qnMinorLeft
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolSemiDirect
section
theorem volume_unipotent_all_cm : PI.VolSemiDirect.VolumeUnipotentAllCM :=
  PI.VolSemiDirect.W.volume_unipotent_of_modulus_one
    (PI.VolSemiDirect.W.Md.modOne_of PI.VolSemiDirect.W.Md.heisenberg_coordinates_holds
      (PI.VolSemiDirect.W.Md.wMod_of
        (PI.VolSemiDirect.W.Cj.unipotent_modulus_of_stable_rank_one PI.VolSemiDirect.W.SR.stable_rank_one_adeles)))
    PI.VolSemiDirect.W.representation_continuous PI.VolSemiDirect.W.projection_preserves_rational
end

