import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0044
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0042
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0045
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0057
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0047
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0048
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0053
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0050
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ConvGG
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetPf
section
noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.IdMeet

theorem volColC_holds : VolColC :=
  volColC_of noinfEqC_holds nocolEqC_holds gcCountC_holds fundMeasEqC_holds indexVolC_holds indexTransferC_holds
    conjUC_holds gcFundC_holds gcConjC_holds hinfConjC_holds

theorem idMeetOneC_holds : IdMeetOneC := idMeetOneC_of idMeetKeyC_holds

theorem idMeetPhaseC_holds : IdMeetPhaseC := idMeetPhaseC_of idMeetKeyC_holds

theorem idMeetVolC_holds : IdMeetVolC := idMeetVolC_of idMeetKeyC_holds volColC_holds

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjInInfinityXOfG
section
open Formalism.BasicNotions Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf

theorem realObj_inInfinityX_ofG (hI : Formalism.L2.SG.RealObj.EnergyInt.StepIntG) (hC : Formalism.L2.S.Pv.ConvG.StepConvG)
    {D : D7}
    (hg : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (hsc : 0 < sc) : InInfinityX X u u' sc := Formalism.L2.SG.RealObj.EnergyInst.inInfinityXAt (X := X) (hI D hg) (hC D hg) u u' sc hsc

end Formalism.L2.SG.Pf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabFinal
section
noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.Pf.Slab

theorem neatKu_full : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u : D.what₂.Word), NeatKu X u Y.hK :=
  fun _ X Y u => neatKu_of_gamUnipKu X u Y.hK (latOfLattice_holds X u) (gamUnipKu_holds X u Y.hK)

theorem rInvC_holds : RInvC := rInvC_of nilradical_conj_level'

theorem ooLintSumC_holds_slab (hMaj : MajPtC) (hCnt : CountC) : OOLintSumC :=
  ooLintSumC_of_parts Formalism.L2.SG.Pf.RegroupPf.slabCoverC_holds hMaj rInvC_holds hCnt neatKu_full

end Formalism.L2.SG.Pf
end
end

