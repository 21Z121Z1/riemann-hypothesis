import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0007
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfV
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0001

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfM
section
namespace Formalism.MainNotions.S.Gauge

theorem cdGauge_of_lamVol (D : Formalism.BasicNotions.D7) (hcd : Formalism.BasicNotions.cdScaleTie D)
    (hL : ∀ {m P Q : ℕ} (ε : Fin m → Bool) (e : Fin P ⊕ Fin Q ≃ Fin m), LamVol ε e)
    (n : ℕ) (ε : Fin n → Bool) : CdGauge D n ε :=
  cdGauge_of_parts D hcd (fun ε => l1BallDensity_signs ε) (fun ε => l1BallMeasurable_signs ε) hL (fun ε e => setEq ε e) (fun ε e => upqIn ε e) n ε

end Formalism.MainNotions.S.Gauge
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfVF
section
noncomputable section

namespace Formalism.MainNotions.S.Gauge

theorem lamVol_of_sum_equiv {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : LamVol ε e :=
  CdV.lamVol_of ε e (mp_cF ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q)))

end Formalism.MainNotions.S.Gauge
end
end

