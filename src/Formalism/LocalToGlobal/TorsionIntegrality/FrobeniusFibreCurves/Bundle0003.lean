import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0002

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveCocycleIntegralAllResidues
section
noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.L2.Th1.A (fgl iSer logSer wpReg g₂ g₃ IntModel)

def CurveFrobStick : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    (at1 0 (sgW W s2) * at1 1 (sgW W s2) * at1 2 (sgW W s2)) ^ 3 * det3 (wpReg W) =
      -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
        (evalSumThree (sgW W s2) * evalDiffThree 0 1 (sgW W s2) * evalDiffThree 0 2 (sgW W s2) * evalDiffThree 1 2 (sgW W s2))

def CurveParThree : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W → Simeq (par3 (fgl W) (iSer W) (phW W s2)) 0

def CurveCocycleIntegralAllResidues : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W →
    DivAB (beW W s2) ∧ swap2 (beW W s2) = beW W s2 ∧
      Simeq (d1 (fgl W) (beW W s2)) 0 ∧ Simeq (d1 (fgl W) (swap2 (beW W s2))) 0 ∧
      ∀ n : ℕ, 3 ≤ n → ‖PowerSeries.constantCoeff ((Dinv (logSer W))^[n] (phW W s2))‖ ≤ 1

end Formalism.L2.Th1.B
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.IsFibreCurve
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B

open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr)

section Alg

variable {K : Type} [Field K] [CharZero K]

abbrev phTw (g2 s2 c0 xT : K) (P l : PowerSeries K) : PowerSeries K :=
  phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l

abbrev thTw (g2 s2 c0 xT : K) (P : PowerSeries K) : PowerSeries K :=
  thZ s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P)

def IsFibreZ (P tr : PowerSeries K) {ι : Type} [Fintype ι] (c : ι → K)
    (wp wm : ι → PowerSeries K) (al S : K) : Prop :=
  (∀ Q, HasSecondLogDeriv (wpShift P (c Q)) (2 * P - wp Q - wm Q)) ∧
    PowerSeries.C (al ^ 2) * PowerSeries.rescale al tr = ∑ Q, (wp Q + wm Q) - PowerSeries.C S

def IsFibreCurve (W : WeierstrassCurve K) (xT yT : K) {ι : Type} [Fintype ι] (xQ yQ : ι → K)
    (al S : K) : Prop :=
  (∀ Q, W.toAffine.Equation (xQ Q) (yQ Q)) ∧
    PowerSeries.C (al ^ 2) * PowerSeries.rescale al (wTr W xT yT) =
      ∑ Q, (wTr W (xQ Q) (yQ Q) + wTr W (xQ Q) (W.toAffine.negY (xQ Q) (yQ Q))) - PowerSeries.C S

end Alg

end Formalism.L2.Th1.B
end
end

