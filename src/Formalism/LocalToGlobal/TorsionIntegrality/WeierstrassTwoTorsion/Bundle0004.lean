import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Laurent
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowThird
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalGroupEqWSeries
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ToLTDenMulInv
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
section
universe u v

namespace Formalism.L2.Th1.A

theorem compInvSpec : CompInvSpec.{u} := composition_inverse_spec
theorem compInvMap : CompInvMap.{u, v} := composition_inverse_map
theorem integSpec : IntegSpec.{u} := integration_spec

theorem flowNegUW : FlowNegUW.{u} := chartFlowNegation
theorem chordRegular : ChordRegular.{u} := chordFormula
theorem flowTranslate : FlowTranslate.{u} := flowTranslation
theorem flowLogDeriv : FlowLogDeriv.{u} := flowLogDerivative
theorem flowTwoTorsion : FlowTwoTorsion.{u} := twoTorsionTranslation
theorem flowTwoTorsionWp : FlowTwoTorsionWp.{u} := twoTorsionTranslationWeierstrassForm

theorem wSerSpec : WSerSpec.{u} := w_series_spec
theorem wSerFactor : WSerFactor.{u} := w_series_factorization
theorem unitSpec : UnitSpec.{u} := invariant_differential_units
theorem seriesMap : SeriesMap.{u, v} := series_map
theorem flowU : FlowU.{u} := unit_flow
theorem dLSpec : DLSpec.{u} := invariant_derivation_spec
theorem flowL : FlowL.{u} := invariant_flow
theorem iSerSpec : ISerSpec.{u} := iSerSpec_of wSerSpec wSerFactor unitSpec flowU flowNegUW

theorem logSpec : LogSpec.{u} := logSpec_of integSpec unitSpec
theorem expSpec : ExpSpec.{u} := expSpec_of integSpec compInvSpec unitSpec
theorem chainZ : ChainZ.{u} := chainZ_of integSpec compInvSpec unitSpec
theorem logNeg : LogNeg.{u} := logNeg_of integSpec compInvSpec unitSpec iSerSpec
theorem flowZ : FlowZ.{u} := flowZ_of expSpec chainZ
theorem wpODE : WpODE.{u} := wpODE_of expSpec chainZ

theorem fglMap : FglMap.{u, v} := formal_group_map
theorem fglChord : FglChord.{u} := formal_group_chord
theorem fglSum : FglSum.{u} := formal_group_sum

theorem tSpec : TSpec.{u} := tSpec_of iSerSpec
theorem plusChord : PlusChord.{u} := plusChord_of flowL
theorem plusFlow : PlusFlow.{u} := plusFlow_of dLSpec flowL
theorem plusNeg : PlusNeg.{u} := plusNeg_of iSerSpec
theorem plusMap : PlusMap.{u, v} := addition_map

end Formalism.L2.Th1.A
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementJ
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.A

def IntModel {K : Type} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1

def BridgeWp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.B.IsWp (g₂ W) (g₃ W) (wpReg W)

def BridgeLaw : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.LawLog (fgl W) (logSer W) ∧ Formalism.L2.Th1.B.IsInv (logSer W) (iSer W) ∧
    (‖(2 : K)‖ = 1 → Formalism.L2.Th1.B.IsHalf (logSer W) (halfSer W))

def BridgeCurve : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.CurveHyp (fgl W) (iSer W) (logSer W) (wpReg W) (xS W) (W.b₂ / 12)

def BridgeTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K)
    (xT yT : K), W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    (tS W xT).subst (expSer W) = Formalism.L2.Th1.B.wOf (xT + W.b₂ / 12) (wpReg W) ∧
    Formalism.L2.Th1.B.IsW (3 * (xT + W.b₂ / 12)) (3 * (xT + W.b₂ / 12) ^ 2 - g₂ W / 4)
      ((tS W xT).subst (expSer W)) ∧
    (IntModel W → ‖xT‖ ≤ 1 → Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) (tS W xT))

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.A

def shortW {K : Type} [Field K] (g2 g3 : K) : WeierstrassCurve K :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -g2 / 4, a₆ := -g3 / 4 }

def ShortInv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    (shortW g2 g3).b₂ = 0 ∧ g₂ (shortW g2 g3) = g2 ∧ g₃ (shortW g2 g3) = g3 ∧
    (shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2

def WpNumEq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.CM.wpNum (g₂ W) (g₃ W) = 1 + X ^ 2 * wpReg W ∧
    Formalism.L2.Th1.CM.wpDen (g₂ W) (g₃ W) = 1 - C (1 / 2 : K) * X ^ 3 * derivative K (wpReg W)

def WpRegInv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W W' : WeierstrassCurve K),
    g₂ W = g₂ W' → g₃ W = g₃ W' → wpReg W = wpReg W'

def USerEq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    Formalism.L2.Th1.CM.uSer g2 g3 = expSer (shortW g2 g3)

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementN
section
open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def PlusZCleared : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    derivative K (derivative K (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))))
        * (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12)))
      - derivative K (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))) ^ 2
      = (2 * wpReg W - ((xPlus W xP yP).subst (expSer W) + C (W.b₂ / 12))
          - ((xPlus W xP (W.toAffine.negY xP yP)).subst (expSer W) + C (W.b₂ / 12)))
        * (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))) ^ 2

def PlusNegY : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    (yPlus W xP yP).subst (iSer W) = (curveS W).toAffine.negY
      (xPlus W xP (W.toAffine.negY xP yP)) (yPlus W xP (W.toAffine.negY xP yP)) ∧
    X ^ 3 * (xPlus W xP yP - xPlus W xP (W.toAffine.negY xP yP))
      = -(C (2 * yP + W.a₁ * xP + W.a₃) * (2 * yS W + C W.a₁ * X * xS W + C W.a₃ * X ^ 3)
          * tS W xP ^ 2) ∧
    coeff 1 (xPlus W xP yP) = 2 * yP + W.a₁ * xP + W.a₃

def ExpAdd : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    (expSer W).subst (U₁ + U₂ : MvPowerSeries (Fin 2) K)
      = MvPowerSeries.subst (![(expSer W).subst (U₁ : MvPowerSeries (Fin 2) K),
          (expSer W).subst (U₂ : MvPowerSeries (Fin 2) K)] : Fin 2 → MvPowerSeries (Fin 2) K) (fgl W)

def FlowUnique : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (x y x' y' : R⟦X⟧),
    (∀ (n : ℕ) (r : R), n ≠ 0 → (n : R) * r = 0 → r = 0) →
    IsFlow (curveS W) (D W) x y → IsFlow (curveS W) (D W) x' y' →
    constantCoeff x = constantCoeff x' → constantCoeff y = constantCoeff y' → x = x' ∧ y = y'

def ChordEquation : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP xQ yQ t : R),
    W.toAffine.Equation xP yP → W.toAffine.Equation xQ yQ → t * (xP - xQ) = 1 →
    W.toAffine.Equation (W.toAffine.addX xP xQ ((yP - yQ) * t))
      (W.toAffine.addY xP xQ yP ((yP - yQ) * t))

def PlusPlus : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP xQ yQ t : R),
    (∀ (n : ℕ) (r : R), n ≠ 0 → (n : R) * r = 0 → r = 0) →
    W.toAffine.Equation xP yP → W.toAffine.Equation xQ yQ → t * (xP - xQ) = 1 →
    ∀ s : R⟦X⟧, s * (xPlus W xP yP - C xQ) = 1 →
    xPlus W (W.toAffine.addX xP xQ ((yP - yQ) * t)) (W.toAffine.addY xP xQ yP ((yP - yQ) * t))
      = (curveS W).toAffine.addX (xPlus W xP yP) (C xQ) ((yPlus W xP yP - C yQ) * s) ∧
    yPlus W (W.toAffine.addX xP xQ ((yP - yQ) * t)) (W.toAffine.addY xP xQ yP ((yP - yQ) * t))
      = (curveS W).toAffine.addY (xPlus W xP yP) (C xQ) (yPlus W xP yP)
          ((yPlus W xP yP - C yQ) * s)

end Formalism.L2.Th1.A
end
end

