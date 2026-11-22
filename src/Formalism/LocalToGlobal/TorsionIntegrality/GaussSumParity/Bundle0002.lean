import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0004
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0001

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.GramExists
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (lgF at1 UnrOK)

def EigenOdd : Prop :=
  ∀ (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l → ∀ (ι : Type) [Fintype ι]
    (om oms : ι → K) (b : K) (c : ι → ι → K), (∀ r r', σ (σ (c r' r)) = c r' r) →
    (∀ r, b * oms r = ∑ r', σ (c r' r) * oms r') → ∀ s : ZMod d, s.val % 2 = 1 →
    MvPowerSeries.subst (fun x : Bool × ι => if x.1 = true then
        PowerSeries.subst (∑ r, MvPowerSeries.C (c x.2 r) * at1 (true, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K)) (zXY l σ om oms s) =
      MvPowerSeries.C (σ^[s.val] b) * zXY l σ om oms s

def GramExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → (∃ ζ : K, IsPrimitiveRoot ζ (l ^ 2 - 1)) →
    ∀ (E : Type) [Fintype E] [DecidableEq E],
      ∃ c : Bool × E → Bool × E → K,
        (∀ k x, ‖c k x‖ ≤ 1 ∧ σ (σ (c k x)) = c k x) ∧
        ∀ x x' : Bool × E, ∑ k, c k x * σ (c k x') = if x.1 ≠ x'.1 ∧ x.2 = x'.2 then 1 else 0

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.RingAFacts
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def RingAFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    (∀ x ∈ ringA l, ‖x‖ ≤ 1) ∧
    (∀ x ∈ ringA l, ∃ f : ℕ, 0 < f ∧ ∃ y ∈ ringA l, x ^ (l ^ f) - x = (l : ℂ_[l]) * y)

def FrobA : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    ∃ σ0 : ringA l →+* ringA l,
      (∀ ζ : ringA l, (ζ : ℂ_[l]) ∈ muPrime l → σ0 ζ = ζ ^ l) ∧
      ∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y

def FrobAIsom : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (σ0 : ringA l →+* ringA l),
    (∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y) →
    ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp BHyp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog BetaHyp)

section Defs

variable {K : Type} [Field K]

def thetaS (l : ℕ) (g2 g3 ε : K) : PowerSeries K :=
  PowerSeries.subst (PowerSeries.C ε * lgF K l) (Formalism.L2.Th1.CM.uSer g2 g3)

variable [CharZero K]

def phFF (l : ℕ) (g2 g3 s2 ε : K) : PowerSeries K :=
  -PowerSeries.subst (PowerSeries.C ε * lgF K l)
      (Formalism.L2.Th1.B.sigS (Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW g2 g3))) +
    PowerSeries.C (s2 / 2) * (PowerSeries.C ε * lgF K l) ^ 2 -
    Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU (lgF K l))

def phCurve (g2 g3 s2 : K) : PowerSeries K :=
  Formalism.L2.Th1.B.phO s2 (Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW g2 g3)) (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3))

end Defs

def LtLogIsLgF : Prop :=
  ∀ (K : Type) [Field K] (l : ℕ), 2 ≤ l → Formalism.L2.Th1.CM.ltLog K l = lgF K l

def ThetaHom : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ = (l : ℝ)⁻¹ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ g2 g3 ε : K,
    PowerSeries.subst (thetaS l g2 g3 ε) (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)) =
      PowerSeries.C ε * lgF K l ∧
    IsHom F (Formalism.L2.Th1.A.fgl (Formalism.L2.Th1.A.shortW g2 g3)) (thetaS l g2 g3 ε)

def PhCompare : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ∀ g2 g3 s2 ε : K, ‖ε‖ = 1 → (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
    Simeq (phFF l g2 g3 s2 ε : MvPowerSeries Unit K)
      (PowerSeries.subst (thetaS l g2 g3 ε) (phCurve g2 g3 s2))

def CurveExponentCoboundaryCocycle : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime → 2 < l →
    ‖(l : K)‖ = (l : ℝ)⁻¹ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ g2 g3 s2 ε : K, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
      (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
      F1 F (cob F (phFF l g2 g3 s2 ε))

def BHypCurve : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ g2 g3 s2 ε : K, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
      (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
    ∀ (ι : Type) [Fintype ι] (om oms : ι → K), OwOK d σ om oms →
    ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
      BHyp l d ⊤ ζ (beMean l σ (cob F (phFF l g2 g3 s2 ε)) om oms ζ)

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementN
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog Simeq)

def ChainNonVacuous : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 2 < l → ∀ (ν r0 r1 : ℕ) [NeZero ν],
    ∃ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin ν → MaximalUnramifiedExtension l)
      (U0 Φ : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) ℂ_[l]) (ph : PowerSeries (MaximalUnramifiedExtension l)),
      UnrOK (MaximalUnramifiedExtension l) l σ ∧ CompleteSpace (MaximalUnramifiedExtension l) ∧ (∀ a, ‖(MaximalUnramifiedExtension l).subtype a‖ = ‖a‖) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1)) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ (2 * ν) - 1)) ∧ 2 ≤ 2 * ν ∧ Even (2 * ν) ∧
      (∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l])) ∧
      OwOK (2 * ν) σ om oms ∧ TrDual (2 * ν) σ om oms ∧ IsLawOfLog l F ∧ F1 F be ∧ F2 l σ be ∧
      ¬ Simeq be 0 ∧ Integral U0 ∧ MvPowerSeries.constantCoeff Φ = 0 ∧
      Simeq Φ (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be)) ∧
      Simeq (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be)

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TwoPlaces
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog bSum idM ZV serAlong)
open Formalism.InvariantFactorPaths.G7 (Simeq UnrOK IsLawOfLog)
open MvPowerSeries

abbrev PV (ι : Type) (N0 N1 : ℕ) := Bool × ι × Fin N0 × Fin N1

def TwoPlaces : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    [IsUltrametricDist K] [CharZero K] (l d₁ d₂ N0 N1 : ℕ) [NeZero d₁] [NeZero d₂]
    (σ : K0 →+* K0) (j : K0 →+* K),
    UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) → 2 ≤ d₁ → Even d₁ → 2 ≤ d₂ → Even d₂ →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
      (om₁ oms₁ : ι₁ → K0) (om₂ oms₂ : ι₂ → K0),
      OwOK d₁ σ om₁ oms₁ → TrDual d₁ σ om₁ oms₁ → OwOK d₂ σ om₂ oms₂ → TrDual d₂ σ om₂ oms₂ →
    ∀ ζ₁ ζ₂ : K0, IsPrimitiveRoot ζ₁ (l ^ d₁ - 1) → IsPrimitiveRoot ζ₂ (l ^ d₂ - 1) →
    ∀ (U0 Φ : MvPowerSeries (PV ι₁ N0 N1 ⊕ PV ι₂ N0 N1) K), Integral U0 → constantCoeff Φ = 0 →
      Simeq Φ (serAlong Sum.inl (sumE (map j be0)) + serAlong Sum.inr (sumE (map j be0))) →
      ∃ U : MvPowerSeries (ZV d₁ N0 N1 ⊕ ZV d₂ N0 N1) K, Integral U ∧
        ∀ (g₁ : ZV d₁ N0 N1 → MvPowerSeries (ZV d₁ N0 N1) K)
          (g₂ : ZV d₂ N0 N1 → MvPowerSeries (ZV d₂ N0 N1) K),
          (∀ y, constantCoeff (g₁ y) = 0) → (∀ y, subst g₁ (entLog (K := K) l y) = X y) →
          (∀ y, constantCoeff (g₂ y) = 0) → (∀ y, subst g₂ (entLog (K := K) l y) = X y) →
          subst (Sum.elim (fun x => serAlong Sum.inl (xOfZ (d := d₁) l j σ om₁ oms₁ x))
              (fun x => serAlong Sum.inr (xOfZ (d := d₂) l j σ om₂ oms₂ x))) (mvExp (-Φ) * U0) =
            subst (Sum.elim (fun x => serAlong Sum.inl (g₁ x)) (fun x => serAlong Sum.inr (g₂ x))) U *
              (serAlong Sum.inl (mvExp (-(bSum (idM : ZV d₁ N0 N1 → ZV d₁ N0 N1 → K)
                  (map j (beMean l σ be0 om₁ oms₁ ζ₁))))) *
               serAlong Sum.inr (mvExp (-(bSum (idM : ZV d₂ N0 N1 → ZV d₂ N0 N1 → K)
                  (map j (beMean l σ be0 om₂ oms₂ ζ₂))))))

end Formalism.L2.Th1.D
end
end

