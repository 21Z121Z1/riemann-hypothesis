import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementS
import Formalism.GaussJetBounds.Bundle0006
import Formalism.GaussJetBounds.Bundle0005
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementR

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementK
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)

section DefsK

variable {K : Type} [Field K]

def kernelAt [CharZero K] (linv ph : PowerSeries K) {n m : Type} [Fintype n] [Fintype m] (c : n → K)
    (A : n → m → K) (G : MvPowerSeries n K) : MvPowerSeries m K :=
  linSub A (toZ linv (mvExp (-(phSum c ph)) * G))

def betaPair (H : Type) [Fintype H] (N0 N1 : ℕ) (u : H → K) :
    MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K :=
  ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
    MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2)

def pairMatB {H : Type} [DecidableEq H] {N0 N1 : ℕ} (I : K)
    (i y : (Bool × H) × Fin N0 × Fin N1) : K :=
  if i.1.2 = y.1.2 ∧ i.2 = y.2 then (if i.1.1 = false then 1 else if y.1.1 = false then I else -I)
  else 0

end DefsK

def KernelShape : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K) (d : ℕ),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → ShapeAt l linv ph d → (d : K) ≠ 0 →
    ∀ (H : Type) [Fintype H] (N0 N1 : ℕ) (n : Type) [Fintype n] (c : n → K)
      (A : n → ((Bool × H) × Fin N0 × Fin N1) → K) (u : H → K) (th : K)
      (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K),
    ‖(2 : K)‖ = 1 → (∀ i, ‖c i‖ ≤ 1) → (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(d : K)‖ ^ (1 / 2 : ℝ) →
    MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum c) = MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    ∃ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K, JetsIntegral sg ∧
      kernelAt linv ph c A G = Formalism.DworkPowerSeriesWeights.mvExp ((-(jet l ph 2)) • betaPair H N0 N1 u) * sg

def KernelThmB : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K) (d : ℕ),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → ShapeAt l linv ph d → 0 < ‖(d : K)‖ → ‖(d : K)‖ < 1 →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (n : Type) [Fintype n] (c : n → K)
      (A : n → ((Bool × H) × Fin N0 × Fin N1) → K) (u : H → K) (th : K)
      (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K),
    ‖(2 : K)‖ = 1 → (∀ i, ‖c i‖ ≤ 1) → (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(d : K)‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum c) = MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    ∀ (x : Bool × H → Matrix (Fin N0) (Fin N0) K), (∀ τ i a, ‖x τ i a‖ ≤ 1) →
      (∀ τ, ‖(x τ).det‖ = 1) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (p : ∀ τ, Fin (colN τ) → ℕ)
      (hp : ∀ τ c, p τ c ≤ N0), (∀ τ c, 1 ≤ p τ c) → ∀ (I : ∀ τ c, Fin (p τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ p τ c)).card) → (∀ τ, size τ = ∑ c, p τ c) →
      ‖jetPair (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (∑ a, MvPolynomial.C (x τ i a) * MvPolynomial.X (τ, a, b) :
              MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K)) (p τ) (hp τ) (I τ))
          (kernelAt linv ph c A G)‖ ≤
        ‖(d : K)‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))

def KernelThmBGauss : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l linv ph : PowerSeries ℂ_[p]),
    IsLogPair l linv → IsOneUnit (unitBall ℂ_[p]) (PowerSeries.derivative ℂ_[p] l) →
    PowerSeries.constantCoeff ph = 0 → ShapeAt l linv ph p →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (n : Type) [Fintype n] (c : n → ℂ_[p])
      (A : n → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p])
      (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p]),
    ‖(2 : ℂ_[p])‖ = 1 → (∀ i, ‖c i‖ ≤ 1) → (∀ i x, ‖A i x‖ ≤ 1) →
    ‖th‖ ≤ ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum c) = MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
    ∀ G : MvPowerSeries n ℂ_[p], IntMv (unitBall ℂ_[p]) G →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
      (hht : ∀ τ c, ht τ c ≤ N0), (∀ τ c, 1 ≤ ht τ c) → ∀ (I : ∀ τ c, Fin (ht τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card) →
      (∀ τ, size τ = ∑ c, ht τ c) →
    ∀ nn : ((Bool × H) × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff nn (jetPairPoly (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) =>
              (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (τ, i, a)) * MvPolynomial.X (τ, a, b) :
                MvPolynomial ((Bool × H) × Fin N0 × Fin N1)
                  (MvPolynomial ((Bool × H) × Fin N0 × Fin N0) ℂ_[p])))
            (ht τ) (hht τ) (I τ))
          (kernelAt linv ph c A G))‖ ≤
        ‖(p : ℂ_[p])‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))

def PairedSquaresB : Prop :=
  ∀ (K : Type) [Field K] (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (I : K), I ^ 2 = -1 →
    linSub (pairMatB (H := H) (N0 := N0) (N1 := N1) I) (sqSum (fun _ => (1 : K))) =
      MvPowerSeries.C 2 * betaPair H N0 N1 (fun _ => 2)

def CurvePairedThmB : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ‖(2 : K)‖ = 1 →
    ∀ (s2 al albar : K) (d : ℕ) (t : ℤ) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al‖ = 1 → al + albar = (t : K) →
    (al - albar) ^ 2 = -(d : K) → d ≠ 0 → ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 →
    al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) → ‖(d : K)‖ < 1 →
    ∀ (Im : K), Im ^ 2 = -1 →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
      (G : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K), IntMv (unitBall K) G →
    ∀ (x : Bool × H → Matrix (Fin N0) (Fin N0) K), (∀ τ i a, ‖x τ i a‖ ≤ 1) →
      (∀ τ, ‖(x τ).det‖ = 1) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (p : ∀ τ, Fin (colN τ) → ℕ)
      (hp : ∀ τ c, p τ c ≤ N0), (∀ τ c, 1 ≤ p τ c) → ∀ (I : ∀ τ c, Fin (p τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ p τ c)).card) → (∀ τ, size τ = ∑ c, p τ c) →
      ‖jetPair (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (∑ a, MvPolynomial.C (x τ i a) * MvPolynomial.X (τ, a, b) :
              MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K)) (p τ) (hp τ) (I τ))
          (kernelAt (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (fun _ => (1 : K))
            (pairMatB Im) G)‖ ≤
        ‖(d : K)‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))

end Formalism.L2.Th1.G
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementT
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xPlus)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

section DefsT

variable {K : Type} [Field K]

def th0 [CharZero K] (W : WeierstrassCurve K) (x0 y0 s2 : K) : PowerSeries K :=
  mvExp (-(lam (wTr W x0 y0) s2))

def phT (W : WeierstrassCurve K) (x0 y0 s2 : K) : PowerSeries K :=
  PowerSeries.subst (logSer W) (lam (wTr W x0 y0) s2)

end DefsT

def ThetaZeroSquare : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (x0 y0 s2 : K),
    W.toAffine.Equation x0 y0 → 2 * y0 + W.a₁ * x0 + W.a₃ = 0 →
    PowerSeries.X ^ 2 * th0 W x0 y0 s2 ^ 2 =
      sgStar (wpReg W) s2 ^ 2 * wpShift (wpReg W) (x0 + W.b₂ / 12)

def ThetaZeroEven : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (x0 y0 s2 : K),
    W.toAffine.Equation x0 y0 → 2 * y0 + W.a₁ * x0 + W.a₃ = 0 →
    PowerSeries.constantCoeff (th0 W x0 y0 s2) = 1 ∧
      ∀ n : ℕ, Odd n → PowerSeries.coeff n (th0 W x0 y0 s2) = 0

def ShiftedSigmaConstantIntegralOfIsogenySum : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (s2 al albar b : K) (ι : Type)
    [Fintype ι] (xP : ι → K),
    al * albar = (Fintype.card ι : K) + 1 → ‖al * (al - albar)‖ = 1 → (∀ P, ‖xP P‖ ≤ 1) →
    ‖(al ^ 2 - 1) * (b / 12)‖ ≤ 1 → al * (al - albar) * s2 = ∑ P, (xP P + b / 12) →
    ‖s2 + b / 12‖ ≤ 1

def ThetaZeroJetsTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ∀ (x0 y0 s2 : K), W.toAffine.Equation x0 y0 →
    2 * y0 + W.a₁ * x0 + W.a₃ = 0 → ‖x0‖ ≤ 1 → ‖y0‖ ≤ 1 → ‖x0 + W.b₂ / 12 + s2‖ ≤ 1 →
    (∀ i : ℕ, 1 ≤ i → ‖jet (logSer W) (phT W x0 y0 s2) i‖ ≤ 1) ∧
    JetsIn1 (unitBall K) (th0 W x0 y0 s2) ∧
    ∀ i : ℕ, ‖jet (logSer W) (PowerSeries.subst (logSer W) (th0 W x0 y0 s2)) i‖ ≤ 1

def ThetaZeroJetsCurve : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W →
    ∀ (s2 al albar : K) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al * (al - albar)‖ = 1 →
    ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 → al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) →
    ∀ (x0 y0 : K), W.toAffine.Equation x0 y0 → 2 * y0 + W.a₁ * x0 + W.a₃ = 0 →
    ‖x0‖ ≤ 1 → ‖y0‖ ≤ 1 →
    JetsIn1 (unitBall K) (th0 W x0 y0 s2) ∧
      ∀ i : ℕ, 1 ≤ i → ‖jet (logSer W) (phT W x0 y0 s2) i‖ ≤ 1

def KernelTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → (∀ i : ℕ, 1 ≤ i → ‖jet l ph i‖ ≤ 1) →
    ∀ (n : Type) [Fintype n] (c : n → K), (∀ i, ‖c i‖ ≤ 1) →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    JetsIntegral (toZ linv (mvExp (-(phSum c ph)) * G)) ∧
    ∀ P : MvPolynomial n K, (∀ m, ‖MvPolynomial.coeff m P‖ ≤ 1) →
      ‖jetPair P (toZ linv (mvExp (-(phSum c ph)) * G))‖ ≤ 1

def CurveKernelTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W →
    ∀ (s2 al albar : K) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al * (al - albar)‖ = 1 →
    ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 → al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) →
    ∀ (x0 y0 : K), W.toAffine.Equation x0 y0 → 2 * y0 + W.a₁ * x0 + W.a₃ = 0 →
    ‖x0‖ ≤ 1 → ‖y0‖ ≤ 1 →
    ∀ (n : Type) [Fintype n] (c : n → K), (∀ i, ‖c i‖ ≤ 1) →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    ∀ P : MvPolynomial n K, (∀ m, ‖MvPolynomial.coeff m P‖ ≤ 1) →
      ‖jetPair P (toZ (expSer W) (mvExp (-(phSum c (phT W x0 y0 s2))) * G))‖ ≤ 1

def SplitVanishTwo : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ (l linv ph : PowerSeries K) (a b : K),
    Frame R l linv ph → F1 R l linv ph → EndInt R l linv a →
    a ∈ closure (Set.range (fun n : ℤ => (n : K))) → PhNormAt R l linv ph a b →
    a ≠ 0 → a ≠ b → b ≠ 1 →
    IsBinomScalar R (a * (a - b))⁻¹ → IsBinomScalar R (a * (1 - b))⁻¹ →
    LG R ph

end Formalism.L2.Th1.G
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementV
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

def IntUnram : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K),
    Frame (unitBall K) l linv ph → IsOneUnit (unitBall K) (PowerSeries.derivative K l) →
    F1 (unitBall K) l linv ph → (∀ i : ℕ, 1 ≤ i → ‖jet l ph i‖ ≤ 1) →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt (unitBall K) l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar (unitBall K) (τ z)) →
    (∀ α : O, PhNormAt (unitBall K) l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt (unitBall K) l linv ph (τ α) (τ (star α))) →
    ∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] (w : n → O), (∀ j, star (w j) = w j) →
    ∀ δ : m → Fin 4 × n → O,
      (∀ a b, ∑ i, star (δ i a) * δ i b = if a = b then w a.2 else 0) →
    ∀ (Th : MvPowerSeries n K) (G : MvPowerSeries (Fin 4 × n) K), IntMv (unitBall K) G →
      tens4 Th = toZ linv (mvExp (-(phIso τ l linv ph δ)) * G) →
    JetsIntegral Th ∧
    ∀ (ν : Type) [Fintype ν] (A : n → ν → K), (∀ i x, ‖A i x‖ ≤ 1) →
    ∀ P : MvPolynomial ν K, (∀ k, ‖MvPolynomial.coeff k P‖ ≤ 1) →
      ‖jetPair P (linSub A Th)‖ ≤ 1

def CurveJetsUnram : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ‖(2 : K)‖ = 1 →
    ∀ (s2 al albar : K) (t : ℤ) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al‖ = 1 → al + albar = (t : K) →
    ‖al - albar‖ = 1 → ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 →
    al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) →
    ∀ i : ℕ, 1 ≤ i → ‖jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) i‖ ≤ 1

end Formalism.L2.Th1.G
end
end

