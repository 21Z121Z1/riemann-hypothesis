import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0002

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI
section
open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def WpCleared : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    constantCoeff (wpReg W) = 0 ∧ (∀ n : ℕ, Odd n → coeff n (wpReg W) = 0) ∧
    (-2 + X ^ 3 * derivative K (wpReg W)) ^ 2 =
      4 * (1 + X ^ 2 * wpReg W) ^ 3 - C (g₂ W) * X ^ 4 * (1 + X ^ 2 * wpReg W) - C (g₃ W) * X ^ 6

def WpInU : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    X ^ 2 * (1 + logSer W ^ 2 * (wpReg W).subst (logSer W)) =
      logSer W ^ 2 * (xS W + C (W.b₂ / 12) * X ^ 2)

def TInZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP : K),
    (tS W xP).subst (expSer W) * (1 + X ^ 2 * wpReg W - C (xP + W.b₂ / 12) * X ^ 2) = X ^ 2

def CubeTwoR : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    ∃ c : MvPowerSeries (Fin 2) R, MvPowerSeries.constantCoeff c = -1 ∧
      U₂ ^ 2 * (xS W).subst (U₁ : MvPowerSeries (Fin 2) R)
        - U₁ ^ 2 * (xS W).subst (U₂ : MvPowerSeries (Fin 2) R)
        = c * fgl W * MvPowerSeries.subst
            (![U₁, (iSer W).subst (U₂ : MvPowerSeries (Fin 2) R)] :
              Fin 2 → MvPowerSeries (Fin 2) R) (fgl W)

def CubeThreeR : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    let t : Fin 3 → MvPowerSeries (Fin 3) R := fun i => MvPowerSeries.X i
    let row : Fin 3 → Fin 3 → MvPowerSeries (Fin 3) R := fun i =>
      ![t i ^ 3, t i * (xS W).subst (t i), (yS W).subst (t i)]
    ∃ e : MvPowerSeries (Fin 3) R, MvPowerSeries.constantCoeff e = -1 ∧
      (Matrix.of row).det
        = e * MvPowerSeries.subst
              (![MvPowerSeries.subst (![t 0, t 1] : Fin 2 → MvPowerSeries (Fin 3) R) (fgl W), t 2] :
                Fin 2 → MvPowerSeries (Fin 3) R) (fgl W)
            * (t 0 - t 1) * (t 0 - t 2) * (t 1 - t 2)

def CoeffMem : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (S : Subring R),
    W.a₁ ∈ S → W.a₂ ∈ S → W.a₃ ∈ S → W.a₄ ∈ S → W.a₆ ∈ S →
    (∀ n, coeff n (wSer W) ∈ S) ∧ (∀ n, coeff n (xS W) ∈ S) ∧ (∀ n, coeff n (yS W) ∈ S) ∧
    (∀ n, coeff n (fw W) ∈ S) ∧ (∀ n, coeff n (om W) ∈ S) ∧ (∀ n, coeff n (iSer W) ∈ S) ∧
    (∀ d, MvPowerSeries.coeff d (fgl W) ∈ S) ∧ (∀ (k : ℤ) n, coeff n (zSer W k) ∈ S) ∧
    ((∃ h ∈ S, 2 * h = 1) → ∀ n, coeff n (halfSer W) ∈ S) ∧
    (∀ xP ∈ S, ∀ n, coeff n (tS W xP) ∈ S) ∧
    (∀ xP ∈ S, ∀ yP ∈ S, ∀ n, coeff n (xPlus W xP yP) ∈ S ∧ coeff n (yPlus W xP yP) ∈ S)

def LogCoeff : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (n : ℕ),
    ((n + 1 : ℕ) : K) * coeff (n + 1) (logSer W) = coeff n (om W)

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementM
section
open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def ZMap : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [CharZero K] [Field L] [CharZero L] (φ : K →+* L)
    (W : WeierstrassCurve K),
    PowerSeries.map φ (logSer W) = logSer (W.map φ) ∧
    PowerSeries.map φ (expSer W) = expSer (W.map φ) ∧
    PowerSeries.map φ (wpReg W) = wpReg (W.map φ) ∧
    φ (g₂ W) = g₂ (W.map φ) ∧ φ (g₃ W) = g₃ (W.map φ)

def DiscRel : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    g₂ W ^ 3 - 27 * g₃ W ^ 2 = W.Δ

def ChainNeg : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (f : R⟦X⟧),
    D W (f.subst (iSer W)) = -(D W f).subst (iSer W)

def ChainZSer : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℤ),
    D W (zSer W n) = C (n : R) * (fw W).subst (zSer W n) ∧
    (om W).subst (zSer W n) * derivative R (zSer W n) = C (n : R) * om W ∧
    ∀ f : R⟦X⟧, D W (f.subst (zSer W n)) = C (n : R) * (D W f).subst (zSer W n)

def ChainFgl : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (f : R⟦X⟧),
    (fw W).subst (U₁ : MvPowerSeries (Fin 2) R) * MvPowerSeries.pderiv R 0 (f.subst (fgl W))
      = (D W f).subst (fgl W) ∧
    (fw W).subst (U₂ : MvPowerSeries (Fin 2) R) * MvPowerSeries.pderiv R 1 (f.subst (fgl W))
      = (D W f).subst (fgl W)

def ConstOfD : Prop :=
  ∀ (R : Type u) [CommRing R] [IsAddTorsionFree R] (W : WeierstrassCurve R),
    (∀ f : R⟦X⟧, D W f = 0 → f = C (constantCoeff f)) ∧
    (∀ f : LaurentSeries R, dL f = 0 → f = HahnSeries.C (f.coeff 0)) ∧
    (∀ f : LaurentSeries R, DL W f = 0 → f = HahnSeries.C (f.coeff 0))

def JetZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (f : K⟦X⟧) (n : ℕ),
    (n.factorial : K) * coeff n (f.subst (expSer W)) = constantCoeff ((D W)^[n] f)

def JetMem : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (S : Subring K),
    W.a₁ ∈ S → W.a₂ ∈ S → W.a₃ ∈ S → W.a₄ ∈ S → W.a₆ ∈ S →
    (∀ f : K⟦X⟧, (∀ n, coeff n f ∈ S) → ∀ n, coeff n (D W f) ∈ S) ∧
    (∀ f : K⟦X⟧, (∀ n, coeff n f ∈ S) → ∀ n : ℕ,
      (n.factorial : K) * coeff n (f.subst (expSer W)) ∈ S) ∧
    ∀ n : ℕ, (n.factorial : K) * coeff n (expSer W) ∈ S

def WpPrimeShape : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    dL (wpL W) = -2 * uPow (-3) + toL (derivative K (wpReg W)) ∧
    toL ((wSer W).subst (expSer W)) * yZ W = -1

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementO
section
open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def divSer {R : Type u} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) : R⟦X⟧ := compInv (zSer W n)

def DivSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℤ), IsUnit (n : R) →
    constantCoeff (divSer W n) = 0 ∧ (n : R) * coeff 1 (divSer W n) = 1 ∧
    (zSer W n).subst (divSer W n) = X ∧ (divSer W n).subst (zSer W n) = X ∧
    (∀ (S : Type v) [CommRing S] (φ : R →+* S),
      PowerSeries.map φ (divSer W n) = divSer (W.map φ) n) ∧
    (n = 2 → divSer W n = halfSer W)

def DivLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (n : ℤ), n ≠ 0 →
    C (n : K) * (logSer W).subst (divSer W n) = logSer W

def FlowDouble : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y s : A),
    IsDer D → ConstCurve D W → IsFlow W D x y → s * (2 * y + W.a₁ * x + W.a₃) = 1 →
    let ℓ := (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * s
    W.toAffine.Equation (W.toAffine.addX x x ℓ) (W.toAffine.addY x x y ℓ) ∧
    D (W.toAffine.addX x x ℓ)
      = 2 * (2 * W.toAffine.addY x x y ℓ + W.a₁ * W.toAffine.addX x x ℓ + W.a₃) ∧
    W.toAffine.addX x x ℓ * (2 * y + W.a₁ * x + W.a₃) ^ 2
      = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈

end Formalism.L2.Th1.A
end
end

