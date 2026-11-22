import Formalism.YangianSpanCharacter.Bundle0001

-- bundled from Formalism.YangianSpanCharacter.ExchangeGen
section
namespace Formalism.YangianSpanCharacter.T

open Matrix

def pt3 {R : Type*} (M : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R :=
  Matrix.of fun a b => M (a.1, a.2.1, b.2.2) (b.1, b.2.1, a.2.2)

def Tbt {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (Y : R) (p c ci : A) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.1 then Tm Y p c ci jl.2 ik.2 else 0

def YBEt : Prop :=
  ∀ (R : Type) [CommRing R] (Y Y' Yb : R),
    ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R) - sizeConstantAtParamsWeight R) *
        pt3 ((Yb - Y') • 1 - flipOneThree R) * pt3 ((Yb - Y) • 1 - flipTwoThree R) =
      pt3 ((Yb - Y) • 1 - flipTwoThree R) * pt3 ((Yb - Y') • 1 - flipOneThree R) *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R) - sizeConstantAtParamsWeight R)

def ExchangeT : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (p c ci : A) (Y Yb : R),
    WeylRel p c ci →
      Tbt Yb p c ci * pt1 ((Yb - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) *
          T1 Y p c ci =
        T1 Y p c ci * pt1 ((Yb - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) *
          Tbt Yb p c ci

def Gauge : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (p c ci hi θ : A) (Y : R),
    hi * c = c * hi → hi * ci = ci * hi → p * hi = hi * p - hi * θ →
      Tm Y p c ci * Matrix.diagonal (fun _ => hi) =
        Matrix.diagonal (fun _ => hi) * (Tm Y p c ci - !![θ, 0; 0, 0])

def JFlip : Prop :=
  ∀ (R : Type) [CommRing R],
    J0 R * (-J0 R) = 1 ∧ J0 R * (1 - Pf R) * (-J0 R) = pt1 (Pf R)

def E1 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.2 = jl.2 then M ik.1 jl.1 else 0

def E2 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.1 then M ik.2 jl.2 else 0

def ExchangeGen : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (M0 Mb : Matrix (Fin 2) (Fin 2) A) (d : R),
    (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E1 Mb * E2 M0 =
        E2 M0 * E1 Mb * (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) →
      E2 Mbᵀ * pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E1 M0 =
        E1 M0 * pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E2 Mbᵀ

end Formalism.YangianSpanCharacter.T
end

-- bundled from Formalism.YangianSpanCharacter.StatementY
section
namespace Formalism.YangianSpanCharacter.Y

open Matrix Formalism.YangianSpanCharacter.T

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

def lf (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u : 𝕜) : A := τinv u * t u 1 0

def mf (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u : 𝕜) : A := τinv u * t u 0 1

def hf (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (u : 𝕜) : A := q u • (τinv u * τinv (u + 1))

def eta (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u v : 𝕜) : A :=
  (u - v)⁻¹ • (lf t τinv u - lf t τinv v)

def mu (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u v : 𝕜) : A :=
  (u - v)⁻¹ • (mf t τinv u - mf t τinv v)

def ModHyp (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜) : Prop :=
  (∀ (u v : 𝕜) (i j k l : Fin 2),
      (u - v) • (t u i j * t v k l - t v k l * t u i j) = t u k j * t v i l - t v k j * t u i l) ∧
    (∀ Y : 𝕜, (t (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J A * t Y = q Y • Formalism.YangianSpanCharacter.T.J A) ∧
    (∀ Y : 𝕜, t Y * Formalism.YangianSpanCharacter.T.J A * (t (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J A) ∧
    (∀ u ∈ S, t u 1 1 * τinv u = 1 ∧ τinv u * t u 1 1 = 1) ∧
    (∀ u v : 𝕜, Commute (t u 1 1) (t v 1 1)) ∧
    (∀ u v : 𝕜, Commute (t u 1 0) (t v 1 0))

def MShift : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y : 𝕜, Y ∈ S → Y + 1 ∈ S → mf t τinv (Y + 1) = t Y 0 1 * τinv Y

def QuasiDet : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y : 𝕜, Y ∈ S → Y + 1 ∈ S → t Y 0 0 - t Y 0 1 * τinv Y * t Y 1 0 = q Y • τinv (Y + 1)

def Y1 : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → v ∈ S → u ≠ v →
      t u 1 1 * lf t τinv v - lf t τinv v * t u 1 1 = -(t u 1 1 * eta t τinv u v)

def Y1' : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → v ∈ S → u ≠ v →
      t u 1 1 * mf t τinv v - mf t τinv v * t u 1 1 = t u 1 1 * mu t τinv u v

def Y2 : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → v ∈ S → u ≠ v →
      lf t τinv u * lf t τinv v - lf t τinv v * lf t τinv u =
        eta t τinv u v * (lf t τinv u - lf t τinv v)

def Y3 : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → u + 1 ∈ S → u - 1 ∈ S → v ∈ S → v + 1 ∈ S → u ≠ v →
      (u - v - 1) • (mf t τinv u * lf t τinv v - lf t τinv v * mf t τinv u) =
        hf τinv q v - hf τinv q (u - 1)

def ModHypModel : Prop :=
  ModHyp (𝕜 := ℚ) (A := ℚ) (fun _ => !![2, 1; 1, 1]) (fun _ => 1) (fun _ => 1) Set.univ

end Formalism.YangianSpanCharacter.Y
end

-- bundled from Formalism.YangianSpanCharacter.TJTrev
section
namespace Formalism.YangianSpanCharacter.T

open Matrix

def TJTrev : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (q d di : A) (Y : R),
    d * di = 1 → di * d = 1 → d * q = q * d + d →
      Tm (Y + 1) q d di * J A * (Tm Y q d di)ᵀ = J A

end Formalism.YangianSpanCharacter.T
end

