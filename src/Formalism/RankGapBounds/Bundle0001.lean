import Mathlib

-- bundled from Formalism.RankGapBounds.CloudMinFalse
section
namespace Formalism.RankGapBounds.JumpSetsAlt

open Finset

def maxVal (l n : ℕ) : ℕ := (Finset.range (n + 1)).sup fun i => (Nat.choose n i).factorization l

def posPairs (N : ℕ) : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2

def eExp {N : ℕ} (U : Fin N → ℤ) (l : ℕ) : ℕ :=
  ∑ p ∈ posPairs N, maxVal l (U p.1 - U p.2 - 1).toNat

def SummandLeLog : Prop :=
  ∀ l n : ℕ, l.Prime → maxVal l n ≤ Nat.log l (n + 1)

def SummandZero : Prop :=
  ∀ l n : ℕ, l.Prime → n + 1 < l → maxVal l n = 0

def CloudLog : Prop :=
  ∀ (l k : ℕ) (U : Fin k → ℤ) (xm xp : ℤ), l.Prime → StrictAnti U →
    (∀ a, xm ≤ U a ∧ U a ≤ xp) →
    eExp U l ≤ k ^ 2 * Nat.log l ((xp - xm).toNat + k)

def CloudZero : Prop :=
  ∀ (l k : ℕ) (U : Fin k → ℤ) (xm xp : ℤ), l.Prime → StrictAnti U →
    (∀ a, xm ≤ U a ∧ U a ≤ xp) → (xp - xm).toNat + k < l →
    eExp U l = 0

def RestZero : Prop :=
  ∀ (l N : ℕ) (U : Fin N → ℤ) (lo : ℤ) (w : ℕ), l.Prime → StrictAnti U →
    (∀ a, lo ≤ U a ∧ U a ≤ lo + w) → w + N < l →
    eExp U l = 0

def RestLog : Prop :=
  ∀ (l N h : ℕ) (U : Fin N → ℤ), l.Prime → StrictAnti U →
    (∀ a, 0 ≤ U a ∧ U a ≤ h) →
    eExp U l ≤ N ^ 2 * Nat.log l (2 * h + N)

def CloudMinFalse : Prop :=
  ¬ ∀ (l k : ℕ) (U : Fin k → ℤ) (xm xp : ℤ), l.Prime → StrictAnti U →
    (∀ a, xm ≤ U a ∧ U a ≤ xp) →
    (eExp U l : ℝ) ≤ min ((k : ℝ) ^ 2 * (Nat.log l ((xp - xm).toNat + k) : ℝ))
                         ((k : ℝ) * (((xp - xm).toNat : ℝ) + k) / ((l : ℝ) - 1))

def witnessU : Fin 10 → ℤ := ![114, 113, 112, 111, 110, 4, 3, 2, 1, 0]

def WitnessBig : Prop := 25 ≤ eExp witnessU 101

end Formalism.RankGapBounds.JumpSetsAlt
end

-- bundled from Formalism.RankGapBounds.ConjInOrbit
section
namespace Formalism.RankGapBounds.ExistsSmulMemTer

abbrev G0 := ZMod 2 × ZMod 2
abbrev GG (e : ℕ) := G0 × ZMod (2 ^ e)

def sg : G0 := (1, 0)
def c0 : G0 := (0, 1)
def cc (e : ℕ) : GG e := (c0, 0)

def InPhi {e : ℕ} (γ : GG e) : Prop := γ.1.2 = 0

def place {e : ℕ} (γ : GG e) : GG e := if γ.1.2 = 0 then γ else γ + cc e

def OrbitParity : Prop :=
  ∀ (e : ℕ) (φ τ : GG e) (i : ℕ), φ.1.2 = 1 → InPhi τ → (InPhi (i • φ + τ) ↔ Even i)

def OrbitCoord : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)) (i : ℕ), (place (i • φ + ((0 : G0), t))).2 = t + i • φ.2

def OrbitOver : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)) (i : ℕ),
    (φ.1 = c0 → (place (i • φ + ((0 : G0), t))).1 = 0) ∧
    (φ.1 = sg + c0 → (place (i • φ + ((0 : G0), t))).1 = if Even i then 0 else sg)

def ConjInOrbit : Prop :=
  ∀ (e : ℕ) (φ : GG e), φ.1.2 = 1 → (cc e ∈ AddSubgroup.zmultiples φ ↔ φ = cc e)

def OrbitCard : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)), φ.1 = c0 → φ.2 ≠ 0 →
    (Set.range fun i : ℕ => place (i • φ + ((0 : G0), t))).ncard = addOrderOf φ.2 ∧
    Even (addOrderOf φ.2)

end Formalism.RankGapBounds.ExistsSmulMemTer
end

-- bundled from Formalism.RankGapBounds.LargePrimeFactor
section
open Real Finset

namespace Formalism.RankGapBounds.ChebyshevFactorialBounds

noncomputable section

def primesUpTo (X : ℕ) : Finset ℕ := (Finset.range (X + 1)).filter Nat.Prime

def leastRes (a : ℤ) (l : ℕ) : ℕ := sInf {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ a - (d : ℤ)}

structure Data (ι : Type) where

  T2 : Finset ι

  Nr : ℕ
  k : ℕ
  t : ℕ
  m : ℕ
  h : ℕ
  S : ℕ
  eta' : ℕ
  Wthin : ℕ
  D0 : ℕ
  lJ : ℝ
  Kexc : ℝ
  q : ι → ℕ
  j : ι → ℕ
  xlo : ι → ℤ
  xhi : ι → ℤ
  maxB : ι → ℤ
  Exc : Finset ℕ
  Bad : Finset ℕ
  J : ℕ → ℕ
  ex : ι → ℕ → ℕ
  ecl : ι → ℕ → ℕ
  erest : ι → ℕ → ℕ
  mw : ι → ℕ → ℕ
  mwF : ι → ℕ → ℕ

namespace Data

def kap {ι : Type} (D : Data ι) (l : ℕ) : ℕ := D.h / (l - 1)

def Icl {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : ℝ := by
  classical
  exact if ∃ y : ℤ, D.xlo τ ≤ y ∧ y ≤ D.xhi τ ∧ (l : ℤ) ∣ y - D.maxB τ then 1 else 0

def d0 {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : ℕ := leastRes (D.xlo τ - D.maxB τ) l

def depth {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : ℕ :=
  D.q τ * D.h + (l * D.mwF τ l + D.mw τ l) * (D.t + 2 * D.kap l)

def cW {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : ℝ :=
  ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * ((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1)
    + (D.ecl τ l : ℝ)
    + (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l)
    + min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ))
    + ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ)))

def ExcCost {ι : Type} (D : Data ι) : Prop :=
  ∀ l ∈ D.Exc, (D.J l : ℝ) * Real.log (l : ℝ) ≤ D.Kexc

def SumExactBound {ι : Type} [Fintype ι] (D : Data ι) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → D.J l ≤ ∑ τ, D.ex τ l

def ExactExpTotal {ι : Type} (D : Data ι) : Prop :=
  ∀ (τ : ι) (l : ℕ), l.Prime → l ∉ D.Exc →
    (D.ex τ l : ℝ) ≤ (D.Nr : ℝ) ^ 2 * Real.logb (l : ℝ) (2 * (D.h : ℝ) + (D.Nr : ℝ))

def ExactExpStop {ι : Type} (D : Data ι) : Prop :=
  ∀ (τ : ι) (l : ℕ), l.Prime → D.h + D.Nr < l → D.ex τ l = 0

def ThinStop {ι : Type} (D : Data ι) : Prop :=
  ∀ τ : ι, τ ∉ D.T2 → ∀ l : ℕ, l.Prime → D.Wthin < l → D.ex τ l = 0

def CloudRestCut {ι : Type} (D : Data ι) : Prop :=
  ∀ τ ∈ D.T2, ∀ l : ℕ, l.Prime → l ∉ D.Exc →
    (D.ex τ l : ℝ) ≤ (D.ecl τ l : ℝ) + (D.erest τ l : ℝ)
      + (D.k : ℝ) * ((D.Nr : ℝ) - (D.k : ℝ)) * (Nat.log l (2 * D.h + D.Nr) : ℝ)

def CloudBound {ι : Type} (D : Data ι) : Prop :=
  ∀ τ ∈ D.T2, ∀ l : ℕ, l.Prime → l ∉ D.Exc →
    D.ecl τ l ≤ D.k ^ 2 * Nat.log l (D.S + D.k) ∧ (D.S + D.k < l → D.ecl τ l = 0)

def RestBound {ι : Type} (D : Data ι) : Prop :=
  ∀ τ ∈ D.T2, ∀ l : ℕ, l.Prime → l ∉ D.Exc →
    (D.eta' + D.Nr < l → D.erest τ l = 0) ∧
    (D.erest τ l : ℝ) ≤ ((D.Nr : ℝ) - (D.k : ℝ)) ^ 2 * Real.logb (l : ℝ) (2 * (D.h : ℝ) + (D.Nr : ℝ))

def BlockIdealBound {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → D.h + D.Nr < l ^ 2 → D.Nr + 1 < l → D.t + 2 * D.kap l < l →
    (D.J l : ℝ) ≤ ∑ τ, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW τ l) else (D.ex τ l : ℝ))

def NoWindowResidue {ι : Type} (D : Data ι) : Prop :=
  ∀ l : ℕ, l.Prime → D.lJ < (l : ℝ) → l ∉ D.Bad → l ∉ D.Exc →
    ∀ τ : ι, D.mw τ l = 0 ∧ D.mwF τ l = 0

def Inputs {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) : Prop :=
  D.ExcCost ∧ D.SumExactBound ∧ D.ExactExpTotal ∧ D.ExactExpStop ∧ D.ThinStop ∧ D.CloudRestCut ∧
    D.CloudBound ∧ D.RestBound ∧ D.BlockIdealBound ∧ D.NoWindowResidue

def Params {ι : Type} (D : Data ι) : Prop :=
  1 ≤ D.h ∧ D.k ≤ D.Nr ∧ 2 ≤ D.h + D.Nr ∧ 1 ≤ D.D0 ∧ 1 < D.lJ ∧
    (D.Nr : ℝ) + 1 ≤ D.lJ ∧ (D.h : ℝ) + (D.Nr : ℝ) < D.lJ ^ 2 ∧ (D.S : ℝ) + (D.k : ℝ) ≤ D.lJ ∧
    (D.t : ℝ) + 2 * (D.h : ℝ) / (D.lJ - 1) ≤ D.lJ ∧
    ∀ τ ∈ D.T2, 0 ≤ D.maxB τ ∧ D.maxB τ + (D.D0 : ℤ) ≤ D.xlo τ ∧ D.xlo τ ≤ D.xhi τ ∧
      D.xhi τ - D.xlo τ ≤ (D.S : ℤ) ∧ D.xhi τ ≤ (D.h : ℤ) ∧ D.q τ + D.j τ ≤ D.m

def rhs {ι : Type} [Fintype ι] (D : Data ι) (C : ℝ) : ℝ :=
  (D.Exc.card : ℝ) * D.Kexc
  + ((D.Bad.card : ℝ) * (Fintype.card ι : ℝ) + ((Fintype.card ι : ℝ) - (D.T2.card : ℝ)) * (D.Wthin : ℝ))
      * (D.Nr : ℝ) ^ 2 * Real.log (2 * (D.h : ℝ) + (D.Nr : ℝ))
  + (D.T2.card : ℝ) *
    ( (D.k : ℝ) ^ 2 * ((D.S : ℝ) + (D.k : ℝ)) * Real.log ((D.S : ℝ) + (D.k : ℝ))
      + ((D.eta' : ℝ) + (D.Nr : ℝ)) * ((D.Nr : ℝ) - (D.k : ℝ)) ^ 2
          * Real.log (2 * (D.h : ℝ) + (D.Nr : ℝ))
      + D.lJ * (D.k : ℝ) * ((D.Nr : ℝ) - (D.k : ℝ)) * Real.log (2 * (D.h : ℝ) + (D.Nr : ℝ))
      + (D.k : ℝ) * ((D.S : ℝ) + 1) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
      + (D.k : ℝ) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
      + (D.m : ℝ) * (D.h : ℝ) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
          * (1 + Real.log ((D.h : ℝ) + (D.Nr : ℝ)))
      + C * ( (D.m : ℝ) * ((D.h : ℝ) + (D.Nr : ℝ)) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
          + (D.k : ℝ) * (D.S : ℝ) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
          + (D.m : ℝ) * (D.h : ℝ) * ((D.h : ℝ) + (D.Nr : ℝ)) / (D.D0 : ℝ)
          + (D.m : ℝ) * (D.h : ℝ) * (1 + Real.log (D.h : ℝ)) * Real.log ((D.h : ℝ) + (D.Nr : ℝ)) ) )

end Data

def Corollary : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι), D.Inputs → D.Params →
      ∀ X : ℕ, ∑ l ∈ primesUpTo X, (D.J l : ℝ) * Real.log (l : ℝ) ≤ D.rhs C

def ChebyshevTheta : Prop :=
  ∀ n : ℕ, ∑ p ∈ primesUpTo n, Real.log (p : ℝ) ≤ Real.log 4 * (n : ℝ)

def MertensType : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∑ p ∈ primesUpTo n, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ C * Real.log (n : ℝ)

def LargePrimeFactor : Prop :=
  ∀ (L : ℝ) (z : ℕ), 0 ≤ L → 1 ≤ z → (z : ℝ) < L ^ 2 →
    (z.primeFactors.filter (fun p : ℕ => L < (p : ℝ))).card ≤ 1

def HarmonicLog : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∑ d ∈ Finset.Icc 1 n, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log (n : ℝ)

def LeastResFacts : Prop :=
  ∀ (a : ℤ) (l : ℕ), 1 ≤ l →
    1 ≤ leastRes a l ∧ leastRes a l ≤ l ∧ (l : ℤ) ∣ a - (leastRes a l : ℤ) ∧
      (1 ≤ a → a < (l : ℤ) → (leastRes a l : ℤ) = a)

end

end Formalism.RankGapBounds.ChebyshevFactorialBounds
end

-- bundled from Formalism.RankGapBounds.MeanBoundSecondForm
section
open Real

namespace Formalism.RankGapBounds.WeightedMeanData

noncomputable section

def ph (y : ℝ) : ℝ := y * Real.log y - y

def wmean {ι : Type} [Fintype ι] (d X : ι → ℝ) : ℝ := (∑ i, d i * X i) / (∑ i, d i)

def umean {ι : Type} [Fintype ι] (X : ι → ℝ) : ℝ := (∑ i, X i) / (Fintype.card ι : ℝ)

structure Consts where

  cDiv : ℝ

  eDiv : ℝ

  cE : ℝ

  cH : ℝ

  cCount : ℝ

  cSlope : ℝ

  cSl1 : ℝ

  cLoss : ℝ

  eLoss : ℝ

  cHH : ℝ

structure Data (U0 : Type) (W : U0 → Type) (Top : Type) (m f : ℕ) where
  x : ℝ
  ε : ℝ
  a : ℝ
  b : ℝ
  b' : ℝ
  k : ℝ
  L : ℝ
  La : ℝ
  B0 : ℝ
  Nc : ℝ
  gam : ℝ
  LpL : ℝ
  v : ℝ
  lg : ℝ
  logGam : ℝ
  aT : Top → ℝ
  w : U0 → Fin m → Fin f → ℝ
  d : (u0 : U0) → W u0 → ℝ
  T : (u0 : U0) → W u0 → ℝ
  muN : (u0 : U0) → W u0 → ℝ
  muMaxN : (u0 : U0) → W u0 → ℝ
  h : (u0 : U0) → W u0 → ℝ
  muM : (u0 : U0) → W u0 → ℝ
  muMaxM : (u0 : U0) → W u0 → ℝ
  EeJ : (u0 : U0) → W u0 → Fin m → ℝ
  muCC : U0 → ℝ
  muMinCC : U0 → ℝ
  Fo : U0 → ℝ
  Ga : U0 → ℝ
  Ta : U0 → ℝ
  ASK : U0 → ℝ
  IO : U0 → ℝ
  HH : U0 → ℝ
  del : U0 → ℝ
  η : U0 → ℝ
  e : U0 → ℝ
  delBar : ℝ
  etaBar : ℝ
  eBar : ℝ

namespace Data

variable {U0 : Type} [Fintype U0] [Nonempty U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

def nT (_ : Data U0 W Top m f) : ℝ := (Fintype.card Top : ℝ)

def sumA : ℝ := ∑ t, D.aT t

def logOm : ℝ := D.gam + Real.log (π / D.v) - D.LpL

def Ee (u0 : U0) (u : W u0) : ℝ := ∑ j, D.EeJ u0 u j

def s (u0 : U0) : ℝ := wmean (D.d u0) (fun u => D.muN u0 u - D.h u0 u)

def uF (u0 : U0) : ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => D.muMaxN u0 u - D.h u0 u)) - D.s u0

def Tterm (u0 : U0) (u : W u0) : ℝ :=
  (4 * (f : ℝ) / D.T u0 u) *
    (|D.Ga u0| + D.Ta u0 + D.muMaxM u0 u - D.muM u0 u + 2 * (f : ℝ) * Real.log (D.T u0 u))

def Lo (u0 : U0) (u : W u0) : ℝ :=
  C.cSl1 * D.IO u0 + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * Real.log (D.T u0 u)
    + C.cSl1 * (m : ℝ) * D.B0 + D.Tterm u0 u

def LoP : ℝ := C.cLoss * D.nT * (m : ℝ) * D.b * D.x ^ (C.eLoss * D.ε)

def Main (u0 : U0) : ℝ :=
  ∑ j : Fin m, ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL
    - (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ))

def HidaSetting : Prop :=
  0 < D.x ∧ 0 < D.b ∧ 0 ≤ D.a ∧ 0 ≤ D.b' ∧ 0 < D.k ∧ 0 < D.v ∧ 0 < f ∧
  (∀ t, 0 ≤ D.aT t) ∧ (∀ u0 j ρ, 0 < D.w u0 j ρ) ∧
  (∀ u0 (u : W u0), 0 < D.d u0 u) ∧ (∀ u0 (u : W u0), 0 < D.T u0 u) ∧
  (∀ u0 (u : W u0), D.muN u0 u ≤ D.muMaxN u0 u) ∧
  0 ≤ C.cSl1 ∧ D.delBar < 1 ∧ 0 ≤ D.etaBar ∧ 0 ≤ D.eBar ∧ D.eBar ≤ 1 / 4

def DIV : Prop :=
  ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
    (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm) - D.aT t * Real.log (D.T u0 u)))
      + C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)

def EComp : Prop :=
  ∀ u0 (u : W u0) (j : Fin m), |D.EeJ u0 u j - D.sumA * D.lg| ≤ C.cE * D.B0

def HComp : Prop :=
  ∀ u0 (u u' : W u0),
    |(D.h u0 u + ∑ t, D.aT t * Real.log (D.T u0 u)) - (D.h u0 u' + ∑ t, D.aT t * Real.log (D.T u0 u'))|
      ≤ C.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0)

def Count : Prop :=
  ∀ u0 (u : W u0),
    ((∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
        - C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) - 2 * D.logGam / ((f : ℝ) * D.k)
        ≤ Real.log (D.T u0 u)) ∧
    Real.log (D.T u0 u) ≤ C.cCount * (m : ℝ) * D.L ∧
    ∀ u' : W u0, |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ C.cCount * Real.log D.k

def Slopes : Prop :=
  ∀ u0 (u : W u0), -(C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)) ≤ D.muM u0 u ∧
    D.muMaxM u0 u ≤ C.cSlope * D.nT * D.a * D.La

def SlopesN : Prop :=
  ∀ u0 (u : W u0),
    D.muMaxN u0 u ≤ D.muMaxM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u + C.cSl1 * (m : ℝ) * D.B0 ∧
    D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - D.Lo C u0 u ≤ D.muN u0 u

def Losses : Prop :=
  umean (fun u0 => D.ASK u0 - D.Ga u0) ≤ D.LoP C ∧ umean D.IO ≤ D.LoP C

def SlopeIneq : Prop :=
  ∀ u0, 0 ≤ D.del u0 → D.del u0 < 1 → 0 ≤ D.η u0 → 0 ≤ D.e u0 → D.e u0 ≤ 1 / 4 →
    D.s u0 - D.muMinCC u0 ≤ D.HH u0 → 0 < D.HH u0 →
    D.s u0 - Real.log (Fintype.card (W u0) : ℝ)
      - (1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
          + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) ≤ D.muCC u0

def HHBound : Prop :=
  ∀ u0, D.s u0 - D.muMinCC u0 ≤ D.HH u0 ∧ 0 < D.HH u0 ∧ D.HH u0 ≤ D.x ^ C.cHH * D.b

def FParams : Prop :=
  ∀ u0, 0 ≤ D.del u0 ∧ D.del u0 ≤ D.delBar ∧ 0 ≤ D.η u0 ∧ D.η u0 ≤ D.etaBar ∧
    0 ≤ D.e u0 ∧ D.e u0 ≤ D.eBar

def Vvar : ℝ :=
  2 * (m : ℝ) * C.cE * D.B0 + C.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0)
    + D.sumA * (C.cCount * Real.log D.k)

def MLo : ℝ :=
  C.cSl1 * D.LoP C + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L)
    + C.cSl1 * (m : ℝ) * D.B0 + umean (fun u0 => wmean (D.d u0) (D.Tterm u0))

def UBar : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0 + D.MLo C

def ErrX : ℝ :=
  D.sumA * (C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) + 2 * D.logGam / ((f : ℝ) * D.k))
    + (C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + D.MLo C
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (D.UBar C + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))

def MeanBoundSecondForm : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → D.EComp C → D.HComp C → D.Count C → D.Slopes C → D.SlopesN C →
    D.Losses C → D.SlopeIneq → D.HHBound C → D.FParams →
    umean D.ASK ≤ umean D.Main + D.ErrX C

def TaBound (cTa Xp Bo : ℝ) : Prop :=
  1 ≤ Xp ∧ 0 ≤ Bo ∧ ∀ u0, D.Ta u0 ≤ cTa * (m : ℝ) * D.nT * D.a * Real.log Xp + Bo

def TaB (cTa Xp Bo : ℝ) : ℝ := cTa * (m : ℝ) * D.nT * D.a * Real.log Xp + Bo

def TtermB (cTa Xp Bo : ℝ) (u0 : U0) (u : W u0) : ℝ :=
  (4 * (f : ℝ) / D.T u0 u) *
    (|D.Ga u0| + D.TaB cTa Xp Bo + D.muMaxM u0 u - D.muM u0 u + 2 * (f : ℝ) * Real.log (D.T u0 u))

def MLoB (cTa Xp Bo : ℝ) : ℝ :=
  C.cSl1 * D.LoP C + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L)
    + C.cSl1 * (m : ℝ) * D.B0 + umean (fun u0 => wmean (D.d u0) (D.TtermB cTa Xp Bo u0))

def UBarB (cTa Xp Bo : ℝ) : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0
    + D.MLoB C cTa Xp Bo

def ErrXB (cTa Xp Bo : ℝ) : ℝ :=
  D.sumA * (C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) + 2 * D.logGam / ((f : ℝ) * D.k))
    + (C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + D.MLoB C cTa Xp Bo
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (D.UBarB C cTa Xp Bo + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))

def MeanBoundOfTail (cTa Xp Bo : ℝ) : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → D.EComp C → D.HComp C → D.Count C → D.Slopes C →
    D.SlopesN C → D.Losses C → D.SlopeIneq → D.HHBound C → D.FParams → D.TaBound cTa Xp Bo →
    umean D.ASK ≤ umean D.Main + D.ErrXB C cTa Xp Bo

end Data

end

end Formalism.RankGapBounds.WeightedMeanData
end

