import Mathlib
import Formalism.PieriBlockIdeals.Bundle0001
import Formalism.RankGapBounds.Bundle0001

-- bundled from Formalism.PieriBlockIdeals.ContentDistanceBounds
section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

def MinStep : Prop :=
  ∀ (R : Type) [CommRing R] (Q : Type) [AddCommGroup Q] [Module R Q] (l : R) (a b : ℕ),
    (∀ q : Q, l ^ a • q = 0) → (∀ q : Q, l ^ b • q = 0) → ∀ q : Q, l ^ (min a b) • q = 0

def ExactStep : Prop :=
  ∀ (R : Type) [CommRing R] (A B Q : Type) [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup Q] [Module R Q] (f : A →ₗ[R] B) (g : B →ₗ[R] Q) (l : R) (c : ℕ),
    Function.Exact f g → (∀ q : Q, l ^ c • q = 0) → ∀ y : B, l ^ c • y ∈ LinearMap.range f

def ContentDistanceBounds : Prop :=
  ∀ (r w H : ℕ) (lam tau : ℕ → ℕ), Antitone lam → Antitone tau → (∀ a, lam a ≤ tau a) →
    lam 0 ≤ w → w ≤ H → 0 < r → (∀ a < r, ¬ (lam a ≤ a + w ∧ a + w < tau a)) →
    ∀ a < r, ∀ col : ℕ, lam a ≤ col → col < tau a →
      1 ≤ (w : ℤ) - ((col : ℤ) - (a : ℤ)) ∧ (w : ℤ) - ((col : ℤ) - (a : ℤ)) ≤ (H : ℤ) + r - 1

def Markov : Prop :=
  ∀ (k i d : ℕ) (n : Fin k → ℕ), ∑ R, n R ≤ i → 1 ≤ d →
    ((Finset.univ.filter (fun R => d ≤ n R)).card) * d ≤ i

def NoResidue : Prop :=
  ∀ (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ),
    (∀ u ∈ U, u ∉ Finset.Icc b (b + t - 1) → ∀ x ∈ Finset.Icc (b - κ) (b + t - 1 + κ),
      (0 < |u - x| ∧ |u - x| < (l : ℤ)) ∨ ¬ ((l : ℤ) ∣ u - x)) →
    mwCount l b t κ U = 0

def PrimeCount : Prop :=
  ∀ (L : ℝ) (T : Finset ℤ) (P : Finset ℕ), 0 ≤ L → (∀ n ∈ T, n ≠ 0 ∧ ((|n| : ℤ) : ℝ) < L ^ 2) →
    (∀ l ∈ P, l.Prime ∧ L < (l : ℝ) ∧ ∃ n ∈ T, (l : ℤ) ∣ n) → P.card ≤ T.card

def ISum : Prop :=
  ∀ (h : ℕ) (L : ℝ) (xm xp mB : ℤ) (P : Finset ℕ), 0 ≤ L → (h : ℝ) < L ^ 2 → 0 ≤ mB → mB < xm →
    xm ≤ xp → xp ≤ (h : ℤ) → (∀ l ∈ P, l.Prime ∧ L < (l : ℝ)) →
    ∑ l ∈ P, IlInd l xm xp mB * Real.log (l : ℝ) ≤ (((xp - xm : ℤ) : ℝ) + 1) * Real.log (h : ℝ)

def GatedCap : Prop :=
  ∀ (D h : ℕ) (L A k : ℝ) (P : Finset ℕ), 1 ≤ D → D ≤ h → 0 ≤ A → 0 ≤ k → (h : ℝ) < L ^ 2 →
    1 ≤ L → (∀ l ∈ P, l.Prime ∧ L < (l : ℝ)) →
    ∑ l ∈ P, (if ((d0 l D : ℕ) : ℤ) < (D : ℤ) then min k (A / (d0 l D : ℝ)) else 0) *
        Real.log (l : ℝ) ≤
      Real.log (h : ℝ) * ∑ d ∈ Finset.Icc 1 h, min k (A / (d : ℝ))

def SL2CommutationRelation : Prop :=
  ∀ (A : Type) [Ring A] (h e f : A), h * e - e * h = 2 * e → h * f - f * h = -(2 * f) →
    e * f - f * e = h →
    ∀ i : ℕ, e * f ^ (i + 1) - f ^ (i + 1) * e = ((i : A) + 1) * (f ^ i * (h - (i : A)))

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.ParamsWindow
section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

def lamOf (N : ℕ) (U : ℕ → ℤ) (i : ℕ) : ℤ := U i - ((N : ℤ) - 1 - (i : ℤ))

def CrossTerm : Prop :=
  ∀ (l N h a : ℕ) (U : ℕ → ℤ), l.Prime → (∀ i j, i < j → j < N → U j < U i) →
    (∀ i < N, 0 ≤ U i ∧ U i ≤ (h : ℤ)) → a ≤ N →
    ∑ i ∈ Finset.range a, ∑ j ∈ Finset.Ico a N,
      (Nat.log l (((j : ℤ) - (i : ℤ) + lamOf N U 0 - lamOf N U (N - 1)).toNat) -
        padicValInt l (lamOf N U i - lamOf N U j + (j : ℤ) - (i : ℤ))) ≤
      a * (N - a) * Nat.log l (2 * h + N)

def ExpStopH : Prop :=
  ∀ (l N h : ℕ) (U : Fin N → ℤ), l.Prime → StrictAnti U → (∀ i, 0 ≤ U i ∧ U i ≤ (h : ℤ)) →
    h < l → Formalism.RankGapBounds.JumpSetsAlt.eExp U l = 0

def ParamsWindow : Prop :=
  ∀ (b h l t : ℕ) (lstar h0 η : ℝ), 1 ≤ lstar → (h : ℝ) ≤ 2 * b → lstar < (l : ℝ) →
    12 * b / lstar + 2 * t + 8 ≤ h0 → 2 * η + t + 8 * b / lstar + 7 < lstar → 0 ≤ η →
    ((h / (l - 1) : ℕ) : ℝ) ≤ h0 / 4 - t / 2 - 2 ∧ η + t + ((h / (l - 1) : ℕ) : ℝ) < l ∧
      0 < h0 / 2 - 1 - t / 2 - ((h / (l - 1) : ℕ) : ℝ)

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.StatementC
section
open Real Finset

namespace Formalism.CohomologicalDescent.Cor

open Formalism.RankGapBounds.ChebyshevFactorialBounds

noncomputable section

def DB {ι : Type} (D : Data ι) (τ : ι) : ℤ := D.xlo τ - D.maxB τ

def coefficientBoundTau {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : ℝ :=
  ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) + 6)
    + (D.ecl τ l : ℝ)
    + (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l)
    + (if ((D.d0 τ l : ℕ) : ℤ) < DB D τ then
        min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ)) else 0)
    + ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ)))

def BlockIdealBound5 {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → D.lJ < (l : ℝ) → D.h + D.Nr < l ^ 2 → D.Nr + 1 < l →
    D.t + 2 * D.kap l < l →
    (D.J l : ℝ) ≤ ∑ τ, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (coefficientBoundTau D τ l) else (D.ex τ l : ℝ))

def ExactExpStop5 {ι : Type} (D : Data ι) : Prop :=
  ∀ (τ : ι) (l : ℕ), l.Prime → l ∉ D.Exc → D.h + D.Nr < l → D.ex τ l = 0

def ThinStop5 {ι : Type} (D : Data ι) : Prop :=
  ∀ τ : ι, τ ∉ D.T2 → ∀ l : ℕ, l.Prime → l ∉ D.Exc → D.Wthin < l → D.ex τ l = 0

def Inputs5 {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) : Prop :=
  D.ExcCost ∧ D.SumExactBound ∧ D.ExactExpTotal ∧ ExactExpStop5 D ∧ ThinStop5 D ∧ D.CloudRestCut ∧
    D.CloudBound ∧ D.RestBound ∧ BlockIdealBound5 D ∧ D.NoWindowResidue

def rhs5 {ι : Type} [Fintype ι] (D : Data ι) (C : ℝ) : ℝ :=
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
          + (D.m : ℝ) * (D.h : ℝ) * (1 + Real.log (D.h : ℝ)) * Real.log ((D.h : ℝ) + (D.Nr : ℝ)) ) )

def Corollary5 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι), Inputs5 D → D.Params →
      ∀ X : ℕ, ∑ l ∈ primesUpTo X, (D.J l : ℝ) * Real.log (l : ℝ) ≤ rhs5 D C

end

end Formalism.CohomologicalDescent.Cor
end

-- bundled from Formalism.PieriBlockIdeals.WEChain
section
noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

def WEChain : Prop :=
  ∀ (k j t q l h κ : ℕ) (K : Type) [Field K] [CharP K l]
    (U U' V V' : Fin (k + j + t + q) → ℤ) (b b' c c' : ℤ) (kc kp : Fin t → ℤ),
    l.Prime → t + 2 * κ < l →
    StrictAnti U → StrictAnti U' → StrictAnti V → StrictAnti V' →
    (∀ a, 0 ≤ U a) → (∀ a, U' a ≤ (h : ℤ)) → ∑ a, U a = ∑ a, U' a →
    (∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U a = b + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) →
    (∀ s : Fin t, ∃ a, V a = b' + ((s : ℕ) : ℤ)) →
    (∏ a, (X + C (((U a + c : ℤ)) : K))) = ∏ a, (X + C (((U' a + c : ℤ)) : K)) →
    (∏ a, (X + C (((V a + c' : ℤ)) : K))) = ∏ a, (X + C (((V' a + c' : ℤ)) : K)) →
    (∀ s, |kc s| ≤ (κ : ℤ)) → (∀ s, |kp s| ≤ (κ : ℤ)) →
    Multiset.map (fun s : Fin t => ((b + ((s : ℕ) : ℤ) - kc s : ℤ) : ZMod l)) Finset.univ.val ≤
      Multiset.map (fun a => ((U' a : ℤ) : ZMod l)) Finset.univ.val →
    Multiset.map (fun s : Fin t => ((b' + ((s : ℕ) : ℤ) - kp s : ℤ) : ZMod l)) Finset.univ.val ≤
      Multiset.map (fun a => ((V' a : ℤ) : ZMod l)) Finset.univ.val →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ) + (l : ℤ) * kp s - kc s) →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U a - U' a) ≤
      (q : ℤ) * h +
        ((l : ℤ) * (mwCount l b' t κ (Finset.univ.image V) : ℤ) +
          (mwCount l b t κ (Finset.univ.image U) : ℤ)) * ((t : ℤ) + 2 * κ)

end Formalism.CohomologicalDescent
end
end

