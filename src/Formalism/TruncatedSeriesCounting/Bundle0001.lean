import Mathlib
import Formalism.GaussValuationBounds.Statement
import Formalism.WindowSums.Statement
import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
import Formalism.FrobeniusContraction.Bundle0002

-- bundled from Formalism.TruncatedSeriesCounting.AprimeArith
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

def Mpar (ℓ g h : ℕ) : ℕ := (h + 2 * g) / (ℓ - 1) + 1

def sigE (ℓ g h j : ℕ) : ℕ :=
  ⌈((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1⌉₊

def a0E (ℓ g h j ell : ℕ) (rr : ℝ) : ℝ := 2 * (sigE ℓ g h j : ℝ) + rr + 2 * g * ell

def eE (ℓ g h j ell : ℕ) (rr kap : ℝ) : ℝ :=
  2 * rr + 4 * (sigE ℓ g h j : ℝ) + 2 * a0E ℓ g h j ell rr + 2 * kap

def MparGt : Prop :=
  ∀ ℓ g h : ℕ, 2 ≤ ℓ → h + 2 * g < (ℓ - 1) * Mpar ℓ g h

def SigELe : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ g h j : ℕ, 1 ≤ j →
    (sigE ℓ g h j : ℝ) ≤ 3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4

def EShape : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ (G g h j ell : ℕ) (C₀ rr kap : ℝ), 1 ≤ j → G ≤ g → 1 ≤ g → g ≤ h →
    1 ≤ ell → 0 ≤ C₀ →
    rr ≤ C₀ * ((G : ℝ) / ℓ + (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + Real.logb ℓ h + 1) →
    kap ≤ C₀ * ((g : ℝ) * ell + Real.logb ℓ h + 1) →
    eE ℓ g h j ell rr kap ≤
      (12 * C₀ + 50) * ((h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + (g : ℝ) * ell + Real.logb ℓ h)

def RrBound : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ (n : ℕ) [NeZero n] (H : ZMod n → ℕ) (G h j : ℕ) (cut : ZMod n) (s r : ℝ),
    1 ≤ h → (∀ x, H x ≤ 2 * h) → (∀ k : ℕ, 1 ≤ k → k ≤ j → H (cut + k) ≤ 2 * G) →
    s ≤ ∑' a : ℕ, ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ) +
        (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) + 3) / ((ℓ : ℝ) - 1) ^ a →
    r ≤ s * ℓ / ((ℓ : ℝ) - 1) ^ 2 + (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) →
    r ≤ 20 * ((G : ℝ) / ℓ + (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + Real.logb ℓ h + 1)

def ExponentBoundOfRankAndKappaBounds : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ (G g h j ell : ℕ) (rr kap : ℝ), 1 ≤ j → G ≤ g → 1 ≤ g → g ≤ h → 1 ≤ ell →
    rr ≤ 20 * ((G : ℝ) / ℓ + (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + Real.logb ℓ h + 1) →
    kap ≤ ell + 20 * g * (1 + ell) + 5 * (4 * g / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * h)) →
    eE ℓ g h j ell rr kap ≤
      800 * ((h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + (g : ℝ) * ell + Real.logb ℓ h)

def AprimeArith : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, 11 ≤ ℓ → ∀ (b w S η j ell b₀ b₁ : ℕ) (rr : ℝ),
    1 ≤ j → C * ((j : ℝ) + 1) * ((w + S + η : ℕ) + 1 : ℝ) ≤ b → ell ≤ 3 * j + 1 →
    b ≤ b₀ → b₀ ≤ b + η → b ≤ b₁ → b₁ ≤ b + η →
    rr ≤ 20 * (((w + S + η : ℕ) : ℝ) / ℓ + ((b + η + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) +
      Real.logb ℓ (b + η + S : ℕ) + 1) →
    max (w + S + η) 1 < b₀ ∧ max (w + S + η) 1 < b₁ ∧ (b₀ : ℝ) < ℓ * b₁ ∧ (b₀ : ℝ) ≤ ℓ * b₁ / 2 ∧
      a0E ℓ (max (w + S + η) 1) (b + η + S) j ell rr < (b₁ : ℝ) / 2

def DDSat : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (P : Ideal (PowerSeries O)) (a : ℕ) (x : O),
      PowerSeries.C x ∈ Ideal.span {PowerSeries.C (ϖ ^ a)} ⊔ P →
      ϖ ^ a ∣ x ∨ PowerSeries.C x ∈ P

end Formalism.TruncatedSeriesCounting.WachCoordinates
end
end

-- bundled from Formalism.TruncatedSeriesCounting.PowMemSpanOfMemSpanLinearDistinguished
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

open PowerSeries

def PowMemIdealPowXPowOfMemSpan : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) [Fact ℓ.Prime] (p₂ : PowerSeries O) (y B c : ℕ),
    p₂ ∈ Ideal.span {PowerSeries.C (ℓ : O), (PowerSeries.X : PowerSeries O) ^ (ℓ ^ 2)} →
    (c : ℝ) ≤ (y : ℝ) + 1 - (B : ℝ) / (ℓ : ℝ) ^ 2 →
    p₂ ^ y ∈ Formalism.WindowSums.IdLQ (O := O) ℓ c B

def PowMemSpanOfMemSpanLinearDistinguished : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) [Fact ℓ.Prime] (ε u p₂ : PowerSeries O) (w B η c : ℕ),
    p₂ ∈ Ideal.span {PowerSeries.C (ℓ : O), (Formalism.WindowSums.p1 ℓ ε u) ^ ℓ} →
    (c : ℝ) ≤ (w : ℝ) - (B : ℝ) / (ℓ : ℝ) - (η : ℝ) / (ℓ : ℝ) ^ 2 →
    p₂ ^ w ∈ Ideal.span {PowerSeries.C ((ℓ : O) ^ c),
      (Formalism.WindowSums.p1 ℓ ε u) ^ B * (PowerSeries.X : PowerSeries O) ^ η}

def BinomSplit : Prop :=
  ∀ (R : Type) [CommRing R] (x y : R) (a s : ℕ), 1 ≤ a + s →
    (x + y) ^ (a + s - 1) ∈ Ideal.span {x ^ a, y ^ s}

def LemmaGLag : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V]
    (T : Module.End ℤ_[ℓ] V) (c : ℤ → ℤ_[ℓ]),
    (∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧ PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j')) →
    ∀ (a S η b E : ℕ) (R₂ : Finset ℤ) (x : V),
      2 * a + η + 1 ≤ b →
      R₂ ⊆ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) →
      Polynomial.aeval T (∏ i ∈ Finset.range a,
        (Polynomial.X - Polynomial.C (c ((b : ℤ) - (i : ℤ))))) x = 0 →
      Polynomial.aeval T (∏ j ∈ R₂, (Polynomial.X - Polynomial.C (c j))) x = 0 →
      ((3 * a + S + 2 * η : ℕ) : ℝ) / ((ℓ : ℝ) - 1) +
          2 * Real.logb ℓ ((b + S + a + η : ℕ) : ℝ) ≤ E →
      ((ℓ : ℤ_[ℓ]) ^ E) • x = 0

def KapWin : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (χ : ℤ_[ℓ]ˣ), PadicInt.valuation ((χ : ℤ_[ℓ]) - 1) = 1 →
    ∀ (ell K D : ℕ) (a : Fin K → ℤ) (L : Fin K → ℕ) (JJ : Finset ℤ),
      JJ ⊆ Finset.univ.biUnion (fun k => Finset.Ico (a k) (a k + (L k : ℤ))) →
      (∀ i ∈ JJ, |i| ≤ (D : ℤ)) →
      (Formalism.WindowSums.PP ℓ χ ell JJ).eval 1 ≠ 0 ∧
      (PadicInt.valuation ((Formalism.WindowSums.PP ℓ χ ell JJ).eval 1) : ℝ) ≤
        (ell : ℝ) + ((∑ k, L k : ℕ) : ℝ) * (1 + ell) +
          ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D)

def ColTwoStep : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g g₀ e e' : ℕ)
    (Z I : Submodule O M) (s s₀ : Finset M),
    I ≤ Z → s.card ≤ g → s₀.card ≤ g₀ → (↑s₀ : Set M) ⊆ Z →
    Submodule.span O (s : Set M) ⊔ I = Z →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (ℓ ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g * e + g₀ * e' : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

def sigT (ℓ E M j : ℕ) : ℕ :=
  ⌈((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌉₊ + 1

def SigA : Prop :=
  ∀ (ℓ : ℕ), 11 ≤ ℓ → ∀ (G h j : ℕ), 1 ≤ j →
    (2 * sigT ℓ (2 * G) (2 * h / (ℓ - 1) + 1) j : ℝ) ≤ 0.05 * h + 0.5 * G + 5

def SigB : Prop :=
  ∀ (ℓ : ℕ), 11 ≤ ℓ → ∀ (w S h : ℕ),
    (sigT ℓ (2 * (w + S)) (2 * h / (ℓ - 1) + 1) 1 : ℝ) ≤
      3 * ((w : ℝ) + S) / ℓ + 3 * (h : ℝ) / (ℓ : ℝ) ^ 2 + 3

def CorAWordUD : Prop :=
  ∀ (ℓ j j' w S η b bU A : ℕ), 11 ≤ ℓ → 1 ≤ j → j' ≤ 3 * j + 1 →
    10 * (j + 1) * (w + S + η + 1) ≤ b → b ≤ bU →
    (A : ℝ) ≤ (((b + η + S : ℕ) : ℝ) + (η : ℝ)) / ((ℓ : ℝ) - 1) + 1 →
    A + η + 2 * sigT ℓ (2 * (w + S + η)) (2 * (b + η + S) / (ℓ - 1) + 1) j +
      2 * j' * (w + S + η) + 1 ≤ bU

def CorAWordDU : Prop :=
  ∀ (ℓ s g b bU bD η S : ℕ), 2 ≤ ℓ → s < g → bU ≤ b + η → η < b → b ≤ bD →
    bU * ℓ ^ s < (bD + S) * ℓ ^ g

def Clusters {n : ℕ} (j : ℕ) (thick : ZMod n → Prop) : Prop :=
  ∀ t, thick t →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (t - k)) ∨
    (∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ thick (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ thick (t - k))

def CutsExist : Prop :=
  ∀ (n j : ℕ) [NeZero n] (thick : ZMod n → Prop) [DecidablePred thick],
    1 ≤ j → j + 1 ≤ n → Clusters j thick →
    ∃ (m : ℕ) (c : ℕ → ℤ), 1 ≤ m ∧ c m = c 0 + n ∧
      ∀ k < m,
        (∀ i : ℕ, 1 ≤ i → i ≤ j → ¬ thick ((c k + i : ℤ) : ZMod n)) ∧
        (j : ℤ) ≤ c (k + 1) - c k ∧ c (k + 1) - c k ≤ 3 * j + 1 ∧
        ((Finset.Ioc (c k) (c (k + 1))).filter (fun i : ℤ => thick (i : ZMod n))).card ≤ 2

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
end
end

-- bundled from Formalism.TruncatedSeriesCounting.StatementX
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.X

open PowerSeries

def QaNum : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (H' H : ℕ) (eW : ℝ), H' ≤ H →
    eW ≤ (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 3 + Real.logb ℓ ((H' : ℝ) + 1) →
    (((H' / (ℓ - 1) + 1 : ℕ)) : ℝ) + eW - 1 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H

def TruncSig : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (y X M η : ℕ),
    (y : ℝ) * ℓ / ((ℓ : ℝ) - 1) - max 0 ((ℓ : ℝ) * y - X) ≤ ((X : ℝ) + 1) / ((ℓ : ℝ) - 1) + 1 ∧
    (y : ℝ) * ℓ / ((ℓ : ℝ) - 1) - max 0 ((ℓ : ℝ) * y - η - M) ≤
      ((M : ℝ) + η) / ((ℓ : ℝ) - 1) + 1 ∧
    (y : ℝ) * ℓ / ((ℓ : ℝ) - 1) - max 0 (((ℓ : ℝ) - 1) * y - (X : ℝ) / ℓ) ≤
      (X : ℝ) / ((ℓ : ℝ) - 1) ^ 2 + 1

def TruncRem1 : Prop :=
  ∀ (R : Type) [CommRing R] (ℓ : ℕ), 1 ≤ ℓ → ∀ (π₀ : R) (y K c : ℕ),
    (c : ℤ) ≤ (ℓ : ℤ) * y - K →
    (π₀ * (π₀ + (ℓ : R)) ^ (ℓ - 1)) ^ y ∈
      Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K}

def ArcExp : Prop :=
  ∀ (r σ κ G : ℝ) (j' ell : ℕ), 0 ≤ r → 0 ≤ σ → 0 ≤ κ → 0 ≤ G → j' ≤ ell →
    r + 4 * σ + κ + max (r + κ) (2 * σ + 2 * j' * G + 1) ≤
      2 * r + 6 * σ + 2 * κ + 2 * G * ell + 1

def SatA : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (ℓ f f' : A), f' ≠ 0 →
    (∀ a : A, ℓ * a ∈ Ideal.span {f} → a ∈ Ideal.span {f}) →
    (∀ a : A, ℓ * a ∈ Ideal.span {f'} → a ∈ Ideal.span {f'}) →
    ∀ (x : FractionRing A) (k : ℕ),
      (∃ b : A, algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) f' * x) →
      (∃ a : A, algebraMap A (FractionRing A) (f * a) = algebraMap A (FractionRing A) ℓ ^ k * x) →
      ∃ a : A, x = algebraMap A (FractionRing A) (f * a)

def UnitCoefficientPowerMod : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) (ε u : PowerSeries O) (y : ℕ),
    (PowerSeries.coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y) - (PowerSeries.constantCoeff u) ^ y ∈
      Ideal.span {(ℓ : O)}) ∧
    (IsLocalRing O → ¬ IsUnit (ℓ : O) → IsUnit u →
      IsUnit (PowerSeries.coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y)))

end Formalism.TruncatedSeriesCounting.X
end
end

-- bundled from Formalism.TruncatedSeriesCounting.WindowSeparated
section
noncomputable section

open Classical

namespace Formalism.TruncatedSeriesCounting.tableLineDegreeTwo

open Formalism.WachCohomologyFacts

def LowN (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (V2.InWinN G h η)

def WindowSmall (ℓ η : ℕ) (σ : ℤ) : Prop := (η : ℤ) + 4 * σ + 6 < ℓ

def WindowSeparated (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ LowN G h η U, ∀ y ∈ Top.GlobalTheory w t, σ + 2 < |x - y|

def Slot (ℓ : ℕ) (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  0 ≤ σ ∧ 1 ≤ t ∧ (∀ x ∈ U, 1 ≤ x ∧ x ≤ (h : ℤ) - 1) ∧ w + t ≤ h ∧
    1 ≤ w ∧ (G = true → w + t - 1 ≤ η) ∧ (G = false → (h : ℤ) - η ≤ w) ∧
    WindowSmall ℓ η σ ∧ WindowSeparated G h η w t σ U ∧ V2.ResidueAvoidance ℓ G h η σ U

def Residues : Prop :=
  ∀ (ℓ : ℕ) (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), Slot ℓ G h η w t σ U →
    (∀ x ∈ U, ∀ e : ℤ, -σ - 1 ≤ e → e ≤ (t : ℤ) + σ →
      ((x : ℤ) : ZMod ℓ) ≠ (((w : ℤ) + e : ℤ) : ZMod ℓ)) ∧
    (G = false → ∀ u : ℤ, (u ∈ U ∨ u ∈ Top.GlobalTheory w t) → ∀ a : ℤ, 0 ≤ a → a ≤ (h : ℤ) - w →
      ((u - w - a : ℤ) : ZMod ℓ) = 0 → u - w - a = 0) ∧
    (G = true → ∀ x ∈ U, ∀ e : ℤ, 1 ≤ e → e ≤ σ → ((x + e : ℤ) : ZMod ℓ) ≠ 0) ∧
    (G = false → ∀ u : ℤ, (u ∈ U ∨ u ∈ Top.GlobalTheory w t) → ∀ e : ℤ, 1 ≤ e → e ≤ σ + 1 →
      ((u : ℤ) : ZMod ℓ) ≠ (((h : ℤ) + e : ℤ) : ZMod ℓ))

def resCount (ℓ : ℕ) (U : Multiset ℤ) (x : ZMod ℓ) : ℕ := U.countP (fun u => ((u : ℤ) : ZMod ℓ) = x)

def CountG : Prop :=
  ∀ (ℓ : ℕ) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), Slot ℓ true h η w t σ U →
    ∀ (S m : ZMod ℓ → ℕ),
      (∀ x, S x + m (x + 1) = resCount ℓ U x + m x) →
      (∀ x, m x ≠ 0 → ∃ u ∈ U, ∃ e : ℤ, 1 ≤ e ∧ e ≤ σ ∧ x = ((u + e : ℤ) : ZMod ℓ)) →
      ∑ n ∈ Finset.range w, S (n : ZMod ℓ) = U.countP (fun u => u < (w : ℤ))

def CountBd : Prop :=
  ∀ (ℓ : ℕ) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), Slot ℓ false h η w t σ U →
    ∀ (S m : ZMod ℓ → ℕ),
      (∀ x, S x + m (x + 1) = resCount ℓ U x + m x) →
      (∀ x, m x ≠ 0 → ∃ u ∈ U, ∃ e : ℤ, 1 ≤ e ∧ e ≤ σ ∧ x = ((u + e : ℤ) : ZMod ℓ)) →
      (∀ x, S x ≠ 0 → ∃ u : ℤ, (u ∈ U ∨ u ∈ Top.GlobalTheory w t) ∧ x = ((u : ℤ) : ZMod ℓ)) →
      ∑ n ∈ Finset.Icc (w : ℤ) (h : ℤ), S ((n : ℤ) : ZMod ℓ) =
        Multiset.card U - U.countP (fun u => u < (w : ℤ))

def KerCount : Prop :=
  ∀ (ℓ w : ℕ) (S : Multiset (ZMod ℓ)), 1 ≤ w → w < ℓ →
    Multiset.card ((S ×ˢ (Finset.Icc 1 w).val).filter
        (fun p : ZMod ℓ × ℕ => p.1 - (w : ZMod ℓ) + (p.2 : ZMod ℓ) = 0)) =
      S.countP (fun s => ∃ n < w, s = (n : ZMod ℓ))

def KerGr : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V →ₗ[k] V) (m : ℕ) (F : ℕ → Submodule k V),
    F 0 = ⊥ → F m = ⊤ → (∀ i, F i ≤ F (i + 1)) → (∀ i, ∀ x ∈ F i, f x ∈ F i) →
    Module.finrank k (LinearMap.ker f) ≤
      ∑ i ∈ Finset.range m,
        (Module.finrank k ↥(F (i + 1) ⊓ (F i).comap f) - Module.finrank k ↥(F i))

def KerEig : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (g : V →ₗ[k] V),
    Module.finrank k (LinearMap.ker g) ≤ (LinearMap.charpoly g).rootMultiplicity 0

def Close : Prop :=
  (∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (KK L N : Submodule k V) (r d : ℕ),
      L ≤ KK ⊓ N → Module.finrank k KK - Module.finrank k L ≤ r →
      Module.finrank k ↥(KK ⊓ N) - Module.finrank k L = r - d → d ≤ r →
      Module.finrank k KK - Module.finrank k ↥(KK ⊓ N) ≤ d) ∧
  (∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (Hf adm : Submodule k V), Hf ≤ adm → Module.finrank k adm ≤ Module.finrank k Hf →
      adm = Hf)

def DepthSteps : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h w : ZMod f → ℕ), 2 ≤ ℓ → ∀ i : ZMod f,
    V2.sgN f ℓ h i + 2 * ℓ < (ℓ : ℤ) * (V2.sgN f ℓ h (i - 1) + 3) - h i ∧
    (w i ≤ h i → ((h i : ℤ) - w i) + 2 < (ℓ : ℤ) * (V2.sgN f ℓ h (i - 1) + 3) - w i) ∧
    ∀ s : ℕ, V2.sgN f ℓ h i + 1 + ℓ * s ≤ (ℓ : ℤ) * (V2.sgN f ℓ h (i - 1) + 1 + s) - h i

def PsiPow : Prop :=
  ∀ (k : Type) [Field k] (ℓ : ℕ) [CharP k ℓ] (hℓ : ℓ.Prime)
    (ψ : PowerSeries k →+ PowerSeries k),
    (∀ a x : PowerSeries k, ψ (PowerSeries.expand ℓ hℓ.ne_zero a * x) = a * ψ x) →
    (∀ j < ℓ, ψ ((1 + PowerSeries.X) ^ j) = if j = 0 then 1 else 0) →
    (∀ j < ℓ, ψ (PowerSeries.X ^ j) = (-1) ^ j) ∧
    ∀ s : ℕ, ψ '' {x | PowerSeries.X ^ s ∣ x} = {y | PowerSeries.X ^ (s / ℓ) ∣ y}

def PsiExists : Prop :=
  ∀ (k : Type) [Field k] (ℓ : ℕ) [CharP k ℓ] (hℓ : ℓ.Prime),
    ∃ ψ : PowerSeries k →+ PowerSeries k,
      (∀ a x : PowerSeries k, ψ (PowerSeries.expand ℓ hℓ.ne_zero a * x) = a * ψ x) ∧
      (∀ j < ℓ, ψ ((1 + PowerSeries.X) ^ j) = if j = 0 then 1 else 0)

end Formalism.TruncatedSeriesCounting.tableLineDegreeTwo
end
end

