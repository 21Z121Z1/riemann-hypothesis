import Mathlib
import Formalism.PairingDivisors.StatementH

-- bundled from Formalism.PairingDivisors.StatementA
section
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

noncomputable section

namespace Formalism.PairingDivisionLocalBalance

def ValAdd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (a b : K),
    a ≠ 0 → b ≠ 0 → a + b ≠ 0 → min (vw w a) (vw w b) ≤ vw w (a + b)

def CharSumVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (ι : Type) [Fintype ι]
    (a ζ : ι → K) (N : ℝ),
    (∀ i, ∃ n : ℕ, 0 < n ∧ ζ i ^ n = 1) →
    (∀ i, a i = 0 ∨ -N ≤ (vw w (a i) : ℝ)) →
    (∑ i, a i * ζ i = 0 ∨ -N ≤ (vw w (∑ i, a i * ζ i) : ℝ))

def eq {k : Type} [Field k] (q : ℕ) (s : ℕ) (Y : k) : k :=
  (1 - Y * ((q : k) ^ s)⁻¹) * (1 - Y⁻¹ * ((q : k) ^ s)⁻¹) + ((q : k) - 1) * (((q : k) ^ s)⁻¹) ^ 2

def EqLocal : Prop :=
  ∀ (q s : ℕ) (Y : ℂ), 2 ≤ q → 1 ≤ s → ‖Y‖ = 1 →
    Summable (fun p : ℕ × ℕ =>
      (Y * ((q : ℂ) ^ s)⁻¹) ^ (p.1 + 1) * (Y⁻¹ * ((q : ℂ) ^ s)⁻¹) ^ (p.2 + 1)) ∧
    1 + ((q : ℂ) - 1) * ∑' p : ℕ × ℕ,
      (Y * ((q : ℂ) ^ s)⁻¹) ^ (p.1 + 1) * (Y⁻¹ * ((q : ℂ) ^ s)⁻¹) ^ (p.2 + 1) =
      eq q s Y * ((1 - Y * ((q : ℂ) ^ s)⁻¹)⁻¹ * (1 - Y⁻¹ * ((q : ℂ) ^ s)⁻¹)⁻¹)

def EqSymm : Prop :=
  ∀ (k : Type) [Field k] (q s : ℕ) (Y : k), Y ≠ 0 →
    eq q s Y = eq q s Y⁻¹ ∧
    eq q s Y = 1 - (Y + Y⁻¹) * ((q : k) ^ s)⁻¹ + (q : k) * (((q : k) ^ s)⁻¹) ^ 2

def EqIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (q s : ℕ) (Y : K),
    1 ≤ q → Y ≠ 0 → vw w (q : K) = 0 → vw w Y = 0 →
    (eq q s Y = 0 ∨ 0 ≤ vw w (eq q s Y))

def RemoveQ : Prop :=
  ∀ (k : Type) [Field k] (P : Type) [DecidableEq P] (Q : Finset P) (unr : P → Prop) [DecidablePred unr]
    (val : Finset P → k) (c Lval : k) (e : P → k) (q1 : P),
    (∀ Q' ⊆ Q, val Q' = c * Lval * ∏ q ∈ Q'.filter unr, e q) → q1 ∈ Q → unr q1 →
    val Q = e q1 * val (Q.erase q1)

def UpperStays : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (P : Type) (R : Finset P)
    (y y' : K) (e : P → K) (B : ℝ),
    y ≠ 0 → y = y' * ∏ q ∈ R, e q → (∀ q ∈ R, 0 ≤ vw w (e q)) → (vw w y : ℝ) ≤ B →
    (vw w y' : ℝ) ≤ B

def GaussUnit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (G G' : 𝓞 K) (q : ℕ),
    1 ≤ q → (G : K) * (G' : K) = (q : K) → vw w (q : K) = 0 → vw w (G : K) = 0

def RatioVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (a a' : K) (g : ℤ),
    a ≠ 0 → a' ≠ 0 → vw w (a / a') = (vw w a + g) - (vw w a' + g)

end Formalism.PairingDivisionLocalBalance
end
end

-- bundled from Formalism.PairingDivisors.StatementX
section
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

noncomputable section

namespace Formalism.PairingDivisionLocalBalance

def HtLe {K : Type} [Field K] [NumberField K] [StarRing K] (g : Pl K → ℤ) (z : K) (B : ℝ) : Prop :=
  (Function.support fun w : Pl K => lw w * |((vw w z + g w : ℤ) : ℝ)|).Finite ∧
  ∑ᶠ w : Pl K, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ B

def cmFactor {K : Type} [Field K] {I : Type} [Fintype I] (al : I → Bool) (x u y : I → K) : K :=
  ∏ i, (if al i then u i * y i / x i else (u i * y i / x i)⁻¹)

def CMFactorBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (I : Type) [Fintype I] (al : I → Bool) (T : Finset (Pl K)) (g : I → Pl K → ℤ)
    (x x1 x2 : I → K) (y u : Pl K → I → K) (ch : Pl K → Bool)
    (S Se : Finset ℕ) (N0 : I → ℕ → ℝ) (ep : ℕ → ℝ) (B : I → ℝ),
    (∀ i, x i ≠ 0 ∧ x1 i ≠ 0 ∧ x2 i ≠ 0) → (∀ w i, y w i ≠ 0 ∧ u w i ≠ 0) →

    (∀ i, HtLe (g i) (x i) (B i) ∧ HtLe (g i) (x1 i) (B i) ∧ HtLe (g i) (x2 i) (B i)) →

    (∀ i, ∀ l ∈ S, 0 ≤ N0 i l) → (∀ l ∈ Se, 0 ≤ ep l) →

    (∀ w ∈ T, ∀ i, vw w (u w i) = 0) →

    (∀ w ∈ T, ∀ i, - wt S (N0 i) w ≤ ((vw w (y w i) + g i w : ℤ) : ℝ) ∧
      ((vw w (y w i) + g i w : ℤ) : ℝ) ≤
        ((vw w (if ch w then x1 i else x2 i) + g i w : ℤ) : ℝ) + wt Se ep w) →
    (∀ w ∈ T, (vw w (cmFactor al x (u w) (y w)) : ℝ) ≤
      ∑ i, (|((vw w (x i) + g i w : ℤ) : ℝ)| + |((vw w (x1 i) + g i w : ℤ) : ℝ)|
          + |((vw w (x2 i) + g i w : ℤ) : ℝ)|)
        + ∑ i, (wt S (N0 i) w + wt Se ep w)) ∧
    ∑ w ∈ T, lw w * (vw w (cmFactor al x (u w) (y w)) : ℝ) ≤
      ∑ i, (3 * B i + ∑ l ∈ S, N0 i l * Real.log l)
        + (Fintype.card I : ℝ) * ∑ l ∈ Se, ep l * Real.log l

def Export : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (I : Type) [Fintype I] (al : I → Bool) (T : Finset (Pl K)) (g : I → Pl K → ℤ)
    (x x1 x2 : I → K) (y u : Pl K → I → K) (ch : Pl K → Bool)
    (S Se : Finset ℕ) (N0 : I → ℕ → ℝ) (B : I → ℝ) (nI f b L xx CB CN : ℝ),
    (∀ i, x i ≠ 0 ∧ x1 i ≠ 0 ∧ x2 i ≠ 0) → (∀ w i, y w i ≠ 0 ∧ u w i ≠ 0) →
    (∀ i, HtLe (g i) (x i) (B i) ∧ HtLe (g i) (x1 i) (B i) ∧ HtLe (g i) (x2 i) (B i)) →
    (∀ i, ∀ l ∈ S, 0 ≤ N0 i l) → (∀ l ∈ Se, l.Prime) →
    (∀ w ∈ T, ∀ i, vw w (u w i) = 0) →
    (∀ w ∈ T, ∀ i, - wt S (N0 i) w ≤ ((vw w (y w i) + g i w : ℤ) : ℝ) ∧
      ((vw w (y w i) + g i w : ℤ) : ℝ) ≤
        ((vw w (if ch w then x1 i else x2 i) + g i w : ℤ) : ℝ)
          + wt Se (fun l => 1 / (l : ℝ) ^ 2) w) →

    0 ≤ f → 0 ≤ b → 0 ≤ L → 1 ≤ xx → 0 ≤ CB → 0 ≤ CN →
    (Fintype.card I : ℝ) ≤ nI →
    (∀ i, B i ≤ CB * f * b * (L + Real.log xx)) →
    (∀ i, ∑ l ∈ S, N0 i l * Real.log l ≤ CN * f * b * (L + Real.log xx)) →
    ∑ w ∈ T, lw w * (vw w (cmFactor al x (u w) (y w)) : ℝ) ≤
      nI * ((3 * CB + CN) * f * b * (L + Real.log xx) + 1)

end Formalism.PairingDivisionLocalBalance
end
end

