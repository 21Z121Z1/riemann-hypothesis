import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

-- bundled from Formalism.GL3MeanSquares.BoxCountAll
section
noncomputable section

namespace Formalism.HermitianLattices.BoxCountUnconditional

def BoxCountAll : Prop :=
  ∃ C : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxCountHyp C

end Formalism.HermitianLattices.BoxCountUnconditional
end
end

-- bundled from Formalism.GL3MeanSquares.PrimePairOfBoxAndWeakMeanSquareHypotheses
section
open Finset ArithmeticFunction Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2

noncomputable section

namespace Formalism.HermitianLattices.WeakMeanSquareEstimates

def MeanSquareHypW (ε C x₀ : ℝ) : Prop :=
  ∀ (x X : ℝ) (m₀ a₀ : ℕ) (κ : ℕ → ℂ), x₀ ≤ x → 8 ∣ m₀ →
    (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (ε / 5) ∨ x ^ 400 < (p : ℝ)) → a₀.Coprime m₀ → a₀ % 4 = 3 →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ n, ‖κ n‖ ≤ 1) → (∀ a b, κ (a * b) = κ a * κ b) →
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) ∧
    (∑ q ∈ PPset m₀ a₀ X,
        ‖∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2) ≤
      C * x * Real.log x * ((PPset m₀ a₀ X).card : ℝ)

def MeanSquareWeaken : Prop :=
  ∀ ε C x₀ : ℝ, MeanSquareHyp ε C x₀ → MeanSquareHypW ε C x₀

def PrimePairOfBoxAndWeakMeanSquareHypotheses : Prop :=
  ∀ ε C₂ C₂' x₂ C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < C₂ → 0 < C₄ →
    BoxCountHyp C₂ → BoxTailHyp ε C₂' x₂ → MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ExistsSplitGoodPrimePair ε C₂' x

end Formalism.HermitianLattices.WeakMeanSquareEstimates
end
end

-- bundled from Formalism.GL3MeanSquares.WeightedSumIntegralFormula
section
open Finset ArithmeticFunction Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2

noncomputable section

namespace Formalism.HermitianLattices.GL2b2

def WGIntegral : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a w w' : ℝ), 0 < a → 0 < w → w ≤ w' →
    (w' : ℂ) * ZeroFreeRegionGL2.Gchi χ (a / w') - (w : ℂ) * ZeroFreeRegionGL2.Gchi χ (a / w) = -(∫ s in w..w', Formalism.ZeroFreeDirichlet.psiChi χ (a / s))

def WeightedSumIntegralFormula : Prop :=
  ∀ (a w w' : ℝ), 0 < a → 0 < w → w ≤ w' →
    w' * ZeroFreeRegionGL2.G1 (a / w') - w * ZeroFreeRegionGL2.G1 (a / w) = -(∫ s in w..w', (Chebyshev.psi (a / s) - a / s))

def TwInjective : Prop :=
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q q' : ℕ) [Fact q.Prime] [Fact q'.Prime], t ≠ 0 → q ≠ 2 → q' ≠ 2 →
    q.Coprime t → q'.Coprime t → q ≠ q' →
    ∃ n : ℕ, ZeroFreeRegionGL2.tw θ q (n : ZMod (t * q)) ≠ ZeroFreeRegionGL2.tw θ q' (n : ZMod (t * q'))

def NegSymbolBridge : Prop :=
  ∀ q : ℕ, q % 4 = 3 → (∀ n : ℕ, Odd n → jacobiSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q) ∧
    (jacobiSym 2 q = 1 ↔ q % 8 = 7)

def EvenRealTwoPower : Prop :=
  ∀ (e : ℕ) (h : 8 ∣ 2 ^ (e + 2)) (ξ : DirichletCharacter ℂ (2 ^ (e + 2))), ξ.Even → ξ ^ 2 = 1 →
    ξ = 1 ∨ ξ = DirichletCharacter.changeLevel h ZeroFreeRegionGL2.chi8

def NoRealZeroSmall : Prop :=
  (∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0) ∧
  (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8 (σ : ℂ) ≠ 0)

def NoExcOfNoRealZero : Prop :=
  ∀ (c₁ : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), c₁ / Real.log (2 * q) < 1 →
    (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) →
    (∀ s : ℂ, Formalism.ZeroFreeDirichlet.InRegion c₁ q s → Formalism.ZeroFreeDirichlet.IsLZero χ s → s.im = 0) →
    Formalism.ZeroFreeDirichlet.ExcZeros c₁ χ ∅

end Formalism.HermitianLattices.GL2b2
end
end

-- bundled from Formalism.GL3MeanSquares.ZeroDensityBox
section
noncomputable section

namespace Formalism.HermitianLattices.ZeroDensityInBoxes

def ZeroDensityBox : Prop :=
  ∃ C : ℝ, ∀ (Q : ℝ) (S : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1))), 3 ≤ Q →
    (∀ p ∈ S, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)

def BoxTailAll : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxTailHyp ε C x₀

def BoxCountOfZD : Prop :=
  ZeroDensityBox → ∃ C : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxCountHyp C

end Formalism.HermitianLattices.ZeroDensityInBoxes
end
end

