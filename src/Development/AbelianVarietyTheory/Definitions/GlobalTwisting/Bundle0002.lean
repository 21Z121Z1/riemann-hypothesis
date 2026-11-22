import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Formalism.LandauZeroFreeBounds.Statement
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
section
noncomputable section

namespace GlobalTheory.NT

open Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField IsDedekindDomain ArithmeticFunction
open Formalism.HermitianLattices.GL2PrimeSums (Li PP)

def ZeroFreeRegionPrimitiveCharacter : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ q → χ.IsPrimitive →
    ∀ s : ℂ, 1 - c / Real.log (max (q : ℝ) (q * |s.im|)) ≤ s.re → DirichletCharacter.LFunction χ s = 0 →
      IsRealChar χ ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
      ∀ s' : ℂ, 1 - c / Real.log (max (q : ℝ) (q * |s'.im|)) ≤ s'.re → DirichletCharacter.LFunction χ s' = 0 → s' = s

def PageTheorem : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (β₁ β₂ : ℝ), χ₁.IsPrimitive → χ₂.IsPrimitive → IsRealChar χ₁ → IsRealChar χ₂ →
    (q₁ : ℝ) ≤ Q → (q₂ : ℝ) ≤ Q → 1 - c / Real.log Q < β₁ → β₁ < 1 → 1 - c / Real.log Q < β₂ → β₂ < 1 →
    DirichletCharacter.LFunction χ₁ β₁ = 0 → DirichletCharacter.LFunction χ₂ β₂ = 0 →
    q₁ = q₂ ∧ ∀ n : ℕ, χ₁ (n : ZMod q₁) = χ₂ (n : ZMod q₂)

def ZetaClassicalZeroFreeRegion : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)

def LFunctionPositive_conductorFourEight : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q = 4 ∨ q = 8) → χ.IsPrimitive → ∀ σ : ℝ, 0 < σ →
    0 < (DirichletCharacter.LFunction χ σ).re ∧ (DirichletCharacter.LFunction χ σ).im = 0

def QE : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u →
    ‖psi0 χ u + zsum χ {ρ | |ρ.im| < T} (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤
      C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ {ρ | |ρ.im| < 1} (fun ρ => 1 / ‖ρ‖))

def QF : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
    (ntZeros χ ∩ {ρ | |ρ.im - t| ≤ 1}).Finite ∧
      zsumR χ {ρ | |ρ.im - t| ≤ 1} (fun _ => 1) ≤ C * Real.log (q * (|t| + 2))

def QFsum : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T →
    (ntZeros χ ∩ {ρ | |ρ.im| ≤ T}).Finite ∧
      zsumR χ {ρ | 1 < |ρ.im| ∧ |ρ.im| < T} (fun ρ => 1 / |ρ.im|) ≤ C * Real.log (q * T) ^ 2

def QFsym : Prop :=
  (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ ρ : ℂ,
    (ρ ∈ ntZeros χ ↔ 1 - ρ ∈ ntZeros χ⁻¹) ∧ (ρ ∈ ntZeros χ ↔ 1 - (starRingEnd ℂ) ρ ∈ ntZeros χ) ∧
    (ρ ∈ ntZeros χ → mult χ⁻¹ (1 - ρ) = mult χ ρ ∧ mult χ (1 - (starRingEnd ℂ) ρ) = mult χ ρ ∧ 1 ≤ mult χ ρ)) ∧
  ∀ σ : ℝ, 0 < σ → σ < 1 → (riemannZeta σ).re < 0 ∧ (riemannZeta σ).im = 0

def QG : Prop :=
  (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y) ∧
  (∀ y : ℝ, 2 ≤ y → (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ 2 * y / Real.log y) ∧
  (∀ y : ℝ, 2 ≤ y → Chebyshev.theta y < y * Real.log 4) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ y : ℝ, 2 ≤ y → c * y ≤ Chebyshev.theta y) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → |∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) - Real.log y| ≤ C)

def QC : Prop :=
  ∀ e : ℝ, 0 < e → ∃ c : ℝ, 0 < c ∧ ∀ σ Q : ℝ, 4 / 5 ≤ σ → σ ≤ 1 → 3 ≤ Q →
    ∑ q ∈ Finset.range ⌊Q⌋₊, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive},
      zsumR χ {ρ | σ ≤ ρ.re ∧ |ρ.im| ≤ Q} (fun _ => 1) ≤ c * Q ^ ((6 + e) * (1 - σ))

def QA : Prop :=
  ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L],
      2 ≤ bigQ K L → ∃ (θ : (L ≃ₐ[K] L) → ℝ) (β : ℝ),
        (((∀ σ, θ σ = 0) ∧ ∀ (χ : (L ≃ₐ[K] L) →* ℂˣ) (b : ℝ), χ ^ 2 = 1 → 1 - 1 / (8 * Real.log (bigQ K L)) < b → b < 1 →
            ¬ HeckeZero L χ b) ∨
          ∃ χ₁ : (L ≃ₐ[K] L) →* ℂˣ, χ₁ ^ 2 = 1 ∧ 1 - 1 / (8 * Real.log (bigQ K L)) < β ∧ β < 1 ∧ HeckeZero L χ₁ β ∧
            ∀ σ, (θ σ : ℂ) = (χ₁ σ : ℂˣ)) ∧
        ∀ (σ : L ≃ₐ[K] L) (X : ℝ), bigQ K L ^ c₂ ≤ X →
          |(Module.finrank K L : ℝ) * piC L σ X - (Li X - θ σ * Li (X ^ β))| ≤
            C * (Real.exp (-(c₃ * Real.log X / Real.log (bigQ K L))) +
              Real.exp (-(Real.sqrt (c₃ * Real.log X) / Real.sqrt (Module.finrank ℚ K)))) * (Li X - θ σ * Li (X ^ β))

def QB : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L],
    2 ≤ bigQ K L → ∀ (χ : (L ≃ₐ[K] L) →* ℂˣ) (β : ℝ), χ ^ 2 = 1 → β < 1 → HeckeZero L χ β →
      c / bigQ K L ^ 2 ≤ (1 - β) * Real.log (bigQ K L)

def RayField : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) ∧
      Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ IsFrob L 𝔭 σ} = ⊤ ∧
      ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
        ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔
          ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α})

def QAQ : Prop :=
  ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧ ∀ (m : ℕ) [NeZero m], 3 ≤ m → m % 4 ≠ 2 → ∃ (θ : ℕ → ℝ) (β : ℝ),
    ((∀ a, θ a = 0) ∨ ∃ χ₁ : DirichletCharacter ℂ m, χ₁ ≠ 1 ∧ IsRealChar χ₁ ∧ 1 - 1 / (8 * Real.log m) < β ∧ β < 1 ∧
        DirichletCharacter.LFunction χ₁ β = 0 ∧ ∀ a : ℕ, (θ a : ℂ) = χ₁ (a : ZMod m)) ∧
    ∀ a : ℕ, a.Coprime m → ∀ X : ℝ, (m : ℝ) ^ c₂ ≤ X →
      |(m.totient : ℝ) * (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card : ℝ) -
          (Li X - θ a * Li (X ^ β))| ≤
        C * (Real.exp (-(c₃ * Real.log X / Real.log m)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
          (Li X - θ a * Li (X ^ β))

def QBQ : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m) (β : ℝ), 3 ≤ m → χ ≠ 1 → IsRealChar χ → β < 1 →
    DirichletCharacter.LFunction χ β = 0 → c / (m : ℝ) ^ 2 ≤ (1 - β) * Real.log m

def PsiReg : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ M : ℝ, 8 ≤ M → (q : ℝ) ≤ M → (∀ ρ ∈ ntZeros χ, ρ.re ≤ 1 - c₀ / Real.log (M * (|ρ.im| + 3))) →
    ∀ u : ℝ, 3 ≤ u → ‖psi0 χ u‖ ≤ C * u * (Real.log u + Real.log M) ^ 2 *
      Real.exp (-(c * Real.log u / (Real.log M + Real.sqrt (Real.log u))))

def PNT : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ u : ℝ, 1 ≤ u → ‖psi0 χ u‖ ≤ C * u * Real.exp (-(c * Real.sqrt (Real.log u)))

def IntegralFormulaTwistedChebyshev : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ y : ℝ, 1 ≤ y →
    MeasureTheory.IntegrableOn (fun u : ℝ => psi0 χ u / (u : ℂ) ^ 2) (Set.Ioi y) ∧
      gChi χ y = -(y : ℂ) * ∫ u in Set.Ioi y, psi0 χ u / (u : ℂ) ^ 2

def WeightedSumTendsto : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ x : ℝ, 1 ≤ x →
    Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, ((GlobalTheoryTheory.cn x n : ℝ) : ℂ) * χ (n : ZMod q))
      Filter.atTop (nhds (-gChi χ x))

def FewBadRealCharacters : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
    (({c : Σ q : ℕ, DirichletCharacter ℂ (q + 1) | ((c.1 + 1 : ℕ) : ℝ) ≤ Q ∧ c.2.IsPrimitive ∧ IsRealChar c.2 ∧ c.2 ≠ 1 ∧
      ¬ GoodFor Q c.2}.ncard : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 4)

def ChebyshevPsiCharacterBounds : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → GoodFor Q χ →
    (∀ u : ℝ, 2 ≤ u → ‖psi0 χ u‖ ≤
      C * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2)) ∧
    ∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u → ‖psi0 χ u‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u))

def ChebyshevTailSmall : Prop :=
  ∃ C : ℝ, ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Q : ℝ,
    x ^ (eps / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (eps / 4) →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → GoodFor Q χ →
      (∃ S : ℂ, TailSum χ (zz x) S ∧ ‖(x : ℂ) * S‖ ≤ x ^ eps) ∧ ‖logDerivativeAtOne χ‖ ≤ 200 * eps * Real.log x + C

def QAK : Prop :=
  ∃ C₀ Cr cr cb : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < cb ∧ ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 1 ≤ M →
    ∃ (G β : ℝ) (θ : ℤ) (π₁ π₂ : ℝ → ℕ) (η' : ℝ → ℝ),
      1 ≤ G ∧ G ≤ 4 * d * (M : ℝ) ^ 2 ∧ θ ∈ ({-1, 0, 1} : Set ℤ) ∧
      (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / ((4 * d * (M : ℝ) ^ 2) ^ 2 * Real.log (4 * d * (M : ℝ) ^ 2)) ≤ 1 - β) ∧
      (∀ Y : ℝ, 1 ≤ Y → (π₂ Y : ℝ) ≤ 2 * Real.sqrt Y) ∧
      (∀ Y : ℝ, 0 ≤ η' Y ∧ η' Y ≤ 3 * Real.log (4 * d * (M : ℝ) ^ 2)) ∧
      (∀ Y : ℝ, (4 * d * (M : ℝ) ^ 2) ^ C₀ ≤ Y →
        |G * ((π₁ Y : ℝ) + π₂ Y + η' Y) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β Y| ≤
          Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr (4 * d * (M : ℝ) ^ 2) Y * Formalism.HermitianLattices.GL2PrimeSums.Emain θ β Y) ∧
      ∀ Y Y' : ℝ, 0 ≤ Y → Y ≤ Y' → (π₁ Y' : ℝ) - π₁ Y ≤
        2 * (({p : ℕ | p.Prime ∧ Y < p ∧ (p : ℝ) ≤ Y' ∧ NormOne d M p}.ncard : ℕ) : ℝ)

def NormPrimesShortIntervals : Prop :=
  ∃ C₀ C c c' : ℝ, 1 ≤ C₀ ∧ 0 < C ∧ 0 < c ∧ 0 < c' ∧ ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 1 ≤ M →
    ∀ X h : ℝ, (4 * d * (M : ℝ) ^ 2) ^ C₀ ≤ X → 0 < h → h ≤ 1 →
      Formalism.HermitianLattices.GL2PrimeSums.rhoErr C c (4 * d * (M : ℝ) ^ 2) X ≤ h / 100 →
      (4 * d * (M : ℝ) ^ 2) ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
      c' * h * (4 * d * (M : ℝ) ^ 2) ^ (-6 : ℝ) * X / Real.log X ≤
        (({p : ℕ | p.Prime ∧ X < p ∧ (p : ℝ) ≤ X * (1 + h) ∧ NormOne d M p}.ncard : ℕ) : ℝ)

def QuadraticSymbolMeans : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (m₀ a₀ : ℕ) (X : ℝ),
    0 < m₀ → 8 ∣ m₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (eps / 5) ∨ zz x < p) → a₀.Coprime m₀ → a₀ % 4 = 3 →
    0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X →
    X ^ ((9 : ℝ) / 10) ≤ ((PP m₀ a₀ X).card : ℝ) ∧ ∃ nStar : ℕ,
      ∀ n n' : ℕ, n ∈ Finset.Icc 1 ⌊zz x⌋₊ → n' ∈ Finset.Icc 1 ⌊zz x⌋₊ → IsPrimePow n → IsPrimePow n' →
        Formalism.HermitianLattices.GL2PrimeSums.outPart m₀ (n * n') ≠ 1 → Formalism.HermitianLattices.GL2PrimeSums.outPart m₀ (n * n') ≠ nStar →
        |(∑ q ∈ PP m₀ a₀ X, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / (PP m₀ a₀ X).card| ≤
          C * Real.exp (-c * Real.log x ^ 2)

def QuadraticSymbolMeanSquare : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (m₀ a₀ : ℕ) (X : ℝ) (κ : ℕ → ℂ),
    0 < m₀ → 8 ∣ m₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (eps / 5) ∨ zz x < p) → a₀.Coprime m₀ → a₀ % 4 = 3 →
    0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → (∀ n, ‖κ n‖ ≤ 1) →
    X ^ ((9 : ℝ) / 10) ≤ ((PP m₀ a₀ X).card : ℝ) ∧
      (∑ q ∈ PP m₀ a₀ X, ‖Ssum x κ q‖ ^ 2) / (PP m₀ a₀ X).card ≤ 36 * x * Real.log x

def QuadraticSymbolMeanSquareWeak : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (m₀ a₀ : ℕ) (X : ℝ) (κ : ℕ → ℂ),
    0 < m₀ → 8 ∣ m₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (eps / 5) ∨ zz x < p) → a₀.Coprime m₀ → a₀ % 4 = 3 →
    0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → (∀ n, ‖κ n‖ ≤ 1) →
    κ 1 = 1 → (∀ m n, κ (m * n) = κ m * κ n) →
    X ^ ((9 : ℝ) / 10) ≤ ((PP m₀ a₀ X).card : ℝ) ∧
      (∑ q ∈ PP m₀ a₀ X, ‖Ssum x κ q‖ ^ 2) / (PP m₀ a₀ X).card ≤ C * x * Real.log x

def ChoiceOfFirstModulus : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ q : ℕ, QNum x eps q ∧
    (∀ M : ℕ, M ≠ 0 → 8 * q ∣ M → BoxQ x eps q M) ∧ ‖Ssum x (fun _ => 1) q‖ ≤ x ^ ((1 : ℝ) / 2 + eps) / 2

def ChoiceOfDiscriminant : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, QNum x eps q → ∃ d : ℕ, DNum x eps q d ∧
    BoxD x eps q d (8 * q * d) ∧ ‖Ssum x (fun _ => 1) d‖ ≤ x ^ ((1 : ℝ) / 2 + eps) / 2 ∧
    ‖Ssum x (psDir q) d‖ ≤ x ^ ((1 : ℝ) / 2 + eps) / 2

def ChoiceOfModulusAndDiscriminant : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ q d : ℕ, QNum x eps q ∧ DNum x eps q d ∧
    BoxQ x eps q (8 * q * d) ∧ BoxD x eps q d (8 * q * d) ∧
    BoundsAtX x eps 4 (psDir q) (8 * q * d) ∧ BoundsAtX x eps 4 (chDir d) (8 * q * d) ∧
    BoundsAtX x eps 4 (fun a => chDir d a * psDir q a) (8 * q * d) ∧ kronSym (-(q : ℤ)) d = -1 ∧
    ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x ^ 3 → Real.log (4 * n * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def UniformZeroFreeRegion : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (x eps : ℝ) (e q d : ℕ), QNum x eps q → DNum x eps q d → BoxQ x eps q (8 * q * d) →
    BoxD x eps q d (8 * q * d) → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharE (2 ^ e) q d χ →
      N ∣ 4 * 2 ^ e * q * d ∧
      ∀ ρ ∈ ntZeros χ, ρ.re ≤ 1 - c / Real.log (((4 * 2 ^ e * q * d : ℕ) : ℝ) * (|ρ.im| + 3))

def ThinScalesBound : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ e q d : ℕ, QNum x eps q → DNum x eps q d →
    BoxQ x eps q (8 * q * d) → BoxD x eps q d (8 * q * d) →
    Real.log (4 * 2 ^ e * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharE (2 ^ e) q d χ →
      ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖gChi χ y‖ ≤ y * Real.exp (-(1 / 2 * x ^ (eps / 8)))

def TypePrimesInDyadicInterval : Prop :=
  ∀ eps A : ℝ, 0 < eps → eps < 1 / 52 → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (d N r : ℕ) (Y : ℝ),
    d.Prime → d % 4 = 3 → 100 ≤ d → 0 < N → d ∣ N → Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 →
    1 ≤ r → (r : ℝ) ≤ x ^ A → Real.exp (x ^ eps) ^ 8 ≤ Y →
    Y ^ ((9 : ℝ) / 10) ≤ (({g : ℕ | g.Prime ∧ Y < g ∧ (g : ℝ) ≤ 2 * Y ∧ NormOne d N g}.ncard : ℕ) : ℝ) ∧
    ∀ E₁ E₂ : Finset ℕ, (E₁.card : ℝ) ≤ Y ^ ((4 : ℝ) / 5) → (E₂.card : ℝ) ≤ Y ^ ((4 : ℝ) / 5) →
      ∃ g₁ g₂ : ℕ, g₁ ∉ E₁ ∧ g₂ ∉ E₂ ∧ g₁ ≠ g₂ ∧ (∀ g ∈ ({g₁, g₂} : Finset ℕ), g.Prime ∧ Y < g ∧ (g : ℝ) ≤ 2 * Y ∧
        NormOne d N g) ∧ Disjoint (Formalism.CyclotomicNorms.BB r g₁) (Formalism.CyclotomicNorms.BB r g₂)

def FewOverlappingExceptionalPrimes : Prop :=
  ∀ (g₁ r : ℕ) (Y : ℝ), g₁.Prime → 1 ≤ r → 1 ≤ Y →
    (({g : ℕ | g.Prime ∧ Y < g ∧ (g : ℝ) ≤ 2 * Y ∧ ¬ Disjoint (Formalism.CyclotomicNorms.BB r g₁) (Formalism.CyclotomicNorms.BB r g)}.ncard : ℕ) : ℝ) ≤
      (3 * r + 1) * (4 * (r : ℝ) ^ 2 * Y ^ ((3 : ℝ) / 4) + 1)

def LevelPrimeShortInterval : Prop :=
  ∀ eps A CY cs : ℝ, 0 < eps → eps < 1 / 52 → 0 < A → 0 < CY → 0 < cs → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (d N g₁ g₂ : ℕ) (Y m F Ts : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 0 < N → d ∣ N →
      Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 → 1 ≤ g₁ → 1 ≤ g₂ → (g₁ : ℝ) ≤ 2 * Y → (g₂ : ℝ) ≤ 2 * Y →
      Real.log Y ≤ CY * x ^ eps → x ^ ((1 : ℝ) / 3) ≤ m → 1 ≤ F → F ≤ x ^ A → 0 < Ts → cs * m * x ^ eps ≤ Real.log Ts →
      ∃ T : ℕ, T.Prime ∧ Ts < T ∧ (T : ℝ) ≤ Ts * (1 + 1 / F) ∧ NormOne d (N * (g₁ * g₂) ^ 2) T

def AuxiliaryNormPrimes : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ C' N₀ : ℝ, 0 < C' ∧ ∀ (d N M₀ J : ℕ) (EX : Finset ℕ), d.Prime → d % 4 = 3 → 100 ≤ d → d ∣ N →
    N₀ ≤ N → 0 < N → 1 ≤ M₀ → (M₀ : ℝ) ≤ (N : ℝ) ^ C → (J : ℝ) ≤ (N : ℝ) ^ C → (EX.card : ℝ) ≤ (N : ℝ) ^ C →
    ∃ S : Finset ℕ, S.card = J ∧ ∀ p ∈ S, p.Prime ∧ p ∉ EX ∧ NormOne d (M₀ * N) p ∧ p ≡ 1 [MOD M₀ * N] ∧
      (p : ℝ) ≤ (N : ℝ) ^ C'

end GlobalTheory.NT

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
section
noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField

def Std (C : FC) : Prop :=
  C.Fixed ∧ C.Cc = 2 ∧ C.P.CLw = 11 * 405 ∧ C.P.Cj0 = 405 ∧ C.P.cw = 9 / 10 ∧ C.P.CYL = 9 ∧ C.P.CccK = 1 ∧
    C.T.Cp = 1 ∧ C.T.eP = 12 ∧ C.T.cTO = 377 ∧ C.CTu = 25 ∧ C.P.CetaF = 6 ∧ 1 ≤ C.P.Cpde ∧ 1000 ≤ C.T.CP ∧
    (∀ c ∈ C.cMid C.P.CF, 1 ≤ c) ∧ ∀ c ∈ C.cLast, 1 ≤ c

def TOv (s : Scale) : ℕ := ⌈s.x ^ (377 : ℝ)⌉₊

def nWv (R : Ranks) (s : Scale) : ℕ :=
  8 * ⌈10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8⌉₊

def h0v (s : Scale) (ch : ℝ) : ℕ := 2 * ⌈s.x ^ ch⌉₊

def Delv (s : Scale) (cD : ℝ) : ℕ := ⌈s.x ^ cD⌉₊

def Lwv (s : Scale) : ℕ := 10 * ⌈(405 : ℝ) * Real.log s.x⌉₊ + 2 * ⌈30 / s.eps⌉₊ + 22

def RankVal (s : Scale) (R : Ranks) : Prop :=
  (s.x ^ (2 + 8 * s.eps) ≤ (R.n : ℝ) ∧ (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps)) ∧
  (Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ) ∧ (R.m : ℝ) ≤ 2 * Real.sqrt (s.x * s.delta1)) ∧
  (s.x ^ (9 / 2 + 10 * s.eps) ≤ (R.k : ℝ) ∧ (R.k : ℝ) ≤ 2 * s.x ^ (9 / 2 + 10 * s.eps)) ∧
  R.r + R.t = 8 * R.f * R.r + 4 + TOv s * nWv R s

namespace RankVal

variable {s : Scale} {R : Ranks}

theorem n_lo (h : RankVal s R) : s.x ^ (2 + 8 * s.eps) ≤ (R.n : ℝ) := h.1.1
theorem n_up (h : RankVal s R) : (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps) := h.1.2

theorem n_le (h : RankVal s R) : (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps + s.eps / 100) := by
  have h2 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ (2 + 8 * s.eps + s.eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith [s.eps_pos])
  linarith [h.n_up]

theorem n_le_of_o (h : RankVal s R) {C : ℝ} (hC : (R.o : ℝ) ≤ C) : (R.n : ℝ) ≤ 2 * C * s.x ^ (2 + 8 * s.eps) := by
  have h0 : 0 < R.o := by
    rcases Nat.eq_zero_or_pos R.o with h0 | h0
    · have h1 := R.toFrame.ord_le_o_mul_two_pow
      have h2 := R.toFrame.ord_pos
      rw [h0] at h1
      omega
    · exact h0
  have h1 : (1 : ℝ) ≤ C := le_trans (by exact_mod_cast h0) hC
  have h2 : 0 ≤ s.x ^ (2 + 8 * s.eps) := Real.rpow_nonneg (by linarith [s.one_lt_alt]) _
  nlinarith [h.n_up]

theorem n_le' (h : RankVal s R) : (R.n : ℝ) ≤ 2 * s.x ^ ((9 : ℝ) / 4) := by
  have := s.eps_lt
  have h2 : s.x ^ (2 + 8 * s.eps + s.eps / 100) ≤ s.x ^ ((9 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith)
  linarith [h.n_le]

end RankVal

def PairWin (s : Scale) (Y : ℝ) : Prop := s.x ^ (1 / s.J) ≤ Y ∧ Y ≤ s.x

def PairRow (Y eps : ℝ) {R : Ranks} (H : Host R) : Prop :=
  H.q.Prime ∧ H.q % 8 = 3 ∧ Real.sqrt (GlobalTheoryTheory.X1 Y eps) < H.q ∧ (H.q : ℝ) ≤ GlobalTheoryTheory.X1 Y eps ∧
  H.d.Prime ∧ H.d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 Y eps) < H.d ∧ (H.d : ℝ) ≤ GlobalTheoryTheory.X2 Y eps ∧
  GlobalTheoryTheory.kronSym (-(H.d : ℤ)) H.q = 1 ∧
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(H.d : ℤ)) p = 1) ∧
  Real.log (H.QS * H.q * H.d) ≤ 2 * Y ^ (eps / 5) * Real.log Y ^ 2

def HostConst (s : Scale) (C8 : ℝ) {R : Ranks} (H : Host R) : Prop :=
  s.J ≤ C8 ∧ (R.o : ℝ) ≤ C8 ∧ (H.QS : ℝ) ≤ C8 * R.n

def HostVal (s : Scale) (C8 : ℝ) {R : Ranks} (H : Host R) : Prop :=
  (∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H) ∧
  (s.delta1 * R.n / 2 ≤ (H.TT.card : ℝ) ∧ (H.TT.card : ℝ) ≤ 2 * s.delta1 * R.n) ∧
  s.x ^ (-s.eps) * R.n ≤ (H.T2.card : ℝ) ∧
  ((H.pde : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8 ∧ (H.pde' : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8) ∧
  (∀ i, ((R.k : ℝ) * s.b) ^ 8 ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8) ∧
  H.Lw = Lwv s ∧ H.ccK = ⊤ ∧ ⌊s.x ^ (s.ez / 5)⌋₊ ≤ H.splitBound ∧ HostConst s C8 H

def HostArith {R : Ranks} (H : Host R) : Prop :=
  (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)) ∧
  (∀ i, H.g i % (H.QS * H.q * H.d) = 1) ∧
  ((Ideal.primesOver (Ideal.span {(H.pde : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E ∧
    (Ideal.primesOver (Ideal.span {(H.pde' : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E) ∧
  ∀ p ∈ H.levelPrimes, H.cls p = .splitK

def HCVal (s : Scale) (cD ch : ℝ) {R : Ranks} (H : Host R) {Tau : Type} [Fintype Tau]
    (eTau : Tau → R.GG) (hc : Tau → HCParam R) (bT : H.TT → ℤ) : Prop :=
  (∀ τ (i : Fin (R.k - 1)), (hc τ).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Delv s cD : ℚ))) ∧
  (∀ τ (hk : 0 < R.k), eTau τ ∉ H.topPlaces →
    (hc τ).u ⟨0, hk⟩ = ((R.k - 2 : ℕ) : ℚ) * (4 * (Delv s cD : ℚ)) + (R.k : ℚ) * (4 * (Delv s cD : ℚ)) + 1 / 2 ∧
    (hc τ).u ⟨R.k - 1, by omega⟩ = -1 / 2) ∧
  (∃ b1 : Tau → ℤ,
    (∀ τ (j : Fin R.m), (hc τ).b j = (b1 τ : ℚ) + (j.1 : ℚ) * (h0v s ch : ℚ) ∧
      (hc τ).e j = (hc τ).b j + (h0v s ch : ℚ) / 2) ∧
    (∀ τ (t : H.TT), eTau τ = R.tau1 t → b1 τ = bT t + ⌊s.b' / s.x⌋) ∧
    (∀ τ, eTau τ ∈ H.thickPlaces → ⌈s.b⌉ ≤ b1 τ ∧ b1 τ < ⌈s.b⌉ + (NumberField.Units.torsionOrder H.E : ℤ)) ∧
    (∀ τ, H.IsThin (eTau τ) → b1 τ = ⌈s.w'' R.n⌉)) ∧
  ∀ j : Fin R.m, UpperTheory.MUQ (fun τ => H.emb (eTau τ)) (fun τ => (hc τ).e j)

structure Val (C : FC) (cD ch : ℝ) {D : D7} (L : SizeData₂ D) : Prop where
  ranks : RankVal L.sc D.R
  host : HostVal L.sc C.P.Cpde D.host
  hc : HCVal L.sc cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc L.bT
  dlog : |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps
  Del_eq : D.s.Del = (Delv L.sc cD : ℚ)
  eta_eq : L.etaSz = (D.R.m : ℝ) * (h0v L.sc ch : ℝ)
  La_eq : L.LaG = G.La C.GK L.sc
  bT_le : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ)
  logFiveDepth_eq : L.j0 = ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊
  Ct_eq : L.Ct = C.Ct
  Cc_eq : L.Cc = C.Cc
  CGam_eq : L.CGam = C.CGam
  secondConstant_eq : D.host.CT2 = C.CT2
  words : Fintype.card D.what₂.Word = ⌈3 * GamL L ^ 2 * L.sc.x ^ C.P.CF⌉₊
  etaF_eq : D.div.etaF = 6 * L.sc.x ^ (-C.P.CF)

def SzRow (P : FC → ∀ D : D7, SizeData₂ D → Prop) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ C : FC, Std C → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ,
    ∀ (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x → Val C cD ch L → P C D L

theorem pairWin_self (s : Scale) : PairWin s s.x := by
  refine ⟨?_, le_rfl⟩
  have h : 1 / s.J ≤ 1 := (div_le_one (lt_of_lt_of_le one_pos s.one_le_J)).2 s.one_le_J
  simpa using Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le h

theorem PairWin.one_lt {s : Scale} {Y : ℝ} (h : PairWin s Y) : 1 < Y :=
  (Real.one_lt_rpow s.one_lt_alt (one_div_pos.2 (lt_of_lt_of_le one_pos s.one_le_J))).trans_le h.1

theorem PairWin.rpow_ez_le {s : Scale} {Y : ℝ} (h : PairWin s Y) {c : ℝ} (hc : 0 < c) :
    s.x ^ (s.ez / c) ≤ Y ^ (s.eps / c) := by
  have hx : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have e : s.ez / c = 1 / s.J * (s.eps / c) := by unfold Scale.ez; ring
  rw [e, Real.rpow_mul hx.le]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) h.1 (div_nonneg s.eps_pos.le hc.le)

theorem PairWin.rpow_le {s : Scale} {Y : ℝ} (h : PairWin s Y) {a : ℝ} (ha : 0 ≤ a) : Y ^ a ≤ s.x ^ a :=
  Real.rpow_le_rpow (by linarith [h.one_lt]) h.2 ha

theorem PairWin.log_le {s : Scale} {Y : ℝ} (h : PairWin s Y) : Real.log Y ≤ Real.log s.x :=
  Real.log_le_log (by linarith [h.one_lt]) h.2

theorem PairWin.log_div_le {s : Scale} {Y : ℝ} (h : PairWin s Y) : Real.log s.x / s.J ≤ Real.log Y := by
  have hx : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have h1 := Real.log_le_log (Real.rpow_pos_of_pos hx _) h.1
  rw [Real.log_rpow hx] at h1
  calc Real.log s.x / s.J = 1 / s.J * Real.log s.x := by ring
    _ ≤ _ := h1

theorem PairWin.rpow_inv_le {s : Scale} {Y C : ℝ} (h : PairWin s Y) (hJ : s.J ≤ C) : s.x ^ (1 / C) ≤ Y :=
  (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le
    (one_div_le_one_div_of_le (lt_of_lt_of_le one_pos s.one_le_J) hJ)).trans h.1

theorem PairWin.z_log_sq_le {s : Scale} {Y : ℝ} (h : PairWin s Y) :
    Y ^ (s.eps / 5) * Real.log Y ^ 2 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  have h0 : 0 ≤ Real.log Y := Real.log_nonneg h.one_lt.le
  have h1 := h.rpow_le (a := s.eps / 5) (by linarith [s.eps_pos])
  exact mul_le_mul h1 (pow_le_pow_left₀ h0 h.log_le 2) (sq_nonneg _)
    (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)

theorem four_mul_QS_div {R : Ranks} (H : Host R) : 4 * (H.QS / 4) = H.QS :=
  Nat.mul_div_cancel' (Dvd.dvd.trans ⟨2 ^ R.e, by ring⟩ H.tower_dvd)

theorem pairRow_iff_rowq (Y eps : ℝ) {R : Ranks} (H : Host R) : PairRow Y eps H ↔ Rowq Y eps (H.QS / 4) H.q H.d := by
  have e : (4 : ℝ) * ((H.QS / 4 : ℕ) : ℝ) = H.QS := by exact_mod_cast four_mul_QS_div H
  unfold PairRow Rowq
  rw [e]

namespace HostVal

variable {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R}

theorem split_tie (h : HostVal s C8 H) : ⌊s.x ^ (s.ez / 5)⌋₊ ≤ H.splitBound := h.2.2.2.2.2.2.2.1

theorem J_le (h : HostVal s C8 H) : s.J ≤ C8 := h.2.2.2.2.2.2.2.2.1

theorem o_le (h : HostVal s C8 H) : (R.o : ℝ) ≤ C8 := h.2.2.2.2.2.2.2.2.2.1

theorem QS_le (h : HostVal s C8 H) : (H.QS : ℝ) ≤ C8 * R.n := h.2.2.2.2.2.2.2.2.2.2

theorem one_le (h : HostVal s C8 H) : 1 ≤ C8 := s.one_le_J.trans h.J_le

theorem eps_div_le_ez (h : HostVal s C8 H) : s.eps / C8 ≤ s.ez :=
  div_le_div_of_nonneg_left s.eps_pos.le (lt_of_lt_of_le one_pos s.one_le_J) h.J_le

theorem log_cond_le (h : HostVal s C8 H) :
    Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  obtain ⟨Y, hY, hr⟩ := h.1
  have := hY.z_log_sq_le
  linarith [hr.2.2.2.2.2.2.2.2.2.2]

theorem d_le (h : HostVal s C8 H) : (H.d : ℝ) ≤ GlobalTheoryTheory.X2 s.x s.eps := by
  obtain ⟨Y, hY, hr⟩ := h.1
  exact hr.2.2.2.2.2.2.2.1.trans (Real.exp_le_exp.2 hY.z_log_sq_le)

theorem split (h : HostVal s C8 H) (p : ℕ) (hp : p.Prime) (hle : (p : ℝ) ≤ s.x ^ (s.ez / 5)) :
    GlobalTheoryTheory.kronSym (-(H.d : ℤ)) p = 1 := by
  obtain ⟨Y, hY, hr⟩ := h.1
  exact hr.2.2.2.2.2.2.2.2.2.1 p hp (hle.trans (hY.rpow_ez_le (by norm_num)))

theorem mono (h : HostVal s C8 H) {C8' : ℝ} (hC : C8 ≤ C8') : HostVal s C8' H := by
  have hN : (1 : ℝ) ≤ (H.QS : ℝ) * H.q * H.d := by
    have : 0 < H.QS * H.q * H.d := Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos
    exact_mod_cast this
  have m := Real.rpow_le_rpow_of_exponent_le hN hC
  obtain ⟨a, b, c, ⟨d1, d2⟩, e, f, g, i, j1, j2, j3⟩ := h
  exact ⟨a, b, c, ⟨d1.trans m, d2.trans m⟩, e, f, g, i, j1.trans hC, j2.trans hC,
    j3.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))⟩

end HostVal

end GlobalTheory.EX

end
end

