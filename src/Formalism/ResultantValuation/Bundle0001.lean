import Mathlib

-- bundled from Formalism.ResultantValuation.BoundedCubic
section
noncomputable section

namespace Formalism.ResultantValuation

def thirdDiff {G : Type} [AddCommGroup G] (φ : G → ℝ) (x y z : G) : ℝ :=
  φ (x + y + z) - φ (x + y) - φ (x + z) - φ (y + z) + φ x + φ y + φ z - φ 0

def BoundedCubic : Prop :=
  ∀ (G : Type) [AddCommGroup G] (φ : G → ℝ), (∃ C : ℝ, ∀ x, |φ x| ≤ C) →
    (∃ c : ℝ, ∀ x y z, thirdDiff φ x y z = c) → ∀ x, φ x = φ 0

end Formalism.ResultantValuation
end
end

-- bundled from Formalism.ResultantValuation.KoszulSecondDifferential
section
open Polynomial

noncomputable section

namespace Formalism.ResultantValuation

def AdjugateRankOne : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (A : Matrix (Fin n) (Fin n) R), A.det = 0 →
    ∀ k l : Fin n, A.adjugate k l • A.adjugate =
      Matrix.vecMulVec (fun i => A.adjugate i l) (fun j => A.adjugate k j)

def koszulFirstDifferential {A : Type} [CommRing A] (r : ℕ) (x y : A) :
    (Fin r → A) →ₗ[A] (Fin r → A) × (Fin r → A) :=
  LinearMap.prod (x • LinearMap.id) (y • LinearMap.id)

def koszulSecondDifferential {A : Type} [CommRing A] (r : ℕ) (x y : A) :
    (Fin r → A) × (Fin r → A) →ₗ[A] (Fin r → A) :=
  y • LinearMap.fst A (Fin r → A) (Fin r → A) - x • LinearMap.snd A (Fin r → A) (Fin r → A)

abbrev koszulFirstCohomology {A : Type} [CommRing A] (r : ℕ) (x y : A) : Type :=
  LinearMap.ker (koszulSecondDifferential r x y) ⧸
    (LinearMap.range (koszulFirstDifferential r x y)).comap (LinearMap.ker (koszulSecondDifferential r x y)).subtype

abbrev truncPoly (k : Type) [Field k] (n : ℕ) : Type := k[X] ⧸ Ideal.span {(X : k[X]) ^ n}

def KoszulLength : Prop :=
  ∀ (k : Type) [Field k] (n r : ℕ), 1 ≤ n → ∀ (u : (truncPoly k n)ˣ) (w : truncPoly k n),
    Module.length (truncPoly k n)
      (koszulFirstCohomology r (Ideal.Quotient.mk _ X * (u : truncPoly k n))
        (Ideal.Quotient.mk _ X * w)) = ((2 * r : ℕ) : ℕ∞)

open Classical in

def ComplementCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (r t : ℕ), Module.finrank F V = r + t → ∀ v : Fin r → V,
    Nat.card {U : Submodule F V //
        Module.finrank F U = t ∧ Submodule.span F (Set.range v) ⊔ U = ⊤} =
      if LinearIndependent F v then Fintype.card F ^ (r * t) else 0

def SubspaceMobius : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V],
    (∑ᶠ W : Submodule F V, (-1 : ℤ) ^ Module.finrank F W *
        (Fintype.card F : ℤ) ^ (Module.finrank F W).choose 2) =
      if Module.finrank F V = 0 then 1 else 0

def parabolicSet (F : Type) [Field F] (r t : ℕ) : Set (GL (Fin (r + t)) F) :=
  {g | ∀ i j : Fin (r + t), r ≤ (i : ℕ) → (j : ℕ) < r → (g : Matrix (Fin (r + t)) (Fin (r + t)) F) i j = 0}

def ParabolicConstant : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (r t : ℕ),
    (∏ i ∈ Finset.Icc 1 r, (1 - (Fintype.card F : ℝ) ^ (-(i : ℤ)))) *
        ((Nat.card (GL (Fin (r + t)) F) : ℝ) / (Nat.card (parabolicSet F r t) : ℝ)) *
        (∏ i ∈ Finset.Icc (t + 1) (r + t), (1 - (Fintype.card F : ℝ) ^ (-(i : ℤ))))⁻¹ =
      (Fintype.card F : ℝ) ^ (r * t)

def CMFactorUnit : Prop :=
  ∀ (K : Type) [Field K] (q ε X : K) (m : ℕ), q = 1 → ε ^ 2 = 1 → Odd m → X ^ m = 1 → X ≠ 1 →
    (1 - X * ε) * (1 - X⁻¹ * ε) + (q - 1) * ε ^ 2 ≠ 0

end Formalism.ResultantValuation
end
end

-- bundled from Formalism.ResultantValuation.ResultantConjugate
section
open Finset

noncomputable section

namespace Formalism.ResultantValuation

def PermDetOnePlus : Prop :=
  ∀ (m : ℕ) (σ : Equiv.Perm (Fin m)),
    ((1 : Matrix (Fin m) (Fin m) ℚ) + σ.permMatrix ℚ).det ≠ 0 ↔ ∀ k ∈ σ.cycleType, Odd k

def ResultantConjugate : Prop :=
  ∀ (K : Type) [Field K] (c : K →+* K) (a b : ℕ) (α : Fin a → K) (β : Fin b → K)
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)),
    (∀ i, α i ≠ 0) → (∀ j, β j ≠ 0) →
    (∀ i, c (α i) = (α (σ i))⁻¹) → (∀ j, c (β j) = (β (τ j))⁻¹) →
    (∏ i, ∏ j, (α i - β j)) =
      (-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a * c (∏ i, ∏ j, (α i - β j))

def CayleyDifference : Prop :=
  ∀ (K : Type) [Field K] (ε g₁ g₂ : K), (2 : K) ≠ 0 → ε ≠ 0 → g₁ + 1 ≠ 0 → g₂ + 1 ≠ 0 →
    g₁ = (ε + ε * (g₁ - 1) * (g₁ + 1)⁻¹) * (ε - ε * (g₁ - 1) * (g₁ + 1)⁻¹)⁻¹ ∧
    ε * (g₁ - 1) * (g₁ + 1)⁻¹ - ε * (g₂ - 1) * (g₂ + 1)⁻¹ =
      2 * ε * (g₁ - g₂) / ((g₁ + 1) * (g₂ + 1))

def LaplaceRows : Prop :=
  ∀ (R : Type) [CommRing R] (a b : ℕ) (M : Matrix (Fin (a + b)) (Fin (a + b)) R),
    M.det = ∑ J : {J : Finset (Fin (a + b)) // J.card = a},
      (-1 : R) ^ (a * (a - 1) / 2 + ∑ j ∈ J.1, (j : ℕ)) *
        (M.submatrix (Fin.castAdd b) (J.1.orderEmbOfFin J.2)).det *
        (M.submatrix (Fin.natAdd a)
          ((J.1ᶜ).orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin, J.2]; omega))).det

def VandermondeSplit : Prop :=
  ∀ (R : Type) [CommRing R] (a b : ℕ) (z : Fin (a + b) → R),
    (Matrix.vandermonde z).det =
      (Matrix.vandermonde (z ∘ Fin.castAdd b)).det * (Matrix.vandermonde (z ∘ Fin.natAdd a)).det *
        ∏ i : Fin a, ∏ j : Fin b, (z (Fin.natAdd a j) - z (Fin.castAdd b i))

end Formalism.ResultantValuation
end
end

-- bundled from Formalism.ResultantValuation.WindowValuation
section
noncomputable section

namespace Formalism.ResultantValuation

def LTEUnit : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ i : ℕ, 1 ≤ i → ((u ^ i - 1).valuation : ℕ) = 1 + padicValNat l i

def WindowValuation : Prop :=
  ∀ l b S : ℕ, l.Prime → 1 ≤ b →
    ((∑ i ∈ Finset.Ico b (b + S), padicValNat l i : ℕ) : ℝ) ≤
      (S : ℝ) / ((l : ℝ) - 1) + (Nat.log l (b + S) : ℝ)

def WindowKappaEq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ b S : ℕ, 1 ≤ b →
      (∏ i ∈ Finset.Ico b (b + S), (1 - u ^ i)).valuation =
        S + ∑ i ∈ Finset.Ico b (b + S), padicValNat l i

def WindowKappa : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ b S : ℕ, 1 ≤ b →
      ((∏ i ∈ Finset.Ico b (b + S), (1 - u ^ i)).valuation : ℝ) ≤
        (S : ℝ) + (S : ℝ) / ((l : ℝ) - 1) + (Nat.log l (b + S) : ℝ)

end Formalism.ResultantValuation
end
end

