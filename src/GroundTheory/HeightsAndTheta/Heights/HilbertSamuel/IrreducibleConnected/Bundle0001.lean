import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StClopenPieceSheetCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Matrix

def ClopenPieceSheetCount.Statement : Prop :=
  ∀ (n d N : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (Z : Set (Fin n → ℂ)) (Ω : Set (Fin d → ℂ))
    (O F : Set (Fin n → ℂ)),
    IsOpen Ω → IsPreconnected Ω →
    (∀ y ∈ Ω, {x | x ∈ Z ∧ A *ᵥ x = y}.Finite ∧ {x | x ∈ Z ∧ A *ᵥ x = y}.ncard = N ∧
      ∀ x ∈ Z, A *ᵥ x = y → ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
          ContinuousOn g U ∧ g y = x ∧ (∀ w ∈ U, A *ᵥ g w = w) ∧ Z ∩ V = g '' U) →
    IsOpen O → IsClosed F →
    {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} ∩ O = {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} ∩ F →
    ∃ k : ℕ, ∀ y ∈ Ω, {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}.ncard = k

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StEntirePolynomialGrowth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def EntirePolynomialGrowth.Statement : Prop :=
  ∀ (d : ℕ) (f : (Fin d → ℂ) → ℂ) (C : ℝ) (M : ℕ), Differentiable ℂ f →
    (∀ y : Fin d → ℂ, ‖f y‖ ≤ C * (1 + ‖y‖) ^ M) →
    ∃ p : MvPolynomial (Fin d) ℂ, ∀ y : Fin d → ℂ, f y = eval y p

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StGrowthOffHypersurfacePolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def GrowthOffHypersurfacePolynomial.Statement : Prop :=
  ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ) (M : ℕ), Q ≠ 0 →
    DifferentiableOn ℂ f {y | eval y Q ≠ 0} →
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 → ‖f y‖ ≤ C * (1 + ‖y‖) ^ M) →
    ∃ p : MvPolynomial (Fin d) ℂ, ∀ y : Fin d → ℂ, eval y Q ≠ 0 → f y = eval y p

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StMonicRootGrowth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def MonicRootGrowth.Statement : Prop :=
  ∀ (d : ℕ) (m : Polynomial (MvPolynomial (Fin d) ℂ)), m.Monic →
    ∃ (C : ℝ) (M : ℕ), ∀ (y : Fin d → ℂ) (τ : ℂ), (m.map (eval y)).IsRoot τ →
      ‖τ‖ ≤ C * (1 + ‖y‖) ^ M

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StPieceRootProductPolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Matrix

def PieceRootProductPolynomial.Statement : Prop :=
  ∀ (n d N k : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (Z : Set (Fin n → ℂ)) (c : Fin n → ℂ)
    (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Q : MvPolynomial (Fin d) ℂ) (O F : Set (Fin n → ℂ)),
    m.Monic → Q ≠ 0 →
    (∀ x ∈ Z, (m.map (eval (A *ᵥ x))).IsRoot (∑ j, c j * x j)) →
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 →
      {x | x ∈ Z ∧ A *ᵥ x = y}.Finite ∧ {x | x ∈ Z ∧ A *ᵥ x = y}.ncard = N ∧
      ∀ x ∈ Z, A *ᵥ x = y → ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
          DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A *ᵥ g w = w) ∧ Z ∩ V = g '' U) →
    IsOpen O → IsClosed F →
    {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ O = {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ F →
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 → {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}.ncard = k) →
    ∃ G : Polynomial (MvPolynomial (Fin d) ℂ), G.Monic ∧ G.natDegree = k ∧
      ∀ y : Fin d → ℂ, eval y Q ≠ 0 →
        G.map (eval y) = ∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
          (Polynomial.X - Polynomial.C (∑ j, c j * x j))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StatementsBasicOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def IrreducibleBasicOpenConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (W : Ideal (MvPolynomial σ ℂ)) (g : MvPolynomial σ ℂ), W.IsPrime → g ∉ W →
    IsPreconnected (zeroLocus ℂ W \ {x : σ → ℂ | eval x g = 0})

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

