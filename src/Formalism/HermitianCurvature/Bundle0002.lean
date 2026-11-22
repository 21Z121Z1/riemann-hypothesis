import Formalism.DoubleCosetMeasures.Statement
import Formalism.HermitianCurvature.Bundle0001

-- bundled from Formalism.HermitianCurvature.StatementA
section
namespace Formalism.FourierDecayAlt.A

open Formalism.DoubleCosetMeasures MeasureTheory

def LevelOneKernelPoint : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (l : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ) (C : Type) [AddCommGroup C] [Module R C] (e : C)
    (lam : C →ₗ[R] KR R) (μ₁ : Measure (lowW K (l ++ [1]) t))
    (μ₂ : Measure (upUniG K (l ++ [1]).sum)),
    BB R (l ++ [1]) t ψ C e lam μ₁ μ₂ ≠ 0 →
      lam e = Submodule.Quotient.mk (((t l.length)⁻¹ : Kˣ) : K)

def LevelOneKernelPair : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (l l' : List ℕ) (t t' : ℕ → Kˣ) (ψ : AddChar K ℂ)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (μ₁ : Measure (lowW K (l ++ [1]) t)) (μ₂ : Measure (upUniG K (l ++ [1]).sum))
    (μ₁' : Measure (lowW K (l' ++ [1]) t')) (μ₂' : Measure (upUniG K (l' ++ [1]).sum)),
    BB R (l ++ [1]) t ψ C e lam μ₁ μ₂ ≠ 0 → BB R (l' ++ [1]) t' ψ C e lam μ₁' μ₂' ≠ 0 →
      (((t l.length)⁻¹ : Kˣ) : K) - (((t' l'.length)⁻¹ : Kˣ) : K) ∈ R

end Formalism.FourierDecayAlt.A
end

-- bundled from Formalism.HermitianCurvature.StatementK
section
namespace Formalism.FourierDecayAlt.K

open Matrix Finset Real

def IsUpUni {K : Type} [Field K] {n : ℕ} (u : Matrix (Fin n) (Fin n) K) : Prop :=
  u.BlockTriangular id ∧ ∀ a, u a a = 1

def w0 {K : Type} [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b => if (a : ℕ) + (b : ℕ) + 1 = n then 1 else 0

def BigCellFree : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (v v' u u' : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
    IsUpUni v → IsUpUni v' → IsUpUni u → IsUpUni u' → (∀ a, d a ≠ 0) →
    u * (v * w0 n * Matrix.diagonal d * v') * u' = v * w0 n * Matrix.diagonal d * v' →
    u = 1 ∧ u' = 1

def JointTheoremA : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C' C : ℝ, ∀ (Kx Θ : ℝ) (f r : ℕ) (e σ : ℕ → ℝ),
    4 ≤ Kx → 1 ≤ f → C' ≤ Θ → (r : ℝ) * (C₀ / Θ) ^ f ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + (C₀ * Θ ^ (-(Kx - 5/2))) ^ f) * √(1 + e i) * σ (i - 1) +
        ∑ t ∈ Icc 2 i, ((C₀ / Θ) ^ f) ^ (t - 1) * σ (i - t)) →
    σ (r + 1) ^ 2 ≤
      (1 + C * ((r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2

end Formalism.FourierDecayAlt.K
end

