import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRemovableHyperplane
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

def RemovableHyperplane.Statement : Prop :=
  ∀ (k n : ℕ) (R : ℝ) (f : (Fin (k + 1) → ℂ) → Fin n → ℂ),
    DifferentiableOn ℂ f (Metric.ball 0 R ∩ {t | t 0 ≠ 0}) →
    Bornology.IsBounded (f '' (Metric.ball 0 R ∩ {t | t 0 ≠ 0})) →
    ∃ g : (Fin (k + 1) → ℂ) → Fin n → ℂ, DifferentiableOn ℂ g (Metric.ball 0 R) ∧
      Set.EqOn g f (Metric.ball 0 R ∩ {t | t 0 ≠ 0})

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRiemannExtensionAnalytic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

noncomputable section

def RiemannExtensionAnalytic.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (g f : (Fin k → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ g U →
    (∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0) →
    DifferentiableOn ℂ f (U ∩ {t | g t ≠ 0}) →
    (∀ τ ∈ U, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f '' (N ∩ U ∩ {t | g t ≠ 0}))) →
    ∃ F : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U ∩ {t | g t ≠ 0})

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRiemannExtensionPolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

def RiemannExtensionPolynomial.Statement : Prop :=
  ∀ (k : ℕ) (P : MvPolynomial (Fin k) ℂ) (O : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → ℂ),
    P ≠ 0 → IsOpen O → ContinuousOn f O → DifferentiableOn ℂ f (O ∩ {y | eval y P ≠ 0}) →
    DifferentiableOn ℂ f O

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRootSumHolomorphic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def RootSumHolomorphic.Statement : Prop :=
  ∀ (d : ℕ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (W : Set (Fin d → ℂ)) (Φ : (Fin d → ℂ) → ℂ → ℂ),
    m.Monic → IsOpen W → (∀ y ∈ W, (m.map (MvPolynomial.eval y)).Separable) →
    (∀ y ∈ W, ∀ τ : ℂ, (m.map (MvPolynomial.eval y)).IsRoot τ →
      ∃ O : Set ((Fin d → ℂ) × ℂ), IsOpen O ∧ (y, τ) ∈ O ∧ ∃ Ψ : (Fin d → ℂ) × ℂ → ℂ,
        DifferentiableOn ℂ Ψ O ∧
        ∀ p ∈ O, (m.map (MvPolynomial.eval p.1)).IsRoot p.2 → Φ p.1 p.2 = Ψ p) →
    DifferentiableOn ℂ (fun y => ((m.map (MvPolynomial.eval y)).roots.map (Φ y)).sum) W

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRueckertNullstellensatz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def RueckertNullstellensatz.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (g : (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (f i) w) → AnalyticAt ℂ g w →
    (∀ᶠ z in 𝓝 w, (∀ i, f i z = 0) → g z = 0) →
    ∃ (m : ℕ) (h : Fin k → (σ → ℂ) → ℂ), 0 < m ∧ (∀ i, AnalyticAt ℂ (h i) w) ∧
      ∀ᶠ z in 𝓝 w, g z ^ m = ∑ i, h i z * f i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSeparateWeierstrassDivision
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def SeparateWeierstrassDivision.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (n : σ → ℕ)
    (b : (m : σ) → Fin (n m) → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ),
    (∀ m j, AnalyticAt ℂ (b m j) y₀) →
    (∀ m (T : ℂ), T ^ n m + ∑ j, b m j y₀ * T ^ (j : ℕ) = (T - u₀ m) ^ n m) →
    AnalyticAt ℂ f (y₀, u₀) →
    ∃ (v : σ → (Fin d → ℂ) × (σ → ℂ) → ℂ) (r : ((m : σ) → Fin (n m)) → (Fin d → ℂ) → ℂ),
      (∀ m, AnalyticAt ℂ (v m) (y₀, u₀)) ∧ (∀ α, AnalyticAt ℂ (r α) y₀) ∧
      ∀ᶠ x in 𝓝 (y₀, u₀),
        f x = ∑ m, v m x * (x.2 m ^ n m + ∑ j, b m j x.1 * x.2 m ^ (j : ℕ)) +
          ∑ α, r α x.1 * ∏ m, x.2 m ^ (α m : ℕ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSimpleRootBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def SimpleRootBranch.Statement : Prop :=
  ∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (y : Fin d → ℂ) (τ : ℂ),
    (p.map (MvPolynomial.eval y)).IsRoot τ →
      (p.map (MvPolynomial.eval y)).derivative.eval τ ≠ 0 →
        ∃ (U : Set (Fin d → ℂ)) (B : Set ℂ) (ψ : (Fin d → ℂ) → ℂ),
          IsOpen U ∧ y ∈ U ∧ IsOpen B ∧ τ ∈ B ∧ DifferentiableOn ℂ ψ U ∧ ψ y = τ ∧
            ∀ w ∈ U, ψ w ∈ B ∧
              ∀ s ∈ B, ((p.map (MvPolynomial.eval w)).IsRoot s ↔ s = ψ w)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMatricesOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def SliceMatricesOpen.Statement : Prop :=
  ∀ (n k m : ℕ) (γ : Fin m → (Fin (k + 1) → ℂ) → Fin n → ℂ) (s : Fin m → Fin (k + 1) → ℂ),
    (∀ b, DifferentiableAt ℂ (γ b) (s b)) →
    (∀ b (v : Fin (k + 1) → ℂ), v 0 = 0 → fderiv ℂ (γ b) (s b) v = 0 → v = 0) →
      IsOpen {L : Matrix (Fin k) (Fin n) ℂ |
          ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))} ∧
        {L : Matrix (Fin k) (Fin n) ℂ |
          ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))}.Nonempty

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeDeepWeightMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def poincareDeepWeight (z : ℂ) : ℝ :=
  if Real.log (‖z‖ ^ 2) < -Real.exp 1 then (‖z‖ ^ 2 * Real.log (‖z‖ ^ 2) ^ 2)⁻¹ else 0

def TubeDeepWeightMass.Statement : Prop :=
  ∀ (d : ℕ) (R : ℝ),
    ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R}, ENNReal.ofReal (poincareDeepWeight (z 0)) < ⊤

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountConstant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def UnbranchedProperCountConstant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ),
    IsOpen D → IsPreconnected D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    AnalyticOnNhd ℂ δ D →
    (∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) →
    ∃ N : ℕ, ∀ y ∈ D, δ y ≠ 0 → {x | x ∈ Y ∧ A x = y}.encard = N

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountLocallyConstant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def UnbranchedProperCountLocallyConstant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) →
    ∀ y ∈ D, δ y ≠ 0 → {x | x ∈ Y ∧ A x = y}.Finite ∧
      ∀ᶠ y' in 𝓝 y, {x | x ∈ Y ∧ A x = y'}.encard = {x | x ∈ Y ∧ A x = y}.encard

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnitaryZariskiDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def UnitaryZariskiDense.Statement : Prop :=
  ∀ (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ), p ≠ 0 →
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun ij : Fin n × Fin n => U ij.1 ij.2) p ≠ 0

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

