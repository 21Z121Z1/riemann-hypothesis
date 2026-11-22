import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.DeltaIntSeries
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

def DeltaIntSeries.Statement : Prop :=
  ∃ D : PowerSeries ℤ, coeff 0 D = 1 ∧ (∀ r : ℝ, 0 ≤ r → r < 1 → IntSeriesConv D r) ∧
    ∀ τ : UpperHalfPlane, ModularForm.discriminant τ =
      Function.Periodic.qParam 1 τ * intSeriesEval D (Function.Periodic.qParam 1 τ)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesInv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

def IntSeriesInv.Statement : Prop :=
  ∀ (F : PowerSeries ℤ) (r : ℝ), 0 < r → IntSeriesConv F r → coeff 0 F = 1 →
    ∃ (G : PowerSeries ℤ) (r' : ℝ), 0 < r' ∧ IntSeriesConv G r' ∧ F * G = 1

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesNorm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

def IntSeriesNorm.Statement : Prop :=
  ∀ (F : PowerSeries ℤ) (r : ℝ), 0 < r → IntSeriesConv F r → ∀ p : ℕ, 0 < p → ∀ j : ℕ,
    ∃ E : PowerSeries ℤ, IntSeriesConv E (r ^ p) ∧ ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ r →
      ((Multiset.range p).map fun a : ℕ ↦
          intSeriesEval F (Complex.exp (2 * π * Complex.I * a / p) * t)).esymm j =
        intSeriesEval E (t ^ p)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

def IntSeriesRing.Statement : Prop :=
  ∀ r : ℝ, 0 ≤ r →
    (∃ S : Subring (PowerSeries ℤ), ∀ F, F ∈ S ↔ IntSeriesConv F r) ∧
    (∀ F G, IntSeriesConv F r → IntSeriesConv G r → ∀ z : ℂ, ‖z‖ ≤ r →
      intSeriesEval (F * G) z = intSeriesEval F z * intSeriesEval G z) ∧
    (∀ F, IntSeriesConv F r → ∀ z : ℂ, ‖z‖ ≤ r →
      HasSum (fun n ↦ ((coeff n F : ℤ) : ℂ) * z ^ n) (intSeriesEval F z)) ∧
    (∀ F (r' : ℝ), IntSeriesConv F r → 0 ≤ r' → r' ≤ r → IntSeriesConv F r') ∧
    (∀ (p : ℕ) (hp : p ≠ 0) F, IntSeriesConv F (r ^ p) →
      IntSeriesConv (expand p hp F) r ∧
        ∀ z : ℂ, ‖z‖ ≤ r → intSeriesEval (expand p hp F) z = intSeriesEval F (z ^ p))

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

