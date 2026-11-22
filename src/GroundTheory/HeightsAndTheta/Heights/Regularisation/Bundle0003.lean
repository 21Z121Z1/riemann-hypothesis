import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.StLogCoverDescent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology

noncomputable section

def LogCoverDescent.Statement : Prop :=
  ∀ (n a : ℕ) (h : a ≤ n) (φ : (Fin n → ℂ) → ℂ), AnalyticOnNhd ℂ φ (logCover h) →
    (∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) →
    AnalyticOnNhd ℂ (fun z => φ (logLift a z)) (puncturedChart h (ball 0 1)) ∧
      ∀ w ∈ logCover h, φ (logLift a (expCover a w)) = φ w

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsChartBounds
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (Mollifier)

noncomputable section

def ChartMollifiedBounds.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ)
    (A : ReciprocityTheory.AnForm.M.FinHolAtlas D X) (R : RegChartData A) (ρ : Mollifier D),
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      (∀ j, ∀ x ∈ closure (R.mid j), closedBall (R.chart j x) t ⊆ (R.chart j).target) ∧
      ∀ K : ℝ, 0 ≤ K → ∀ j : Fin R.N, ∀ x ∈ R.mid j,
        -K - C ≤ R.phReg ρ K t j x ∧ R.phReg ρ K t j x ≤ C ∧
          (x ∈ R.Yo → R.ph x ≤ R.phReg ρ K t j x)

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsTruncPsh
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (IsPsh)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

def TruncPsh.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ δ B : ℝ, 0 < δ ∧ ∀ j : Fin R.N, ∃ V : Set (Fin D → ℂ), IsOpen V ∧
      V ⊆ (R.chart j).target ∧ (∀ x ∈ R.mid j, closedBall (R.chart j x) δ ⊆ V) ∧
      ∀ K : ℝ, IsPsh V (R.trunc K j) ∧ ∀ y ∈ V, R.trunc K j y ≤ max B (-K)

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsTruncTransfer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

def TruncTransfer.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ δ L B : ℝ, 0 < δ ∧ 1 ≤ L ∧ ∀ (K : ℝ) (j k : Fin R.N),
      ∀ x ∈ R.mid j ∩ R.mid k, ∀ t : ℝ, 0 < t → t < δ → ∀ y ∈ closedBall (R.chart j x) t,
        R.trunc K j y ≤ max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B) +
          (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t

end

end GroundTheory.Heights₂.Heights.Regular
end

