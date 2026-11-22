import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.SymbolExtensionProperty
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

def FLBoundOfGoodS.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (A : FinHolAtlas D X) (d : IndefiniteRowSideFullHecke.EffectiveHS.FSData A Y) (s : Fin D → Fin d.W.n → ℂ),
    d.IsGoodS s → FLBound A d.W.e (fun i => d.W.sec (s i))

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.ImportsAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel

def NatSpaceEqVnat.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] (A : FinHolAtlas D X) (d : IndefiniteRowSideFullHecke.EffectiveHS.HSData A Y) (j : ℕ),
    ((d.natSpace j : Submodule ℂ (Fin A.n → X → ℂ)) : Set (Fin A.n → X → ℂ)) =
      Vnat A (HolLineBundle.split_model_to_place_model d.L₂) (HolLineBundle.split_model_to_place_model d.L) d.φA
        (IndefiniteRowSideFullHecke.EffectiveHS.fsPhi d.W) j

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.ImportsBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

def TopFormNormEqIntegral.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (A : FinHolAtlas D X) (B : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    (ψ : Fin A.n → X → ℝ) (F : Fin A.n → X → ℂ),
    IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight B ψ → F ∈ IndefiniteRowSideFullHecke.EffectiveHS.topForms B →
    topNormSq A ψ F = IndefiniteRowSideFullHecke.EffectiveHS.topFormWeightedL2 ψ F

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.ImportsTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

def HasSymbolIffSymEq.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas D X)
    (d : IndefiniteRowSideFullHecke.EffectiveHS.FSData A Y) (B : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    (s : Fin D → Fin d.W.n → ℂ) (a : ℕ) (F : Fin A.n → X → ℂ) (g : (Fin D → ℕ) → X → ℂ),
    F ∈ IndefiniteRowSideFullHecke.EffectiveHS.topForms B →
    (d.HasSymbol s a F g ↔ d.InFil s a F ∧ SymEq A (fun i => d.W.sec (s i)) F a g)

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtCompact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def TopSecCompact.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (m : ℕ) (F : ℕ → Fin X.A.n → X.U → ℂ) (C : ℝ),
    (∀ n, F n ∈ topSections X.A X.L₂ X.L m) →
    (∀ n, topNormSq X.A (X.wt m) (F n) ≤ ENNReal.ofReal C) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G ∈ topSections X.A X.L₂ X.L m,
      ∀ k x, Tendsto (fun n => F (φ n) k x) atTop (𝓝 (G k x))

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtDelta
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def extEv {D : ℕ} {X : EmbDatum D} (Z : ZeroDatum X) (k : Fin X.A.n) (y : X.U) : ℝ :=
  (∑ i, ‖Z.s i k y‖ ^ 2) * Real.exp (-fsWeight X.e k y) / rSq Z.c

def extX (ε t : ℝ) : ℝ := 1 + Real.log (1 + ε ^ 2) - Real.log (t + ε ^ 2)

def extDen (ε t : ℝ) : ℝ := (extX ε t + 1) ^ 2 + curvEta (extX ε t)

def extFactor (D : ℕ) (ε δ t : ℝ) : ℝ := ((t + δ ^ 2) ^ D)⁻¹ / extDen ε t

def ExtDelta.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (j : ℕ), 1 ≤ D → 2 ≤ j →
    ∀ (g : X.U → ℂ) (θ : ℝ), 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ F₀ : Fin X.A.n → X.U → ℂ,
        (∀ k, ContinuousOn (F₀ k ∘ (X.A.chart k).symm) (X.A.chart k).target) ∧
        (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source,
          F₀ k x = jac X.A k l x * X.L₂.g k l x * X.L.g k l x ^ (D + j) * F₀ l x) ∧
        (∀ k, ∀ x ∉ (X.A.chart k).source, F₀ k x = 0) ∧
        (∀ x ∈ Z.S, res X.A Z.s F₀ x = g x) ∧
        topNormSq X.A (X.wt (D + j)) F₀ ≤ ENNReal.ofReal θ ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ ε → ∃ F ∈ topSections X.A X.L₂ X.L (D + j),
          chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * ‖F₀ k y - F k y‖ ^ 2 *
            Real.exp (-X.wt (D + j) k y) * extFactor D ε δ (extEv Z k y))) ≤
          ENNReal.ofReal (36 * Real.log 2 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g + θ)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

