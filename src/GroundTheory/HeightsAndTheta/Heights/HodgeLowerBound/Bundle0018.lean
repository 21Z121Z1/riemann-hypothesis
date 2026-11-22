import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerSpan
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def PlueckerSpan.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (τ : Ψ) (i : Fin (D.N - 1)),
    Submodule.span Ω (Set.range (Pl.pluecker τ i)) =
      Submodule.span Ω (Set.range (flagMinor (genMatFr Ω Ψ D.N τ) i))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsProjLineAmple
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ContDiff

def ProjLineAmple.Statement : Prop :=
  ∀ A : HermLine (PBlk 2), IsSmoothHerm A → 0 < A.a () → AmpleOnGenericFibre (⊥ : Ideal (MRing (PBlk 2))) A

namespace Line

theorem isOpen_nonzeroL : IsOpen {y : (Σ _ : Unit, Fin 2) → ℂ | ∃ i, y ⟨(), i⟩ ≠ 0} := by
  simp only [Set.ofPred_exists]
  exact isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRatioFieldSpan
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def RatioFieldSpan.Statement : Prop :=
  ∀ (F M : Type) [Field F] [Field M] [Algebra F M] (I J : Type) (u : I → M) (w : J → M) (v v' : M),
    Submodule.span F (Set.range u) = Submodule.span F (Set.range w) →
    v ∈ Submodule.span F (Set.range u) → v' ∈ Submodule.span F (Set.range u) → v ≠ 0 → v' ≠ 0 →
    IntermediateField.adjoin F (Set.range fun i => u i / v) = IntermediateField.adjoin F (Set.range fun j => w j / v')

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

