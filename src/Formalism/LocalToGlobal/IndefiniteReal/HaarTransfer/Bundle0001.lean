import Mathlib

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.SchurClosable
section
namespace Formalism.IndefR.Leaf

open Filter Topology

def SchurClosable : Prop :=
  ∀ (G H H' : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (π : G →* (H →L[ℂ] H)) (π' : G →* (H' →L[ℂ] H')),
    (∀ g x, ‖π g x‖ = ‖x‖) → (∀ g x, ‖π' g x‖ = ‖x‖) →
    (∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H) →
    ∀ (D : Submodule ℂ H) (A : D →ₗ[ℂ] H'), Dense (D : Set H) →
      (∀ g, ∀ x ∈ D, π g x ∈ D) →
      (∀ g (x : D) (hx : π g x ∈ D), A ⟨π g x, hx⟩ = π' g (A x)) →
      (∀ (u : ℕ → D) (y : H'), Tendsto (fun n => (u n : H)) atTop (𝓝 0) →
        Tendsto (fun n => A (u n)) atTop (𝓝 y) → y = 0) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : D, inner ℂ (A x) (A y) = (c : ℂ) * inner ℂ (x : H) (y : H)

end Formalism.IndefR.Leaf
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.SobLeafP
section
open NumberField NumberField.InfinitePlace

namespace Formalism.IndefR.Leaf.HaarTransferContinuity

variable (F : Type) [Field F] [NumberField F]

abbrev W := ({v : InfinitePlace F // v.IsReal} → ℝ) × ({v : InfinitePlace F // ¬ v.IsReal} → ℂ)

noncomputable def E (x : InfiniteAdeleRing F) : W F :=
  (fun v => Completion.extensionEmbeddingOfIsReal v.2 (x v.1),
   fun v => Completion.extensionEmbedding v.1 (x v.1))

open scoped Classical in
noncomputable def G (w : W F) : InfiniteAdeleRing F := fun v =>
  if h : v.IsReal then (Completion.isometryEquivRealOfIsReal h).symm (w.1 ⟨v, h⟩)
  else (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp h)).symm (w.2 ⟨v, h⟩)

end Formalism.IndefR.Leaf.HaarTransferContinuity
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.Unimod
section
namespace Formalism.IndefR.Leaf

open MeasureTheory

def HaarRightInvProd : Prop :=
  ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [T2Space G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
    [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂],
    (∀ μ : Measure G₁, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
    (∀ μ : Measure G₂, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → μ.IsMulRightInvariant

def HaarRightInvPi : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)]
    [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)],
    (∀ i, ∀ μ : Measure (G i), μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ μ : Measure (∀ i, G i), μ.IsHaarMeasure → μ.IsMulRightInvariant

def HaarRightInvTransfer : Prop :=
  ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (_e : G ≃ₜ* H),
    (∀ μ : Measure G, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ ν : Measure H, ν.IsHaarMeasure → ν.IsMulRightInvariant

end Formalism.IndefR.Leaf
end

