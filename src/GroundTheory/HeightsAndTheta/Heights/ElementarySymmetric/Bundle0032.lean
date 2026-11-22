import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0004

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.HeckeRatioPoleOrders
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Filter Topology

noncomputable section

def HeckeRatioPoleOrders.Statement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), Odd p →
    (∀ k < p, Tendsto (fun τ : ℍ ↦
      Function.Periodic.qParam 1 τ ^ (p - 1) * (heckeRatios ⟨p, hp.pos⟩ τ).esymm k) atImInfty (𝓝 0)) ∧
    Tendsto (fun τ : ℍ ↦
      Function.Periodic.qParam 1 τ ^ (p - 1) * (heckeRatios ⟨p, hp.pos⟩ τ).esymm p) atImInfty (𝓝 1) ∧
    Tendsto (fun τ : ℍ ↦ (heckeRatios ⟨p, hp.pos⟩ τ).esymm (p + 1)) atImInfty (𝓝 ((p : ℂ) ^ 12))

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.HeckeRatioPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial

noncomputable section

def HeckeRatioPoly.Statement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), Odd p → ∃ Q : ℕ → ℤ[X],
    (∀ (k : ℕ) (τ : ℍ), (heckeRatios ⟨p, hp.pos⟩ τ).esymm k = aeval (modularJ τ) (Q k)) ∧
    (∀ k < p, (Q k).natDegree < p - 1) ∧ (Q p).Monic ∧ (Q p).natDegree = p - 1 ∧
    Q (p + 1) = C ((p : ℤ) ^ 12)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.JPolyLeading
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial Filter Topology

noncomputable section

def JPolyLeading.Statement : Prop :=
  ∀ Q : ℤ[X], Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ Q.natDegree * aeval (modularJ τ) Q)
    atImInfty (𝓝 (Q.leadingCoeff : ℂ))

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

