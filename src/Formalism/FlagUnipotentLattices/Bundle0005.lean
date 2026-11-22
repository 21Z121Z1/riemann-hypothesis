import Formalism.FlagUnipotentLattices.Bundle0002
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.Bundle0002
import Formalism.FlagUnipotentLattices.Bundle0004

-- bundled from Formalism.FlagUnipotentLattices.GlobalAssemblyDoubled
section
namespace Formalism.HermitianLatticeCounting.Final.S4

theorem global_assembly : Formalism.HermitianLatticeCounting.S4.WeightedAmplitudeSqSumBoundTwoTypeClasses := Formalism.HermitianLatticeCounting.P.hermitian_assembly_numeric_bound
theorem global_assembly_doubled : Formalism.HermitianLatticeCounting.S4.NonGenericBoundLargeHeight := Formalism.HermitianLatticeCounting.P.non_generic_bound_large_height
theorem geomPowers : Formalism.HermitianLatticeCounting.S4.GeomPowers := Formalism.HermitianLatticeCounting.P.geometric_powers_bound

end Formalism.HermitianLatticeCounting.Final.S4
end

-- bundled from Formalism.FlagUnipotentLattices.QDetNegTranspose
section
open Finset TensorProduct

noncomputable section

namespace Formalism.HermitianLatticeCounting.S8

def QDetNegTranspose : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E →
    ∀ x : ℂ, Formalism.REAL.qdet (fun a b => -E b a) x = ((-1 : ℂ) ^ n) • Formalism.REAL.qdet E ((n : ℂ) - 1 - x)

def ResidueOpE : Prop :=
  ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (r k : ℕ)
    (c w : ℕ → Fin (2 * r + k + 1)) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ V)
    (π : Fin k → Fin k → Module.End ℂ U) (d : ℕ → ℂ) (ℓ : V →ₗ[ℂ] U)
    (lam : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℂ)
    (p : Fin (2 * r + k + 1) → Module.End ℂ (V ⊗[ℂ] (Fin (2 * r + k + 1) → ℂ))) (v : V),
    Formalism.REAL.GlRel E → Formalism.REAL.GlRel π → ChainLabel r k c w → ChainEquivariant r k c w E π d ℓ →
    (∀ (x : ℂ) (v : V), Formalism.REAL.qdet E x v = (∏ s, (x - ((2 * r + k : ℕ) : ℂ) / 2 + lam s)) • v) →
    (∀ (x : ℂ) (a : U), Formalism.REAL.qdet π x a = (∏ j, (x - ((k : ℂ) - 1) / 2 + u j)) • a) →
    ∑ i, p i = 1 → (∀ i j, p i * p j = if i = j then p i else 0) →
    Formalism.REAL.Om (fun _ => true) E (stdRep (2 * r + k + 1)) =
      ∑ i, (lam i + (1 - ((2 * r + k + 1 : ℕ) : ℂ)) / 2) • p i →
    Function.Injective lam → (∀ j < 2 * r, d j ≠ 0) → ℓ v ≠ 0 →
    ∀ i, (LLmap ℓ (c 0) (p i (v ⊗ₜ[ℂ] (Pi.single (c (2 * r)) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ))) = 0 ↔
      ∃ j, u j = lam i + 1 / 2)

end Formalism.HermitianLatticeCounting.S8
end
end

