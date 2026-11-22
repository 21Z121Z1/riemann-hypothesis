import Formalism.FlagUnipotentLattices.Bundle0003
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegerGroupLocalParametrization
import Formalism.FlagUnipotentLattices.StabiliserComplementDecomposition
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
import Formalism.FlagUnipotentLattices.Bundle0008
import Formalism.FlagUnipotentLattices.MemLpTwoOfOneTop
import Formalism.FlagUnipotentLattices.Bundle0004
import Formalism.FlagUnipotentLattices.Bundle0005
import Formalism.FlagUnipotentLattices.Bundle0006
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.Bundle0002
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LanglandsParameterEquivariant
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnAndSetIntegralEqZeroOfIsCompact

-- bundled from Formalism.FlagUnipotentLattices.ArithmeticIdentityEntries
section
namespace Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure

theorem unitsSquareIndex : Formalism.HermitianLatticeCounting.LocalIntegralStructure.UnitsSquareIndex := Formalism.HermitianLatticeCounting.P.units_square_index
theorem classNumberBound : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ClassNumberBound := Formalism.HermitianLatticeCounting.P.class_number_bound

end Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
end

-- bundled from Formalism.FlagUnipotentLattices.BlockMinorAbsoluteFromExplicit
section
namespace Formalism.HermitianLatticeCounting.Final.ExpansionTerms

theorem n3cModel : Formalism.HermitianLatticeCounting.ExpansionTerms.DualVectorNormOnGroup := Formalism.HermitianLatticeCounting.P.dual_vector_norm_on_group

end Formalism.HermitianLatticeCounting.Final.ExpansionTerms
end

-- bundled from Formalism.FlagUnipotentLattices.FlagUnipotentLattice
section
open MeasureTheory NumberField Matrix

noncomputable section

namespace Formalism.HermitianLatticeCounting.S7

def KernelZeroEquiv : Prop :=
  ∀ (K H L : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (act : K → L → K) (ρ : L → H →L[ℂ] H)
    (κ : K → H →L[ℂ] H), Continuous κ → (∀ k l, κ (act k l) = κ k ∘L ρ l) →
    (∀ φ : K → H, Continuous φ → (∀ k l, φ (act k l) = ContinuousLinearMap.adjoint (ρ l) (φ k)) →
      (∫ k, κ k (φ k) ∂μ) = 0) → ∀ k, κ k = 0

def KernelZeroUnitary : Prop :=
  ∀ (K H L : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (act : K → L → K) (ρ : L → H ≃ₗᵢ[ℂ] H)
    (κ : K → H →L[ℂ] H), Continuous κ → (∀ k l v, κ (act k l) v = κ k (ρ l v)) →
    (∀ φ : K → H, Continuous φ → (∀ k l, φ (act k l) = (ρ l).symm (φ k)) →
      (∫ k, κ k (φ k) ∂μ) = 0) → ∀ k, κ k = 0

def ResidueRingCard : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g : ℕ),
    Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) = g ^ Module.finrank ℚ E

def LevelIndexField : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g n : ℕ), 1 ≤ g →
    Nat.card (Matrix (Fin n) (Fin n) (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}))ˣ ≤ (g ^ Module.finrank ℚ E) ^ (n ^ 2)

def FlagUnipotent : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (m : ℕ) (F : ℕ → Submodule R V)
    (γ : V →ₗ[R] V), F 0 = ⊥ → F m = ⊤ → (∀ i < m, ∀ x ∈ F (i + 1), γ x - x ∈ F i) → (γ - 1) ^ m = 0

def FlagUnipotentRel : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (m : ℕ) (F : ℕ → Submodule R V)
    (γ : V →ₗ[R] V), (∀ i < m, ∀ x ∈ F (i + 1), γ x - x ∈ F i) → ∀ x ∈ F m, ((γ - 1) ^ m) x ∈ F 0

def FlagUnipotentLattice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (γ : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (P : Ideal (𝓞 E)) (F : ℕ → Submodule (𝓞 E) (Fin n → E)),
    F 0 = P • L → F n = L → (∀ i < n, ∀ x ∈ F (i + 1), γ *ᵥ x - x ∈ F i) →
    ∀ x ∈ L, ((γ - 1) ^ n) *ᵥ x ∈ P • L

end Formalism.HermitianLatticeCounting.S7
end
end

-- bundled from Formalism.FlagUnipotentLattices.ThirdHeightFromSecond
section
namespace Formalism.HermitianLatticeCounting.Final.S8

theorem conjDual : Formalism.HermitianLatticeCounting.S8.ConjDual := Formalism.HermitianLatticeCounting.P.conjugate_dual_representation
theorem assemblyB : Formalism.HermitianLatticeCounting.S8.AssemblyB := Formalism.HermitianLatticeCounting.P.assembly_of_second_bound
theorem residue : Formalism.HermitianLatticeCounting.S8.Residue := Formalism.HermitianLatticeCounting.P.residue_formula

theorem explicitC : Formalism.HermitianLatticeCounting.S8.ExplicitC := Formalism.HermitianLatticeCounting.P.explicit_constant_bound

end Formalism.HermitianLatticeCounting.Final.S8
end

