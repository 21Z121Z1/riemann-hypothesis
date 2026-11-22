import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSmulIntegralMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSelfDualLatticeAtPlaceIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceBasisGramIntegralInvertibl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.SDBasis

theorem exists_basis_unimodular : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → ∃ β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, β i j ∈ idAt D (· = v)) ∧ (∀ i j, β' i j ∈ idAt D (· = v)) ∧ β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) ∧ (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v ε Λ hT hεε hcε hεO hε hΛ
  obtain ⟨β, β', hβ, hβ', h1, h2, h3⟩ :=
    _root_.GlobalTheory.IwaPlace.FreeAt.exists_basis D S.rank v ε Λ hT hεε hcε hεO hε hΛ.1 (_root_.GlobalTheory.IwaPlace.SDStable.smul_mem D S v Λ hΛ) hΛ.2.1 (_root_.GlobalTheory.IwaPlace.SDBound.exists_mul_mem_intAt D S v Λ hΛ)
  exact ⟨β, β', hβ, hβ', h1, h2, h3, _root_.GlobalTheory.IwaPlace.GramBasis.gram_basis D S v ε Λ β β' hεε hcε hεO hε hΛ hβ hβ' h1 h2 h3⟩

end GlobalTheory.IwaPlace.SDBasis
