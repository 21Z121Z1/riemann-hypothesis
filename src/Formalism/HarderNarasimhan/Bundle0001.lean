import Formalism.HarderNarasimhan.Statement
import Formalism.LatticeSlopes.CovolAntiSameRank
import Mathlib

-- bundled from Formalism.HarderNarasimhan.DegSupermodZ
section
open Module Submodule

noncomputable section

namespace Formalism.HN

def DegSupermodZ : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L A B : Submodule ℤ E), DiscreteTopology L → A ≤ L → B ≤ L →
    Formalism.F.rk (A ⊔ B) + Formalism.F.rk (A ⊓ B) = Formalism.F.rk A + Formalism.F.rk B ∧
    Formalism.F.deg A + Formalism.F.deg B ≤ Formalism.F.deg (A ⊔ B) + Formalism.F.deg (A ⊓ B)

def SatR : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L N : Submodule R V),
    IsLat ρ L → N ≤ L →
    ∃ N' : Submodule R V, N ≤ N' ∧ N' ≤ L ∧ zl ρ N' = Formalism.F.satur (zl ρ L) (zl ρ N)

def FinSup : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V)
    (S : Set (Submodule R V)), IsLat ρ L → (∀ N ∈ S, N ≤ L) →
    ∃ t : Finset (Submodule R V), (↑t : Set (Submodule R V)) ⊆ S ∧ sSup S = t.sup id

def SatBasic : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V),
    IsLat ρ L →
    (∀ N : Submodule R V, N ≤ L → IsLat ρ N) ∧
    (∀ A B : Submodule R V, A ≤ B → B ≤ L → rk ρ A ≤ rk ρ B ∧ (rk ρ A = rk ρ B → deg ρ A ≤ deg ρ B)) ∧
    (∀ S N : Submodule R V, IsSat ρ L S → S ≤ N → N ≤ L → rk ρ N = rk ρ S → N = S) ∧
    (∀ N : Submodule R V, N ≤ L → (rk ρ N = 0 ↔ N = ⊥)) ∧
    deg ρ (⊥ : Submodule R V) = 0 ∧ IsSat ρ L ⊥ ∧ IsSat ρ L L ∧
    (∀ S : Submodule R V, IsSat ρ L S →
      Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ S)) = rk ρ L - rk ρ S ∧
      rk ρ S ≤ rk ρ L ∧
      Formalism.F.deg (Formalism.F.quot (zl ρ L) (zl ρ S)) = deg ρ L - deg ρ S)

def RatioMax : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L S : Submodule R V),
    IsLat ρ L → IsSat ρ L S → S ≠ L →
    ∃ N : Submodule R V, S < N ∧ IsSat ρ L N ∧
      ∀ N' : Submodule R V, S < N' → N' ≤ L →
        (deg ρ N' - deg ρ S) * ((rk ρ N : ℝ) - rk ρ S) ≤
          (deg ρ N - deg ρ S) * ((rk ρ N' : ℝ) - rk ρ S)

end Formalism.HN
end
end

-- bundled from Formalism.HarderNarasimhan.StatementCor
section
open Module Submodule

noncomputable section

namespace Formalism.HN

def HNCor : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V),
    IsLat ρ L →
    Antitone (hnStep ρ L) ∧
    (L ≠ ⊥ → ∀ θ : ℝ, hnStep ρ L θ = L ↔ θ ≤ muMin ρ L) ∧
    (∀ θ : ℝ, muMax ρ L < θ → hnStep ρ L θ = ⊥) ∧
    (∀ t : ℝ, (Finset.univ.filter (fun j => slopeList ρ L j < t)).card =
      rk ρ L - rk ρ (hnStep ρ L t)) ∧
    (∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → muMax ρ N ≤ muMax ρ L) ∧
    (∀ (N : Submodule R V) (θ : ℝ), N ≤ L → N ≠ ⊥ → θ ≤ muMin ρ N →
      rk ρ N ≤ (Finset.univ.filter (fun j => θ ≤ slopeList ρ L j)).card)

def ImageStep : Prop :=
  ∀ (R ι W F : Type*) [Ring R] [AddCommGroup W] [Module R W] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (V E : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    (ρ : ∀ i, V i →+ E i) (ρ' : W →+ F) (L : ∀ i, Submodule R (V i)) (M : Submodule R W)
    (s : Finset ι) (φ : ∀ i, L i →ₗ[R] M) (C : ι → ℝ) (θ : ℝ),
    (∀ i ∈ s, IsLat (ρ i) (L i)) → IsLat ρ' M →
    (∀ i ∈ s, 0 < C i ∧ (∀ x : L i, ‖ρ' (φ i x : W)‖ ≤ C i * ‖ρ i (x : V i)‖) ∧
      (L i ≠ ⊥ → θ ≤ muMin (ρ i) (L i) - Real.log (C i))) →
    (⨆ i ∈ s, (LinearMap.range (φ i)).map M.subtype) ≤ hnStep ρ' M θ

end Formalism.HN
end
end

