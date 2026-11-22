import Mathlib
import Formalism.PieriBlockIdeals.Bundle0006
import Formalism.PieriBlockIdeals.StatementLR

-- bundled from Formalism.PieriBlockIdeals.LemmaDGradedOfPieriReal
section
namespace Formalism.CohomologicalDescent.ColumnMinorsFromPieri

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

def LemmaDSkeleton5 : Prop :=
  ∀ (O K V P : Type) (q : ℕ) [CommRing O] [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Algebra O K] [AddCommGroup V]
    [Module K V] [Module O V] [IsScalarTower O K V] [DecidableEq P] [Fintype P] (S : HidaSetting K V P (Fin q))
    (B : LinearMap.BilinForm K V) (n w : ℕ) (lam2 : Fin q → ℕ) (DelL : Submodule O S.W)
    (xi : (P ⊕ Fin q → ℤ) →+ ℤ) (lam : P ⊕ Fin q → ℤ)
    (l : ℕ) (e : ℕ) (i' : ℤ), l.Prime → (∀ m : ℤ, ¬ (l : ℤ) ∣ m → IsUnit (m : O)) →
    S.w = (w : K) → (∀ b, lam2 b ≤ w) → Contra S B → Generated S →
    (∀ x y, B x y = B y x) → (∀ x, x ≠ 0 → 0 < B x x) →
    FiniteDimensional K S.W → (∀ b, ⨆ μ : K, Module.End.eigenspace (S.EW b b) μ = ⊤) →
    (∀ (v : S.W) (μ : Fin q → K), v ≠ 0 → LP.IsHW S.EW μ v → μ = fun b => (lam2 b : K)) →
    (∀ b b', ∀ u ∈ DelL, S.EW b b' u ∈ DelL) →
    (∀ (α : P) (b : Fin q), 0 ≤ xi (Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1)) →
    (∀ κ, xi (lam - κ) ≤ i' → ∀ u ∈ NablaL S B DelL, (u : V) ∈ S.wt κ → (l : O) ^ e • u ∈ DelL) →
    ∀ ν, ∑ α : P, ν (Sum.inl α) + (n : ℤ) = (Fintype.card P : ℤ) * (w : ℤ) → xi (lam - ν) ≤ i' →
      ∀ v ∈ B.dualSubmodule (DeltaAll S DelL), v ∈ S.wt ν →
      (l : O) ^ (e + padicValInt l (LD.Dn (Fintype.card P) w n lam2)) • v ∈ DeltaAll S DelL ∧
        (l : O) ^ (e + padicValInt l (LD.Dn (Fintype.card P) w n lam2)) • v ∈ S.wt ν

def ColumnsInstance : Prop :=
  (⨆ tau, PathSpace ℚ (P := Unit) (fun _ _ : Fin 2 => (0 : Module.End ℚ ℚ)) 2 (fun _ => 0) tau) = ⊤ ∧
    (∃ _b : Fin 2, ∃ j < (1 : ℕ), Fintype.card Unit < LD.colLen (fun _ : Fin 2 => 0) (fun _ => 1) j) ∧
    (∃ z ∈ PathSpace ℚ (P := Unit) (fun _ _ : Fin 2 => (0 : Module.End ℚ ℚ)) 2 (fun _ => 0) (fun _ => 1),
      z ≠ 0 ∧ toSym ℚ z = 0) ∧
    ∃ z ∈ PathSpace ℚ (P := Unit) (fun _ _ : Fin 2 => (0 : Module.End ℚ ℚ)) 2 (fun _ => 0) ![2, 0], toSym ℚ z ≠ 0

def ColumnsRealOfPieriReal : Prop := LR.PieriReal → LR.ColumnsReal

def LemmaDGradedOfPieriReal : Prop := LR.PieriReal → LD.LemmaDGraded

end Formalism.CohomologicalDescent.ColumnMinorsFromPieri
end

-- bundled from Formalism.PieriBlockIdeals.StatementLPR
section
open MvPolynomial

namespace Formalism.CohomologicalDescent.LPR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample Formalism.CohomologicalDescent.LP Formalism.CohomologicalDescent.LR

def DiagTransfer : Prop :=
  ∀ (K M A : Type) [Field K] [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A] (i : M →ₗ[K] A)
    (g : Module.End K M) (f : Module.End K A), Function.Injective i → (∀ x, i (g x) = f (i x)) →
    (⨆ μ : K, Module.End.eigenspace f μ) = ⊤ → (⨆ μ : K, Module.End.eigenspace g μ) = ⊤

def IrredGen : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (T : Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N), FormMod T B → ∀ h : N, h ≠ 0 →
    (∀ Z : Submodule K N, Stab T Z → Z ≠ ⊥ → h ∈ Z) → ∀ S : Submodule K N, Stab T S → h ∈ S → S = ⊤

def EulerDiag : Prop :=
  ∀ (r n : ℕ) (a : Fin r), (⨆ μ : ℚ, Module.End.eigenspace (der r n a a : Module.End ℚ (MvPolynomial (Fin r × Fin n) ℚ)) μ) = ⊤

def RealFinite : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ), FiniteDimensional ℚ ↥(dualWeyl ℚ r n ν)

def RealFormMod : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ),
    FormMod (rationalBlockModuleSetting p q w lam2).EW ((formB p q w lam2).restrict (rationalBlockModuleSetting p q w lam2).W)

def RealHW : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ), Antitone lam2 → (∀ b, lam2 b ≤ w) → ∀ h : (rationalBlockModuleSetting p q w lam2).W,
    ((h : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = hw ℚ le_rfl (LD.blockWt p q w lam2) →
    h ≠ 0 ∧ IsHW (rationalBlockModuleSetting p q w lam2).EW (fun b => (lam2 b : ℚ)) h

def RealGen : Prop :=
  ∀ (p q w : ℕ) (lam2 : Fin q → ℕ), Antitone lam2 → (∀ b, lam2 b ≤ w) →
    ∀ S : Submodule ℚ (rationalBlockModuleSetting p q w lam2).W, Stab (rationalBlockModuleSetting p q w lam2).EW S →
      (∀ v, IsHW (rationalBlockModuleSetting p q w lam2).EW (fun b => (lam2 b : ℚ)) v → v ∈ S) → S = ⊤

end Formalism.CohomologicalDescent.LPR
end

