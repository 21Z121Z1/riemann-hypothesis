import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.Bundle0001
import Formalism.PeriodIntegrals.Bundle0022

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealKVCompatU
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Links
  Formalism.IndefR.WeilFull Matrix

namespace Formalism.IndefR.Fock.Exist

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def RealKVCompat (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    {S' : D.what₂.Tau → SPar} (M : DSModel W S') (c : CoefA V) (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (Δ : PolF D W.rank V.rank) : Prop :=
  Δ ≠ 0 ∧ ∀ ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilFull ψ V W χV χW ω →
    ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → f ≠ 0 → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (cart M τ)) f) →
      ∃ io, IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f) Δ io

def KVWeight (N p n : ℕ) (κ : ℚ) (Λ : Fin N → ℝ) : Prop :=
  p ≤ N ∧ ∃ ap am : ℕ → ℕ, Antitone ap ∧ Antitone am ∧ (∀ i, p ≤ i → ap i = 0) ∧ (∀ b, N - p ≤ b → am b = 0) ∧
    ((Finset.range p).filter (fun i => ap i ≠ 0)).card + ((Finset.range (N - p)).filter (fun b => am b ≠ 0)).card ≤ n ∧
    ∀ a : Fin N, Λ a =
      if (a : ℕ) < p then (ap a : ℝ) + (n : ℝ) / 2 + (κ : ℝ)
      else -(am (N - 1 - a) : ℝ) - (n : ℝ) / 2 + (κ : ℝ)

def KVWeightCpt (n p q : ℕ) (κ : ℚ) (lam : Fin n → ℝ) : Prop :=
  ∃ ap am : ℕ → ℕ, Antitone ap ∧ Antitone am ∧ (∀ i, p ≤ i → ap i = 0) ∧ (∀ b, q ≤ b → am b = 0) ∧
    ((Finset.range p).filter (fun i => ap i ≠ 0)).card + ((Finset.range q).filter (fun b => am b ≠ 0)).card ≤ n ∧
    ∀ a : Fin n, lam a =
      (if (a : ℕ) < p then (ap a : ℝ) else 0) - (if n - q ≤ (a : ℕ) then (am (n - 1 - a) : ℝ) else 0) + (κ : ℝ)

def RealKVLoc (W : HSp D) {S' : D.what₂.Tau → SPar} (M : DSModel W S') (p : D.what₂.Tau → ℕ) (nV : ℕ)
    (αV : D.what₂.Tau → ℚ) : Prop :=
  ∀ τ, (∀ a, M.ε τ a = decide ((a : ℕ) < p τ)) ∧ KVWeight W.rank (p τ) nV (αV τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ))

def RealKVCompatU (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (αV αW : D.what₂.Tau → ℚ)
    {S' : D.what₂.Tau → SPar} (M : DSModel W S') (c : CoefA V) (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (Δ : PolF D W.rank V.rank) : Prop :=
  Δ ≠ 0 ∧ ∃ io, ∀ χV χW : (AE D)ˣ →* Circle, (∀ τ, HasInfExp D χV τ (αV τ)) → (∀ τ, HasInfExp D χW τ (αW τ)) →
    ∀ ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilFull ψ V W χV χW ω →
      ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → f ≠ 0 → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (cart M τ)) f) →
        IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f) Δ io

end Formalism.IndefR.Fock.Exist

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FockTheta.SquareNormIntegralNonneg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix MeasureTheory

namespace Formalism.IndefR.Fock.Delta

open Formalism.IndefR.Fock.Sk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def factProd {D : D7} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) : ℝ :=
  ∏ τ, ((∏ i ∈ Finset.range (p τ), ((ap τ i).factorial : ℝ)) * ∏ i ∈ Finset.range (q τ), ((am τ i).factorial : ℝ))

def FockDeltaLow (D : D7) : Prop :=
  ∀ (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ),
    (∀ τ, p τ + q τ ≤ m) → (∀ τ, p τ ≤ n ∧ q τ ≤ n) → (∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) →
    (∀ τ i, p τ ≤ i → ap τ i = 0) → (∀ τ i, q τ ≤ i → am τ i = 0) →
      factProd p q ap am ≤ (Formalism.REAL.fockF (delta (D := D) (m := m) (n := n) p q ap am) (delta p q ap am)).re

def NormDeltaLow (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ),
    PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
        ∀ (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ),
          (∀ τ, p τ + q τ ≤ T.rank) → (∀ τ, p τ ≤ S.rank ∧ q τ ≤ S.rank) → (∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) →
          (∀ τ i, p τ ≤ i → ap τ i = 0) → (∀ τ i, q τ ≤ i → am τ i = 0) →
            factProd p q ap am * nrm2 μ 𝓕 f ≤
              nrm2 μ 𝓕 (fockVec (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT (delta p q ap am) f)

end Formalism.IndefR.Fock.Delta

end
end

