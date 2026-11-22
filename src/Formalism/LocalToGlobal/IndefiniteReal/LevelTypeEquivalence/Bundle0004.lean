import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0002
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev cED (D : D7) : AE D ≃L[AF D.host.F] (Fin (PHeisFC.nE D) → AF D.host.F) := PHeisFC.cE D.host.F D.host.E

def eInf (D : D7) : AF D.host.F := pairA D.host.F 1 0

def eFin (D : D7) : AF D.host.F := pairA D.host.F 0 1

def cEf (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) ≃ₗ[Af D.host.F] (Fin (PHeisFC.nE D) → Af D.host.F) :=
  (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun

def cEi (D : D7) : (Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₗ[Ainf D.host.F] (Fin (PHeisFC.nE D) → Ainf D.host.F) :=
  (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun

theorem cEf_finPart (x : AE D) : cEf D (finPart D x) = fun a => (cED D x a).2 := by
  induction x using TensorProduct.induction_on with
  | zero => funext a; simp <;> rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]; funext a; simp <;> rfl
  | tmul a e =>
    funext i
    simp [finPart, cEf, cED, PHeisFC.cE, PHeisFC.bA, Algebra.TensorProduct.basis_repr_tmul]
    rfl

theorem cEi_infPart (x : AE D) : cEi D (infPart D x) = fun a => (cED D x a).1 := by
  induction x using TensorProduct.induction_on with
  | zero => funext a; simp <;> rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]; funext a; simp <;> rfl
  | tmul a e =>
    funext i
    simp [infPart, cEi, cED, PHeisFC.cE, PHeisFC.bA, Algebra.TensorProduct.basis_repr_tmul]
    rfl

theorem finPart_eq_zero_iff (x : AE D) : finPart D x = 0 ↔ ∀ a, (cED D x a).2 = 0 := by
  rw [← (cEf D).map_eq_zero_iff (x := finPart D x), cEf_finPart]
  constructor
  · intro h a
    exact congrFun h a
  · intro h
    funext a
    exact h a

theorem infPart_eq_zero_iff (x : AE D) : infPart D x = 0 ↔ ∀ a, (cED D x a).1 = 0 := by
  rw [← (cEi D).map_eq_zero_iff (x := infPart D x), cEi_infPart]
  constructor
  · intro h a
    exact congrFun h a
  · intro h
    funext a
    exact h a

theorem finPart_eq_zero_iff_smul (x : AE D) : finPart D x = 0 ↔ eInf D • x = x := by
  rw [finPart_eq_zero_iff, ← (cED D).injective.eq_iff, map_smul]
  constructor
  · intro h
    funext a
    show eInf D * cED D x a = cED D x a
    exact Prod.ext (show 1 * (cED D x a).1 = (cED D x a).1 from one_mul _)
      (show 0 * (cED D x a).2 = (cED D x a).2 by rw [h a, zero_mul])
  · intro h a
    have h2 : 0 * (cED D x a).2 = (cED D x a).2 := congrArg Prod.snd (congrFun h a)
    rw [zero_mul] at h2
    exact h2.symm

theorem infPart_eq_zero_iff_smul (x : AE D) : infPart D x = 0 ↔ eFin D • x = x := by
  rw [infPart_eq_zero_iff, ← (cED D).injective.eq_iff, map_smul]
  constructor
  · intro h
    funext a
    show eFin D * cED D x a = cED D x a
    exact Prod.ext (show 0 * (cED D x a).1 = (cED D x a).1 by rw [h a, zero_mul])
      (show 1 * (cED D x a).2 = (cED D x a).2 from one_mul _)
  · intro h a
    have h2 : 0 * (cED D x a).1 = (cED D x a).1 := congrArg Prod.fst (congrFun h a)
    rw [zero_mul] at h2
    exact h2.symm

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaGrowthRatNorm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ThetaGrowthNorm (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau → 0 < S.rank → 0 < T.rank →
      ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S × GA D T), IsCompact K →
        ∃ (N : ℕ) (C : ℝ), ∀ k ∈ K, ∀ a ∈ GinfC S, ∀ b ∈ GinfC T,
          ‖thetaKO om (a * k.1) (b * k.2) f‖ ≤ C * (normInf θ S a * normInf θ T b) ^ N

def ThetaGrowthRatNorm (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau → 0 < S.rank →
      ∀ f, IsThetaFunO ψ S T f → ∀ (K : Set (GA D S)) (K' : Set (GA D T)), IsCompact K → IsCompact K' →
        ∃ (N : ℕ) (C : ℝ), ∀ k ∈ K, ∀ a ∈ GinfC S, ∀ γ ∈ GQ T, ∀ c ∈ K',
          ‖thetaKO om (a * k) (γ * c) f‖ ≤ C * normInf θ S a ^ N

def ThetaModGrowthL (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau → 0 < S.rank →
      ∀ f, IsThetaFunO ψ S T f → ∀ (h : GA D T) (x : GA D S), ∃ (C : ℝ) (N : ℕ), ∀ g ∈ GinfC S,
        ‖thetaKO om (x * g) h f‖ ≤ C * normInf θ S g ^ N

def ThetaModGrowthR (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau → 0 < T.rank →
      ∀ f, IsThetaFunO ψ S T f → ∀ (g : GA D S) (x : GA D T), ∃ (C : ℝ) (N : ℕ), ∀ h ∈ GinfC T,
        ‖thetaKO om g (x * h) f‖ ≤ C * normInf θ T h ^ N

def DefCocompact (T : HSp D) : Prop :=
  ∃ K' : Set (GA D T), IsCompact K' ∧ ∀ h : GA D T, ∃ γ ∈ GQ T, ∃ k ∈ K', h = γ * k

def DefCocompactAll (D : D7) : Prop :=
  ∀ T : HSp D, Formalism.UG.IsTotDef D.sp.cm.sig T.gram → DefCocompact T

def ThetaGrowthDef (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau → 0 < S.rank → DefCocompact T →
      ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S), IsCompact K →
        ∃ (N : ℕ) (C : ℝ), ∀ k ∈ K, ∀ a ∈ GinfC S, ∀ h : GA D T,
          ‖thetaKO om (a * k) h f‖ ≤ C * normInf θ S a ^ N

end Formalism.IndefR.Eqv

end
end

