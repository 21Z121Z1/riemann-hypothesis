import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.PeriodIntegrals.Bundle0027
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.SchurOrthogonalityAlt
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def SobOrbitDense (M : DSModel V S) : Prop :=
  ∀ τ (v : M.H τ), v ∈ M.sm τ → v ≠ 0 → ∀ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ →
    (∀ g : Gt V τ, ℓ (M.rep τ (gm g) v) = 0) → ∀ w ∈ M.sm τ, ℓ w = 0

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

open Classical in

structure EqCont (M : DSModel V S) (T : MMap M) : Prop where
  equiv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)
  cont : ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

variable {θ}

open Classical in

theorem eqCont_of_mem {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (hT : T ∈ Mult θ M J χ) : EqCont θ M T := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact ⟨hT.equiv, hT.cont⟩
  | zero =>
    refine ⟨fun τ g _ v w _ => ?_, fun τ v x => ⟨0, sobCont_zero, fun w => ?_⟩⟩
    · rw [MultilinearMap.zero_apply, MultilinearMap.zero_apply]; rfl
    · simp
  | add T T' _ _ h h' =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.add_apply, MultilinearMap.add_apply, h.equiv τ g hg v w hw, h'.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      obtain ⟨ℓ', hℓ', e'⟩ := h'.cont τ v x
      exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by
        rw [LinearMap.add_apply, e, e', MultilinearMap.add_apply, Pi.add_apply]⟩
  | smul a T _ h =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.smul_apply, MultilinearMap.smul_apply, h.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      exact ⟨a • ℓ, sobCont_smul a hℓ, fun w => by
        rw [LinearMap.smul_apply, e, MultilinearMap.smul_apply, Pi.smul_apply]⟩

open Classical in

theorem place_zero {M : DSModel V S} (hS : SobOrbitDense M) {T : MMap M} (hT : EqCont θ M T) (τ : D.what₂.Tau)
    (v : M.Vec) (hv : (v τ : M.H τ) ≠ 0) (h0 : T v = 0) (w : M.sm τ) : T (Function.update v τ w) = 0 := by
  funext x
  obtain ⟨ℓ, hℓ, e⟩ := hT.cont τ v x
  have horb : ∀ g : Gt V τ, ℓ (M.rep τ (gm g) (v τ : M.H τ)) = 0 := by
    intro g
    have hm : M.rep τ (gm g) (v τ : M.H τ) ∈ M.sm τ := sm_stable M τ g (v τ).2
    have e1 := e ⟨M.rep τ (gm g) (v τ : M.H τ), hm⟩
    rw [hT.equiv τ (gm g) (gm_mem g) v ⟨M.rep τ (gm g) (v τ : M.H τ), hm⟩ rfl, h0] at e1
    exact e1
  have := hS τ (v τ : M.H τ) (v τ).2 hv ℓ hℓ horb (w : M.H τ) w.2
  rw [← e w, this]
  rfl

open Classical in

theorem eq_zero_of_vec {M : DSModel V S} (hS : SobOrbitDense M) {T : MMap M} (hT : EqCont θ M T) (v : M.Vec)
    (hv : ∀ τ, (v τ : M.H τ) ≠ 0) (h0 : T v = 0) : T = 0 := by
  have key : ∀ s : Finset D.what₂.Tau, ∀ u : M.Vec, T (s.piecewise u v) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro u; simpa using h0
    | insert a s ha ih =>
      intro u
      have hva : ((s.piecewise u v) a : M.H a) ≠ 0 := by
        rw [Finset.piecewise_eq_of_notMem _ _ _ ha]; exact hv a
      have := place_zero hS hT a (s.piecewise u v) hva (ih u) (u a)
      rw [Finset.piecewise_insert]
      exact this
  ext u
  have := key Finset.univ u
  rw [Finset.piecewise_univ] at this
  rw [this]
  rfl

variable (θ) in
open Classical in

theorem resInjVec (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (hS : SobOrbitDense M) :
    ResInjVec M (Mult θ M J χ) := by
  intro T hT v hv h0
  exact eq_zero_of_vec hS (eqCont_of_mem hT) v hv h0

end Formalism.IndefR.AutomorphicEvaluation

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.PublishedAut
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.PublishedAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FinCovolGA (D : D7) : Prop :=
  ∀ V : HSp D, V.SigOK → ∀ (μ : Measure (GA D V)), μ.IsHaarMeasure → ∀ 𝓕 : Set (GA D V),
    IsFundamentalDomain (GQ V) 𝓕 μ → μ 𝓕 ≠ ⊤

def ClassFinGA (D : D7) : Prop :=
  ∀ V : HSp D, V.SigOK → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) →
    ∃ S : Finset (GA D V), ∀ x : GA D V, ∃ γ ∈ GQ V, ∃ s ∈ S, ∃ r ∈ GinfC V, ∃ u ∈ U, x = γ * s * r * u

def StepFinCovolGA (D : D7) : Prop := PI.AdelFinVol.AdelFinVol → FinCovolGA D

def StepClassFinGA (D : D7) : Prop := PI.AdelClassFin.AdelClassFin → ClassFinGA D

def StepDSExists (D : D7) : Prop :=
  Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExists → ∀ (V : HSp D) (S : D.what₂.Tau → SPar),
    Formalism.IndefR.Mult.DSExists V S

def StrongApproxSU (D : D7) : Prop :=
  ∀ V : HSp D, 2 ≤ V.rank → ∀ e : AE D, IsSplitIdem D e → ∀ g : GA D V, (mt V g).det = 1 →
    g ∈ closure {x : GA D V | ∃ γ ∈ GQ V, (mt V γ).det = 1 ∧
      ∃ h : GA D V, (mt V h).det = 1 ∧ SuppAt e V h ∧ x = γ * h}

variable {D : D7}

def opPoly {X : Type} (A : (X → ℂ) → (X → ℂ)) (P : Polynomial ℂ) (φ : X → ℂ) : X → ℂ :=
  ∑ j ∈ P.support, P.coeff j • (A^[j] φ)

def AtTauExists (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  ∀ τ (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) → ∃ x, IsAtTau θ V τ g x

theorem atTauExists_of {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) (V : HSp D) :
    AtTauExists θ V := by
  intro τ g hg
  obtain ⟨x, hx, -⟩ := Formalism.IndefR.Eqv.atTauExUnique_holds (D := D) θ hθ V τ g hg
  exact ⟨x, hx⟩

def KtauS (V : HSp D) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) :
    Set (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  {k | k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ k * s τ = s τ * k}

def HCFiniteness (D : D7) : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (V : HSp D), AtTauExists θ V → ∀ (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ τ, Formalism.IndefR.Datum.IsCartanInv (gramAt D V τ) (s τ)) →
  ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) →
  ∀ (p : D.what₂.Tau → ℕ → Polynomial ℂ), (∀ τ j, p τ j ≠ 0) →
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → Matrix ι ι ℂ),
    FiniteDimensional ℂ (Submodule.span ℂ {Φ : GA D V → (ι → ℂ) |
      (∀ i, IsAutFunSm θ V fun g => Φ g i) ∧
      (∀ τ, ∀ k ∈ KtauS V s τ, ∀ g, Φ (g * atTau θ V τ k) = (ρ τ k).mulVec (Φ g)) ∧
      (∀ u ∈ U, u ∈ GfC V → ∀ g, Φ (g * u) = Φ g) ∧
      ∀ τ, ∀ j < V.rank, ∀ i, opPoly (gelf θ V τ j) (p τ j) (fun g => Φ g i) = 0})

def KTypeSm {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) : Prop :=
  ∀ τ, ∃ W : Submodule ℂ (M.H τ), FiniteDimensional ℂ W ∧ W ≠ ⊥ ∧ Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) W ∧
    ∀ w ∈ W, w ∈ M.sm τ

def GelfScalar (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) : Prop :=
  ∀ τ (j : ℕ), ∃ c : ℂ, ∀ T ∈ Formalism.IndefR.Mult.Mult θ M J χ, ∀ v : M.Vec, gelf θ V τ j (T v) = c • T v

def StepHCFinite (D : D7) : Prop :=
  HCFiniteness D → ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    KTypeSm M → GelfScalar θ M J χ →
    Formalism.IndefR.AutomorphicEvaluation.ResInjVec M (Formalism.IndefR.Mult.Mult θ M J χ) → Formalism.IndefR.Mult.HCFinite θ M J χ

end Formalism.IndefR.PublishedAut

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SEEofApply
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict
open scoped TensorProduct

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

def vOf {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
    {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {c : ℝ} (h : EvalTie M μ 𝓕 E X G ι c) : M.Vec := h.choose

def jOf {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
    {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {c : ℝ} (h : EvalTie M μ 𝓕 E X G ι c) : E ≃ₗ[ℂ] EEC X G :=
  h.choose_spec.2.choose

theorem jOf_spec {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
    {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {c : ℝ} (h : EvalTie M μ 𝓕 E X G ι c) (T : E) :
    (((jOf h T : EEC X G) : L2X X) =ᵐ[muX X] fun x => ev M (vOf h) (T : MMap M) (ι.symm x)) ∧
      ‖((jOf h T : EEC X G) : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re :=
  h.choose_spec.2.choose_spec T

def sEEof {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
    {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {c : ℝ} (h : EvalTie M μ 𝓕 E X G ι c) :
    E →ₗ⋆[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X :=
  (conjHH X G).toLinearMap.comp (jOf h).toLinearMap

end Formalism.IndefR.AutomorphicEvaluation

end
end

