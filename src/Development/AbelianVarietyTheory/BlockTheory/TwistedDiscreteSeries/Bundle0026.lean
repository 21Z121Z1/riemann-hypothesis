import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open Formalism.IndefR.Lift (liftInt)
open GlobalTheory.Cusp (constTerm frameFlag)
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def adel {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin m) (Fin n) (AE D) := x.map (incA D)

abbrev ct {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x

def IsWittStep (B B' : HSp D) (t : ℕ) (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E) : Prop :=
  B'.rank + 2 * t = B.rank ∧ HSpace.IsIsomEmb B' B ι ∧ IsIsoSub B C ∧ ct (frameMat B B' ι) * B.gram * C = 0

theorem isWittLower_iff (B B' : HSp D) (t : ℕ) : IsWittLower B B' t ↔ ∃ ι C, IsWittStep B B' t ι C :=
  ⟨fun ⟨h, ι, h1, C, h2, h3⟩ => ⟨ι, C, h, h1, h2, h3⟩, fun ⟨ι, C, h, h1, h2, h3⟩ => ⟨h, ι, h1, C, h2, h3⟩⟩

theorem exists_isWittStep_iff (B : HSp D) (t : ℕ) :
    (∃ B' ι C, IsWittStep B B' t ι C ∧ B'.SigOK) ↔ t ≤ GlobalTheory.Cusp.wittIndex B := by
  rw [← GlobalTheory.Cusp.exists_isWittLower_iff]
  exact ⟨fun ⟨B', ι, C, h, h'⟩ => ⟨B', (isWittLower_iff _ _ _).2 ⟨ι, C, h⟩, h'⟩,
    fun ⟨B', h, h'⟩ => let ⟨ι, C, h⟩ := (isWittLower_iff _ _ _).1 h; ⟨B', ι, C, h, h'⟩⟩

theorem IsWittStep.isIsoFrame {B B' : HSp D} {t : ℕ} {ι : B'.V →ₗ[D.host.E] B.V}
    {C : Matrix (Fin B.rank) (Fin t) D.host.E} (h : IsWittStep B B' t ι C) (ht : 1 ≤ t) : IsIsoFrame B C :=
  ⟨ht, h.2.2.1.1, h.2.2.1.2⟩

def IsLeviElt (B B' : HSp D) {t : ℕ} (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E)
    (a : GL (Fin t) (AE D)) (h' : GA D B') (m : GA D B) : Prop :=
  HMul.hMul (Formalism.L2.Theta.mt B m) (adel C) = HMul.hMul (adel C) a.val ∧
    HMul.hMul (Formalism.L2.Theta.mt B m) (adel (frameMat B B' ι)) =
      HMul.hMul (adel (frameMat B B' ι)) (Formalism.L2.Theta.mt B' h')

def IsAutCharGL (t : ℕ) (μ : GL (Fin t) (AE D) →* Circle) : Prop :=
  Continuous μ ∧ ∀ a : GL (Fin t) D.host.E, μ (Matrix.GeneralLinearGroup.map (incA D) a) = 1

def IsAutCharU (V : HSp D) (ξ : GA D V →* Circle) : Prop := Continuous ξ ∧ ∀ γ ∈ GQ V, ξ γ = 1

def detPow {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) : ℝ :=
  (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((n : ℝ) / 2)

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

def IsRapidCusp (A : HSp D) (f : GA D A → ℂ) : Prop := GlobalTheory.Grow.RapidDec A f ∧ IsCuspFun A f

def IsQuotMeas (A : HSp D) (ν : Measure (GA D A)) (𝓕 : Set (GA D A)) : Prop :=
  ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ A) 𝓕 ν

abbrev Rep (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

def IsWeilRep (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∃ χS χT : (AE D)ˣ →* Circle, IsWeilDatumO ψ S T χS χT om

def HasConstS (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (om : Rep S T) (τ : D.what₂.Tau) (κ : ℝ) :
    Prop :=
  ∀ (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
    IsCartanInv (gramAt D S τ) sS → IsCartanInv (gramAt D T τ) sT →
    ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f →
    ∀ X ∈ lieAt S τ, X * sS = sS * X → ∀ g, IsAtTau θ S τ (NormedSpace.exp X) g →
      om (g, 1) f = Complex.exp (-(sT.trace / 2 * (sS * X).trace + (κ : ℂ) * X.trace)) • f

def HasConstT (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (om : Rep S T) (τ : D.what₂.Tau) (κ : ℝ) :
    Prop :=
  ∀ (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
    IsCartanInv (gramAt D S τ) sS → IsCartanInv (gramAt D T τ) sT →
    ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f →
    ∀ X ∈ lieAt T τ, X * sT = sT * X → ∀ h, IsAtTau θ T τ (NormedSpace.exp X) h →
      om (1, h) f = Complex.exp (sS.trace / 2 * (sT * X).trace + (κ : ℂ) * X.trace) • f

section Target

variable (ψ : AddChar (AF D.host.F) ℂ) (S T T' : HSp D) {t : ℕ} (ι : T'.V →ₗ[D.host.E] T.V)
  (C : Matrix (Fin T.rank) (Fin t) D.host.E)

def resT (μ : Measure (Mx D t S.rank)) (𝓖 : Set (Mx D t S.rank)) (φ : WO S T → ℂ) : WO S T' → ℂ :=
  fun w' => ∫ y in 𝓖, φ (adel C * (y : Matrix (Fin t) (Fin S.rank) (AE D)) +
    adel (frameMat T T' ι) * (w' : Matrix (Fin T'.rank) (Fin S.rank) (AE D))) ∂μ

def CompatT (om : Rep S T) (om' : Rep S T') : Prop :=
  ∀ μ 𝓖, IsCovolOne (ratMx D t S.rank) μ 𝓖 → ∀ (g : GA D S) φ, IsThetaFunO ψ S T φ →
    resT S T T' ι C μ 𝓖 (om (g, 1) φ) = om' (g, 1) (resT S T T' ι C μ 𝓖 φ)

def liftT {S T : HSp D} (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (om : Rep S T) (f : GA D S → ℂ) (φ : WO S T → ℂ) :
    GA D T → ℂ :=
  liftInt ν 𝓕 (fun h g φ => thetaKO om g h φ) φ f

def ThetaT {S T : HSp D} (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (om : Rep S T) (π : Submodule ℂ (GA D S → ℂ)) :
    Submodule ℂ (GA D T → ℂ) :=
  Submodule.span ℂ {F | ∃ f ∈ π, ∃ φ, IsThetaFunO ψ S T φ ∧ F = liftT ν 𝓕 om f φ}

def IsTowerT {S T : HSp D} (om : Rep S T) (r : ℕ) (Y : ℕ → HSp D) (ι : ∀ i, (Y i).V →ₗ[D.host.E] T.V)
    (C : ∀ i, Matrix (Fin T.rank) (Fin i) D.host.E) (omY : ∀ i, Rep S (Y i)) : Prop :=
  ∀ i, 1 ≤ i → i ≤ r → IsWittStep T (Y i) i (ι i) (C i) ∧ IsWeilRep ψ S (Y i) (omY i) ∧
    CompatT ψ S T (Y i) (ι i) (C i) om (omY i)

end Target

def CompatExistsT (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  (∀ θ : InfFam D, IsInfFam θ → ∀ τ, ∃ κ, HasConstS ψ θ S T om τ κ) ∧
    ∀ (T' : HSp D) (t : ℕ) ι (C : Matrix (Fin T.rank) (Fin t) D.host.E), 1 ≤ t → IsWittStep T T' t ι C →
      ∃ om' : Rep S T', IsWeilRep ψ S T' om' ∧ CompatT ψ S T T' ι C om om' ∧
        ∀ θ : InfFam D, IsInfFam θ → ∀ τ κ, HasConstS ψ θ S T om τ κ ↔ HasConstS ψ θ S T' om' τ κ

def LiftConvT (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ ν 𝓕, IsQuotMeas S ν 𝓕 → ∀ f, IsRapidCusp S f → ∀ φ, IsThetaFunO ψ S T φ →
    (∀ h, IntegrableOn (fun g => thetaKO om g h φ * f g) 𝓕 ν) ∧ Continuous (liftT ν 𝓕 om f φ) ∧
      ∀ γ ∈ GQ T, ∀ h, liftT ν 𝓕 om f φ (γ * h) = liftT ν 𝓕 om f φ h

def ConstTermT (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ (T' : HSp D) (t : ℕ) ι (C : Matrix (Fin T.rank) (Fin t) D.host.E) (ht : 1 ≤ t) (hs : IsWittStep T T' t ι C)
    (om' : Rep S T'), IsWeilRep ψ S T' om' → CompatT ψ S T T' ι C om om' →
    ∃ (μa : GL (Fin t) (AE D) →* Circle) (ξ : GA D T' →* Circle), IsAutCharGL t μa ∧ IsAutCharU T' ξ ∧
      ∀ μ 𝓖, IsCovolOne (ratMx D t S.rank) μ 𝓖 →
        (∀ φ', IsThetaFunO ψ S T' φ' ↔ ∃ φ, IsThetaFunO ψ S T φ ∧ φ' = resT S T T' ι C μ 𝓖 φ) ∧
        ∀ ν 𝓕, IsQuotMeas S ν 𝓕 → ∀ f, IsRapidCusp S f → ∀ φ, IsThetaFunO ψ S T φ →
          (∀ h, constTerm (frameFlag (hs.isIsoFrame ht)) (liftT ν 𝓕 om f φ) h =
            liftT ν 𝓕 om' f (resT S T T' ι C μ 𝓖 (om (1, h) φ)) 1) ∧
          ∀ a h' m, IsLeviElt T T' ι C a h' m →
            constTerm (frameFlag (hs.isIsoFrame ht)) (liftT ν 𝓕 om f φ) m =
              (μa a : ℂ) * (detPow a S.rank : ℂ) * (ξ h' : ℂ) * liftT ν 𝓕 om' f (resT S T T' ι C μ 𝓖 φ) h'

def CuspIffT (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ Y ι C omY, IsTowerT ψ om (GlobalTheory.Cusp.wittIndex T) Y ι C omY →
    ∀ ν 𝓕, IsQuotMeas S ν 𝓕 → ∀ π : Submodule ℂ (GA D S → ℂ), (∀ f ∈ π, IsRapidCusp S f) →
      ((∀ F ∈ ThetaT ψ ν 𝓕 om π, IsCuspFun T F) ↔
        ∀ i, 1 ≤ i → i ≤ GlobalTheory.Cusp.wittIndex T → ThetaT ψ ν 𝓕 (omY i) π = ⊥)

section Source

variable (ψ : AddChar (AF D.host.F) ℂ) (S S' T : HSp D) {t : ℕ} (ι : S'.V →ₗ[D.host.E] S.V)
  (C : Matrix (Fin S.rank) (Fin t) D.host.E)

def resS (μ : Measure (Mx D T.rank t)) (𝓖 : Set (Mx D T.rank t)) (φ : WO S T → ℂ) : WO S' T → ℂ :=
  fun w' => ∫ y in 𝓖, φ ((y : Matrix (Fin T.rank) (Fin t) (AE D)) * adel (ct C * S.gram) +
    (w' : Matrix (Fin T.rank) (Fin S'.rank) (AE D)) * adel (S'.gram⁻¹ * ct (frameMat S S' ι) * S.gram)) ∂μ

def CompatS (om : Rep S T) (om' : Rep S' T) : Prop :=
  ∀ μ 𝓖, IsCovolOne (ratMx D T.rank t) μ 𝓖 → ∀ (h : GA D T) φ, IsThetaFunO ψ S T φ →
    resS S S' T ι C μ 𝓖 (om (1, h) φ) = om' (1, h) (resS S S' T ι C μ 𝓖 φ)

def liftS {S T : HSp D} (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (om : Rep S T) (f : GA D T → ℂ) (φ : WO S T → ℂ) :
    GA D S → ℂ :=
  liftInt ν 𝓕 (thetaKO om) φ f

def ThetaS {S T : HSp D} (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (om : Rep S T) (π : Submodule ℂ (GA D T → ℂ)) :
    Submodule ℂ (GA D S → ℂ) :=
  Submodule.span ℂ {F | ∃ f ∈ π, ∃ φ, IsThetaFunO ψ S T φ ∧ F = liftS ν 𝓕 om f φ}

def IsTowerS {S T : HSp D} (om : Rep S T) (r : ℕ) (Y : ℕ → HSp D) (ι : ∀ i, (Y i).V →ₗ[D.host.E] S.V)
    (C : ∀ i, Matrix (Fin S.rank) (Fin i) D.host.E) (omY : ∀ i, Rep (Y i) T) : Prop :=
  ∀ i, 1 ≤ i → i ≤ r → IsWittStep S (Y i) i (ι i) (C i) ∧ IsWeilRep ψ (Y i) T (omY i) ∧
    CompatS ψ S (Y i) T (ι i) (C i) om (omY i)

end Source

def CompatExistsS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  (∀ θ : InfFam D, IsInfFam θ → ∀ τ, ∃ κ, HasConstT ψ θ S T om τ κ) ∧
    ∀ (S' : HSp D) (t : ℕ) ι (C : Matrix (Fin S.rank) (Fin t) D.host.E), 1 ≤ t → IsWittStep S S' t ι C →
      ∃ om' : Rep S' T, IsWeilRep ψ S' T om' ∧ CompatS ψ S S' T ι C om om' ∧
        ∀ θ : InfFam D, IsInfFam θ → ∀ τ κ, HasConstT ψ θ S T om τ κ ↔ HasConstT ψ θ S' T om' τ κ

def LiftConvS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ ν 𝓕, IsQuotMeas T ν 𝓕 → ∀ f, IsRapidCusp T f → ∀ φ, IsThetaFunO ψ S T φ →
    (∀ g, IntegrableOn (fun h => thetaKO om g h φ * f h) 𝓕 ν) ∧ Continuous (liftS ν 𝓕 om f φ) ∧
      ∀ γ ∈ GQ S, ∀ g, liftS ν 𝓕 om f φ (γ * g) = liftS ν 𝓕 om f φ g

def ConstTermS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ (S' : HSp D) (t : ℕ) ι (C : Matrix (Fin S.rank) (Fin t) D.host.E) (ht : 1 ≤ t) (hs : IsWittStep S S' t ι C)
    (om' : Rep S' T), IsWeilRep ψ S' T om' → CompatS ψ S S' T ι C om om' →
    ∃ (μa : GL (Fin t) (AE D) →* Circle) (ξ : GA D S' →* Circle), IsAutCharGL t μa ∧ IsAutCharU S' ξ ∧
      ∀ μ 𝓖, IsCovolOne (ratMx D T.rank t) μ 𝓖 →
        (∀ φ', IsThetaFunO ψ S' T φ' ↔ ∃ φ, IsThetaFunO ψ S T φ ∧ φ' = resS S S' T ι C μ 𝓖 φ) ∧
        ∀ ν 𝓕, IsQuotMeas T ν 𝓕 → ∀ f, IsRapidCusp T f → ∀ φ, IsThetaFunO ψ S T φ →
          (∀ g, constTerm (frameFlag (hs.isIsoFrame ht)) (liftS ν 𝓕 om f φ) g =
            liftS ν 𝓕 om' f (resS S S' T ι C μ 𝓖 (om (g, 1) φ)) 1) ∧
          ∀ a g' m, IsLeviElt S S' ι C a g' m →
            constTerm (frameFlag (hs.isIsoFrame ht)) (liftS ν 𝓕 om f φ) m =
              (μa a : ℂ) * (detPow a T.rank : ℂ) * (ξ g' : ℂ) * liftS ν 𝓕 om' f (resS S S' T ι C μ 𝓖 φ) g'

def CuspIffS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ Y ι C omY, IsTowerS ψ om (GlobalTheory.Cusp.wittIndex S) Y ι C omY →
    ∀ ν 𝓕, IsQuotMeas T ν 𝓕 → ∀ π : Submodule ℂ (GA D T → ℂ), (∀ f ∈ π, IsRapidCusp T f) →
      ((∀ F ∈ ThetaS ψ ν 𝓕 om π, IsCuspFun S F) ↔
        ∀ i, 1 ≤ i → i ≤ GlobalTheory.Cusp.wittIndex S → ThetaS ψ ν 𝓕 (omY i) π = ⊥)

def TowerGeneral (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T), IsWeilRep ψ S T om →
    (CompatExistsT ψ S T om ∧ LiftConvT ψ S T om ∧ ConstTermT ψ S T om ∧ CuspIffT ψ S T om) ∧
      CompatExistsS ψ S T om ∧ LiftConvS ψ S T om ∧ ConstTermS ψ S T om ∧ CuspIffS ψ S T om

def TowerAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T), IsWeilRep ψ S T om → IsAniso S →
    CompatExistsT ψ S T om ∧
    (∀ (T' : HSp D) (t : ℕ) ι (C : Matrix (Fin T.rank) (Fin t) D.host.E) (ht : 1 ≤ t) (hs : IsWittStep T T' t ι C)
      (om' : Rep S T'), IsWeilRep ψ S T' om' → CompatT ψ S T T' ι C om om' →
      ∀ μ 𝓖, IsCovolOne (ratMx D t S.rank) μ 𝓖 → ∀ φ, IsThetaFunO ψ S T φ →
        IsThetaFunO ψ S T' (resT S T T' ι C μ 𝓖 φ) ∧
        (∀ g h, constTerm (frameFlag (hs.isIsoFrame ht)) (fun x => thetaKO om g x φ) h =
          thetaKO om' g 1 (resT S T T' ι C μ 𝓖 (om (1, h) φ))) ∧
        ∀ ν 𝓕, IsQuotMeas S ν 𝓕 → ∀ f : GA D S → ℂ, Continuous f → (∀ γ ∈ GQ S, ∀ g, f (γ * g) = f g) →
          ∀ h, constTerm (frameFlag (hs.isIsoFrame ht)) (liftT ν 𝓕 om (star f) φ) h =
            liftT ν 𝓕 om' (star f) (resT S T T' ι C μ 𝓖 (om (1, h) φ)) 1) ∧
    ∀ Y ι C omY, IsTowerT ψ om (GlobalTheory.Cusp.wittIndex T) Y ι C omY →
      ∀ ν 𝓕, IsQuotMeas S ν 𝓕 → ∀ f : GA D S → ℂ, Continuous f → (∀ γ ∈ GQ S, ∀ g, f (γ * g) = f g) →
        (∀ i, 1 ≤ i → i ≤ GlobalTheory.Cusp.wittIndex T → ∀ φ', IsThetaFunO ψ S (Y i) φ' →
          liftT ν 𝓕 (omY i) (star f) φ' = 0) →
        ∀ φ, IsThetaFunO ψ S T φ → IsCuspFun T (liftT ν 𝓕 om (star f) φ)

def TowerProperty (D : D7) : Prop := TowerAniso D ∧ TowerGeneral D

example (D : D7) : ∃ B' ι C, IsWittStep (CuspDecay.Model.plane D) B' 1 ι C ∧ B'.rank = 0 := by
  obtain ⟨B', ι, C, h, -⟩ := (exists_isWittStep_iff (CuspDecay.Model.plane D) 1).2 (GlobalTheory.Cusp.wittIndex_plane D).ge
  have h1 : B'.rank + 2 * 1 = 2 := h.1
  exact ⟨B', ι, C, h, by omega⟩

example (B B' : HSp D) {t : ℕ} (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E) :
    IsLeviElt B B' ι C 1 1 1 := by
  simp [IsLeviElt, Formalism.L2.Theta.mt]

end GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)

def stdParabolic (k : Type) [Field k] (r a : ℕ) : Subgroup (GL (Fin r) k) where
  carrier := {g | ∀ i j : Fin r, j.val < a → a ≤ i.val → (g : Matrix (Fin r) (Fin r) k) i j = 0}
  one_mem' := fun i j hj hi => Matrix.one_apply_ne (by rintro rfl; omega)
  mul_mem' := fun {g h} hg hh i j hj hi => by
    rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < a
    · rw [hg i l hl hi, zero_mul]
    · rw [hh l j hj (not_lt.1 hl), mul_zero]
  inv_mem' := fun {g} hg i j hj hi => by
    have hb : (g : Matrix (Fin r) (Fin r) k).BlockTriangular fun l => if l.val < a then (0 : ℕ) else 1 := by
      intro i j h
      by_cases h1 : j.val < a <;> by_cases h2 : i.val < a <;> simp [h1, h2] at h
      exact hg i j h1 (not_lt.1 h2)
    letI := g.invertible
    have := Matrix.blockTriangular_inv_of_blockTriangular hb
    rw [Matrix.coe_units_inv]
    exact this (by simp [hj, not_lt.2 hi])

def InConjParabolic {k : Type} [Field k] {r : ℕ} (H : Subgroup (GL (Fin r) k)) (a : ℕ) : Prop :=
  ∃ g : GL (Fin r) k, ∀ p ∈ H, g⁻¹ * p * g ∈ stdParabolic k r a

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def parAt {D : D7} {V : HSp D} (𝔉 : IsoFlag V) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) : Subgroup (GL (Fin V.rank) (Fv D.host.F v)) :=
  (PLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))

def ParabolicAtSplitPlaces : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ (T : TypeDataG V) (𝔉 : IsoFlag V), 𝔉.Proper →
    ∃ a : ℕ, 0 < a ∧ 2 * a + 1 ≤ V.rank ∧ ∀ v : T.S,
      InConjParabolic (parAt 𝔉 (T.frame v)) a ∧ InConjParabolic (parAt 𝔉 (T.frame v)) (V.rank - a)

def UnipIntegralsVanish {D : D7} {V : HSp D} (𝔉 : IsoFlag V) (f : GA D V → ℂ) : Prop :=
  ∀ (ν : Measure (NA 𝔉)) [ν.IsHaarMeasure] (x y : GA D V),
    Integrable (fun n : NA 𝔉 => f (x * n * y)) ν ∧ ∫ n : NA 𝔉, f (x * n * y) ∂ν = 0

def TestFnConstTermVanish : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V), HypH (k := fun v : T.S => ResF v.1) T.τ → ∀ (U : AuxiliaryPlaceHermitianSpace V)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) [∀ w, (μa w).IsHaarMeasure]
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) [∀ v, (μf v).IsHaarMeasure]
    (f : GA D V → ℂ), IsTestFnG M T U μa μf f →
    ∀ 𝔉 : IsoFlag V, 𝔉.Proper → UnipIntegralsVanish 𝔉 f ∧ UnipIntegralsVanish 𝔉 (starFn f)

def ParabolicAndConstTerm : Prop := ParabolicAtSplitPlaces ∧ TestFnConstTermVanish

example (k : Type) [Field k] (g : GL (Fin 2) k) :
    g ∈ stdParabolic k 2 1 ↔ (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
  change (∀ i j : Fin 2, _) ↔ _
  simp [Fin.forall_fin_two]

example (k : Type) [Field k] (r a : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical k r a ⊆ stdParabolic k r a := fun u hu i j hj hi => by
  by_contra h
  have := hu i j (by rwa [Matrix.one_apply_ne (by rintro rfl; omega)])
  omega

example {D : D7} {V : HSp D} (𝔉 : IsoFlag V) : ∃ ν : Measure (NA 𝔉), ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩

example {D : D7} {V : HSp D} (𝔉 : IsoFlag V) {φ : GA D V → ℝ} (hc : Continuous φ) (h0 : 0 ≤ φ)
    (h : UnipIntegralsVanish 𝔉 fun g => (φ g : ℂ)) : φ = 0 := funext fun x => by
  obtain ⟨h1, h2⟩ := h Measure.haar x 1
  have hc' : Continuous fun n : NA 𝔉 => φ (x * n * 1) := hc.comp (by fun_prop)
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero,
    integral_eq_zero_iff_of_nonneg (f := fun n : NA 𝔉 => φ (x * n * 1)) (fun n => h0 _) (by simpa using h1.re)] at h2
  simpa using congrFun ((hc'.ae_eq_iff_eq _ continuous_zero).1 h2) 1

end GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TraceKernelDecomposition
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.Mem.Th
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition

section Core

variable {X : Type} [MeasurableSpace X] {ν : Measure X}

def HasRows (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (β : X → Lp ℂ 2 ν) : Prop :=
  ∀ φ : Lp ℂ 2 ν, B φ =ᵐ[ν] fun x => ⟪β x, φ⟫_ℂ

def IsKernelOf (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (K : X → X → ℂ) : Prop :=
  (∀ x, MemLp (K x) 2 ν) ∧ ∀ φ : Lp ℂ 2 ν, T φ =ᵐ[ν] fun x => ∫ z, K x z * φ z ∂ν

def TraceIsDiagonal (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (K : X → X → ℂ) : Prop :=
  IsTraceClass T ∧ Integrable (fun x => K x x) ν ∧ trace T = ∫ x, K x x ∂ν

end Core

def TraceKernelCore : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    [ν.IsOpenPosMeasure] [IsSeparable ν] (n : ℕ) (B C : Fin n → (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (β γ : Fin n → X → Lp ℂ 2 ν),
    (∀ i, IsHilbertSchmidt (B i)) → (∀ i, IsHilbertSchmidt (C i)) →
    (∀ i, Continuous (β i)) → (∀ i, Continuous (γ i)) →
    (∀ i, HasRows (B i) (β i)) → (∀ i, HasRows (ContinuousLinearMap.adjoint (C i)) (γ i)) →
      (∀ i, IsKernelOf (B i ∘L C i) (fun x z => ⟪β i x, γ i z⟫_ℂ) ∧
        TraceIsDiagonal (B i ∘L C i) fun x z => ⟪β i x, γ i z⟫_ℂ) ∧
      ∀ K : X → X → ℂ, Continuous (Function.uncurry K) → IsKernelOf (∑ i, B i ∘L C i) K →
        TraceIsDiagonal (∑ i, B i ∘L C i) K

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsCcInf (θ : InfF D) (V : HSp D) (f : GA D V → ℂ) : Prop :=
  Continuous f ∧ HasCompactSupport f ∧
    (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ g, f (g * k) = f g) ∧
    ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

def MapsIntoCusp (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA D V → ℂ) : Prop :=
  ∀ F : DividedPowerChartLift V μ, RopG V μ f F ∈ L2cusp V μ

def CuspTraceClass (θ : InfF D) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : Prop :=
  ∀ f, IsCcInf θ V f → IsTraceClass (RcuspOp V μ f)

def TraceKernelAt (θ : InfF D) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : Prop :=
  ∀ f, IsCcInf θ V f → MapsIntoCusp V μ f → MapsIntoCusp V μ (starFn f) →
    TraceIsDiagonal (ν := autMeasure V μ) (RopG V μ f) (kernelQ (GQ V) f)

def TraceKernel : Prop :=
  ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    CuspTraceClass θ V μ → TraceKernelAt θ V μ

def TraceKernelUncond : Prop :=
  ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    TraceKernelAt θ V μ

theorem TraceKernel.uncond (h : TraceKernel)
    (hc : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant], CuspTraceClass θ V μ) : TraceKernelUncond :=
  fun D θ hθ V μ _ _ => h D θ hθ V μ (hc D θ hθ V μ)

example (V : HSp D) (f : GA D V → ℂ) (x : GA D V) :
    kernelQ (GQ V) f (mk _ x) (mk _ x) = ∑' γ : GQ V, f (x⁻¹ * γ * x) := kernelQ_mk f x x

theorem oneP_mem_GinfC (θ : InfF D) (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    oneP θ V τ X t ∈ GinfC V := by
  unfold oneP atTau
  split_ifs with h
  exacts [h.choose_spec.1, one_mem _]

theorem isCcInf_indicator (θ : InfF D) (V : HSp D) {K : Subgroup (GA D V)} (ho : IsOpen (K : Set (GA D V)))
    (hc : IsCompact (K : Set (GA D V))) (hK : GinfC V ≤ K) :
    IsCcInf θ V ((K : Set (GA D V)).indicator fun _ => 1) := by
  have hinv : ∀ k ∈ K, ∀ g, (K : Set (GA D V)).indicator (fun _ => (1 : ℂ)) (g * k) =
      (K : Set (GA D V)).indicator (fun _ => (1 : ℂ)) g := fun k hk g => by
    by_cases hg : g ∈ K
    · rw [Set.indicator_of_mem (K.mul_mem hg hk), Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem fun h => hg ((K.mul_mem_cancel_right hk).1 h)]
  have hcl : IsClopen (K : Set (GA D V)) := ⟨K.isClosed_of_isOpen ho, ho⟩
  refine ⟨hcl.continuous_indicator continuous_const, HasCompactSupport.intro' hc hcl.1 fun x hx => Set.indicator_of_notMem hx _,
    ⟨K, ho, fun k hk _ => hinv k hk⟩, fun k τs Xs _ g => ?_⟩
  have : ∀ t : Fin k → ℝ, (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod ∈ K := fun t =>
    K.list_prod_mem fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact hK (oneP_mem_GinfC θ V _ _ _)
  simp only [hinv _ (this _)]
  exact contDiff_const

theorem exists_isCcInf (θ : InfF D) (V : HSp D) (hV : V.gram = 1) : ∃ f, IsCcInf θ V f ∧ f 1 = 1 := by
  obtain ⟨K, hK, ho, -, hc⟩ := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).2.2.2.2.2.2
    (Submodule.span _ (Set.range (Pi.basisFun D.host.E (Fin V.rank)))) 1
    ⟨Submodule.fg_span (Set.finite_range _), by
      rw [Submodule.span_span_of_tower, (Pi.basisFun D.host.E (Fin V.rank)).span_eq]⟩ one_pos
  refine ⟨_, isCcInf_indicator θ V ho (hc hV) fun k hk => (hK k).2 ?_, Set.indicator_of_mem K.one_mem _⟩
  have h1 := (hK 1).1 K.one_mem
  have e : (finHom V k).1 = (finHom V 1).1 := by rw [map_one, show finHom V k = 1 from hk]
  unfold GlobalTheory.Ker.CongK at h1 ⊢
  rw [GlobalTheory.Ker.CongTop.fmt_eq] at h1 ⊢
  rwa [e]

end GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition

end
end

