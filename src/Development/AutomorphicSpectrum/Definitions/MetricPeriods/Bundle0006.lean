import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0004
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
section
namespace GlobalTheory.CompanionTheory.Ar.ThA

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def wabs (X : Data E r) (la : Wt X.Ψ r) : ℝ := ∑ τ, ∑ i, |(la τ i : ℝ)|

def GapsGe (X : Data E r) (la : Wt X.Ψ r) (g : ℝ) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → (la τ j : ℝ) + g ≤ la τ i) ∧
    ∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → 0 < X.p0 → X.p0 < r → (la τ i0 : ℝ) + g ≤ la τ i1

def rhoW (X : Data E r) : Wt X.Ψ r := fun _ a =>
  if (a : ℕ) < X.p0 then -(((r : ℤ) - X.p0) + (a : ℕ)) else -(((a : ℕ) : ℤ) - X.p0)

def delW (X : Data E r) : Wt X.Ψ r := fun _ a => if (a : ℕ) < X.p0 then -1 else 0

def rad0 (r : ℕ) : ℝ := 1 / (1116 * (r : ℝ))

def nrm2 (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) : ℝ :=
  (∫ z in FF, X.pnorm la P (cpt X x0 z) ^ 2 ∂muF X x0) / (muF X x0 FF).toReal

def BergLB (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (la : Wt X.Ψ r)
    (x : Frame X.Ψ r) (t : ℝ) : Prop :=
  ∃ P ∈ X.SS la, 0 < nrm2 X x0 FF la P ∧ t * nrm2 X x0 FF la P ≤ X.pnorm la P x ^ 2

def FinDimSS (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS la, ∃ c : Fin K → ℂ,
    ∀ x ∈ X.dom, f x = ∑ i, c i * g i x

def HasLevel (X : Data E r) (c : ℕ) : Prop :=
  ∀ γ ∈ X.Γ, ∀ v ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (c : E) • y

def InjBall (X : Data E r) (x1 : Frame X.Ψ r) (ρ : ℝ) : Prop :=
  Metric.ball 0 ρ ⊆ OmF X x1 ∧
  ∀ γ ∈ X.Γ, ∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∀ z' ∈ Metric.ball (0 : V (nd X)) ρ,
    ∀ b ∈ Bor X.Ψ r, cpt X x1 z' = lact γ (rmul (cpt X x1 z) b) → γ = 1

def satG (X : Data E r) (x1 : Frame X.Ψ r) (S : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z ∈ S, x = lact γ (rmul (cpt X x1 z) b)}

def IsSmSec (X : Data E r) (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ) : Prop :=
  ContDiffOn ℝ ∞ F X.dom ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, F (rmul x b) = bchar la b * F x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, F (lact γ x) = X.χ la γ * F x

def crossDet (X : Data E r) (x y : Frame X.Ψ r) (τ : X.Ψ) : ℂ :=
  (Matrix.of fun a b : Fin X.p0 => hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a))
    (col (mat y τ) (Fin.castLE X.p0_le b))).det

def kerK (X : Data E r) (b : ℝ) (x y : Frame X.Ψ r) : ℝ :=
  ∏ τ, (‖crossDet X x x τ‖ * ‖crossDet X y y τ‖ / ‖crossDet X x y τ‖ ^ 2) ^ b

def dbarM (X : Data E r) (F : Frame X.Ψ r → ℂ) (x1 : Frame X.Ψ r) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℂ :=
  ∑ j, wdb (nd X) j (fun w => F (cpt X x1 w)) z * conj (ξ j)

def thetaM (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x1 : Frame X.Ψ r) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  leviM X (phla X (la - kapW X)) x1 z ξ - 2 * (r : ℝ) * leviM X (phla X (delW X)) x1 z ξ +
    leviM X ψ x1 z ξ

def QHyp (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (F0 : Frame X.Ψ r → ℂ)
    (a : Frame X.Ψ r → ℝ) : Prop :=
  IsInvFn X ψ ∧ ContDiffOn ℝ ∞ ψ X.dom ∧ (∃ C : ℝ, ∀ x ∈ X.dom, |ψ x| ≤ C) ∧
  IsSmSec X la F0 ∧ (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la F0 x ≤ C) ∧
  Measurable a ∧ IsInvFn X a ∧ (∃ C : ℝ, ∀ x ∈ X.dom, 0 ≤ a x ∧ a x ≤ C) ∧
  ∀ x1, IsOrth X x1 → ∀ z ∈ OmF X x1, ∀ ξ : Fin (nd X) → ℂ,
    16 * (r : ℝ) ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) * leviM X (phla X (delW X)) x1 z ξ ≤
      thetaM X la ψ x1 z ξ ∧
    ‖dbarM X F0 x1 z ξ‖ ^ 2 * X.nfac la (cpt X x1 z) ^ 2 ≤ a (cpt X x1 z) * thetaM X la ψ x1 z ξ

def CutData (X : Data E r) (la : Wt X.Ψ r) (x1 : Frame X.Ψ r) (χ : ℝ → ℝ) (δ : ℝ)
    (ψ : Frame X.Ψ r → ℝ) (F0 : Frame X.Ψ r → ℂ) (a : Frame X.Ψ r → ℝ) : Prop :=
  (∀ z ∈ Metric.ball (0 : V (nd X)) (rad0 r),
    ψ (cpt X x1 z) = (nd X : ℝ) * etaCut χ (rad0 r) δ z ∧
    F0 (cpt X x1 z) = (χ (‖z‖ ^ 2 / rad0 r ^ 2) : ℂ) ∧
    a (cpt X x1 z) ≤ if rad0 r ^ 2 / 4 ≤ ‖z‖ ^ 2 then 9 / (113 * (nd X : ℝ)) * X.nfac la (cpt X x1 z) ^ 2 else 0) ∧
  ∀ x ∈ X.dom, x ∉ satG X x1 (Metric.ball 0 (rad0 r)) → ψ x = 0 ∧ F0 x = 0 ∧ a x = 0

def HasPeriod (X : Data E r) (P : Frame X.Ψ r → ℂ) (M : ℝ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ a : E, cc a = a → IsIntegral ℤ a → ∀ x ∈ X.dom,
    P (X.flow ξ (fun τ => (M : ℂ) * τ.1 a) x) = P x

def FJSupp (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (σ : ℝ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 →
    (∀ τ, 0 ≤ ν τ) ∧ σ ≤ (∑ τ, Real.sqrt (ν τ)) ^ 2

def pp3c (E : Type) [Field E] [NumberField E] (M w : ℝ) : ℝ :=
  2 * (w + fdeg E * Real.log (4 * M * Real.sqrt (dE E)) + fdeg E * Real.log (fdeg E) + 3)

end

end GlobalTheory.CompanionTheory.Ar.ThA
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

structure GroupDict (F : UnivFam E Ψ j j' n g Λ) where

  h : HermitianForm (maximalRealSubfield E) E (Fin (j + j') → E)

  e : Λ →+ (Fin (j + j') → E)
  e_inj : Function.Injective e
  e_smul : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x

  Dn : ℕ
  integral : IsDIntegral h Dn e.range
  orth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0

  M : Majorant h (Pi.basisFun E (Fin (j + j')))

  κ : ℝ
  κ_pos : 0 < κ

  π : archUnitary h (Pi.basisFun E (Fin (j + j'))) → Fin n → ℂ
  π_cont : Continuous π
  π_range : Set.range π = ballDom F.q
  π_fibre : ∀ a b, π a = π b ↔ a⁻¹ * b ∈ M.stab
  len : ∀ a x, (F.R (π a)).normSq x = κ * M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (e x))) ^ 2

  α : latticeStab h e.range ≃* autGrp (E := E) F.form
  α_eq : ∀ γ x, e ((α γ).1 x) = ((γ : h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (e x)
  α_act : ∀ (γ : latticeStab h e.range) a,
    (F.R (π a)).EqvBy (F.R (π (archEmbed h (Pi.basisFun E (Fin (j + j'))) γ * a))) (α γ).1
  act : ∀ a₀, ∃ (A : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ A (ballDom F.q) ∧
    DifferentiableOn ℂ G (ballDom F.q) ∧ (∀ a, π (a₀ * a) = A (π a)) ∧
    ∀ t ∈ ballDom F.q, ballPot F.q (A t) = ballPot F.q t + (G t).re

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights TensorProduct

structure LinPt (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] where

  ρ : 𝓞 E →+* Module.End L V

  σ : Ψ ⊕ Ψ → (𝓞 E →+* L)
  σ_bij : Function.Bijective σ
  σ_inj : ∀ s, Function.Injective (σ s)

  Λ : Submodule (𝓞 L) V
  fg : Λ.FG
  span : Submodule.span L (Λ : Set V) = ⊤
  stable : ∀ a, ∀ x ∈ Λ, ρ a x ∈ Λ

  I : AddSubgroup V
  I_le : ∀ x ∈ I, x ∈ Λ
  I_stable : ∀ a, ∀ x ∈ I, ρ a x ∈ I
  I_basis : ∃ (r : ℕ) (e : Fin r → V), LinearIndependent L e ∧ AddSubgroup.closure (Set.range e) = I

  Bq : HermitianBundle.{0} L

  f : Λ →ₗ[𝓞 L] Bq.carrier
  ker : ∀ x : Λ, f x = 0 ↔ (x : V) ∈ Submodule.span (𝓞 L) (I : Set V)
  full : ∀ y : Bq.carrier, ∃ (a : 𝓞 L) (x : Λ), a ≠ 0 ∧ f x = a • y
  orth : ∀ s s', s ≠ s' → OrthAt Bq (((eigSp ρ (σ s)).restrictScalars (𝓞 L)).comap Λ.subtype |>.map f)
    (((eigSp ρ (σ s')).restrictScalars (𝓞 L)).comap Λ.subtype |>.map f)

namespace LinPt

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V)

def eig (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) V := A.Λ ⊓ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)

def tor (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) V := Submodule.span (𝓞 L) (A.I : Set V) ⊓ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)

def img (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) A.Bq.carrier := ((A.eig s).comap A.Λ.subtype).map A.f

def fam (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : Fin (r + k) → V :=
  Fin.append (fun a => eigComp A.ρ (A.σ s) (v a)) fun c => (q c : V)

def IsAdapted (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : Prop :=
  LinearIndependent L (A.fam s v q) ∧ Submodule.span L (Set.range (A.fam s v q)) = eigSp A.ρ (A.σ s)

def gramDet (ι : L →+* ℂ) {k : ℕ} (q : Fin k → A.Λ) : ℝ :=
  (Matrix.of fun c c' => (A.Bq.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] A.f (q c))
    ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] A.f (q c'))).det.re

def labDeg (s : Ψ ⊕ Ψ) (F : Submodule (𝓞 L) V) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : ℝ :=
  (logIdx F (A.fam s v q) - (∑ ι : L →+* ℂ, Real.log (A.gramDet ι q)) / 2) / Module.finrank ℚ L

def phiDeg [Fintype Ψ] (lab : Ψ → Ψ ⊕ Ψ) (F : Ψ → Submodule (𝓞 L) V) {r k : ℕ} (v : Fin r → V)
    (q : Ψ → Fin k → A.Λ) : ℝ :=
  ∑ τ, A.labDeg (lab τ) (F τ) v (q τ) - Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / 2 +
    Fintype.card Ψ * r / 2 * Real.log (4 * Real.pi)

end LinPt

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

