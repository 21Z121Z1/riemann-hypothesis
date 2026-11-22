import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ChartSpec
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def sq2 (X : Data E r) {N : ℕ} (la : Wt X.Ψ r) (w : Fin N → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  ∑ k, X.pnorm la (w k) x ^ 2

def IndepOn (X : Data E r) {m : ℕ} (f : Fin m → Frame X.Ψ r → ℂ) : Prop :=
  ∀ a : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0

def dimSS (X : Data E r) (la : Wt X.Ψ r) : ℕ := Module.finrank ℂ (spanDom X (X.SS la))

def volSS (X : Data E r) (la : Wt X.Ψ r) : ℝ :=
  Filter.limsup (fun n : ℕ => ((nd X).factorial : ℝ) * (dimSS X (n • la) : ℝ) / (n : ℝ) ^ nd X) atTop

def rootPair (X : Data E r) (v : X.Ψ → Fin r → ℝ) (e : Ent X) : ℝ :=
  if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then v e.1 e.2.1.1 - v e.1 e.2.1.2
  else v e.1 e.2.1.2 - v e.1 e.2.1.1

def vdeg (X : Data E r) (v : X.Ψ → Fin r → ℝ) : ℝ := ∏ e : Ent X, rootPair X v e

def wtR (X : Data E r) (la : Wt X.Ψ r) : X.Ψ → Fin r → ℝ := fun τ a => (la τ a : ℝ)

open Classical in

def covol (X : Data E r) : ℝ≥0∞ :=
  if h : ∃ FF, IsFundSet X (x0F X) FF then muF X (x0F X) h.choose else 0

def ivol (X : Data E r) (v : X.Ψ → Fin r → ℝ) : ℝ :=
  ((nd X).factorial : ℝ) / Real.pi ^ nd X * (covol X).toReal * vdeg X v

def ChartSpec (X : Data E r) (e : X.dom → OpenPartialHomeomorph (Yq X) (V (nd X))) : Prop :=
  ∀ i : X.dom, q X i ∈ (e i).source ∧ e i (q X i) = 0 ∧
    ∀ z ∈ (e i).target, ∃ h : cpt X i.1 z ∈ X.dom, (e i).symm z = q X ⟨_, h⟩

def frE (X : Data E r) (e : X.dom → OpenPartialHomeomorph (Yq X) (V (nd X))) (i : X.dom) (y : Yq X) : Frame X.Ψ r :=
  cpt X i.1 (e i y)

open Classical in

def tgE (X : Data E r) (e : X.dom → OpenPartialHomeomorph (Yq X) (V (nd X))) (i j : X.dom) (y : Yq X) :
    GL (Fin r) E :=
  if h : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, frE X e i y = lact γ (rmul (frE X e j y) b) then h.choose else 1

open Classical in

def tbE (X : Data E r) (e : X.dom → OpenPartialHomeomorph (Yq X) (V (nd X))) (i j : X.dom) (y : Yq X) :
    Frame X.Ψ r :=
  if h : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, frE X e i y = lact γ (rmul (frE X e j y) b)
  then h.choose_spec.2.choose else 0

def gE (X : Data E r) (e : X.dom → OpenPartialHomeomorph (Yq X) (V (nd X))) (la : Wt X.Ψ r) (i j : X.dom)
    (y : Yq X) : ℂ :=
  X.χ la (tgE X e i j y) * bchar la (tbE X e i j y)

def phE (X : Data E r) (e : X.dom → OpenPartialHomeomorph (Yq X) (V (nd X))) (la : Wt X.Ψ r) (i : X.dom)
    (y : Yq X) : ℝ :=
  phla X la (frE X e i y)

def FitsP (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]
    (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)) : Prop :=
  Fits X A ∧ ∀ la i y, y ∈ (A.chart i).source → A.ph la i y = phla X la (cpt X i.1 (A.chart i y))

def hAux (X : Data E r) (L : Wt X.Ψ r) (m k : ℕ) (P b w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ)
    (ε β α : ℝ) (x : Frame X.Ψ r) : ℝ :=
  X.pnorm (m • L) P x ^ 2 * (X.pnorm (k • L) b x ^ 2) ^ ε * (X.pnorm L w0 x ^ 2) ^ β / sq2 X L s x ^ α

def MarginC (X : Data E r) (Xa : ArchInM X) : Prop :=
  ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
    ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + (1 + Xa.c1 / Xa.a1) * leviO X x0 Xa.ps0 z ξ

end GlobalTheory.CompanionTheory.Ar.Deg
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenOver
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (K : Type) [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

def delG (D : ℕ) {N : ℕ} (x : Fin (N + 1) → Ω) : ℕ :=
  Module.finrank (IntermediateField.adjoin K (Set.range
    (ReciprocityTheory.ChartRestriction.G.T0.sImg (D := D) (0 : Fin (N + 1)) (fun k : Fin N => x k.succ / x 0))))
    (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)

variable {K}

def GenOver (σ : K →+* ℂ) {I : Type} (t : I → ℂ) : Prop :=
  ∀ Q : MvPolynomial I K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0

def OnCone (σ : K →+* ℂ) {N : ℕ} (x : Fin (N + 1) → Ω) (v : Fin (N + 1) → ℂ) : Prop :=
  ∀ (Q : MvPolynomial (Fin (N + 1)) K) (d : ℕ), Q.IsHomogeneous d → MvPolynomial.aeval x Q = 0 →
    MvPolynomial.eval₂ σ v Q = 0

def IsAtPt {N : ℕ} (x : Fin (N + 1) → Ω) (P : Ω →+* ℂ) (v : Fin (N + 1) → ℂ) : Prop :=
  v 0 ≠ 0 ∧ ∀ j, v j = P (x j / x 0) * v 0

def FnTie (σ : K →+* ℂ) (X : Data E r) {N : ℕ} (x : Fin (N + 1) → Ω) (w : Fin (N + 1) → Frame X.Ψ r → ℂ) : Prop :=
  x 0 ≠ 0 ∧ IntermediateField.adjoin K (Set.range fun j => x j / x 0) = ⊤ ∧
  (∀ y ∈ X.dom, (∃ j, w j y ≠ 0) ∧ OnCone σ x fun j => w j y) ∧
  ∀ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = σ →
    (∃ y ∈ X.dom, IsAtPt x P fun j => w j y) ∧
    ∀ y ∈ X.dom, ∀ y' ∈ X.dom, (IsAtPt x P fun j => w j y) → (IsAtPt x P fun j => w j y') →
      ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y' = lact γ (rmul y b)

end GlobalTheory.CompanionTheory.Ar.Deg
end
end

