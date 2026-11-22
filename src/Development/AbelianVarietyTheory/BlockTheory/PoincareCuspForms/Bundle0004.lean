import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.InterpolationPeaks
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.InterpolationPeaks

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def bExp (X : Data E r) : ℝ := 5 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2

def leviR {n : ℕ} (g : V n → ℝ) (z : V n) (ξ : Fin n → ℂ) : ℝ :=
  (leviV n (fun w => ((g w : ℝ) : ℂ)) z ξ).re

def smoothPart (X : Data E r) (x0 : Frame X.Ψ r) (G L : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ)
    (z : V (nd X)) : ℝ :=
  phla X G (cpt X x0 z) - Real.log (densF X x0 z) - (nd X : ℝ) * phla X L (cpt X x0 z) + ps (cpt X x0 z)

def MarginAt (X : Data E r) (x0 : Frame X.Ψ r) (G L : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ) (m : ℝ) : Prop :=
  ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    m * leviR (rhF X x0) z ξ ≤ leviR (smoothPart X x0 G L ps) z ξ

def StrictAt (X : Data E r) (x0 : Frame X.Ψ r) (G L : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ) : Prop :=
  (∃ η : ℝ, 0 < η ∧ ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    2 * η * leviR (fun w => phla X L (cpt X x0 w)) z ξ ≤ leviR (smoothPart X x0 G L ps) z ξ) ∧
  ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 → 0 < leviR (fun w => phla X L (cpt X x0 w)) z ξ

def HasMargin (X : Data E r) (G L : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ) (b : ℝ) : Prop :=
  ∃ m : ℝ, b < m ∧ ∀ x0, IsOrth X x0 → MarginAt X x0 G L ps m

def tFac {X : Data E r} (Xa : ArchInM X) : ℝ := 1 + Xa.c1 / Xa.a1

def InOrbit {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (x : Frame X.Ψ r) : Prop :=
  ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (Fl.xs j) b)

def ModeBound (X : Data E r) : Prop :=
  ∀ (G : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ps : Frame X.Ψ r → ℝ) (a : ℝ),
    0 ≤ a → IsInvFn X ps → cfwM X ps a → X.IsBddSec G P →
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C A : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ENNReal.ofReal (X.pnorm G P x) ≤ ENNReal.ofReal (C * X.la1 x ^ (-A)) *
        ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
          ENNReal.ofReal (Real.exp (ps (cpt X x z) / 2))) →
    ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∀ x ∈ X.dom, X.fj G ξ ν P x ≠ 0 → a ≤ ∑ τ, ν τ

def PeakAt {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (G : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ)
    (b : ℝ) (x0 : Frame X.Ψ r) (z0 : V (nd X)) : Prop :=
  ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) ∧
    InAt X x0 (fun x => ENNReal.ofReal (Real.exp (-(phla X G x + ps x)))) b F ∧
    IsBEq X G P ∧ (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ F z0 ≠ 0 ∧
    ∀ x ∈ X.dom, InOrbit Fl x → (¬ ∃ β ∈ Bor X.Ψ r, x = rmul (cpt X x0 z0) β) → P x = 0

def InterpFor (b : ∀ {r : ℕ}, Data E r → ℝ) : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    HasMargin X Xa.Fp Xa.L (fun _ => 0) (b X) →
    ∀ v : Fin Fl.δ → ℂ, ∃ P ∈ X.SS Xa.Fp, ∀ j, P (Fl.xs j) = v j

def InterpGtFor (b : ∀ {r : ℕ}, Data E r → ℝ) : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → ModeBound X →
    HasMargin X Xa.Fp Xa.L (fun x => tFac Xa * Xa.ps0 x) (b X) →
    ∀ v : Fin Fl.δ → ℂ, ∃ P ∈ X.SSgt Xa.Fp Xa.c1, ∀ j, P (Fl.xs j) = v j

def CoreFor (b : ∀ {r : ℕ}, Data E r → ℝ) : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ)
    (x0 : Frame X.Ψ r) (z0 : V (nd X)) (m : ℝ),
    IsInvFn X ps → (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C) →
    IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ps (cpt X x0 z)) (OmF X x0) →
    z0 ∈ OmF X x0 → InOrbit Fl (cpt X x0 z0) →
    b X < m → MarginAt X x0 G Xa.L ps m → StrictAt X x0 G Xa.L ps →
    PeakAt Fl G ps (b X) x0 z0

variable (E)

def InterpStatement : Prop := InterpFor (E := E) bExp

def InterpGtStatement : Prop := InterpGtFor (E := E) bExp

def CoreStatement : Prop := CoreFor (E := E) bExp

def StrictStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (t : ℝ), 0 ≤ t → t * Xa.rr ≤ 2 * Xa.T →
    ∀ x0, IsOrth X x0 → StrictAt X x0 Xa.Fp Xa.L (fun x => t * Xa.ps0 x)

def Statement : Prop :=
  InterpStatement E ∧ InterpGtStatement E ∧ CoreStatement E ∧ StrictStatement E

variable {E}

theorem four_lt_bExp (X : Data E r) (hf : 0 < X.Ψ.card) (hr : 0 < r) :
    4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bExp X := by
  have h1 : (0 : ℝ) < X.Ψ.card := by exact_mod_cast hf
  have h2 : (0 : ℝ) < r := by exact_mod_cast hr
  have : 0 < (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by positivity
  unfold bExp; nlinarith

theorem factor_mul_firstMinimum {X : Data E r} (Xa : ArchInM X) : tFac Xa * Xa.a1 = Xa.c1 + Xa.a1 := by
  have := Xa.frame_theta_weight_pos.ne'
  unfold tFac; field_simp; ring

theorem tFac_range {X : Data E r} (Xa : ArchInM X) : 0 ≤ tFac Xa ∧ tFac Xa * Xa.rr ≤ 2 * Xa.T := by
  have h1 := Xa.frame_theta_weight_pos
  have h2 := Xa.frame_theta_const_pos
  refine ⟨by unfold tFac; positivity, ?_⟩
  rw [mul_comm]; exact Xa.rr_le

theorem peak_of_interpGt (h : InterpGtStatement E) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa)
    (hd : PropDisc X) (hm : ModeBound X)
    (hq : HasMargin X Xa.Fp Xa.L (fun x => tFac Xa * Xa.ps0 x) (bExp X)) (j : Fin Fl.δ) :
    ∃ P ∈ X.SSgt Xa.Fp Xa.c1, ∀ j', P (Fl.xs j') ≠ 0 ↔ j' = j := by
  obtain ⟨P, hP, hv⟩ := h r X Xa Fl hd hm hq (fun j' => if j' = j then 1 else 0)
  refine ⟨P, hP, fun j' => ?_⟩
  rw [hv]; by_cases e : j' = j <;> simp [e]

end

end GlobalTheory.IndefiniteRowSideFullHecke.InterpolationPeaks
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SpanSubtraction
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology Asymptotics
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def wtTop {X : Data E r} (Xa : ArchInM X) : Wt X.Ψ r := Xa.Fp + Xa.T • Xa.L

def wtLow {X : Data E r} (Xa : ArchInM X) : Wt X.Ψ r := Xa.Fp + nd X • Xa.L

def wNorm {X : Data E r} (Xa : ArchInM X) (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2)

def BddByPow {X : Data E r} (Xa : ArchInM X) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (wtTop Xa) f x ≤ C * wNorm Xa x ^ Xa.T

def BasisOnS {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa)
    (t : Fin Fl.δ → Frame X.Ψ r → ℂ) : Prop :=
  Function.Bijective fun (c : Fin Fl.δ → ℂ) (j : Fin Fl.δ) => ∑ i, c i * t i (Fl.xs j)

def zAt {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) (u : V (nd X)) : V (nd X) :=
  WithLp.toLp 2 fun k => Fl.s k (cpt X (Fl.xs j) u) / Fl.w0 (cpt X (Fl.xs j) u)

def VanOrd {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (a : ℕ) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∀ j : Fin Fl.δ, (fun u : V (nd X) => f (cpt X (Fl.xs j) u)) =O[𝓝 0] fun u => ‖zAt Fl j u‖ ^ a

def FiniteVolume (X : Data E r) : Prop :=
  ∃ x0 : Frame X.Ψ r, IsOrth X x0 ∧ ∃ FF : Set (V (nd X)), IsFundSet X x0 FF ∧ muF X x0 FF < ⊤

def FiniteDimCusp (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS la, ∃ c : Fin K → ℂ,
    ∀ x ∈ X.dom, f x = ∑ i, c i * g i x

def GapsPairing (X : Data E r) (la : Wt X.Ψ r) (m : ℝ) : Prop :=
  ∀ τ : X.Ψ,
    (∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ j ≤ la τ i) ∧
    ∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → m ≤ ((la τ i1 - la τ i0 : ℤ) : ℝ)

def DivHyp {X : Data E r} (Xa : ArchInM X) : Prop :=
  0 < X.p0 ∧ X.p0 < r ∧ 8 ≤ r ∧ PropDisc X ∧ FiniteVolume X ∧ FiniteDimCusp X (wtTop Xa) ∧
    GapsPairing X (Xa.Fp - kapW X) (19 / 10 * ((nd X : ℝ) + 2) * Xa.T)

def lead {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (t : Fin Fl.δ → Frame X.Ψ r → ℂ)
    (cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ) : Frame X.Ψ r → ℂ :=
  leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc

def tail {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa)
    (h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), monoM X Fl.s α x * h α x

def SubtractStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (t : Fin Fl.δ → Frame X.Ψ r → ℂ),
    (∀ i, t i ∈ X.SS Xa.Fp) → BasisOnS Fl t →
    ∀ f, X.IsSec (wtTop Xa) f →
      ∃ cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ,
        VanOrd Fl (Xa.T - nd X) fun x => f x - lead Fl t cc x

def DivisionStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), DivHyp Xa →
    ∀ f ∈ X.SS (wtTop Xa), BddByPow Xa f → VanOrd Fl (Xa.T - nd X) f →
      ∃ h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ,
        (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), h α ∈ X.SS (wtLow Xa)) ∧
        ∀ x ∈ X.dom, f x = tail Fl h x

def InSpan {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (t : Fin Fl.δ → Frame X.Ψ r → ℂ)
    (f : Frame X.Ψ r → ℂ) : Prop :=
  ∃ (cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ) (h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ),
    (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), h α ∈ X.SS (wtLow Xa)) ∧
    ∀ x ∈ X.dom, f x = lead Fl t cc x + tail Fl h x

def SpanBoundStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), DivHyp Xa →
    ∀ t : Fin Fl.δ → Frame X.Ψ r → ℂ, (∀ i, t i ∈ X.SS Xa.Fp) → BasisOnS Fl t →
    ∀ f ∈ X.SS (wtTop Xa), BddByPow Xa f → InSpan Fl t f

def SpanStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), DivHyp Xa →
    ∀ t : Fin Fl.δ → Frame X.Ψ r → ℂ, (∀ i, t i ∈ X.SS Xa.Fp) → BasisOnS Fl t →
    ∀ f ∈ X.SSgt (wtTop Xa) Xa.c1, InSpan Fl t f

theorem VanOrd.add {X : Data E r} {Xa : ArchInM X} {Fl : FlatM X Xa} {a : ℕ}
    {f g : Frame X.Ψ r → ℂ} (hf : VanOrd Fl a f) (hg : VanOrd Fl a g) :
    VanOrd Fl a fun x => f x + g x := fun j => (hf j).add (hg j)

theorem VanOrd.eq_zero {X : Data E r} {Xa : ArchInM X} {Fl : FlatM X Xa} {a : ℕ} (ha : a ≠ 0)
    {f : Frame X.Ψ r → ℂ} (hf : VanOrd Fl a f) (j : Fin Fl.δ)
    (hs : ∀ k, Fl.s k (cpt X (Fl.xs j) 0) = 0) : f (cpt X (Fl.xs j) 0) = 0 := by
  obtain ⟨C, hC⟩ := (hf j).bound
  have h := hC.self_of_nhds
  have hz : zAt Fl j 0 = 0 := by
    ext k
    simp [zAt, hs k]
  simp only [hz, norm_zero, zero_pow ha, mul_zero] at h
  exact norm_le_zero_iff.mp h

end

end GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction
end

