import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S
open scoped Topology TensorProduct ContDiff

namespace GlobalTheory.CuspGeo

section Inst

variable (I : AutInst)

def IntVec (u : Fin I.n → I.E) : Prop := ∀ i, IsIntegral ℤ (u i)

def vec (y : I.Ginf) (u : Fin I.n → I.E) : InfinitePlace I.F → Fin I.n → ℂ :=
  fun v => uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (u i))

def NoShort (y : I.Ginf) (t : ℝ) : Prop := ∀ u, IntVec I u → u ≠ 0 → t ≤ ‖vec I y u‖

def Close (u : I.Ginf) (δ : ℝ) : Prop := ∀ v i j, ‖(uMat (u v) - 1) i j‖ ≤ δ

def IsZBasis {N : ℕ} (e : Fin N → Fin I.n → I.E) : Prop :=
  LinearIndependent ℤ e ∧ ∀ u, IntVec I u ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e i

def IsRealCoord {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) : Prop :=
  ∀ x y, ρ x ⬝ᵥ ρ y = ∑ v, ∑ i, (star (x v i) * y v i).re

def gm {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => ρ (vec I y (e j)) i

def trForm (x y : Fin I.n → I.E) : ℚ := Algebra.trace ℚ I.E (Formalism.UG.hform (starRingEnd I.E) I.J x y)

def BddType {N : ℕ} (R : ℝ) (e : Fin N → Fin I.n → I.E) : Prop :=
  (∀ k j, ∃ z : Fin N → ℤ, (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i ∧ ∀ i, |(z i : ℝ)| ≤ R) ∧
    ∀ i j, |(trForm I (e i) (e j) : ℝ)| ≤ R

def RedBasis : Prop :=
  ∃ (N : ℕ) (R C : ℝ), ∀ y : I.Ginf, ∃ e : Fin N → Fin I.n → I.E, IsZBasis I e ∧ BddType I R e ∧
    ∀ t : ℝ, 0 < t → t ≤ 1 → NoShort I y t → ∀ j, ‖vec I y (e j)‖ * t ^ N ≤ C

def HtMin : Prop :=
  ∃ (b : ℕ) (C : ℝ) (K : Set I.Gf), IsCompact K ∧ ∀ (y : I.Ginf) (t : ℝ), 0 < t → t ≤ 1 → NoShort I y t →
    ∃ γ ∈ I.GFset, γ.2 ∈ K ∧ ∀ v i j, ‖uMat ((γ.1 * y) v) i j‖ * t ^ b ≤ C

def ShortCusp : Prop :=
  ∀ U ∈ 𝓝 (1 : I.Gf), ∃ s₀ η₀ C : ℝ, 0 < s₀ ∧ 0 < η₀ ∧ ∀ (y : I.Ginf) (η : ℝ), 0 < η → η ≤ η₀ →
    (∃ u, IntVec I u ∧ u ≠ 0 ∧ ‖vec I y u‖ ≤ s₀ * η ^ (I.n + 1)) →
    ∃ W, I.IsIsot W ∧ ∀ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA W →
      ∃ γ ∈ I.GFset, γ.2 ∈ U ∧ Close I (y⁻¹ * (γ.1 * m) * y) (C * η)

def NearInst : Prop :=
  ∀ Kp : Subgroup I.Gf, IsOpen (Kp : Set I.Gf) → ∃ (b : ℕ) (C δ₀ : ℝ) (K : Set I.Gf), 0 < δ₀ ∧ IsCompact K ∧
    ∀ x : I.GA, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∃ γ ∈ I.GFset, (γ * x).2 ∈ K ∧ ∀ v i j, ‖uMat ((γ * x).1 v) i j‖ * δ ^ b ≤ C) ∧
      (δ₀ ≤ δ ∨ ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset, ∃ u : I.Ginf, ∃ k ∈ Kp,
        m * x = γ * x * (u, k) ∧ Close I u (C * δ))

end Inst

section Rec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

def CloseR (u : GA D V) (δ : ℝ) : Prop :=
  u ∈ GinfC V ∧ ∀ τ i j, ‖(infMat D.sp.cm.sig V.gram (θ τ) u - 1) i j‖ ≤ δ

def Near : Prop :=
  ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ (b : ℕ) (C δ₀ : ℝ), 0 < δ₀ ∧
    ∀ g : GA D V, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ GlobalTheory.Grow.quotHeight V g * δ ^ b ≤ C ∧
      (δ₀ ≤ δ ∨ ∃ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ ∧ ∀ m ∈ NI V C₀,
        ∃ γ ∈ GQ V, ∃ u k : GA D V, CloseR θ V u (C * δ) ∧ k ∈ U ∧ k ∈ GfC V ∧ m * g = γ * g * u * k)

def SmoothW (φ : GA D V → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

end Rec

end GlobalTheory.CuspGeo

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TermSumBoundOfPairsAmplitude
section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
namespace GlobalTheory.Core.Deg

def TailU : Prop :=
  ∀ Cg cb Cw cT CT : ℝ, 0 < cb → 0 < cT → ∃ CH : ℝ, 0 ≤ CH ∧ ∀ C₁ : ℕ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (C0 : ℝ) (D : D7) (large₂ : SizeData₂ D), Formalism.BasicNotions.Ties D → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
      (∀ w : D.what₂.Word, 1 ≤ Tr D w * Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS)) → TailAt D large₂ CH C₁

def AmpU : Prop :=
  ∀ Cg cb Cw cT CT : ℝ, 0 < cb → 0 < cT → ∃ CH : ℝ, 0 ≤ CH ∧ ∀ Cs : ℝ, 0 ≤ Cs →
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → AmpAt large₂ Y u CH Cs C

def PairsU : Prop :=
  ∀ Cg cb Cw cT CT CH : ℝ, 0 ≤ CH → ∃ Ch Cp : ℝ, 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → PairsAt large₂ Y u CH Ch Cp

def TypeU : Prop :=
  ∀ Cg cb Cw cT CT : ℝ, 0 < cb → 0 < cT → ∃ CH Ch Cp : ℝ, 0 ≤ CH ∧ 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∀ Cs : ℝ, Cp + 4 ≤ Cs →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → TypeAt large₂ Y u CH Cs C Ch Cp

def PairsDegOfType : Prop :=
  ∀ CH Ch Cp C : ℝ, 0 ≤ CH → 0 ≤ Ch → 0 ≤ Cp → 2 * (CH + 1) ≤ C → ∃ Cl₀ : ℝ,
    ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Cl₀ ≤ Cl →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → TypeAt large₂ Y u CH (Cp + 4) C Ch Cp →
      Formalism.L2.SG.RowsOther.PairsDegAmp (Y.tO u u) (PgC Y) (duC X Y u) D.R.k D.R.f

def TermSumBoundOfPairsAmplitude : Prop :=
  ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
    Formalism.L2.SG.RowsOther.PairsDegAmp (Y.tO u u) (PgC Y) (duC X Y u) D.R.k D.R.f → VanishingGramTermsBound Y u

end GlobalTheory.Core.Deg
end
end

