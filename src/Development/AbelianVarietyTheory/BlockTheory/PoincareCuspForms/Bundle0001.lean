import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.RealPointModes
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.RealPointModes

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

abbrev Idx (E : Type) [Field E] [NumberField E] : Type :=
  Module.Free.ChooseBasisIndex ℤ (𝓞 (maximalRealSubfield E))

def modeAt (X : Data E r) (ν : maximalRealSubfield E) (τ : X.Ψ) : ℝ := (τ.1 (ν : E)).re

def modeTrace (X : Data E r) (ν : maximalRealSubfield E) : ℝ := ∑ τ, modeAt X ν τ

def realPoint (X : Data E r) (u : Idx E → ℝ) (τ : X.Ψ) : ℝ :=
  ∑ i, u i * modeAt X (integralBasis (maximalRealSubfield E) i) τ

def cubeMean (X : Data E r) (ξ : Fin r → E) (ν : maximalRealSubfield E)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (N : ℕ) : ℂ :=
  ∫ u in Set.Icc (0 : Idx E → ℝ) 1,
    P (X.flow ξ (fun τ => (((N : ℝ) * realPoint X u τ : ℝ) : ℂ)) x) *
      exp (-(4 * Real.pi * I) *
        ((∑ τ, modeAt X ν τ * ((N : ℝ) * realPoint X u τ) : ℝ) : ℂ))

def fj (X : Data E r) (ξ : Fin r → E) (ν : maximalRealSubfield E)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  Filter.limUnder Filter.atTop fun k : ℕ => cubeMean X ξ ν P x k.factorial

def IsIsotropic (X : Data E r) (ξ : Fin r → E) : Prop :=
  ξ ∈ X.Λ ∧ ξ ≠ 0 ∧ herm X.Gm ξ ξ = 0

def IsShort (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1

def qq (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (τ : X.Ψ) : ℝ :=
  1 + (s τ).im / X.tt ξ x τ

def GrowthLE (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ) : Prop :=
  ∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-A)

def Moderate (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∃ C A : ℝ, 0 ≤ A ∧ GrowthLE X la P C A

def Bounded (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C

def SS (X : Data E r) (la : Wt X.Ψ r) : Set (Frame X.Ψ r → ℂ) :=
  {P | X.IsSec la P ∧ Bounded X la P ∧
    ∀ ξ, IsIsotropic X ξ → ∀ x ∈ X.dom, fj X ξ 0 P x = 0}

def SSgt (X : Data E r) (la : Wt X.Ψ r) (c : ℝ) : Set (Frame X.Ψ r → ℂ) :=
  {P | P ∈ SS X la ∧ ∀ ξ, IsIsotropic X ξ → ∀ ν : maximalRealSubfield E, modeTrace X ν ≤ c →
    ∀ x ∈ X.dom, fj X ξ ν P x = 0}

def FirstMinimumAlongFlow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (R : ℝ),
    ∃ C : ℝ, 0 < C ∧ ∀ ξ, IsIsotropic X ξ → ∀ x ∈ X.dom, IsShort X ξ x →
      ∀ s : X.Ψ → ℂ, (∀ τ, |(s τ).re| ≤ R) → (∀ τ, 0 < qq X ξ x s τ) →
        C⁻¹ * X.la1 x * (⨅ τ : X.Ψ, Real.sqrt (min (qq X ξ x s τ) (qq X ξ x s τ)⁻¹)) ≤
          X.la1 (X.flow ξ s x)

def CoefficientBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ), X.IsSec la P → 0 ≤ A → GrowthLE X la P C A →
    (∀ ξ, IsIsotropic X ξ → ∀ x ∈ X.dom, ∀ ν : maximalRealSubfield E,
      fj X ξ ν P x ≠ 0 → ∀ τ, 0 ≤ modeAt X ν τ) ∧
    ∀ η : ℝ, 0 < η → η < 1 → ∃ Cη : ℝ, ∀ ξ, IsIsotropic X ξ → ∀ x ∈ X.dom, IsShort X ξ x →
      ∀ ν : maximalRealSubfield E,
        X.pnorm la (fj X ξ ν P) x ≤ Cη * X.la1 x ^ (-A) *
          Real.exp (-(4 * Real.pi * (1 - η)) * ∑ τ, modeAt X ν τ * X.tt ξ x τ)

def ModesAdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la la' : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ),
    X.IsSec la P → Moderate X la P → X.IsSec la' Q → Moderate X la' Q →
    ∀ ξ, IsIsotropic X ξ → ∀ x ∈ X.dom, ∀ ν : maximalRealSubfield E,
      fj X ξ ν (P * Q) x ≠ 0 →
        ∃ ν₁ ν₂ : maximalRealSubfield E, ν₁ + ν₂ = ν ∧ fj X ξ ν₁ P x ≠ 0 ∧ fj X ξ ν₂ Q x ≠ 0

def CuspSpacesClosed : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ la : Wt X.Ψ r, ∃ S : Submodule ℂ (Frame X.Ψ r → ℂ), (S : Set (Frame X.Ψ r → ℂ)) = SS X la) ∧
    (∀ (la : Wt X.Ψ r) (c : ℝ),
      ∃ S : Submodule ℂ (Frame X.Ψ r → ℂ), (S : Set (Frame X.Ψ r → ℂ)) = SSgt X la c) ∧
    (∀ (la la' : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ), P ∈ SS X la → X.IsSec la' Q → Bounded X la' Q →
      P * Q ∈ SS X (la + la')) ∧
    ∀ (la la' : Wt X.Ψ r) (c : ℝ) (P Q : Frame X.Ψ r → ℂ), P ∈ SSgt X la c → X.IsSec la' Q →
      Bounded X la' Q → P * Q ∈ SSgt X (la + la') c

def Statement : Prop :=
  FirstMinimumAlongFlow ∧ CoefficientBounds ∧ ModesAdd ∧ CuspSpacesClosed

end

end GlobalTheory.IndefiniteRowSideFullHecke.RealPointModes
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TorusMarkingPhase
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusMarkingPhase

open NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def normSqAt (X : FD.Data E r) (x : FD.Frame X.Ψ r) (v : Fin r → E) : ℝ :=
  ∑ τ : X.Ψ, X.c τ * X.maj x τ (FD.Data.emb τ.1 v)

def altForm (X : FD.Data E r) (v w : Fin r → E) : ℚ :=
  Algebra.trace ℚ E (-X.ξ0 * FD.herm X.Gm v w)

def IsMarking (X : FD.Data E r) (x : FD.Frame X.Ψ r) (T : I2.PT E) (φ : X.Λ ≃+ T.L) : Prop :=
  (∀ (α : 𝓞 E) (v : X.Λ),
    (φ (α • v) : I2.Vsp T.dim) = I2.act α (φ v : I2.Vsp T.dim)) ∧
  (∀ v : X.Λ, ‖(φ v : I2.Vsp T.dim)‖ ^ 2 = normSqAt X x (v : Fin r → E)) ∧
  (∀ v w : X.Λ, (I2.Hf (φ v : I2.Vsp T.dim) (φ w : I2.Vsp T.dim)).im =
    (altForm X (v : Fin r → E) (w : Fin r → E) : ℝ))

def IsTorusAt (X : FD.Data E r) (x : FD.Frame X.Ψ r) (T : I2.PT E) : Prop :=
  x ∈ X.dom ∧ ∃ φ : X.Λ ≃+ T.L, IsMarking X x T φ

def phAt (X : FD.Data E r) (θ : ℝ) (x : FD.Frame X.Ψ r) : ℝ :=
  if X.la1 x < θ then 2 * (I2.PT.f E : ℝ) / (I2.PT.rd E ^ 2 * X.la1 x ^ 2) else 0

def ph (X : FD.Data E r) (q : ℕ) (R0 : ℝ) (x : FD.Frame X.Ψ r) : ℝ :=
  phAt X (I2.th (E := E) q R0) x

def TorusAtMinimum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 0 < r →
    ∀ (X : FD.Data E r) (x : FD.Frame X.Ψ r) (T : I2.PT E), IsTorusAt X x T →
      T.la1 = X.la1 x ∧ (∀ θ : ℝ, T.ph θ = phAt X θ x) ∧
        ∀ (D : ℕ) (P : I2.Par T D), P.ph = ph X P.q P.R0 x

end

end GlobalTheory.IndefiniteRowSideFullHecke.TorusMarkingPhase
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TorusThetaNorms
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusThetaNorms

open NumberField Complex ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def riem (D : FD.Data E r) (v w : Fin r → E) : ℚ :=
  Algebra.trace ℚ E (-(D.κ0 / 2) * FD.herm D.Gm v w)

def Unimodular (D : FD.Data E r) : Prop :=
  (∀ v ∈ D.Λ, ∀ w ∈ D.Λ, ∃ k : ℤ, riem D v w = k) ∧
    ∀ φ : D.Λ →+ ℤ, ∃ v ∈ D.Λ, ∀ w : D.Λ, (φ w : ℚ) = riem D v (w : Fin r → E)

def embR (D : FD.Data E r) (v : Fin r → E) : D.Ψ → Fin r → ℂ := fun τ => FD.Data.emb τ.1 v

def IsAdaptedON (D : FD.Data E r) (x e : FD.Frame D.Ψ r) : Prop :=
  (∃ b ∈ FD.Bor D.Ψ r, e = FD.rmul x b) ∧
    ∀ (τ : D.Ψ) (a b : Fin r),
      (D.c τ : ℂ) * FD.hermC τ.1 D.Gm (FD.col (FD.mat e τ) a) (FD.col (FD.mat e τ) b) =
        if a = b then ((FD.sgn D.p0 a : ℝ) : ℂ) else 0

structure TorusAt (D : FD.Data E r) (w0 : 𝓞 E) (x : FD.Frame D.Ψ r) where

  X : I2.PT E
  rank_eq : X.r = r

  dim_mem : ∀ τ : D.Ψ, X.dim τ.1 = r - D.p0

  dim_conj : ∀ τ : D.Ψ, X.dim (ComplexEmbedding.conjugate τ.1) = D.p0

  e : FD.Frame D.Ψ r
  e_adapted : IsAdaptedON D x e

  φ : (D.Ψ → Fin r → ℂ) → I2.Vsp X.dim

  φ_mem : ∀ (w : D.Ψ → Fin r → ℂ) (τ : D.Ψ) (i : Fin (X.dim τ.1)) (a : Fin r),
    (a : ℕ) = D.p0 + i →
      φ w ⟨τ.1, i⟩ = -((D.c τ : ℂ) * FD.hermC τ.1 D.Gm (w τ) (FD.col (FD.mat e τ) a))

  φ_conj : ∀ (w : D.Ψ → Fin r → ℂ) (τ : D.Ψ)
    (i : Fin (X.dim (ComplexEmbedding.conjugate τ.1))) (a : Fin r),
    (a : ℕ) + i + 1 = D.p0 →
      φ w ⟨ComplexEmbedding.conjugate τ.1, i⟩ =
        conj ((D.c τ : ℂ) * FD.hermC τ.1 D.Gm (w τ) (FD.col (FD.mat e τ) a))

  lattice : ∀ y : I2.Vsp X.dim, y ∈ X.L ↔ ∃ v ∈ D.Λ, y = φ (embR D v)

  eps_eq : ∀ v ∈ D.Λ,
    (X.eps (φ (embR D v)) : ℝ) = Real.cos (Real.pi * (riem D v ((w0 : E) • v) : ℝ))

  s : (Fin 1 → I2.Vsp X.dim) → ℂ
  s_mem : s ∈ X.Sec 1 1
  s_ne : s ≠ 0
  s_gen : ∀ F ∈ X.Sec 1 1, ∃ z : ℂ, F = z • s

def TorusExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (D : FD.Data E r) (w0 : 𝓞 E),
    (w0 : E) + FD.cc (w0 : E) = 1 → Unimodular D → ∀ x ∈ D.dom, Nonempty (TorusAt D w0 x)

def TorusCompatible : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (D : FD.Data E r) (w0 : 𝓞 E)
    (x : FD.Frame D.Ψ r) (T : TorusAt D w0 x),
    (∀ (α : 𝓞 E) (v : Fin r → E), T.φ (embR D ((α : E) • v)) = I2.act α (T.φ (embR D v))) ∧
    (∀ v w : Fin r → E, (I2.Hf (T.φ (embR D v)) (T.φ (embR D w))).im = (riem D v w : ℝ)) ∧
    ∀ w : D.Ψ → Fin r → ℂ, (I2.Hf (T.φ w) (T.φ w)).re = ∑ τ, D.c τ * D.maj x τ (w τ)

def actL {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) : I2.Vsp dim →ₗ[ℂ] I2.Vsp dim where
  toFun := I2.act α
  map_add' v w := by ext i; simp [I2.act, mul_add]
  map_smul' z v := by ext i; simp [I2.act, mul_left_comm]

namespace TorusAt

variable {D : FD.Data E r} {w0 : 𝓞 E} {x : FD.Frame D.Ψ r} (T : TorusAt D w0 x)

def sNorm : ℝ := Real.sqrt (T.X.l2 1 T.s)

def thetaVal {n : ℕ} (q : ℕ) (π : I2.Vsp T.X.dim →ₗ[ℂ] I2.Vsp T.X.dim)
    (P : MvPolynomial (I2.Letter n T.X.dim) ℂ) (b : Fin n → I2.Vsp T.X.dim) : ℂ :=
  I2.polyDeriv P I2.dir (T.X.U q b (I2.s0 T.X π T.s)) 0 / (T.sNorm : ℂ) ^ n

def IsThetaDatum {n : ℕ} (q : ℕ) (α : 𝓞 E) (d : ℕ) (P : MvPolynomial (I2.Letter n T.X.dim) ℂ)
    (y : Fin n → Fin r → E) : Prop :=
  1 ≤ q ∧ (α : E) * FD.cc (α : E) = q ∧ P.IsHomogeneous d ∧ ∀ k, FD.cc (α : E) • y k ∈ D.Λ

def thetaNorm {n : ℕ} (q : ℕ) (α : 𝓞 E) (d : ℕ) (P : MvPolynomial (I2.Letter n T.X.dim) ℂ)
    (y : Fin n → Fin r → E) : ℝ :=
  Real.pi ^ (-(d : ℝ) / 2) * ‖T.thetaVal q (actL α) P fun k => -T.φ (embR D (y k))‖

theorem exists_col_mem (τ : D.Ψ) (i : Fin (T.X.dim τ.1)) : ∃ a : Fin r, (a : ℕ) = D.p0 + i := by
  have h1 := T.dim_mem τ
  have h2 := i.isLt
  exact ⟨⟨D.p0 + i, by omega⟩, rfl⟩

theorem exists_col_conj (τ : D.Ψ) (i : Fin (T.X.dim (ComplexEmbedding.conjugate τ.1))) :
    ∃ a : Fin r, (a : ℕ) + i + 1 = D.p0 := by
  have h1 := T.dim_conj τ
  have h2 := i.isLt
  have h3 := D.p0_le
  exact ⟨⟨D.p0 - 1 - i, by omega⟩, by simp only; omega⟩

end TorusAt

end

end GlobalTheory.IndefiniteRowSideFullHecke.TorusThetaNorms
end

