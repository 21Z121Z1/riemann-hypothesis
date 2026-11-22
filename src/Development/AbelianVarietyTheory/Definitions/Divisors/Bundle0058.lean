import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp
open scoped NNReal

section Generic

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def ratioField (ev : V →ₗ[K] Ω) : IntermediateField K Ω :=
  IntermediateField.adjoin K {a | ∃ v w, a = ev v / ev w}

def GenRatios (ev : V →ₗ[K] Ω) : Prop := ev ≠ 0 ∧ ratioField ev = ⊤

def ValBound (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  ∀ ν : Valuation Ω ℝ≥0, (∀ a : K, a ≠ 0 → ν (algebraMap K Ω a) = 1) → ∃ v, ν t ≤ ν (ev v) ^ τ

example : GenRatios (LinearMap.id : K →ₗ[K] K) :=
  ⟨fun h => one_ne_zero (LinearMap.congr_fun h 1), eq_top_iff.2 fun a _ =>
    IntermediateField.subset_adjoin _ _ ⟨a, 1, by simp⟩⟩

example (ev : V →ₗ[K] Ω) (v : V) : ValBound ev 1 (ev v) := fun _ _ => ⟨v, by simp⟩

end Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def BirOn (Z : Comp Xo c) (G : WTZ E) : Prop := GenRatios (genPoint Z (cuspOn U Z G))

def ValMult (Z : Comp Xo c) (G G' : WTZ E) : Prop :=
  ∃ (a : ℕ) (θ : Rul Xo c), 1 ≤ a ∧ genVal Z θ ≠ 0 ∧ ∀ (k : ℕ), 1 ≤ k → ∀ f ∈ cuspOn U Z ((a * k) • G'),
    θ ^ k * f ∈ cuspOn U Z ((a * k) • G) ∧ ValBound (genPoint Z (cuspOn U Z G)) (a * k) (genVal Z (θ ^ k * f))

end GlobalTheory.DegVal
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
section
noncomputable section

namespace GlobalTheory.UPel.Sm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def InfUniv {D : Datum F} {p N : ℕ} {X : Scheme.{0}} {s : X ⟶ Sp (D.OEp p)} (univ : Obj D p N s) : Prop :=
  ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀),
    Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (t : Sp C ⟶ Sp (D.OEp p)) (o : Obj D p N t) (o₀ : Obj D p N (spMap π ≫ t)) (x₀ : Sp C₀ ⟶ X),
      x₀ ≫ s = spMap π ≫ t → Nonempty (ObjMap o₀ o (spMap π)) → Nonempty (ObjMap o₀ univ x₀) →
      ∃! x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t ∧ Nonempty (ObjMap o univ x)

section KS

variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]

def IsKS (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H)
    (f : H →ₗ[k] H) : Prop :=
  (∀ a, ∀ x ∈ Fil, f (ρ a x) - ρ a (f x) ∈ Fil) ∧ (∀ x ∈ Z, f x ∈ Fil) ∧
    ∀ x ∈ Fil, ∀ y ∈ Fil, φ (f x) y + φ x (f y) = 0

def KSDim (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) (d : ℕ) :
    Prop :=
  ∃ f : Fin d → (H →ₗ[k] H), (∀ i, IsKS ρ φ Fil Z (f i)) ∧
    ∀ g, IsKS ρ φ Fil Z g → ∃! c : Fin d → k, ∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil

end KS

end GlobalTheory.UPel.Sm
end
end

