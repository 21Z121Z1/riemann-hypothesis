import Mathlib

-- bundled from Formalism.WachModuleLifts.Statement
section
open Finset

noncomputable section

namespace Formalism.CL

variable (p : ℕ) [Fact p.Prime]

def phiPoly : Polynomial ℚ_[p] :=
  Polynomial.X ^ p - Polynomial.C (p : ℚ_[p]) * Polynomial.X ^ (p - 1) + Polynomial.C (p : ℚ_[p])

def phiIter (g : ℕ) : Polynomial ℚ_[p] := (fun f => (phiPoly p).comp f)^[g] Polynomial.X

def uu (g : ℕ) : PowerSeries ℚ_[p] :=
  (p : ℚ_[p])⁻¹ • ((phiIter p g : Polynomial ℚ_[p]) : PowerSeries ℚ_[p])

def Content (g : ℕ) (f : PowerSeries ℚ_[p]) : Prop :=
  ∀ j : ℕ, ‖PowerSeries.coeff j f‖ ≤ (p : ℝ) ^ (j / p ^ g)

def LemmaCPow : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ), 1 ≤ g → ∀ y : ℕ, Content p g (uu p g ^ y)

def LemmaCInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ), 1 ≤ g →
    (uu p g)⁻¹ * uu p g = 1 ∧ ∀ y : ℕ, Content p g ((uu p g)⁻¹ ^ y)

def ContentMul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (f f' : PowerSeries ℚ_[p]),
    Content p g f → Content p g f' → Content p g (f * f')

def ContentMono : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g s : ℕ) (f : PowerSeries ℚ_[p]), g ≤ s → Content p s f → Content p g f

def LemmaCSharp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (y r : ℕ), r ≤ y → padicValNat p (y.choose r) < p - 1 →
    ‖PowerSeries.coeff (p * r) (uu p 1 ^ y)‖ = (p : ℝ) ^ ((r : ℤ) - padicValNat p (y.choose r))

def LemmaCSharpInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (y r : ℕ), 0 < y → padicValNat p ((y + r - 1).choose r) < p - 1 →
    ‖PowerSeries.coeff (p * r) ((uu p 1)⁻¹ ^ y)‖ =
      (p : ℝ) ^ ((r : ℤ) - padicValNat p ((y + r - 1).choose r))

def LemmaCSharpG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ), 1 ≤ g → ∀ (y r : ℕ), r ≤ y →
    padicValNat p (y.choose r) < p - 1 →
    ‖PowerSeries.coeff (p ^ g * r) (uu p g ^ y)‖ = (p : ℝ) ^ ((r : ℤ) - padicValNat p (y.choose r))

def LemmaCSharpGInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ), 1 ≤ g → ∀ (y r : ℕ), 0 < y →
    padicValNat p ((y + r - 1).choose r) < p - 1 →
    ‖PowerSeries.coeff (p ^ g * r) ((uu p g)⁻¹ ^ y)‖ =
      (p : ℝ) ^ ((r : ℤ) - padicValNat p ((y + r - 1).choose r))

def LemmaCPowMin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ), 1 ≤ g → ∀ (y j : ℕ),
    ‖PowerSeries.coeff j (uu p g ^ y)‖ ≤ (p : ℝ) ^ (min y (j / p ^ g))

def LemmaCSharpOdd1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (y r : ℕ), r ≤ y →
    ‖PowerSeries.coeff (p * r) (uu p 1 ^ y)‖ = (p : ℝ) ^ ((r : ℤ) - padicValNat p (y.choose r))

def LemmaCSharpOdd1Inv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (y r : ℕ), 0 < y →
    ‖PowerSeries.coeff (p * r) ((uu p 1)⁻¹ ^ y)‖ =
      (p : ℝ) ^ ((r : ℤ) - padicValNat p ((y + r - 1).choose r))

def LemmaCSharpOddG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (g : ℕ), 1 ≤ g → ∀ (y r : ℕ), r ≤ y →
    ‖PowerSeries.coeff (p ^ g * r) (uu p g ^ y)‖ = (p : ℝ) ^ ((r : ℤ) - padicValNat p (y.choose r))

def LemmaCSharpOddGInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (g : ℕ), 1 ≤ g → ∀ (y r : ℕ), 0 < y →
    ‖PowerSeries.coeff (p ^ g * r) ((uu p g)⁻¹ ^ y)‖ =
      (p : ℝ) ^ ((r : ℤ) - padicValNat p ((y + r - 1).choose r))

def phiPS (f : PowerSeries ℚ_[p]) : PowerSeries ℚ_[p] :=
  PowerSeries.mk fun r => ∑ s ∈ range (r + 1),
    PowerSeries.coeff s f *
      ((Polynomial.X + Polynomial.C (p : ℚ_[p])) ^ ((p - 1) * s)).coeff (r - s)

def PhiPSPoly : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : Polynomial ℚ_[p]),
    phiPS p (f : PowerSeries ℚ_[p]) =
      ((f.comp (Polynomial.X * (Polynomial.X + Polynomial.C (p : ℚ_[p])) ^ (p - 1)) :
        Polynomial ℚ_[p]) : PowerSeries ℚ_[p])

def LemmaHStep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : ℝ), 0 ≤ σ → σ ≤ p → ∀ f : PowerSeries ℚ_[p],
    (∀ s : ℕ, ‖PowerSeries.coeff s f‖ ≤ (p : ℝ) ^ (σ * s)) →
    ∀ r : ℕ, ‖PowerSeries.coeff r (phiPS p f)‖ ≤ (p : ℝ) ^ (σ * r / p)

def LemmaHLift : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V : Type) [NormedAddCommGroup V] [NormedSpace ℚ_[p] V]
    [IsUltrametricDist V] (u : ℚ_[p]) (x : ℕ → V) (c : ℕ → ℕ → V →L[ℚ_[p]] V) (gg : ℕ → V),
    (∀ m : ℕ, 1 ≤ m → ‖u ^ m - 1‖ = (p : ℝ) ^ (-(1 + (padicValNat p m : ℤ)))) →
    (∀ m i, ‖c m i‖ ≤ 1) → (∀ m, ‖gg m‖ ≤ 1) → ‖x 0‖ ≤ 1 →
    (∀ m : ℕ, 1 ≤ m → (u ^ m - 1) • x m = (∑ i ∈ range m, c m i (x i)) + gg m) →
    ∀ m : ℕ, ‖x m‖ ≤ (p : ℝ) ^ (m + padicValNat p m.factorial)

def Legendre : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m : ℕ),
    ((m : ℝ) + padicValNat p m.factorial) ≤ (m : ℝ) * p / (p - 1)

def Interp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (a : Fin n → ℤ_[p]) (Q : Polynomial ℤ_[p]) (e : ℕ),
    Function.Injective a →
    (∀ i : Fin n, ‖(p : ℤ_[p]) ^ e‖ ≤ ‖Q.eval (a i) * ∏ k ∈ univ.erase i, (a i - a k)‖) →
    Polynomial.C ((p : ℤ_[p]) ^ e) ∈
      Ideal.span ({∏ i : Fin n, (Polynomial.X - Polynomial.C (a i)), Q} : Set (Polynomial ℤ_[p]))

def LTE : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ u : ℤ_[p], ‖u - 1‖ = (p : ℝ)⁻¹ → ∀ m : ℕ, 1 ≤ m →
    ‖u ^ m - 1‖ = (p : ℝ) ^ (-(1 + (padicValNat p m : ℤ)))

def TwoPoly : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ u : ℤ_[p]ˣ, ‖(u : ℤ_[p]) - 1‖ = (p : ℝ)⁻¹ →
    ∀ A : ℕ, 1 ≤ A →
    Polynomial.C ((p : ℤ_[p]) ^ (2 * A - 1 + (2 * A - 1) / (p - 1))) ∈
      Ideal.span ({∏ i ∈ range A, (Polynomial.X - Polynomial.C ((u : ℤ_[p]) ^ i)),
                   ∏ j ∈ Icc 1 A, (Polynomial.X - Polynomial.C (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ^ j))} :
        Set (Polynomial ℤ_[p]))

def RdLemma : Prop :=
  ∀ (R : Type) [CommRing R] (Z : Type) [AddCommGroup Z] [Module R Z] [NoZeroSMulDivisors R Z]
    (d : Module.End R Z) (Rp : Polynomial R) (c : R) (w w' : Z),
    Polynomial.aeval d (Polynomial.X * Rp) = 0 → c ≠ 0 → c • w = d w' →
    Rp.eval 0 • w ∈ LinearMap.range d

def LiftChase : Prop :=
  ∀ (R : Type) [CommRing R]
    (K01 K02 LastRowCutoff PoissonCutoffFormula K21 K22 : Type)
    [AddCommGroup K01] [Module R K01] [AddCommGroup K02] [Module R K02]
    [AddCommGroup LastRowCutoff] [Module R LastRowCutoff] [AddCommGroup PoissonCutoffFormula] [Module R PoissonCutoffFormula]
    [AddCommGroup K21] [Module R K21] [AddCommGroup K22] [Module R K22]
    (d0 : K01 →ₗ[R] K02) (d1 : LastRowCutoff →ₗ[R] PoissonCutoffFormula) (d2 : K21 →ₗ[R] K22)
    (ι1 : K01 →ₗ[R] LastRowCutoff) (ι2 : K02 →ₗ[R] PoissonCutoffFormula) (π1 : LastRowCutoff →ₗ[R] K21) (π2 : PoissonCutoffFormula →ₗ[R] K22),
    (∀ x, d1 (ι1 x) = ι2 (d0 x)) → (∀ x, d2 (π1 x) = π2 (d1 x)) → (∀ x, π1 (ι1 x) = 0) →
    Function.Surjective π1 → Function.Injective ι2 → LinearMap.ker π2 = LinearMap.range ι2 →
    ∀ (c : R) (y₂ : K21), d2 y₂ = 0 →
      (∀ (y₁ : LastRowCutoff) (ω : K02), π1 y₁ = y₂ → ι2 ω = d1 y₁ → c • ω ∈ LinearMap.range d0) →
      ∃ x : LastRowCutoff, d1 x = 0 ∧ π1 x = c • y₂

def EqBelow (B : ℕ) (f h : PowerSeries ℚ_[p]) : Prop :=
  ∀ j < B, PowerSeries.coeff j f = PowerSeries.coeff j h

def IntBelow (B : ℕ) (f : PowerSeries ℚ_[p]) : Prop := ∀ j < B, ‖PowerSeries.coeff j f‖ ≤ 1

def ExactContent (B : ℕ) (f : PowerSeries ℚ_[p]) (β : ℤ) : Prop :=
  (∀ j < B, ‖PowerSeries.coeff j f‖ ≤ (p : ℝ) ^ β) ∧ ∃ j < B, ‖PowerSeries.coeff j f‖ = (p : ℝ) ^ β

def DirUD : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (B : ℕ) (w w' a g : PowerSeries ℚ_[p]) (β t s : ℤ),
    w * w' = 1 → ExactContent p B w β → IntBelow p B a → IntBelow p B g → 0 < s →
    EqBelow p B (PowerSeries.C ((p : ℚ_[p]) ^ (-s)))
      (a + PowerSeries.C ((p : ℚ_[p]) ^ t) * w' * g) →
    s ≤ -t - β

def DirDD : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (B : ℕ) (w w' a g : PowerSeries ℚ_[p]) (β t s m : ℤ),
    w * w' = 1 → ExactContent p B w' β → IntBelow p B a → IntBelow p B g → s < m →
    EqBelow p B (PowerSeries.C ((p : ℚ_[p]) ^ s))
      (PowerSeries.C ((p : ℚ_[p]) ^ m) * a + PowerSeries.C ((p : ℚ_[p]) ^ t) * w * g) →
    t + β ≤ s

end Formalism.CL
end
end

-- bundled from Formalism.WachModuleLifts.StatementW
section
noncomputable section

namespace Formalism.CL.W

structure Base (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] where
  φA : A →ₐ[ℤ_[p]] A
  γA : A →ₐ[ℤ_[p]] A
  π₀ : A
  q : A
  hq : q = π₀ + algebraMap ℤ_[p] A p
  hφ : ∃ v : A, φA π₀ = π₀ * q ^ (p - 1) * v
  comm : ∀ a, φA (γA a) = γA (φA a)

variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]

structure WachMod (B : Base p A) (η : ℕ) (D : Type) [AddCommGroup D] [Module A D]
    [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D] where
  N : Submodule A D
  φ : D →ₗ[ℤ_[p]] D
  γ : D →ₗ[ℤ_[p]] D
  φ_smul : ∀ (a : A) (x : D), φ (a • x) = B.φA a • φ x
  γ_smul : ∀ (a : A) (x : D), γ (a • x) = B.γA a • γ x
  comm : ∀ x, φ (γ x) = γ (φ x)
  π₀_inj : ∀ x : D, B.π₀ • x = 0 → x = 0
  q_bij : Function.Bijective (fun x : D => B.q • x)
  φ_N : ∀ x ∈ N, B.q ^ η • φ x ∈ N
  γ_N : ∀ x ∈ N, ∃ x' ∈ N, γ x - x = B.π₀ • x'
  γ_qN : ∀ y : D, B.q ^ η • y ∈ N → ∃ y' : D, B.q ^ η • y' ∈ N ∧ γ y - y = B.π₀ • y'

namespace WachMod

variable {B : Base p A} {η : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D]
  [IsScalarTower ℤ_[p] A D] (W : WachMod B η D)

def QInv (y : D) : Prop := B.q ^ η • y ∈ W.N

def C1 (y z : D) : Prop := W.QInv y ∧ ∃ n ∈ W.N, z = B.π₀ • n

def C2 (ω : D) : Prop := ∃ y, W.QInv y ∧ ω = B.π₀ • y

def d1 (y z : D) : D := (W.γ y - y) - (W.φ z - z)

def Cocycle (y z : D) : Prop := W.C1 y z ∧ W.d1 y z = 0

def IsCob2 (ω : D) : Prop := ∃ y z, W.C1 y z ∧ ω = W.d1 y z

end WachMod

variable {B : Base p A} {η : ℕ}

structure Hom {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    [AddCommGroup D'] [Module A D'] [Module ℤ_[p] D'] [IsScalarTower ℤ_[p] A D']
    (W : WachMod B η D) (W' : WachMod B η D') where
  f : D →ₗ[A] D'
  φ_comm : ∀ x, f (W.φ x) = W'.φ (f x)
  γ_comm : ∀ x, f (W.γ x) = W'.γ (f x)
  N_le : ∀ x ∈ W.N, f x ∈ W'.N

structure SES {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[p] D₀] [IsScalarTower ℤ_[p] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[p] D₁] [IsScalarTower ℤ_[p] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[p] D₂] [IsScalarTower ℤ_[p] A D₂]
    (W₀ : WachMod B η D₀) (W₁ : WachMod B η D₁) (W₂ : WachMod B η D₂) where
  ι : Hom W₀ W₁
  π : Hom W₁ W₂
  ι_inj : Function.Injective ι.f
  exact : ∀ x, π.f x = 0 ↔ ∃ x₀, ι.f x₀ = x
  π_surj : Function.Surjective π.f
  sat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N

section Hyp

variable {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[p] D₀] [IsScalarTower ℤ_[p] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[p] D₁] [IsScalarTower ℤ_[p] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[p] D₂] [IsScalarTower ℤ_[p] A D₂]
    {W₀ : WachMod B η D₀} {W₁ : WachMod B η D₁} {W₂ : WachMod B η D₂}

def CokerKilled (S : SES W₀ W₁ W₂) (e : ℕ) : Prop :=
  ∀ n ∈ W₂.N, ∃ n₁ ∈ W₁.N, S.π.f n₁ = (p : ℤ_[p]) ^ e • n

def RatSurj (S : SES W₀ W₁ W₂) : Prop :=
  ∀ y z, W₂.Cocycle y z → ∃ k : ℕ, ∃ y₁ z₁, W₁.Cocycle y₁ z₁ ∧ ∃ x ∈ W₂.N,
    S.π.f y₁ = (p : ℤ_[p]) ^ k • y + (W₂.φ x - x) ∧ S.π.f z₁ = (p : ℤ_[p]) ^ k • z + (W₂.γ x - x)

def Lifts (S : SES W₀ W₁ W₂) (c : ℤ_[p]) : Prop :=
  ∀ y z, W₂.Cocycle y z → ∃ y₁ z₁, W₁.Cocycle y₁ z₁ ∧ S.π.f y₁ = c • y ∧ S.π.f z₁ = c • z

end Hyp

def TorsKilled {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : WachMod B η D) (c : ℤ_[p]) : Prop :=
  ∀ ω, W.C2 ω → (∃ k : ℕ, W.IsCob2 ((p : ℤ_[p]) ^ k • ω)) → W.IsCob2 (c • ω)

def LiftW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] (B : Base p A) (η : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[p] D₀] [IsScalarTower ℤ_[p] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[p] D₁] [IsScalarTower ℤ_[p] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[p] D₂] [IsScalarTower ℤ_[p] A D₂]
    (W₀ : WachMod B η D₀) (W₁ : WachMod B η D₁) (W₂ : WachMod B η D₂) (S : SES W₀ W₁ W₂)
    (e : ℕ) (c : ℤ_[p]),
    CokerKilled S e → RatSurj S → TorsKilled W₀ c → Lifts S ((p : ℤ_[p]) ^ e * c)

def ClaimW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] (B : Base p A) (η : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : WachMod B η D) (δ : D →ₗ[ℤ_[p]] D) (R : Polynomial ℤ_[p]) (a : ℕ) (cΓ : ℤ_[p]),
    η ≤ (p - 1) * (a + 1) →
    (∀ y, B.π₀ • δ y = W.γ y - y) →
    (∀ y, W.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W.N) →
    (∀ y, W.QInv y → (p : ℤ_[p]) • y ∈ W.N → y ∈ W.N) →
    cΓ ≠ 0 →
    (∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.π₀ • n) = (W.γ (B.π₀ • x) - B.π₀ • x) + B.π₀ ^ (a + 1) • z') →
    (∀ n ∈ W.N, ∃ z ∈ W.N, B.π₀ ^ (a + 1) • n = B.π₀ ^ (a + 1) • z - W.φ (B.π₀ ^ (a + 1) • z)) →
    TorsKilled W (R.eval 0 * cΓ)

def GammaOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] (B : Base p A) (η : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : WachMod B η D) (u : ℤ_[p]) (a : ℕ),
    (∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W.N, ∃ n' ∈ W.N,
      W.γ (B.π₀ ^ i • n) = u ^ i • (B.π₀ ^ i • n) + B.π₀ ^ (i + 1) • n') →
    ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      (∏ i ∈ Finset.Icc 1 a, (1 - u ^ i)) • (B.π₀ • n) =
        (W.γ (B.π₀ • x) - B.π₀ • x) + B.π₀ ^ (a + 1) • z'

def polyBase (p : ℕ) [Fact p.Prime] : Base p (Polynomial ℤ_[p]) where
  φA := Polynomial.aeval (Polynomial.X * (Polynomial.X + Polynomial.C (p : ℤ_[p])) ^ (p - 1))
  γA := AlgHom.id ℤ_[p] _
  π₀ := Polynomial.X
  q := Polynomial.X + Polynomial.C (p : ℤ_[p])
  hq := by simp [Polynomial.algebraMap_apply]
  hφ := ⟨1, by simp⟩
  comm := fun _ => rfl

def WachNonempty : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ W : WachMod (polyBase p) 0 (FractionRing (Polynomial ℤ_[p])),
    W.N ≠ ⊥ ∧ ¬ IsUnit (polyBase p).π₀

end Formalism.CL.W
end
end

