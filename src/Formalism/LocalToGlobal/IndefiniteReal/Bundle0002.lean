import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement
import Formalism.HarderNarasimhan.Bundle0002

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransfer
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement Formalism.HN

def CharFacts : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (T : Type) [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T)
    (g : G), IsIntegral ℤ (charOf τ g) ∧
      ∀ σ : K →+* ℂ, σ (charOf τ g⁻¹) = star (σ (charOf τ g)) ∧
        ‖σ (charOf τ g)‖ ≤ (finrank K T : ℝ)

def KeyZero : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [Group G] [Fintype G]
    (T : Type) [AddCommGroup T] [Module K T] (τ : Representation K G T)
    (V : Type) [AddCommGroup V] [Module K V] (ρ : Representation K G V) (a : MonoidAlgebra K G),
    τ.asAlgebraHom a = 0 → eS τ ρ ∘ₗ ρ.asAlgebraHom a = 0

def Schur : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s)), IsGood τ →
    (∀ s, eS (τ s) (τ s) = LinearMap.id) ∧ (∀ s t, s ≠ t → eS (τ s) (τ t) = 0) ∧
      ∀ s, ∑ x : G, charOf (τ s) x⁻¹ * charOf (τ s) x = (Fintype.card G : K)

def DimSq : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s)), IsGood τ →
    ∀ s, finrank K (T s) ^ 2 ≤ Fintype.card G ∧
      ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ), nS (τ s) H χ ^ 2 ≤ Fintype.card G

def IdemE : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s)), IsGood τ →
    ∀ (V : Type) [AddCommGroup V] [Module K V] (ρ : Representation K G V),
      (∀ s, eS (τ s) ρ ∘ₗ eS (τ s) ρ = eS (τ s) ρ) ∧
      (∀ s t, s ≠ t → eS (τ s) ρ ∘ₗ eS (τ t) ρ = 0)

def IdemP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (ρ : Representation K G V),
    (∀ (T : Type) [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T),
      (∀ g : G, eS τ ρ ∘ₗ ρ g = ρ g ∘ₗ eS τ ρ) ∧
      (∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ), eS τ ρ ∘ₗ epP H χ ρ = epP H χ ρ ∘ₗ eS τ ρ) ∧
      ∀ A : Submodule (𝓞 K) V, (∀ g : G, ∀ a ∈ A, ρ g a ∈ A) →
        ∀ a ∈ A, (Fintype.card G : 𝓞 K) • eS τ ρ a ∈ A) ∧
    ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ),
      epP H χ ρ ∘ₗ epP H χ ρ = epP H χ ρ ∧
      ∀ A : Submodule (𝓞 K) V, (∀ g : G, ∀ a ∈ A, ρ g a ∈ A) →
        ∀ a ∈ A, (Fintype.card G : 𝓞 K) • epP H χ ρ a ∈ A

def CoreData {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
    {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) {n : ℕ}
    (γ δ : Fin n → G) (c : Matrix (Fin n) (Fin n) K) (Γ : Matrix (Fin n) (Fin n) (𝓞 K)) : Prop :=
  c.det ≠ 0 ∧ (∀ i j, ((Γ i j : 𝓞 K) : K) = (Fintype.card G : K) ^ 2 * c i j) ∧
  (∀ i j (σ : K →+* ℂ), ‖σ (c i j)‖ ≤ (finrank K T : ℝ)) ∧
  ∀ (V : Type) [AddCommGroup V] [Module K V] (ρ : Representation K G V),
    (∀ i j, ∀ a : V, epP H₀ χ₀ ρ (eS τ ρ a) = a →
      epP H₀ χ₀ ρ (ρ (δ i) (epP H χ ρ (ρ (γ j) a))) = c i j • a) ∧
    (∀ a : V, epP H χ ρ (eS τ ρ a) = a →
      ∑ j, ∑ i, c⁻¹ j i • epP H χ ρ (ρ (γ j) (epP H₀ χ₀ ρ (ρ (δ i) a))) = a)

def Core : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s))
    (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ),
    IsGood τ → M1 τ H₀ χ₀ → ∀ s,
      ∃ (γ δ : Fin (nS (τ s) H χ) → G) (c : Matrix (Fin (nS (τ s) H χ)) (Fin (nS (τ s) H χ)) K)
        (Γ : Matrix (Fin (nS (τ s) H χ)) (Fin (nS (τ s) H χ)) (𝓞 K)),
        CoreData (τ s) H₀ χ₀ H χ γ δ c Γ

def Metric : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V),
    (∀ v, IsUnit (X v).det) → IsUnitaryRep b X ρ →
    (∀ (T : Type) [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T)
      (v : InfinitePlace K) (x y : V),
      Formalism.HermitianLatticesTheory.majAt b X v (eS τ ρ x) y = Formalism.HermitianLatticesTheory.majAt b X v x (eS τ ρ y)) ∧
    ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (g : G) (v : InfinitePlace K),
      opNormAt b X b X v (epP H χ ρ ∘ₗ ρ g) ≤ 1

def UnitOfNorm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V),
    (∀ (g : G) (v : InfinitePlace K) (x : V),
      Formalism.HermitianLatticesTheory.normAt b X v (ρ g x) = Formalism.HermitianLatticesTheory.normAt b X v x) → IsUnitaryRep b X ρ

def LiftChar : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (H : Type) [Group H] [Finite H] (χ : H →* Kˣ),
    ∃ χ' : H →* (𝓞 K)ˣ, ∀ h, (((χ' h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((χ h : Kˣ) : K)

def AllPartsTransfer : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] (G : Type) [Group G]
    [Fintype G] (S : Type) [Fintype S] (T : S → Type) [∀ s, AddCommGroup (T s)]
    [∀ s, Module K (T s)] [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s))
    (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ),
    IsGood τ → M1 τ H₀ χ₀ →
      ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
        (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
        (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V),
        (∀ v, IsUnit (X v).det) → IsUnitaryRep b X ρ →
        ∀ A : Submodule (𝓞 K) V, IsGLat ρ A → TransferLatticeConditions τ H₀ χ₀ H χ b X ρ A

def matAct {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}
    (Γ : Matrix (Fin n) (Fin n) K) : (Fin n → V) →ₗ[K] (Fin n → V) :=
  LinearMap.pi fun i => ∑ j, Γ i j • LinearMap.proj j

def IdxBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    (∀ M N P : Submodule (𝓞 K) V, M.FG → N.FG → P.FG →
      Submodule.span K (M : Set V) = Submodule.span K (N : Set V) →
      Submodule.span K (N : Set V) = Submodule.span K (P : Set V) →
      idxW w M N + idxW w N P = idxW w M P) ∧
    (∀ M N : Submodule (𝓞 K) V, N ≤ M → 0 ≤ idxW w M N) ∧
    (∀ (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
      (φ : V →ₗ[K] W) (M N : Submodule (𝓞 K) V),
      Submodule.span K (M : Set V) = Submodule.span K (N : Set V) →
      Set.InjOn φ (Submodule.span K (M : Set V) : Set V) →
      idxW w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) = idxW w M N) ∧
    (∀ (S : Type) [Fintype S] (M N : S → Submodule (𝓞 K) V), (∀ s, (M s).FG) → (∀ s, (N s).FG) →
      (∀ s, Submodule.span K (M s : Set V) = Submodule.span K (N s : Set V)) →
      iSupIndep (fun s => Submodule.span K (M s : Set V)) →
      idxW w (⨆ s, M s) (⨆ s, N s) = ∑ s, idxW w (M s) (N s)) ∧
    (∀ (n : ℕ) (M N : Submodule (𝓞 K) V), M.FG → N.FG →
      Submodule.span K (M : Set V) = Submodule.span K (N : Set V) →
      idxW w (Submodule.pi Set.univ fun _ : Fin n => M) (Submodule.pi Set.univ fun _ : Fin n => N) =
        n * idxW w M N)

def IdxDet : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (M : Submodule (𝓞 K) V), M.FG →
    (∀ d : 𝓞 K, d ≠ 0 →
      idxW w M (M.map ((((d : K) • LinearMap.id : V →ₗ[K] V)).restrictScalars (𝓞 K))) =
        (rkK M : ℤ) * vW w d) ∧
    ∀ (n : ℕ) (Γ : Matrix (Fin n) (Fin n) (𝓞 K)), Γ.det ≠ 0 →
      idxW w (Submodule.pi Set.univ fun _ : Fin n => M)
        ((Submodule.pi Set.univ fun _ : Fin n => M).map
          ((matAct (V := V) (Γ.map (algebraMap (𝓞 K) K))).restrictScalars (𝓞 K))) =
        (rkK M : ℤ) * vW w Γ.det

def ProdFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ lW w) ∧
    (∀ d : 𝓞 K, d ≠ 0 → {w : HeightOneSpectrum (𝓞 K) | vW w d ≠ 0}.Finite ∧
      meanLog d = ∑ᶠ w : HeightOneSpectrum (𝓞 K), lW w * (vW w d : ℝ)) ∧
    ∀ N : ℕ, 0 < N → meanLog (N : 𝓞 K) = Real.log N

def GammaBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n N : ℕ) (Γ : Matrix (Fin n) (Fin n) (𝓞 K)),
    0 < N → n ^ 2 ≤ N → Γ.det ≠ 0 →
    (∀ i j (σ : K →+* ℂ), ‖σ ((Γ i j : 𝓞 K) : K)‖ ≤ (N : ℝ) ^ 3) → GammaOK Γ (Real.log N)

end Formalism.IndefR.LatticeTransfer
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.IndefiniteEpsilonOperator
section
open Module NumberField

noncomputable section

namespace Formalism.IndefR.IndefiniteEpsilonOperator

structure Pair (G K : Type) [Group G] [Field K] where

  H : Subgroup G

  χ : H →* Kˣ

section Ops

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module K U]

def epOp [Finite G] (σ : Representation K G U) (P : Pair G K) : U →ₗ[K] U :=
  letI : Fintype P.H := Fintype.ofFinite P.H
  (Nat.card P.H : K)⁻¹ • ∑ h : P.H, ((P.χ h⁻¹ : Kˣ) : K) • σ (h : G)

def epSp [Finite G] (σ : Representation K G U) (P : Pair G K) : Submodule K U :=
  LinearMap.range (epOp σ P)

def charOf (σ : Representation K G U) (g : G) : K :=
  LinearMap.trace K U (σ g)

def eOp [Fintype G] {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W)
    (ρ : Representation K G U) : U →ₗ[K] U :=
  (charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, charOf τ x⁻¹ • ρ x

def nOf [Finite G] {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W)
    (P : Pair G K) : ℕ :=
  finrank K (epSp τ P)

end Ops

def la (G : Type) [Fintype G] : ℝ := Real.log (Fintype.card G)

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  [Fintype κ] [DecidableEq κ]

def latAt {G : Type} [Group G] [Finite G] (ρ : Representation K G V) (A : Submodule (𝓞 K) V)
    (P : Pair G K) : Submodule (𝓞 K) V :=
  A ⊓ (epSp ρ P).restrictScalars (𝓞 K)

def HtLe (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (φ : V →ₗ[K] W) (U : Submodule K V) (t : ℝ) : Prop :=
  ∃ c : InfinitePlace K → ℝ, (∀ v, 0 < c v) ∧
    (∀ v, ∀ x ∈ U, Formalism.HermitianLatticesTheory.normAt b' X' v (φ x) ≤ c v * Formalism.HermitianLatticesTheory.normAt b X v x) ∧
    (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (c v ^ 2) ≤ t

def CKa (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (RPl : Submodule (𝓞 K) V)
    (bP : Basis κ K W) (XP : InfinitePlace K → Matrix κ κ ℂ) (RP : Submodule (𝓞 K) W) (t : ℝ) :
    Prop :=
  (∀ v, IsUnit (XP v).det) ∧ RP.FG ∧ Submodule.span K (RP : Set W) = ⊤ ∧
  (∃ φ : W →ₗ[K] V, (∀ x ∈ RP, φ x ∈ RPl) ∧ Set.InjOn φ (RP : Set W) ∧
    HtLe bP XP b X φ (Submodule.span K (RP : Set W)) t) ∧
  (∃ ψ : V →ₗ[K] W, (∀ x ∈ RPl, ψ x ∈ RP) ∧ Set.InjOn ψ (RPl : Set V) ∧
    HtLe b X bP XP ψ (Submodule.span K (RPl : Set V)) t)

def muDual (bP : Basis κ K W) (XP : InfinitePlace K → Matrix κ κ ℂ) (RP : Submodule (𝓞 K) W) : ℝ :=
  Formalism.HN.muDef bP.dualBasis (Formalism.HN.dualFrame XP) (Formalism.HN.dualLat RP)

structure GoodTransferSetting {G : Type} [Group G] [Fintype G] {S : Type} [Fintype S] {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V)
    (R : Submodule (𝓞 K) V) (τ : ∀ s, Representation K G (Ws s)) : Prop where

  frame : ∀ v, IsUnit (X v).det

  fg : R.FG

  span : Submodule.span K (R : Set V) = ⊤

  ne_bot : R ≠ ⊥

  roots : ∃ ζ : K, IsPrimitiveRoot ζ (Fintype.card G)

  stable : ∀ g : G, ∀ x ∈ R, ρ g x ∈ R

  unitary : ∀ (g : G) (v : InfinitePlace K) (x : V),
    Formalism.HermitianLatticesTheory.normAt b X v (ρ g x) = Formalism.HermitianLatticesTheory.normAt b X v x

  irred : ∀ s, (τ s).IsIrreducible

  split : ∀ s (f : Ws s →ₗ[K] Ws s), (∀ g, f ∘ₗ τ s g = τ s g ∘ₗ f) → ∃ c : K, f = c • LinearMap.id

  distinct : Function.Injective fun s => charOf (τ s)

  good : ∀ x : V, (∑ s, eOp (τ s) ρ) x = x

end Lat

def M1 {K : Type} [Field K] {G : Type} [Group G] [Finite G] {S : Type} {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] (τ : ∀ s, Representation K G (Ws s))
    (P0 : Pair G K) : Prop :=
  ∀ s, nOf (τ s) P0 = 1

def M2 {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V]
    [Module K V] {S : Type} {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (ρ : Representation K G V) (τ : ∀ s, Representation K G (Ws s)) (P1 : Pair G K)
    (nbar de : ℝ) : Prop :=
  ∀ s, LinearMap.range (eOp (τ s) ρ) ≠ ⊥ →
    (1 - de) * nbar ≤ (nOf (τ s) P1 : ℝ) ∧ (nOf (τ s) P1 : ℝ) ≤ (1 + de) * nbar

def Lemma5Prime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [IsGalois ℚ K]
    (V ι : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (G : Type) [Group G] [Fintype G] (ρ : Representation K G V) (R : Submodule (𝓞 K) V)
    (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s))
    (P0 P1 : Pair G K) (nbar de ka HH0 : ℝ)
    (W0 ι0 : Type) [AddCommGroup W0] [Module K W0] [Module (𝓞 K) W0] [IsScalarTower (𝓞 K) K W0]
    [Fintype ι0] [DecidableEq ι0] (b0 : Basis ι0 K W0) (X0 : InfinitePlace K → Matrix ι0 ι0 ℂ)
    (R0 : Submodule (𝓞 K) W0)
    (W1 ι1 : Type) [AddCommGroup W1] [Module K W1] [Module (𝓞 K) W1] [IsScalarTower (𝓞 K) K W1]
    [Fintype ι1] [DecidableEq ι1] (b1 : Basis ι1 K W1) (X1 : InfinitePlace K → Matrix ι1 ι1 ℂ)
    (R1 : Submodule (𝓞 K) W1),
    GoodTransferSetting b X ρ R τ →
    M1 τ P0 →
    0 < nbar → 0 ≤ de → de ≤ 1 / 3 →
    M2 ρ τ P1 nbar de →
    0 ≤ ka →
    CKa b X (latAt ρ R P0) b0 X0 R0 (ka * la G) →
    CKa b X (latAt ρ R P1) b1 X1 R1 (ka * la G) →
    Formalism.HN.muMaxDef b0 X0 R0 ≤ HH0 →
    Formalism.HN.muMaxDef b1 X1 R1 ≤ HH0 + (8.5 + 2 * ka) * la G ∧
      muDual b1 X1 R1 ≤ muDual b0 X0 R0 + 3 * de * (muDual b0 X0 R0 + HH0 + (2 * ka + 2) * la G) +
        (2 * ka + 10.5) * la G ∧
      0 ≤ muDual b0 X0 R0 + HH0 + (2 * ka + 2) * la G

end Formalism.IndefR.IndefiniteEpsilonOperator
end
end

