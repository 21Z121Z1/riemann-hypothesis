import Mathlib

-- bundled from Formalism.SmithDeterminants.StatementDVR
section
open Finset

noncomputable section

namespace Formalism.A

def mulRange {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (c : R) :
    Submodule R M :=
  LinearMap.range (c • (LinearMap.id : M →ₗ[R] M))

structure SmithData {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (y : M →ₗ[R] M) (d : ℕ) where
  b : Module.Basis (Fin d) R M
  b' : Module.Basis (Fin d) R M
  a : Fin d → R
  hy : ∀ i, y (b i) = a i • b' i

open Classical in

def SmithData.nAbove {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {y : M →ₗ[R] M} {d : ℕ} (S : SmithData y d) (ϖ : R) (t : ℕ) : ℕ :=
  (univ.filter fun i => ¬ S.a i ∣ ϖ ^ t).card

open Classical in

def SmithData.nBetween {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {y : M →ₗ[R] M} {d : ℕ} (S : SmithData y d) (ϖ : R) (t E : ℕ) : ℕ :=
  (univ.filter fun i => ¬ S.a i ∣ ϖ ^ t ∧ S.a i ∣ ϖ ^ E).card

def chain {K : Type*} [Field K] {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (θ : ∀ i, V i →ₗ[K] V (i + 1)) : ∀ m, V 0 →ₗ[K] V m
  | 0 => LinearMap.id
  | m + 1 => (θ m).comp (chain θ m)

def TruncHyp (O K : Type) [CommRing O] [Field K] [Algebra O K] (V : ℕ → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module O (V i)]
    [∀ i, IsScalarTower O K (V i)]
    (M : ∀ i, Submodule O (V i)) (E : ∀ i, Submodule K (V i)) (y T : ∀ i, V i →ₗ[K] V i)
    (θ : ∀ i, V i →ₗ[K] V (i + 1)) (ϖ : O) (c : ℕ → O) (e f s' : ℕ → ℤ) : Prop :=
  algebraMap O K ϖ ≠ 0 ∧
  (∀ i, ∀ v ∈ E i, y i v ∈ E i) ∧
  (∀ i, ∀ v ∈ E i, θ i v ∈ E (i + 1)) ∧
  (∀ i, ∀ v ∈ E i, θ i (y i v) = y (i + 1) (θ i v)) ∧

  (∀ i, ∀ v ∈ M i, θ i v ∈ M (i + 1)) ∧

  (∀ i, ∀ v ∈ M i, ∃ w ∈ M (i + 1), θ i (T i v) = (algebraMap O K ϖ) ^ (s' i) • w) ∧
  (∀ i, ∀ v ∈ E i, T i v = (algebraMap O K ϖ) ^ (e i) • y i v +
      ((algebraMap O K ϖ) ^ (f i) * algebraMap O K (c i)) • v) ∧
  (∀ i, s' i ≤ f i)

def LatticeChainBound : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (V : ℕ → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module O (V i)]
    [∀ i, IsScalarTower O K (V i)]
    (M : ∀ i, Submodule O (V i)) (E : ∀ i, Submodule K (V i)) (y T : ∀ i, V i →ₗ[K] V i)
    (θ : ∀ i, V i →ₗ[K] V (i + 1)) (ϖ : O) (c : ℕ → O) (e f s' : ℕ → ℤ),
    TruncHyp O K V M E y T θ ϖ c e f s' →
    ∀ m : ℕ, ∀ φ ∈ M 0, φ ∈ E 0 →
      ∃ w ∈ M m, chain θ m ((y 0 ^ m) φ) =
        (algebraMap O K ϖ) ^ (∑ i ∈ range m, (s' i - e i)) • w

def LatticeChainBoundNonneg : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (V : ℕ → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module O (V i)]
    [∀ i, IsScalarTower O K (V i)]
    (M : ∀ i, Submodule O (V i)) (E : ∀ i, Submodule K (V i)) (y T : ∀ i, V i →ₗ[K] V i)
    (θ : ∀ i, V i →ₗ[K] V (i + 1)) (ϖ : O) (c : ℕ → O) (e f s' : ℕ → ℤ),
    TruncHyp O K V M E y T θ ϖ c e f s' →
    (∀ v ∈ M 0, y 0 v ∈ M 0) →
    ∀ m : ℕ, ∀ φ ∈ M 0, φ ∈ E 0 →
      ∃ w ∈ M m, chain θ m ((y 0 ^ m) φ) =
        (algebraMap O K ϖ) ^ (∑ i ∈ range m, max (s' i - e i) 0) • w

def RangePowGenerators : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (y : M →ₗ[R] M) (π : R)
    (t n : ℕ) (g : Fin n → M),
    mulRange (M := M) (π ^ t) ≤ LinearMap.range y ⊔ Submodule.span R (Set.range g) →
    ∀ j : ℕ, ∃ gj : Fin (j * n) → M,
      mulRange (M := M) (π ^ (j * t)) ≤
        LinearMap.range (y ^ j) ⊔ Submodule.span R (Set.range gj)

def SmithGen : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (y : M →ₗ[R] M) (d : ℕ)
    (Sd : SmithData y d) (ϖ : R) (t : ℕ),
    ∃ g : Fin (Sd.nAbove ϖ t) → M,
      mulRange (M := M) (ϖ ^ t) ≤ LinearMap.range y ⊔ Submodule.span R (Set.range g)

def LengthQuotientBound : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (ϖ : R), Irreducible ϖ →
    ∀ (y : M →ₗ[R] M) (t n S m : ℕ) (g : Fin n → M),
    mulRange (M := M) (ϖ ^ t) ≤ LinearMap.range y ⊔ Submodule.span R (Set.range g) →
    Module.length R (M ⧸ (LinearMap.range (y ^ m) ⊔ mulRange (M := M) (ϖ ^ S))) ≤
      ((Module.finrank R M * m * t + m * n * S : ℕ) : ℕ∞)

def TruncDet : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] (ϖ : R), Irreducible ϖ →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) R M) (L : M →ₗ[R] (Fin d → R)) (Λ : Submodule R M)
      (S ℓ : ℕ),
    (∀ v ∈ Λ, ∃ w : Fin d → R, L v = ϖ ^ S • w) →
    Module.length R (M ⧸ Λ) ≤ (ℓ : ℕ∞) →
    ϖ ^ (d * S) ∣ ϖ ^ ℓ * (LinearMap.toMatrix b (Pi.basisFun R (Fin d)) L).det

def TruncFinal : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] (ϖ : R), Irreducible ϖ →
    ∀ (y : M →ₗ[R] M) (d : ℕ) (Sd : SmithData y d) (L : M →ₗ[R] (Fin d → R)) (t S m : ℕ),
    (∀ v : M, ∃ w : Fin d → R, L ((y ^ m) v) = ϖ ^ S • w) →
    ϖ ^ (d * S) ∣ ϖ ^ (d * m * t + m * Sd.nAbove ϖ t * S) *
      (LinearMap.toMatrix Sd.b (Pi.basisFun R (Fin d)) L).det

def TwoTier : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] (ϖ : R), Irreducible ϖ →
    ∀ (y : M →ₗ[R] M) (d : ℕ) (Sd : SmithData y d) (t E G m : ℕ),
    Module.length R (M ⧸ (LinearMap.range (y ^ m) ⊔ mulRange (M := M) (ϖ ^ G))) ≤
      ((m * (d * t + Sd.nBetween ϖ t E * E + Sd.nAbove ϖ E * G) : ℕ) : ℕ∞)

def SatChain : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] (ϖ : R), Irreducible ϖ →
    ∀ (y : M →ₗ[R] M) (d : ℕ) (Sd : SmithData y d) (t r : ℕ),
    ∃ A : Submodule R M, (∀ v : M, ϖ • v ∈ A → v ∈ A) ∧
      Module.finrank R (M ⧸ A) ≤ r * Sd.nAbove ϖ t ∧
      ∀ v ∈ A, ϖ ^ (r * t) • v ∈ LinearMap.range (y ^ r)

def GradedHorn : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] (ϖ : R), Irreducible ϖ →
    ∀ (y : M →ₗ[R] M) (d : ℕ) (Sd : SmithData y d) (m g : ℕ),
    Module.length R (M ⧸ (LinearMap.range (y ^ m) ⊔ mulRange (M := M) (ϖ ^ (m * g)))) ≤
      ((m * ∑ j ∈ range g, min d (m * Sd.nAbove ϖ j) : ℕ) : ℕ∞) ∧
    ∀ t₀ : ℕ,
    Module.length R (M ⧸ (LinearMap.range (y ^ m) ⊔ mulRange (M := M) (ϖ ^ (m * g)))) ≤
      ((m * (d * t₀ + m * ∑ j ∈ Ico t₀ g, Sd.nAbove ϖ j) : ℕ) : ℕ∞)

def SmithExists : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (y : M →ₗ[R] M),
    Nonempty (SmithData y (Module.finrank R M))

end Formalism.A
end
end

-- bundled from Formalism.SmithDeterminants.StatementGram
section
open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.A

def mfact {σ : Type*} (g : σ →₀ ℕ) : ℕ := g.prod fun _ n => n.factorial

def fockZ {σ : Type*} (f g : MvPolynomial σ ℤ) : ℤ :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (mfact m : ℤ)

def gramZ {σ ι : Type*} (f : ι → MvPolynomial σ ℤ) : Matrix ι ι ℤ :=
  fun a b => fockZ (f a) (f b)

def l1Z {σ : Type*} (f : MvPolynomial σ ℤ) : ℤ := ∑ m ∈ f.support, |f.coeff m|

def famZ {σ ι : Type*} (E : ι → MvPolynomial σ ℤ) (α : ι → (σ →₀ ℕ)) (a : ι) :
    MvPolynomial σ ℤ :=
  E a * MvPolynomial.monomial (α a) 1

def fockG {σ : Type*} (f g : MvPolynomial σ GaussianInt) : GaussianInt :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * (mfact m : GaussianInt)

def gramG {σ ι : Type*} (f : ι → MvPolynomial σ GaussianInt) : Matrix ι ι GaussianInt :=
  fun a b => fockG (f a) (f b)

def l1G {σ : Type*} (f : MvPolynomial σ GaussianInt) : ℝ :=
  ∑ m ∈ f.support, ‖GaussianInt.toComplex (f.coeff m)‖

def famG {σ ι : Type*} (E : ι → MvPolynomial σ GaussianInt) (α : ι → (σ →₀ ℕ)) (a : ι) :
    MvPolynomial σ GaussianInt :=
  E a * MvPolynomial.monomial (α a) 1

def GramZ : Prop :=
  ∀ (k s : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (E : ι → MvPolynomial (Fin k) ℤ) (e : ι → ℕ) (α : ι → (Fin k →₀ ℕ)),
    (∀ a, (E a).IsHomogeneous (e a)) →
    (∀ a, Finsupp.degree (α a) + e a = s) →
    (∀ a, l1Z (E a) ≤ (k : ℤ) ^ (e a)) →
    LinearIndependent ℤ (famZ E α) →
    (∀ a b, (mfact (α a) : ℤ) ∣ gramZ (famZ E α) a b) ∧
    ((gramZ (famZ E α)).map (Int.cast : ℤ → ℝ)).PosDef ∧
    0 < (gramZ (famZ E α)).det ∧
    (gramZ (famZ E α)).det ≤ ∏ a, gramZ (famZ E α) a a ∧
    (∀ a, gramZ (famZ E α) a a ≤ (mfact (α a) : ℤ) * ((k : ℤ) ^ 2 * s) ^ (e a)) ∧
    (∏ a, (mfact (α a) : ℤ)) ∣ (gramZ (famZ E α)).det ∧
    0 < (gramZ (famZ E α)).det / ∏ a, (mfact (α a) : ℤ) ∧
    (gramZ (famZ E α)).det / ∏ a, (mfact (α a) : ℤ) ≤ ∏ a, ((k : ℤ) ^ 2 * s) ^ (e a) ∧
    (∀ p : ℕ, p.Prime →
      (padicValInt p (gramZ (famZ E α)).det : ℝ) ≤
        ∑ a, ((padicValNat p (mfact (α a)) : ℝ) +
          (e a : ℝ) * Real.log ((k : ℝ) ^ 2 * s) / Real.log p)) ∧
    (∀ a, mfact (α a) ∣ s.factorial)

def GramGauss : Prop :=
  ∀ (k s : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (E : ι → MvPolynomial (Fin k) GaussianInt) (e : ι → ℕ) (α : ι → (Fin k →₀ ℕ)),
    (∀ a, (E a).IsHomogeneous (e a)) →
    (∀ a, Finsupp.degree (α a) + e a = s) →
    (∀ a, l1G (E a) ≤ (k : ℝ) ^ (e a)) →
    LinearIndependent GaussianInt (famG E α) →
    (∀ a b, (mfact (α a) : GaussianInt) ∣ gramG (famG E α) a b) ∧
    ((gramG (famG E α)).map GaussianInt.toComplex).PosDef ∧
    (∀ a, (gramG (famG E α) a a).im = 0 ∧
      (gramG (famG E α) a a).re ≤ (mfact (α a) : ℤ) * ((k : ℤ) ^ 2 * s) ^ (e a)) ∧
    ∃ N : ℤ, (gramG (famG E α)).det = (N : GaussianInt) ∧ 0 < N ∧
      N ≤ ∏ a, (gramG (famG E α) a a).re ∧
      (∏ a, (mfact (α a) : ℤ)) ∣ N ∧
      0 < N / ∏ a, (mfact (α a) : ℤ) ∧
      N / ∏ a, (mfact (α a) : ℤ) ≤ ∏ a, ((k : ℤ) ^ 2 * s) ^ (e a) ∧
      (∀ p : ℕ, p.Prime →
        (padicValInt p N : ℝ) ≤
          ∑ a, ((padicValNat p (mfact (α a)) : ℝ) +
            (e a : ℝ) * Real.log ((k : ℝ) ^ 2 * s) / Real.log p))

end Formalism.A
end
end

