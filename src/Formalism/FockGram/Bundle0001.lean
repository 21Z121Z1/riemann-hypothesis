import Formalism.SmithDeterminants.Bundle0001
import Formalism.FockGram.StatementLat

-- bundled from Formalism.FockGram.StatementFock
section
open Finset Matrix MvPolynomial

noncomputable section

namespace Formalism.E

def fock {R τ : Type*} [CommRing R] [StarRing R] (f g : MvPolynomial τ R) : R :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)

def fockGram {R τ ι : Type*} [CommRing R] [StarRing R] (v : ι → MvPolynomial τ R) :
    Matrix ι ι R :=
  Matrix.of fun i j => fock (v i) (v j)

def symMono {R σ τ : Type*} [CommRing R] {a : ℕ} (e : σ → MvPolynomial τ R) (s : Sym σ a) :
    MvPolynomial τ R :=
  ((s : Multiset σ).map e).prod

def symFact {σ : Type*} [DecidableEq σ] {a : ℕ} (s : Sym σ a) : ℕ :=
  Formalism.A.mfact (Multiset.toFinsupp (s : Multiset σ))

def symPow {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] (a : ℕ) (A : Matrix σ σ R) :
    Matrix (Sym σ a) (Sym σ a) R :=
  Matrix.of fun s t => coeff (Multiset.toFinsupp (t : Multiset σ))
    (((s : Multiset σ).map fun i => ∑ j, C (A i j) * X j).prod)

def symGram {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] (a : ℕ)
    (G : Matrix σ σ R) : Matrix (Sym σ a) (Sym σ a) R :=
  symPow a G * Matrix.diagonal fun t => (symFact t : R)

def FockSesq : Prop :=
  ∀ (R τ : Type) [CommRing R] [StarRing R],
    ∃ B : MvPolynomial τ R →ₗ[R] MvPolynomial τ R →ₗ⋆[R] R, ∀ f g, B f g = fock f g

def FockHerm : Prop :=
  ∀ (R τ : Type) [CommRing R] [StarRing R] (f g : MvPolynomial τ R),
    star (fock f g) = fock g f

def FockBridge : Prop :=
  (∀ (τ : Type) (f g : MvPolynomial τ ℤ), Formalism.A.fockZ f g = fock f g) ∧
  (∀ (τ : Type) (f g : MvPolynomial τ GaussianInt), Formalism.A.fockG f g = fock f g)

def FockPerm : Prop :=
  ∀ (R τ : Type) [CommRing R] [StarRing R] (a : ℕ) (x y : Fin a → MvPolynomial τ R),
    (∀ s, (x s).IsHomogeneous 1) → (∀ t, (y t).IsHomogeneous 1) →
    fock (∏ s, x s) (∏ t, y t) = (Matrix.of fun s t => fock (x s) (y t)).permanent

def FockGramSym : Prop :=
  ∀ (R σ τ : Type) [CommRing R] [StarRing R] [Fintype σ] [DecidableEq σ] (a : ℕ)
    (e : σ → MvPolynomial τ R), (∀ i, (e i).IsHomogeneous 1) →
    fockGram (symMono (a := a) e) = symGram a (fockGram e)

def DetSymPow : Prop :=
  ∀ (R σ : Type) [CommRing R] [Fintype σ] [DecidableEq σ] (a : ℕ) (A : Matrix σ σ R),
    (symPow a A).det = A.det ^ (Fintype.card σ + a - 1).choose (Fintype.card σ)

def DetSymGram : Prop :=
  ∀ (R σ : Type) [CommRing R] [Fintype σ] [DecidableEq σ] (a : ℕ) (G : Matrix σ σ R),
    (symGram a G).det =
      G.det ^ (Fintype.card σ + a - 1).choose (Fintype.card σ) * ∏ t : Sym σ a, (symFact t : R)

def DetFockSym : Prop :=
  ∀ (R σ τ : Type) [CommRing R] [StarRing R] [Fintype σ] [DecidableEq σ] (a : ℕ)
    (e : σ → MvPolynomial τ R), (∀ i, (e i).IsHomogeneous 1) →
    (fockGram (symMono (a := a) e)).det =
      (fockGram e).det ^ (Fintype.card σ + a - 1).choose (Fintype.card σ) *
        ∏ t : Sym σ a, (symFact t : R)

def FockStd : Prop :=
  ∀ (R σ : Type) [CommRing R] [StarRing R] [Fintype σ] [DecidableEq σ] (a : ℕ),
    fockGram (symMono (a := a) (X : σ → MvPolynomial σ R)) =
      Matrix.diagonal (fun t => (symFact t : R)) ∧
    (fockGram (symMono (a := a) (X : σ → MvPolynomial σ R))).det =
      ∏ t : Sym σ a, (symFact t : R)

end Formalism.E
end
end

-- bundled from Formalism.FockGram.StatementHerm
section
open Matrix LinearMap Module

noncomputable section

namespace Formalism.E

def hdual {S K V : Type*} [CommRing S] [Field K] [StarRing K] [Algebra S K] [AddCommGroup V]
    [Module K V] [Module S V] [IsScalarTower S K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule S V) : Submodule S V :=
  ⨅ y ∈ L, (1 : Submodule S K).comap ((B y).restrictScalars S)

def HermDual : Prop :=
  ∀ (S K V ι : Type) [CommRing S] [Field K] [StarRing K] [Algebra S K]
    [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower S K V] [Fintype ι] [DecidableEq ι]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V),
    Function.Injective (algebraMap S K) →
    (∀ s : S, star (algebraMap S K s) ∈ Set.range (algebraMap S K)) →
    (Submodule.span S (Set.range b) ≤ hdual B (Submodule.span S (Set.range b)) ↔
      ∀ i j, B (b i) (b j) ∈ Set.range (algebraMap S K)) ∧
    ∀ [Module.Free ℤ S] [Module.Finite ℤ S] (GS : Matrix ι ι S),
      (∀ i j, B (b i) (b j) = algebraMap S K (GS i j)) → GS.det ≠ 0 →
      (Submodule.span S (Set.range b)).toAddSubgroup.relIndex
          (hdual B (Submodule.span S (Set.range b))).toAddSubgroup =
        (Algebra.norm ℤ GS.det).natAbs ∧
      (hdual B (Submodule.span S (Set.range b)) = Submodule.span S (Set.range b) ↔
        IsUnit GS.det)

def HermTraceGram : Prop :=
  ∀ (S M ι κ : Type) [CommRing S] [StarRing S] [AddCommGroup M] [Module S M]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : M →ₗ⋆[S] M →ₗ[S] S) (b : Basis ι S M) (ω : Basis κ ℤ S),
    (Matrix.of fun p q : ι × κ => Algebra.trace ℤ S (B (ω p.2 • b p.1) (ω q.2 • b q.1))).det =
      (Matrix.of fun k l : κ => Algebra.trace ℤ S (star (ω k) * ω l)).det ^ Fintype.card ι *
        Algebra.norm ℤ (sgram B b).det

end Formalism.E
end
end

-- bundled from Formalism.FockGram.StatementTensor
section
open Matrix LinearMap Module TensorProduct

noncomputable section

namespace Formalism.E

def tensorFunctional (R M₁ M₂ : Type*) [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] :
    (M₁ →ₗ[R] R) →ₗ[R] (M₂ →ₗ[R] R) →ₗ[R] (M₁ ⊗[R] M₂ →ₗ[R] R) :=
  (TensorProduct.mapBilinear (RingHom.id R) M₁ M₂ R R).compr₂
    (LinearMap.llcomp R (M₁ ⊗[R] M₂) (R ⊗[R] R) R (TensorProduct.lid R R).toLinearMap)

def htmul {R M₁ M₂ : Type*} [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R) :
    (M₁ ⊗[R] M₂) →ₗ⋆[R] (M₁ ⊗[R] M₂) →ₗ[R] R :=
  TensorProduct.lift (((tensorFunctional R M₁ M₂).comp B₁).compl₂ B₂)

def HTmulApply : Prop :=
  ∀ (R M₁ M₂ : Type) [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R)
    (x₁ y₁ : M₁) (x₂ y₂ : M₂),
    htmul B₁ B₂ (x₁ ⊗ₜ x₂) (y₁ ⊗ₜ y₂) = B₁ x₁ y₁ * B₂ x₂ y₂

def HTmulGram : Prop :=
  ∀ (R M₁ M₂ ι₁ ι₂ : Type) [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R) (v₁ : ι₁ → M₁) (v₂ : ι₂ → M₂),
    sgram (htmul B₁ B₂) (fun p : ι₁ × ι₂ => v₁ p.1 ⊗ₜ[R] v₂ p.2) =
      Matrix.kroneckerMap (· * ·) (sgram B₁ v₁) (sgram B₂ v₂) ∧
    (sgram (htmul B₁ B₂) (fun p : ι₁ × ι₂ => v₁ p.1 ⊗ₜ[R] v₂ p.2)).det =
      (sgram B₁ v₁).det ^ Fintype.card ι₂ * (sgram B₂ v₂).det ^ Fintype.card ι₁

def HTmulHerm : Prop :=
  ∀ (R M₁ M₂ : Type) [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R),
    B₁.IsSymm → B₂.IsSymm → (htmul B₁ B₂).IsSymm

end Formalism.E
end
end

