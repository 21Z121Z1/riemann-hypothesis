import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.AlphaUniqueness.Statement
import Formalism.LatticeTheta.Statement

-- bundled from Formalism.HermitianLattices.DefsCS
section
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

def zmap {V W : Type*} [AddCommGroup V] [AddCommGroup W] {R : Type*} [Ring R] [Module R V]
    (ι : V →+ W) (M : Submodule R V) : Submodule ℤ W :=
  (M.toAddSubgroup.map ι).toIntSubmodule

def TraceReal : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∃ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) ∧
      (∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖) ∧
      (∀ M : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K M →
        ∃ _ : DiscreteTopology (zmap ι M), IsZLattice ℝ (zmap ι M))

def GenusCovol : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ L M : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L → M ∈ genus h L →
    ∀ [DiscreteTopology (zmap ι L)] [IsZLattice ℝ (zmap ι L)]
      [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)],
      ZLattice.covolume (zmap ι M) = ZLattice.covolume (zmap ι L)

def ShortVectors : Prop :=
  ∀ (N : ℕ) (c C : ℝ), 0 < c → ∃ B : ℝ, ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    (∀ v ∈ Λ, v ≠ 0 → c ≤ ‖v‖) → ZLattice.covolume Λ ≤ C →
    ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ i, v i ∈ Λ) ∧ LinearIndependent ℝ v ∧
      ∀ i, ‖v i‖ ≤ B

def GenusScale : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    ∃ d : ℕ, 0 < d ∧ ∀ M ∈ genus h L, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K)

def FinIntermediate : Prop :=
  ∀ (W : Type) [AddCommGroup W] (P Q : AddSubgroup W), P ≤ Q → Finite (Q ⧸ P.addSubgroupOf Q) →
    Set.Finite {M : AddSubgroup W | P ≤ M ∧ M ≤ Q}

def IsomOfTrace : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (g : V ≃ₗ[K] V),
    (∀ x y : V, Algebra.trace ℚ K (h (g x) (g y)) = Algebra.trace ℚ K (h x y)) → g ∈ isom h

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.DualOrthSum
section
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

def DualOrthSum : Prop :=
  ∀ (R K V : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (V₁ V₂ : Submodule K V), IsCompl V₁ V₂ →
    (∀ x ∈ V₁, ∀ y ∈ V₂, h x y = 0) → (∀ x ∈ V₂, ∀ y ∈ V₁, h x y = 0) →
    ∀ L₁ L₂ : Submodule R V, (L₁ : Set V) ⊆ V₁ → (L₂ : Set V) ⊆ V₂ →
      dual h (L₁ ⊔ L₂) = (dual h L₁ ⊓ V₁.restrictScalars R) ⊔ (dual h L₂ ⊓ V₂.restrictScalars R)

def DualLine : Prop :=
  ∀ (R K V : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
    ∀ z : V, h z z ≠ 0 →
      dual h (Submodule.span R {z}) ⊓ (Submodule.span K {z}).restrictScalars R =
        Submodule.span R {(h z z)⁻¹ • z} ∧
      ∀ (V' : Submodule K V) (L' : Submodule R V), IsCompl V' (Submodule.span K {z}) →
        (∀ x ∈ V', h x z = 0) → (L' : Set V) ⊆ V' →
        dual h L' ⊓ V'.restrictScalars R = L' →
        dual h (L' ⊔ Submodule.span R {z}) = L' ⊔ Submodule.span R {(h z z)⁻¹ • z}

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.NeighbourConstruct
section
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def invIdeal (P : Ideal R) : Submodule R K :=
  ⨅ p ∈ P, (1 : Submodule R K).comap ((LinearMap.mulLeft R (algebraMap R K p)))

def neighbourCore (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Ideal R) (L : Submodule R V) (x : V) :
    Submodule R V :=
  L ⊓ (Submodule.map (Algebra.linearMap R K) (conjIdeal (K := K) P)).comap ((h x).restrictScalars R)

def neighbourOf (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Ideal R) (L : Submodule R V) (x : V) :
    Submodule R V :=
  Submodule.span R {z | ∃ a ∈ invIdeal (K := K) P, z = a • x} ⊔ neighbourCore h P L x

end Defs

def NeighbourConstruct : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
    [IsScalarTower R K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → h.Nondegenerate →
    (∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
    ∀ (P : Ideal R), P.IsMaximal → P ≠ ⊥ → ∀ L : Submodule R V, Submodule.IsLattice K L →
    IsUnimodular h L → ∀ x ∈ L, x ∉ P • L →
    (∃ r ∈ P * conjIdeal (K := K) P, algebraMap R K r = h x x) →
      Submodule.IsLattice K (neighbourOf h P L x) ∧
      IsIntegralLat h (neighbourOf h P L x) ∧ IsUnimodular h (neighbourOf h P L x) ∧
      IsNeighbour (K := K) P L (neighbourOf h P L x) ∧
      L ⊓ neighbourOf h P L x = neighbourCore h P L x

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.StatementTheta
section
open Formalism.K

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

def weilT {D : Type*} (Q : D → ℂ) (f : D → ℂ) : D → ℂ := fun γ => Q γ * f γ

def weilS {D : Type*} [AddCommGroup D] [Fintype D] (Q : D → ℂ) (f : D → ℂ) : D → ℂ :=
  fun γ => ((Real.sqrt (Fintype.card D) : ℝ) : ℂ)⁻¹ *
    ∑ δ, starRingEnd ℂ (polar Q γ δ) * f δ

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

def thetaL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) (γ : V)
    (τ : ℂ) : ℂ :=
  ∑' x : L, Complex.exp (Real.pi * Complex.I * τ *
    ((Algebra.trace ℚ K (h (γ + x) (γ + x)) : ℚ) : ℂ))

def thetaN (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) (n : ℕ)
    (γ : Fin n → V) (τ : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑' x : Fin n → L, Complex.exp (Real.pi * Complex.I * ∑ i, ∑ j,
    ((Algebra.trace ℚ K (h (γ i + x i) (γ j + x j)) : ℚ) : ℂ) * τ j i)

end Defs

def thetaE {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (Λ : Submodule ℤ W) (γ : W)
    (τ : ℂ) : ℂ :=
  ∑' x : Λ, Complex.exp (Real.pi * Complex.I * τ * ((‖γ + (x : W)‖ ^ 2 : ℝ) : ℂ))

def WeilFinite : Prop :=
  ∀ (D : Type) [AddCommGroup D] [Fintype D] (Q : D → ℂ), IsUQuad Q → Nondeg Q →
    (∀ f : D → ℂ, weilS Q (weilS Q f) = fun γ => f (-γ)) ∧
    (∀ f : D → ℂ, ∑ γ, ‖weilS Q f γ‖ ^ 2 = ∑ γ, ‖f γ‖ ^ 2) ∧
    (∀ f : D → ℂ, weilS Q (weilT Q (weilS Q (weilT Q (weilS Q (weilT Q f))))) =
      fun γ => gsum Q / ((Real.sqrt (Fintype.card D) : ℝ) : ℂ) * f (-γ))

def ThetaBasic : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    ∀ (L : Submodule (NumberField.RingOfIntegers K) V) (γ : V) (τ : ℂ),
      (∀ l ∈ L, thetaL h L (γ + l) τ = thetaL h L γ τ) ∧
      thetaL h L (-γ) τ = thetaL h L γ τ ∧
      (∀ g ∈ isom h, thetaL h (gmap g L) (g γ) τ = thetaL h L γ τ) ∧
      ((∀ x ∈ L, ∃ n : ℤ, Algebra.trace ℚ K (h x x) = 2 * n) →
        (∀ x ∈ L, ∃ n : ℤ, Algebra.trace ℚ K (h γ x) = n) →
        thetaL h L γ (τ + 1) =
          Complex.exp (Real.pi * Complex.I * ((Algebra.trace ℚ K (h γ γ) : ℚ) : ℂ)) *
            thetaL h L γ τ) ∧
      (∀ (n : ℕ) (γs : Fin n → V) (T : Matrix (Fin n) (Fin n) ℂ), ∀ g ∈ isom h,
        thetaN h (gmap g L) n (fun i => g (γs i)) T = thetaN h L n γs T) ∧
      (∀ T : Matrix (Fin 1) (Fin 1) ℂ, thetaN h L 1 (fun _ => γ) T = thetaL h L γ (T 0 0))

def ThetaSummable : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    ∀ (γ : V) (τ : ℂ), 0 < τ.im →
      Summable (fun x : L => Complex.exp (Real.pi * Complex.I * τ *
        ((Algebra.trace ℚ K (h (γ + x) (γ + x)) : ℚ) : ℂ)))

def ThetaSEuclid : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W] [BorelSpace W]
    [FiniteDimensional ℝ W] (Λ : Submodule ℤ W) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (γ : W) (τ : ℂ), 0 < τ.im →
    thetaE Λ γ (-τ⁻¹) =
      (-Complex.I * τ) ^ ((Module.finrank ℝ W : ℂ) / 2) / (ZLattice.covolume Λ : ℂ) *
        ∑' μ : Formalism.H.dual Λ, Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ γ (μ : W) : ℝ) : ℂ)) *
          Complex.exp (Real.pi * Complex.I * τ * ((‖(μ : W)‖ ^ 2 : ℝ) : ℂ))

end Formalism.HermitianLatticesTheory
end
end

