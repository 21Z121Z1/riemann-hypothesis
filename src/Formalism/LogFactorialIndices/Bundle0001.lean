import Mathlib

-- bundled from Formalism.LogFactorialIndices.StatementIdx
section
noncomputable section

namespace Formalism.LatticeIndexTer

open Module
open scoped Pointwise

section Defs

variable (O K X : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup X] [Module K X]
  [Module O X]

def IsLat (A : Submodule O X) : Prop := A.FG ∧ Submodule.span K (A : Set X) = ⊤

end Defs

section Defs2

variable (O X : Type) [CommRing O] [AddCommGroup X] [Module O X]

def qlen (A B : Submodule O X) : ℕ∞ := Module.length O (A ⧸ B.comap A.subtype)

def idx (A B : Submodule O X) : ℤ := ((qlen O X A B).toNat : ℤ) - ((qlen O X B A).toNat : ℤ)

end Defs2

def LatFinite : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    (A B : Submodule O X), IsLat O K X A → IsLat O K X B → qlen O X A B ≠ ⊤

def LatBasis : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (A : Submodule O X), IsLat O K X A →
      ∃ b : Basis (Fin (finrank K X)) K X, A = Submodule.span O (Set.range b)

def IdxAdd : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    (A B C : Submodule O X), IsLat O K X A → IsLat O K X B → IsLat O K X C →
      idx O X A C = idx O X A B + idx O X B C

def IdxDet : Prop :=
  ∀ (O K X Y ι : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y] [Fintype ι] [DecidableEq ι]
    (bX : Basis ι K X) (bY : Basis ι K Y) (f : X ≃ₗ[K] Y) (a b : O), a ≠ 0 → b ≠ 0 →
    algebraMap O K a = (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det * algebraMap O K b →
      idx O Y (Submodule.span O (Set.range bY))
          ((Submodule.span O (Set.range bX)).map ((f : X →ₗ[K] Y).restrictScalars O)) =
        ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) - ((IsDiscreteValuationRing.addVal O b).toNat : ℤ)

def ThreeIdx : Prop :=
  ∀ (O K X₁ X₂ X₃ X₄ ι : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K]
    [AddCommGroup X₁] [Module K X₁] [Module O X₁] [IsScalarTower O K X₁]
    [AddCommGroup X₂] [Module K X₂] [Module O X₂] [IsScalarTower O K X₂]
    [AddCommGroup X₃] [Module K X₃] [Module O X₃] [IsScalarTower O K X₃]
    [AddCommGroup X₄] [Module K X₄] [Module O X₄] [IsScalarTower O K X₄] [Fintype ι] [DecidableEq ι]
    (b₁ : Basis ι K X₁) (b₂ : Basis ι K X₂) (b₃ : Basis ι K X₃) (b₄ : Basis ι K X₄)
    (θ' : X₁ ≃ₗ[K] X₂) (j : X₂ ≃ₗ[K] X₃) (θ : X₃ ≃ₗ[K] X₄) (a b : O), a ≠ 0 → b ≠ 0 →
    algebraMap O K a =
      (LinearMap.toMatrix b₁ b₄ ((θ : X₃ →ₗ[K] X₄) ∘ₗ (j : X₂ →ₗ[K] X₃) ∘ₗ (θ' : X₁ →ₗ[K] X₂))).det *
        algebraMap O K b →
    let A := Submodule.span O (Set.range b₁)
    let B' := Submodule.span O (Set.range b₂)
    let B := Submodule.span O (Set.range b₃)
    let A' := Submodule.span O (Set.range b₄)
    ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) - ((IsDiscreteValuationRing.addVal O b).toNat : ℤ) =
      idx O X₂ B' (A.map ((θ' : X₁ →ₗ[K] X₂).restrictScalars O)) +
        idx O X₃ B (B'.map ((j : X₂ →ₗ[K] X₃).restrictScalars O)) +
        idx O X₄ A' (B.map ((θ : X₃ →ₗ[K] X₄).restrictScalars O))

def IdxScale : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ → ∀ (s : ℤ) (N : Submodule O X), IsLat O K X N →
      idx O X N (N.map ((((algebraMap O K ϖ) ^ (-s)) • LinearMap.id : X →ₗ[K] X).restrictScalars O)) =
        -s * (finrank K X : ℤ)

def SubspaceIndex : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ →
    ∀ (F : ℕ) (M Θ : Submodule O X), IsLat O K X M → Θ ≤ (ϖ ^ F) • M → ∀ W : Submodule K X,
      let MW : Submodule O X := M ⊓ W.restrictScalars O
      let ΘW : Submodule O X := Θ ⊓ W.restrictScalars O
      Module.length O (MW ⧸ ΘW.comap MW.subtype) + ((F * (finrank K X - finrank K W) : ℕ) : ℕ∞) ≤
        Module.length O (M ⧸ Θ.comap M.subtype)

def GoodIndex : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (e : X →ₗ[K] X), e ∘ₗ e = e →
    ∀ (A Θ : Submodule O X), IsLat O K X A → IsLat O K X Θ → Θ ≤ A →
      let V₀ : Submodule O X := (LinearMap.range e).restrictScalars O
      idx O X (A ⊓ V₀) (Θ ⊓ V₀) ≤ idx O X A Θ ∧
        idx O X (A ⊓ V₀) (Θ.map (e.restrictScalars O)) ≤ idx O X (A ⊓ V₀) (Θ ⊓ V₀)

def GoodIso : Prop :=
  ∀ (O V : Type) [CommRing O] [AddCommGroup V] [Module O V] (e : V →ₗ[O] V), e ∘ₗ e = e →
    ∀ (A : Submodule O V) (n : O), (∀ a ∈ A, n • e a ∈ A) →
      let V₀ := LinearMap.range e
      let V₁ := LinearMap.ker e
      let P := A.map e
      let Q := A.map (LinearMap.id - e)
      (∀ a ∈ A, n • e a ∈ A ⊓ V₀) ∧ A ⊓ V₀ ≤ P ∧ A ⊓ V₁ ≤ Q ∧
        Nonempty ((P ⧸ (A ⊓ V₀).comap P.subtype) ≃ₗ[O] (Q ⧸ (A ⊓ V₁).comap Q.subtype)) ∧
        ∀ x : P ⧸ (A ⊓ V₀).comap P.subtype, n • x = 0

def GoodGen : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (e : X →ₗ[K] X), e ∘ₗ e = e → ∀ A : Submodule O X, IsLat O K X A →
      let V₀ : Submodule O X := (LinearMap.range e).restrictScalars O
      let P : Submodule O X := A.map (e.restrictScalars O)
      ∃ s : Finset (P ⧸ (A ⊓ V₀).comap P.subtype),
        s.card ≤ min (finrank K (LinearMap.range e)) (finrank K (LinearMap.ker e)) ∧
          Submodule.span O (s : Set (P ⧸ (A ⊓ V₀).comap P.subtype)) = ⊤

def GoodDual : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (B : LinearMap.BilinForm K X), B.Nondegenerate →
    ∀ (e : X →ₗ[K] X), e ∘ₗ e = e → (∀ x y, B (e x) y = B x (e y)) →
    ∀ A : Submodule O X, IsLat O K X A →
      {x : X | x ∈ LinearMap.range e ∧
          ∀ y ∈ A ⊓ (LinearMap.range e).restrictScalars O, B x y ∈ Set.range (algebraMap O K)} =
        e '' {z : X | ∀ y ∈ A, B z y ∈ Set.range (algebraMap O K)}

def PointwiseLength : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [Infinite (IsLocalRing.ResidueField O)]
    (T ι : Type) [CommRing T] [Algebra O T] [Fintype ι] (π : ι → T →ₐ[O] O) (d : ι → ℕ)
    (c : Ideal T), (∀ i, ∃ t ∈ c, π i t ≠ 0) →
    ∀ (X X' : Submodule O ((i : ι) → Fin (d i) → K)), IsLat O K ((i : ι) → Fin (d i) → K) X →
      X' ≤ X →
      (∀ t ∈ c, ∀ x ∈ X, (fun i k => algebraMap O K (π i t) * x i k) ∈ X') →
      Module.length O (X ⧸ X'.comap X.subtype) ≤
        ∑ i, (d i : ℕ∞) * ⨅ t ∈ c, IsDiscreteValuationRing.addVal O (π i t)

end Formalism.LatticeIndexTer
end
end

-- bundled from Formalism.LogFactorialIndices.StatementNorm
section
noncomputable section

namespace Formalism.LatticeIndexTer

open scoped ComplexConjugate

def NormRel : Prop :=
  ∀ (L : Type) [Field L] (σ : L →+* ℂ) (c : L →+* L), (∀ x, σ (c x) = conj (σ x)) →
    ∀ (D : ℕ) (Y : Matrix (Fin D) (Fin D) L) (G : Matrix (Fin D) (Fin D) ℂ),
      ((Y.map σ) * G * (Y.map σ).conjTranspose).det = σ (Y.det * c Y.det) * G.det

def NormRelDiv : Prop :=
  ∀ (L : Type) [Field L] (σ : L →+* ℂ) (c : L →+* L), (∀ x, σ (c x) = conj (σ x)) →
    ∀ (D : ℕ) (Y : Matrix (Fin D) (Fin D) L) (G : Matrix (Fin D) (Fin D) ℂ) (κ : ℝ) (z₀ zμ : L),
      κ ≠ 0 → z₀ ≠ 0 → G.det = (κ : ℂ) * σ z₀ →
      ((Y.map σ) * G * (Y.map σ).conjTranspose).det = (κ : ℂ) * σ zμ →
      Y.det * c Y.det = zμ / z₀

def NormRelVal : Prop :=
  ∀ (L : Type) [Field L] (c : L →+* L), (∀ x, c (c x) = x) →
    ∀ (v v' : AddValuation L (WithTop ℤ)), (∀ x, v' (c x) = v x) →
    ∀ (y z₀ zμ : L), z₀ ≠ 0 → c z₀ = z₀ → c zμ = zμ → y * c y = zμ / z₀ →
      v y + v' y + v z₀ = v zμ ∧ v y + v' y + v' z₀ = v' zμ

def IntegralityLocal : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K]
    (U Xm Zp E : Type) [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U]
    [AddCommGroup Xm] [Module K Xm] [Module O Xm] [IsScalarTower O K Xm]
    [AddCommGroup Zp] [Module K Zp] [AddCommGroup E] [Module K E]
    (P : U →ₗ[K] Xm →ₗ[K] K) (B : U →ₗ[K] E →ₗ[K] K) (pr : Xm →ₗ[K] Zp) (Z : Submodule K Zp)
    (ι : Zp →ₗ[K] E) (ζ : Oˣ) (N : Submodule O U) (Mt : Submodule O Xm) (abelian₂ : Set Zp) (ϖ : O) (s : ℤ),
    Irreducible ϖ →
    (∀ φ F, pr F ∈ Z → P φ F = algebraMap O K ζ * B φ (ι (pr F))) →
    (∀ φ ∈ N, ∀ F ∈ Mt, ∃ o : O, P φ F = (algebraMap O K ϖ) ^ s * algebraMap O K o) →
    (∀ l ∈ abelian₂, l ∈ Z ∧ ∃ F ∈ Mt, pr F = l) →
    ∀ φ ∈ N, ∀ l ∈ abelian₂, ∃ o : O, B ((algebraMap O K ϖ) ^ (-s) • φ) (ι l) = algebraMap O K o

def LogProductFormula : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (x : L), x ≠ 0 →
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ =
      ∑ᶠ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        (FractionalIdeal.count L 𝔭
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L)) x) : ℝ) *
          Real.log (Ideal.absNorm 𝔭.asIdeal : ℝ)

end Formalism.LatticeIndexTer
end
end

-- bundled from Formalism.LogFactorialIndices.StatementSize
section
noncomputable section

namespace Formalism.LatticeIndexTer

def ph (u : ℝ) : ℝ := u * Real.log u - u

def PhIncr : Prop :=
  ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → (1 ≤ u ∨ 1 ≤ v) → |ph (u + v) - ph u| ≤ v * Real.log (u + v + 2)

def PhIncrFalse : Prop :=
  ¬ ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → |ph (u + v) - ph u| ≤ v * Real.log (u + v + 2)

def PhIncrNat : Prop :=
  ∀ u v : ℕ, |ph ((u : ℝ) + v) - ph u| ≤ (v : ℝ) * Real.log ((u : ℝ) + v + 2)

def Interlaced (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S : ℝ) : Prop :=
  (∀ i, 0 ≤ c i ∧ c i ≤ S) ∧ ∀ i : Fin k, c' i ≤ c i.castSucc ∧ c i.succ ≤ c' i

def Interlace : Prop :=
  ∀ (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S w : ℝ), Interlaced k c c' S → 1 ≤ w →
    |(∑ i, ph (w + c i)) - ∑ i, ph (w + c' i)| ≤ (w + 2 * S) * Real.log (w + S + 2)

def InterlaceFalse : Prop :=
  ¬ ∀ (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S w : ℝ), Interlaced k c c' S → 0 ≤ w →
    |(∑ i, ph (w + c i)) - ∑ i, ph (w + c' i)| ≤ (w + 2 * S) * Real.log (w + S + 2)

def InterlaceNat : Prop :=
  ∀ (k : ℕ) (c : Fin (k + 1) → ℕ) (c' : Fin k → ℕ) (S w : ℕ),
    Interlaced k (fun i => (c i : ℝ)) (fun i => (c' i : ℝ)) S →
    |(∑ i, ph ((w : ℝ) + c i)) - ∑ i, ph ((w : ℝ) + c' i)| ≤
      ((w : ℝ) + 2 * S) * Real.log ((w : ℝ) + S + 2)

def hookProd (μ : YoungDiagram) : ℕ :=
  ∏ x ∈ μ.cells, ((μ.rowLen x.1 - x.2) + (μ.colLen x.2 - x.1) - 1)

def HookFact : Prop :=
  ∀ μ : YoungDiagram, ∏ i ∈ Finset.range (μ.colLen 0), (μ.rowLen i).factorial ≤ hookProd μ

def HookLog : Prop :=
  ∀ μ : YoungDiagram,
    (∑ i ∈ Finset.range (μ.colLen 0), Real.log ((μ.rowLen i).factorial : ℝ)) -
        ((μ.colLen 0 : ℝ) ^ 2) * Real.log ((μ.rowLen 0 : ℝ) + μ.colLen 0) ≤
      Real.log (hookProd μ : ℝ)

end Formalism.LatticeIndexTer
end
end

