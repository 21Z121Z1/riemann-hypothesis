import Mathlib

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangeSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def BasisChangeStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) [Fintype ι] (P : MvPolynomial ι K) (d : ℕ),
    P.IsHomogeneous d → (∀ μ, ‖MvPolynomial.coeff μ P‖ ≤ 1) →
    ∀ (A : ι → ι → K) (C : ℝ), 1 ≤ C → (∀ i k, ‖A i k‖ ≤ C) →
      ∀ μ, ‖MvPolynomial.coeff μ
        (MvPolynomial.bind₁ (fun i => ∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) P)‖ ≤ C ^ d

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BetaSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def pairR {f : ℕ} (χ β : Fin f → ℝ) : ℝ := ∑ i, χ i * β i

def BetaStatement : Prop :=
  ∀ (f : ℕ) (b : Module.Basis (Fin f) ℝ (Fin f → ℝ)) (m : ℕ), 0 < m →
    let SS : Submodule ℤ (Fin f → ℝ) := Submodule.span ℤ (Set.range b)
    ∀ χ₀ ∈ SS, (∀ i, 0 ≤ χ₀ i) →
      ∃ β : Fin f → ℝ, (∀ i, 0 < β i) ∧ (∀ χ ∈ SS, ∃ z : ℤ, pairR χ β = m * z) ∧
        ∀ χ ∈ SS, (∀ i, 0 ≤ χ i) → pairR χ β = pairR χ₀ β → χ = χ₀

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDetectStatement
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

section Defs

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    Submodule F (F ⊗[K] V) :=
  Submodule.span F ((fun u => (1 : F) ⊗ₜ[K] u) '' (U : Set V))

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

noncomputable def inclT (K₁ : IntermediateField K Ω) (V : Type*) [AddCommGroup V] [Module K V] :
    K₁ ⊗[K] V →ₗ[K₁] Ω ⊗[K] V :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K₁ Ω) (LinearMap.id : V →ₗ[K] V)

def DefinedOver (c : Module.Dual Ω (Ω ⊗[K] V)) (K' : IntermediateField K Ω) : Prop :=
  ∀ x : K' ⊗[K] V, c (inclT K' V x) ∈ Set.range (algebraMap K' Ω)

noncomputable def descend (K₁ : IntermediateField K Ω) (W : Submodule Ω (Ω ⊗[K] V)) :
    Submodule K₁ (K₁ ⊗[K] V) :=
  (W.restrictScalars K₁).comap (inclT K₁ V)

end Defs

def FiniteDetectStatement : Prop :=
  ∀ (L E : Type) [Field L] [AddCommGroup E] [Module L E] [FiniteDimensional L E]
    (W : Submodule L E) (FF : Set (Module.Dual L E)),
    (∀ c ∈ FF, W ≤ LinearMap.ker c) →
    (∀ x : E, x ∉ W → ∃ c ∈ FF, c x ≠ 0) →
    ∃ s : Finset (Module.Dual L E), (↑s ⊆ FF) ∧ (⨅ c ∈ s, LinearMap.ker c) = W

def RationalityStatement : Prop :=
  ∀ (K Ω V : Type) [Field K] [Field Ω] [Algebra K Ω] [AddCommGroup V] [Module K V]
    (U : Submodule K V) [FiniteDimensional K U]
    (W : Submodule Ω (Ω ⊗[K] V)) (FF : Set (Module.Dual Ω (Ω ⊗[K] V))),
    W ≤ baseSpan Ω U →
    (∀ c ∈ FF, ∃ K' : IntermediateField K Ω, FiniteDimensional K K' ∧ DefinedOver c K') →
    (∀ c ∈ FF, W ≤ LinearMap.ker c) →
    (∀ x ∈ baseSpan Ω U, x ∉ W → ∃ c ∈ FF, c x ≠ 0) →
    ∃ K₁ : IntermediateField K Ω, FiniteDimensional K K₁ ∧
      ∃ (ρ : ℕ) (c : Fin ρ → Module.Dual Ω (Ω ⊗[K] V)),
        (∀ i, c i ∈ FF ∧ DefinedOver (c i) K₁) ∧
        descend K₁ W = baseSpan K₁ U ⊓
          ⨅ i, LinearMap.ker ((c i).restrictScalars K₁ ∘ₗ inclT K₁ V) ∧
        Submodule.span Ω (inclT K₁ V '' (descend K₁ W : Set (K₁ ⊗[K] V))) = W ∧
        Module.finrank K₁ (descend K₁ W) = Module.finrank Ω W ∧
        Module.finrank K₁ (descend K₁ W) + ρ = Module.finrank K U

def SelectStatement : Prop :=
  ∀ (L E ι : Type) [Field L] [AddCommGroup E] [Module L E] [FiniteDimensional L E]
    (ρ : ℕ) (c : Fin ρ → Module.Dual L E) (MD : Submodule L E),
    (⨅ i, LinearMap.ker (c i)) = MD →
    Module.finrank L MD + ρ = Module.finrank L E →
    ∀ th : ι → E, Submodule.span L (Set.range th) = ⊤ →
      ∃ sel : Fin ρ → ι, Function.Injective sel ∧
        (Matrix.of fun i j => c i (th (sel j))).det ≠ 0

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

noncomputable def ordAt {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F]
    [Algebra R F] [IsFractionRing R F] (v : IsDedekindDomain.HeightOneSpectrum R) (x : F) : ℤ :=
  -WithZero.log (v.valuation F x)

def QuotLocalStatement : Prop :=
  ∀ (O Q : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup Q] [Module O Q] (ρ : ℕ), Nonempty (Module.Basis (Fin ρ) O Q) →
    ∀ (c : Fin ρ → (Q →ₗ[O] O)) (th : Fin ρ → Q),
      (Matrix.of fun i j => c i (th j)).det ≠ 0 →
      Module.length O (Q ⧸ Submodule.span O (Set.range th)) ≤
        IsDiscreteValuationRing.addVal O (Matrix.of fun i j => c i (th j)).det

def QuotShiftStatement : Prop :=
  ∀ (R F : Type) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (v : IsDedekindDomain.HeightOneSpectrum R)
    (Q : Type) [AddCommGroup Q],
    let Rv := (v.valuationSubringAtPrime F).toSubring
    ∀ [Module Rv Q] (ρ : ℕ), Nonempty (Module.Basis (Fin ρ) Rv Q) →
    ∀ (c : Fin ρ → (Q →ₗ[Rv] F)) (s : Fin ρ → ℝ) (β : ℝ) (th : Fin ρ → Q),
      (∀ i q, c i q ≠ 0 → -β ≤ (ordAt v (c i q) : ℝ) + s i) →
      (Matrix.of fun i j => c i (th j)).det ≠ 0 →
      ∃ n : ℕ, Module.length Rv (Q ⧸ Submodule.span Rv (Set.range th)) = n ∧
        (n : ℝ) ≤ (ordAt v (Matrix.of fun i j => c i (th j)).det : ℝ) + ∑ i, s i + ρ * β

def FreeQuotStatement : Prop :=
  ∀ (R F X : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]
    (M₁ : Submodule R X), M₁.FG → ∀ N : Submodule F X,
      Module.Free R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) ∧
      Module.finrank R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) +
          Module.finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) =
        Module.finrank F ↥(Submodule.span F (M₁ : Set X))

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

