import Mathlib

-- bundled from ReciprocityTheory.NeutralLocalFields.GrunwaldWang
section
open NumberField IsDedekindDomain

namespace Neutral.GrunwaldWang

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]

def LiesAbove (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A.nonunits ↔ x ∈ v.asIdeal

def IsComplexConjugationAt (w : InfinitePlace K) (c : Ω ≃ₐ[K] Ω) : Prop :=
  ∃ j : Ω →+* ℂ, (∀ x, j (c x) = starRingEnd ℂ (j x)) ∧ InfinitePlace.mk (j.comp (algebraMap K Ω)) = w

def Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (m : ℕ), 0 < m → ¬ 8 ∣ m →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (A : T → ValuationSubring Ω), (∀ v, LiesAbove (A v) v.1) →
    ∀ χ : ∀ v : T, (A v).decompositionSubgroup K →* Multiplicative (ZMod m), (∀ v, Continuous (χ v)) →
    ∀ (R : Finset (InfinitePlace K)) (c : R → (Ω ≃ₐ[K] Ω)), (∀ w, IsComplexConjugationAt w.1 (c w)) →
    ∀ ε : R → Multiplicative (ZMod m), (∀ w, ε w ^ 2 = 1) →
      ∃ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod m), Continuous ψ ∧
        (∀ v : T, ψ.comp ((A v).decompositionSubgroup K).subtype = χ v) ∧ ∀ w : R, ψ (c w) = ε w

def SolubleStatement : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (N : Subgroup (Ω ≃ₐ[F] Ω)), N.Normal → IsOpen (N : Set (Ω ≃ₐ[F] Ω)) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : S → ValuationSubring Ω), (∀ v, LiesAbove (A v) v.1) →
    ∀ U : ∀ v : S, Subgroup ((A v).decompositionSubgroup F), (∀ v, (U v).Normal) →
      (∀ v, IsOpen (U v : Set ((A v).decompositionSubgroup F))) →
    ∀ R : Set (InfinitePlace F), (∀ w ∈ R, w.IsReal) →
      ∃ (H : Subgroup (Ω ≃ₐ[F] Ω)) (_ : H.Normal), IsOpen (H : Set (Ω ≃ₐ[F] Ω)) ∧ Group.IsSolvable ((Ω ≃ₐ[F] Ω) ⧸ H) ∧ H ⊔ N = ⊤ ∧
        (∀ v : S, H.subgroupOf ((A v).decompositionSubgroup F) = U v) ∧
        ∀ w ∈ R, ∀ c : Ω ≃ₐ[F] Ω, IsComplexConjugationAt w c → c ∈ H

end Neutral.GrunwaldWang
end

-- bundled from ReciprocityTheory.NeutralLocalFields.HilbertClassField
section
open NumberField IsDedekindDomain

namespace Neutral.HilbertClassField

variable {E : Type*} [Field E] [NumberField E] {Ω : Type*} [Field Ω] [Algebra E Ω]

def LiesAbove (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A.nonunits ↔ x ∈ v.asIdeal

def IsArithFrobenius (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (φ : Ω ≃ₐ[E] Ω) : Prop :=
  φ ∈ A.decompositionSubgroup E ∧ ∀ x ∈ A, φ x - x ^ Nat.card (𝓞 E ⧸ v.asIdeal) ∈ A.nonunits

def IsComplexConjugation (c : Ω ≃ₐ[E] Ω) : Prop :=
  ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)

variable (E Ω) in

def hilbertSubgroup : Subgroup (Ω ≃ₐ[E] Ω) :=
  (Subgroup.closure ((commutator (Ω ≃ₐ[E] Ω) : Set (Ω ≃ₐ[E] Ω)) ∪
    {σ | ∃ A : ValuationSubring Ω, σ ∈ (A.inertiaSubgroup E).map (A.decompositionSubgroup E).subtype} ∪
    {c | IsComplexConjugation c})).topologicalClosure

def Statement : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), Function.Surjective art ∧ art.ker = hilbertSubgroup E Ω ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ →
        art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

end Neutral.HilbertClassField
end

