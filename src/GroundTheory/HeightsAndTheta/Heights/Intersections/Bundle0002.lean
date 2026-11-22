import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StRelAlgClosureFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def RelAlgClosureFinite.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (S : Finset L),
    IntermediateField.adjoin K (S : Set L) = ⊤ → FiniteDimensional K (algebraicClosure K L)

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StTrdegAdjoinFrac
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def TrdegAdjoinFrac.Statement : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ D] (E : Type) [CommRing E] [IsDomain E] [Algebra ℤ E]
    [Algebra (FractionRing D) E] (s : Set E),
    Function.Injective (algebraMap ℤ D) →
    Algebra.trdeg ℤ (Algebra.adjoin ℤ
        (Set.range (fun d : D => algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d)) ∪ s)) =
      Algebra.trdeg ℤ D + Algebra.trdeg (FractionRing D) (Algebra.adjoin (FractionRing D) s)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLinearQuotient
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial

def LinearQuotient.Statement : Prop :=
  ∀ (F : Type) [Field F] (σ : Type) [Fintype σ] (S : Set (MvPolynomial σ F)),
    (∀ f ∈ S, f.IsHomogeneous 1) →
    ∃ (r : ℕ) (φ : MvPolynomial σ F →ₐ[F] MvPolynomial (Fin r) F), Function.Surjective φ ∧
      RingHom.ker φ = Ideal.span S ∧ ∀ s, (φ (X s)).IsHomogeneous 1

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsReducedCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

def ReducedCutLength.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (I : Ideal T) (x : T) (Q : Ideal T) [Q.IsPrime],
    I.IsRadical → (∀ p ∈ I.minimalPrimes, x ∉ p) → Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes →
    Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (I ⊔ Ideal.span {x}))) =
      ∑ᶠ p ∈ I.minimalPrimes, Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (p ⊔ Ideal.span {x})))

end GroundTheory.Heights₂.Heights.Inter
end

