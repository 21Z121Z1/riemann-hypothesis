import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsIntegralPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

noncomputable section

abbrev completionIntegersTo (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (L : Type) [Field L] [Algebra (v.adicCompletion F) L] : v.adicCompletionIntegers F →+* L :=
  (algebraMap (v.adicCompletion F) L).comp (v.adicCompletionIntegers F).subtype

def IntegralPointThroughPrime.Hyp (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] (v : HeightOneSpectrum (𝓞 F)) (P : Ideal R) (u g : R) : Prop :=
  P.IsPrime ∧ P.comap (algebraMap (𝓞 F) R) = v.asIdeal ∧ u ∉ P ∧ g ≠ 0

def IntegralPointThroughPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R]
    [Module.Flat (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (v : HeightOneSpectrum (𝓞 F))
    (P : Ideal R) (u g : R), IntegralPointThroughPrime.Hyp F R v P u g →
    ∃ (L : Type) (_ : Field L) (_ : Algebra (v.adicCompletion F) L)
      (_ : FiniteDimensional (v.adicCompletion F) L) (y : R →+* L),
      y.comp (algebraMap (𝓞 F) R) =
          (algebraMap (v.adicCompletion F) L).comp
            ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)) ∧
        (∀ a : R, (completionIntegersTo F v L).IsIntegralElem (y a)) ∧
        y g ≠ 0 ∧
        (∃ b : L, b * y u = 1 ∧ (completionIntegersTo F v L).IsIntegralElem b) ∧
        ∀ a ∈ P, ∀ b : L, b * y a = 1 → ¬ (completionIntegersTo F v L).IsIntegralElem b

def placeTwo : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩

end

end GroundTheory.Heights₂.Heights.FourB
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsKrullHeightOne
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

def KrullHeightOne.Hyp {A : Type*} [CommRing A] (p q : A) : Prop :=
  q ≠ 0 ∧ ¬ q ∣ p

def KrullHeightOne.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (p q : A),
    KrullHeightOne.Hyp p q →
      ∃ P : Ideal A, P.IsPrime ∧ P.height = 1 ∧ ∃ c ∉ P, ∃ t ∈ P, c * q = t * p

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsZariskiDense
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

def ZariskiDense.Hyp (A : Type*) [CommRing A] [Algebra ℂ A] (g : A) : Prop :=
  Algebra.FiniteType ℂ A ∧ IsDomain A ∧ g ≠ 0

def ZariskiDense.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℂ A] (g : A), ZariskiDense.Hyp A g →
    ∀ (x : A →ₐ[ℂ] ℂ) (s : Finset A) (ε : ℝ), 0 < ε →
      ∃ y : A →ₐ[ℂ] ℂ, (∀ a ∈ s, ‖y a - x a‖ < ε) ∧ y g ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

