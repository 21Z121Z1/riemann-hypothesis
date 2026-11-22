import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0030

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeGraphCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def ConeGraphCover.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
    ∃ (e : ℕ → (Fin n ≃ Fin m ⊕ Fin (n - m))) (Ω : ℕ → Set (EuclideanSpace ℂ (Fin m)))
      (Φ : ℕ → EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m))),
      (∀ i, IsOpen (Ω i) ∧ DifferentiableOn ℂ (Φ i) (Ω i) ∧
        graphPt (e i) (Φ i) '' Ω i ⊆ coneSet h J ∧
        ∀ x ∈ Ω i, coneTangent h J (graphPt (e i) (Φ i) x) =
          LinearMap.range (fderiv ℂ (graphPt (e i) (Φ i)) x :
            EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))) ∧
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ ⋃ i, graphPt (e i) (Φ i) '' Ω i) = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPointLengthModP
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime)

def PointLengthModP.Statement : Prop :=
  ∀ (n p : ℕ) (W : Ideal (MRing (PBlk n))) (F : Type) [Field F],
    p.Prime → IsMultiProjPrime W → C (p : ℤ) ∈ W →
      Function.Surjective (Int.castRingHom F) → ((p : ℤ) : F) = 0 →
        ∀ i : Fin n,
          (Module.length ℤ (MRing (PBlk n) ⧸ (W ⊔ Ideal.span {(X ⟨(), i⟩ : MRing (PBlk n)) - 1}))).toNat =
            Module.finrank F (MvPolynomial (Fin n) F ⧸
              ((IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F)) ⊔
                Ideal.span {(X i : MvPolynomial (Fin n) F) - 1}))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsReductionModP
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime)

def ReductionModP.Statement : Prop :=
  ∀ (n p : ℕ) (W : Ideal (MRing (PBlk n))) (F : Type) [Field F],
    p.Prime → IsMultiProjPrime W → C (p : ℤ) ∈ W →
      Function.Surjective (Int.castRingHom F) → ((p : ℤ) : F) = 0 →
        IsProjPrime ((IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F))) ∧
        ringKrullDim (MvPolynomial (Fin n) F ⧸
            (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F))) =
          ringKrullDim (MRing (PBlk n) ⧸ W) ∧
        ∀ i : Fin n, ((X i : MvPolynomial (Fin n) F) ∈
            (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F)) ↔
          (X ⟨(), i⟩ : MRing (PBlk n)) ∈ W)

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionCycleModP
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime)

def SectionCycleModP.Statement : Prop :=
  ∀ (n p : ℕ) (W : Ideal (MRing (PBlk n))) (F : Type) [Field F],
    p.Prime → IsMultiProjPrime W → C (p : ℤ) ∈ W →
      Function.Surjective (Int.castRingHom F) → ((p : ℤ) : F) = 0 →
        ∀ i : Fin n, (X ⟨(), i⟩ : MRing (PBlk n)) ∉ W →
          divCycle ((IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F)))
              (Pi.single i 1) =
            Finsupp.mapDomain
              (fun W' => (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W').map (MvPolynomial.map (Int.castRingHom F)))
              (ReciprocityTheory.ChartRestriction.G.Geo.divCycle W (X ⟨(), i⟩))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

