import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0051

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelInvariants.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (Ω : Type) [Field Ω] [Algebra S Ω] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → IndefiniteRowSideFullHecke.Kleiman2.SameModel S y y' →
    (IndefiniteRowSideFullHecke.Kleiman2.IsBirational S y ↔ IndefiniteRowSideFullHecke.Kleiman2.IsBirational S y') ∧
      (IndefiniteRowSideFullHecke.Kleiman2.IsNormalModel S y ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNormalModel S y')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def VeryAmpleEq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    IsGraphGen Q n s →
      (Kleiman.IsVeryAmple Q.toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple S (graphVec x s) (graphDeg n))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def ZeroIdealEq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (D : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω), (∃ i, x i ≠ 0) → IsGraphGen D n s →
    ∀ σ : Ω, Kleiman.zeroIdeal D.toSubSystem σ =
      (IndefiniteRowSideFullHecke.Kleiman2.divIdeal S (graphVec x s) (graphDeg n) σ).comap
        (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ k, graphIdx N m k))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def StepEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω), IsGraphGen Q n s →
    ∀ (d : ℕ) (r : ℚ) (a : ℕ) (mm : ℤ) (c₁ : ℕ) (σ : Ω),
      (∃ T : Kleiman.StepData k x, T.M = Q ∧ T.d + 1 = d ∧ T.t - T.s' = r ∧ T.p = a ∧ T.m = mm ∧
          T.c₁ = c₁ ∧ T.si = σ) ↔
        (1 ≤ d ∧ IndefiniteRowSideFullHecke.Kleiman2.IsStepData k (graphVec x s) baseBlock d (graphDeg n) r a mm c₁ σ)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def GenFibNef.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (Ω : Type) [Field Ω] [Algebra O Ω] [Algebra F Ω] [IsScalarTower O F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    (β : K → ℤ),
    IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (FractionRing O) (NumbersDVR.genFib (mIdealOver O y)) β ↔
      IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β

example (h : GenFibNef.Statement) :=
  h exO exF exΩ (Unit ⊕ Unit) (graphIdx 1 2) (graphVec (Kleiman.lineX exF) (Kleiman.lineX exF)) (graphDeg 0)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def GenericFibreScalars.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsDomain S] (F : Type) [Field F] [Algebra S F] (Ω : Type) [Field Ω] [Algebra S Ω]
    [Algebra F Ω] [IsScalarTower S F Ω] [IsFractionRing S F] (N N' : ℕ) (x : Fin (N + 1) → Ω)
    (x' : Fin (N' + 1) → Ω),
    IsNoetherianRing S → x' ≠ 0 → Kleiman.IsDomination S x x' →
    IndefiniteRowSideFullHecke.Kleiman2.SameModel F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) →
    ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ Kleiman.domRing S x x' i, ∃ s : S,
      algebraMap S Ω s ≠ 0 ∧ algebraMap S Ω s * b ∈ Kleiman.chartRing S x (Kleiman.singleChart hi)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ModelGenericPoint.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (NumbersDVR.MRing ι O)) (d : ℕ),
    NumbersDVR.IsModelOver P d →
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra O Ω) (_ : Algebra (FractionRing O) Ω)
      (_ : IsScalarTower O (FractionRing O) Ω) (y : (Σ k, ι k) → Ω),
      mIdealOver O y = P ∧ ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0

example (h : ModelGenericPoint.Statement) :=
  h exO Unit (fun _ => Fin 2) ⊥ 1 NefFibresSegre.hyps

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def DomEq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N N' : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (x' : Fin (N' + 1) → Ω),
    (Kleiman.IsDomination S x x' ↔
      IndefiniteRowSideFullHecke.Kleiman2.Dominates S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) ∧
    (Kleiman.IsDomination S x x' → ∀ (Q : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
      IsGraphGen Q n s →
        Kleiman.pullSecs x' Q.toSubSystem =
          secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (graphVec x s))
            (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (graphDeg n)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def NumEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (pp : Ideal (Kleiman.Poly k N)) (e : ℕ) (b : Fin e → ℤ),
    Kleiman.IsSubvar x pp e →
    Kleiman.interNum pp (fun i => Kleiman.twistSys k x (b i)) =
      NumbersDVR.intNum k (pp.comap (Kleiman.oneBlock (S := k) (N := N))) (fun i (_ : Unit) => b i)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreFibresNef.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    [Algebra (FractionRing O) Ω] [IsScalarTower O (FractionRing O) Ω] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∀ β : K → ℤ,
      (IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (IsLocalRing.ResidueField O)
          (NumbersDVR.specialIdeal (mIdealOver O (segreJoin y))) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔
        IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (IsLocalRing.ResidueField O)
          (NumbersDVR.specialIdeal (mIdealOver O y)) β) ∧
      (IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (FractionRing O) (NumbersDVR.genFib (mIdealOver O (segreJoin y)))
          (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔
        IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (FractionRing O) (NumbersDVR.genFib (mIdealOver O y)) β)

theorem SegreFibresNef.hyps :
    ∀ k, ∃ i, IndefiniteRowSideFullHecke.Kleiman2.oneBlock (Kleiman.lineX exF) ⟨k, i⟩ ≠ 0 :=
  fun _ => ⟨0, Kleiman.lineX_ne_zero exF 0⟩

example (h : SegreFibresNef.Statement) :=
  h exO exΩ Unit (fun _ => Fin (1 + 1)) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (Kleiman.lineX exF)) SegreFibresNef.hyps 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def SegreModel.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
    ∃ (N : ℕ) (e : (∀ k, ι k) ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω),
      (∀ c, x (e c) = ∏ k, y ⟨k, c k⟩) ∧ x ≠ 0 ∧
      ∀ (R : Type) [CommRing R] [Algebra R Ω], IndefiniteRowSideFullHecke.Kleiman2.SameModel R y (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreRealise.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ a, Fintype (ι a)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ a, ι a) → Ω) (d : ℕ)
    (μs : Fin d → K → ℤ),
    (∀ a, ∃ i, y ⟨a, i⟩ ≠ 0) → FieldNumbers.relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) →
    ∃ (N : ℕ) (eqv : (∀ a, ι a) ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω)
      (Ms : Fin d → Kleiman.LineBundle F x),
      (∀ i, x (eqv i) = ∏ a, y ⟨a, i a⟩) ∧
      Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) d ∧
      (∀ j (c : ℤ), ((Ms j).twist (Kleiman.twistSys F x c)).secs =
        secOver F y (μs j + fun _ => c)) ∧
      (∀ j, Kleiman.Nef (Ms j).toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y (μs j)) ∧
      Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun j => (Ms j).toSubSystem) =
        NumbersDVR.intNum F (mIdealOver F y) μs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

