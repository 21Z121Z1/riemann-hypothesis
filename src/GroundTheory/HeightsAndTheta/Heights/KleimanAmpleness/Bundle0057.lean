import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0004

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def BaseRealises.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ b : ℤ, BundleRealises y k₀ (Kleiman.twistBundle F x b) (b • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def NumModel.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (n : ℕ) (L : Fin n → Kleiman.LineBundle F x) (δ : Fin n → K → ℤ),
        (∀ i, BundleRealises y k₀ (L i) (δ i)) → Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) n →
          Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun i => (L i).toSubSystem) =
            NumbersDVR.intNum F (mIdealOver F y) δ

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelWithBaseLocalization.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) (ι : K → Type) (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K)
    (S' : Type) [CommRing S'] [Algebra S S'] [Algebra S' Ω] [IsScalarTower S S' Ω]
    (M : Submonoid S) [IsLocalization M S'],
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S' y k₀

example (h : ModelWithBaseLocalization.Statement) :=
  h exO Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 1) (IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1) (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () exF
    (nonZeroDivisors exO) isModelWithBase_exO_pnPt

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def MultiSerre.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)),
    NumbersDVR.IsMultiHomogIdeal V →
      ∀ᶠ m : K → ℤ in Filter.atTop,
        (∀ i : ℕ, 1 ≤ i → Subsingleton (cechHc ι (quotPart F V) m i)) ∧
        (Module.finrank F (cechHc ι (quotPart F V) m 0) : ℤ) = NumbersDVR.hilbFn V m

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SpecialCurvesLift.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra O Ω] [Algebra (FractionRing O) Ω] [IsScalarTower O (FractionRing O) Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω),
    x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase O y k₀ →
      ∀ P : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) (IsLocalRing.ResidueField O)),
        NumbersDVR.IsMultiProjPrime P →
        NumbersDVR.specialIdeal (mIdealOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) ≤ P →
          ∃ W : Ideal (NumbersDVR.MRing ι (IsLocalRing.ResidueField O)), NumbersDVR.IsMultiProjPrime W ∧
            NumbersDVR.specialIdeal (mIdealOver O y) ≤ W ∧
            baseComap (IsLocalRing.ResidueField O) k₀ e W = P

theorem SpecialCurvesLift.hyps :
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () ∧
      NumbersDVR.IsMultiProjPrime (NumbersDVR.specialIdeal (mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.oneBlock
        (IndefiniteRowSideFullHecke.Kleiman2.blockVec (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () ∘ (Equiv.refl (Fin (1 + 1))).symm)))) := by
  refine ⟨SpecialCurves.hyps.1, ?_⟩
  rw [ModelCurvesLift.oneBlock_pnPt]
  exact SpecialCurves.hyps.2.1

example (h : SpecialCurvesLift.Statement) :=
  h exO Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 1) (IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1) (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () 1
    (Equiv.refl _) _ rfl SpecialCurvesLift.hyps.1 _ SpecialCurvesLift.hyps.2 le_rfl

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SpecialModelPoint.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    [Algebra (FractionRing O) Ω] [IsScalarTower O (FractionRing O) Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K), IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase O y k₀ →
    ∀ (Ω' : Type) [Field Ω'] [Algebra (IsLocalRing.ResidueField O) Ω'] (y' : (Σ k, ι k) → Ω'),
      (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) →
      NumbersDVR.specialIdeal (mIdealOver O y) ≤ mIdealOver (IsLocalRing.ResidueField O) y' →
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase (IsLocalRing.ResidueField O) y' k₀

theorem SpecialModelPoint.hyps :
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () ∧
      (∀ k, ∃ i, IndefiniteRowSideFullHecke.Kleiman2.pnPt (IsLocalRing.ResidueField exO) 1 ⟨k, i⟩ ≠ 0) ∧
      NumbersDVR.specialIdeal (mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1)) ≤
        mIdealOver (IsLocalRing.ResidueField exO) (IndefiniteRowSideFullHecke.Kleiman2.pnPt (IsLocalRing.ResidueField exO) 1) := by
  refine ⟨isModelWithBase_exO_pnPt, fun _ => ⟨0, IndefiniteRowSideFullHecke.Kleiman2.pnPt_ne_zero _ 1 _⟩, ?_⟩
  rw [specialIdeal_exO_pnPt]
  exact bot_le

example (h : SpecialModelPoint.Statement) :=
  h exO (IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1) Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 1) (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) ()
    SpecialModelPoint.hyps.1 _ (IndefiniteRowSideFullHecke.Kleiman2.pnPt (IsLocalRing.ResidueField exO) 1) SpecialModelPoint.hyps.2.1
    SpecialModelPoint.hyps.2.2

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def VeryAmpleModel.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
        (Kleiman.IsVeryAmple Q.toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y β)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def TensorRealise.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (n : ℕ) (L : Fin n → Kleiman.LineBundle F x) (δ : Fin n → K → ℤ),
        (∀ i, BundleRealises y k₀ (L i) (δ i)) → ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in Filter.atTop,
          ((Kleiman.tensorSub (fun i => (L i).toSubSystem) T).twist (Kleiman.twistSys F x (c : ℤ))).secs =
            secOver F y (∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ n : ℕ, (Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) n ↔
        relDim (mIdealOver F y) = ((n : ℕ) : WithBot (WithTop ℤ)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def EulerPoly.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)),
    NumbersDVR.IsMultiHomogIdeal V →
      ∃ (B : ℕ) (χ : MvPolynomial K ℚ),
        (∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F V) m i)) ∧
        (∀ (m : K → ℤ) (i : ℕ), B < i → Subsingleton (cechHc ι (quotPart F V) m i)) ∧
        ∀ m : K → ℤ, ∑ i ∈ Finset.range (B + 1),
          (-1 : ℚ) ^ i * (Module.finrank F (cechHc ι (quotPart F V) m i) : ℚ) =
            eval (fun k => (m k : ℚ)) χ

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver chartRingOver)

def ModelCechRefine.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (T : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω),
      (∀ J, (T.sub J : Set Ω) = chartSecOver F y k₀ e γ J) →
      ∀ n : ℕ, Nonempty (T.H n ≃ₗ[F] cellH F y γ n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def GraphRestrict.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω)
    (K' : Type) [Field K'] [Algebra k K'] (x' : Fin (N + 1) → K') (s' : Fin m → K')
    (hxy : ∀ i, x' i ≠ 0 → x i ≠ 0),
    IsGraphGen Q n s → mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s') →
    (∃ i, x' i ≠ 0) → (∃ j, s' j ≠ 0) →
    ∃ (Q' : Kleiman.LineBundle k x') (r : Ω → K'),
      Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r ∧ IsGraphGen Q' n s'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

