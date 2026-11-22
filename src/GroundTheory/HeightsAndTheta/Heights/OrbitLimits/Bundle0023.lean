import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.KerEqBotOfCoord
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0019
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartProjFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj PBlk)
open ComplexSets

def SegreChartProjFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w, Ψ w 0 = w i) →
      ∀ J ∈ segreChartComponents P σ i, IsFiniteProjection J (chartProjMatrix σ Ψ)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartSheetCompare
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm oneLine isSmoothHerm_oneLine)
open ComplexSets Matrix

def SegreChartSheetCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι), (∀ j, IsSmoothHerm (L j)) →
      ∃ C : ℝ, ∀ J ∈ segreChartComponents P σ i, ∀ (A : Matrix (Fin e) (Fin m) ℂ) (x : Fin m → ℂ)
        (s : (Fin e → ℂ) → Fin m → ℂ), x ∈ zeroSet J → IsSheetAt J A x s →
          |ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i L k ∘ s) (A *ᵥ x)| ≤
            C * |ReciprocityTheory.AnForm.maDens
              (fun _ => (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s) (A *ᵥ x)|

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreSheetFormCompare
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm pot segre oneLine isSmoothHerm_oneLine)

def SegreSheetFormCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
      ∃ C : ℝ, ∀ (z : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (U : Set (Fin e → ℂ)) (y : Fin e → ℂ),
        IsOpen U → y ∈ U → DifferentiableOn ℂ z U → (∀ k, ∃ j, z y ⟨k, j⟩ ≠ 0) →
          |ReciprocityTheory.AnForm.maDens (fun j => pot L j ∘ z) y| ≤
            C * ReciprocityTheory.AnForm.maDens
              (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) y

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsAmpleCountAlongMultiplesAmple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def AmpleCountAlongMultiples.StatementAmple : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    KH.AmpleV ℚ (KH.genIdeal y) N.a →
    (∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y) (c • N.a - fun _ => 1)) →
    (∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) N.a) →
    ∀ ε : ℝ, 0 < ε → ∃ b : ℕ, 1 ≤ b ∧ ∀ᶠ k : ℕ in atTop,
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε) *
          (((b * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y N) (chartLat y N.a) (b * k)

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsArithNakaiMoishezon
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def IsAmpleOnModel (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  ∀ e : K → ℤ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ (q : ℕ) (w : Fin q → Ω),
    (∀ j, w j ∈ chartLat y (e + (n : ℤ) • a) 1) ∧ KH.GeneratesOn y (e + (n : ℤ) • a) w

end Objects

def ArithNakaiMoishezon.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) L → IsConjInvariantH L →
    IsAmpleOnModel y L.a →
    (∀ (W : Ideal (MRing ι)) (e : ℕ), IsArithVar W (e + 1) → mCoordIdeal y ≤ W →
      0 < II K ι W (e + 1) (fun _ => L)) →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ (q : ℕ) (w : Fin q → Ω),
      (∀ j, w j ∈ chartLat y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n).a 1) ∧
      KH.GeneratesOn y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n).a w ∧
      ∃ c : ℝ, c < 1 ∧
        ∀ j, IsBoundedH (mCoordIdeal y) y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n) 1 c (w j)

section Inhabitants

open ProjLine

theorem isAmpleOnModel_projLine : IsAmpleOnModel (ι := GlobalTheory (Fin 2)) y fsLine1.a := by
  intro e
  refine ⟨(-e ()).toNat, fun n hn => ?_⟩
  obtain ⟨q, w, hw, hg, -⟩ := SmallGenTwist.smallGen_zcomb (ι := GlobalTheory (Fin 2)) y (fsH (GlobalTheory (Fin 2)))
    (SmallGenTwist.smallGen_fsH _) 0 (e () + n).toNat
  have ha : (HermLine.zcomb (fsH (GlobalTheory (Fin 2))) (fsH (GlobalTheory (Fin 2))) ((0 : ℕ) : ℤ)
      (((e () + n).toNat : ℕ) : ℤ)).a = e + (n : ℤ) • fsLine1.a := by
    funext k
    obtain rfl : k = () := rfl
    have h1 : fsLine1.a () = 1 := rfl
    have h2 : (fsH (GlobalTheory (Fin 2))).a () = 1 := by rw [SmallGenTwist.fsH_a]
    simp only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
    omega
  exact ⟨q, w, fun j => ha ▸ hw j, ha ▸ hg⟩

theorem ArithNakaiMoishezon.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ (⊥ : Ideal (MRing (GlobalTheory (Fin 2)))) ≤ mCoordIdeal y ∧
      IsSemipositiveRel ⊥ (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1 ∧ IsConjInvariantH fsLine1 ∧
      IsAmpleOnModel (ι := GlobalTheory (Fin 2)) y fsLine1.a :=
  ⟨G1.hyps_inhabited.1, bot_le, G1.hyps_inhabited.2.2.2.1, G1.hyps_inhabited.2.2.2.2.2,
    isAmpleOnModel_projLine⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsConeComplexBaseChange
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def ConeComplexBaseChange.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (s : MRing ι) (W' : Ideal (MRing ι)) (Wa : Ideal (MRingOver ℂ ι)),
    IsArithVar P (n + 2) → s ∉ P → W' ∈ divSupp P s → IsHorizontal W' →
    Wa ∈ (W'.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
      (P.map (MvPolynomial.map (Int.castRingHom ℂ))).IsRadical ∧
      (∀ Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
        ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((n + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ∧
          MvPolynomial.map (Int.castRingHom ℂ) s ∉ Q) ∧
      Wa ∈ ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveFormNonvanishing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def CurveFormNonvanishing.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (d : K → ℕ) (g : MRing ι),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog g d → aeval y g ≠ 0 →
      ∀ z ∈ mcPts (mCoordIdeal y), eval z (map (Int.castRingHom ℂ) g) ≠ 0

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveRatSectionSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def ratLogNormPow {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n : ℕ)
    (g h : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ n))

def CurveRatSectionSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → IsSmoothHerm A →
    ∀ (n : ℕ) (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh →
      (∀ k, (dg k : ℤ) = dh k + n * A.a k) → aeval y g ≠ 0 → aeval y h ≠ 0 →
      (n : ℝ) * II K ι (mCoordIdeal y) 1 (fun _ => A) =
        vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) g -
          vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) h -
          ∑ᶠ q : projPts (mCoordIdeal y), ratLogNormPow A n g h (Quot.out q : mcPts (mCoordIdeal y))

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsDivPushSheetSum
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

section DivPt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e n : ℕ}

def divPt (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) :
    ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)

end DivPt

def DivPushSheetSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X) (BW : ∀ k, FinHolAtlas n (W k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ k, HoloMap (BW k) R.A Subtype.val) →
    (∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) →
    ∀ᵐ y, ∀ W' ∈ divSupp P s, IsHorizontal W' → ∀ w ∈ fibre W' Ψ y,
      ∑ k, (m k : ℝ) * ∑ᶠ x ∈ {x : W k | projCoord R Ψ (x : R.X) = y ∧ divPt R Ψ (x : R.X) = w},
          Real.log (B.h (R.lift x x)) *
            pushDens (BW k) (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
              (projCoord R Ψ ∘ Subtype.val) x =
        (multAt (P ⊔ Ideal.span {s}) W' : ℝ) *
          sheetDensity W' Ψ (pot L) (fun z => Real.log (B.h z)) y w

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

def trivLine : HermLine (PBlk 2) :=
  HermLine.ofWeight (fun _ => 0) (fun _ _ _ => rfl)

end Inhabitants

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftCountAlongMultiples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftCountAlongMultiples.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem) (a : ℕ) (ι' : Type) [Fintype ι'] (x' : ι' → Ω),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    1 ≤ a → (∀ j, x' j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) x' →
    Birational (fun p : Σ _ : Unit, ι' => x' p.2) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ((a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε) *
          ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y N) (chartLat y N.a) (a * k)

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjGenericRank
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjGenericRank.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ j, ∀ᵐ u, u ∈ (BV.chart j).target → (BV.chart j).symm u ∉ projRegular R Ψ BV →
      ∃ p : (k : K) → ι k,
        (∀ k, R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1 ⟨k, p k⟩ ≠ 0) ∧
        Module.finrank ℂ (LinearMap.range (fderiv ℂ
          (fun y => ReciprocityTheory.ChartRestriction.G.Geo.affCoord p
            (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm y).1)) u :
            (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) < n

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRankDropDens
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjRankDropDens.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (V : Set R.X) (BV : FinHolAtlas n V),
    (∀ j, IsSmoothHerm (L j)) → HoloMap BV R.A Subtype.val →
    ∀ j, ∀ u ∈ (BV.chart j).target, ∀ p : (k : K) → ι k,
      (∀ k, R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1 ⟨k, p k⟩ ≠ 0) →
      Module.finrank ℂ (LinearMap.range (fderiv ℂ
        (fun y => ReciprocityTheory.ChartRestriction.G.Geo.affCoord p
          (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm y).1)) u :
          (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) < n →
      locDens BV (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val) j u = 0

end GroundTheory.Heights₂.Heights.Targets
end
end

