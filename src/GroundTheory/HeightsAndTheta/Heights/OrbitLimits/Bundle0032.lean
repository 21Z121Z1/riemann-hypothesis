import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftBlockDatum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.DivPushResSideInhabitants

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSheetLift
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet bsmul eval_bsmul_of_isMultiHomog
  prod_update_eq)

namespace SheetLift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem bsmul_mem {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : bsmul c z ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · obtain ⟨S, hS, hPS⟩ := hP
    have hle : P ≤ RingHom.ker ((eval (bsmul c z)).comp (map (Int.castRingHom ℂ))) := by
      rw [hPS, Ideal.span_le]
      intro g hg
      obtain ⟨a, ha⟩ := hS g hg
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, eval_bsmul_of_isMultiHomog ha c z,
        hz.2 g (by rw [hPS]; exact Ideal.subset_span hg), mul_zero]
    exact hle hf

omit [∀ k, Fintype (ι k)] in

theorem segre_bsmul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (bsmul c z) = fun i => (∏ k, c k) * segre z i := by
  funext i
  simp only [segre, bsmul, Finset.prod_mul_distrib]

def lift [DecidableEq K] (i0 : (k : K) → ι k) (k0 : K) (w : ((k : K) → ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => (if p.1 = k0 then w i0 else 1) * (w (Function.update i0 p.1 p.2) / w i0)

theorem lift_segre [DecidableEq K] (i0 : (k : K) → ι k) (k0 : K) {z : (Σ k, ι k) → ℂ}
    (hz : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) = bsmul (fun k => (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩) z := by
  have h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp hz) k (Finset.mem_univ k)
  funext ⟨k, j⟩
  have e1 : segre z (Function.update i0 k j) = z ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ :=
    prod_update_eq z i0 k j
  have e2 : segre z i0 = z ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ := by
    have := prod_update_eq z i0 k (i0 k)
    rwa [Function.update_eq_self] at this
  have hQ : ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' _ => h0 k'
  have hk := h0 k
  simp only [lift, bsmul]
  rw [e1, e2]
  field_simp

theorem lift_spec [DecidableEq K] {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (i0 : (k : K) → ι k)
    (k0 : K) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hne : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) ∈ mcPts P ∧ segre (lift i0 k0 (segre z)) = segre z := by
  have h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp hne) k (Finset.mem_univ k)
  rw [lift_segre i0 k0 hne]
  refine ⟨bsmul_mem hP (fun k => div_ne_zero (by split_ifs <;> simp [hne]) (h0 k)) hz, ?_⟩
  have hprod : ∏ k, (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩ = 1 := by
    rw [Finset.prod_div_distrib, Finset.prod_ite_eq' Finset.univ k0, if_pos (Finset.mem_univ _)]
    exact div_self hne
  rw [segre_bsmul, hprod]
  funext i
  rw [one_mul]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem differentiableAt_lift [DecidableEq K] {e : ℕ} (i0 : (k : K) → ι k) (k0 : K)
    {h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ} {y : Fin e → ℂ} (hd : DifferentiableAt ℂ h y)
    (hne : h y i0 ≠ 0) : DifferentiableAt ℂ (fun y' => lift i0 k0 (h y')) y := by
  have hc : ∀ i, DifferentiableAt ℂ (fun y' => h y' i) y := fun i => differentiableAt_pi.mp hd i
  refine differentiableAt_pi.mpr fun p => ?_
  simp only [lift, div_eq_mul_inv]
  refine DifferentiableAt.mul ?_ ((hc (Function.update i0 p.1 p.2)).mul ((hc i0).inv hne))
  by_cases hp : p.1 = k0
  · simp only [hp, if_true]
    exact hc i0
  · simp only [hp, if_false]
    exact differentiableAt_const _

theorem proof : SheetLift.Statement := by
  intro K _ ι _ P e Ψ y h hP hev
  classical
  obtain ⟨hd0, ⟨z0, hz0, hs0⟩, -⟩ := hev.self_of_nhds
  rcases isEmpty_or_nonempty K with hK | ⟨⟨k0⟩⟩
  · refine ⟨fun _ => z0, hs0, hev.mono fun y' ⟨_, ⟨z, hz, hs⟩, hΨ⟩ => ?_⟩
    have hzz : z0 = z := funext fun p => (IsEmpty.false p.1).elim
    refine ⟨differentiableAt_const _, hzz ▸ hz, ?_⟩
    show Ψ (segre z0) = _
    rw [hzz, hs]
    exact hΨ
  · choose i0 hi0 using hz0.1
    have hy : h y i0 ≠ 0 := by
      rw [← hs0]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hi0 k
    have hnear : ∀ᶠ y' in 𝓝 y, h y' i0 ≠ 0 :=
      (differentiableAt_pi.mp hd0 i0).continuousAt.eventually_ne hy
    refine ⟨fun y' => lift i0 k0 (h y'), ?_, (hev.and hnear).mono fun y' ⟨⟨hd, ⟨z, hz, hs⟩, hΨ⟩, hne⟩ => ?_⟩
    · show segre (lift i0 k0 (h y)) = h y
      rw [← hs0]
      exact (lift_spec hP i0 k0 hz0 (hs0 ▸ hy)).2
    · have hne' : segre z i0 ≠ 0 := hs ▸ hne
      obtain ⟨h1, h2⟩ := lift_spec hP i0 k0 hz hne'
      refine ⟨differentiableAt_lift i0 k0 hd hne, ?_, ?_⟩
      · show lift i0 k0 (h y') ∈ mcPts P
        rw [← hs]
        exact h1
      · show Ψ (segre (lift i0 k0 (h y'))) = _
        rw [← hs, h2, hs]
        exact hΨ

end SheetLift

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatFibreAvoid
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

def RatFibreAvoid.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q f : MvPolynomial (Fin n) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → f ∉ J →
      ∀ᵐ (y : Fin d → ℂ), ∀ x ∈ RatChart.ratFibre J p q y, eval x f ≠ 0

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatPosPartLocal
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

def RatChart.ratPosDens {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  RatChart.ratSheetSum J p q (fun x s => max (f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y

def RatPosPartLocal.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (x : Fin n → ℂ),
    Measurable f → (∀ k, SmoothNear (ComplexSets.zeroSet J) (φ k)) →
    (∃ s, IsSheetAt J A x s) → (∃ s', RatChart.IsRatSheetAt J p q x s') →
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ x ∈ W ∧
        ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) =
            ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (E.indicator f) φ y)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatSheetCover
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

def RatSheetCover.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      ∀ᵐ (y : Fin d → ℂ), ∀ x ∈ RatChart.ratFibre J p q y, ∃ s, RatChart.IsRatSheetAt J p q x s

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatSheetNoChartNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

def RatSheetNoChartNull.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ComplexSets.IsFiniteProjection J A →
    (∀ y, (RatChart.ratFibre J p q y).Finite) →
      volume (RatChart.ratMap p q ''
        {x | x ∈ ComplexSets.zeroSet J ∧ (∃ s, RatChart.IsRatSheetAt J p q x s) ∧
          ¬ ∃ s', IsSheetAt J A x s'}) = 0

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatSheetSumMeasurable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

def RatSheetSumMeasurable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (Φ : ℝ → ℝ → ℝ) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    (∀ y, (RatChart.ratFibre J p q y).Finite) → Measurable (Function.uncurry Φ) → Measurable g →
      Measurable fun y => RatChart.ratSheetSum J p q
        (fun x s => Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y)) y

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsDivPushResOrderSum
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

open Classical in

def sncMult {X : Type*} {r : ℕ} (m : Fin r → ℕ) (W : Fin r → Set X) (x : X) : ℕ :=
  ∑ k, if x ∈ W k then m k else 0

def DivPushResOrderSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (A : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) →
    ∀ᵐ y, ∀ W' ∈ divSupp P s, IsHorizontal W' → ∀ w ∈ fibre W' Ψ y,
      ∀ Wa ∈ (W'.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
      (∃ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ (∀ f ∈ Wa, eval z f = 0) ∧ segre z = w) →
        multAt ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))) Wa =
          ∑ᶠ x ∈ {x : R.X | projCoord R Ψ x = y ∧ divPt R Ψ x = w}, sncMult m W x

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphMetric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftGraphMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (a r : ℕ) (v : Fin r → Ω),
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    (∀ j, v j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) v →
    ∃ A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι r), A.a = unitDeg (none : Option K) ∧ IsConjInvariantH A ∧
      IsSemipositiveRel (mCoordIdeal (addBlock y v)) (mCoordIdeal (addBlock y v)) A ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin r,
        secNormAt y N a (v j) (basePart₂ z) * A.h z = ‖z ⟨none, j⟩‖

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftGraphPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (n : K → ℤ) (r : ℕ) (v : Fin r → Ω),
    (∀ j, v j ∈ chartLat y n 1) → KH.GeneratesOn y n v →
    ∀ w ∈ mcPts (mCoordIdeal y), ∃ z ∈ mcPts (mCoordIdeal (addBlock y v)), basePart₂ z = w

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjFullRankDense
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def projFullRank {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {n : ℕ} (R : AnLogRes P J (n + 1)) {V : Set R.X} (BV : FinHolAtlas n V) : Set V :=
  {x | ∃ p : (k : K) → ι k, (∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) ∧ ∃ j, x ∈ (BV.chart j).source ∧
    Module.finrank ℂ (LinearMap.range (fderiv ℂ
      (fun y => ReciprocityTheory.ChartRestriction.G.Geo.affCoord p (R.lift x.1 ((BV.chart j).symm y).1)) (BV.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) = n}

def ProjFullRankDense.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ x ∈ projFullRank R BV, x ∈ interior (closure (projRegular R Ψ BV))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegularClosureOpen
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjRegularClosureOpen.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsOpen (closure (projRegular R Ψ BV))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegularNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjRegularNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ j, volume ((BV.chart j).target ∩ (BV.chart j).symm ⁻¹'
      (interior (closure (projRegular R Ψ BV)) \ projRegular R Ψ BV)) = 0

end GroundTheory.Heights₂.Heights.Targets
end
end

