import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeMassOfFibre.Statement : Prop :=
  ∀ (n m δ : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    IsProjPrime J →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = δ) →
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} =
        (δ : ENNReal) * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0}

theorem ConeMassOfFibre.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      ∀ᵐ π : Fin 1 → Fin 1 → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 1),
        fibreCount (HermNorm.std 1) ⊥ π w = ((1 : ℕ) : ℕ∞) := by
  refine ⟨isProjPrime_point ℂ, ?_⟩
  have hnull : ∀ᵐ π : Fin 1 → Fin 1 → ℂ, π 0 0 ≠ 0 := by
    have hp : MeasurePreserving (fun π : Fin 1 → Fin 1 → ℂ => π 0 0) :=
      (volume_preserving_funUnique (Fin 1) ℂ).comp
        (volume_preserving_funUnique (Fin 1) (Fin 1 → ℂ))
    rw [ae_iff]
    have hset : {π : Fin 1 → Fin 1 → ℂ | ¬ π 0 0 ≠ 0} = (fun π => π 0 0) ⁻¹' {0} := by
      ext π; simp
    rw [hset, hp.measure_preimage (measurableSet_singleton 0).nullMeasurableSet]
    simp
  filter_upwards [hnull] with π hπ
  refine Filter.Eventually.of_forall fun w => ?_
  have hfib : {y | y ∈ coneSet (HermNorm.std 1) ⊥ ∧ linProj π y = w} =
      {WithLp.toLp 2 fun _ => w 0 / π 0 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, coneSet, Ideal.mem_bot]
    constructor
    · rintro ⟨-, hy⟩
      have h0 := congrArg (fun v : EuclideanSpace ℂ (Fin 1) => v 0) hy
      simp only [linProj, Fin.sum_univ_one] at h0
      ext i
      fin_cases i
      simp only [Fin.zero_eta, Fin.isValue]
      rw [← h0]
      field_simp
    · rintro rfl
      refine ⟨fun q hq => by simp [hq], ?_⟩
      ext i
      fin_cases i
      simp [linProj]
      field_simp
  rw [fibreCount, hfib, Set.encard_singleton]
  rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFiniteFibresDimLe
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def FiniteFibresDimLe.Statement : Prop :=
  ∀ (n d : ℕ) (Q : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), Q.IsPrime →
    (∀ y : Fin d → ℂ, (ComplexSets.fibre Q A y).Finite) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤ ((d : ℕ) : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsHolomorphicImplicitGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

def HolomorphicImplicitGraph.Statement : Prop :=
  ∀ (n m : ℕ) (f : Fin (n - m) → EuclideanSpace ℂ (Fin n) → ℂ) (y : EuclideanSpace ℂ (Fin n))
    (V : Set (EuclideanSpace ℂ (Fin n))),
    (∀ i, ContDiff ℂ 1 (f i)) → IsOpen V → y ∈ V → (∀ i, f i y = 0) →
    finrank ℂ ↥(⨅ i, LinearMap.ker (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin n))) = m →
      ∃ (e : Fin n ≃ Fin m ⊕ Fin (n - m)) (Ω : Set (EuclideanSpace ℂ (Fin m)))
        (Φ : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m)))
        (U : Set (EuclideanSpace ℂ (Fin n))),
        IsOpen U ∧ y ∈ U ∧ U ⊆ V ∧ IsOpen Ω ∧ DifferentiableOn ℂ Φ Ω ∧
        graphPt e Φ '' Ω = {z | z ∈ U ∧ ∀ i, f i z = 0} ∧
        ∀ x ∈ Ω, LinearMap.range (fderiv ℂ (graphPt e Φ) x :
            EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) =
          ⨅ i, LinearMap.ker (fderiv ℂ (f i) (graphPt e Φ x) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncIdealSeparate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncIdealSeparate.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P Q : Ideal (MvPolynomial (Fin n) F)),
    IsProjPrime P → IsProjPrime Q → incIdeal Q k ≠ ⊥ → incIdeal Q k ≤ incIdeal P k → Q ≤ P

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPolyLocalGenerators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

def polyTangent {n : ℕ} (S : Set (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    Submodule ℂ (Fin n → ℂ) where
  carrier := {v | ∀ q ∈ S, ∑ j, eval p (pderiv j q) * v j = 0}
  add_mem' {v w} hv hw q hq := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hv hw ⊢
    rw [hv q hq, hw q hq, add_zero]
  zero_mem' q _ := by simp
  smul_mem' c v hv q hq := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum] at hv ⊢
    rw [hv q hq, mul_zero]

def PolyLocalGenerators.Statement : Prop :=
  ∀ (n m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = m →
    ∀ p : Fin n → ℂ, (∀ q ∈ J, eval p q = 0) →
      finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p) = m →
      ∃ (q : Fin (n - m) → MvPolynomial (Fin n) ℂ) (g : MvPolynomial (Fin n) ℂ),
        (∀ i, q i ∈ J) ∧ eval p g ≠ 0 ∧ finrank ℂ (polyTangent (Set.range q) p) = m ∧
        ∀ r ∈ J, g * r ∈ Ideal.span (Set.range q)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def projVar (e : ℕ) (i : Fin (e + 1)) : FractionRing (MvPolynomial (Fin (e + 1)) ℂ) :=
  algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (X i)

def projPar {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) :
    Vertical.Par e n → FractionRing (MvPolynomial (Fin (e + 1)) ℂ)
  | .inl (i, j) =>
      projVar e i.succ * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) -
        projVar e 0 * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A i.succ j)
  | .inr j => algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) / projVar e 0

def ProjSecDegree.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    ComplexSets.projDegree J A =
      Module.finrank (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
        (Vertical.SecAlg
          (J.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecDegreeGe.Statement : Prop :=
  ∀ (k E : Type) [Field k] [PerfectField k] [Field E] [Algebra k E] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → E),
    IsProjPrime Q → IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      eval (fun j => y (.inr j)) (Vertical.specRest (algebraMap k E) g y) ≠ 0 →
        Module.Finite E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) ∧
          δ ≤ Module.finrank E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecDegreeLe.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → E),
    IsProjPrime Q → IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      Module.Finite E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      IsDomain (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      Algebra.IsSeparable E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      Vertical.specRest (algebraMap k E) g y ≠ 0 →
        Module.finrank E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) ≤ δ

namespace SecDegreeLe

abbrev pointSecAlg : Type :=
  Vertical.SecAlg ((⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).map (MvPolynomial.map (algebraMap ℚ ℚ)))
    (fun _ : Vertical.Par 0 1 => (1 : ℚ))

end SecDegreeLe

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecFiniteUnit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecFiniteUnit.Statement : Prop :=
  ∀ (k R : Type) [Field k] [CommRing R] [Algebra k R] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R), IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      IsUnit (eval (fun j => y (.inr j)) (Vertical.specRest (algebraMap k R) g y)) →
        Module.Finite R (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k R))) y)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecRankSpecialize
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecRankSpecialize.Statement : Prop :=
  ∀ (R K κ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field κ] [Algebra R κ] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Vertical.Par e n → R),
    Function.Surjective (algebraMap R κ) → Module.Finite R (Vertical.SecAlg Q y) →
      Module.finrank K
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y)) ≤
        Module.finrank κ
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))

theorem SecRankSpecialize.hypotheses_inhabited :
    letI : Algebra (PowerSeries ℚ) ℚ := (PowerSeries.constantCoeff (R := ℚ)).toAlgebra
    IsDomain (PowerSeries ℚ) ∧ IsLocalRing (PowerSeries ℚ) ∧
      IsFractionRing (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) ∧
      Function.Surjective (algebraMap (PowerSeries ℚ) ℚ) ∧
      Module.Finite (PowerSeries ℚ)
        (Vertical.SecAlg (⊥ : Ideal (MvPolynomial (Fin 1) (PowerSeries ℚ)))
          (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ))) := by
  letI : Algebra (PowerSeries ℚ) ℚ := (PowerSeries.constantCoeff (R := ℚ)).toAlgebra
  refine ⟨inferInstance, inferInstance, inferInstance,
    fun a => ⟨PowerSeries.C a, by simp [RingHom.algebraMap_toAlgebra]⟩, ?_⟩
  set I := Vertical.secIdeal (⊥ : Ideal (MvPolynomial (Fin 1) (PowerSeries ℚ)))
    (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ))
  have hX : ∀ j : Fin 1, Ideal.Quotient.mk I (X j) = 1 := by
    intro j
    rw [Fin.fin_one_eq_zero j, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_sup_right (Ideal.subset_span ?_)
    simp [Vertical.chartForm, linForm]
  have hrange : ∀ p : MvPolynomial (Fin 1) (PowerSeries ℚ),
      Ideal.Quotient.mk I p ∈ Set.range (algebraMap (PowerSeries ℚ) (Vertical.SecAlg ⊥
        (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ)))) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact ⟨a, rfl⟩
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
    | mul_X p j hp =>
      obtain ⟨a, ha⟩ := hp
      exact ⟨a, by rw [map_mul, hX, mul_one, ha]⟩
  refine Module.Finite.of_surjective (Algebra.linearMap (PowerSeries ℚ) _) ?_
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hrange p

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsThroughTwoPointsTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ThroughTwoPointsTrdeg.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] (n k : ℕ) [Algebra K Ω]
    [Algebra (MvPolynomial (Fin k × Fin n) K) Ω] [IsScalarTower K (MvPolynomial (Fin k × Fin n) K) Ω],
    Function.Injective (algebraMap (MvPolynomial (Fin k × Fin n) K) Ω) →
    ∀ x c : Fin n → K, ∑ j, c j * x j = 1 →
    ∀ (y : Fin n → Ω) (j : Fin n), y j ≠ 0 → (∀ t : Ω, y ≠ fun m => t * algebraMap K Ω (x m)) →
      (∀ i, ∑ m, algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (genSubst x c (i, m)) * y m = 0) →
        (k : Cardinal) ≤ Algebra.trdeg K (Algebra.adjoin K (Set.range fun m => y m * (y j)⁻¹))

section Inhabitants

def pointOffFirstAxis : Fin 3 → FractionRing (MvPolynomial (Fin 1 × Fin 3) ℚ) :=
  fun m => algebraMap (MvPolynomial (Fin 1 × Fin 3) ℚ) _
    (![0, X (0, 2), -X (0, 1)] m)

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

