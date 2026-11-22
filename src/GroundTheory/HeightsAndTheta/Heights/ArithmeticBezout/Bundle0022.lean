import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartResidueDegreeAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartResidueDegreeAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t → W ∈ relComps (I ⊔ Ideal.span {linForm u}) → q ∈ incIdeal W e →
        linForm t ∉ W →
          Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ chartIdeal I t e p W) = 1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncidenceZeroLocus
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncidenceZeroLocus.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsHomogIdeal Q →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] (v : Fin k × Fin n → Ω),
      (∀ g ∈ incIdeal Q k, aeval v g = 0) →
        ∃ y : Fin n → Ω, y ≠ 0 ∧ (∀ q ∈ Q, aeval y q = 0) ∧ ∀ i, ∑ j, v (i, j) * y j = 0

section Inhabitants

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isProjPrime_span_X_zero (F : Type*) [Field F] :
    IsProjPrime (Ideal.span {(X 0 : MvPolynomial (Fin 2) F)}) where
  isPrime := (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime
  isHomog := by
    rw [isHomogIdeal_iff]
    refine Ideal.homogeneous_span _ _ fun x hx => ⟨1, ?_⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [mem_homogeneousSubmodule]
    exact isHomogeneous_X _ _
  isRelevant := ⟨1, by
    rw [Ideal.mem_span_singleton]
    intro h
    have := (X_dvd_X (R := F)).mp h
    exact absurd this (by decide)⟩

def linearFormX0 (Ω : Type*) [Zero Ω] [One Ω] : Fin 1 × Fin 2 → Ω := fun ij => if ij.2 = 0 then 1 else 0

theorem linearFormX0_mem_incidence :
    linearFormX0 (AlgebraicClosure ℚ) ∈ incidence (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 := by
  refine ⟨![0, 1], fun h => one_ne_zero (congrFun h 1), fun g hg => ?_, fun i => ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hg
    simp
  · simp [linearFormX0]

theorem IncidenceZeroLocus.hypotheses_inhabited :
    IsHomogIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) ∧
      ∀ g ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1,
        aeval (linearFormX0 (AlgebraicClosure ℚ)) g = 0 := by
  refine ⟨(isProjPrime_span_X_zero ℚ).isHomog, fun g hg => ?_⟩
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
  exact hg _ linearFormX0_mem_incidence

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionOrderAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

open Classical in

def SectionOrderAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      specFirst f u ≠ 0 ∧ ∀ q : MvPolynomial (Fin e × Fin n) F, Irreducible q →
        emultiplicity q (specFirst f u) =
          ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e,
            ((divCycle I u W : ℕ) : ℕ∞)

end GroundTheory.Heights₂.Heights
end

