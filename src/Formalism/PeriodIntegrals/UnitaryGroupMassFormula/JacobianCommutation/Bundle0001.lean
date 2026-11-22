import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.CutDefs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.CkDefs
section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.JCC.Ck

def PartialsContinuousDifferentiable : Prop :=
  ∀ (d : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Set (Fin d → ℝ))
    (F : (Fin d → ℝ) → E) (D : Fin d → (Fin d → ℝ) → E),
    IsOpen V → (∀ i, ContinuousOn (D i) V) →
    (∀ y ∈ V, ∀ i, HasDerivAt (fun t : ℝ => F (y + t • Pi.single i (1 : ℝ))) (D i y) 0) →
    ∀ y ∈ V, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (D i y)) y

def ChartEx : Prop :=
  ∀ (k r : ℕ) (O : Set (B.Mat k r)), IsOpen O → ∀ g₀ ∈ O ∩ B.GV k r,
    ∃ (d : ℕ) (Eb : Fin d → B.Mat k r) (c : Fin d → (B.Mat k r →L[ℝ] ℝ))
      (φ : (Fin d → ℝ) → B.Mat k r) (X : Fin d → (Fin d → ℝ) → B.Mat k r)
      (V : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (π : B.Mat k r → (Fin d → ℝ)),
      (∀ a, B.inLie k r (Eb a)) ∧ (∀ Y, B.inLie k r Y → Y = ∑ a, (c a Y : ℝ) • Eb a) ∧
      IsOpen V ∧ IsOpen U ∧ g₀ ∈ U ∧ ContinuousOn φ V ∧
      (∀ y ∈ V, φ y ∈ O ∩ B.GV k r ∧ φ y ∈ U ∧ π (φ y) = y) ∧
      (∀ (n : ℕ) (i : Fin d), ContDiffOn ℝ n (X i) V) ∧ (∀ i, ∀ y ∈ V, B.inLie k r (X i y)) ∧
      (∀ i, ∀ y ∈ V, ∀ t : ℝ, φ (y + t • Pi.single i (1 : ℝ)) = φ y * NormedSpace.exp ((t : ℂ) • X i y)) ∧
      (∀ n : ℕ, ContDiffOn ℝ n π U) ∧ Set.MapsTo π U V ∧ (∀ g ∈ U, g ∈ B.GV k r → φ (π g) = g)

end PI.UnitaryGroupMassFormula.JCC.Ck
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.PRhoRw
section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.JCC

section twist

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

def twistL (A : Wp →L[ℂ] Wp) (B : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  (((ContinuousLinearMap.compL ℂ Wq Wp Wp) A).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B)).restrictScalars ℝ

end twist

variable {k r : ℕ}

theorem uwset_inv {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  obtain ⟨h1, h2, h3⟩ := hh
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh h1
  have key : ∀ v, Matrix.mulVec h v = v → Matrix.mulVec h⁻¹ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h1, fun a => ⟨key _ (h2 a).1, key _ (h2 a).2⟩, key _ h3⟩

section rho

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

end rho

end PI.UnitaryGroupMassFormula.JCC
end
end

