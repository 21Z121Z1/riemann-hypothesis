import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0097
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormLelongCompact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceFormLelongCompact.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ (divCycle W u').support, linForm ℓ ∉ P) →
    SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) f → HasCompactSupport f →
      Tendsto (fun ε => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) f
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) (𝓝[>] 0)
        (𝓝 (∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
            varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e f (fun _ x => Real.log (h.dualNorm x)) -
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) f (fun _ x => Real.log (h.dualNorm x))))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLelongError
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix

noncomputable section

def SliceLelongError.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      Tendsto (fun k =>
          varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log (h.dualNorm x))
              (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) -
            varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log ‖linEval u x‖)
              (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegCutTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceRegCutTail.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (ε : ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W → 0 < ε →
      Tendsto (fun k => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - sliceCut h k x)
        (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegMassContinuous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceRegMassContinuous.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (w : (Fin n → ℂ) → ℝ) (C : ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W → Measurable w → (∀ x, |w x| ≤ C) →
      ContinuousOn (fun ε => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) w
        (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) (Set.Ioi 0)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegMassLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceRegMassLimit.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ (divCycle W u').support, linForm ℓ ∉ P) → ContDiff ℝ ∞ f → HasCompactSupport f →
      Tendsto (fun ε => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - f x)
            (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - f x) (fun _ x => Real.log (h.dualNorm x))) (𝓝[>] 0)
        (𝓝 (∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
            varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fun x => 1 - f x) (fun _ x => Real.log (h.dualNorm x))))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegMassMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem SliceCut.monotone {n : ℕ} (h : HermNorm n) (x : Fin n → ℂ) : Monotone fun k => sliceCut h k x := by
  intro k m hkm
  simp only [sliceCut]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkm' : (k : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkm 1
  rcases le_or_gt 0 (Real.log (h.dualNorm x)) with hL | hL
  · apply Real.smoothTransition.monotone
    have := div_le_div_of_nonneg_left hL hk hkm'
    linarith
  · have h1 : ∀ j : ℕ, Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((j : ℝ) + 1)) = 1 := fun j =>
      Real.smoothTransition.one_of_one_le (by
        have : Real.log (h.dualNorm x) / ((j : ℝ) + 1) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hL.le (by positivity)
        linarith)
    rw [h1 k, h1 m]

def SliceRegMassMono.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (ε : ℝ)
    (a b : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W → 0 < ε →
    Measurable a → Measurable b → (∀ x, 0 ≤ a x) → (∀ x, a x ≤ b x) → (∀ x, b x ≤ 1) →
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a (fun _ x => Real.log (h.dualNorm x)) ≤
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b (fun _ x => Real.log (h.dualNorm x))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceRegTail.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (a : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ (divCycle W u').support, linForm ℓ ∉ P) →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) → ContinuousOn a {x | x ≠ 0} →
      ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k, K ≤ k → ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        |varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a
            (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) -
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => sliceCut h k x * a x)
            (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))| ≤ δ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegTailMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceRegTailMass.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ (divCycle W u').support, linForm ℓ ∉ P) →
      ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k, K ≤ k → ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - sliceCut h k x)
            (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - sliceCut h k x)
            (fun _ x => Real.log (h.dualNorm x)) ≤ δ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegVarBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceRegVarBound.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (ε C : ℝ)
    (b₁ b₂ w : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W → 0 < ε →
    Measurable b₁ → Measurable b₂ → Measurable w →
    (∀ x, |b₁ x| ≤ C) → (∀ x, |b₂ x| ≤ C) → (∀ x, w x ∈ Set.Icc (0 : ℝ) 1) →
    (∀ x, |b₁ x - b₂ x| ≤ C * w x) →
      |varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b₁
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) -
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b₂
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))| ≤
        C * (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) w
            (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
          2 * varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) w
            (fun _ x => Real.log (h.dualNorm x)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionTailMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceSectionTailMass.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ (divCycle W u').support, linForm ℓ ∉ P) →
      ∀ P ∈ (divCycle W u').support,
        Tendsto (fun k => varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fun x => 1 - sliceCut h k x)
          (fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceWeightBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix

noncomputable section

def SliceWeightBound.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
      ∃ C : ℝ, ∀ (w : (Fin n → ℂ) → ℝ) (M : ℝ), Measurable w → (∀ x, |w x| ≤ M) →
        |varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
            (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x)
            (fun _ x => Real.log (h.dualNorm x))| ≤ C * M

end

end GroundTheory.Heights₂.Heights
end

