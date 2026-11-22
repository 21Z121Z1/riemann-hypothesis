import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBundleRadicalAway
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

def universalSliceIdeal {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) :
    Ideal (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) :=
  J.map (MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ)) ⊔
    Ideal.span (Set.range fun i : Fin d => ∑ j, C (X (i, j)) * (X j - C (C (q j))))

theorem fibreIdeal_universalSliceIdeal {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (L : Matrix (Fin d) (Fin n) ℂ) :
    fibreIdeal (universalSliceIdeal J d q) (fun ij => L ij.1 ij.2) = sliceIdeal J L q := by
  rw [fibreIdeal, universalSliceIdeal, Ideal.map_sup, ← fibreIdeal, fibreIdeal_map_C, Ideal.map_span,
    sliceIdeal, ← Set.range_comp]
  have h : (MvPolynomial.map (eval fun ij : Fin d × Fin n => L ij.1 ij.2)) ∘
      (fun i : Fin d => ∑ j, C (X (i, j)) * (X j - C (C (q j)))) =
      fun i => ComplexSets.linPoly L i - C ((L *ᵥ q) i) := by
    funext i
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, map_sum]
  rw [h]

def SliceBundleRadicalAway.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical → ∀ k : Fin n,
    IsRadicalAway (universalSliceIdeal J d q) (X k - C (C (q k)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceComponents
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SliceComponents.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u ℓ : Fin n → ℂ),
    IsProjPrime J → (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      Set.InjOn (fun W => W ⊔ Ideal.span {linForm ℓ - 1}) ((divCycle J u).support : Set _) ∧
        (fun W => W ⊔ Ideal.span {linForm ℓ - 1}) '' ((divCycle J u).support : Set _) =
          (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u}).minimalPrimes ∧
        ∀ W ∈ (divCycle J u).support,
          localMult (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u})
              (W ⊔ Ideal.span {linForm ℓ - 1}) = divCycle J u W

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutOffLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

variable {n : ℕ}

def SliceCutOffLimit.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 2) g → linForm ℓ ∉ W →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
        ∀ F G : (Fin n → ℂ) → ℝ,
          (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → F (t • x) = F x) →
          (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → G (t • x) = G x) →
          ContDiffOn ℝ ∞ F {x | x ≠ 0} → ContDiffOn ℝ ∞ G {x | x ≠ 0} →
            Tendsto (fun k =>
                varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => χ k x * F x)
                  (vecCons G fun _ x => Real.log (h.dualNorm x))) atTop
              (𝓝 (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) F
                (vecCons G fun _ x => Real.log (h.dualNorm x)))) ∧
            Tendsto (fun k =>
                varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) G
                  (vecCons (fun x => χ k x * F x) fun _ x => Real.log (h.dualNorm x))) atTop
              (𝓝 (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) G
                (vecCons F fun _ x => Real.log (h.dualNorm x))))

theorem HermNorm.dualNorm_sq (h : HermNorm n) (y : Fin n → ℂ) :
    h.dualNorm y ^ 2 = ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem HermNorm.contDiff_dualNorm_sq (h : HermNorm n) :
    ContDiff ℝ ∞ fun y : Fin n → ℂ => h.dualNorm y ^ 2 := by
  simp_rw [HermNorm.dualNorm_sq]
  refine ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)

theorem HermNorm.contDiffOn_log_dualNorm (h : HermNorm n) :
    ContDiffOn ℝ ∞ (fun y : Fin n → ℂ => Real.log (h.dualNorm y)) {y | y ≠ 0} := by
  have he : (fun y : Fin n → ℂ => Real.log (h.dualNorm y)) =
      fun y => Real.log (h.dualNorm y ^ 2) / 2 := by
    funext y
    rw [Real.log_pow]
    push_cast
    ring
  rw [he]
  exact (h.contDiff_dualNorm_sq.contDiffOn.log fun y hy =>
    (pow_pos (h.dualNorm_pos hy) 2).ne').div_const 2

theorem fsLogReg_smul (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) (t : ℂ) (x : Fin n → ℂ)
    (ht : t ≠ 0) : fsLogReg h u ε (t • x) = fsLogReg h u ε x := by
  have hs : ∑ j, u j * (t • x) j = t * ∑ j, u j * x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  have ht2 : ‖t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
  unfold fsLogReg
  rw [hs, h.dualNorm_smul, norm_mul, mul_pow, mul_pow, mul_left_comm ε, ← mul_add,
    mul_div_mul_left _ _ ht2]

theorem contDiffOn_fsLogReg (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fsLogReg h u ε) {y | y ≠ 0} := by
  have hnum : ContDiff ℝ ∞ fun y : Fin n → ℂ => ‖∑ j, u j * y j‖ ^ 2 + ε * h.dualNorm y ^ 2 :=
    ((contDiff_norm_sq ℝ).comp (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j))).add
      (contDiff_const.mul h.contDiff_dualNorm_sq)
  have hpos : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < h.dualNorm y ^ 2 := fun y hy =>
    pow_pos (h.dualNorm_pos hy) 2
  refine ((hnum.contDiffOn.div h.contDiff_dualNorm_sq.contDiffOn fun y hy => (hpos y hy).ne').log
    fun y hy => ?_).div_const 2
  have := hpos y hy
  exact (div_pos (by positivity) this).ne'

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SliceDim.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) =
        ((e : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceExhaustion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix
open scoped ContDiff

noncomputable section

def SliceExhaustion.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      ∃ f : ℕ → (Fin n → ℂ) → ℝ, (∀ k, ContDiff ℝ ∞ (f k)) ∧ (∀ k, HasCompactSupport (f k)) ∧
        (∀ k x, f k x ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ x, Tendsto (fun k => f k x) atTop (𝓝 1)) ∧
        Tendsto (fun k => varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (f k)
            (fun _ x => Real.log (h.dualNorm x))) atTop
          (𝓝 (varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ => 1)
            (fun _ x => Real.log (h.dualNorm x)))) ∧
        (∀ W ∈ (divCycle J u).support,
          Tendsto (fun k => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k)
              (fun _ x => Real.log (h.dualNorm x))) atTop
            (𝓝 (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (fun _ => 1)
              (fun _ x => Real.log (h.dualNorm x))))) ∧
        Tendsto (fun k =>
            varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log (h.dualNorm x))
                (vecCons (f k) fun _ x => Real.log (h.dualNorm x)) -
              varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log ‖linEval u x‖)
                (vecCons (f k) fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceLength.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet W ⊆ closure (zeroSet W ∩ U) ∧
        ∀ q ∈ zeroSet W ∩ U, Dense {L : Matrix (Fin d) (Fin n) ℂ |
          IsRadicalAt (sliceIdeal J L q) q ∧
            localMult (J ⊔ Ideal.span {linForm u}) W =
              localMult (sliceIdeal J L q ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q))}

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAway
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

def SliceReducedAway.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical →
    ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
      ∀ L ∈ O, ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → sliceIdeal J L q ≤ P →
        P ≠ RingHom.ker (eval q) →
          ∀ g ∈ (sliceIdeal J L q).radical, ∃ s ∉ P, s * g ∈ sliceIdeal J L q

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAwayZariski
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

def SliceReducedAwayZariski.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical →
    ∃ F : MvPolynomial (Fin d × Fin n) ℂ, F ≠ 0 ∧
      ∀ L : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F ≠ 0 →
        ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → sliceIdeal J L q ≤ P →
          P ≠ RingHom.ker (eval q) →
            ∀ g ∈ (sliceIdeal J L q).radical, ∃ s ∉ P, s * g ∈ sliceIdeal J L q

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeCollarCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def TubeCollarCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ C : ℝ, ∀ y, {y | -Real.exp 1 ≤ logAbsSq P y}.indicator (tubeDens J A P R (fun _ => euclPot)) y ≤
        C * chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ))
          (fun _ : Fin (d + 1) => euclPot) y

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeCollarMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def TubeCollarMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      Integrable ({y | -Real.exp 1 ≤ logAbsSq P y}.indicator (tubeDens J A P R (fun _ => euclPot)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeDeepMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def TubeDeepMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      Integrable ({y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeDeepRankOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def deepMap {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (I : Fin d → Fin n) (y : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  vecCons (eval y P) fun i => s y (I i)

def deepJacDet {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (I : Fin d → Fin n) (y : Fin (d + 1) → ℂ) : ℂ :=
  LinearMap.det ((fderiv ℂ (deepMap P s I) y : (Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) :
    (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ))

def TubeDeepRankOne.Statement : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (U : Set (Fin (d + 1) → ℂ)) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ),
    IsOpen U → y ∈ U → DifferentiableOn ℂ s U → (∀ y' ∈ U, A *ᵥ s y' = y') → eval y P ≠ 0 →
      ReciprocityTheory.AnForm.maDens
          (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y =
        (2 / Real.pi) ^ (d + 1) * ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 / ‖eval y P‖ ^ 2

end

end GroundTheory.Heights₂.Heights
end

