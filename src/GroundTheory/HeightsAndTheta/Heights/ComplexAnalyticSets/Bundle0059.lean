import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedCoverCycles
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

def PuncturedCoverCycles.Statement : Prop :=
  ∀ (n e N : ℕ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (c : Fin (e + 1) → ℂ) (r : ℝ)
    (X : Set (Fin n → ℂ)),
    0 < r → c 0 = 0 →
    (∀ x ∈ X, dist (A *ᵥ x) c < r ∧ (A *ᵥ x) 0 ≠ 0) →
    (∀ y : Fin (e + 1) → ℂ, dist y c < r → y 0 ≠ 0 → {x | x ∈ X ∧ A *ᵥ x = y}.encard = N) →
    (∀ x ∈ X, ∃ (O : Set (Fin (e + 1) → ℂ)) (V' : Set (Fin n → ℂ)) (g : (Fin (e + 1) → ℂ) → Fin n → ℂ),
      IsOpen O ∧ A *ᵥ x ∈ O ∧ IsOpen V' ∧ x ∈ V' ∧ DifferentiableOn ℂ g O ∧ g (A *ᵥ x) = x ∧
        (∀ y ∈ O, A *ᵥ g y = y) ∧ X ∩ V' = g '' O) →
    ∃ (m : ℕ) (ord : Fin m → ℕ) (ψ : Fin m → (Fin (e + 1) → ℂ) → Fin n → ℂ) (δ : ℝ),
      0 < δ ∧ δ ≤ 1 ∧ ∑ b, ord b = N ∧ (∀ b, 1 ≤ ord b) ∧
      (∀ b, DifferentiableOn ℂ (ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0})) ∧
      (∀ b, ∀ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0},
        ψ b t ∈ X ∧ A *ᵥ ψ b t = Function.update t 0 (t 0 ^ ord b)) ∧
      (∀ b, Set.InjOn (ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0})) ∧
      (∀ b b', b ≠ b' → ∀ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0},
        ∀ t' ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}, ψ b t ≠ ψ b' t') ∧
      (∀ x ∈ X, dist (A *ᵥ x) c < δ ^ N →
        ∃ b, ∃ t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}, ψ b t = x)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSectionDegreeSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SectionDegreeSum.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e δ : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 2) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 2) f → IsMultiHomog δ f → linForm u ∉ I →
      ∃ (g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin (e + 1) × Fin n) F)
        (δW : Ideal (MvPolynomial (Fin n) F) → ℕ),
        (∀ W ∈ (divCycle I u).support,
          IsProjPrime W ∧ IsChowForm W (e + 1) (g W) ∧ IsMultiHomog (δW W) (g W)) ∧
        δ = ∑ W ∈ (divCycle I u).support, divCycle I u W * δW W

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSectionHyperplaneAvoid
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SectionHyperplaneAvoid.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    IsProjPrime J → ∃ ℓ : Fin n → ℂ, linForm ℓ ∉ J ∧ ∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetComass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

variable {n d : ℕ}

def sheetJac (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ) : ℝ :=
  areaJacobian ((WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
    ((fderiv ℝ s y : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℝ] (Fin n → ℂ)) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap)

theorem sheetJac_nonneg (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ) : 0 ≤ sheetJac s y :=
  Real.sqrt_nonneg _

def SheetComass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ), (∀ k, SmoothNear (zeroSet J) (φ k)) →
    ∃ C : ℝ, ∀ x ∈ zeroSet J ∩ Metric.closedBall 0 R, ∀ s : (Fin d → ℂ) → Fin n → ℂ, IsSheetAt J A x s →
      |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ x)| ≤ C * sheetJac s (A *ᵥ x)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetLogNormDens
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SheetLogNormDens.Statement : Prop :=
  ∀ (n d m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ)
    (s : (Fin d → ℂ) → Fin n → ℂ) (T : Fin d → Matrix (Fin m) (Fin n) ℂ),
    IsSheetAt J A x s → (∀ k, T k *ᵥ x ≠ 0) →
      0 ≤ ReciprocityTheory.AnForm.maDens
        (fun k => (fun z => Real.log √(∑ i, ‖(T k *ᵥ z) i‖ ^ 2)) ∘ s) (A *ᵥ x)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetOnlyNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Matrix

noncomputable section

def SheetOnlyNull.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    IsFiniteProjection J A' →
      volume ((fun x => A *ᵥ x) ''
        {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ ¬ ∃ s', IsSheetAt J A' x s'}) = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SliceIdeal.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (F : MvPolynomial (Fin (k + 1) × Fin n) ℂ)
    (ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (k + 1) F → linForm ℓ ∉ J →
      (J ⊔ Ideal.span {linForm ℓ - 1}).IsPrime ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) = (k : ℕ) ∧
        ∀ u : Fin n → ℂ, linForm u ∉ J → linForm u ∉ J ⊔ Ideal.span {linForm ℓ - 1}

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceObjects
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

variable {n d : ℕ}

def sliceIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  J ⊔ Ideal.span (Set.range fun i => linPoly L i - C ((L *ᵥ q) i))

def IsRadicalAt (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Prop :=
  ∀ f ∈ I.radical, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧ s * f ∈ I

theorem eval_linPoly (L : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly L i) = (L *ᵥ x) i := by
  simp [linPoly, Matrix.mulVec, dotProduct]

theorem zeroSet_sliceIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) : zeroSet (sliceIdeal J L q) = zeroSet J ∩ {x | L *ᵥ x = L *ᵥ q} := by
  ext x
  simp only [zeroSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun f hf => h f (Ideal.mem_sup_left hf), funext fun i => ?_⟩
    have := h _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rwa [map_sub, eval_linPoly, eval_C, sub_eq_zero] at this
  · rintro ⟨hJ, hL⟩ f hf
    have hle : sliceIdeal J L q ≤ RingHom.ker (eval x) := by
      refine sup_le (fun g hg => RingHom.mem_ker.2 (hJ g hg)) ?_
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_linPoly, eval_C, hL, sub_self]
    exact RingHom.mem_ker.1 (hle hf)

theorem isRadicalAt_of_isRadical {I : Ideal (MvPolynomial (Fin n) ℂ)} (hI : I.IsRadical)
    (q : Fin n → ℂ) : IsRadicalAt I q :=
  fun f hf => ⟨1, by simp, by rw [one_mul]; exact hI hf⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SliceSectionMass.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ => 1)
          (fun _ x => Real.log (h.dualNorm x)) =
        ∑ W ∈ (divCycle J u).support, ((divCycle J u W : ℕ) : ℝ) *
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (fun _ => 1)
            (fun _ x => Real.log (h.dualNorm x))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetBallCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def SmallSetBallCover.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ T : Finset (Fin n → ℂ),
        (↑T : Set (Fin n → ℂ)) ⊆ zeroSet I ∩ K ∧ zeroSet I ∩ K ⊆ ⋃ c ∈ T, Metric.ball c r ∧
          (T.card : ℝ) * r ^ (2 * d) ≤ C * r ^ 2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetTubeVolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def SmallSetTubeVolume.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (zeroSet I ∩ K)) ≤
          ENNReal.ofReal (C * r ^ ((2 * n + 2 : ℤ) - 2 * d))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOffDiscriminant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def StokesOffDiscriminant.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 → (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s) →
    ∀ (F G : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
      SmoothNear (zeroSet J) F → SmoothNear (zeroSet J) G → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport F →
      (∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
        ∀ x ∈ U ∩ zeroSet J, F x = 0) →
        chartInt J A F (vecCons G φ) = chartInt J A G (vecCons F φ)

end

end GroundTheory.Heights₂.Heights
end

