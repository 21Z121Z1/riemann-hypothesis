import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StDiagFibreFubini
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def diagWordMomentPoly (k i : ℕ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure)
    (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
    (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd]
      (pderiv 0 (pderiv 1 ((X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) : MvPolynomial (Fin 2) ℝ))))

def DiagFibreFubini.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
      ∃ Λ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ,
        (∀ i < k, diagInt S.WW S.g S.h X₀ X₁ (word D k i X₀ X₁ A₀) =
          2 ^ (2 * k) * Λ (diagWordMomentPoly k i)) ∧
        ptsIntegral S.WW
            (pot (Fin.cons X₀ (mix (2 * k - 1) X₁ A₀ : Fin D → HermLine S.WIdx) : Fin (D + 1) → HermLine S.WIdx))
            (fun _ => 1) =
          -(2 ^ (2 * k) * Λ (pushMomentPoly k))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StDiagFibreMoment
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def DiagFibreMoment.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
      ∑ i ∈ Finset.range k, diagInt S.WW S.g S.h X₀ X₁ (word D k i X₀ X₁ A₀) =
        -kappa k * ptsIntegral S.WW
          (pot (Fin.cons X₀ (mix (2 * k - 1) X₁ A₀ : Fin D → HermLine S.WIdx) : Fin (D + 1) → HermLine S.WIdx))
          (fun _ => 1)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StWWFibrePoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def wwLinPot {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (X₀ X₁ A₀ : HermLine ι) (k : ℕ)
    (u : ℕ → Fin 2 → ℝ) : Fin e → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z =>
    if (j : ℕ) < 2 * k then u j 0 * Real.log (X₀.h z) + u j 1 * Real.log (X₁.h z) else Real.log (A₀.h z)

def wwLinProd (k : ℕ) (u : ℕ → Fin 2 → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∏ n ∈ Finset.range (2 * k), (C (u n 0) * X 0 + C (u n 1) * X 1)

def wwFibreMoment (w : S2 × S2 → ℝ) (Q : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure) w
    (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] (pderiv 0 (pderiv 1 Q)))

def wwLogWeight (p : S2 × S2) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2)

def WWFibrePoly.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
      ∃ Λ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ, ∀ u : ℕ → Fin 2 → ℝ,
        ptsIntegral S.WW (wwLinPot (e := D + 1) X₀ X₁ A₀ k u) (diagLogNorm S.g S.h X₀ X₁) =
            2 ^ (2 * k) * Λ (wwFibreMoment wwLogWeight (wwLinProd k u)) ∧
          ptsIntegral S.WW (wwLinPot (e := D + 1) X₀ X₁ A₀ k u) (fun _ => 1) =
            2 ^ (2 * k) * Λ (wwFibreMoment (fun _ => 1) (wwLinProd k u))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.XiPluckerRel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace ProjectiveLineBundle

variable {D : ℕ} (S : ProjectiveLineBundle D)

def pluckerWW (k m : S.κ) : MRing S.WIdx :=
  X ⟨.line0, k⟩ * X ⟨.line1, m⟩ - X ⟨.line0, m⟩ * X ⟨.line1, k⟩

def IsPluckerRel (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx) : Prop :=
  (∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3))) ∧
    ∀ i l k m, S.g * rename (T.yyEmb 0) (F i l k m) -
      S.h * S.pluckerWW k m * X ⟨.det, l⟩ * X ⟨.base, i⟩ ^ N ∈ S.WW

end ProjectiveLineBundle

def PluckerRel.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D), ∃ (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx), S.IsPluckerRel N F

section Inhabit

def exPluckerF : Unit → Unit → Unit ⊕ Unit → Unit ⊕ Unit → MRing ExY
  | _, _, .inl _, .inr _ => X ⟨.base, ()⟩ ^ 3
  | _, _, .inr _, .inl _ => -X ⟨.base, ()⟩ ^ 3
  | _, _, _, _ => 0

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter
end

