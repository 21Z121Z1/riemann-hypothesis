import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZCombExpand
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def ZCombExpand.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (d : ℕ) (M H : HermLine ι) (q p : ℕ),
      IsArithVar P d → IsSmoothHerm M → IsSmoothHerm H →
      I P d (fun _ => HermLine.zcomb M H (q : ℤ) (p : ℤ)) =
          ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * (q : ℝ) ^ (d - i) * (p : ℝ) ^ i *
            I P d (fun j : Fin d => if (j : ℕ) < d - i then M else H) ∧
        (1 ≤ d → I P d (fun j : Fin d => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ)) =
          ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * (q : ℝ) ^ (d - 1 - i) * (p : ℝ) ^ i *
            I P d (fun j : Fin d => if (j : ℕ) < d - i then M else H))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZCombLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ZCombLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A B : HermLine ι) (II : IntersectionSystem) (k : ℕ),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → IsSmoothHerm A → IsSmoothHerm B →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p q : ℕ, 0 < p → 0 < q → (p : ℝ) / q < δ →
      |II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A B ((q : ℤ) - k * p) p) /
          (q : ℝ) ^ (D + 1) - II K ι (mCoordIdeal y) (D + 1) (fun _ => A)| < ε ∧
      |(genDeg (mCoordIdeal y) D (HermLine.zcomb A B ((q : ℤ) - k * p) p).a : ℝ) / (q : ℝ) ^ D -
          genDeg (mCoordIdeal y) D A.a| < ε

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

