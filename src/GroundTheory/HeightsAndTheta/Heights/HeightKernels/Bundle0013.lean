import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartIbpSymm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartIbpSymm.Statement : Prop :=
  ∀ (n : ℕ) (A B C D : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ),
    A.PosDef → B.PosDef → C.PosDef → D.PosDef → (∀ i, (T i).PosDef) →
    ∫ y : Fin (n + 1) → ℂ, (hermChartPot A y - hermChartPot B y) *
        maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
          fun i => hermChartPot (T i)) y =
      ∫ y : Fin (n + 1) → ℂ, (hermChartPot C y - hermChartPot D y) *
        maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
          fun i => hermChartPot (T i)) y

example : (Matrix.diagonal ![(4 : ℂ), 1, 1] : Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(1 : ℂ), 1, 9] : Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef ∧
    (∀ i : Fin 1, ((fun _ => Matrix.diagonal ![(1 : ℂ), 4, 1]) i :
      Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef) :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one,
    Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num,
    fun _ => Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLocallyPrincipalCoprime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def LocallyPrincipalCoprime.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L) (M : AddSubgroup L) (ι : Type) [Fintype ι]
    (a : ι → L),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) →
    M ≠ ⊥ → ∀ s : B, s ≠ 0 →
      ∃ (β δ : B) (I : Ideal B), β ≠ 0 ∧ δ ≠ 0 ∧ I ⊔ Ideal.span {s} = ⊤ ∧
        ∀ x : L, x ∈ M ↔ ∃ y ∈ I, (β : L) * x = δ * y

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsOrderIdealIndexExtension
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def OrderIdealIndexExtension.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L), Module.Finite ℤ B →
    ∃ (r : ℕ) (s : B), s ≠ 0 ∧ Module.finrank ℚ L = r * Module.finrank ℤ B ∧
      (∀ I : Ideal B, I ≠ ⊥ → I.toAddSubgroup.index ≠ 0) ∧
      ∀ I : Ideal B, I ≠ ⊥ → (I.IsPrincipal ∨ I ⊔ Ideal.span {s} = ⊤) →
        (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup.relIndex
            (1 : Submodule (𝓞 L) L).toAddSubgroup = I.toAddSubgroup.index ^ r

end

end GroundTheory.Heights₂.Heights
end

