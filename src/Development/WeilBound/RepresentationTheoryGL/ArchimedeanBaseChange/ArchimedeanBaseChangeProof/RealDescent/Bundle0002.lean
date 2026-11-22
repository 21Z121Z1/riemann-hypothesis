import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RGrowthPiJ
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F
open scoped Classical

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

def GrowthPiJ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (n : ℕ), 1 ≤ n →
  ∀ [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] [MeasurableSpace (GA E 0)] [BorelSpace (GA E 0)]
  (μ₁ : Measure (GA E n)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E 0)) [μ₂.IsHaarMeasure],
  ∃ D : Dom E n 0, (∀ F : H E n 0 → ℂ, Continuous F → HasCompactSupport F → ∫ x, F x ∂D.μ = ∫ x₁, ∫ x₂, F (x₁, x₂) ∂μ₂ ∂μ₁) ∧
    ∀ π : CuspSub E n, ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
    (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (r₀ r₁ ε : ℝ), IsTestM Φ₁ → IsTestM Φ₂ →
    (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → 0 ≤ r₀ → 0 ≤ r₁ → 0 < ε → ∃ (C : ℝ) (N : ℕ), ∀ (k : ℕ)
      (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)) (t : ℂ), IsTestM Φ → IsROp D Φ (T₁ * U * T₂) →
      (∀ f ∈ piSp D π ι, U f ∈ piSp D π ι) → (∀ f ∈ (piSp D π ι)ᗮ, U f ∈ (piSp D π ι)ᗮ) →
      D4.IsTest2J (trM Φ M) (r₀ + k * r₁) → IsTwTr D.μ π (trM Φ M) t →
      ‖ellSum2 μ₁ μ₂ (trM Φ M) - t / 2‖ ≤ C * (1 + k) ^ N * ‖U ∘L (piSp D π ι)ᗮ.subtypeL‖ + C * ‖U‖ * ε ^ k

def RGrowthPiJ : Prop := D4.EllFormula2J → PositivityTheory.Rg.BcB.E1.SFun → PiVecEx → PiInv → GrowthPiJ

end PositivityTheory.Rg.BcB.Desc

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.RgJS

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def prg (D : Dom E n 0) (ψ : Sm E n) (u : ℝ → ℂ) (φ : Sm E n) : ℂ :=
  ∫ x, starRingEnd ℂ (ψ.1 x.1 * u (ldet x)) * φ.1 x.1 ∂D.ν

def Orth (D : Dom E n 0) (π : CuspSub E n) (φ : Sm E n) : Prop :=
  ∀ ψ ∈ π.V, ∀ u : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → prg D ψ u φ = 0

def OrthCount : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∃ (ψ : ℕ → Sm E n) (u : ℕ → ℝ → ℂ), (∀ j, ψ j ∈ π.V ∧ Continuous (u j) ∧ HasCompactSupport (u j)) ∧
    ∀ φ : Sm E n, IsAutForm φ → (∀ j, prg D (ψ j) (u j) φ = 0) → Orth D π φ

def OrthAct : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ φ : Sm E n, IsAutForm φ → Orth D π φ → ∀ o, Orth D π (act o φ)

def NoPi : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ U : Submodule ℂ (Sm E n), IsStable U → (∀ φ ∈ U, IsAutForm φ ∧ Orth D π φ) →
    ∀ (z : ℂ), ∀ T : Sm E n →ₗ[ℂ] Sm E n, (∀ o, ∀ φ ∈ U, T (act o φ) = act o (T φ)) →
      (∀ φ ∈ U, ∃ ψ ∈ π.V, ∀ g, (T φ).1 g = ψ.1 g * Complex.exp (z * logAbs g.val.det)) → ∀ φ ∈ U, T φ = 0

def RNoPi : Prop := GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.CuspidalMultiplicityOne → NoPi

def TwTrEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ φ : H E n 0 → ℂ, IsTestH φ → FinOn D.μ π φ → ∃! t, IsTwTr D.μ π φ t

def AbsSplit : Prop := ForSys fun {W} q X _ A => ∀ (I : Set W), (Summable fun w : I => (q w : ℝ)⁻¹) → ∀ x₀ : X,
  (∀ w ∈ I, ∀ a, ‖A x₀ w a‖ ≤ 1) → ∀ (ι : Type) [Fintype ι] (y : ι → X),
    (∀ w, w ∉ I → ∀ k : ℕ, ∑ a, A x₀ w a ^ (k + 1) = ∑ j, ∑ b, A (y j) w b ^ (k + 1)) → ∃ j, y j = x₀

def RAbsSplit : Prop := EulerLog → Conv1 → Unb → AbsSplit

def InertThin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
  Summable fun w : {w : HeightOneSpectrum (𝓞 E) // ¬ IsSplitAt w} => (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹

def RSplitCore2 : Prop := AbsSplit → InertThin → DetOne → PrimeOff → RSplitCore

end PositivityTheory.Rg.BcB.Desc

end
end

