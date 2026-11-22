import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOnChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def StokesOnChart.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (f g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
    (HasCompactSupport f ∨ HasCompactSupport g) →
      chartInt J A f (vecCons g φ) = chartInt J A g (vecCons f φ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def VanishNearPoint.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ),
    J.IsPrime → x ∈ zeroLocus J → (∀ᶠ y in 𝓝 x, y ∈ zeroLocus J → eval y f = 0) → f ∈ J

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntAdd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def VarIntAdd.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (φ : Fin k → (Fin n → ℂ) → ℝ),
    J.IsPrime → Continuous f → HasCompactSupport f → Continuous g → HasCompactSupport g →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
      varInt J k (f + g) φ = varInt J k f φ + varInt J k g φ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntChartChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff

noncomputable section

def VarIntChartChange.Statement : Prop :=
  ∀ (n d : ℕ) (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ) (U U' : Set (Fin n → ℂ))
    (Φ Ψ : (Fin n → ℂ) → Fin n → ℂ) (f f' : (Fin n → ℂ) → ℝ) (φ φ' : Fin d → (Fin n → ℂ) → ℝ)
    (c : Fin d → ℝ) (g : Fin d → (Fin n → ℂ) → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    J'.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') = d →
    linForm u ∉ J → linForm u' ∉ J' →
    IsOpen U → IsOpen U' → zeroSet J \ {x | linEval u x = 0} ⊆ U →
    zeroSet J' \ {x | linEval u' x = 0} ⊆ U' →
    DifferentiableOn ℂ Φ U' → DifferentiableOn ℂ Ψ U →
    Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}) →
    Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}) →
    (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x) →
    (∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x) →
    Measurable f → Measurable f' → (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, f' x = f (Φ x)) →
    (∀ k, SmoothNear (zeroSet J) (φ k)) → (∀ k, SmoothNear (zeroSet J') (φ' k)) →
    (∀ k, DifferentiableOn ℂ (g k) U') → (∀ k, ∀ x ∈ U', g k x ≠ 0) →
    (∀ k, ∀ x ∈ U', φ' k x = φ k (Φ x) + c k * Real.log ‖g k x‖) →
    (∀ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J A → Integrable (chartAbsDens J A f φ)) →
      varInt J d f φ = varInt J' d f' φ'

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarMassNearSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def VarMassNearSmall.Statement : Prop :=
  ∀ (n d : ℕ) (W I : Ideal (MvPolynomial (Fin n) ℂ)) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (f : (Fin n → ℂ) → ℝ),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
    (∀ i, SmoothNear (zeroSet W) (φ i)) → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) →
    Continuous f → HasCompactSupport f →
      ∀ δ > 0, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧
        ∀ χ : (Fin n → ℂ) → ℝ, Continuous χ → (∀ x, |χ x| ≤ 1) → tsupport χ ⊆ U →
          |varInt W d (fun x => χ x * f x) φ| ≤ δ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarWirtinger
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

def VarWirtinger.Statement : Prop :=
  ∀ d : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ),
      J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
        Integrable (chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
            (fun _ => euclPot)) ∧
          μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ B) =
            ENNReal.ofReal (c * ∫ y, chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
              (fun _ => euclPot) y)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyMassLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def VarietyMassLower.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ∀ R : ℝ,
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R → ∀ ρ ∈ Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal (c * ρ ^ (2 * d)) ≤
          μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

variable {n : ℕ}

def fsLogReg (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) (y : Fin n → ℂ) : ℝ :=
  Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * h.dualNorm y ^ 2) / h.dualNorm y ^ 2) / 2

open Classical in

def formInt (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (e : ℕ)
    (a b : (Fin n → ℂ) → ℝ) : ℝ :=
  if hℓ : ∃ ℓ : Fin n → ℂ, linForm ℓ ∉ W then
    varInt (W ⊔ Ideal.span {linForm hℓ.choose - 1}) (e + 1) a
      (vecCons b fun _ x => Real.log (h.dualNorm x))
  else 0

theorem fsLogReg_tendsto (h : HermNorm n) (u y : Fin n → ℂ) (hy : 0 < h.dualNorm y)
    (hu : ∑ j, u j * y j ≠ 0) :
    Tendsto (fun ε => fsLogReg h u ε y) (𝓝 0) (𝓝 (fsLog h u y)) := by
  have hc : (0 : ℝ) < h.dualNorm y ^ 2 := by positivity
  have hs : (0 : ℝ) < ‖∑ j, u j * y j‖ := norm_pos_iff.mpr hu
  have hcont : ContinuousAt (fun ε : ℝ =>
      Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * h.dualNorm y ^ 2) / h.dualNorm y ^ 2) / 2) 0 := by
    refine ContinuousAt.div_const (ContinuousAt.log ?_ ?_) _
    · fun_prop
    · simp only [zero_mul, add_zero]
      positivity
  have := hcont.tendsto
  simp only [zero_mul, add_zero] at this
  unfold fsLogReg
  convert this using 2
  rw [fsLog, ← div_pow, Real.log_pow]
  push_cast
  ring

def FormIntSymm.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ) (ε δ : ℝ),
    IsProjPrime W → (∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g) →
    0 < ε → 0 < δ →
      formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε) =
        formInt h W e (fsLogReg h u' ε) (fsLogReg h u δ)

def FormIntPos.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ)
    (ε δ δ' : ℝ),
    IsProjPrime W → (∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g) →
    0 < ε → 0 < δ → δ ≤ δ' →
      formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε) + coneIntegral h W (e + 1) (fsLogReg h u δ) ≤
        formInt h W e (fsLogReg h u δ') (fsLogReg h u' ε) +
          coneIntegral h W (e + 1) (fsLogReg h u δ')

def FormIntLelong.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ) (δ : ℝ),
    IsProjPrime W → (∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g) →
    linForm u' ∉ W → 0 < δ →
      Tendsto (fun ε => formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε)) (𝓝[>] 0)
        (𝓝 (cycleIntegral h (divCycle W u') e (fsLogReg h u δ) -
          coneIntegral h W (e + 1) (fsLogReg h u δ)))

def RegConeLimit.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    IsProjPrime J → (∃ g : MvPolynomial (Fin (e + 1) × Fin n) ℂ, IsChowForm J (e + 1) g) →
    linForm u ∉ J →
      Tendsto (fun ε => coneIntegral h J e (fsLogReg h u ε)) (𝓝[>] 0)
        (𝓝 (coneIntegral h J e (fsLog h u)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsLocalBranches
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

def BranchesToGoodPosition.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J (d + 1) p) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
    p ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
    (∃ N ∈ 𝓝 p, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 p, ∀ b, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | GroundTheory.Heights₂.Heights.linEval u x = 0}) →
    (∀ b, GroundTheory.Heights₂.Heights.VanishesToOrder
      (fun t => GroundTheory.Heights₂.Heights.linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      ∃ (q : Fin n → ℂ) (π : Matrix (Fin d) (Fin n) ℂ) (U : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ))
        (ρ : ℝ), GoodPosition J W u q π U V ρ (∑ b, ord b)

def GoodPositionToBranches.Statement : Prop :=
  ∀ (n e : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ)
    (π : Matrix (Fin e) (Fin n) ℂ) (U : Set (Fin n → ℂ)) (V : Set (Fin e → ℂ)) (ρ : ℝ) (N : ℕ),
    IsAffVariety J (e + 1) → linForm u ∉ J → W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
    GoodPosition J W u p π U V ρ N →
      ∃ (q : Fin n → ℂ) (m : ℕ) (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J (e + 1) q)
        (ord : Fin m → ℕ),
        q ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧
        (∃ N' ∈ 𝓝 q, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N' ⊆ ⋃ b, (γ b).image) ∧
        (∃ N' ∈ 𝓝 q, ∀ b, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ N' ⊆ (γ b).slice) ∧
        (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | GroundTheory.Heights₂.Heights.linEval u x = 0}) ∧
        (∀ b, GroundTheory.Heights₂.Heights.VanishesToOrder
          (fun t => GroundTheory.Heights₂.Heights.linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
        ∑ b, ord b = N

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsSheetMeasurable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def SheetSumMeasurable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    Measurable g → (∀ k, SmoothNear (zeroSet J) (φ k)) →
      Measurable (chartDens J A g φ) ∧ Measurable (chartAbsDens J A g φ)

end

end GroundTheory.Heights₂.Heights
end

