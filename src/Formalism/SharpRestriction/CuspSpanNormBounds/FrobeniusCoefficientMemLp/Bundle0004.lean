import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle0003
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0005
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTurn
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.BetaCut
section
open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.BetaCut

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def coefM {k r : ℕ} {H Wp Wq : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  (innerSL ℂ ξ').smulRight (⟪v, σ g v'⟫_ℂ • ξ)

def CoefInCC : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (h : ℝ) (m : ℕ) (A : ℝ),
    IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → GapAtLeast ε lam h → ReciprocityTheory.ChartRestriction.DS.thrStar ε + m < h → A ≤ m →
    ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
      (ξ : Wp) (ξ' : Wq), Formalism.FourierDecayAlt.B.InCC (k := k) (r := r) A 5 (coefM σ v v' ξ ξ')

def BetaInfCoefNZ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (h : ℝ),
    IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → GapAtLeast ε lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h →
    ∀ (v v' : H) (l : H → Wp) (l' : H → Wq) (ξ : Wp) (ξ' : Wq),
      v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ →
      Formalism.FourierDecayAlt.ThreeDimData.be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN v v = (innerSL ℂ (l v)).smulRight (l v) →
      Formalism.FourierDecayAlt.ThreeDimData.be D.z' Formalism.QuantumDeterminants.cStd D.π' σ D.μW' D.μN v' v' = (innerSL ℂ (l' v')).smulRight (l' v') →
      ⟪l v, ξ⟫_ℂ ≠ 0 → ⟪ξ', l' v'⟫_ℂ ≠ 0 →
      Formalism.FourierDecayAlt.B.betaInf D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') ≠ 0

end Formalism.MainNotions.S.Pv.BetaCut
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesSh
section
set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.S.Pv.Frames

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Bridge Formalism.BasicNotions

variable {k r : ℕ}

theorem orbSqO_le_turn (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (hc : L.c = ((2 * ka : ℝ) : ℂ))
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (p : Point ℂ (r + 1)) :
    orbSqO L f p ≤ orbSq (turnL L ka) (turnF L ka f) (turnPt p) := by
  unfold orbSqO orbSq
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hg => ?_
  rw [← OrbInt_turn L ka hc f g ν]
  exact le_iSup_of_le (tTi k r * g * tT k r) (le_iSup_of_le (μR.map (cA k r))
    (le_iSup_of_le (ν.map (thP k r)) (le_iSup_of_le
      ⟨isPtRep_turn L ka hg.1, isRelStab_turn L ka hc hg.2.1, isRootMeas_turn L ka hka hc hg.2.2.1,
        isOrbQuot_turn L ka hg.2.2.2⟩ le_rfl)))

section OneRec

variable (D : D7)

def FrameChangeSH (Ch Cs Cn Cf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (ka b : ℝ),
    Real.exp 1 ≤ b → 0 < ka → ka ≤ b ^ Ch → ka⁻¹ ≤ b ^ Ch → L.c = ((2 * ka : ℝ) : ℂ) → L.κN ≠ ⊤ →
    L.ε = epsSH D.R → 0 < L.κN →
    StdHyp Ch Cs D.R.k D.R.rS L.ε lam0 L.u L.u' (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') ka b →
    l1dist L.lam lam0 ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    IsKFinCoefH L.σ f →
    ∃ (L₁ : LocBessel D.R.k D.R.rS) (f₁ : Mx D.R.k D.R.rS → (L₁.Wq →L[ℂ] L₁.Wp)),
      L₁.ε = L.ε ∧ L₁.lam = L.lam ∧ L₁.u = L.u ∧ L₁.u' = L.u' ∧ L₁.c = cOfDpsi ((1 : ℝ) : ℂ) ∧ 0 < L₁.κN ∧ L₁.κN ≠ ⊤ ∧
      Tz D.R.k D.R.rS L₁.z = Tz D.R.k D.R.rS L.z * ka ^ (2 * D.R.rS) ∧
      Tz D.R.k D.R.rS L₁.z' = Tz D.R.k D.R.rS L.z' * ka ^ (2 * D.R.rS) ∧
      IsKFinCoefH L₁.σ f₁ ∧
      ∀ μsec, IsSection D.R.k D.R.rS L.z L.z' μsec → ∃ μsec₁, IsSection D.R.k D.R.rS L₁.z L₁.z' μsec₁ ∧
        ∃ K₁ : ℝ, 0 < K₁ ∧
        jNorm2 L₁ f₁ μsec₁ ≤ ENNReal.ofReal K₁ * jNorm2 L f μsec ∧
        (jNorm2 L f μsec ≠ 0 → jNorm2 L₁ f₁ μsec₁ ≠ 0) ∧
        ∀ p : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p ≠ 0 →
          ∃ p₁ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁ ≠ 0 ∧
            max 1 (1 / Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁) ≤
              b ^ (Cf * (D.R.m : ℝ) ^ 2) * max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) ∧
            ENNReal.ofReal (K₁ * ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) * orbSqO L f p ≤
              ENNReal.ofReal (b ^ (Cf * (D.R.m : ℝ) ^ 2) *
                ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁) * orbSq L₁ f₁ p₁

end OneRec

end Formalism.MainNotions.S.Pv.Frames

end
end

