import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigen
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.IsClosedUnitaryOfComplex

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PDifferentExtNorm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

theorem absNorm_extDifferent {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    letI : Algebra E L := ι.toAlgebra
    Ideal.absNorm (extDifferent ι) = (discr E).natAbs ^ Module.finrank E L := by
  let _ : Algebra E L := ι.toAlgebra
  have h1 : RingOfIntegers.mapRingHom ι = algebraMap (𝓞 E) (𝓞 L) := rfl
  have h3 : Module.finrank (𝓞 E) (𝓞 L) = Module.finrank E L :=
    (IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L).symm
  rw [extDifferent, h1, Ideal.absNorm_algebraMap, absNorm_differentIdeal E (𝓞 E), h3]

theorem DifferentExtNorm.full : DifferentExtNorm.Statement := by
  intro E L _ _ _ _ ι
  refine ⟨extDifferent_ne_bot ι, ?_⟩
  let _ : Algebra E L := ι.toAlgebra
  have hN := absNorm_extDifferent ι
  have hd : (discr E) ≠ 0 := discr_ne_zero E
  have hE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hdeg : Module.finrank ℚ L = Module.finrank ℚ E * Module.finrank E L :=
    (Module.finrank_mul_finrank ℚ E L).symm
  rw [hN, logRd, Nat.cast_pow, Real.log_pow, hdeg, Nat.cast_mul]
  have habs : ((discr E).natAbs : ℝ) = |(discr E : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  field_simp

end GroundTheory.Heights₂.Heights.NineStatements
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StPshLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open ReciprocityTheory.AnForm.A (IsPsh)

def PshLocal.Statement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ), IsOpen U →
    (∀ z ∈ U, ∃ W : Set (Fin D → ℂ), IsOpen W ∧ z ∈ W ∧ W ⊆ U ∧ IsPsh W φ) → IsPsh U φ

end GroundTheory.Heights₂.Heights.NineStatements
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.WeightedScaling
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField MeasureTheory GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FiniteCovolume
open scoped ENNReal Matrix

section Weighted

variable {K : Type} [Field K] [NumberField K] [IsCMField K] {N : ℕ}

def wNorm {V : HermSpace K N} (M : Majorant V) (c : InfinitePlace K → ℝ)
    (x : InfinitePlace K → Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ w, c w * (ReciprocityTheory.ChartRestriction.G.SA.hf (starRingEnd ℂ) (M.H w) (x w) (x w)).re)

def wCount {V : HermSpace K N} (M : Majorant V) (c : InfinitePlace K → ℝ) (VV : Set (Fin N → K))
    (t : ℝ) (g : RealPts V) : ℝ≥0∞ :=
  (({v | v ∈ VV ∧ wNorm M c (gAct g⁻¹ (realVec v)) < t} : Set (Fin N → K)).encard : ℝ≥0∞)

end Weighted

def WeightedScaling.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N)
    (M : Majorant V) (c : InfinitePlace E → ℝ), (∀ w, 0 < c w) →
    ∀ (L : Submodule (𝓞 E) (Fin N → E)) (VV : Set (Fin N → E)),
    IsLattice L → VV ⊆ L → (∀ v ∈ VV, v ≠ 0 ∧ V.h v v = 0) →
    (∀ g : unitaryGroup V, g ∈ stab V L → ∀ v ∈ VV,
      ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v ∈ VV) →
    ∀ μ : Measure (RealPts V), μ.IsHaarMeasure →
    ∀ s : Set (RealPts V), IsFundamentalDomain (gammaInf V L) s μ →
    ∀ t : ℝ, (∀ θ : ℝ, 0 < θ → (∫⁻ g in s, wCount M c VV (θ * t) g ∂μ) =
        ENNReal.ofReal θ ^ (2 * fDeg E * (N - 1)) * ∫⁻ g in s, wCount M c VV t g ∂μ) ∧
      ((∃ C : ℕ, ∀ v ∈ VV, lineIndex L v ≤ C) → (∫⁻ g in s, wCount M c VV t g ∂μ) < ⊤)

end GroundTheory.Heights₂.Heights.NineStatements
end
end

