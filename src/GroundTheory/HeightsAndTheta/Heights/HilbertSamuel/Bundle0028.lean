import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionSup
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def resolutionVolumeL2 (d : HSMDatum D Ω κ) (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) : ℝ :=
  Real.sqrt (∫ y, ptNorm d.m (Int.castRingHom ℂ) n f (resPt d y) ^ 2 ∂d.dV)

def resolutionVolumeL2Complex (d : HSMDatum D Ω κ) (n : ℕ) (f : MvPolynomial (Ix κ) ℂ) : ℝ :=
  Real.sqrt (∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV)

def ResolutionSupBound.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MvPolynomial (Ix κ) ℂ, f.IsHomogeneous n →
      ∀ z ∈ pts (coordIdeal ℤ d.x),
        ptNorm d.m (RingHom.id ℂ) n f z ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f

theorem ptNorm_map_intCast (m : ConeMetric ℂ (Ix κ)) (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) (z : Ix κ → ℂ) :
    ptNorm m (RingHom.id ℂ) n (map (Int.castRingHom ℂ) f) z = ptNorm m (Int.castRingHom ℂ) n f z := by
  simp [ptNorm, MvPolynomial.map_id]

theorem ResolutionSupBound.toInt (h : ResolutionSupBound.Statement) :
    ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
      ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n →
        ∀ z ∈ pts (coordIdeal ℤ d.x),
          ptNorm d.m (Int.castRingHom ℂ) n f z ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2 d n f := by
  intro D Ω _ _ κ _ d
  obtain ⟨C, hC⟩ := h D Ω κ d
  refine ⟨C, fun n hn f hf z hz => ?_⟩
  have := hC n hn (map (Int.castRingHom ℂ) f) (hf.map _) z hz
  simpa only [resolutionVolumeL2Complex, resolutionVolumeL2, ptNorm_map_intCast] using this

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsScaledFSTopPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable def scaledFSH {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  (fsH ι).tensor (constLine (-1))

def ScaledFSTopPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → 0 < II K ι P d (fun _ => scaledFSH ι)

theorem scaledFSH_a {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    (scaledFSH ι).a = fun _ => 1 := by
  funext k
  simp [scaledFSH, HermLine.tensor, fsH, HermLine.ofMetrics, constLine, HermLine.ofWeight]

theorem scaledFSH_h {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    (scaledFSH ι).h z = (∏ k, (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩)) * Real.exp 1 := by
  simp [scaledFSH, HermLine.tensor, fsH, HermLine.ofMetrics, constLine, HermLine.ofWeight]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def SecEq.Statement : Prop := KH.SecEqStatement

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecMRankBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SecMRankBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (b : K → ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ k, 1 ≤ b k) →
    (∀ m : ℕ, Module.Finite ℤ (secM y (fun k => m * b k))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤ C * ((m : ℝ) + 1) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeronese
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SecondVeronese.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D →
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (κ : Type) (_ : Fintype κ) (d : HSMDatum D Ω κ),
      (∀ n : ℕ, resChi d n = chiP D (2 * n)) ∧
      (∀ I : AllFam, I.IsFamily → top I d.x d.m D = 2 ^ (D + 1) * hhOf I D) ∧
      genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 = 2 ^ D

example : (1 : ℕ) ≤ 1 := le_rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionProduct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionProduct.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A B C : HermLine ι) (n j τ : ℕ) (s t : Ω),
    (τ : ℤ) • C.a = (n : ℤ) • A.a + (j : ℤ) • B.a →
    (∀ z ∈ mcPts (mCoordIdeal y), C.h z ^ τ = A.h z ^ n * B.h z ^ j) →
    s ∈ chartLat y A.a n → t ∈ chartLat y B.a 1 →
    s * t ^ j ∈ chartLat y C.a τ ∧
      ∀ c c' : ℝ, IsBoundedH (mCoordIdeal y) y A n c s → IsBoundedH (mCoordIdeal y) y B 1 c' t →
        IsBoundedH (mCoordIdeal y) y C τ (c * c' ^ j) (s * t ^ j)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionRingFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ (r : ℕ) (d : Fin r → ℕ) (e : Fin r → Ω), (∀ i, e i ∈ chartLat y a (d i)) ∧
      ∀ n : ℕ, chartLat y a n ≤ AddSubgroup.closure
        {s | ∃ (i : Fin r) (μ : Fin q → ℕ), d i + ∑ j, μ j = n ∧ s = e i * ∏ j, w j ^ μ j}

def SectionBounded.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (q : ℕ) (w : Fin q → Ω),
    (∀ j, w j ∈ chartLat y A.a 1) → KH.GeneratesOn y A.a w → (∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) →
    ∀ (n : ℕ) (s : Ω), s ∈ chartLat y A.a n → ∃ C : ℝ, IsBoundedH (mCoordIdeal y) y A n C s

def SectionBoundedMul.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n m : ℕ) (C C' : ℝ) (s t : Ω),
    s ∈ chartLat y A.a n → t ∈ chartLat y A.a m →
    IsBoundedH (mCoordIdeal y) y A n C s → IsBoundedH (mCoordIdeal y) y A m C' t →
    IsBoundedH (mCoordIdeal y) y A (n + m) (C * C') (s * t)

section Inhabitants

open ProjLine

theorem isBoundedH_one_of_isSmallH {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {s : Ω}
    (h : IsSmallH P y A τ s) : IsBoundedH P y A τ 1 s := by
  intro dg dh g h' z hg hh hdeg he hz
  rw [one_mul]
  exact h dg dh g h' z hg hh hdeg he hz

theorem SectionRingFinite.hyps_inhabited :
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) ∧ (∀ j : Fin 2, y ⟨(), j⟩ ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1) ∧
      KH.GeneratesOn (ι := GlobalTheory (Fin 2)) y fsLine1.a (fun j : Fin 2 => y ⟨(), j⟩) :=
  ⟨IntegralClosureFinite.hyps_inhabited.2.1, coord_mem_chartLat, generatesOn_coords⟩

theorem SectionBounded.hyps_inhabited :
    (∀ j : Fin 2, y ⟨(), j⟩ ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1) ∧
      KH.GeneratesOn (ι := GlobalTheory (Fin 2)) y fsLine1.a (fun j : Fin 2 => y ⟨(), j⟩) ∧
      ∀ j : Fin 2, IsSmallH (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) y fsLine1 1 (y ⟨(), j⟩) :=
  ⟨coord_mem_chartLat, generatesOn_coords, isSmallH_coord⟩

theorem SectionBoundedMul.hyps_inhabited :
    y ⟨(), 0⟩ ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1 ∧ y ⟨(), 1⟩ ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1 ∧
      IsBoundedH (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) y fsLine1 1 1 (y ⟨(), 0⟩) ∧
      IsBoundedH (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) y fsLine1 1 1 (y ⟨(), 1⟩) :=
  ⟨coord_mem_chartLat 0, coord_mem_chartLat 1, isBoundedH_one_of_isSmallH (isSmallH_coord 0),
    isBoundedH_one_of_isSmallH (isSmallH_coord 1)⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSupBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionSupBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (e : Ω),
    ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} → e ∈ chartLat y A.a τ →
    ∃ C : ℝ, 0 ≤ C ∧ IsBoundedH (mCoordIdeal y) y A τ (Real.exp C) e

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionsRank.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (n : ℕ),
    GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
        ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) =
      (Module.finrank ℤ (sec ℤ x n) : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreArith
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def segreCoords {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [CommRing Ω] (y : (Σ k, ι k) → Ω) :
    Ix ((k : K) → ι k) → Ω :=
  fun p => ∏ k, y ⟨k, p.2 k⟩

def SegreArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) →
    IsArithVar (ι := GlobalTheory ((k : K) → ι k)) (coordIdeal ℤ (segreCoords y)) (D + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSeparatedSmallCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SeparatedSmallCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (τ : ℕ) (b : ℝ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → 0 ≤ b →
    (∀ s : Ω, s ∈ chartLat y A.a τ → s ≠ 0 → ∀ c : ℝ, c < Real.exp (-b) →
      ¬ IsBoundedH (mCoordIdeal y) y A τ c s) →
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ ≤
      (Module.finrank ℤ (chartLat y A.a τ) : ℝ) * (b + Real.log 3)

section Inhabitant

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end Inhabitant

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftDegreePolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftDegreePolynomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (a b : K → ℤ),
    IsArithVar P (D + 1) →
    ∃ r : Polynomial ℝ, r.natDegree ≤ D ∧ r.coeff D = (genDeg P D a : ℝ) ∧
      ∀ q : ℕ, (genDeg P D ((q : ℤ) • a + b) : ℝ) = r.eval (q : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

