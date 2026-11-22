import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAvoidFormFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def AvoidFormFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (S : Set (MRingOver ℂ ι)) (G : MRingOver ℂ ι) (e : K → ℕ),
    (∀ k, 1 ≤ e k) → IsMultiHomog G e → (∀ s ∈ S, ∃ a, IsMultiHomog s a) →
    (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) → eval z G ≠ 0) →
    ∃ T : Finset ((Σ k, ι k) → ℂ), ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      (∀ s ∈ S, eval z s = 0) → ∃ t ∈ T, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * t p

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensChartSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

def BergmanDensChartSum.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L) (dV : SmoothVolume A)
    (P : ChartPartition A) (g : X → ℝ), Continuous g →
      ∫ x, g x * bergmanDens W dV x ∂dV.μ =
        (∑ j, ∫ y in (A.chart j).target,
          P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * chernTopDens W j y) / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBirationalModelExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def BirationalModelExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ),
    IsArithVar P d → ∃ (Ω : Type) (_ : Field Ω) (y : (Σ k, ι k) → Ω), mCoordIdeal y = P ∧ Birational y

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockDefectMetricChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def HSMBlockDatum.withMetric (d : HSMBlockDatum D K ι Ω) (A' : HermLine ι) (P0' : Ideal (MRing ι))
    (hdeg : A'.a = unitDeg d.k₀) (hc : IsConjInvariantH A') (hle : P0' ≤ mCoordIdeal d.y)
    (hp : IsSemipositiveRel P0' (mCoordIdeal d.y) A') : HSMBlockDatum D K ι Ω :=
  { d with A := A', P0 := P0', deg := hdeg, conjInv := hc, normalForm_baseLattice_le_dualSpan_sup_line := hle, semipos := hp }

def BlockDefectMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (I : AllFam) (d : HSMBlockDatum D K ι Ω) (A' : HermLine ι) (P0' : Ideal (MRing ι))
    (hdeg : A'.a = unitDeg d.k₀) (hc : IsConjInvariantH A') (hle : P0' ≤ mCoordIdeal d.y)
    (hp : IsSemipositiveRel P0' (mCoordIdeal d.y) A'),
    I.IsFamily →
    (fun n => hsDefect D (blockChi (d.withMetric A' P0' hdeg hc hle hp))
          (I K ι (mCoordIdeal d.y) (D + 1) fun _ => A') n -
        hsDefect D (blockChi d) (I K ι (mCoordIdeal d.y) (D + 1) fun _ => d.A) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

section Objects

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

def blockMapC {J : Type} (k₀ : K) (M : Matrix J (ι k₀) ℤ) (z : (Σ k, ι k) → ℂ) : J → ℂ :=
  fun j => ∑ i, (M j i : ℂ) * z ⟨k₀, i⟩

def IsBlockImage {Ω : Type} [Field Ω] {J : Type} [Fintype J] (y : (Σ k, ι k) → Ω) (k₀ : K)
    (M : Matrix J (ι k₀) ℤ) (N : Matrix (ι k₀) J ℤ) (x : J → Ω) : Prop :=
  (∀ j, x j = ∑ i, (M j i : Ω) * y ⟨k₀, i⟩) ∧ ∀ i, y ⟨k₀, i⟩ = ∑ j, (N i j : Ω) * x j

end Objects

def BlockImageDatum.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ (d₀ : HSMBlockDatum D K ι Ω) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι d.k₀) ℤ)
      (N : Matrix (ι d.k₀) (Ix (Fin r)) ℤ) (d' : HSMDatum D Ω (Fin r)),
      d₀.y = d.y ∧ d₀.k₀ = d.k₀ ∧ IsBlockImage d.y d.k₀ M N d'.x ∧
      (∀ z ∈ mcPts (mCoordIdeal d.y), d₀.A.h z = d'.m.ρ (blockMapC d.k₀ M z)) ∧
      ∀ n, blockChi d₀ n = resChi d' n

section Inhabitants

open ProjLine

def idBlockMat : Matrix (Ix (Fin 2)) (Fin 2) ℤ := fun j i => if j.2 = i then 1 else 0

def idBlockMat' : Matrix (Fin 2) (Ix (Fin 2)) ℤ := fun i j => if j.2 = i then 1 else 0

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMeasureChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockMeasureChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d d' : HSMBlockDatum D K ι Ω),
    d'.y = d.y → d'.k₀ = d.k₀ → d'.A = d.A →
    (fun n => blockChi d' n - blockChi d n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMetricChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (I : AllFam) (d d' : HSMBlockDatum D K ι Ω),
    I.IsFamily → d'.y = d.y → d'.k₀ = d.k₀ →
    (fun n => hsDefect D (blockChi d') (I K ι (mCoordIdeal d'.y) (D + 1) fun _ => d'.A) n -
        hsDefect D (blockChi d) (I K ι (mCoordIdeal d.y) (D + 1) fun _ => d.A) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionSup
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def blockL2NormComplex (d : HSMBlockDatum D K ι Ω) (n : ℕ) (f : MRingOver ℂ ι) : ℝ :=
  Real.sqrt (∫ x, (‖eval (blockPt d x) f‖ / d.A.h (blockPt d x) ^ n) ^ 2 ∂d.dV)

def BlockResolutionSupBound.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MRingOver ℂ ι, IsMultiHomog f (blockDeg d.k₀ n) →
      ∀ z ∈ mcPts (mCoordIdeal d.y),
        ‖eval z f‖ / d.A.h z ^ n ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockSectionsRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockSectionsRank.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ →
    ∃ C : ℝ, ∀ n : ℕ,
      |(Module.finrank ℤ (secM y (blockDeg k₀ n)) : ℝ) -
          (genDeg (mCoordIdeal y) D (unitDeg k₀) : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

section Def

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def HermLine.constShift (A : HermLine ι) (η : ℝ) : HermLine ι :=
  A.tensor (HermLine.ofWeight (fun _ => η) (fun _ _ _ => rfl))

end Def

def ConstantShift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (η : ℝ),
    IsIntersectionFamily I → IsArithVar P (D + 1) → IsSmoothHerm A →
    I P (D + 1) (fun _ => HermLine.constShift A η) =
      I P (D + 1) (fun _ => A) - ((D : ℝ) + 1) * η * geomDeg P A D

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsRegular
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

def ConstantsRegular.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (θ : 𝓞 F) (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (N : Ω) * algebraMap F Ω (θ : F) ∈ chartRingZ y c

section Inhabitants

open ProjLine

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDefectMetricChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def HSMDatum.withMetric (d : HSMDatum D Ω κ) (m : ConeMetric ℂ (Ix κ)) (P0 : Ideal (MRing (GlobalTheory κ)))
    (hs : IsSmoothMetric m) (hc : IsConjInvariant m) (hle : P0 ≤ coordIdeal ℤ d.x)
    (hp : IsSemipositiveRel P0 (coordIdeal ℤ d.x) (HermLine.ofCone m)) : HSMDatum D Ω κ :=
  { d with m := m, P0 := P0, smooth := hs, conjInv := hc, normalForm_baseLattice_le_dualSpan_sup_line := hle, semipos := hp }

def DefectMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)) (P0₁ : Ideal (MRing (GlobalTheory κ))) (hs : IsSmoothMetric m₁)
    (hc : IsConjInvariant m₁) (hle : P0₁ ≤ coordIdeal ℤ d.x)
    (hp : IsSemipositiveRel P0₁ (coordIdeal ℤ d.x) (HermLine.ofCone m₁)) (e : Fin (D + 1) → Ix κ),
    I.IsFamily → IsProjFrame d.x e →
    (fun n => hsDefect D (resChi (d.withMetric m₁ P0₁ hs hc hle hp)) (top I d.x m₁ D) n -
        hsDefect D (resChi d) (top I d.x d.m D) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

