import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StDivisorNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def DivisorNull.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (R : RegChartData A),
    A.IsAnalyticSubset R.Yoᶜ ∧ interior R.Yoᶜ = ∅

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailLog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection logNormSec)

noncomputable section

variable {D : ℕ} {X : Type*} [TopologicalSpace X]

def secOpen (s : X → X → ℂ) : Set X := {y | s y y ≠ 0}

def rSec (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ := Real.exp 1 - 2 * logNormSec L s y

structure IsLemmaEPot (A : FinHolAtlas D X) (Om : KaehlerForm A) (L : LocPot X)
    (s : X → X → ℂ) (C₁ : ℝ) (u : X → ℝ) : Prop where
  smooth : A.SmoothOn (secOpen s) u
  nonneg : FormNonneg A (secOpen s) (potForm Om.pot u)
  nonpos : ∀ x ∈ secOpen s, u x ≤ 0
  le_u : ∀ x ∈ secOpen s, -(C₁ * Real.log (rSec L s x)) ≤ u x
  smooth_or_pole : A.Smooth u ∨ ∀ y, y ∉ secOpen s → Tendsto u (𝓝[secOpen s] y) atBot

def LemmaETailLog.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    Dense (secOpen s) → (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    ∃ CE : ℝ, ∀ u : Fin D → X → ℝ, (∀ i, IsLemmaEPot A Om L s C₁ (u i)) →
      TailLogBound A (secOpen s) (rSec L s) (fun i => potForm Om.pot (u i)) CE

section Inhabitants

open OnePoint
open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isPlurisubharmonic projLine_isHolomorphicSection crd0 crd1 fsPot_φ_coe
  projLineSection_infty projLineSection_coe)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMonoDens
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

def ListMonoDens.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th : Fin D → LocPot X)
    (Om : LocPot X) (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsPotential A (th i)) →
    IsPotential A Om → (∀ i, A.SmoothOn Yo (u i)) → (∀ i, LeviLe A Set.univ 1 (th i) 1 Om) →
    (∀ i, FormNonneg A Yo (potForm (th i) (u i))) →
    ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo →
      0 ≤ locDens A (fun i => potForm (th i) (u i)) j y ∧
        locDens A (fun i => potForm (th i) (u i)) j y ≤ locDens A (fun i => potForm Om (u i)) j y

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMonoRaise
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)

def ListMonoRaise.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th Om : LocPot X)
    (u : X → ℝ), IsOpen Yo → IsPotential A th → IsPotential A Om → A.SmoothOn Yo u →
    LeviLe A Set.univ 1 th 1 Om → FormNonneg A Yo (potForm th u) → FormNonneg A Yo (potForm Om u)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListProductMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def ListProductMass.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (R : RegChartData A) (Om : KaehlerForm A) (C₁ : ℝ) (th : Fin D → LocPot X)
    (u : Fin D → X → ℝ), (∀ i, IsSmoothPotForm A R.Yo R.r Om C₁ (th i) (u i)) →
      mInt A (fun i => potForm (th i) (u i)) (fun _ => 1) ≤ Om.vol

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLogSmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def ListTailLogSmooth.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (R : RegChartData A) (Om : KaehlerForm A) (C₁ : ℝ), ∃ CE : ℝ,
    ∀ (th : Fin D → LocPot X) (u : Fin D → X → ℝ),
      (∀ i, IsSmoothPotForm A R.Yo R.r Om C₁ (th i) (u i)) →
        TailLogBound A R.Yo R.r (fun i => potForm (th i) (u i)) CE

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLocDensContOnOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

def LocDensContOnOpen.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th : Fin D → LocPot X)
    (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsPotential A (th i)) → (∀ i, A.SmoothOn Yo (u i)) →
    ∀ j, ContinuousOn (locDens A (fun i => potForm (th i) (u i)) j)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StMIntMonoOfDensLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens mInt MIntegrable)

def MIntMonoOfDensLe.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] (A : FinHolAtlas D X) (V : Set X)
    (Φ Ψ : Fin D → LocPot X),
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ V →
      0 ≤ locDens A Φ j y ∧ locDens A Φ j y ≤ locDens A Ψ j y) →
    ∀ g : X → ℝ, (∀ x, 0 ≤ g x) → (∀ x, x ∉ V → g x = 0) → MIntegrable A Ψ g →
      mInt A Φ g ≤ mInt A Ψ g

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic locDensCont locDens_nonneg_of_psh)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StMIntegrableOfDensLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens MIntegrable)

def MIntegrableOfDensLe.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (V : Set X) (Φ Ψ : Fin D → LocPot X),
    IsOpen V → (∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V)) →
    (∀ j, ContinuousOn (locDens A Ψ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V)) →
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ V →
      0 ≤ locDens A Φ j y ∧ locDens A Φ j y ≤ locDens A Ψ j y) →
    ∀ g : X → ℝ, (∀ x, x ∉ V → g x = 0) → MIntegrable A Ψ g → MIntegrable A Φ g

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic locDensCont locDens_nonneg_of_psh)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StProductBounds
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def ProductBounds.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (R : RegChartData A) (Om : KaehlerForm A) (C₁ : ℝ), ∃ V CE : ℝ,
    ∀ (th : Fin D → LocPot X) (u : Fin D → X → ℝ),
      (∀ i, IsSmoothPotForm A R.Yo R.r Om C₁ (th i) (u i)) →
        MassBound A R.Yo (fun i => potForm (th i) (u i)) th V ∧
          TailLogBound A R.Yo R.r (fun i => potForm (th i) (u i)) CE

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TailDimZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot ChartPartition mInt integralWith locDens)

theorem tailLogBound_dim_zero {X : Type} [TopologicalSpace X] (A : FinHolAtlas 0 X) (Yo : Set X)
    (r : X → ℝ) (T : Fin 0 → LocPot X) : ∃ CE : ℝ, TailLogBound A Yo r T CE := by
  classical
  have hv : (volume : Measure (Fin 0 → ℂ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  have : IsFiniteMeasure (volume : Measure (Fin 0 → ℂ)) := ⟨by rw [hv]; exact ENNReal.one_lt_top⟩
  have hd : ∀ j y, locDens A T j y = 1 := fun j y => by
    simp [locDens, ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]
  have hint : ∀ (f : (Fin 0 → ℂ) → ℝ) (K : Set (Fin 0 → ℂ)),
      ∫ y in K, f y = (volume K).toReal * f default := by
    intro f K
    have : f = fun _ => f default := funext fun y => congrArg f (Subsingleton.elim y default)
    rw [this, integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  have hvol : ∀ K : Set (Fin 0 → ℂ), 0 ≤ (volume K).toReal ∧ (volume K).toReal ≤ 1 := fun K =>
    ⟨ENNReal.toReal_nonneg, by
      have := ENNReal.toReal_mono (by rw [hv]; exact ENNReal.one_ne_top)
        (measure_mono (μ := volume) (Set.subset_univ K))
      rwa [hv, ENNReal.toReal_one] at this⟩
  set p : Fin A.n → X := fun j => (A.chart j).symm default
  set B := ∑ j, |Real.log (r (p j))|
  set M := ∑ j, |r (p j)| + Real.exp 1
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM : 0 < M := by positivity
  refine ⟨B * M, fun R₀ hR₀ => ⟨fun j K _ _ => Integrable.of_finite.integrableOn, ?_⟩⟩
  set g := (tail Yo r R₀).indicator fun x => Real.log (r x)
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le (Real.exp_pos 1) hR₀
  have hlog : 1 ≤ Real.log R₀ := by
    have := Real.log_le_log (Real.exp_pos 1) hR₀
    rwa [Real.log_exp] at this
  have hg : ∀ x, |g x| ≤ |Real.log (r x)| := fun x => by
    simp only [g, Set.indicator]
    split_ifs <;> simp
  have hterm : ∀ (P : ChartPartition A) j,
      |∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
          locDens A T j y| ≤ |Real.log (r (p j))| ∧
        (M < R₀ → ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) *
          g ((A.chart j).symm y) * locDens A T j y = 0) := by
    intro P j
    rw [hint, hd, mul_one]
    have hχ0 := P.nonneg j (p j)
    have hχ1 : P.χ j (p j) ≤ 1 := P.sum_eq_one (p j) ▸
      Finset.single_le_sum (fun i _ => P.nonneg i (p j)) (Finset.mem_univ j)
    obtain ⟨hv0, hv1⟩ := hvol (A.chart j).target
    refine ⟨?_, fun hMR => ?_⟩
    · rw [abs_mul, abs_mul, abs_of_nonneg hv0, abs_of_nonneg hχ0]
      have := hg (p j)
      have h2 : P.χ j (p j) * |g (p j)| ≤ |Real.log (r (p j))| := by nlinarith [abs_nonneg (g (p j))]
      nlinarith [abs_nonneg (g (p j))]
    · have hr : |r (p j)| ≤ ∑ i, |r (p i)| :=
        Finset.single_le_sum (f := fun i => |r (p i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      have hn : p j ∉ tail Yo r R₀ := fun h => by
        have := h.2
        have := le_abs_self (r (p j))
        have := Real.exp_pos 1
        linarith
      show (volume (A.chart j).target).toReal * (P.χ j (p j) * g (p j)) = 0
      rw [show g (p j) = 0 from Set.indicator_of_notMem hn _]
      simp
  have hRHS : 0 ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀ := by
    have : 0 ≤ Real.log R₀ := by linarith
    positivity
  show mInt A T g ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀
  unfold mInt
  split_ifs with h
  · unfold integralWith
    by_cases hMR : M < R₀
    · rw [Finset.sum_eq_zero fun j _ => (hterm h.some j).2 hMR]
      exact hRHS
    · replace hMR := not_lt.mp hMR
      calc _ ≤ ∑ j, |Real.log (r (p j))| :=
            Finset.sum_le_sum fun j _ => (le_abs_self _).trans (hterm h.some j).1
        _ ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀ := by
          rw [le_div_iff₀ hR₀pos, pow_one]
          have h1 : B * R₀ ≤ B * M := mul_le_mul_of_nonneg_left hMR hB
          have h2 : B * M ≤ B * M * Real.log R₀ := by
            have := mul_nonneg hB hM.le
            nlinarith
          linarith
  · exact hRHS

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

