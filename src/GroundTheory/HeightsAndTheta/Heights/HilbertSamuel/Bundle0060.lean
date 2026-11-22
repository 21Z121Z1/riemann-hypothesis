import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsBoundedAtOfIsBoundedH
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGraphDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameGraphDeg.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∃ (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))))
      (J : IFamily G.Φ (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) (Sum.inr : Unit → Unit ⊕ Unit))),
      IsFieldIntersection J ∧ J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = (projDeg x e : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameImage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameImage.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsProjFrame x e →
    imageZ (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
      (graphIdeal (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))) = ⊥

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsQuotPartGraded
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def QuotPartGraded.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (V : Ideal (MRingOver S ι)), IsMultiHomogIdeal V → KH.IsMGraded S ι (KH.quotPart S V)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealFormsOnPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RealFormsOnPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (d : ℕ) (e : K → ℕ) (r : ℕ) (g : Fin r → MRing ι),
    IsArithVar (mCoordIdeal y) d → (∀ i, IsMultiHomog (g i) e) →
    LinearIndependent ℤ (fun i => aeval y (g i)) →
    ∀ c : Fin r → ℝ,
      (∀ z ∈ mcPts (mCoordIdeal y), ∑ i, (c i : ℂ) * eval z (map (Int.castRingHom ℂ) (g i)) = 0) →
      c = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealGramComparison
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def RealGramComparison.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ), IsProjFrame d.x e →
    (fun n => resChi d n - resCChi d n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSecM
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) : Submodule R Ω :=
  Submodule.span R ((fun μ : (Σ k, ι k) → ℕ => ∏ p, y p ^ μ p) '' {μ | ∀ k, ∑ i, μ ⟨k, i⟩ = b k})

theorem monomial_mem_relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {b : K → ℕ} (μ : (Σ k, ι k) → ℕ)
    (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = b k) : ∏ p, y p ^ μ p ∈ relSecM R y b :=
  Submodule.subset_span ⟨μ, hμ, rfl⟩

theorem relSecM_fg (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) : (relSecM R y b).FG := by
  have hfin : {μ : (Σ k, ι k) → ℕ | ∀ k, ∑ i, μ ⟨k, i⟩ = b k}.Finite := by
    refine (Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Iic (b p.1)) fun p => Set.finite_Iic _).subset ?_
    intro μ hμ p _
    simp only [Set.mem_Iic]
    rw [← hμ p.1]
    exact Finset.single_le_sum (f := fun i => μ ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
  exact Submodule.fg_span (hfin.image _)

theorem mul_mem_relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {b b' : K → ℕ} {x x' : Ω}
    (hx : x ∈ relSecM R y b) (hx' : x' ∈ relSecM R y b') : x * x' ∈ relSecM R y (b + b') := by
  have hle : relSecM R y b * relSecM R y b' ≤ relSecM R y (b + b') := by
    rw [relSecM, relSecM, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨μ, hμ, rfl⟩, _, ⟨ν, hν, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨μ + ν, fun k => ?_, ?_⟩
    · simp [Finset.sum_add_distrib, hμ k, hν k]
    · simp [pow_add, Finset.prod_mul_distrib]
  exact hle (Submodule.mul_mem_mul hx hx')

theorem adjoin_isNoetherianRing {m : ℕ} (g : Fin m → Ω) : IsNoetherianRing (Algebra.adjoin ℤ (Set.range g)) := by
  have : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range g)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range g)
  exact Algebra.FiniteType.isNoetherianRing ℤ _

omit [∀ k, Fintype (ι k)] in

theorem mul_prod_mem_relChartLat (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {a a' : K → ℤ} {n : ℕ} (e : K → ℕ)
    (c0 : ∀ k, ι k) (h : ∀ k, a' k = n * a k + e k) {s : Ω} (hs : s ∈ relChartLat R y a n) :
    s * ∏ k, y ⟨k, c0 k⟩ ^ e k ∈ relChartLat R y a' 1 := by
  intro c hc
  have key : ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a' k)) =
      y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) * (y ⟨k, c k⟩ ^ e k)⁻¹ := by
    intro k
    rw [h k, show -(((1 : ℕ) : ℤ) * ((n : ℤ) * a k + (e k : ℤ))) = -((n : ℤ) * a k) + -((e k : ℕ) : ℤ) by push_cast; ring,
      zpow_add₀ (hc k), zpow_neg (y ⟨k, c k⟩) ((e k : ℕ) : ℤ), zpow_natCast]
  rw [Finset.prod_congr rfl fun k _ => key k, Finset.prod_mul_distrib]
  have hmem : (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, (y ⟨k, c0 k⟩ / y ⟨k, c k⟩) ^ e k ∈
      Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) :=
    mul_mem (hs c hc) (prod_mem fun k _ => pow_mem (Algebra.subset_adjoin
      (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ⟨k, c0 k⟩)) _)
  convert hmem using 1
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_inv_distrib]
  ring

end Objects

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionDegree.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (m : ConeMetric ℂ (Ix κ)), IsProjFrame d.x e → IsSmoothMetric m →
    mInt d.R.A (fun _ => resPot d m) (fun _ => 1) = (projDeg d.x e : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionInterpIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionInterpIntegral.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)), IsSmoothMetric m₁ →
    ((D : ℝ) + 1) * resMetricInt d m₁ =
      ∑ i ∈ Finset.range (D + 1),
        mInt d.R.A (fun j : Fin D => if j.val < i then resPot d m₁ else resPot d d.m)
          (fun y => logRatio d.m m₁ (resPt d y))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMetricPair
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def ResolutionMetricPair.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)) (P0₁ : Ideal (MRing (GlobalTheory κ))), IsSmoothMetric m₁ →
    P0₁ ≤ coordIdeal ℤ d.x → IsSemipositiveRel P0₁ (coordIdeal ℤ d.x) (HermLine.ofCone m₁) →
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W₀ W₁ : Weight L) (dV : SmoothVolume A)
      (σ : ℕ → MvPolynomial (Ix κ) ℚ → Fin A.n → d.R.X → ℂ),
      A.Compatible d.R.A ∧ W₀.IsSemipositive ∧ W₁.IsSemipositive ∧ dV.μ = d.dV ∧
      (∀ (n : ℕ) (b : MvPolynomial (Ix κ) ℚ), b.IsHomogeneous n → σ n b ∈ L.sections n) ∧
      (∀ y : d.R.X, ∃ c : ℂ, c ≠ 0 ∧
        (∀ (n : ℕ) (b : MvPolynomial (Ix κ) ℚ), b.IsHomogeneous n →
          σ n b (chartIdx A y) y = eval (c • resPt d y) (map (algebraMap ℚ ℂ) b)) ∧
        W₀.φ (chartIdx A y) y = 2 * Real.log (d.m.ρ (c • resPt d y)) ∧
        W₁.φ (chartIdx A y) y = 2 * Real.log (m₁.ρ (c • resPt d y))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ g : d.R.X → ℝ, Continuous g →
        ∫ y, g y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
          mInt d.R.A (fun _ => resPot d (interp d.m m₁ t)) g / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedBridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionMixedBridge.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (M : Fin D → ConeMetric ℂ (Ix κ)) (m₁ : ConeMetric ℂ (Ix κ)),
    (∀ j, IsSmoothMetric (M j)) → IsSmoothMetric m₁ →
    ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ d.x) (fun j z => Real.log ((M j).ρ z)) (logRatio d.m m₁) =
      mInt d.R.A (fun j => resPot d (M j)) (fun y => logRatio d.m m₁ (resPt d y))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResolutionMixedIntegral.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)), IsSmoothMetric m₁ →
    ∑ i ∈ Finset.range (D + 1),
        ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ d.x) (mixPot d.m m₁ D i) (logRatio d.m m₁) =
      ((D : ℝ) + 1) * resMetricInt d m₁

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionPullback
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionPullback.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W : Weight L) (dV : SmoothVolume A),
      A.Compatible d.R.A ∧ W.IsSemipositive ∧ dV.μ = d.dV ∧
      ∀ (n : ℕ) (f : MRing ι), IsMultiHomog f (blockDeg d.k₀ n) →
        ∃ s ∈ L.sections n, ∀ x : d.R.X,
          ptNormSq W n s x =
            (‖eval (blockPt d x) (map (Int.castRingHom ℂ) f)‖ / d.A.h (blockPt d x) ^ n) ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

