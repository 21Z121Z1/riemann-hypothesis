import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Telescoping
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.C2ConvergenceHypothesesNonempty
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax Mollifier molli)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts errE errorWithLinear ell)

noncomputable section

def ChartsCompareAt {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
    (R : RegChartData A) (ρ : Mollifier D) (C t : ℝ) : Prop :=
  ∀ j k (x : X), x ∈ R.V' j → x ∈ R.V' k →
    |R.phChart R.φ ρ t j x - R.phChart R.φ ρ t k x| ≤ errorWithLinear C t

def GluedLocal.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D) (Cη : ℝ) (η : Fin R.n → X → ℝ),
    R.IsCutoffFamily Cη η → ∀ x₀ : X, ∃ (N : Set X) (J : Finset (Fin R.n)) (c : Fin R.n),
      IsOpen N ∧ x₀ ∈ N ∧ c ∈ J ∧ (∀ j ∈ J, N ⊆ R.V' j) ∧ N ⊆ R.V'' c ∧
      ∀ C t : ℝ, 0 < errorWithLinear C t → ChartsCompareAt R ρ C t → ∀ x ∈ N,
        R.glued R.φ ρ η C t x =
          @regMax (Fin R.n) _ ⟨c⟩ (errorWithLinear C t) (fun j => if j ∈ J then R.regArg R.φ ρ η C t j x
            else R.regArg R.φ ρ η C t c x - errorWithLinear C t) + errorWithLinear C t / 2

def ArgumentConvergenceC2.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D) (Cη : ℝ) (η : Fin R.n → X → ℝ),
    R.IsCutoffFamily Cη η → ∀ C : ℝ, 0 < C → ∀ (j : Fin R.n) (k : Fin A.n) (L : Set (Fin D → ℂ)),
      IsCompact L → L ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.Yo ∩ R.V' j) →
      ∃ U : Set (Fin D → ℂ), IsOpen U ∧ L ⊆ U ∧
        ContDiffOn ℝ 2 (fun y => R.φ ((A.chart k).symm y)) U ∧
        (∀ᶠ t in 𝓝[>] 0, ContDiffOn ℝ 2 (fun y => R.regArg R.φ ρ η C t j ((A.chart k).symm y)) U) ∧
        TendstoC2On (fun t y => R.regArg R.φ ρ η C t j ((A.chart k).symm y))
          (fun y => R.φ ((A.chart k).symm y)) L ∧
        ∃ M : ℝ, ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ L,
          ‖fderiv ℝ (fun y' => R.regArg R.φ ρ η C t j ((A.chart k).symm y')) y -
              fderiv ℝ (fun y' => R.φ ((A.chart k).symm y')) y‖ ≤ M * (t + errorWithLinear C t)

def PropertyF.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D) (Cη : ℝ) (η : Fin R.n → X → ℝ),
    R.IsCutoffFamily Cη η → ∀ C : ℝ, 0 < C →
    (∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ → ChartsCompareAt R ρ C t) →
    ∀ (k : Fin A.n) (K : Set (Fin D → ℂ)), IsCompact K →
      K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' R.Yo →
      TendstoC2On (fun t y => R.glued R.φ ρ η C t ((A.chart k).symm y))
        (fun y => R.φ ((A.chart k).symm y)) K

section Inhabitant

open ReciprocityTheory.AnForm.M (p1 projectiveLineChartAtZero projLineChart0_target projLineAtlas_chart0)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData projLineCutoff projLine_cutoffFamily mollifier_bounded_inhabited)

def p1j0 : Fin projLineChartData.n := ⟨0, by show 0 < 2; norm_num⟩

end Inhabitant

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceStatements
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens chartPartMeasure
  existsPartition)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

section Objects

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

def Family.coefWeight (F : Family A) (x : Option (Fin F.m) → ℝ) (t : ℝ) : X → ℝ :=
  fun p => ∑ i, x (some i) * (F.sys i).ph t p

def Family.coefForm (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) (t : ℝ) : LocPot X :=
  F.chernForm (fun i => x (some i)) t + LocPot.rsmul (x none) a

def Family.coefRefForm (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) : LocPot X :=
  lincomb F.m (fun i => x (some i)) (fun i => (F.R i).θ) + LocPot.rsmul (x none) a

def Family.weightEnergy (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (D + 1), mInt A
    (fun i : Fin D => if (i : ℕ) < k then F.coefForm a x t else F.coefRefForm a x) (F.coefWeight x t)

def Family.arithSelfInt (F : Family A) (a : LocPot X) (a₀ : MvPolynomial (Option (Fin F.m)) ℝ)
    (δ : ℝ) (x : Option (Fin F.m) → ℝ) (t : ℝ) : ℝ :=
  (MvPolynomial.eval x a₀ + F.weightEnergy a x t) / δ

def Family.mixedProduct (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) (t t' : ℝ)
    (k : ℕ) : Fin D → LocPot X :=
  fun i => if (i : ℕ) < k then F.coefForm a x t else F.coefForm a x t'

def Family.Admissible (F : Family A) (t : ℝ) : Prop :=
  0 < t ∧ ∀ i, (F.sys i).ell₀ ≤ ell t

end Objects

section Potentials

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem isPotential_lincomb : ∀ (m : ℕ) (c : Fin m → ℝ) (P : Fin m → LocPot X),
    (∀ i, IsPotential A (P i)) → IsPotential A (lincomb m c P)
  | 0, _, _, _ => ReciprocityTheory.AnForm.M.isPotential_ofFun A _ fun _ => contDiffOn_const
  | m + 1, c, P, hP => ReciprocityTheory.AnForm.M.isPotentialAdd A _ _
      (ReciprocityTheory.AnForm.M.isPotentialRsmul A (c 0) (P 0) (hP 0))
      (isPotential_lincomb m _ _ fun i => hP i.succ)

theorem Family.coefForm_isPotential (F : Family A) {a : LocPot X} (ha : IsPotential A a)
    (x : Option (Fin F.m) → ℝ) {t : ℝ} (ht : F.Admissible t) : IsPotential A (F.coefForm a x t) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd A _ _
    (isPotential_lincomb _ _ _ fun i => ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (F.R i).θ_pot
      (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ ((F.sys i).smooth t ht.1 (ht.2 i))))
    (ReciprocityTheory.AnForm.M.isPotentialRsmul A _ a ha)

theorem Family.mixedProduct_isPotential (F : Family A) {a : LocPot X} (ha : IsPotential A a)
    (x : Option (Fin F.m) → ℝ) {t t' : ℝ} (ht : F.Admissible t) (ht' : F.Admissible t') (k : ℕ)
    (i : Fin D) : IsPotential A (F.mixedProduct a x t t' k i) := by
  unfold Family.mixedProduct
  split_ifs
  · exact F.coefForm_isPotential ha x ht
  · exact F.coefForm_isPotential ha x ht'

end Potentials

def Convergence.TVHyp {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {A : FinHolAtlas D X} (F : Family A) (a : LocPot X)
    (Λ M CE L₀ : ℝ) : Prop :=
  ∀ x : Option (Fin F.m) → ℝ, ∑ o, |x o| ≤ Λ → ∀ t t' : ℝ, 0 < t' → t' ≤ t → L₀ ≤ ell t →
    ∀ k ≤ D, TVBounds A (F.mixedProduct a x t t' k) F.Yo F.r M CE

def WeightCocycle.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (F : Family A) (a : LocPot X), IsPotential A a → ∀ (x : Option (Fin F.m) → ℝ) (t t' : ℝ),
    F.Admissible t → F.Admissible t' →
      F.weightEnergy a x t - F.weightEnergy a x t' =
        ∑ k ∈ Finset.range (D + 1),
          mInt A (F.mixedProduct a x t t' k) fun p => F.coefWeight x t p - F.coefWeight x t' p

def PolynomialInWeights.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (F : Family A) (a : LocPot X), IsPotential A a → ∀ t : ℝ, F.Admissible t →
      ∃ p : MvPolynomial (Option (Fin F.m)) ℝ, p.totalDegree ≤ D + 1 ∧
        ∀ x, MvPolynomial.eval x p = F.weightEnergy a x t

def Convergence.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (D : ℕ) (A : FinHolAtlas D X) (F : Family A) (a : LocPot X)
    (a₀ : MvPolynomial (Option (Fin F.m)) ℝ) (δ Λ M CE L₀ : ℝ),
    IsPotential A a → 0 < δ → (∀ i, (F.sys i).ell₀ ≤ L₀) → 0 ≤ M → 0 ≤ CE →
    Convergence.TVHyp F a Λ M CE L₀ →
    ∃ C L₁ : ℝ, ∀ x : Option (Fin F.m) → ℝ, ∑ o, |x o| ≤ Λ → ∀ t t' : ℝ, 0 < t' → t' ≤ t →
      L₁ ≤ ell t → |F.arithSelfInt a a₀ δ x t - F.arithSelfInt a a₀ δ x t'| ≤ convRate D C t

def CoefficientLimit.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (D : ℕ) (A : FinHolAtlas D X) (F : Family A) (a : LocPot X)
    (a₀ : MvPolynomial (Option (Fin F.m)) ℝ) (δ L₀ : ℝ),
    IsPotential A a → a₀.totalDegree ≤ D + 1 → 0 < δ → (∀ i, (F.sys i).ell₀ ≤ L₀) →
    (∀ Λ : ℝ, ∃ M CE : ℝ, 0 ≤ M ∧ 0 ≤ CE ∧ Convergence.TVHyp F a Λ M CE L₀) →
    ∃ P : MvPolynomial (Option (Fin F.m)) ℝ, P.totalDegree ≤ D + 1 ∧
      (∀ x, Tendsto (fun t => F.arithSelfInt a a₀ δ x t) (𝓝[>] 0) (𝓝 (MvPolynomial.eval x P))) ∧
      ∀ p : ℝ → MvPolynomial (Option (Fin F.m)) ℝ,
        (∀ᶠ t in 𝓝[>] 0, (p t).totalDegree ≤ D + 1 ∧
          ∀ x, MvPolynomial.eval x (p t) = F.arithSelfInt a a₀ δ x t) →
        ∀ α, Tendsto (fun t => (p t).coeff α) (𝓝[>] 0) (𝓝 (P.coeff α))

section Inhabitants

open ReciprocityTheory.AnForm (fsDens levi maDens_one fsDens_pos)
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineCharts projLineCharts_potential_zero isPsh_const)

attribute [local instance] projectiveLineBorel projectiveLine_borelSpace

def projectiveLineDataEmptyDivisor : RegChartData p1 where
  toRegCharts := projLineCharts
  Yo := Set.univ
  isOpen_Yo := isOpen_univ
  S _ := ∅
  mem_Yo_iff _ z _ := by simp [ReciprocityTheory.AnForm.A.coordDiv]
  r _ := Real.exp 1
  f _ _ := 0
  f_cont _ := continuousOn_const
  f_bdd _ := ⟨0, fun _ _ => by simp⟩
  r_chart _ _ _ := by simp
  one_le_r _ _ := Real.one_le_exp zero_le_one
  φ _ := 0
  φ_smooth _ := contDiffOn_const
  psh j := by
    show ReciprocityTheory.AnForm.A.IsPsh _ (projLineCharts.u (fun _ => 0) j)
    rw [projLineCharts_potential_zero]
    exact isPsh_const _ 0
  C := 0
  φ_le _ _ := le_rfl
  le_φ _ _ := by simp
  grad j z _ := by
    show ‖fderiv ℝ (projLineCharts.u (fun _ => 0) j) z‖ ≤ _
    rw [projLineCharts_potential_zero]
    simp

def projectiveLineSystemEmptyDivisor : System projectiveLineDataEmptyDivisor where
  ph _ _ := 0
  C := 0
  ell₀ := 1
  smooth _ _ _ _ := contDiffOn_const
  le_ph _ _ _ _ _ := le_rfl
  ph_le _ _ _ _ := le_rfl
  le_log _ _ _ _ := by simp
  thGe t _ _ := by
    intro x k y _ w
    have h : ((fun z => projectiveLineDataEmptyDivisor.θ.φ x z + (fun _ : OnePoint ℂ => (0 : ℝ)) z) ∘ (p1.chart k).symm) =
        fun _ => (0 : ℝ) := by
      funext z
      show (0 : ℝ) + 0 = 0
      simp
    rw [h, levi_const, errE_zero]
    simp
  near t ht _ _ _ _ := by
    show (0 : ℝ) ≤ 0 + t ^ (1 / 3 : ℝ) + errE 0 t
    rw [errE_zero]
    have := Real.rpow_nonneg ht.le (1 / 3 : ℝ)
    linarith
  far t ht _ _ _ := by
    show (0 : ℝ) ≤ 0 + t ^ (1 / 3 : ℝ) + errE 0 t * _
    rw [errE_zero]
    have := Real.rpow_nonneg ht.le (1 / 3 : ℝ)
    linarith
  mono _ _ _ _ _ _ := by simp
  c2 _ _ _ _ := ⟨tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _,
    tendstoUniformlyOn_self _ _ _⟩

def projectiveLineFamilyEmptyDivisor : Family p1 where
  m := 1
  R _ := projectiveLineDataEmptyDivisor
  sys _ := projectiveLineSystemEmptyDivisor
  Yo := Set.univ
  r _ := Real.exp 1
  om := fsPot
  Yo_eq _ := rfl
  r_eq _ _ _ := rfl
  om_eq _ := rfl

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassError
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassError.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W)
    (a : ℕ) (ha : a < D + 1), ∀ δ, 0 < δ → ∃ τ, 0 < τ ∧ ∀ t₀ t, 0 < t → t ≤ t₀ → t₀ ≤ τ →
      S.ell₀ ≤ ell t₀ → S.errW a ha t₀ t ≤ δ ∧ S.errDiv a ha t₀ t ≤ δ

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassReplace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassReplace.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∃ Cκ, 0 ≤ Cκ ∧ ∀ (a : ℕ) (ha : a < D + 1) (t₀ : ℝ), 0 < t₀ → S.ell₀ ≤ ell t₀ →
      ∃ K, 0 ≤ K ∧ ∀ ε t, 0 < ε → ε ≤ 1 → 0 < t → t ≤ t₀ →
        S.plTerm a ha ε t ≤ K * S.J a ε t + Cκ * S.errW a ha t₀ t + 2 * S.errDiv a ha t₀ t

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassStep.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W)
    (a : ℕ) (ha : a < D + 1) (ε t : ℝ), 0 < ε → 0 < t → S.ell₀ ≤ ell t →
      S.J (a + 1) ε t ≤ S.J a ε t + S.plTerm a ha ε t

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassZero.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ t, S.J 0 ε t ≤ η

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.LinearWeights
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

section Linear

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

def Family.weight (F : Family A) {Λ : Type*} [AddCommGroup Λ] [Module ℝ Λ]
    (φ₀ φc : Λ →ₗ[ℝ] (X → ℝ)) (c : Λ →ₗ[ℝ] (Fin F.m → ℝ)) (t : ℝ) (lam : Λ) : X → ℝ :=
  fun x => φ₀ lam x + ∑ i, c lam i * (F.sys i).ph t x + φc lam x

theorem Family.weight_isLinearMap (F : Family A) {Λ : Type*} [AddCommGroup Λ] [Module ℝ Λ]
    (φ₀ φc : Λ →ₗ[ℝ] (X → ℝ)) (c : Λ →ₗ[ℝ] (Fin F.m → ℝ)) (t : ℝ) :
    IsLinearMap ℝ (F.weight φ₀ φc c t) where
  map_add a b := by
    funext x
    simp only [Family.weight, map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul s a := by
    funext x
    simp only [Family.weight, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    ring

theorem Family.chernForm_isLinearMap (F : Family A) {Λ : Type*} [AddCommGroup Λ] [Module ℝ Λ]
    (c : Λ →ₗ[ℝ] (Fin F.m → ℝ)) (t : ℝ) (x y : X) :
    IsLinearMap ℝ fun lam => (F.chernForm (c lam) t).φ x y := by
  have h : ∀ lam, (F.chernForm (c lam) t).φ x y =
      ∑ i, c lam i * ((F.R i).θ + LocPot.ofFun ((F.sys i).ph t)).φ x y :=
    fun lam => lincomb_φ _ _ _ _ _
  constructor
  · intro a b
    rw [h (a + b), h a, h b, map_add, ← Finset.sum_add_distrib]
    simp only [Pi.add_apply, add_mul]
  · intro s a
    rw [h (s • a), h a, map_smul, smul_eq_mul, Finset.mul_sum]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

end Linear

section Currents

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem levi_add_const' {ι : Type*} [Fintype ι] (f : (ι → ℂ) → ℝ) (c : ℝ) (z w : ι → ℂ) :
    levi (fun y => f y + c) z w = levi f z w := by
  have : fderiv ℝ (fun y => f y + c) = fderiv ℝ f := funext fun _ => fderiv_add_const c
  simp only [levi, this]

theorem System.curr_isSmoothPotForm {A : FinHolAtlas D X} {R : RegChartData A} (S : System R)
    (hr : ∀ x ∈ R.Yo, Real.exp 1 ≤ R.r x) (Om : KaehlerForm A)
    (h1 : LeviLe A Set.univ 1 (thetaOmega R) 1 Om.pot)
    (h2 : LeviLe A Set.univ (-1) Om.pot 1 (thetaOmega R)) (t : ℝ) (ht : 0 < t)
    (hl : S.ell₀ ≤ ell t) (he : errE S.C t ≤ 1) :
    IsSmoothPotForm A R.Yo R.r Om (|R.C| + |S.C|) (thetaOmega R) (S.uT t) := by
  have hsm : A.Smooth (S.uT t) := fun j => (S.smooth t ht hl j).sub contDiffOn_const
  refine ⟨⟨ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ R.θ_pot R.om_pot, h1, h2,
    fun j => (hsm j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.subset_univ _))),
    fun x _ => sub_nonpos.2 (S.ph_le t ht hl x), ?_, ?_, Or.inl hsm⟩, hsm⟩
  · intro x hx
    have hL : 1 ≤ Real.log (R.r x) := by
      have := Real.log_le_log (Real.exp_pos 1) (hr x hx)
      rwa [Real.log_exp] at this
    have ha := S.le_ph t ht hl x hx
    have hb := R.le_φ x hx
    have hc := mul_le_mul_of_nonneg_right (le_abs_self R.C) (zero_le_one.trans hL)
    have hd := mul_le_mul_of_nonneg_left hL (abs_nonneg S.C)
    have he' := le_abs_self S.C
    show -((|R.C| + |S.C|) * Real.log (R.r x)) ≤ S.ph t x - S.C
    nlinarith
  · intro x k y hy w
    set f : (Fin D → ℂ) → ℝ := (fun z => R.θ.φ x z + S.ph t z) ∘ (A.chart k).symm with hfdef
    set g : (Fin D → ℂ) → ℝ := R.om.φ x ∘ (A.chart k).symm with hgdef
    have hyθ : (A.chart k).symm y ∈ R.θ.U x := hy.2.2.1.1
    have hyω : (A.chart k).symm y ∈ R.om.U x := hy.2.2.1.2
    have hf : ContDiffAt ℝ 2 f y := by
      have hθ := R.θ_pot.1 x k
      have hp := (S.smooth t ht hl k).mono
        (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.subset_univ (R.θ.U x))))
      exact ((hθ.add hp).contDiffAt (((A.chart k).isOpen_inter_preimage_symm
        (R.θ.isOpen_U x)).mem_nhds ⟨hy.1, hyθ⟩)).of_le (WithTop.coe_le_coe.2 le_top)
    have hg : ContDiffAt ℝ 2 g y :=
      ((R.om_pot.1 x k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm
        (R.om.isOpen_U x)).mem_nhds ⟨hy.1, hyω⟩)).of_le (WithTop.coe_le_coe.2 le_top)
    have hfun : (potForm (thetaOmega R) (S.uT t)).φ x ∘ (A.chart k).symm =
        fun y' => (f y' + 1 * g y') + -S.C := by
      funext y'
      show (R.θ.φ x _ + R.om.φ x _) + (S.ph t _ - S.C) = _
      simp only [hfdef, hgdef, Function.comp_apply]
      ring
    rw [hfun, levi_add_const', ReciprocityTheory.AnForm.levi_add_smul 1 hf hg w, one_mul]
    have hge := S.thGe t ht hl x k y ⟨hy.1, hyθ, hyω⟩ w
    have hgnn : 0 ≤ levi g y w := by
      by_cases hw : w = 0
      · subst hw
        simp [levi]
      · exact (R.om_pos x k y ⟨hy.1, hyω⟩ w hw).le
    have hprod := mul_nonneg (sub_nonneg.2 he) hgnn
    show 0 ≤ levi f y w + levi g y w
    nlinarith

end Currents

def LinearWeights.Statement : Prop :=
  (∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (F : Family A)
      (Λ : Type) [AddCommGroup Λ] [Module ℝ Λ] (φ₀ φc : Λ →ₗ[ℝ] (X → ℝ))
      (c : Λ →ₗ[ℝ] (Fin F.m → ℝ)) (t : ℝ),
      IsLinearMap ℝ (F.weight φ₀ φc c t) ∧
        ∀ x y : X, IsLinearMap ℝ fun lam => (F.chernForm (c lam) t).φ x y) ∧
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (R : RegChartData A)
    (S : System R), (∀ x ∈ R.Yo, Real.exp 1 ≤ R.r x) →
    ∃ (Om : KaehlerForm A) (C₁ : ℝ), ∀ t, 0 < t → S.ell₀ ≤ ell t → errE S.C t ≤ 1 →
      IsSmoothPotForm A R.Yo R.r Om C₁ (thetaOmega R) (S.uT t)

theorem LinearWeights.proof (hK : KaehlerBound.Statement) : LinearWeights.Statement := by
  refine ⟨fun A F Λ _ _ φ₀ φc c t => ⟨F.weight_isLinearMap φ₀ φc c t,
    fun x y => F.chernForm_isLinearMap c t x y⟩, ?_⟩
  intro D X _ A R S hr
  obtain ⟨Om, h1, h2⟩ := hK A R
  exact ⟨Om, |R.C| + |S.C|, fun t ht hl he => S.curr_isSmoothPotForm hr Om h1 h2 t ht hl he⟩

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

