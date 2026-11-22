import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeierstrassDivisionAtPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

variable {τ : Type} [DecidableEq τ]

def lastToCoordinate (c : τ) : (Option {c' // c' ≠ c} → ℂ) →L[ℂ] (τ → ℂ) :=
  ContinuousLinearMap.pi fun c' =>
    if h : c' = c then ContinuousLinearMap.proj none else ContinuousLinearMap.proj (some ⟨c', h⟩)

def coordinateToLast (c : τ) : (τ → ℂ) →L[ℂ] (Option {c' // c' ≠ c} → ℂ) :=
  ContinuousLinearMap.pi fun o =>
    match o with
    | none => ContinuousLinearMap.proj c
    | some c' => ContinuousLinearMap.proj c'.1

theorem lastToCoordinate_apply (c : τ) (w : Option {c' // c' ≠ c} → ℂ) (c' : τ) :
    lastToCoordinate c w c' = if h : c' = c then w none else w (some ⟨c', h⟩) := by
  by_cases h : c' = c <;> simp [lastToCoordinate, h]

omit [DecidableEq τ] in
theorem coordinateToLast_none (c : τ) (y : τ → ℂ) : coordinateToLast c y none = y c := rfl

omit [DecidableEq τ] in
theorem coordinateToLast_some (c : τ) (y : τ → ℂ) (c' : {c' // c' ≠ c}) :
    coordinateToLast c y (some c') = y c'.1 := rfl

theorem lastToCoordinate_coordinateToLast (c : τ) (y : τ → ℂ) :
    lastToCoordinate c (coordinateToLast c y) = y := by
  funext c'
  rw [lastToCoordinate_apply]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem lastToCoordinate_pointWithLast (c : τ) (s : ℂ) :
    lastToCoordinate c (pointWithLast 0 s) = Pi.single c s := by
  funext c'
  rw [lastToCoordinate_apply]
  split_ifs with h
  · subst h; simp [pointWithLast]
  · simp [pointWithLast, h]

theorem WeierstrassDivisionAtPoint.proof (hW : WeierstrassDivision.Statement) :
    WeierstrassDivisionAtPoint.Statement := by
  intro τ _ _ y₀ c d F g hF hg hord
  have hA : ∀ h : (τ → ℂ) → ℂ, AnalyticAt ℂ h y₀ →
      AnalyticAt ℂ (fun w => h (y₀ + lastToCoordinate c w)) 0 := by
    intro h hh
    exact AnalyticAt.fun_comp_of_eq hh (analyticAt_const.add ((lastToCoordinate c).analyticAt 0)) (by simp)
  have hord' : analyticOrderAt
      (fun t => (fun w => F (y₀ + lastToCoordinate c w)) (pointWithLast 0 t)) 0 = d := by
    simpa only [lastToCoordinate_pointWithLast] using hord
  obtain ⟨q, a, hq, ha, heq⟩ := hW {c' // c' ≠ c} d _ _ (hA F hF) (hA g hg) hord'
  refine ⟨fun y => q (coordinateToLast c (y - y₀)), fun j u => a j (fun c' => u c'.1 - y₀ c'.1), ?_, ?_, ?_⟩
  · exact AnalyticAt.fun_comp_of_eq hq
      (((coordinateToLast c).analyticAt _).comp (analyticAt_id.sub analyticAt_const)) (by simp)
  · intro j
    have hR : AnalyticAt ℂ (fun u : τ → ℂ => fun c' : {c' // c' ≠ c} => u c'.1 - y₀ c'.1) (zeroCoordinate c y₀) := by
      have hL := ((ContinuousLinearMap.pi fun c' : {c' // c' ≠ c} =>
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c'.1).analyticAt (zeroCoordinate c y₀)).sub
          (analyticAt_const (v := fun c' : {c' // c' ≠ c} => y₀ c'.1))
      convert hL using 1
      funext u c'
      rfl
    refine AnalyticAt.fun_comp_of_eq (ha j) hR ?_
    funext c'
    simp [zeroCoordinate_apply, c'.2]
  · have hT : Tendsto (fun y => coordinateToLast c (y - y₀)) (𝓝 y₀) (𝓝 0) := by
      have hc : Continuous fun y : τ → ℂ => coordinateToLast c (y - y₀) :=
        (coordinateToLast c).continuous.comp (continuous_id.sub continuous_const)
      simpa using hc.tendsto y₀
    filter_upwards [hT.eventually heq] with y hy
    have hy' : y₀ + lastToCoordinate c (coordinateToLast c (y - y₀)) = y := by
      rw [lastToCoordinate_coordinateToLast]; abel
    simp only [hy'] at hy
    rw [hy]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (fun i : {c' // c' ≠ c} => coordinateToLast c (y - y₀) (some i)) =
        fun c' => zeroCoordinate c y c'.1 - y₀ c'.1 := by
      funext c'
      rw [coordinateToLast_some, zeroCoordinate_apply, if_neg c'.2, Pi.sub_apply]
    rw [h1, coordinateToLast_none, Pi.sub_apply]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZariskiAnalyticNormality
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

theorem holGerms_isUnit_of_value_ne_zero {σ : Type} [Fintype σ] {w : σ → ℂ} (φ : holGerms w)
    (hφ : holGermValue w φ ≠ 0) : IsUnit φ := by
  rcases φ with ⟨_, f, hf, rfl⟩
  have hfw : f w ≠ 0 := hφ
  let ψ : holGerms w := ⟨((fun z => (f z)⁻¹ : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ), _, hf.inv hfw, rfl⟩
  refine IsUnit.of_mul_eq_one ψ (Subtype.ext ?_)
  change ((fun z => f z * (f z)⁻¹ : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = ((fun _ => (1 : ℂ) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
  exact Germ.coe_eq.2 ((hf.continuousAt.eventually_ne hfw).mono fun z hz => mul_inv_cancel₀ hz)

theorem holGermPointIdeal_le_jacobson {σ : Type} [Fintype σ] (w : σ → ℂ) :
    holGermPointIdeal w ≤ (⊥ : Ideal (holGerms w)).jacobson := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  apply holGerms_isUnit_of_value_ne_zero
  have hx0 : holGermValue w x = 0 := RingHom.mem_ker.1 hx
  simp [map_add, map_mul, hx0]

theorem germQuotPointIdeal_le_jacobson {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    germQuotPointIdeal I w ≤ (⊥ : Ideal (holGerms w ⧸ I.map (polyGerm w))).jacobson := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have hu := Ideal.mem_jacobson_bot.1 (holGermPointIdeal_le_jacobson w hx') y'
  simpa [map_add, map_mul] using hu.map (Ideal.Quotient.mk (I.map (polyGerm w)))

theorem ZariskiAnalyticNormality.proof (hN : HolGermsNoetherian.Statement)
    (hD : CompletionNormalDescent.Statement) (hA : AffineCompletionNormal.Statement)
    (hE : GermCompletionEquiv.Statement) : ZariskiAnalyticNormality.Statement := by
  intro σ _ I w hI hIC hw
  have := hN σ w
  obtain ⟨e, -⟩ := hE σ I w
  obtain ⟨hdom, hic⟩ := hA σ I (polyPointIdeal I w) hI hIC (polyPointIdeal_isMaximal I w hw)
  have hdom' : IsDomain (AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :=
    e.toMulEquiv.isDomain
  have hic' : IsIntegrallyClosed
      (AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :=
    IsIntegrallyClosed.of_equiv e.symm
  obtain ⟨hB, hBic⟩ := hD _ (germQuotPointIdeal I w) inferInstance
    (germQuotPointIdeal_le_jacobson I w) hdom' hic'
  exact ⟨(Ideal.Quotient.isDomain_iff_prime _).1 hB, hBic⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConePolar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ConePolar.Statement : Prop :=
  ∀ e : ℕ, ∃ κ : ℝ, ∀ (n : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (g : (Fin n → ℂ) → ℝ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) →
    ContinuousOn g {x | x ≠ 0} →
      coneIntegral h J e g =
        κ * varInt (J ⊔ Ideal.span {linForm ℓ - 1}) e g (fun _ x => Real.log (h.dualNorm x))

theorem isProjPrime_bot_space (n : ℕ) : IsProjPrime (⊥ : Ideal (MvPolynomial (Fin (n + 1)) ℂ)) where
  isPrime := Ideal.isPrime_bot
  isHomog f hf d := by
    rw [Ideal.mem_bot] at hf ⊢
    rw [hf, map_zero]
  isRelevant := ⟨0, fun hX => X_ne_zero (0 : Fin (n + 1)) (Ideal.mem_bot.mp hX)⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff

noncomputable section

def CutOffBoundaryBound.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (F G : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    SmoothNear (zeroSet J) F → SmoothNear (zeroSet J) G → (∀ i, SmoothNear (zeroSet J) (φ i)) →
    HasCompactSupport F →
      ∃ R C : ℝ, ∀ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ →
        |chartInt J A G (vecCons (fun x => χ x * F x) φ) -
            chartInt J A (fun x => χ x * G x) (vecCons F φ)| ≤
          C * ((∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1) (vecCons χ φ) y) +
            Real.sqrt (energyInt J A (Metric.closedBall 0 R) χ))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryParts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

def MaDensLeibniz.Statement : Prop :=
  ∀ (D : ℕ) (φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (f g : (Fin (D + 1) → ℂ) → ℝ) (z : Fin (D + 1) → ℂ),
    ContDiffAt ℝ 2 f z → ContDiffAt ℝ 2 g z →
      maDens (Fin.cons (fun y => f y * g y) φ) z =
          f z * maDens (Fin.cons g φ) z + g z * maDens (Fin.cons f φ) z + gradDens φ f g z +
            gradDens φ g f z ∧
        maDens (Fin.cons (fun y => f y ^ 2 / 2) φ) z =
          f z * maDens (Fin.cons f φ) z + gradDens φ f f z

def EnergyDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (v : (Fin (d + 1) → ℂ) → ℝ),
    AnalyticAt ℂ s y → 0 ≤ gradDens (fun _ : Fin d => euclPot ∘ s) v v y

def GradDensSheetBound.Statement : Prop :=
  ∀ (n d : ℕ) (φ : Fin d → (Fin n → ℂ) → ℝ) (U K : Set (Fin n → ℂ)),
    IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (φ i) U) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ)
        (v w : (Fin (d + 1) → ℂ) → ℝ), AnalyticAt ℂ s y → s y ∈ K →
          |gradDens (fun i => φ i ∘ s) v w y| ≤
            C * Real.sqrt (gradDens (fun _ : Fin d => euclPot ∘ s) v v y) *
              Real.sqrt (gradDens (fun _ : Fin d => euclPot ∘ s) w w y)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffDominated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def CutOffDominated.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (P : MvPolynomial (Fin d) ℂ) (χ : ℕ → (Fin n → ℂ) → ℝ) (f : (Fin n → ℂ) → ℝ)
    (ψ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A → P ≠ 0 →
    (∀ k, Measurable (χ k)) → (∀ k x, χ k x ∈ Set.Icc (0 : ℝ) 1) →
    (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → Tendsto (fun k => χ k x) atTop (𝓝 1)) →
    ContinuousOn f (zeroSet J) → (∀ i, SmoothNear (zeroSet J) (ψ i)) →
    Integrable (chartAbsDens J A f ψ) →
      Tendsto (fun k => chartInt J A (fun x => χ k x * f x) ψ) atTop (𝓝 (chartInt J A f ψ))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def CutOffLimit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧
        (∀ k, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
          ∀ x ∈ U ∩ zeroSet J, χ k x = 0) ∧
        ∀ (F G : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
          SmoothNear (zeroSet J) F → SmoothNear (zeroSet J) G → (∀ i, SmoothNear (zeroSet J) (φ i)) →
          HasCompactSupport F →
            Tendsto (fun k => chartInt J A (fun x => χ k x * F x) (vecCons G φ)) atTop
                (𝓝 (chartInt J A F (vecCons G φ))) ∧
              Tendsto (fun k => chartInt J A G (vecCons (fun x => χ k x * F x) φ)) atTop
                (𝓝 (chartInt J A G (vecCons F φ)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationMinorOfDetection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem DerivationMinorOfDetection.polyOriginIdeal_isPrime : polyOriginIdeal.IsPrime :=
  polyOriginIdeal_isMaximal.isPrime

attribute [local instance] DerivationMinorOfDetection.polyOriginIdeal_isPrime

def DerivationMinorOfDetection.Statement : Prop :=
  ∀ (T : Type) [CommRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (f : Fin h → T), (∀ i, f i ∈ P) →
    (∀ a : Fin h → Localization.AtPrime P,
      ∑ i, a i * algebraMap T (Localization.AtPrime P) (f i) ∈ maximalIdeal (Localization.AtPrime P) ^ 2 →
        ∀ i, a i ∈ maximalIdeal (Localization.AtPrime P)) →
    (∀ g ∈ P, (∀ D : Derivation ℤ T T, D g ∈ P) →
      algebraMap T (Localization.AtPrime P) g ∈ maximalIdeal (Localization.AtPrime P) ^ 2) →
    ∃ D : Fin h → Derivation ℤ T T, (Matrix.of fun i j => D j (f i)).det ∉ P

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscriminantSheetCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def DiscriminantSheetCover.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ (P : MvPolynomial (Fin d) ℂ) (U D : ℕ → Set (Fin d → ℂ)) (N : ℕ → ℕ)
        (s : (k : ℕ) → Fin (N k) → (Fin d → ℂ) → Fin n → ℂ),
        P ≠ 0 ∧
        (∀ k, IsOpen (U k) ∧ MeasurableSet (D k) ∧ D k ⊆ U k ∧
          ∀ j, DifferentiableOn ℂ (s k j) (U k)) ∧
        Pairwise (Function.onFun Disjoint D) ∧
        (⋃ k, D k)ᶜ ⊆ {y | eval y P = 0} ∧
        volume (⋃ k, D k)ᶜ = 0 ∧
        (∀ k, ∀ y ∈ U k,
          ComplexSets.fibre J A y = Set.range (fun j => s k j y) ∧
          Function.Injective (fun j => s k j y) ∧
          ∀ j, IsSheetAt J A (s k j y) (s k j))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGeneralPointBranches
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def DivisorGeneralPointBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W ∧
            (∀ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W' → W' = W) ∧
            (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W) ∧
            ∃ (m : ℕ) (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ)
              (π : Matrix (Fin d) (Fin n) ℂ),
              (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
              (∃ N ∈ 𝓝 q, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) ∧
              (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) ∧
              (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
              ∀ b, Function.Bijective
                (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGoodPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

variable {n : ℕ}

def DivisorRegularAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (d : ℕ) (q : Fin n → ℂ) : Prop :=
  ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
    (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
      (∀ y ∈ O, A (g y) = y) ∧ zeroSet J ∩ {x | linEval u x = 0} ∩ V = g '' O

def NormalDivisorChartAt {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (u : Fin n → ℂ) (d : ℕ) (q : Fin n → ℂ) : Prop :=
  ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q →
    ∃ (r : ℝ) (φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ) (k : ℕ), 0 < r ∧
      DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧ φ 0 = w ∧
      Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧
      (∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' Metric.ball 0 s) ∧
      VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k ∧
      ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
        fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0

def NormalDoublePointsOnDivisor {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (u : Fin n → ℂ) (q : Fin n → ℂ) : Prop :=
  ∃ N ∈ 𝓝 q, ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal,
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' →
      IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N → w ≠ w' → linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0

theorem eq_const_of_mem_zeroSetIn_lineDiagonal {z : Fin 1 ⊕ Fin 1 → ℂ}
    (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalIdeal) :
    z = fun _ => z (Sum.inl 0) := by
  have hzd : z (Sum.inr 0) = z (Sum.inl 0) := by
    have h1 := hz (X (Sum.inr 0) - X (Sum.inl 0)) (by
      show IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalMap (X (Sum.inr 0) - X (Sum.inl 0)) = 0
      rw [IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalMap, map_sub, aeval_X, aeval_X]
      simp)
    simp only [map_sub, eval_X] at h1
    exact sub_eq_zero.mp h1
  funext s
  rcases s with i | i
  · rw [Subsingleton.elim i 0]
  · rw [Subsingleton.elim i 0, hzd]

theorem lineNormalDivisorChartAt :
    NormalDivisorChartAt IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel (fun _ => (1 : ℂ)) 0 0 := by
  intro w hw hw0
  have hw' : w = 0 := by
    rw [eq_const_of_mem_zeroSetIn_lineDiagonal hw]
    have h0 : w (Sum.inl 0) = 0 := congrFun hw0 0
    funext _
    exact h0
  subst hw'
  refine ⟨1, fun t _ => t 0, 1, one_pos, Differentiable.differentiableOn (by fun_prop), ?_, rfl,
    fun t _ => IndefiniteRowSideFullHecke.ComplexSets.const_mem_zeroSetIn_lineDiagonal (t 0), ?_, ?_, ?_⟩
  · intro s _ t _ hst
    funext i
    rw [show i = 0 from Fin.ext (by omega)]
    exact congrFun hst (Sum.inl 0)
  · intro s hs
    refine ⟨Metric.ball 0 s, Metric.ball_mem_nhds 0 hs, ?_⟩
    rintro z ⟨hz, hzB⟩
    refine ⟨fun _ => z (Sum.inl 0), ?_, (eq_const_of_mem_zeroSetIn_lineDiagonal hz).symm⟩
    rw [mem_ball_zero_iff] at hzB ⊢
    refine lt_of_le_of_lt ?_ hzB
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro _
    exact norm_le_pi_norm z (Sum.inl 0)
  · refine ⟨fun _ => 1, differentiableOn_const _, fun _ _ => one_ne_zero, fun t _ => ?_⟩
    simp [linEval, IndefiniteRowSideFullHecke.ComplexSets.firstCoords]
  · intro v hv _
    funext i
    rw [show i = 0 from Fin.ext (by omega)]
    exact hv

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermGeneralCoordinates
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def GeneralLinearCoordinates.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (f : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → ¬ (∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0) →
    ∃ (A : (Option σ → ℂ) ≃L[ℂ] (Option σ → ℂ)) (d : ℕ),
      analyticOrderAt (fun t => f (A (pointWithLast 0 t))) 0 = d

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

