import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MonomialValuesOneBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped Pointwise

noncomputable section

namespace SpanningAtDominantWeight

theorem exists_le_sum_eq {α : Type} [Fintype α] (f : α → ℕ) :
    ∀ a : ℕ, a ≤ ∑ i, f i → ∃ g : α → ℕ, g ≤ f ∧ ∑ i, g i = a := by
  classical
  intro a
  induction a with
  | zero => exact fun _ ↦ ⟨0, fun _ ↦ Nat.zero_le _, by simp⟩
  | succ a ih =>
    intro ha
    obtain ⟨g, hg, hs⟩ := ih (by omega)
    have hex : ∃ i, g i < f i := by
      by_contra h
      push Not at h
      have : ∑ i, f i ≤ ∑ i, g i := Finset.sum_le_sum fun i _ ↦ h i
      omega
    obtain ⟨i, hi⟩ := hex
    refine ⟨Function.update g i (g i + 1), fun j ↦ ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        omega
      · simp only [Function.update_of_ne hj]
        exact hg j
    · rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)] at hs
      omega

variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem exists_split (μ : Coord n →₀ ℕ) (d e : ι → ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = d k + e k) :
    ∃ μ₁ μ₂ : Coord n →₀ ℕ, μ = μ₁ + μ₂ ∧ (∀ k, ∑ i, μ₁ ⟨k, i⟩ = d k) ∧ ∀ k, ∑ i, μ₂ ⟨k, i⟩ = e k := by
  classical
  choose g hg hs using fun k ↦
    exists_le_sum_eq (fun i : Fin (n k + 1) ↦ μ ⟨k, i⟩) (d k) (by rw [hμ k]; omega)
  let μ₁ : Coord n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p ↦ g p.1 p.2
  have h₁ : ∀ p, μ₁ p = g p.1 p.2 := fun p ↦ rfl
  refine ⟨μ₁, μ - μ₁, ?_, fun k ↦ ?_, fun k ↦ ?_⟩
  · ext p
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, h₁]
    have : g p.1 p.2 ≤ μ p := hg p.1 p.2
    omega
  · simp only [h₁]
    exact hs k
  · have hsplit : ∑ i, μ ⟨k, i⟩ = ∑ i, g k i + ∑ i, (μ - μ₁) ⟨k, i⟩ := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [Finsupp.tsub_apply, h₁]
      have : g k i ≤ μ ⟨k, i⟩ := hg k i
      omega
    have := hμ k
    have := hs k
    omega

theorem prod_pow_add {M : Type} [CommMonoid M] (z : Coord n → M) (μ₁ μ₂ : Coord n →₀ ℕ) :
    ∏ p, z p ^ (μ₁ + μ₂) p = (∏ p, z p ^ μ₁ p) * ∏ p, z p ^ μ₂ p := by
  simp [pow_add, Finset.prod_mul_distrib]

theorem aeval_monomial_one {R : Type} [CommRing R] (z : Coord n → R) (μ : Coord n →₀ ℕ) :
    aeval z (monomial μ (1 : ℤ)) = ∏ p, z p ^ μ p := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), map_one, one_mul]

omit [Fintype ι] in

theorem isMultiHomog_monomial (μ : Coord n →₀ ℕ) (d : ι → ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = d k) :
    Geo.IsMultiHomog (ι := blockIdx n) (monomial μ (1 : ℤ)) d := by
  classical
  intro m hm k
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  subst this
  exact hμ k

theorem secM_eq_span {Ω : Type} [Field Ω] (y : Coord n → Ω) (d : ι → ℕ) :
    Geo.secM (ι := blockIdx n) y d = (Submodule.span ℤ (monomialValues y d)).toAddSubgroup := by
  unfold Geo.secM
  congr 1
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro s ⟨g, hg, rfl⟩
    rw [g.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm ↦ ?_
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hg m hm, rfl⟩)
  · rw [Submodule.span_le]
    rintro s ⟨μ, hμ, rfl⟩
    exact Submodule.subset_span ⟨monomial μ 1, isMultiHomog_monomial μ d hμ, aeval_monomial_one y μ⟩

theorem monomialValues_add {Ω : Type} [Field Ω] (y : Coord n → Ω) (d e : ι → ℕ) :
    monomialValues y (d + e) = monomialValues y d * monomialValues y e := by
  ext s
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    obtain ⟨μ₁, μ₂, rfl, h₁, h₂⟩ := exists_split μ d e hμ
    exact Set.mem_mul.mpr ⟨_, ⟨μ₁, h₁, rfl⟩, _, ⟨μ₂, h₂, rfl⟩, (prod_pow_add y μ₁ μ₂).symm⟩
  · intro hs
    obtain ⟨_, ⟨μ₁, h₁, rfl⟩, _, ⟨μ₂, h₂, rfl⟩, rfl⟩ := Set.mem_mul.mp hs
    exact ⟨μ₁ + μ₂, fun k ↦ by simp [Finset.sum_add_distrib, h₁, h₂], (prod_pow_add y μ₁ μ₂).symm⟩

theorem monomialValues_nsmul {Ω : Type} [Field Ω] (y : Coord n → Ω) (d : ι → ℕ) (τ : ℕ) :
    monomialValues y (τ • d) = monomialValues y d ^ τ := by
  induction τ with
  | zero => rw [zero_smul, monomialValues_zero, pow_zero, Set.singleton_one]
  | succ τ ih => rw [succ_nsmul, monomialValues_add, ih, pow_succ]

theorem monomialValues_one_block {Ω : Type} [Field Ω] (m : ℕ) (x' : Fin (m + 1) → Ω) :
    monomialValues (n := fun _ : Unit ↦ m) (fun p ↦ x' p.2) (fun _ ↦ 1) = Set.range x' := by
  classical
  ext s
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    have hsum : ∑ i, μ ⟨(), i⟩ = 1 := hμ ()
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hsum
    have hj1 : μ ⟨(), j⟩ = 1 := by omega
    have hrest := Finset.sum_eq_zero_iff.mp (by omega : ∑ i ∈ Finset.univ.erase j, μ ⟨(), i⟩ = 0)
    refine ⟨j, ?_⟩
    rw [Fintype.prod_eq_single (⟨(), j⟩ : Coord fun _ : Unit ↦ m)]
    · simp [hj1]
    · rintro ⟨⟨⟩, i⟩ hi
      have hij : i ≠ j := fun h ↦ hi (h ▸ rfl)
      rw [hrest i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩), pow_zero]
  · rintro ⟨j, rfl⟩
    refine ⟨Finsupp.single ⟨(), j⟩ 1, fun k ↦ ?_, ?_⟩
    · simp [Finsupp.single_apply]
    · rw [← Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_single_index (by simp)]
      simp

theorem monomial_bound {Q : Ideal (MvPolynomial (Coord n) ℤ)} {A : Geo.HermLine (blockIdx n)} {b : ι → ℕ}
    (hA : Geo.MonomialsBounded (ι := blockIdx n) Q A b) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) Q) :
    ∀ τ : ℕ, ∀ μ : Coord n →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = (τ • b) k) → ‖∏ p, z p ^ μ p‖ ≤ A.h z ^ τ := by
  intro τ
  induction τ with
  | zero =>
    intro μ hμ
    have h0 : ∀ p, μ p = 0 := fun p ↦ by
      have := hμ p.1
      rw [zero_smul, Pi.zero_apply, Finset.sum_eq_zero_iff] at this
      exact this p.2 (Finset.mem_univ _)
    simp [h0]
  | succ τ ih =>
    intro μ hμ
    obtain ⟨μ₁, μ₂, rfl, h₁, h₂⟩ := exists_split μ (τ • b) b (fun k ↦ by rw [hμ k, succ_nsmul]; rfl)
    rw [prod_pow_add, norm_mul, pow_succ]
    exact mul_le_mul (ih μ₁ h₁) (hA z hz μ₂ h₂) (norm_nonneg _) (pow_nonneg (A.pos z hz.1).le _)

theorem isSmallH_monomial {Ω : Type} [Field Ω] (y : Coord n → Ω) (A : Geo.HermLine (blockIdx n)) (b : ι → ℕ)
    (hAa : ∀ k, A.a k = b k)
    (hA : Geo.MonomialsBounded (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) A b) (τ : ℕ)
    (μ : Coord n →₀ ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = (τ • b) k) :
    Geo.IsSmallH (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) y A τ (∏ p, y p ^ μ p) := by
  intro dg dh g h z hg hh hd hgh hz
  have hdeg : dg = τ • b + dh := by
    funext k
    have := hd k
    rw [hAa k] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast (by linarith : (dg k : ℤ) = τ * b k + dh k)
  have hmh := LowerBoundFree.isMultiHomog_mul (isMultiHomog_monomial μ (τ • b) hμ) hh
  rw [← hdeg] at hmh
  have hneg : Geo.IsMultiHomog (ι := blockIdx n) (-(monomial μ (1 : ℤ) * h)) dg :=
    fun m hm ↦ hmh m (by simpa using hm)
  have hF := LowerBoundFree.isMultiHomog_add hg hneg
  have hF0 : aeval y (g + -(monomial μ (1 : ℤ) * h)) = 0 := by
    rw [map_add, map_neg, map_mul, aeval_monomial_one, hgh]
    ring
  have hz0 := hz.2 _ (LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
  have hmz : eval z (map (Int.castRingHom ℂ) (monomial μ (1 : ℤ))) = ∏ p, z p ^ μ p := by
    rw [map_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), map_one, one_mul]
  rw [map_add, map_neg, map_mul, eval_add, eval_neg, eval_mul, hmz, add_neg_eq_zero] at hz0
  rw [hz0, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (monomial_bound hA hz τ μ hμ) (norm_nonneg _)

end SpanningAtDominantWeight

theorem SpanningAtDominantWeight.proof : SpanningAtDominantWeight.Statement := by
  intro ι _ _ n Ω _ y b m x' hx' τ
  have hτ : (fun _ : Unit ↦ τ) = τ • fun _ : Unit ↦ 1 := by
    funext
    simp
  refine ⟨?_, SpanningAtDominantWeight.secM_eq_span y (τ • b), fun A Q hA z hz μ hμ ↦ SpanningAtDominantWeight.monomial_bound hA hz τ μ hμ,
    fun A hAa hA μ hμ ↦ SpanningAtDominantWeight.isSmallH_monomial y A b hAa hA τ μ hμ⟩
  rw [SpanningAtDominantWeight.secM_eq_span, SpanningAtDominantWeight.secM_eq_span, hτ, SpanningAtDominantWeight.monomialValues_nsmul,
    SpanningAtDominantWeight.monomialValues_one_block, SpanningAtDominantWeight.monomialValues_nsmul, ← Submodule.span_pow, ← Submodule.span_pow, hx']

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.NormSqEvalConeScale
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace ChartMetric

theorem contDiff_evalCone {ι : Type} [Fintype ι] {n : ι → ℕ} (f : MvPolynomial (Coord n) ℤ) :
    ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ evalCone z f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : (fun z : Cone n ℂ ↦ evalCone z (C a)) = fun _ ↦ (a : ℂ) := by
      funext z; unfold evalCone; rw [eval₂_C]; simp
    rw [h]; exact contDiff_const
  | add p q hp hq =>
    have h : (fun z : Cone n ℂ ↦ evalCone z (p + q)) = fun z ↦ evalCone z p + evalCone z q := by
      funext z; simp [evalCone, eval₂_add]
    rw [h]; exact hp.add hq
  | mul_X p v hp =>
    have h : (fun z : Cone n ℂ ↦ evalCone z (p * X v)) = fun z ↦ evalCone z p * z v.1 v.2 := by
      funext z; simp [evalCone, eval₂_mul, eval₂_X]
    have hv : ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ z v.1 v.2) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n v.1 + 1) ↦ ℂ) v.2).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun k ↦ Fin (n k + 1) → ℂ) v.1)).contDiff
    rw [h]; exact hp.mul hv

theorem norm_sq_evalCone_scale {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (t : ι → ℂ) (z : Cone n ℂ)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    ‖evalCone (fun k i ↦ t k * z k i) f‖ ^ 2 = (∏ k, ‖t k‖ ^ (2 * (δ k : ℤ))) * ‖evalCone z f‖ ^ 2 := by
  have h : evalCone (fun k i ↦ t k * z k i) f = (∏ k, t k ^ δ k) * evalCone z f :=
    eval₂_scale_of_isWeightedHomogeneous t (fun v ↦ z v.1 v.2) hf
  rw [h, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [norm_pow, ← pow_mul, ← zpow_natCast]
  congr 1
  push_cast
  ring

theorem chartSum_scale {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (t : ι → ℂ) (z : Cone n ℂ) (d : ι → ℕ) :
    ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (fun k i ↦ t k * z k i) (chartMonomial c d)‖ ^ 2 =
      (∏ k, ‖t k‖ ^ (2 * (d k : ℤ))) * ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone z (chartMonomial c d)‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ ↦
    norm_sq_evalCone_scale t z (isWeightedHomogeneous_chartMonomial c d)

theorem chartSum_pos {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {z : Cone n ℂ}
    (hz : BlockNonzero z) (d : ι → ℕ) :
    0 < ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone z (chartMonomial c d)‖ ^ 2 := by
  choose c hc using fun k ↦ Function.ne_iff.mp (hz k)
  have h0 : evalCone z (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h0) 2)
    (Finset.single_le_sum (f := fun c ↦ ‖evalCone z (chartMonomial c d)‖ ^ 2)
      (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ c))

theorem den_scale {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
    (D : AddBlockData P) {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {r : ℕ} {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ}
    (hG : P.IsHomogGenerators G δ) (t : ι → ℂ) (ht : ∀ k, t k ≠ 0) (z : Cone n ℂ) :
    D.den d g G δ (fun k i ↦ t k * z k i) =
      (∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k))) * D.den d g G δ z := by
  have ht' : ∀ k, ‖t k‖ ≠ 0 := fun k ↦ norm_ne_zero_iff.mpr (ht k)
  unfold AddBlockData.den
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    obtain ⟨e, he, hed⟩ := hg.homog c j
    rw [norm_sq_evalCone_scale t z he]
    simp only [hed]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [norm_sq_evalCone_scale t z (hG.homog i)]
    have hl : ∀ k, l2Norm (fun j ↦ t k * z k j) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) =
        ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) * l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) :=
      fun k ↦ by rw [vectorL2Norm_const_mul, mul_zpow]
    simp only [hl, Finset.prod_mul_distrib]
    have hs : (∏ k, ‖t k‖ ^ (2 * (δ i k : ℤ))) * ∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) =
        ∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← zpow_add₀ (ht' k)]
      congr 1
      ring
    rw [← hs]
    ring

theorem scale_alg (A B h s L S Den : ℝ) (hA : 0 < A) (hB : 0 < B) (hD : 0 < Den) :
    A * h * (s * L) * Real.sqrt (B * S / (B * A ^ 2 * Den)) = s * (h * L * Real.sqrt (S / Den)) := by
  have e : B * S / (B * A ^ 2 * Den) = S / Den / A ^ 2 := by
    field_simp
  rw [e, Real.sqrt_div' _ (sq_nonneg A), Real.sqrt_sq hA.le]
  field_simp

theorem proof (hDen : ChartDenominatorAlt.Statement) (hPts : ConePoints.Statement) (hCross : ChartCrossRatio.Statement) :
    ChartMetric.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG
  have hDen' := hDen ι n P D d g hg r G δ hG
  have hold : ContDiff ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ (D.basePart₂ w : Cone n ℂ)) :=
    contDiff_pi.2 fun k ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun o ↦ Fin (D.extSizes o + 1) → ℂ) (some k)).contDiff
  have hmaps : Set.MapsTo (fun w : Cone D.extSizes ℂ ↦ (D.basePart₂ w : Cone n ℂ))
      {w | BlockNonzero w} {z | BlockNonzero z} := fun w hw k ↦ hw (some k)
  refine ⟨⟨HermLine.mk (n := D.extSizes) AddBlockData.newDeg (D.plusMetric N d g G δ) ?pos ?smul ?smooth, rfl, fun w _ ↦ rfl, ?conj⟩, ?pts⟩
  case pos =>
    intro w hw
    have hz : BlockNonzero (D.basePart₂ w) := fun k ↦ hw (some k)
    unfold AddBlockData.plusMetric
    exact mul_pos (mul_pos (N.metric_pos _ hz) (vectorL2Norm_pos (hw none)))
      (Real.sqrt_pos.mpr (div_pos (chartSum_pos hz d) (hDen'.1 _ hz)))
  case smul =>
    intro t w ht hw
    have hz : BlockNonzero (D.basePart₂ w) := fun k ↦ hw (some k)
    have ht' : ∀ k, t (some k) ≠ 0 := fun k ↦ ht (some k)
    have hpos : ∀ k, 0 < ‖t (some k)‖ := fun k ↦ norm_pos_iff.mpr (ht' k)
    have hdeg : ∏ o, ‖t o‖ ^ AddBlockData.newDeg o = ‖t none‖ := by
      rw [Fintype.prod_option]
      simp [AddBlockData.newDeg]
    have hm := N.metric_smul (fun k ↦ t (some k)) (D.basePart₂ w) ht' hz
    have hs := chartSum_scale (fun k ↦ t (some k)) (D.basePart₂ w) d
    have hd := den_scale D hg hG (fun k ↦ t (some k)) ht' (D.basePart₂ w)
    beta_reduce at hm hs hd
    have hC : ∏ k, ‖t (some k)‖ ^ (2 * ((d k : ℤ) + D.deg k)) =
        (∏ k, ‖t (some k)‖ ^ (2 * (d k : ℤ))) * (∏ k, ‖t (some k)‖ ^ D.deg k) ^ 2 := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ (hpos k).ne']
      congr 1
      push_cast
      ring
    show D.plusMetric N d g G δ (fun o i ↦ t o * w o i) =
      (∏ o, ‖t o‖ ^ AddBlockData.newDeg o) * D.plusMetric N d g G δ w
    have eold : D.basePart₂ (fun o i ↦ t o * w o i) = fun k i ↦ t (some k) * D.basePart₂ w k i := rfl
    have enew : D.newPart (fun o i ↦ t o * w o i) = fun i ↦ t none * D.newPart w i := rfl
    unfold AddBlockData.plusMetric
    rw [eold, enew, hdeg, hm, vectorL2Norm_const_mul, hs, hd, hC, hN]
    exact scale_alg _ _ _ _ _ _ _ (Finset.prod_pos fun k _ ↦ zpow_pos (hpos k) _)
      (Finset.prod_pos fun k _ ↦ zpow_pos (hpos k) _) (hDen'.1 _ hz)
  case smooth =>
    have h1 : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ N.metric (D.basePart₂ w)) {w | BlockNonzero w} :=
      N.metric_smooth.comp hold.contDiffOn hmaps
    have h2 : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ l2Norm (D.newPart w)) {w | BlockNonzero w} :=
      contDiffOn_l2Norm_block (n := D.extSizes) none
    have hS : ContDiff ℝ ∞ (fun w : Cone D.extSizes ℂ ↦
        ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (D.basePart₂ w) (chartMonomial c d)‖ ^ 2) :=
      ContDiff.sum fun c _ ↦ (contDiff_norm_sq ℝ).comp ((contDiff_evalCone _).comp hold)
    have hDn : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ D.den d g G δ (D.basePart₂ w)) {w | BlockNonzero w} :=
      hDen'.2.comp hold.contDiffOn hmaps
    have h3 := (hS.contDiffOn.div hDn fun w hw ↦ (hDen'.1 _ (hmaps hw)).ne').sqrt fun w hw ↦
      (div_pos (chartSum_pos (hmaps hw) d) (hDen'.1 _ (hmaps hw))).ne'
    exact (h1.mul h2).mul h3
  case conj =>
    intro hNc w hw
    have hz : BlockNonzero (D.basePart₂ w) := fun k ↦ hw (some k)
    have hN' : N.metric (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) = N.metric (D.basePart₂ w) := hNc _ hz
    have hev : ∀ f : MvPolynomial (Coord n) ℤ, evalCone (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) f =
        starRingEnd ℂ (evalCone (D.basePart₂ w) f) :=
      fun f ↦ evalCone_map (starRingEnd ℂ) (D.basePart₂ w) f
    have hS : ∑ c : (k : ι) → Fin (n k + 1),
        ‖evalCone (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) (chartMonomial c d)‖ ^ 2 =
        ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (D.basePart₂ w) (chartMonomial c d)‖ ^ 2 := by
      simp only [hev, Complex.norm_conj]
    have hD : D.den d g G δ (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) = D.den d g G δ (D.basePart₂ w) := by
      unfold AddBlockData.den
      simp only [hev, Complex.norm_conj, vectorL2Norm_conj]
    have eold : D.basePart₂ (fun o i ↦ starRingEnd ℂ (w o i)) = fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i) := rfl
    have enew : D.newPart (fun o i ↦ starRingEnd ℂ (w o i)) = fun i ↦ starRingEnd ℂ (D.newPart w i) := rfl
    show D.plusMetric N d g G δ (fun o i ↦ starRingEnd ℂ (w o i)) = D.plusMetric N d g G δ w
    unfold AddBlockData.plusMetric
    rw [eold, enew, vectorL2Norm_conj, hN', hS, hD]
  case pts =>
    intro w hw c la hm hz'
    obtain ⟨hzP, -⟩ := (hPts ι n P D d g hg).2 w hw
    have hG0 : ∀ i, evalCone (D.basePart₂ w) (G i) = 0 := fun i ↦
      hzP.2 _ (by rw [← hG.span_eq]; exact Ideal.subset_span ⟨i, rfl⟩)
    have hcr : ∀ c' j, evalCone (D.basePart₂ w) (chartMonomial c' d) * evalCone (D.basePart₂ w) (g c j) =
        evalCone (D.basePart₂ w) (chartMonomial c d) * evalCone (D.basePart₂ w) (g c' j) := by
      intro c' j
      have h := hzP.2 _ (hCross ι n P D d g hg c c' j)
      unfold evalCone at h ⊢
      rw [eval₂_sub, eval₂_mul, eval₂_mul, sub_eq_zero] at h
      exact h
    have hla : ∀ c' j, D.newPart w j * evalCone (D.basePart₂ w) (chartMonomial c' d) =
        la * evalCone (D.basePart₂ w) (g c' j) := by
      intro c' j
      rw [hz' j, div_mul_eq_mul_div, div_eq_iff hm, mul_assoc, mul_comm (evalCone _ (g c j)), hcr c' j]
      ring
    have hl2 : l2Norm (D.newPart w) ^ 2 = ∑ j, ‖D.newPart w j‖ ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    have hden : D.den d g G δ (D.basePart₂ w) = ∑ c', ∑ j, ‖evalCone (D.basePart₂ w) (g c' j)‖ ^ 2 := by
      simp [AddBlockData.den, hG0]
    have key : l2Norm (D.newPart w) ^ 2 * ∑ c', ‖evalCone (D.basePart₂ w) (chartMonomial c' d)‖ ^ 2 =
        ‖la‖ ^ 2 * D.den d g G δ (D.basePart₂ w) := by
      rw [hl2, hden, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ ↦ ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have e := congrArg (fun x : ℂ ↦ ‖x‖ ^ 2) (hla c' j)
      simp only [norm_mul, mul_pow] at e
      exact e
    have hDpos : 0 < D.den d g G δ (D.basePart₂ w) := hDen'.1 _ hzP.1
    have hL : 0 ≤ l2Norm (D.newPart w) := Real.sqrt_nonneg _
    have e : l2Norm (D.newPart w) *
        Real.sqrt ((∑ c', ‖evalCone (D.basePart₂ w) (chartMonomial c' d)‖ ^ 2) / D.den d g G δ (D.basePart₂ w)) =
        ‖la‖ := by
      rw [← Real.sqrt_sq hL, ← Real.sqrt_mul (sq_nonneg _), ← mul_div_assoc, key, mul_div_assoc,
        div_self hDpos.ne', mul_one, Real.sqrt_sq (norm_nonneg _)]
    unfold AddBlockData.plusMetric
    rw [mul_assoc, e, mul_comm]

end ChartMetric

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PHomogGeneratorsExist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem sum_weightedHomogeneousComponent_image (f : MvPolynomial (Coord n) ℤ) :
    ∑ m ∈ f.support.image (Finsupp.weight (coordDeg n)), weightedHomogeneousComponent (coordDeg n) m f = f := by
  conv_rhs => rw [← sum_weightedHomogeneousComponent (coordDeg n) f]
  refine (finsum_eq_sum_of_support_subset _ ?_).symm
  intro m hm
  rw [Function.mem_support] at hm
  rw [Finset.coe_image, Set.mem_image]
  by_contra h
  refine hm (weightedHomogeneousComponent_eq_zero' m f fun d hd hdm ↦ h ⟨d, hd, hdm⟩)

theorem HomogGeneratorsExist.proof : HomogGeneratorsExist.Statement := by
  classical
  intro ι _ _ n P
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P.ideal : P.ideal.FG)

  let S : Finset (MvPolynomial (Coord n) ℤ) := s.biUnion fun f ↦
    (f.support.image (Finsupp.weight (coordDeg n))).image fun m ↦ weightedHomogeneousComponent (coordDeg n) m f
  have hShom : ∀ g ∈ S, ∃ m : ι → ℕ, IsWeightedHomogeneous (coordDeg n) g m := by
    intro g hg
    simp only [S, Finset.mem_biUnion, Finset.mem_image] at hg
    obtain ⟨f, -, m, -, rfl⟩ := hg
    exact ⟨m, weightedHomogeneousComponent_isWeightedHomogeneous m f⟩
  have hSP : ∀ g ∈ S, g ∈ P.ideal := by
    intro g hg
    simp only [S, Finset.mem_biUnion, Finset.mem_image] at hg
    obtain ⟨f, hf, m, -, rfl⟩ := hg
    exact P.homogeneous f (hs ▸ Ideal.subset_span hf) m
  let e := S.equivFin
  refine ⟨S.card, fun i ↦ (e.symm i : MvPolynomial (Coord n) ℤ),
    fun i ↦ Classical.choose (hShom _ (e.symm i).2), ⟨fun i ↦ Classical.choose_spec (hShom _ (e.symm i).2), ?_⟩⟩
  have hrange : Set.range (fun i ↦ (e.symm i : MvPolynomial (Coord n) ℤ)) = (S : Set _) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp⟩
  rw [hrange]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro g hg
    exact hSP g hg
  · rw [← hs, Ideal.span_le]
    intro f hf
    rw [← sum_weightedHomogeneousComponent_image f]
    refine Ideal.sum_mem _ fun m hm ↦ Ideal.subset_span ?_
    simp only [S, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image]
    exact ⟨f, hf, m, by simpa using hm, rfl⟩

end

end GroundTheory.Heights₂.Heights
end

