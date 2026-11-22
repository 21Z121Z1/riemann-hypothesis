import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0125
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0127
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0122
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0124
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0097
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0079
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetLogNormDens
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi

noncomputable section

namespace SheetLogNormDensity

theorem log_sqrt_eq_phi {m : ℕ} (w : Fin m → ℂ) : Real.log √(∑ i, ‖w i‖ ^ 2) = phi w := by
  have h : (∑ i, ‖w i‖ ^ 2) = sqSum w := rfl
  rw [h, Real.log_sqrt (sqSum_nonneg w), phi]
  ring

theorem sqSum_ne_zero {m : ℕ} {w : Fin m → ℂ} (hw : w ≠ 0) : sqSum w ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2) ?_).ne'
  exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

end SheetLogNormDensity

theorem SheetLogNormDens.proof : SheetLogNormDens.Statement := by
  intro n d m J A x s T hs hT
  have hsx : s (A *ᵥ x) = x := by
    obtain ⟨_, _, _, _, h, _⟩ := hs
    exact h
  have han := FormIntegralPositivity.analyticAt_sheet hs
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  let L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin (T k))
  have hL : ∀ z, L z = T k *ᵥ z := fun z => rfl
  have hτ : AnalyticAt ℂ (L ∘ s) (A *ᵥ x) := (L.analyticAt _).comp han
  have hS : sqSum ((L ∘ s) (A *ᵥ x)) ≠ 0 := by
    rw [Function.comp_apply, hsx, hL]
    exact SheetLogNormDensity.sqSum_ne_zero (hT k)
  have hφ : ContDiffAt ℝ 2 phi ((L ∘ s) (A *ᵥ x)) := contDiffAt_phi hS
  have hfun : (fun z => Real.log √(∑ i, ‖(T k *ᵥ z) i‖ ^ 2)) ∘ s = phi ∘ (L ∘ s) := by
    funext y
    simp only [Function.comp_apply, hL]
    exact SheetLogNormDensity.log_sqrt_eq_phi _
  rw [hfun]
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
  rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
  exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceAbsIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets

open scoped ENNReal

noncomputable section

theorem finsum_const_mul_ofReal {α : Type*} (c : ℝ≥0∞) (hc : c ≠ 0) (g : α → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∑ᶠ x, c * ENNReal.ofReal (g x) = c * ENNReal.ofReal (∑ᶠ x, g x) := by
  have hsupp : (Function.support fun x => c * ENNReal.ofReal (g x)) = Function.support g := by
    ext x
    simp only [Function.mem_support, ne_eq, mul_eq_zero, hc, false_or, ENNReal.ofReal_eq_zero, not_le]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (hg x) (Ne.symm h)⟩
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum _ hfin, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp [hsupp]),
      ← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun i _ => hg i]
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (by rwa [hsupp]),
      ENNReal.ofReal_zero, mul_zero]

theorem gramVol_zero_map {e n : ℕ} (y : Fin e → ℂ) :
    gramVol (fun _ : Fin e → ℂ => (0 : Fin n → ℂ)) y = 0 := by
  have hw : (Fin.cons (0 : Fin n → ℂ) (fun _ : Fin e => (0 : Fin n → ℂ)) : Fin (e + 1) → Fin n → ℂ) = 0 := by
    ext a i
    refine Fin.cases ?_ (fun j => ?_) a <;> simp
  have hM0 : (Matrix.of fun _ _ => (0 : ℂ) : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) = 0 := rfl
  simp [gramVol, hw, hM0, Matrix.det_zero]

theorem lintegral_line_gram_abs {n : ℕ} (e : ℕ) (h : HermNorm n) (w : (Fin n → ℂ) → ℝ)
    (hw : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → w (t • x) = w x) (x : Fin n → ℂ) (hx : x ≠ 0) (G : ℝ)
    (hG : 0 ≤ G) :
    ∫⁻ t : ℂ, ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x))) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * G) =
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        (|w x| * ((e.factorial : ℝ) / Real.pi ^ e * G / h.dualNorm x ^ (2 * (e + 1))))) := by
  have hg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → (fun x => |w x|) (t • x) = (fun x => |w x|) x :=
    fun t x ht => by simp only [hw t x ht]
  have key := integral_line_gram e h (fun x => |w x|) hg x hx G
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  have hinv : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  set ρ := ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ with hρ_def
  have hρ : 0 < ρ := by
    rw [hρ_def, norm_pos_iff]
    intro h0
    apply hx
    rw [← hinv, show (h.matᵀ)⁻¹ *ᵥ x = 0 by simpa using congrArg WithLp.ofLp h0, Matrix.mulVec_zero]
  have hpt : ∀ t : ℂ, h.pointOf (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = t • x := by
    intro t
    have : (fun i => (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) i) = t • ((h.matᵀ)⁻¹ *ᵥ x) := by
      ext i
      simp
    simp only [HermNorm.pointOf, this, Matrix.mulVec_smul, hinv]
  have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
      fun t => (|w x| * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht
    have hiff : ‖t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
      rw [norm_smul, lt_div_iff₀ hρ]
    by_cases hb : ‖t‖ < 1 / ρ
    · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
        indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hw t x ht]
      ring
    · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
        indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
      ring
  have hint : Integrable (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) := by
    refine (((integrable_indicator_iff measurableSet_ball).2 ?_).const_mul (|w x| * G)).congr hae.symm
    exact ((continuous_norm.pow _).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) (1 / ρ))).mono_set ball_subset_closedBall
  have hfun : (fun t : ℂ => ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x))) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * G)) = fun t => ENNReal.ofReal
        ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|)
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) :=
    funext fun t => (ENNReal.ofReal_mul (indicator_nonneg (fun _ _ => abs_nonneg _) _)).symm
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t =>
    mul_nonneg (indicator_nonneg (fun _ _ => abs_nonneg _) _) (by positivity))]
  exact congrArg ENNReal.ofReal key

theorem sheetSum_lintegral_eq {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (w : (Fin n → ℂ) → ℝ)
    (hw : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → w (t • x) = w x) (y : Fin (e + 1) → ℂ) :
    (∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
      ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|)
        (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y))) *
      ENNReal.ofReal (‖t‖ ^ (2 * (e + 1)) * gramVol (fun y' =>
        (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)) =
    ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) *
      ENNReal.ofReal (chartAbsDens (J ⊔ Ideal.span {linForm ℓ - 1}) A w
        (fun _ x => Real.log (h.dualNorm x)) y) := by
  have hc : ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  unfold chartAbsDens sheetSum
  rw [finsum_mem_def, finsum_mem_def, ← finsum_const_mul_ofReal _ hc _
    (fun x => indicator_nonneg (fun x _ => by dsimp only; split_ifs; exacts [abs_nonneg _, le_rfl]) x)]
  refine finsum_congr fun x => ?_
  by_cases hx : x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    by_cases hs : ∃ s, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A x s
    · have hsT : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x = hs.choose := by
        unfold sheetThrough; rw [dif_pos hs]
      obtain ⟨-, -, -, -, hsx, -⟩ := hs.choose_spec
      have hy : hs.choose y = x := by rw [← hx.2]; exact hsx
      have hx0 : x ≠ 0 := by
        rintro rfl
        have hmem := hx.1 (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        simp [linForm] at hmem
      have hG := gramVol_nonneg (fun y' => (h.matᵀ)⁻¹ *ᵥ hs.choose y') y
      have hd : 0 ≤ h.dualNorm x ^ (2 * (e + 1 + 1)) :=
        pow_nonneg (by unfold HermNorm.dualNorm; positivity) _
      have hm := maDens_log_dualNorm_sheet h J ℓ A y x hs.choose hx hs.choose_spec
      beta_reduce at hm
      rw [dif_pos hs, hsT, hy, lintegral_line_gram_abs (e + 1) h w hw x hx0 _ hG]
      beta_reduce
      rw [hm, abs_mul,
        abs_of_nonneg (div_nonneg (mul_nonneg (by positivity) hG) hd),
        ← ENNReal.ofReal_mul (by positivity)]
    · have hsT : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x = 0 := by
        unfold sheetThrough; rw [dif_neg hs]
      rw [dif_neg hs, hsT]
      simp only [Pi.zero_apply, Matrix.mulVec_zero, gramVol_zero_map, mul_zero, ENNReal.ofReal_zero,
        lintegral_zero]
  · simp [indicator_of_notMem hx]

theorem SliceAbsIndep.proof (hL : ConeSheetGramLintegral.Statement) (hD : ConeDimOfChowForm.Statement) :
    SliceAbsIndep.Statement := by
  intro n e h J F ℓ ℓ' A A' w hJ hF hℓ hℓ' hA hA' hwm hw
  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) :=
    hD ℂ n (e + 2) J F hJ hF
  have hpm : Continuous fun z : EuclideanSpace ℂ (Fin n) => h.pointOf z := by
    unfold HermNorm.pointOf
    exact continuous_const.matrix_mulVec (PiLp.continuous_ofLp 2 _)
  have hFm : Measurable fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal
      ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|) z) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_abs.measurable.comp (hwm.comp hpm.measurable)).indicator measurableSet_ball)
  have hc0 : ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hR : ∀ (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
      (∫⁻ y, ∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
        ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|)
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y))) *
        ENNReal.ofReal (‖t‖ ^ (2 * (e + 1)) * gramVol (fun y' =>
          (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)) =
      ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) *
        ∫⁻ y, ENNReal.ofReal (chartAbsDens (J ⊔ Ideal.span {linForm ℓ - 1}) A w
          (fun _ x => Real.log (h.dualNorm x)) y) := fun ℓ A => by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun y => sheetSum_lintegral_eq h J ℓ A w hw y
  have k1 := (hL n (e + 1) h J ℓ A _ hJ hdim hℓ hA hFm).2
  have k2 := (hL n (e + 1) h J ℓ' A' _ hJ hdim hℓ' hA' hFm).2
  rw [hR] at k1 k2
  obtain ⟨hM0, hMtop⟩ := coordBall_mass (n := n) (m := e + 1 + 1) (le_of_ringKrullDim_quotient J hdim)
  have key := k1.symm.trans k2
  rwa [ENNReal.mul_right_inj hM0.ne' hMtop.ne, ENNReal.mul_right_inj hc0 ENNReal.ofReal_ne_top] at key

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutOffLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceCutOffLimit.vecCons_eq_affine {n e : ℕ} (h : HermNorm n) (G : (Fin n → ℂ) → ℝ) :
    (vecCons G fun (_ : Fin e) x => Real.log (h.dualNorm x)) =
      fun k x => (vecCons (0 : ℝ) fun (_ : Fin e) => (1 : ℝ)) k * Real.log (h.dualNorm x) +
        (vecCons G fun (_ : Fin e) (_ : Fin n → ℂ) => (0 : ℝ)) k x := by
  funext k x
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

theorem SliceCutOffLimit.proof (hI : SliceIdeal.Statement) (hM : SliceFormMass.Statement)
    (hB : SliceCutBoundary.Statement) : SliceCutOffLimit.Statement := by
  intro n e h W g ℓ hW hg hℓ
  obtain ⟨hJ, hdim, -⟩ := hI n (e + 1) W g ℓ hW hg hℓ
  refine ⟨sliceCut h, SliceCut.contDiff h, SliceCut.hasCompactSupport h, fun F G hF0 hG0 hF hG => ?_⟩
  by_cases hA : ∃ A : Matrix (Fin (e + 1)) (Fin n) ℂ, IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A
  · simp only [varInt, dif_pos hA]
    have hAs := hA.choose_spec
    generalize hA.choose = A at hAs ⊢
    have hne : zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}) ⊆ {x | x ≠ 0} := by
      rintro x hx rfl
      have h1 := hx (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.subset_span rfl))
      simp [linForm] at h1
    have hnear : ∀ f : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ f {x | x ≠ 0} →
        SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) f := fun f hf =>
      ⟨{x | x ≠ 0}, isOpen_ne, hne, hf⟩
    have hpot : ∀ f : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ f {x | x ≠ 0} →
        ∀ i, SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}))
          (vecCons f (fun (_ : Fin e) x => Real.log (h.dualNorm x)) i) := by
      intro f hf i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hnear f hf
      · simpa using hnear _ h.contDiffOn_log_dualNorm
    have hint : ∀ f f' : (Fin n → ℂ) → ℝ, (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → f (t • x) = f x) →
        ContDiffOn ℝ ∞ f {x | x ≠ 0} → (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → f' (t • x) = f' x) →
        ContDiffOn ℝ ∞ f' {x | x ≠ 0} →
        Integrable (chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A f
          (vecCons f' fun _ x => Real.log (h.dualNorm x))) := by
      intro f f' hf0 hf hf'0 hf'
      rw [SliceCutOffLimit.vecCons_eq_affine h f']
      refine hM n e h W g ℓ A f _ _ hW hg hℓ hAs hf0 hf.continuousOn (fun k t x ht => ?_) (fun k => ?_)
      · refine Fin.cases ?_ (fun i => ?_) k
        · simpa using hf'0 t x ht
        · simp
      · refine Fin.cases ?_ (fun i => ?_) k
        · simpa using hf'
        · simpa using contDiffOn_const
    have hD := fun (f : (Fin n → ℂ) → ℝ) (f' : (Fin n → ℂ) → ℝ) hf0 hf hf'0 hf' =>
      CutOffDominated.proof n (e + 1) _ A 1 (sliceCut h) f (vecCons f' fun _ x => Real.log (h.dualNorm x))
        hJ hdim hAs one_ne_zero (SliceCut.measurable h) (SliceCut.mem_Icc h)
        (fun x _ _ => SliceCut.tendsto_one h x) (hf.continuousOn.mono hne) (hpot f' hf')
        (hint f f' hf0 hf hf'0 hf')
    refine ⟨hD F G hF0 hF hG0 hG, ?_⟩
    have h1 := (hD G F hG0 hG hF0 hF).add (hB n e h W g ℓ A F G hW hg hℓ hAs hF0 hG0 hF hG)
    simpa using h1
  · simp only [varInt, dif_neg hA]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceFormLelong
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceFormLelong.ne_zero_of_mem {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hℓ : linForm ℓ - 1 ∈ I) {x : Fin n → ℂ} (hx : x ∈ zeroSet I) : x ≠ 0 := by
  rintro rfl
  have := hx _ hℓ
  simp [linForm] at this

theorem SliceFormLelong.tendsto_varietyIntegral_sliceCutoff_mul {n d : ℕ} (h : HermNorm n)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ) (a : (Fin n → ℂ) → ℝ)
    (hM : SliceWeightMassFinite.Statement) (hI : I.IsPrime) (hℓ : linForm ℓ - 1 ∈ I)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = d)
    (ha : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) (hac : ContinuousOn a {x | x ≠ 0}) :
    Tendsto (fun k => varInt I d (fun x => sliceCut h k x * a x) fun _ x => Real.log (h.dualNorm x))
      atTop (𝓝 (varInt I d a fun _ x => Real.log (h.dualNorm x))) := by
  have hne : zeroSet I ⊆ {x | x ≠ 0} := fun x hx => SliceFormLelong.ne_zero_of_mem hℓ hx
  have hsm : SmoothNear (zeroSet I) fun x => Real.log (h.dualNorm x) :=
    ⟨{0}ᶜ, isOpen_compl_singleton, hne, contDiffOn_log_dualNorm h⟩
  by_cases hA : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection I A
  · simp only [varInt, dif_pos hA]
    exact CutOffDominated.proof n d I hA.choose 1 (sliceCut h) a (fun _ x => Real.log (h.dualNorm x))
      hI hdim hA.choose_spec one_ne_zero (SliceCut.measurable h) (SliceCut.mem_Icc h)
      (fun x _ _ => SliceCut.tendsto_one h x) (hac.mono hne) (fun _ => hsm)
      (hM n d h I ℓ hA.choose a hI hℓ hdim hA.choose_spec ha hac)
  · simp only [varInt, dif_neg hA]
    exact tendsto_const_nhds

theorem SliceFormLelong.proof (hI : SliceIdeal.Statement) (hC : SliceComponents.Statement)
    (hM : SliceWeightMassFinite.Statement) (hK : SliceFormLelongCompact.Statement)
    (hT : SliceRegTail.Statement) : SliceFormLelong.Statement := by
  intro n e h W F u' ℓ a hW hF hu hℓ hℓP ha hsa
  obtain ⟨hprime, hdim, huJ⟩ := hI n (e + 1) W F ℓ hW hF hℓ
  obtain ⟨-, himg, -⟩ := hC n W u' ℓ hW hℓP
  have hmem1 : ∀ K : Ideal (MvPolynomial (Fin n) ℂ), linForm ℓ - 1 ∈ K ⊔ Ideal.span {linForm ℓ - 1} :=
    fun _ => Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hac : ContinuousOn a {x | x ≠ 0} := hsa.continuousOn
  have hmin : ∀ P ∈ (divCycle W u').support, P ⊔ Ideal.span {linForm ℓ - 1} ∈
      (W ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u'}).minimalPrimes := fun P hP => by
    rw [← himg]
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hP)

  have hL := (tendsto_finsetSum _ fun P hP =>
    (SliceFormLelong.tendsto_varietyIntegral_sliceCutoff_mul h _ ℓ a hM (hmin P hP).1.1 (hmem1 P)
      (IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hprime hdim (huJ u' hu) (hmin P hP)) ha hac).const_mul
        ((divCycle W u' P : ℕ) : ℝ)).sub
    (SliceFormLelong.tendsto_varietyIntegral_sliceCutoff_mul h _ ℓ a hM hprime (hmem1 W) hdim ha hac)

  have hKk := fun k : ℕ => hK n e h W F u' ℓ (fun x => sliceCut h k x * a x) hW hF hu hℓ hℓP
    ⟨{x | x ≠ 0}, isOpen_compl_singleton, fun x hx => SliceFormLelong.ne_zero_of_mem (hmem1 W) hx,
      (SliceCut.contDiff h k).contDiffOn.mul hsa⟩ (SliceCut.hasCompactSupport h k).mul_right
  have key : ∀ δ x y z w : ℝ, |x - y| ≤ δ / 3 → |y - z| < δ / 3 → |z - w| < δ / 3 → |x - w| < δ := by
    intro δ x y z w h1 h2 h3
    have := abs_sub_le x y w
    have := abs_sub_le y z w
    linarith
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨K, hKt⟩ := hT n e h W F u' ℓ a hW hF hu hℓ hℓP ha hac (δ / 3) (by positivity)
  obtain ⟨k, hkK, hk⟩ :=
    ((eventually_ge_atTop K).and (Metric.tendsto_nhds.mp hL (δ / 3) (by positivity))).exists
  filter_upwards [Metric.tendsto_nhds.mp (hKk k) (δ / 3) (by positivity), self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iic_mem_nhds one_pos)] with ε hε hε0 hε1
  rw [Real.dist_eq] at hε hk ⊢
  exact key δ _ _ _ _ (hKt k hkK ε ⟨hε0, hε1⟩) hε hk

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceWeightBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

theorem SliceWeightBound.proof (hL : SliceLogIntegrable.Statement) : SliceWeightBound.Statement := by
  classical
  intro n e h J F u ℓ hJ hF hu hℓ
  set S := J ⊔ Ideal.span {linForm ℓ - 1} with hS
  set g : (Fin n → ℂ) → ℝ := fun x => Real.log (h.dualNorm x) - Real.log ‖linEval u x‖ with hg
  set φ : Fin (e + 1) → (Fin n → ℂ) → ℝ := fun _ x => Real.log (h.dualNorm x) with hφ
  by_cases hA : ∃ A : Matrix (Fin (e + 1)) (Fin n) ℂ, IsFiniteProjection S A
  · refine ⟨∫ y, chartAbsDens S hA.choose g φ y, fun w M _ hwM => ?_⟩
    have hM : 0 ≤ M := (abs_nonneg _).trans (hwM 0)
    have hint := hL n e h J F u ℓ hA.choose hJ hF hu hℓ hA.choose_spec
    have hpt : ∀ y, ‖chartDens S hA.choose (fun x => g x * w x) φ y‖ ≤
        M * chartAbsDens S hA.choose g φ y := by
      intro y
      refine (Real.norm_eq_abs _ ▸ abs_chartDens_le _ _ _ _ y).trans ?_
      refine sheetSum_le_mul (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA.choose_spec y) M _ _ ?_
      intro x _ s _
      rw [abs_mul, abs_mul, abs_mul]
      have := hwM x
      calc |g x| * |w x| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|
          = |w x| * (|g x| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|) := by ring
        _ ≤ M * (|g x| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|) :=
          mul_le_mul_of_nonneg_right this (by positivity)
    have hb := norm_integral_le_of_norm_le (hint.const_mul M) (Filter.Eventually.of_forall hpt)
    rw [integral_const_mul, Real.norm_eq_abs] at hb
    simp only [varInt, dif_pos hA, chartInt]
    linarith
  · refine ⟨0, fun w M _ hwM => ?_⟩
    simp only [varInt, dif_neg hA, abs_zero, zero_mul, le_refl]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceWeightMassFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem SliceWeightMassFinite.exists_bound {n : ℕ} (a : (Fin n → ℂ) → ℝ)
    (hdeg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) (ha : ContinuousOn a {x | x ≠ 0}) :
    ∃ M : ℝ, ∀ x : Fin n → ℂ, x ≠ 0 → |a x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn
    (ha.mono fun x hx h0 => by simp [h0] at hx)
  refine ⟨M, fun x hx => ?_⟩
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hn : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx'
  rw [← hdeg (((‖x‖ : ℝ) : ℂ))⁻¹ x (inv_ne_zero hn), ← Real.norm_eq_abs]
  refine hM _ ?_
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hx']

theorem SliceWeightMassFinite.proof (h₁ : SliceMassFinite.Statement) : SliceWeightMassFinite.Statement := by
  classical
  intro n d h I ℓ A a hI hℓ hdim hA hdeg ha
  set φ : Fin d → (Fin n → ℂ) → ℝ := fun _ x => Real.log (h.dualNorm x) with hφ
  have h0 : ∀ x ∈ zeroSet I, x ≠ 0 := by
    rintro x hx rfl
    have := hx _ hℓ
    simp [linForm] at this
  obtain ⟨M, hM⟩ := SliceWeightMassFinite.exists_bound a hdeg ha
  set g : (Fin n → ℂ) → ℝ := (zeroSet I).piecewise a 0 with hgdef
  have hg : Measurable g :=
    (ha.mono fun x hx => h0 x hx).measurable_piecewise continuousOn_const
      (SheetSumMeasurable.isClosed_zeroSet I).measurableSet
  have heq : chartAbsDens I A a φ = chartAbsDens I A g φ := by
    funext y
    unfold chartAbsDens sheetSum
    refine finsum_congr fun x => finsum_congr fun hx => ?_
    simp only [hgdef, Set.piecewise_eq_of_mem _ _ _ hx.1]
  have hmeas : Measurable (chartAbsDens I A a φ) := by
    rw [heq]
    exact SheetSumMeasurable.measurable_sheetSum hA (fun u v => |u * v|)
      (continuous_fst.mul continuous_snd).abs.measurable hg φ
  refine ((h₁ n d h I ℓ A hI hℓ hdim hA).const_mul M).mono' hmeas.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hnn : 0 ≤ chartAbsDens I A a φ y :=
    finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  refine sheetSum_le_mul (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y) M _ _ fun x hx s _ => ?_
  rw [abs_mul, one_mul]
  exact mul_le_mul_of_nonneg_right (hM x (h0 x hx.1)) (abs_nonneg _)

end

end GroundTheory.Heights₂.Heights
end

