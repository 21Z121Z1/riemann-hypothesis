import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0085
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0124
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0120
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0123
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0108
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0122
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0121
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0079
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.MeasurableOfContinuousOnNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntSlice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff

variable {n : ℕ}

theorem linEval_smul (ℓ x : Fin n → ℂ) (t : ℂ) : linEval ℓ (t • x) = t * linEval ℓ x := by
  simp only [linEval, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem differentiable_linEval (ℓ : Fin n → ℂ) : Differentiable ℂ (linEval ℓ) := by
  unfold linEval
  fun_prop

theorem mem_zeroSet_slice_iff (W : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ x : Fin n → ℂ) :
    x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}) ↔ x ∈ zeroSet W ∧ linEval ℓ x = 1 := by
  have hev : eval x (linForm ℓ - 1) = linEval ℓ x - 1 := by simp [linForm, linEval]
  constructor
  · intro hx
    refine ⟨fun q hq => hx q (Ideal.mem_sup_left hq), ?_⟩
    have := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rwa [hev, sub_eq_zero] at this
  · rintro ⟨hx, h1⟩ q hq
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hq
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_add, map_mul, hev, h1, hx y hy]
    simp

theorem ne_zero_of_mem_slice {W : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ x : Fin n → ℂ}
    (hx : x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) : x ≠ 0 := by
  rintro rfl
  have := ((mem_zeroSet_slice_iff W ℓ 0).mp hx).2
  simp [linEval] at this

theorem slice_rescale {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W) (ℓ ℓ' x : Fin n → ℂ)
    (hx : x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ' - 1}) \ {x | linEval ℓ x = 0}) :
    (linEval ℓ x)⁻¹ • x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}) \ {x | linEval ℓ' x = 0} ∧
      (linEval ℓ' ((linEval ℓ x)⁻¹ • x))⁻¹ • ((linEval ℓ x)⁻¹ • x) = x := by
  obtain ⟨hxs, hx0⟩ := hx
  rw [mem_zeroSet_slice_iff] at hxs
  have hx0' : linEval ℓ x ≠ 0 := hx0
  refine ⟨⟨(mem_zeroSet_slice_iff W ℓ _).mpr ⟨PointLine.smul_mem_zeroSet hW hxs.1 _, ?_⟩, ?_⟩, ?_⟩
  · rw [linEval_smul, inv_mul_cancel₀ hx0']
  · simp only [Set.mem_ofPred_eq, linEval_smul, hxs.2, mul_one]
    exact inv_ne_zero hx0'
  · rw [linEval_smul, hxs.2, mul_one, inv_inv, smul_smul, mul_inv_cancel₀ hx0', one_smul]

theorem FormIntSlice.proof (hI : SliceIdeal.Statement) (hM : SliceFormMass.Statement)
    (hCC : VarIntChartChange.Statement) : FormIntSlice.Statement := by
  intro n e h W F ℓ a b hW hF hℓ ha hac hb hbs
  have hex : ∃ ℓ : Fin n → ℂ, linForm ℓ ∉ W := ⟨ℓ, hℓ⟩
  rw [formInt, dif_pos hex]
  set ℓ₁ := hex.choose
  have hℓ₁ : linForm ℓ₁ ∉ W := hex.choose_spec
  obtain ⟨hP₁, hD₁, hN₁⟩ := hI n (e + 1) W F ℓ₁ hW hF hℓ₁
  obtain ⟨hP, hD, hN⟩ := hI n (e + 1) W F ℓ hW hF hℓ
  set φ : Fin (e + 1) → (Fin n → ℂ) → ℝ := vecCons b fun _ x => Real.log (h.dualNorm x)
  have hsm : ∀ m : Fin n → ℂ, ∀ k, SmoothNear (zeroSet (W ⊔ Ideal.span {linForm m - 1})) (φ k) := by
    intro m k
    refine Fin.cases ?_ (fun _ => smoothNear_log_dualNorm_slice h W m) k
    exact ⟨{x | x ≠ 0}, isOpen_ne, fun x hx => ne_zero_of_mem_slice hx, hbs⟩
  have hopen : ∀ m : Fin n → ℂ, IsOpen {x : Fin n → ℂ | linEval m x ≠ 0} :=
    fun m => isOpen_ne_fun (differentiable_linEval m).continuous continuous_const
  have hmeas : Measurable a := by
    have hs : ({0}ᶜ : Set (Fin n → ℂ)) = {x | x ≠ 0} := by ext; simp
    exact measurable_of_continuousOn_compl_singleton 0 (hs ▸ hac)
  refine hCC n (e + 1) _ _ ℓ ℓ₁ {x | linEval ℓ x ≠ 0} {x | linEval ℓ₁ x ≠ 0}
    (fun x => (linEval ℓ₁ x)⁻¹ • x) (fun x => (linEval ℓ x)⁻¹ • x) a a φ φ
    (vecCons 0 fun _ => 1) (fun _ => linEval ℓ₁) hP₁ hD₁ hP hD (hN₁ ℓ hℓ) (hN ℓ₁ hℓ₁) (hopen ℓ) (hopen ℓ₁)
    (fun x hx => hx.2) (fun x hx => hx.2)
    (((differentiable_linEval ℓ₁).differentiableOn.inv fun x hx => hx).smul differentiableOn_id)
    (((differentiable_linEval ℓ).differentiableOn.inv fun x hx => hx).smul differentiableOn_id)
    (fun x hx => (slice_rescale hW.isHomog ℓ₁ ℓ x hx).1) (fun x hx => (slice_rescale hW.isHomog ℓ ℓ₁ x hx).1)
    (fun x hx => (slice_rescale hW.isHomog ℓ₁ ℓ x hx).2) (fun x hx => (slice_rescale hW.isHomog ℓ ℓ₁ x hx).2)
    hmeas hmeas (fun x hx => (ha _ x (inv_ne_zero hx.2)).symm) (hsm ℓ₁) (hsm ℓ)
    (fun _ => (differentiable_linEval ℓ₁).differentiableOn) (fun _ x hx => hx) ?_ ?_
  · intro k x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (by simp [linEval])
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [φ, hb _ x (inv_ne_zero hx)]
    · simp only [φ, Matrix.cons_val_succ, one_mul]
      rw [HermNorm.dualNorm_smul, Real.log_mul (by simpa using hx) (HermNorm.dualNorm_pos h hx0).ne',
        norm_inv, Real.log_inv]
      ring
  · intro A hA
    have hφ : φ = fun k x => (vecCons 0 fun _ => 1 : Fin (e + 1) → ℝ) k * Real.log (h.dualNorm x) +
        (vecCons b fun _ _ => 0 : Fin (e + 1) → (Fin n → ℂ) → ℝ) k x := by
      funext k x
      refine Fin.cases ?_ (fun i => ?_) k <;> simp [φ]
    rw [hφ]
    refine hM n e h W F ℓ₁ A a _ _ hW hF hℓ₁ hA ha hac (fun k => ?_) (fun k => ?_)
    · exact Fin.cases (fun t x ht => hb t x ht) (fun _ _ _ _ => rfl) k
    · exact Fin.cases hbs (fun _ => contDiffOn_const) k

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelDisc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormalModelDisc.proof (hreg : NormalCurveRegularPoint.Statement) : NormalModelDisc.Statement := by
  intro n J M w _ hdim hw
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  obtain ⟨A, O, V, g, hO, -, hwV, hg, hAg, hZV⟩ :=
    hreg (Fin n ⊕ Fin M.m) M.ideal w M.isPrime M.isIntegrallyClosed hdim' hw
  have hwg : w ∈ g '' O := hZV ▸ ⟨hw, hwV⟩
  obtain ⟨y₀, hy₀, hgy₀⟩ := hwg
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO y₀ hy₀
  have hmem : ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) r, y₀ + τ ∈ O := fun τ hτ ↦ hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa using hτ)
  refine ⟨r, hr, fun τ ↦ g (y₀ + τ), ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    exact ((hg _ (hmem τ hτ)).differentiableAt.comp τ
      (differentiableAt_const y₀ |>.add differentiableAt_id)).differentiableWithinAt
  · intro s hs t ht hst
    have h := congrArg A hst
    simp only at h
    rw [hAg _ (hmem s hs), hAg _ (hmem t ht)] at h
    exact add_left_cancel h
  · intro τ hτ
    have h : g (y₀ + τ) ∈ g '' O := ⟨_, hmem τ hτ, rfl⟩
    rw [← hZV] at h
    exact h.1
  · simp [hgy₀]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutTailMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem SliceCutTailMass.proof (hMF : SliceMassFinite.Statement) : SliceCutTailMass.Statement := by
  classical
  intro n e h W F ℓ hW hF hℓ
  obtain ⟨hprime, hdim, -⟩ := SliceIdeal.proof n (e + 1) W F ℓ hW hF hℓ
  set I := W ⊔ Ideal.span {linForm ℓ - 1} with hIdef
  have hmem : linForm ℓ - 1 ∈ I := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  unfold varInt
  split_ifs with hA
  swap
  · exact tendsto_const_nhds
  set A := hA.choose
  have hAf : IsFiniteProjection I A := hA.choose_spec
  have hfin : ∀ y, (fibre I A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n (e + 1) I A hprime hdim hAf y).2.1
  have hne : zeroSet I ⊆ {x | x ≠ 0} := fun x hx hx0 => by
    subst hx0
    have := hx _ hmem
    simp [linForm] at this
  have hsm : ∀ _ : Fin (e + 1), SmoothNear (zeroSet I) fun x => Real.log (h.dualNorm x) := fun _ =>
    ⟨{0}ᶜ, isOpen_compl_singleton, hne, contDiffOn_log_dualNorm h⟩
  have hint := hMF n (e + 1) h I ℓ A hprime hmem hdim hAf
  unfold chartInt
  have key := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (F := fun k => chartDens I A (fun x => 1 - sliceCut h k x) fun _ x => Real.log (h.dualNorm x))
    (chartAbsDens I A (fun _ => 1) fun _ x => Real.log (h.dualNorm x))
    (fun k => (SheetSumMeasurable.proof n (e + 1) I A _ _ hprime hdim hAf
      (measurable_const.sub (SliceCut.measurable h k)) hsm).1.aestronglyMeasurable) hint
    (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · rwa [integral_zero] at key
  · rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    rw [CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    split_ifs with hs
    · have h01 := SliceCut.mem_Icc h k x
      rw [abs_mul, abs_mul, abs_one, one_mul, abs_of_nonneg (by linarith [h01.2])]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [h01.1])
    · simp
  · unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    have hterm : ∀ x, Tendsto (fun k : ℕ => if hs : ∃ s, IsSheetAt I A x s then
        (1 - sliceCut h k x) * ReciprocityTheory.AnForm.maDens
          (fun i => (fun (_ : Fin (e + 1)) x => Real.log (h.dualNorm x)) i ∘ hs.choose) y else 0)
        atTop (𝓝 0) := fun x => by
      split_ifs with hs
      · simpa using ((SliceCut.tendsto_one h x).const_sub 1).mul_const
          (ReciprocityTheory.AnForm.maDens (fun i => (fun (_ : Fin (e + 1)) x => Real.log (h.dualNorm x)) i ∘ hs.choose) y)
      · exact tendsto_const_nhds
    simpa using tendsto_finsetSum (hfin y).toFinset fun x _ => hterm x

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceExhaustion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceExhaustion.varInt_tendsto_sliceCut {n d : ℕ} (h : HermNorm n)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ) (hM : SliceMassFinite.Statement)
    (hI : I.IsPrime) (hℓ : linForm ℓ - 1 ∈ I) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = d)
    (hsm : SmoothNear (zeroSet I) fun x => Real.log (h.dualNorm x)) :
    Tendsto (fun k => varInt I d (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) atTop
      (𝓝 (varInt I d (fun _ => 1) fun _ x => Real.log (h.dualNorm x))) := by
  by_cases hA : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection I A
  · simp only [varInt, dif_pos hA]
    have := CutOffDominated.proof n d I hA.choose 1 (sliceCut h) (fun _ => 1)
      (fun _ x => Real.log (h.dualNorm x)) hI hdim hA.choose_spec one_ne_zero (SliceCut.measurable h)
      (SliceCut.mem_Icc h) (fun x _ _ => SliceCut.tendsto_one h x) continuousOn_const (fun _ => hsm)
      (hM n d h I ℓ hA.choose hI hℓ hdim hA.choose_spec)
    simpa only [mul_one] using this
  · simp only [varInt, dif_neg hA]
    exact tendsto_const_nhds

theorem SliceExhaustion.proof (hI : SliceIdeal.Statement) (hC : SliceComponents.Statement)
    (hM : SliceMassFinite.Statement) (hE : SliceLelongError.Statement) : SliceExhaustion.Statement := by
  intro n e h J F u ℓ hJ hF hu hℓ hℓW
  obtain ⟨hprime, hdim, huJ⟩ := hI n (e + 1) J F ℓ hJ hF hℓ
  obtain ⟨-, himg, -⟩ := hC n J u ℓ hJ hℓW
  have hmem1 : ∀ K : Ideal (MvPolynomial (Fin n) ℂ), linForm ℓ - 1 ∈ K ⊔ Ideal.span {linForm ℓ - 1} :=
    fun _ => Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  refine ⟨sliceCut h, SliceCut.contDiff h, SliceCut.hasCompactSupport h, SliceCut.mem_Icc h,
    SliceCut.tendsto_one h,
    SliceExhaustion.varInt_tendsto_sliceCut h _ ℓ hM hprime (hmem1 J) hdim
      (smoothNear_log_dualNorm_slice h J ℓ), fun W hW => ?_, hE n e h J F u ℓ hJ hF hu hℓ hℓW⟩
  have hmin : W ⊔ Ideal.span {linForm ℓ - 1} ∈
      (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u}).minimalPrimes := by
    rw [← himg]
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hW)
  exact SliceExhaustion.varInt_tendsto_sliceCut h _ ℓ hM hmin.1.1 (hmem1 W)
    (IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hprime hdim (huJ u hu) hmin)
    (smoothNear_log_dualNorm_slice h W ℓ)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceFormMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff

namespace SliceFormMass

theorem exists_bound {n : ℕ} (f : (Fin n → ℂ) → ℝ)
    (hf0 : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → f (t • x) = f x) (hfc : ContinuousOn f {x | x ≠ 0}) :
    ∃ M : ℝ, ∀ x : Fin n → ℂ, x ≠ 0 → |f x| ≤ M := by
  have hS : Metric.sphere (0 : Fin n → ℂ) 1 ⊆ {x | x ≠ 0} := by
    intro x hx hx0
    rw [hx0, mem_sphere_zero_iff_norm, norm_zero] at hx
    exact zero_ne_one hx
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn (hfc.mono hS)
  refine ⟨M, fun x hx => ?_⟩
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have ht : ((‖x‖⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hn)
  rw [← hf0 _ x ht, ← Real.norm_eq_abs]
  refine hM _ ?_
  rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hn]

theorem measurable_of_continuousOn_ne_zero {n : ℕ} {f : (Fin n → ℂ) → ℝ}
    (hfc : ContinuousOn f {x | x ≠ 0}) : Measurable f := by
  refine measurable_of_isOpen fun O hO => ?_
  have hsplit : f ⁻¹' O = ({x | x ≠ 0} ∩ f ⁻¹' O) ∪ ({0} ∩ f ⁻¹' O) := by
    ext x
    by_cases hx : x = 0 <;> simp [hx]
  rw [hsplit]
  exact (hfc.isOpen_inter_preimage (isOpen_ne) hO).measurableSet.union
    ((Set.finite_singleton (0 : Fin n → ℂ)).subset Set.inter_subset_left).measurableSet

end SliceFormMass

theorem SliceFormMass.proof (hI : SliceIdeal.Statement) (hM : SliceMassFinite.Statement)
    (hC : SheetFormCompare.Statement) : SliceFormMass.Statement := by
  intro n e h W F ℓ A f c ψ hW hF hℓ hA hf0 hfc hψ0 hψc
  obtain ⟨hprime, hdim, -⟩ := hI n (e + 1) W F ℓ hW hF hℓ
  have hmem : linForm ℓ - 1 ∈ W ⊔ Ideal.span {linForm ℓ - 1} :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hint := hM n (e + 1) h _ ℓ A hprime hmem hdim hA
  obtain ⟨M, hMf⟩ := SliceFormMass.exists_bound f hf0 hfc
  obtain ⟨C, hCs⟩ := hC n (e + 1) h c ψ hψ0 hψc
  have hmeas : Measurable (chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A f
      (fun k x => c k * Real.log (h.dualNorm x) + ψ k x)) :=
    SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
      (continuous_abs.comp (continuous_fst.mul continuous_snd)).measurable
      (SliceFormMass.measurable_of_continuousOn_ne_zero hfc) _
  refine (hint.const_mul (M * |C|)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hnn : 0 ≤ chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A f
      (fun k x => c k * Real.log (h.dualNorm x) + ψ k x) y :=
    finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs <;> positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  refine sheetSum_le_mul (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y) (M * |C|) _ _ fun x hx s hs => ?_
  obtain ⟨hxZ, hxy⟩ := hx
  obtain ⟨U, hU, hyU, hsd, hsx, -, -⟩ := hs
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hxZ _ hmem
    simp [linForm] at this
  have hbd := hCs s U (A *ᵥ x) hU hyU hsd (by rw [hsx]; exact hx0)
  rw [show A *ᵥ x = y from hxy] at hbd
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMf x hx0)
  rw [one_mul, abs_mul]
  calc |f x| * |ReciprocityTheory.AnForm.maDens
        (fun k => (fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) y|
      ≤ M * (|C| * |ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y|) :=
        mul_le_mul (hMf x hx0) (hbd.trans ((le_abs_self _).trans (abs_mul _ _).le))
          (abs_nonneg _) hM0
    _ = M * |C| * |ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y| := by
        ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMassFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets
open scoped nonZeroDivisors

noncomputable section

theorem SliceMassFinite.exists_projClosure {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (hI : I.IsPrime) (hℓ : linForm ℓ - 1 ∈ I)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (W : Ideal (MvPolynomial (Fin n) ℂ)) (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ),
      IsProjPrime W ∧ IsChowForm W (e + 2) F ∧ linForm ℓ ∉ W ∧ W ⊔ Ideal.span {linForm ℓ - 1} = I := by
  obtain ⟨W, hW, hℓW, hWI, -⟩ := ChartHomogenise.proof ℂ n I ℓ hI hℓ
  have hP := hW.isPrime

  have hx : Ideal.Quotient.mk W (linForm ℓ - 1) ∈ (MvPolynomial (Fin n) ℂ ⧸ W)⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hP.ne_top ?_
    have h00 := hW.isHomog _ (Ideal.Quotient.eq_zero_iff_mem.mp h0) 0
    rw [homogeneousComponent_zero] at h00
    have hc : coeff 0 (linForm ℓ - 1) = -1 := by
      simp [linForm, coeff_sum, coeff_C_mul, coeff_X]
    rw [hc, map_neg, map_one, Ideal.neg_mem_iff] at h00
    exact (Ideal.eq_top_iff_one W).mpr h00
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx
  have eq := DoubleQuot.quotQuotEquivQuotSup W (Ideal.span {linForm ℓ - 1})
  rw [Ideal.map_span, Set.image_singleton] at eq
  rw [ringKrullDim_eq_of_ringEquiv eq, hWI, hdim] at h1

  have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : WithBot ℕ∞) := by
    have := ringKrullDim_quotient_le W
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at this

  have hdimW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    generalize hD : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = D at h1 h2
    induction D using WithBot.recBotCoe with
    | bot => simp at h1
    | coe b =>
      induction b using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : (⊤ : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h2
        exact ENat.natCast_ne_top _ (top_le_iff.mp h3)
      | coe m =>
        have hm1 : e + 1 + 1 ≤ m := by exact_mod_cast h1
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have hA' : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety W (k + 1) := ⟨hP, by rw [hD]; rfl⟩
        have h3 := IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice hA' hW.isHomog hℓW
        rw [hWI, hdim] at h3
        have hk : k ≤ e + 1 := by exact_mod_cast h3
        have hke : k + 1 = e + 1 + 1 := by omega
        rw [hke]
        rfl
  obtain ⟨F, hFW⟩ := (IndefiniteRowSideFullHecke.ComplexSets.exists_isChowForm_iff (e := e + 1) hW).mpr ⟨hP, hdimW⟩
  exact ⟨W, F, hW, hFW, hℓW, hWI⟩

theorem SliceMassFinite.proof (hF : SliceFormMass.Statement) : SliceMassFinite.Statement := by
  intro n d h I ℓ A hI hℓ hdim hA
  cases d with
  | zero =>
    have hconst : chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) =
        fun _ => chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) 0 :=
      funext fun y => congrArg _ (Subsingleton.elim y 0)
    rw [hconst]
    have : IsFiniteMeasure (volume : Measure (Fin 0 → ℂ)) := by
      rw [MeasureTheory.volume_pi, Measure.pi_of_empty (x := 0)]
      infer_instance
    exact integrable_const _
  | succ e =>
    obtain ⟨W, F, hW, hFW, hℓW, hWI⟩ := SliceMassFinite.exists_projClosure I ℓ hI hℓ hdim
    have hA2 : IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A := by
      rw [hWI]
      exact hA
    have hmass := hF n e h W F ℓ A (fun _ => 1) (fun _ => 1) (fun _ _ => 0) hW hFW hℓW hA2
      (fun _ _ _ => rfl) continuousOn_const (fun _ _ _ _ => rfl) (fun _ => contDiffOn_const)
    rw [hWI] at hmass
    simpa only [one_mul, add_zero] using hmass

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUniformiserBranchSimpleZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem UniformiserBranchSimpleZero.proof (hloc : UniformiserLocallyInjective.Statement)
    (hder : InjectiveHolomorphicDerivNeZero.Statement) : UniformiserBranchSimpleZero.Statement := by
  intro σ _ I w t r φ hI hic hdim ht hr hdiff hinj hmaps hw0
  have hball : ∀ {ρ : ℝ} {τ : ℂ}, τ ∈ Metric.ball (0 : ℂ) ρ →
      (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) ρ := by
    intro ρ τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hwZ : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I := hw0 ▸ hmaps (Metric.mem_ball_self hr)
  have htw : eval w t = 0 := by
    by_contra h
    exact ht.not_isUnit (isUnit_algebraMap_pointLocalRing I w t h)
  obtain ⟨U, hU, hUinj⟩ := hloc σ I w t hI hic hdim hwZ ht
  have hφc : ContinuousAt φ 0 :=
    (hdiff.differentiableAt (Metric.ball_mem_nhds 0 hr)).continuousAt
  have hc1 : Continuous fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ) := continuous_pi fun _ ↦ continuous_id
  have hcont : ContinuousAt (fun τ : ℂ ↦ φ fun _ ↦ τ) 0 :=
    ContinuousAt.comp_of_eq (g := φ) (f := fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) hφc hc1.continuousAt rfl
  have hpre : (fun τ : ℂ ↦ φ fun _ ↦ τ) ⁻¹' U ∈ 𝓝 (0 : ℂ) :=
    hcont.preimage_mem_nhds (by rw [← hw0] at hU; exact hU)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hpre (Metric.ball_mem_nhds 0 hr))
  have hfd : DifferentiableOn ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) (Metric.ball 0 ε) :=
    (differentiable_eval_pointLocal t).comp_differentiableOn (hdiff.comp
      (differentiable_pi.2 fun _ ↦ differentiable_id).differentiableOn fun τ hτ ↦ hball (hεU hτ).2)
  have hfi : Set.InjOn (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) (Metric.ball 0 ε) := by
    intro a ha b hb hab
    have hab' := hUinj ⟨hmaps (hball (hεU ha).2), (hεU ha).1⟩ ⟨hmaps (hball (hεU hb).2), (hεU hb).1⟩ hab
    exact congrFun (hinj (hball (hεU ha).2) (hball (hεU hb).2) hab') 0
  have hd := hder _ _ Metric.isOpen_ball hfd hfi 0 (Metric.mem_ball_self hε)
  have hf0 : (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 = 0 := by
    change eval (φ 0) t = 0
    rw [hw0, htw]
  exact (analyticAt_eval_disc hr hdiff t).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hf0 hd

end GroundTheory.Heights₂.Heights
end

