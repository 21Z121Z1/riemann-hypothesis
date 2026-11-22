import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0069
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0112
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalOpenMapping
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0014

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PRatSheetCover
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

namespace RatSheetCover

variable {n d : ℕ}

theorem differentiable_eval_poly (g : MvPolynomial (Fin n) ℂ) : Differentiable ℂ (fun x => eval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact differentiable_const a
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (differentiable_apply i)

theorem differentiableAt_ratMap (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : eval x q ≠ 0) : DifferentiableAt ℂ (RatChart.ratMap p q) x := by
  show DifferentiableAt ℂ (fun z => fun r => eval z (p r) / eval z q) x
  refine differentiableAt_pi.2 fun r => ?_
  show DifferentiableAt ℂ (fun z => eval z (p r) / eval z q) x
  simp only [div_eq_mul_inv]
  exact (differentiable_eval_poly (p r) x).mul ((differentiable_eval_poly q x).inv hx)

theorem volume_eq_zero_of_hausdorff {S : Set (Fin d → ℂ)} (h : μH[((2 * d : ℕ) : ℝ)] S = 0) :
    volume S = 0 := by
  rw [← SheetOnlyNull.finrank_real_fin_complex] at h
  exact Measure.absolutelyContinuous_isAddHaarMeasure _ _ h

theorem exists_ratSheet {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ}
    {σ : (Fin d → ℂ) → Fin n → ℂ} (hσ : IsSheetAt J A x σ) (hq : eval x q ≠ 0)
    (hinj : Function.Injective (fderiv ℂ (fun t => RatChart.ratMap p q (σ t)) (A *ᵥ x))) :
    ∃ s, RatChart.IsRatSheetAt J p q x s := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hσ
  set F : (Fin d → ℂ) → Fin d → ℂ := fun t => RatChart.ratMap p q (σ t) with hFdef
  set W : Set (Fin d → ℂ) := U ∩ σ ⁻¹' {z | eval z q ≠ 0} with hWdef
  have hW : IsOpen W := hsd.continuousOn.isOpen_inter_preimage hU
    (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const)
  have hFd : DifferentiableOn ℂ F W := fun t ht =>
    ((differentiableAt_ratMap p q ht.2).comp t
      (hsd.differentiableAt (hU.mem_nhds ht.1))).differentiableWithinAt
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hW hFd
  have hxW : A *ᵥ x ∈ W := ⟨hyU, by simp only [Set.mem_preimage, Set.mem_ofPred_eq, hsx]; exact hq⟩
  set G : Set (Fin d → ℂ) := W ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := (SheetOnlyNull.analyticOnNhd_det_jacC hW hFd).continuousOn
    |>.isOpen_inter_preimage hW isOpen_compl_singleton
  have hdet : (ReciprocityTheory.AnForm.A.jacC F (A *ᵥ x)).det ≠ 0 := by
    rw [ReciprocityTheory.AnForm.A.det_jacC]
    exact (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
  have hinj' : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj' w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hxW, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : A *ᵥ x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (A *ᵥ x) = RatChart.ratMap p q x := by simp only [hFdef, hsx]
  have hsym : φ.symm (RatChart.ratMap p q x) = A *ᵥ x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  refine ⟨σ ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hxW, hdet⟩⟩,
    ?_, by simp only [Function.comp_apply, hsym, hsx], fun z hz => ⟨(hsec _ hz.2.1.1).2, hz.2.1.2, ?_⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hsd.differentiableAt (hU.mem_nhds hzG.1.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · refine ⟨V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ U), inter_mem hV
      (((φ.open_source.inter hU).preimage (by fun_prop)).mem_nhds ⟨hysrc, hyU⟩), ?_⟩
    rintro x'' ⟨hx''Z, hx''V, hx''src, hx''U⟩ - -
    have hx'' : x'' = σ (A *ᵥ x'') := hVs x'' ⟨hx''Z, hx''V⟩ hx''U
    have hR : RatChart.ratMap p q x'' = φ (A *ᵥ x'') := by
      rw [hφ, hFdef]; exact congrArg _ hx''
    rw [Function.comp_apply, hR, φ.left_inv hx''src]
    exact hx''

end RatSheetCover

theorem RatSheetCover.proof (h₁ : RatFibreAvoid.Statement) : RatSheetCover.Statement := by
  intro n d J p q hJ hdim
  obtain ⟨A, hA⟩ := IndefiniteRowSideFullHecke.ComplexSets.exists_isFiniteProjection J hJ hdim
  obtain ⟨P, U, D, N, s, hP, hUD, -, hcov, -, hfib⟩ :=
    DiscriminantSheetCover.proof ComplexSets.DiscriminantCover.full n d J A hJ hdim hA
  have hf : pullback A P ∉ J := fun h => hP (hA.injective (a₁ := P) (a₂ := 0) (by
    simp only [map_zero, projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h))
  have hav := h₁ n d J p q (pullback A P) hJ hdim hf
  set Crit : Set (Fin d → ℂ) := ⋃ k, ⋃ j : Fin (N k),
    (fun t => RatChart.ratMap p q (s k j t)) ''
      {t | t ∈ U k ∩ s k j ⁻¹' {z | eval z q ≠ 0} ∧
        ¬ Function.Injective (fderiv ℂ (fun t => RatChart.ratMap p q (s k j t)) t)} with hCritdef
  have hCrit : volume Crit = 0 := by
    refine measure_iUnion_null fun k => measure_iUnion_null fun j => ?_
    have hW : IsOpen (U k ∩ s k j ⁻¹' {z | eval z q ≠ 0}) :=
      ((hUD k).2.2.2 j).continuousOn.isOpen_inter_preimage (hUD k).1
        (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const)
    have hFd : DifferentiableOn ℂ (fun t => RatChart.ratMap p q (s k j t))
        (U k ∩ s k j ⁻¹' {z | eval z q ≠ 0}) := fun t ht =>
      ((RatSheetCover.differentiableAt_ratMap p q ht.2).comp t
        (((hUD k).2.2.2 j).differentiableAt ((hUD k).1.mem_nhds ht.1))).differentiableWithinAt
    exact RatSheetCover.volume_eq_zero_of_hausdorff
      (IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.full d d _ _ hW hFd)
  filter_upwards [hav, compl_mem_ae_iff.2 hCrit] with y hy hyC x hx
  obtain ⟨hxZ, hxq, hxy⟩ := hx
  have hPx : eval (A *ᵥ x) P ≠ 0 := by
    rw [← IndefiniteRowSideFullHecke.ComplexSets.eval_pullback_eq]; exact hy x ⟨hxZ, hxq, hxy⟩
  have hmem : A *ᵥ x ∈ ⋃ k, D k := by
    by_contra h
    exact hPx (hcov h)
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hmem
  have hAU : A *ᵥ x ∈ U k := (hUD k).2.2.1 hk
  obtain ⟨hrange, -, hsh⟩ := hfib k _ hAU
  have hxf : x ∈ fibre J A (A *ᵥ x) := ⟨hxZ, rfl⟩
  rw [hrange] at hxf
  obtain ⟨j, hj⟩ := hxf
  have hσ : IsSheetAt J A x (s k j) := by
    have := hsh j
    simp only at hj
    rwa [hj] at this
  refine RatSheetCover.exists_ratSheet hσ hxq ?_
  by_contra hni
  refine hyC (Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨j, A *ᵥ x, ⟨⟨hAU, ?_⟩, hni⟩, ?_⟩⟩)
  · simp only [Set.mem_preimage, Set.mem_ofPred_eq, hj]; exact hxq
  · simp only [hj, hxy]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PRatSheetNoChartNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace RatSheetNoChartNull

variable {n d : ℕ}

theorem continuousOn_ratMap (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    ContinuousOn (RatChart.ratMap p q) {x | eval x q ≠ 0} :=
  continuousOn_pi.2 fun r =>
    (MvPolynomial.continuous_eval (p r)).continuousOn.div (MvPolynomial.continuous_eval q).continuousOn
      fun _ hx => hx

theorem isOpen_ratPreimage (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    {S : Set (Fin d → ℂ)} (hS : IsOpen S) :
    IsOpen ({x | eval x q ≠ 0} ∩ RatChart.ratMap p q ⁻¹' S) :=
  (continuousOn_ratMap p q).isOpen_inter_preimage
    (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const) hS

theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ DifferentiableOn ℂ s U ∧
      (∀ x' ∈ zeroSet J ∩ W, RatChart.ratMap p q x' ∈ U ∧ RatChart.IsRatSheetAt J p q x' s) ∧
      ((∃ s, RatChart.IsRatSheetAt J p q x s) → x ∈ W) := by
  by_cases hx : ∃ s, RatChart.IsRatSheetAt J p q x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hqx : eval x q ≠ 0 := hsx ▸ (hsec _ hxU).2.1
    refine ⟨s, U, interior V ∩ ({x | eval x q ≠ 0} ∩ RatChart.ratMap p q ⁻¹' U), hU,
      isOpen_interior.inter (isOpen_ratPreimage p q hU), hsd, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hqx, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'q, hx'U⟩
    have hx's : s (RatChart.ratMap p q x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'q hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hq'' hR'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hq'' hR''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, differentiableOn_empty,
      by simp, fun h => absurd h hx⟩

theorem exists_sheet_of_det_ne_zero {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : RatChart.IsRatSheetAt J p q x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A *ᵥ s w) (RatChart.ratMap p q x)).det ≠ 0) :
    ∃ s', IsSheetAt J A x s' := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set R := RatChart.ratMap p q with hRdef
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A *ᵥ s w with hFdef
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hU (SheetOnlyNull.differentiableOn_mulVec A hsd)
  set G : Set (Fin d → ℂ) := U ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G :=
    (SheetOnlyNull.analyticOnNhd_det_jacC hU (SheetOnlyNull.differentiableOn_mulVec A hsd)).continuousOn
      |>.isOpen_inter_preimage hU isOpen_compl_singleton
  have hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hyU, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : R x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (R x) = A *ᵥ x := by simp only [hFdef, hsx]
  have hsym : φ.symm (A *ᵥ x) = R x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  have hqx : eval x q ≠ 0 := hsx ▸ (hsec _ hyU).2.1
  refine ⟨s ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyU, hdet⟩⟩,
    ?_, by simp only [Function.comp_apply, hsym, hsx], fun z hz => ⟨?_, (hsec _ hz.2.1).1⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hsd.differentiableAt (hU.mem_nhds hzG.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · refine ⟨V ∩ ({x | eval x q ≠ 0} ∩ R ⁻¹' (φ.source ∩ U)), inter_mem hV
      ((isOpen_ratPreimage p q (φ.open_source.inter hU)).mem_nhds ⟨hqx, hysrc, hyU⟩), ?_⟩
    rintro x'' ⟨hx''Z, hx''V, hx''q, hx''src, hx''U⟩ -
    have hx'' : x'' = s (R x'') := hVs x'' ⟨hx''Z, hx''V⟩ hx''q hx''U
    have hA : A *ᵥ x'' = φ (R x'') := by rw [hφ, hFdef]; exact congrArg _ hx''
    rw [Function.comp_apply, hA, φ.left_inv hx''src]
    exact hx''

theorem exists_det_ne_zero (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ} {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : J.IsPrime) (hA : IsFiniteProjection J A)
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : RatChart.IsRatSheetAt J p q x s)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : RatChart.ratMap p q x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A *ᵥ s w) w).det ≠ 0 := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set R := RatChart.ratMap p q with hRdef
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A *ᵥ s w with hFdef
  by_contra hall
  push Not at hall
  have hcrit : F '' (W₀ ∩ U) ⊆ F '' {w | w ∈ U ∧ ¬ Function.Injective (fderiv ℂ F w)} :=
    Set.image_mono fun w hw => ⟨hw.2, fun hinj => (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩
  have hnull := measure_mono_null hcrit (h₂ d d U F hU (SheetOnlyNull.differentiableOn_mulVec A hsd))
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).1
  have hqx : eval x q ≠ 0 := hsx ▸ (hsec _ hyU).2.1
  have hnhds := h₁ n d J (linPoly A) hJ hA.injective hA.finite x hxZ
    (V ∩ ({x | eval x q ≠ 0} ∩ R ⁻¹' (W₀ ∩ U)))
    (inter_mem hV ((isOpen_ratPreimage p q (hW₀.inter hU)).mem_nhds ⟨hqx, hxW₀, hyU⟩))
  have hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A i)) = A *ᵥ z := fun z => by
    ext i
    simp [linPoly, Matrix.mulVec, dotProduct]
  simp only [hev] at hnhds
  have hsub : (fun z => A *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J ∩
      (V ∩ ({x | eval x q ≠ 0} ∩ R ⁻¹' (W₀ ∩ U)))) ⊆ F '' (W₀ ∩ U) := by
    rintro _ ⟨z, ⟨hzZ, hzV, hzq, hzW⟩, rfl⟩
    refine ⟨R z, hzW, ?_⟩
    simp only [hFdef]
    rw [← hVs z ⟨hzZ, hzV⟩ hzq hzW.2]
  have hpos := Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)])
    (Filter.mem_of_superset hnhds hsub)
  rw [SheetOnlyNull.finrank_real_fin_complex] at hpos
  exact hpos.ne' hnull

end RatSheetNoChartNull

theorem RatSheetNoChartNull.proof : RatSheetNoChartNull.Statement := by
  intro n d J A p q hJ _ hA _
  set B := {x | x ∈ zeroSet J ∧ (∃ s, RatChart.IsRatSheetAt J p q x s) ∧ ¬ ∃ s', IsSheetAt J A x s'}
    with hBdef
  choose σ U W hU hW hσd hWsh hxW using
    fun x : Fin n → ℂ => RatSheetNoChartNull.exists_sheet_nhds (J := J) (p := p) (q := q) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume (RatChart.ratMap p q '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨hRx, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU i) _ hRx
    refine ⟨Metric.ball (RatChart.ratMap p q x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A *ᵥ σ i v) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC (hU i)
        (SheetOnlyNull.differentiableOn_mulVec A (hσd i))).mono hball,
      RatSheetNoChartNull.exists_det_ne_zero IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof
        IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof hJ hA hsh Metric.isOpen_ball (Metric.mem_ball_self hr),
      ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2 (RatSheetNoChartNull.exists_sheet_of_det_ne_zero (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
  rintro _ ⟨x, hxB, rfl⟩
  have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
  obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
  exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights
end

