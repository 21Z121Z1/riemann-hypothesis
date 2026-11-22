import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0069
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0076
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0048

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchSheetAE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace BranchSheetAE

variable {d : ℕ}

theorem volume_preimage_null {G : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ} (hG : IsOpen G)
    (hF : DifferentiableOn ℂ F G) (hdet : ∀ w ∈ G, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0)
    {N : Set (Fin d → ℂ)} (hN : volume N = 0) :
    volume {t | t ∈ G ∧ F t ∈ N} = 0 := by
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hG hF
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    have hinj : Function.Injective (fderiv ℂ F w) :=
      (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hdet w hw)
    refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  apply measure_null_of_locally_null
  rintro x ⟨hxG, -⟩
  obtain ⟨e, he⟩ := hequiv x hxG
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hsymd : DifferentiableOn ℝ φ.symm (φ.target ∩ φ.symm ⁻¹' G) := by
    rintro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact (hd.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  refine ⟨{t | t ∈ G ∧ F t ∈ N} ∩ φ.source,
    inter_mem_nhdsWithin _ (φ.open_source.mem_nhds he.mem_toOpenPartialHomeomorph_source), ?_⟩
  refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := volume) (hsymd.mono Set.inter_subset_left) (measure_mono_null Set.inter_subset_right hN))
  rintro t ⟨⟨htG, htN⟩, hts⟩
  refine ⟨φ t, ⟨⟨φ.map_source hts, ?_⟩, ?_⟩, φ.left_inv hts⟩
  · show φ.symm (φ t) ∈ G
    rw [φ.left_inv hts]; exact htG
  · rw [hφ]; exact htN

end BranchSheetAE

theorem BranchSheetAE.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.Statement)
    (h₂ : ComplexSets.FibreBound.Statement) (h₃ : DiscriminantSheetCover.Statement) :
    BranchSheetAE.Statement := by
  intro n d J A p γ hJ hdim hA
  set Δ := Metric.ball (0 : Fin d → ℂ) γ.radius with hΔ
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτdef
  have hΔo : IsOpen Δ := Metric.isOpen_ball
  have hτd : DifferentiableOn ℂ τ Δ := SheetOnlyNull.differentiableOn_mulVec A γ.differentiableOn
  have hdeta := SheetOnlyNull.analyticOnNhd_det_jacC hΔo hτd
  have hne : ∃ z ∈ Δ, (ReciprocityTheory.AnForm.A.jacC τ z).det ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨y, hy⟩ := h₁ d d Δ τ hΔo ⟨0, Metric.mem_ball_self γ.radius_pos⟩ hτd fun v hv hinj =>
      (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
        (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall v hv)
    have hinf : (γ.toFun '' {t | t ∈ Δ ∧ τ t = y}).Infinite :=
      (Set.infinite_image_iff (γ.injOn.mono fun t ht => ht.1)).2 hy
    refine hinf ((h₂ n d J A hJ hdim hA y).2.1.subset ?_)
    rintro _ ⟨t, ⟨htΔ, hty⟩, rfl⟩
    exact ⟨γ.mapsTo htΔ, hty⟩
  have hZ := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd hΔo (convex_ball _ _).isPreconnected
    hdeta hne
  obtain ⟨P, U, D, N, s, -, hUD, -, -, hnull, hfib⟩ := h₃ n d J A hJ hdim hA
  set G := Δ ∩ (fun t => (ReciprocityTheory.AnForm.A.jacC τ t).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := hdeta.continuousOn.isOpen_inter_preimage hΔo isOpen_compl_singleton
  have hS := BranchSheetAE.volume_preimage_null hG (hτd.mono Set.inter_subset_left)
    (fun w hw => hw.2) hnull
  rw [ae_restrict_iff' hΔo.measurableSet, ae_iff]
  refine measure_mono_null ?_ (measure_union_null hZ hS)
  intro t ht
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at ht
  obtain ⟨htΔ, hno⟩ := ht
  by_cases hdt : (ReciprocityTheory.AnForm.A.jacC τ t).det = 0
  · exact Or.inl ⟨htΔ, hdt⟩
  refine Or.inr ⟨⟨htΔ, hdt⟩, fun hD => hno ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hD
  obtain ⟨hfibk, -, hsh⟩ := hfib k (τ t) ((hUD k).2.2.1 hk)
  have hmem : γ.toFun t ∈ fibre J A (τ t) := ⟨γ.mapsTo htΔ, rfl⟩
  rw [hfibk] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨s k j, hj ▸ hsh j⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchesToGoodPosition
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

theorem eval_linForm_eq_linEval {n : ℕ} (u x : Fin n → ℂ) :
    eval x (linForm u) = GroundTheory.Heights₂.Heights.linEval u x := by
  simp [linForm, GroundTheory.Heights₂.Heights.linEval]

theorem BranchesToGoodPosition.proof (hG : BranchesGoodPoint.Statement)
    (hC : PowerUnitCount.Statement) : BranchesToGoodPosition.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  obtain ⟨q, π, s, hqW, ⟨N₁, hN₁, hcov₁⟩, ⟨N₂, hN₂, hsl₂⟩, ⟨N₃, hN₃, hz₃⟩, hs, hder, hprop⟩ :=
    hG n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  have hJW : J ≤ W := le_trans le_sup_left hW.1.2
  have hWJ : ∀ x, x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
      x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J := fun x hx f hf => hx f (hJW hf)
  have huW : ∀ x, x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
      GroundTheory.Heights₂.Heights.linEval u x = 0 := fun x hx => by
    rw [← eval_linForm_eq_linEval]
    exact hx _ (hW.1.2 (le_sup_right (a := J) (Ideal.subset_span rfl)))
  choose H hHd hH0 hHeq using hord
  set F : Fin m → (Fin (d + 1) → ℂ) → Fin d → ℂ := fun b τ => π *ᵥ (γ b).toFun τ with hFdef
  have hFd : ∀ b, DifferentiableOn ℂ (F b) (Metric.ball 0 (γ b).radius) := fun b =>
    (Matrix.mulVecLin π).toContinuousLinearMap.differentiable.comp_differentiableOn
      (γ b).differentiableOn
  have hchart := fun b => hC d (ord b) (Metric.ball 0 (γ b).radius) (F b) (H b) (s b)
    Metric.isOpen_ball (hs b).1 (hs b).2.1 (hFd b) (hHd b) (hH0 b _ (hs b).1) (hder b)
  choose P₀ hP₀ hinj hcnt using hchart
  choose ε hε hεP using fun b => hprop b (P₀ b) (hP₀ b)

  obtain ⟨b₀, -⟩ : ∃ b, q ∈ (γ b).image := by
    simpa using hcov₁ ⟨hWJ q hqW, mem_of_mem_nhds hN₁⟩
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨b₀, Finset.mem_univ _⟩
  obtain ⟨δ₁, hδ₁, hδ₁N⟩ := Metric.mem_nhds_iff.1 (inter_mem hN₁ (inter_mem hN₂ hN₃))
  set ε₀ := Finset.univ.inf' hne ε with hε₀
  have hε₀pos : 0 < ε₀ := (Finset.lt_inf'_iff hne).2 fun b _ => hε b
  set δ := min δ₁ ε₀ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have h2δN : Metric.ball q (2 * δ) ⊆ N₁ ∩ (N₂ ∩ N₃) :=
    (Metric.ball_subset_ball (by rw [hδdef]; linarith [min_le_left δ₁ ε₀])).trans hδ₁N
  have h2δε : ∀ b, 2 * δ ≤ ε b := fun b => by
    rw [hδdef]; linarith [min_le_right δ₁ ε₀, Finset.inf'_le ε (Finset.mem_univ b)]

  have hpar : ∀ b, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q (2 * δ) →
      τ ∈ P₀ b := fun b τ hτ hx =>
    hεP b τ hτ (Metric.ball_subset_ball (h2δε b) hx)
  set U := Metric.ball q δ with hUdef
  have hUsub : U ⊆ Metric.ball q (2 * δ) := Metric.ball_subset_ball (by linarith)
  set P : Fin m → Set (Fin (d + 1) → ℂ) := fun b => Metric.ball 0 (γ b).radius ∩ (γ b).toFun ⁻¹' U
    with hPdef
  have hPo : ∀ b, IsOpen (P b) := fun b =>
    (γ b).differentiableOn.continuousOn.isOpen_inter_preimage Metric.isOpen_ball Metric.isOpen_ball
  have hPn : ∀ b, P b ∈ 𝓝 (s b) := fun b =>
    (hPo b).mem_nhds ⟨(hs b).1, by simp [U, (hs b).2.2, hδ]⟩
  have hPP₀ : ∀ b, P b ⊆ P₀ b := fun b τ hτ => hpar b τ hτ.1 (hUsub hτ.2)
  choose V ρ hVo hVm hρ hVsl hVc using fun b => hcnt b (P b) (hPn b) (hPP₀ b)

  have hslq : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W, x ∈ Metric.ball q (2 * δ) →
      ∃ τ ∈ Metric.ball 0 (γ b₀).radius, τ 0 = 0 ∧ (γ b₀).toFun τ = x ∧ τ ∈ P₀ b₀ := by
    intro x hx hxb
    obtain ⟨τ, ⟨hτ, hτ0⟩, rfl⟩ := hsl₂ b₀ ⟨hx, (h2δN hxb).2.1⟩
    exact ⟨τ, hτ, hτ0, rfl, hpar b₀ τ hτ hxb⟩
  refine ⟨q, π, U, ⋂ b, V b, Finset.univ.inf' hne ρ, ?_⟩
  refine
    { isOpen_U := Metric.isOpen_ball
      isBounded_U := Metric.isBounded_ball
      mem_U := Metric.mem_ball_self hδ
      mem_W := hqW
      isOpen_V := isOpen_iInter_of_finite hVo
      mem_V := Set.mem_iInter.2 fun b => by simpa [F, (hs b).2.2] using hVm b
      pos := (Finset.lt_inf'_iff hne).2 fun b _ => hρ b
      zeros := ?_
      injOn := ?_
      count := ?_ }
  · intro x hxU hxJ hux hxV
    have hx2 : x ∈ Metric.ball q (2 * δ) :=
      Metric.closedBall_subset_ball (by linarith) (Metric.closure_ball_subset_closedBall hxU)
    have hxW : x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W :=
      hz₃ x ⟨hxJ, (h2δN hx2).2.2⟩ hux
    obtain ⟨τ, hτ, hτ0, rfl, hτP₀⟩ := hslq _ hxW hx2
    exact ⟨(hVsl b₀ _ (Set.mem_iInter.1 hxV b₀) τ hτP₀ hτ0 rfl).2, hxW⟩
  · rintro x ⟨hxU, hxW⟩ x' ⟨hxU', hxW'⟩ hππ
    obtain ⟨τ, hτ, hτ0, rfl, hτP₀⟩ := hslq _ hxW (hUsub hxU)
    obtain ⟨τ', hτ', hτ0', rfl, hτP₀'⟩ := hslq _ hxW' (hUsub hxU')
    rw [hinj b₀ ⟨hτP₀, hτ0⟩ ⟨hτP₀', hτ0'⟩ hππ]
  · intro w hw t ht0 htρ
    have hwb : ∀ b, w ∈ V b := Set.mem_iInter.1 hw
    have htb : ∀ b, ‖t‖ < ρ b := fun b => lt_of_lt_of_le htρ (Finset.inf'_le ρ (Finset.mem_univ b))
    set T : Fin m → Set (Fin (d + 1) → ℂ) :=
      fun b => {τ | τ ∈ P b ∧ F b τ = w ∧ τ 0 ^ ord b * H b τ = t} with hTdef
    have hval : ∀ b, ∀ τ ∈ T b, GroundTheory.Heights₂.Heights.linEval u ((γ b).toFun τ) = t := by
      rintro b τ ⟨hτP, -, hτt⟩
      rw [← hτt]
      exact hHeq b τ hτP.1
    have hset : {x | x ∈ U ∩ zeroLocus J ∧ π *ᵥ x = w ∧ linVal u x = t} =
        ⋃ b, (γ b).toFun '' T b := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hxU, hxJ⟩, hπx, hux⟩
        obtain ⟨b, τ, hτ, rfl⟩ : ∃ b, x ∈ (γ b).image := by
          simpa using hcov₁ ⟨hxJ, (h2δN (hUsub hxU)).1⟩
        refine ⟨b, τ, ⟨⟨hτ, hxU⟩, hπx, ?_⟩, rfl⟩
        rw [← hHeq b τ hτ]
        exact hux
      · rintro ⟨b, τ, hτT, rfl⟩
        exact ⟨⟨hτT.1.2, (γ b).mapsTo hτT.1.1⟩, hτT.2.1, hval b τ hτT⟩
    have hdisjT : Pairwise (Function.onFun Disjoint fun b => (γ b).toFun '' T b) := by
      intro b c hbc
      refine Set.disjoint_left.2 ?_
      rintro x ⟨τ, hτT, rfl⟩ ⟨τ', hτT', hx⟩
      have h0 := hdisj b c hbc ⟨⟨τ, hτT.1.1, rfl⟩, ⟨τ', hτT'.1.1, hx⟩⟩
      have h1 := hval b τ hτT
      simp only [Set.mem_ofPred_eq] at h0
      rw [h0] at h1
      exact (norm_pos_iff.1 ht0) h1.symm
    rw [hset, Set.encard_iUnion_of_finite hdisjT, finsum_eq_sum_of_fintype, Nat.cast_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [((γ b).injOn.mono fun τ hτ => hτ.1.1).encard_image]
    exact hVc b w (hwb b) t ht0 (htb b)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartMassCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

open scoped ENNReal

noncomputable section

theorem ChartMassCompare.proof (h1 : SheetComass.Statement) (h2 : SheetAreaCompare.Statement) :
    ChartMassCompare.Statement := by
  intro n d J A φ R hJ hdim hA hφ
  obtain ⟨C, hC⟩ := h1 n d J A φ R hφ
  obtain ⟨c, hc, hca⟩ := h2 n d J A
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set B := Metric.closedBall (0 : Fin n → ℂ) R
  refine ⟨ENNReal.ofReal C' * c, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc, fun g hg => ?_⟩
  set gB := B.indicator g with hgBdef
  have hgB : Measurable gB := hg.indicator measurableSet_closedBall

  have hpt : ∀ y, chartAbsDens J A gB φ y ≤
      C' * sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y := by
    intro y
    have hfin := (ComplexSets.FibreBound.proof n d J A hJ hdim hA y).2.1
    unfold chartAbsDens sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    have hxf : x ∈ fibre J A y := hfin.mem_toFinset.mp hx
    split_ifs with hs
    · dsimp only
      rw [← hxf.2]
      by_cases hxB : x ∈ B
      · have hb := hC x ⟨hxf.1, hxB⟩ _ hs.choose_spec
        rw [abs_mul]
        calc |gB x| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ hs.choose) (A *ᵥ x)|
            ≤ |gB x| * (C' * sheetJac hs.choose (A *ᵥ x)) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
                (sheetJac_nonneg _ _))) (abs_nonneg _)
          _ = C' * (|gB x| * sheetJac hs.choose (A *ᵥ x)) := by ring
      · simp [gB, hxB]
    · simp
  have hnn : ∀ y, 0 ≤ chartAbsDens J A gB φ y := fun y =>
    finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs; exacts [abs_nonneg _, le_rfl]
  calc ∫⁻ y, ‖chartAbsDens J A gB φ y‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal C' * ‖sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y‖ₑ := by
        refine lintegral_mono fun y => ?_
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn y),
          ← ENNReal.ofReal_mul hC'0]
        exact ENNReal.ofReal_le_ofReal ((hpt y).trans
          (mul_le_mul_of_nonneg_left (le_abs_self _) hC'0))
    _ = ENNReal.ofReal C' * ∫⁻ y, ‖sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C' * (c * ∫⁻ z in zeroSetEuc J, ‖gB (WithLp.ofLp z)‖ₑ
          ∂(μH[((2 * d : ℕ) : ℝ)])) := by gcongr; exact hca gB hgB
    _ = ENNReal.ofReal C' * c * ∫⁻ z in zeroSetEuc J ∩ {z | WithLp.ofLp z ∈ B},
          ‖g (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        have hT : MeasurableSet {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B} :=
          measurableSet_closedBall.preimage (PiLp.continuous_ofLp 2 _).measurable
        have hfun : (fun z : EuclideanSpace ℂ (Fin n) => ‖gB (WithLp.ofLp z)‖ₑ) =
            {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B}.indicator
              (fun z => ‖g (WithLp.ofLp z)‖ₑ) := by
          ext z
          by_cases hz : WithLp.ofLp z ∈ B <;> simp [gB, hz, Set.indicator]
        rw [hfun, lintegral_indicator hT, Measure.restrict_restrict hT, Set.inter_comm, mul_assoc]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConePolar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology

noncomputable section

theorem anForm_maDens_eq_geo_maDensity {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.ChartRestriction.G.Geo.maDensity φ z :=
  rfl

theorem maDens_log_dualNorm_sheet {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) (A : Matrix (Fin e) (Fin n) ℂ) (y : Fin e → ℂ) (x : Fin n → ℂ)
    (s : (Fin e → ℂ) → Fin n → ℂ) (hx : x ∈ fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y)
    (hs : IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A x s) :
    ReciprocityTheory.AnForm.maDens (fun k => (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k ∘ s) y =
      (e.factorial : ℝ) / Real.pi ^ e * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y /
        h.dualNorm x ^ (2 * (e + 1)) := by
  obtain ⟨U, hU, hyU, hdiff, hsx, -, -⟩ := hs
  obtain ⟨hxZ, rfl⟩ := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h1 : eval (0 : Fin n → ℂ) (linForm ℓ - 1) = 0 :=
      hxZ _ (Ideal.mem_sup_right (Ideal.subset_span rfl))
    rw [map_sub, map_one, linForm, map_sum] at h1
    simp at h1
  have hdual : ∀ z, h.dualNorm z = ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ z)‖ := fun z => by
    simp [HermNorm.dualNorm, EuclideanSpace.norm_eq]
  have hv : ∀ᶠ y' in 𝓝 (A *ᵥ x), DifferentiableAt ℂ (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y' := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    have hs' := (hdiff y' hy').differentiableAt (hU.mem_nhds hy')
    exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h.matᵀ)⁻¹)).differentiableAt.comp y' hs'
  have hne : (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') (A *ᵥ x) ≠ 0 := by
    intro h0
    have hpos := HermNorm.dualNorm_pos h hx0
    rw [hdual, ← hsx, show (h.matᵀ)⁻¹ *ᵥ s (A *ᵥ x) = 0 from h0] at hpos
    simp at hpos
  have key := ChartGramMA.proof e n _ _ hv hne
  have hF : (fun k : Fin e => (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k ∘ s) =
      fun _ y' => Real.log ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s y')‖ := by
    funext k y'
    simp only [Function.comp_apply, hdual]
  rw [hF, anForm_maDens_eq_geo_maDensity, key, hsx, ← hdual]

theorem ConePolar.proof (h₁ : SliceDim.Statement) (h₂ : LinearNoetherNormalization.Statement)
    (h₃ : ConeChartGram.Statement) : ConePolar.Statement := by
  intro e
  refine ⟨1, fun n h J ℓ g hJ hdim hℓ hg hgc => ?_⟩
  have hex : ∃ A : Matrix (Fin e) (Fin n) ℂ, IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A :=
    h₂ n e _ (h₁ n e J ℓ hJ hdim hℓ)
  rw [one_mul, varInt, dif_pos hex, h₃ n e h J ℓ g hex.choose hJ hdim hℓ hg hgc hex.choose_spec,
    chartInt]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [chartDens, sheetSum]
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  split_ifs with hs
  · rw [maDens_log_dualNorm_sheet h J ℓ _ y x _ hx hs.choose_spec]
  · rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem abs_finsum_le_finsum_abs {α : Type*} (f : α → ℝ) : |∑ᶠ i, f i| ≤ ∑ᶠ i, |f i| := by
  by_cases h : (Function.support f).Finite
  · have hs : Function.support (fun i => |f i|) ⊆ ↑h.toFinset := by
      intro i hi
      simpa using hi
    rw [finsum_eq_sum_of_support_subset (s := h.toFinset) f (by rw [Set.Finite.coe_toFinset]),
      finsum_eq_sum_of_support_subset _ hs]
    exact Finset.abs_sum_le_sum_abs _ _
  · rw [finsum_of_infinite_support h, abs_zero]
    exact finsum_nonneg fun i => abs_nonneg _

variable {n d : ℕ}

theorem abs_chartDens_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    |chartDens J A f φ y| ≤ chartAbsDens J A f φ y := by
  classical
  refine (abs_finsum_le_finsum_abs _).trans (le_of_eq (finsum_congr fun x => ?_))
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp

theorem chartAbsDens_nonneg (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    0 ≤ chartAbsDens J A f φ y :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity

theorem CutOff.proof (hS : CutOffShape.Statement) (hT : CutOffTube.Statement)
    (hG : CutOffGradient.Statement) : CutOff.Statement := by
  obtain ⟨K, hK⟩ := hG
  intro n d J A P hJ hdim hA hP
  have hA' : ContDiff ℝ ∞ fun x : Fin n → ℂ => A *ᵥ x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff.restrict_scalars ℝ
  have hc : Continuous fun x : Fin n → ℂ => ‖eval (A *ᵥ x) P‖ ^ 2 :=
    ((MvPolynomial.continuous_eval P).comp hA'.continuous).norm.pow 2
  have key : ∀ T : (Fin (d + 1) → ℂ) → ℝ, Integrable T → ∀ (k : ℕ) (F : (Fin (d + 1) → ℂ) → ℝ),
      (∀ y, ‖F y‖ ≤ K / ((k : ℝ) + 1) * T y) → ‖∫ y, F y‖ ≤ K / ((k : ℝ) + 1) * ∫ y, T y :=
    fun T hTi k F hF => (norm_integral_le_of_norm_le (hTi.const_mul _)
      (Eventually.of_forall hF)).trans_eq (integral_const_mul _ _)
  have lim : ∀ c : ℝ, Tendsto (fun k : ℕ => K / ((k : ℝ) + 1) * c) atTop (𝓝 0) := fun c => by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul K).mul_const c
    rw [mul_zero, zero_mul] at h
    exact h.congr fun k => by ring
  refine ⟨logLogCutAlong A P, fun k => ((hS _ P).1 k).1.comp hA', fun k x => ((hS _ P).1 k).2.1 _,
    fun k => ⟨{x | ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k}, isOpen_lt hc continuous_const, fun x hx => ?_,
      fun x hx => ((hS _ P).1 k).2.2 _ hx.1⟩, fun x _ hx => (hS _ P).2 _ hx, fun R => ?_,
    fun R φ hφ => ?_⟩
  · have hx0 : eval (A *ᵥ x) P = 0 := hx
    show ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k
    rw [hx0, norm_zero, zero_pow two_ne_zero]
    exact (cutLevel_mem k).1
  · have hTi := hT n d J A P R (fun _ => euclPot) hJ hdim hA hP
      fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
    have hl := (lim (∫ y, tubeDens J A P R (fun _ => euclPot) y)).const_mul 2
    rw [mul_zero] at hl
    refine squeeze_zero_norm (fun k => ?_) hl
    have h := hK n d J A P R (fun _ => euclPot) k
    refine (norm_sub_le _ _).trans ?_
    rw [two_mul]
    exact add_le_add (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.1)
      (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.2)
  · refine squeeze_zero_norm (fun k => key _ (hT n d J A P R φ hJ hdim hA hP hφ) k _ fun y => ?_)
      (lim _)
    rw [Real.norm_of_nonneg (chartAbsDens_nonneg _ _ _ _ y)]
    exact (hK n d J A P R φ k y hJ hdim hA).1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermWeierstrassDivision
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem WeierstrassDivision.proof (hP : WeierstrassPreparation.Statement)
    (hD : WeierstrassPolynomialDivision.Statement) : WeierstrassDivision.Statement := by
  intro σ _ d f g hf hg hord
  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hP σ d f hf hord
  obtain ⟨q, a, hq, ha, hgq⟩ := hD σ d c g hc hc0 hg
  refine ⟨fun x => q x / e x, a, hq.div he he0, ha, ?_⟩
  filter_upwards [hfe, hgq, he.continuousAt.eventually_ne he0] with x hfx hgx hex
  rw [hgx, hfx, div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ hex]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

