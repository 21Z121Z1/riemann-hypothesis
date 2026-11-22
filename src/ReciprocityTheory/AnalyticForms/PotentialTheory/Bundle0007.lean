import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0002
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeSheets
section
namespace ReciprocityTheory.AnForm.M

open FinHolAtlas Topology

noncomputable section

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isClosed_of_isAnalyticSubset' (A : FinHolAtlas e X) {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  unfold FinHolAtlas.IsAnalyticSubset at hS
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  have hne : ∃ i, f i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have hxSW : x ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hxW, hcon⟩
    exact hxSW.1
  obtain ⟨i, hi⟩ := hne
  have hca : ContinuousAt (f i) x := by
    obtain ⟨j, hxj⟩ := A.cover x
    have h : ∀ k, AnalyticOnNhd ℂ ((f i) ∘ (A.chart k).symm)
        ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W) := hf i
    have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
      refine ⟨(A.chart j).map_source hxj, ?_⟩
      show (A.chart j).symm ((A.chart j) x) ∈ W
      rw [(A.chart j).left_inv hxj]
      exact hxW
    have h1 : ContinuousAt ((f i ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
      ((h j _ hmem).continuousAt).comp ((A.chart j).continuousAt hxj)
    refine h1.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hxj] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy]
  filter_upwards [hW.mem_nhds hxW, hca.eventually_ne hi] with y hyW hyi hyS
  have hy : y ∈ S ∩ W := ⟨hyS, hyW⟩
  rw [hSW] at hy
  exact hyi (hy.2 i)

theorem exists_localHomeomorph_of_isDegreeOff {A : FinHolAtlas e X} {B : FinHolAtlas e Y}
    {h : Y → X} (hh : HoloMap B A h) {d : ℕ} {S : Set X} (hd : IsDegreeOff A B h d S) (y : Y)
    (hy : h y ∉ S) :
    ∃ E : OpenPartialHomeomorph Y X, y ∈ E.source ∧ Set.EqOn h E E.source ∧
      ∃ j : Fin B.n, E.source ⊆ (B.chart j).source := by
  obtain ⟨j, hyj⟩ := B.cover y
  obtain ⟨k, hk⟩ := A.cover (h y)
  have hb : (B.chart j) y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) := by
    refine ⟨(B.chart j).map_source hyj, ?_⟩
    show h ((B.chart j).symm ((B.chart j) y)) ∈ (A.chart k).source
    rw [(B.chart j).left_inv hyj]
    exact hk
  have han := hh.2 j k ((B.chart j) y) hb
  have hdet := hd.2.2.2.2.2 j k ((B.chart j) y) ((B.chart j).map_source hyj)
    (by rw [(B.chart j).left_inv hyj]; exact hy) (by rw [(B.chart j).left_inv hyj]; exact hk)
  set L := (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv with hL
  have hstrict : HasStrictFDerivAt ((A.chart k) ∘ h ∘ (B.chart j).symm)
      (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) ((B.chart j) y) :=
    han.hasStrictFDerivAt.congr_fderiv (by ext v; rfl)
  set Φ := hstrict.toOpenPartialHomeomorph ((A.chart k) ∘ h ∘ (B.chart j).symm) with hΦ
  have hcoe : (Φ : (Fin e → ℂ) → (Fin e → ℂ)) = (A.chart k) ∘ h ∘ (B.chart j).symm :=
    hstrict.toOpenPartialHomeomorph_coe
  have hsrc : (B.chart j) y ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hU : IsOpen (h ⁻¹' (A.chart k).source) := (A.chart k).open_source.preimage hh.1
  refine ⟨(((B.chart j).trans Φ).trans (A.chart k).symm).restrOpen _ hU, ?_, ?_, j, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source]
    refine ⟨⟨⟨hyj, hsrc⟩, ?_⟩, hk⟩
    show Φ ((B.chart j) y) ∈ (A.chart k).target
    rw [hcoe]
    show (A.chart k) (h ((B.chart j).symm ((B.chart j) y))) ∈ (A.chart k).target
    rw [(B.chart j).left_inv hyj]
    exact (A.chart k).map_source hk
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    obtain ⟨⟨⟨hy1, -⟩, -⟩, hy4⟩ := hy'
    show h y' = (A.chart k).symm (Φ ((B.chart j) y'))
    rw [hcoe]
    show h y' = (A.chart k).symm ((A.chart k) (h ((B.chart j).symm ((B.chart j) y'))))
    rw [(B.chart j).left_inv hy1, (A.chart k).left_inv hy4]
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    exact hy'.1.1.1

theorem degree_local_sheets' [CompactSpace Y] [T2Space Y] [T2Space X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    {S : Set X} (hd : IsDegreeOff A B h d S) (x : X) (hx : x ∉ S) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Disjoint V S ∧ ∃ k : Fin A.n, V ⊆ (A.chart k).source ∧
      ∃ W : Fin d → Set Y, (∀ i, IsOpen (W i)) ∧ Pairwise (Function.onFun Disjoint W) ∧
        h ⁻¹' V = ⋃ i, W i ∧ ∀ i, Set.BijOn h (W i) V ∧
          ∃ j : Fin B.n, W i ⊆ (B.chart j).source := by
  classical
  have hSc : IsClosed S := isClosed_of_isAnalyticSubset' A hd.1
  have hloc : ∀ y : (h ⁻¹' {x} : Set Y), ∃ E : OpenPartialHomeomorph Y X, y.1 ∈ E.source ∧
      Set.EqOn h E E.source ∧ ∃ j : Fin B.n, E.source ⊆ (B.chart j).source := fun y =>
    exists_localHomeomorph_of_isDegreeOff hh hd y.1
      (by rw [show h y.1 = x from y.2]; exact hx)
  choose E hEy hEeq jE hjE using hloc
  have hFc : IsCompact (h ⁻¹' {x}) := (isClosed_singleton.preimage hh.1).isCompact
  have hFfin : (h ⁻¹' {x}).Finite := by
    obtain ⟨t, ht⟩ := hFc.elim_finite_subcover (fun y => (E y).source)
      (fun y => (E y).open_source) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hEy ⟨y, hy⟩⟩)
    refine (t.finite_toSet.image Subtype.val).subset ?_
    intro z hz
    obtain ⟨w, hwt, hzw⟩ := Set.mem_iUnion₂.1 (ht hz)
    have hzx : h z = x := hz
    have hwx : h w.1 = x := w.2
    have h1 : E w w.1 = E w z := by
      rw [← hEeq w hzw, ← hEeq w (hEy w), hzx, hwx]
    exact ⟨w, hwt, (E w).injOn (hEy w) hzw h1⟩
  have : Finite (h ⁻¹' {x}) := hFfin.to_subtype
  have hcard : Nat.card (h ⁻¹' {x}) = d := by
    rw [Nat.card_coe_set_eq]; exact hd.2.2.2.2.1 x hx
  let en : Fin d ≃ (h ⁻¹' {x} : Set Y) := ((Finite.equivFin _).trans (finCongr hcard)).symm
  obtain ⟨U0, hU0, hU0d⟩ := hFfin.t2_separation
  let U : Fin d → Set Y := fun i => U0 (en i).1 ∩ (E (en i)).source
  have hUo : ∀ i, IsOpen (U i) := fun i => (hU0 _).2.inter (E _).open_source
  have hyU : ∀ i, (en i).1 ∈ U i := fun i => ⟨(hU0 _).1, hEy _⟩
  have hUd : Pairwise (Function.onFun Disjoint U) := by
    intro i i' hii'
    have hne : (en i).1 ≠ (en i').1 := fun h' => hii' (en.injective (Subtype.ext h'))
    exact (hU0d (en i).2 (en i').2 hne).mono Set.inter_subset_left Set.inter_subset_left
  have hhU : ∀ i, h '' U i = E (en i) '' U i := fun i =>
    ((hEeq (en i)).mono Set.inter_subset_right).image_eq
  have hhUo : ∀ i, IsOpen (h '' U i) := fun i => by
    rw [hhU]; exact (E _).isOpen_image_of_subset_source (hUo i) Set.inter_subset_right
  have hKc : IsCompact (⋃ i, U i)ᶜ := (isOpen_iUnion hUo).isClosed_compl.isCompact
  have hK : IsClosed (h '' (⋃ i, U i)ᶜ) := (hKc.image hh.1).isClosed
  have hxK : x ∉ h '' (⋃ i, U i)ᶜ := by
    rintro ⟨z, hzK, hzx⟩
    apply hzK
    have hz : z ∈ h ⁻¹' {x} := hzx
    refine Set.mem_iUnion.2 ⟨en.symm ⟨z, hz⟩, ?_⟩
    have := hyU (en.symm ⟨z, hz⟩)
    simpa using this
  obtain ⟨k, hk⟩ := A.cover x
  let V : Set X := (⋂ i, h '' U i) ∩ (A.chart k).source ∩ (h '' (⋃ i, U i)ᶜ)ᶜ ∩ Sᶜ
  have hVo : IsOpen V :=
    (((isOpen_iInter_of_finite hhUo).inter (A.chart k).open_source).inter
      hK.isOpen_compl).inter hSc.isOpen_compl
  have hVU : ∀ i, V ⊆ h '' U i := fun i z hz => Set.mem_iInter.1 hz.1.1.1 i
  refine ⟨V, hVo, ⟨⟨⟨Set.mem_iInter.2 fun i => ⟨(en i).1, hyU i, (en i).2⟩, hk⟩, hxK⟩, hx⟩,
    Set.disjoint_left.2 fun z hz hzS => hz.2 hzS, k, fun z hz => hz.1.1.2, ?_⟩
  refine ⟨fun i => U i ∩ h ⁻¹' V, fun i => (hUo i).inter (hVo.preimage hh.1), ?_, ?_, ?_⟩
  · intro i i' hii'
    exact (hUd hii').mono Set.inter_subset_left Set.inter_subset_left
  · ext z
    constructor
    · intro hz
      have hzU : z ∈ ⋃ i, U i := by
        by_contra hc
        exact hz.1.2 ⟨z, hc, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hzU
      exact Set.mem_iUnion.2 ⟨i, hi, hz⟩
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
      exact hi.2
  · intro i
    refine ⟨⟨fun z hz => hz.2, ?_, ?_⟩, jE (en i), fun z hz => hjE _ hz.1.2⟩
    · intro a ha b hb hab
      apply (E (en i)).injOn ha.1.2 hb.1.2
      rw [← hEeq (en i) ha.1.2, ← hEeq (en i) hb.1.2]
      exact hab
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := hVU i hv
      exact ⟨u, ⟨hu, hv⟩, rfl⟩

end

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def LogNormSecLocalStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (x : X) (y : X), IsSection A L s → y ∈ L.U x → s x y ≠ 0 →
      logNormSec L s y = Real.log ‖s x y‖ - L.φ x y

theorem logNormSecLocal : LogNormSecLocalStatement := by
  intro e X _ A L s x y hS hy hs
  unfold logNormSec
  rw [hS.2 y x y ⟨L.mem_U y, hy⟩, Real.log_mul (norm_ne_zero_iff.mpr hs) (Real.exp_pos _).ne',
    Real.log_exp]
  ring

theorem logNormSec_eq_indicator {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} (hS : IsSection A L s) {x p : X} (hp : p ∈ L.U x) :
    logNormSec L s p = Real.log ‖s x p‖ - L.φ x p + {q | s x q = 0}.indicator (L.φ x) p := by
  by_cases h0 : s x p = 0
  · unfold logNormSec
    rw [hS.2 p x p ⟨L.mem_U p, hp⟩, Set.indicator_apply,
      if_pos (show p ∈ {q | s x q = 0} from h0), h0]
    simp
  · rw [Set.indicator_apply, if_neg (show p ∉ {q | s x q = 0} from h0),
      logNormSecLocal A L s x p hS hp h0]
    ring

theorem prod_option_eq_prod_zpow {e r : ℕ} (σ : Fin r → Option (Fin e)) (m : Fin r → ℕ)
    (w : Fin e → ℂ) (g : Fin r → ℂ) (hg : ∀ k, g k = ∏ i, if σ k = some i then w i ^ m k else 1) :
    ∏ k, g k = ∏ i, w i ^ (((∑ k ∈ Finset.univ.filter (fun k => σ k = some i), m k : ℕ)) : ℤ) := by
  simp_rw [hg]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, zpow_natCast]

theorem logNormIntegrable_of (hLU : ReciprocityTheory.AnForm.A.LogUnitMonoLocIntStatement)
    (hD : LocDensContStatement) : LogNormIntegrableStatement := by
  intro e X _ _ _ A L s r m W hL hS hSNC Φ hΦ j K hKt hK
  refine LocallyIntegrableOn.integrableOn_isCompact (fun y0 hy0 => ?_) hK
  set c := A.chart j with hc
  have hy0t : y0 ∈ c.target := hKt hy0
  obtain ⟨ψ, hψc, hx0ψ, hψU, σ, -, -, u, hu, hu0, hsu⟩ := hSNC (c.symm y0)
  set x0 := c.symm y0 with hx0
  have hNo : IsOpen (c.target ∩ c.symm ⁻¹' ψ.source) := c.isOpen_inter_preimage_symm ψ.open_source
  have hy0N : y0 ∈ c.target ∩ c.symm ⁻¹' ψ.source := ⟨hy0t, hx0ψ⟩
  obtain ⟨ε, hε, hεN⟩ := Metric.isOpen_iff.mp hNo y0 hy0N
  set B := Metric.closedBall y0 (ε / 2) with hB
  have hBN : B ⊆ c.target ∩ c.symm ⁻¹' ψ.source :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεN
  have hBc : IsCompact B := isCompact_closedBall y0 (ε / 2)
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y0 (by linarith)), ?_⟩

  set V := ψ.target ∩ ψ.symm ⁻¹' c.source with hV
  have hVo : IsOpen V := ψ.isOpen_inter_preimage_symm c.open_source
  have hTinvA : AnalyticOnNhd ℂ (c ∘ ψ.symm) V := (hψc j).2
  have hTV : ∀ y ∈ c.target ∩ c.symm ⁻¹' ψ.source,
      ψ (c.symm y) ∈ V ∧ c (ψ.symm (ψ (c.symm y))) = y := by
    intro y hy
    refine ⟨⟨ψ.map_source hy.2, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, ψ.left_inv hy.2]
      exact c.map_target hy.1
    · rw [ψ.left_inv hy.2, c.right_inv hy.1]

  set m' : Fin e → ℤ :=
    fun i => ((∑ k ∈ Finset.univ.filter (fun k => σ k = some i), m k : ℕ) : ℤ) with hm'
  set G : (Fin e → ℂ) → ℝ := fun z => Real.log ‖u (ψ.symm z) * ∏ i, z i ^ m' i‖ with hG
  have hGloc : LocallyIntegrableOn G V := by
    refine hLU e m' V (fun z => u (ψ.symm z)) hVo ?_ (fun z hz => hu0 _ (ψ.map_target hz.1))
    intro z hz
    have hw : c (ψ.symm z) ∈ c.target ∩ c.symm ⁻¹' ψ.source := by
      refine ⟨c.map_source hz.2, ?_⟩
      simp only [Set.mem_preimage, c.left_inv hz.2]
      exact ψ.map_target hz.1
    have h1 : AnalyticAt ℂ ((u ∘ c.symm) ∘ (c ∘ ψ.symm)) z :=
      AnalyticAt.comp (g := u ∘ c.symm) (f := c ∘ ψ.symm) (hu j _ hw) (hTinvA z hz)
    refine (h1.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hVo.mem_nhds hz] with w hw
    simp [Function.comp, c.left_inv hw.2]

  have hTc : ContinuousOn (fun y => ψ (c.symm y)) (c.target ∩ c.symm ⁻¹' ψ.source) :=
    ψ.continuousOn.comp (c.continuousOn_symm.mono Set.inter_subset_left) (fun y hy => hy.2)
  set C := (fun y => ψ (c.symm y)) '' B with hC
  have hCc : IsCompact C := hBc.image_of_continuousOn (hTc.mono hBN)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hCV : C ⊆ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hTV y (hBN hy)).1
  have hCB : (c ∘ ψ.symm) '' C = B := by
    rw [hC, Set.image_image]
    conv_rhs => rw [← Set.image_id B]
    exact Set.image_congr fun y hy => (hTV y (hBN hy)).2
  have hinj : Set.InjOn (c ∘ ψ.symm) C := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ h
    simp only [Function.comp_apply] at h
    rw [(hTV y (hBN hy)).2, (hTV y' (hBN hy')).2] at h
    rw [h]
  have hderR : ∀ z ∈ V, DifferentiableAt ℝ (c ∘ ψ.symm) z := fun z hz =>
    (hTinvA z hz).differentiableAt.restrictScalars ℝ
  have hdetc : ContinuousOn (fun z => |(fderiv ℝ (c ∘ ψ.symm) z).det|) C := by
    have h1 : ContDiffOn ℝ 1 (c ∘ ψ.symm) V :=
      (hTinvA.contDiffOn_of_completeSpace (n := 1)).restrict_scalars ℝ
    exact ((ContinuousLinearMap.continuous_det.comp_continuousOn
      (h1.continuousOn_fderiv_of_isOpen hVo le_rfl)).abs).mono hCV
  have hGT : IntegrableOn (fun y => G (ψ (c.symm y))) B := by
    have hiff := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
      hCm (f := c ∘ ψ.symm) (f' := fun z => fderiv ℝ (c ∘ ψ.symm) z)
      (fun z hz => (hderR z (hCV hz)).hasFDerivAt.hasFDerivWithinAt) hinj
      (fun y => G (ψ (c.symm y)))
    rw [hCB] at hiff
    refine hiff.mpr ?_
    refine IntegrableOn.congr_fun
      ((hGloc.integrableOn_compact_subset hCV hCc).continuousOn_smul hdetc hCc) ?_ hCm
    rintro _ ⟨y, hy, rfl⟩
    have h := (hTV y (hBN hy)).2
    simp only [Function.comp_apply, h]

  have hdB : ContinuousOn (locDens A Φ j) B :=
    (hD A Φ hΦ j).mono (hBN.trans Set.inter_subset_left)
  have hsub : c.target ∩ c.symm ⁻¹' ψ.source ⊆ c.target ∩ c.symm ⁻¹' L.U x0 :=
    fun y hy => ⟨hy.1, hψU hy.2⟩
  have hφB : ContinuousOn (fun y => L.φ x0 (c.symm y)) B :=
    ((hL.1 x0 j).continuousOn.mono hsub).mono hBN
  have hsB : ContinuousOn (fun y => s x0 (c.symm y)) B :=
    ((hS.1 x0 j).continuousOn.mono hsub).mono hBN
  set Z := B ∩ (fun y => s x0 (c.symm y)) ⁻¹' {0} with hZ
  have hZm : MeasurableSet Z :=
    (hsB.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_singleton).measurableSet
  have h1 : IntegrableOn (fun y => G (ψ (c.symm y)) * locDens A Φ j y) B :=
    hGT.mul_continuousOn hdB hBc
  have h2 : IntegrableOn (fun y => L.φ x0 (c.symm y) * locDens A Φ j y) B :=
    (hφB.mul hdB).integrableOn_compact hBc
  have h3 := h2.indicator hZm
  refine IntegrableOn.congr_fun (Integrable.add (Integrable.sub h1 h2) h3) ?_ hBm
  intro y hy
  have hyN := hBN hy
  have hp : c.symm y ∈ L.U x0 := hψU hyN.2
  have hprod : ∀ w : Fin e → ℂ, (∏ k, (match σ k with
      | some i => w i ^ m k
      | none => 1)) = ∏ i, w i ^ m' i := by
    intro w
    apply prod_option_eq_prod_zpow
    intro k
    split <;> simp_all
  have hlog : Real.log ‖s x0 (c.symm y)‖ = G (ψ (c.symm y)) := by
    show _ = Real.log ‖u (ψ.symm (ψ (c.symm y))) * ∏ i, (ψ (c.symm y)) i ^ m' i‖
    rw [ψ.left_inv hyN.2, hsu _ hyN.2]
    exact congrArg (fun t => Real.log ‖u (c.symm y) * t‖) (hprod _)
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [logNormSec_eq_indicator hS hp, hlog]
  by_cases h0 : s x0 (c.symm y) = 0
  · rw [Set.indicator_of_mem (show y ∈ Z from ⟨hy, h0⟩),
      Set.indicator_of_mem (show c.symm y ∈ {q | s x0 q = 0} from h0)]
    ring
  · rw [Set.indicator_of_notMem (show y ∉ Z from fun h => h0 h.2),
      Set.indicator_of_notMem (show c.symm y ∉ {q | s x0 q = 0} from h0)]
    ring

theorem logNormIntegrable : LogNormIntegrableStatement :=
  logNormIntegrable_of ReciprocityTheory.AnForm.A.logUnitMonoLocInt_thm locDensCont

end

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.ProdProofA
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section

variable {e e' : ℕ}

@[simp] theorem appendCLE_apply_castAdd (u : Fin e → ℂ) (v : Fin e' → ℂ) (i : Fin e) :
    appendCLE e e' (u, v) (Fin.castAdd e' i) = u i := by
  simp [appendCLE]

@[simp] theorem appendCLE_apply_natAdd (u : Fin e → ℂ) (v : Fin e' → ℂ) (i : Fin e') :
    appendCLE e e' (u, v) (Fin.natAdd e i) = v i := by
  simp [appendCLE]

theorem appendCLE_symm_apply (y : Fin (e + e') → ℂ) :
    (appendCLE e e').symm y = (fun i => y (Fin.castAdd e' i), fun i => y (Fin.natAdd e i)) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp

def pr1L : (Fin (e + e') → ℂ) →L[ℂ] (Fin e → ℂ) :=
  (ContinuousLinearMap.fst ℂ (Fin e → ℂ) (Fin e' → ℂ)).comp
    ((appendCLE e e').symm : (Fin (e + e') → ℂ) →L[ℂ] _)

def pr2L : (Fin (e + e') → ℂ) →L[ℂ] (Fin e' → ℂ) :=
  (ContinuousLinearMap.snd ℂ (Fin e → ℂ) (Fin e' → ℂ)).comp
    ((appendCLE e e').symm : (Fin (e + e') → ℂ) →L[ℂ] _)

theorem firstProjection_apply (y : Fin (e + e') → ℂ) : (pr1L y : Fin e → ℂ) = ((appendCLE e e').symm y).1 := rfl
theorem secondProjection_apply (y : Fin (e + e') → ℂ) : (pr2L y : Fin e' → ℂ) = ((appendCLE e e').symm y).2 := rfl

@[simp] theorem firstProjection_apply_apply (y : Fin (e + e') → ℂ) (i : Fin e) :
    (pr1L y : Fin e → ℂ) i = y (Fin.castAdd e' i) := by
  rw [firstProjection_apply, appendCLE_symm_apply]

@[simp] theorem secondProjection_apply_apply (y : Fin (e + e') → ℂ) (i : Fin e') :
    (pr2L y : Fin e' → ℂ) i = y (Fin.natAdd e i) := by
  rw [secondProjection_apply, appendCLE_symm_apply]

def J1 (e e' : ℕ) : Matrix (Fin e) (Fin (e + e')) ℂ := Matrix.of fun a k => if k = Fin.castAdd e' a then 1 else 0

def J2 (e e' : ℕ) : Matrix (Fin e') (Fin (e + e')) ℂ := Matrix.of fun a k => if k = Fin.natAdd e a then 1 else 0

theorem natAdd_ne_castAdd' (a : Fin e) (b : Fin e') : (Fin.natAdd e b : Fin (e + e')) ≠ Fin.castAdd e' a := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem castAdd_ne_natAdd' (a : Fin e) (b : Fin e') : (Fin.castAdd e' a : Fin (e + e')) ≠ Fin.natAdd e b :=
  fun h => natAdd_ne_castAdd' a b h.symm

theorem block_eq (M1 : Matrix (Fin e) (Fin e) ℂ) (M2 : Matrix (Fin e') (Fin e') ℂ) :
    (J1 e e')ᵀ * M1 * J1 e e' + (J2 e e')ᵀ * M2 * J2 e e' =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M1 0 0 M2) := by
  ext k l
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k <;>
    refine Fin.addCases (fun c => ?_) (fun d => ?_) l <;>
    simp [Matrix.mul_apply, J1, J2, Matrix.fromBlocks, ite_mul, mul_ite, Finset.sum_ite_eq, natAdd_ne_castAdd', castAdd_ne_natAdd']

theorem det_block (M1 : Matrix (Fin e) (Fin e) ℂ) (M2 : Matrix (Fin e') (Fin e') ℂ) :
    ((J1 e e')ᵀ * M1 * J1 e e' + (J2 e e')ᵀ * M2 * J2 e e').det = M1.det * M2.det := by
  rw [block_eq, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

def finsetAppendEquiv (e e' : ℕ) : Finset (Fin e) × Finset (Fin e') ≃ Finset (Fin (e + e')) where
  toFun p := p.1.map (Fin.castAddEmb e') ∪ p.2.map (Fin.natAddEmb e)
  invFun S := (Finset.univ.filter (fun a => Fin.castAdd e' a ∈ S),
    Finset.univ.filter (fun b => Fin.natAdd e b ∈ S))
  left_inv p := by
    refine Prod.ext ?_ ?_ <;> ext a <;> simp [natAdd_ne_castAdd', castAdd_ne_natAdd']
  right_inv S := by
    ext k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k <;>
      simp [natAdd_ne_castAdd', castAdd_ne_natAdd']

theorem pot_contDiffAt {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (x : X) (k : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ (A.chart k).target) (hzU : (A.chart k).symm z ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) z := by
  have hmem : (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x ∈ 𝓝 z :=
    ((A.chart k).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨hz, hzU⟩
  exact ((hP.1 x k).contDiffAt hmem).of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top)

end

end ReciprocityTheory.AnForm.M
end

