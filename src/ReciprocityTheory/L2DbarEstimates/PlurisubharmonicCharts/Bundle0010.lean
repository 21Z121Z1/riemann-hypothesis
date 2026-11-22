import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0009
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcB
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle0001
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNullB

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxJ
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

structure CutData (Sf : Finset Y) where
  β : Y → V n → ℝ
  r1 : Y → ℝ
  r2 : Y → ℝ
  W : Y → Set Y
  smooth : ∀ P, ContDiff ℝ ∞ (β P)
  one : ∀ P, ∀ u ∈ closedBall (A.chart (A.pick P) P) (r1 P), β P u = 1
  supp : ∀ P, ∀ u, β P u ≠ 0 → u ∈ closedBall (A.chart (A.pick P) P) (r2 P)
  sub : ∀ P ∈ Sf, closedBall (A.chart (A.pick P) P) (r2 P) ⊆
    (A.chart (A.pick P)).target ∩ (A.chart (A.pick P)).symm ⁻¹' W P
  disj : ∀ P ∈ Sf, ∀ Q ∈ Sf, P ≠ Q → Disjoint (W P) (W Q)

variable {A}

namespace CutData

variable {Sf : Finset Y} (D : CutData A Sf)

def K (P : Y) : Set Y := (A.chart (A.pick P)).symm '' closedBall (A.chart (A.pick P) P) (D.r2 P)

def T (P : Y) : Set Y := (A.chart (A.pick P)).symm ''
  (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P))

def χ (P : Y) : Y → ℝ := A.chiC (A.pick P) (D.β P)

theorem K_sub {P : Y} (hP : P ∈ Sf) : D.K P ⊆ (A.chart (A.pick P)).source ∩ D.W P := by
  rintro _ ⟨u, hu, rfl⟩
  have h := D.sub P hP hu
  exact ⟨(A.chart (A.pick P)).map_target h.1, h.2⟩

theorem K_compact {P : Y} (hP : P ∈ Sf) : IsCompact (D.K P) :=
  A.isCompact_chartImage (isCompact_closedBall _ _) fun _ hu => (D.sub P hP hu).1

theorem T_sub_K (P : Y) : D.T P ⊆ D.K P := image_mono diff_subset

theorem T_compact {P : Y} (hP : P ∈ Sf) : IsCompact (D.T P) :=
  A.isCompact_chartImage ((isCompact_closedBall _ _).diff isOpen_ball)
    fun _ hu => (D.sub P hP hu.1).1

theorem χ_smooth {P : Y} (hP : P ∈ Sf) : A.SmoothFn (D.χ P) :=
  A.chiC_smooth (D.smooth P) (D.supp P) (isCompact_closedBall _ _) fun _ hu => (D.sub P hP hu).1

theorem χ_supp (P : Y) (y : Y) (hy : D.χ P y ≠ 0) : y ∈ D.K P := by
  by_contra h; exact hy (A.chiC_eq_zero (D.supp P) h)

theorem not_mem_K {P Q : Y} (hP : P ∈ Sf) (hQ : Q ∈ Sf) (hPQ : P ≠ Q) {y : Y}
    (hy : y ∈ D.K P) : y ∉ D.K Q := fun h =>
  Set.disjoint_left.1 (D.disj P hP Q hQ hPQ) (D.K_sub hP hy).2 (D.K_sub hQ h).2

theorem eventually_χ_zero {P : Y} (hP : P ∈ Sf) (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hy : y ∉ D.K P) : ∀ᶠ v in 𝓝 (A.chart j y), D.χ P ((A.chart j).symm v) = 0 := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (D.K P)ᶜ) :=
    (A.chart j).isOpen_inter_preimage_symm (D.K_compact hP).isClosed.isOpen_compl
  filter_upwards [hopen.mem_nhds ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hy]⟩]
    with v hv
  by_contra h; exact hv.2 (D.χ_supp P _ h)

theorem eventually_χ_one {P : Y} (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hyP : y ∈ (A.chart (A.pick P)).source)
    (hb : A.chart (A.pick P) y ∈ ball (A.chart (A.pick P) P) (D.r1 P)) :
    ∀ᶠ v in 𝓝 (A.chart j y), (A.chart j).symm v ∈ (A.chart (A.pick P)).source ∧
      D.χ P ((A.chart j).symm v) = 1 := by
  have hc : ContinuousOn ((A.chart (A.pick P)) ∘ (A.chart j).symm) (ovl A.chart j (A.pick P)) :=
    (A.trans_contDiffOn j (A.pick P)).continuousOn
  have hopen : IsOpen (ovl A.chart j (A.pick P) ∩ ((A.chart (A.pick P)) ∘ (A.chart j).symm) ⁻¹'
      ball (A.chart (A.pick P) P) (D.r1 P)) :=
    hc.isOpen_inter_preimage (A.isOpen_ovl j _) isOpen_ball
  have hmem : A.chart j y ∈ ovl A.chart j (A.pick P) ∩ ((A.chart (A.pick P)) ∘ (A.chart j).symm) ⁻¹'
      ball (A.chart (A.pick P) P) (D.r1 P) :=
    ⟨A.mem_ovl hj hyP, by simpa [Function.comp, (A.chart j).left_inv hj] using hb⟩
  filter_upwards [hopen.mem_nhds hmem] with v hv
  refine ⟨hv.1.2, ?_⟩
  rw [χ, A.chiC_of_mem hv.1.2]
  exact D.one P _ (ball_subset_closedBall hv.2)

end CutData

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcC
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

theorem fc_det_real (n : ℕ) (J : V n →L[ℂ] V n) :
    |(J.restrictScalars ℝ).det| = ‖J.det‖ ^ 2 := by
  have h : (J.restrictScalars ℝ).det = Complex.normSq J.det := by
    show LinearMap.det ((J : V n →ₗ[ℂ] V n).restrictScalars ℝ) = _
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  rw [h, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]

theorem fc_rho_eq {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i : ι) (hi : y ∈ (A.chart i).source) :
    Real.exp (A.ph A.kap (A.pick y) y) /
        ‖(fderiv ℂ (A.zLoc w0 s (A.pick y)) (A.chart (A.pick y) y)).det‖ ^ 2 =
      Real.exp (A.ph A.kap i y) / ‖(fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det‖ ^ 2 := by
  have hp := A.mem_pick y
  have hg : 0 < ‖A.g A.kap (A.pick y) i y‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (A.g_ne A.kap (A.pick y) i y hp hi)) 2
  rw [fc_det_jz A hD hy (A.pick y) i hp hi, A.ph_trans A.kap (A.pick y) i y hp hi, Real.exp_sub,
    Real.exp_log hg, norm_mul, mul_pow]
  ring

theorem fc_rho_continuous {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) : Continuous (fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have hi0 : (x0 : Y) ∈ (A.chart (A.pick x0)).source := A.mem_pick _
  have hev : (fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) /
      ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) =ᶠ[𝓝 x0]
      fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x0) x) /
        ‖(fderiv ℂ (A.zLoc w0 s (A.pick x0)) (A.chart (A.pick x0) x)).det‖ ^ 2 := by
    have hU : ∀ᶠ x : A.Mset w0 s De in 𝓝 x0, (x : Y) ∈ (A.chart (A.pick x0)).source :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        ((A.chart (A.pick x0)).open_source.mem_nhds hi0)
    filter_upwards [hU] with x hx
    exact fc_rho_eq A hD x.2 (A.pick x0) hx
  refine ContinuousAt.congr ?_ hev.symm
  set i := A.pick (x0 : Y) with hidef
  have hph : ContinuousAt (fun y => A.ph A.kap i y) (x0 : Y) := by
    have h1 : ContinuousAt (A.ph A.kap i ∘ (A.chart i).symm) (A.chart i x0) :=
      ((A.smooth_ph A.kap i).continuousOn).continuousAt
        ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi0))
    have h2 := h1.comp_of_eq ((A.chart i).continuousAt hi0) rfl
    refine h2.congr ?_
    filter_upwards [(A.chart i).open_source.mem_nhds hi0] with y hy
    simp only [Function.comp_apply, (A.chart i).left_inv hy]
  have hO := fc_isOpen_O A (De := De) hD i
  have hmO := fc_mem_O A x0 i hi0
  have hdetc : ContinuousAt (fun y => (fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det) (x0 : Y) := by
    have h1 : ContinuousAt (fderiv ℂ (A.zLoc w0 s i)) (A.chart i x0) :=
      ((fc_zLoc_contDiffOn A hD i).continuousOn_fderiv_of_isOpen hO (by simp)).continuousAt
        (hO.mem_nhds hmO)
    exact ContinuousLinearMap.continuous_det.continuousAt.comp
      (h1.comp_of_eq ((A.chart i).continuousAt hi0) rfl)
  have hne := fc_jz_det_ne A hD hF x0.2 i hi0
  have hFc : ContinuousAt (fun y => Real.exp (A.ph A.kap i y) /
      ‖(fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det‖ ^ 2) (x0 : Y) :=
    (Real.continuous_exp.continuousAt.comp hph).div ((continuous_norm.continuousAt.comp hdetc).pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  exact hFc.comp continuous_subtype_val.continuousAt

theorem fc_mu_piece {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n))
    (he : IsChart n (flatStein A hD hF).z e) (i : ι) (B : Set (A.Mset w0 s De))
    (hB : MeasurableSet B) (hBs : B ⊆ e.source) (hBi : ∀ m ∈ B, (m : Y) ∈ (A.chart i).source) :
    A.mu.comap Subtype.val B =
      ∫⁻ m in B, ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) ∂vol n (flatStein A hD hF).z := by
  have hMm : MeasurableSet (A.Mset w0 s De) := (isOpen_Mset A hD).measurableSet
  have hemb := MeasurableEmbedding.subtype_coe hMm
  have hz := (flatStein A hD hF).isLocalHomeomorph
  have hρ : Measurable fun m => ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) :=
    ENNReal.measurable_ofReal.comp (fc_rho_continuous A hD hF).measurable
  rw [hemb.comap_apply]
  have hBY : MeasurableSet (Subtype.val '' B : Set Y) := hemb.measurableSet_image.2 hB
  rw [A.mu_chart i _ hBY (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)]
  have hBimg : MeasurableSet (e '' B) := by
    have := measurableSet_image_of_chart n (flatStein A hD hF).z e he B hB hBs
    rwa [Set.image_congr fun m hm => he (hBs hm)] at this
  have hR : ∫⁻ m in B, ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) ∂vol n (flatStein A hD hF).z =
      ∫⁻ w in e '' B, ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) (e.symm w)) := by
    rw [← lintegral_indicator hB, lintegral_vol_chart n _ hz e he _ (hρ.indicator hB)
      (fun m hm => Set.indicator_of_notMem (fun h => hm (hBs h)) _)]
    have hsub : e '' B ⊆ e.target := fun _ ⟨m, hm, hmw⟩ => hmw ▸ e.map_source (hBs hm)
    rw [← Set.inter_eq_left.2 hsub, ← Measure.restrict_restrict hBimg, ← lintegral_indicator hBimg]
    refine setLIntegral_congr_fun e.open_target.measurableSet fun w hw => ?_
    by_cases h : e.symm w ∈ B
    · have hw' : w ∈ e '' B := ⟨e.symm w, h, e.right_inv hw⟩
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem hw']
    · have hw' : w ∉ e '' B := by
        rintro ⟨m, hm, rfl⟩
        exact h (by rw [e.left_inv (hBs hm)]; exact hm)
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem hw']
  set S := A.chart i '' (Subtype.val '' B)
  have hS : MeasurableSet S :=
    measurableSet_image_of_chart n (A.chart i) (A.chart i) (fun _ _ => rfl) _ hBY
      (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)
  have hSO : S ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact fc_mem_O A m i (hBi m hm)
  have hFm : ∀ m ∈ B, A.zLoc w0 s i (A.chart i m) = e m := fun m hm =>
    fc_zLoc_chart A hD e he m (hBs hm) i (hBi m hm)
  have himg : e '' B = A.zLoc w0 s i '' S := by
    rw [Set.image_image, Set.image_image]
    exact (Set.image_congr fun m hm => hFm m hm).symm
  have hinj : Set.InjOn (A.zLoc w0 s i) S := by
    rintro _ ⟨_, ⟨m1, hm1, rfl⟩, rfl⟩ _ ⟨_, ⟨m2, hm2, rfl⟩, rfl⟩ h
    rw [hFm m1 hm1, hFm m2 hm2] at h
    rw [e.injOn (hBs hm1) (hBs hm2) h]
  have hder : ∀ v ∈ S, HasFDerivWithinAt (A.zLoc w0 s i)
      ((fderiv ℂ (A.zLoc w0 s i) v).restrictScalars ℝ) S v := fun v hv =>
    ((((fc_zLoc_contDiffOn A hD i).differentiableOn (by simp)).differentiableAt
      ((fc_isOpen_O A hD i).mem_nhds (hSO hv))).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [hR, himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hder hinj]
  refine setLIntegral_congr_fun hS ?_
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  have hne := fc_jz_det_ne A hD hF m.2 i (hBi m hm)
  simp only
  rw [hFm m hm, e.left_inv (hBs hm), (A.chart i).left_inv (hBi m hm),
    fc_rho_eq A hD m.2 i (hBi m hm), ← ENNReal.ofReal_mul (abs_nonneg _), fc_det_real]
  congr 1
  field_simp

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNull
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem dense_Mset {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) :
    Dense (A.Mset w0 s De) :=
  fn_dense A hD hF

theorem mu_compl_Mset {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hN : EXTNullStatement n) (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) : A.mu (A.Mset w0 s De)ᶜ = 0 :=
  fn_mu_compl A hN hD hF

theorem ext_Mset {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hE : EXTStatement n) (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (la : La) (F : ι → Y → ℂ) (hFs : A.IsSecOn la (A.Mset w0 s De) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤) :
    ∃ G : ι → Y → ℂ, A.IsSec la G ∧
      ∀ i y, y ∈ A.Mset w0 s De → y ∈ (A.chart i).source → G i y = F i y :=
  fn_ext A hE hD hF la F hFs hloc

end

end ReciprocityTheory.L2DbarEstimates.Y
end

