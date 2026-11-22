import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftCountAlongMultiples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem LiftCountAlongMultiples.proof (hDat : LiftBlockDatum.Statement) (hTop : PowerBlockTop.Statement)
    (hHSM : TheoremHSMBlock.Statement) (hCount : SupBoundCount.Statement) (hPack : SmallPacking.Statement) :
    LiftCountAlongMultiples.Statement := by
  intro K _ ι _ Ω _ _ y D N P0 II a ι' _ x' hD hII harith hbir hP0 hsemi hconj ha hx' hgen hbir'
  classical
  obtain ⟨d, hdy, hdk, hmet, hlift⟩ :=
    hDat K ι Ω y D N P0 a ι' x' hD harith hbir hP0 hsemi hconj ha hx' hgen hbir'
  rw [hdy] at hmet hlift
  set v := liftCoords x' with hv_def
  have hv1 : ∀ j, v j ∈ chartLat y (a • N.a) 1 := fun j => hx' _
  have hv : ∀ j, v j ∈ chartLat y N.a a := fun j => by
    rw [← LiftBlockSections.chartLat_smul_one]
    exact hv1 j
  have hgenv : KH.GeneratesOn y (fun k => (a : ℤ) * N.a k) v := by
    intro c hc
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    refine ⟨fun j => u ((Fintype.equivFin ι').symm j), fun j => hu _, ?_⟩
    rw [← hsum]
    refine Fintype.sum_equiv (Fintype.equivFin ι').symm _ _ fun j => ?_
    simp [v, liftCoords]
  have hsmooth : IsSmoothHerm N := hsemi.1
  have hB : d.A.a = unitDeg (none : Option K) := by rw [d.deg, hdk]

  have htop : II (Option K) (addIdx ι (Fintype.card ι')) (mCoordIdeal d.y) (D + 1) (fun _ => d.A) =
      (a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) := by
    rw [hdy]
    exact hTop K ι Ω y D N a (Fintype.card ι') v d.A II hII harith hsmooth ha hv hgenv hB d.semipos.1 hmet
  obtain ⟨hchi, C, hC⟩ := hHSM D (Option K) (addIdx ι (Fintype.card ι')) Ω II d hII
  rw [htop] at hchi
  set t := (a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) with ht

  obtain ⟨hfin, -⟩ := hPack K ι Ω y D N (chartLat y N.a) harith hbir hsmooth
    (fun τ => SectionLatticeFinite.chartLat_le_nm y N.a τ)
  have htrans : ∀ n, smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) n ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y N) (chartLat y N.a) (a * n) := by
    intro n
    refine LiftBlockSections.smallSectionCount_mono (fun s hs hsm => ⟨?_, ?_⟩) (hfin _)
    · rw [hdy, hdk] at hs
      have := LiftBlockSections.secM_le_chartLat y v (a • N.a) hv1 n hs
      rwa [smul_smul, mul_comm, LiftBlockSections.chartLat_smul_one] at this
    · rw [hdy] at hsm
      exact LiftBlockSections.isSmallH_of_lift hB hv hmet hlift hsm

  set h0 : ℕ → ℝ := fun τ => smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) τ
    with hh0
  set C' := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hsq : ∀ n : ℕ, (n : ℝ) ^ ((D : ℝ) / 2) = Real.sqrt ((n : ℝ) ^ D) := by
    intro n
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    ring_nf
  set E : ℕ → ℝ := fun n => 2 * C' ^ 2 * Real.log (Real.sqrt 2 * C' ^ 2) * (n : ℝ) ^ D +
    2 * C' ^ 2 * D * ((n : ℝ) ^ D * Real.log n) with hE_def
  have hlow : ∀ n : ℕ, 1 ≤ n → blockChi d n - E n ≤ h0 n := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set c := C' * Real.sqrt ((n : ℝ) ^ D) with hc
    have hc1 : 1 ≤ c := by
      have : 1 ≤ Real.sqrt ((n : ℝ) ^ D) := Real.one_le_sqrt.mpr (one_le_pow₀ hn1)
      nlinarith
    have hc2 : c ^ 2 = C' ^ 2 * (n : ℝ) ^ D := by
      rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
    have hbound : ∀ f : MRing (addIdx ι (Fintype.card ι')), IsMultiHomog f (blockDeg d.k₀ n) →
        ∀ z ∈ mcPts (mCoordIdeal d.y),
          ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f := by
      intro f hf z hz
      refine (hC n hn f hf z hz).trans ?_
      rw [hc, ← hsq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (Real.sqrt_nonneg _)
    obtain ⟨hr, hcnt⟩ := hCount D (Option K) (addIdx ι (Fintype.card ι')) Ω d n c (by linarith) hbound
    set r : ℝ := (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) with hr_def
    have hr0 : 0 ≤ r := Nat.cast_nonneg _
    have hL : 0 ≤ Real.log (Real.sqrt 2 * c ^ 2) := by
      apply Real.log_nonneg
      have : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
      nlinarith
    have hrE : r * Real.log (c * Real.sqrt r) ≤ 2 * c ^ 2 * Real.log (Real.sqrt 2 * c ^ 2) := by
      by_cases h0r : r = 0
      · rw [h0r, zero_mul]
        positivity
      have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm h0r)
      have hlog : Real.log (c * Real.sqrt r) ≤ Real.log (Real.sqrt 2 * c ^ 2) := by
        apply Real.log_le_log (by positivity)
        have h1 : Real.sqrt r ≤ Real.sqrt 2 * c := by
          rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ c), ← Real.sqrt_mul (by norm_num)]
          exact Real.sqrt_le_sqrt hr
        nlinarith
      calc r * Real.log (c * Real.sqrt r) ≤ r * Real.log (Real.sqrt 2 * c ^ 2) :=
            mul_le_mul_of_nonneg_left hlog hr0
        _ ≤ 2 * c ^ 2 * Real.log (Real.sqrt 2 * c ^ 2) := mul_le_mul_of_nonneg_right hr hL
    have hEn : 2 * c ^ 2 * Real.log (Real.sqrt 2 * c ^ 2) = E n := by
      have hnpos : (0 : ℝ) < n := by linarith
      have hlg : Real.log (Real.sqrt 2 * c ^ 2) = Real.log (Real.sqrt 2 * C' ^ 2) + D * Real.log n := by
        rw [hc2, ← mul_assoc, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      rw [hlg, hc2]
      simp only [hE_def]
      ring
    have : blockChi d n - E n ≤ blockChi d n - r * Real.log (c * Real.sqrt r) := by linarith
    exact this.trans hcnt

  have hF : (fun n => hsDefect D (blockChi d) t n - E n) =o[atTop] pw D :=
    hchi.sub (ArithmeticVolumeResolution.error_isLittleO D _ _)

  intro ε hε
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  filter_upwards [hF.def (div_pos hε hfac), eventually_ge_atTop 1] with n hFn hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) := by positivity
  have habs : -(ε / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1)) ≤ hsDefect D (blockChi d) t n - E n := by
    have := neg_abs_le (hsDefect D (blockChi d) t n - E n)
    rw [Real.norm_eq_abs, pw, Real.norm_eq_abs, abs_of_pos hnpos] at hFn
    linarith
  have hl := hlow n hn
  have htr := htrans n
  have key : (t - ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      t * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) - ε / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1) := by
    ring
  rw [key]
  simp only [hsDefect] at habs
  simp only [hh0] at hl
  linarith

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegularClosureOpen
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

namespace ProjRegularClosureOpen

def projNumMat {n : ℕ} (F : (Fin n → ℂ) → Fin (n + 1) → ℂ) (u : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i l => F u 0 * fderiv ℂ (fun v => F v i.succ) u (Pi.single l 1) -
    F u i.succ * fderiv ℂ (fun v => F v 0) u (Pi.single l 1)

theorem analyticAt_projDet {n : ℕ} {F : (Fin n → ℂ) → Fin (n + 1) → ℂ} {u : Fin n → ℂ}
    (hF : AnalyticAt ℂ F u) : AnalyticAt ℂ (fun v => F v 0 * (projNumMat F v).det) u := by
  have hc : ∀ i, AnalyticAt ℂ (fun v => F v i) u := fun i => analyticAt_pi_iff.1 hF i
  have hd : ∀ i (w : Fin n → ℂ), AnalyticAt ℂ (fun v => fderiv ℂ (fun v => F v i) v w) u :=
    fun i w => ((ContinuousLinearMap.apply ℂ ℂ w).analyticAt _).comp (hc i).fderiv
  have hm : ∀ i l, AnalyticAt ℂ (fun v => projNumMat F v i l) u := fun i l =>
    ((hc 0).mul (hd _ _)).sub ((hc _).mul (hd _ _))
  refine (hc 0).mul ?_
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact Finset.univ.analyticAt_fun_sum (fun σ _ =>
    analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hm _ _)))

theorem det_fderiv_div {n : ℕ} {F : (Fin n → ℂ) → Fin (n + 1) → ℂ} {u : Fin n → ℂ}
    (hF : AnalyticAt ℂ F u) (h0 : F u 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ((F u 0 ^ 2)⁻¹) ^ n * (projNumMat F u).det := by
  classical
  have hc : ∀ i, AnalyticAt ℂ (fun v => F v i) u := fun i => analyticAt_pi_iff.1 hF i
  have key : ∀ (i : Fin n) (w : Fin n → ℂ),
      F u 0 ^ 2 * fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u w i =
        F u 0 * fderiv ℂ (fun v => F v i.succ) u w - F u i.succ * fderiv ℂ (fun v => F v 0) u w := by
    intro i w
    have hq : AnalyticAt ℂ (fun v => F v i.succ / F v 0) u := (hc _).div (hc 0) h0
    have hev : (fun v => F v i.succ / F v 0 * F v 0) =ᶠ[𝓝 u] (fun v => F v i.succ) := by
      filter_upwards [(hc 0).continuousAt.eventually_ne h0] with v hv
      exact div_mul_cancel₀ _ hv
    have hmul : fderiv ℂ (fun v => F v i.succ) u = (F u i.succ / F u 0) • fderiv ℂ (fun v => F v 0) u +
        F u 0 • fderiv ℂ (fun v => F v i.succ / F v 0) u := by
      rw [← hev.fderiv_eq]
      exact fderiv_fun_mul hq.differentiableAt (hc 0).differentiableAt
    have hcomp : fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u w i =
        fderiv ℂ (fun v => F v i.succ / F v 0) u w := by
      rw [fderiv_pi (φ := fun (i : Fin n) v => F v i.succ / F v 0)
        (fun i => ((hc _).div (hc 0) h0).differentiableAt)]
      rfl
    rw [hcomp, hmul]
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hM : LinearMap.toMatrix' (fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = (F u 0 ^ 2)⁻¹ • projNumMat F u := by
    ext i l
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, Matrix.smul_apply,
      smul_eq_mul, projNumMat]
    rw [← key i (Pi.single l 1)]
    field_simp
  rw [← LinearMap.det_toMatrix', hM, Matrix.det_smul, Fintype.card_fin]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))

theorem lift_analyticAt_of_mem {V : Set R.X} {BV : FinHolAtlas n V}
    (hB : HoloMap BV R.A Subtype.val) (x : R.X) {j : Fin BV.n} {u : Fin n → ℂ}
    (hu : u ∈ (BV.chart j).target) (hU : ((BV.chart j).symm u).1 ∈ R.U x) :
    AnalyticAt ℂ (fun v => R.lift x ((BV.chart j).symm v).1) u := by
  rw [analyticAt_pi_iff]
  intro p
  obtain ⟨k, hk⟩ : ∃ k, ((BV.chart j).symm u).1 ∈ (R.A.chart k).source := R.A.cover _
  have h1 : AnalyticAt ℂ ((fun y => R.lift x y p) ∘ (R.A.chart k).symm)
      (R.A.chart k ((BV.chart j).symm u).1) :=
    R.holo x p k _ ⟨(R.A.chart k).map_source hk, by
      show (R.A.chart k).symm (R.A.chart k ((BV.chart j).symm u).1) ∈ R.U x
      rw [(R.A.chart k).left_inv hk]; exact hU⟩
  have h2 : AnalyticAt ℂ (R.A.chart k ∘ Subtype.val ∘ (BV.chart j).symm) u :=
    hB.2 j k _ ⟨hu, hk⟩
  have hcont : ContinuousAt (fun v => ((BV.chart j).symm v).1) u :=
    continuous_subtype_val.continuousAt.comp ((BV.chart j).continuousAt_symm hu)
  refine (h1.comp_of_eq h2 rfl).congr ?_
  filter_upwards [hcont.preimage_mem_nhds ((R.A.chart k).open_source.mem_nhds hk)] with v hv
  simp [(R.A.chart k).left_inv hv]

theorem proj_analyticAt_of_mem {V : Set R.X} {BV : FinHolAtlas n V}
    (hB : HoloMap BV R.A Subtype.val) (x : R.X) {j : Fin BV.n} {u : Fin n → ℂ}
    (hu : u ∈ (BV.chart j).target) (hU : ((BV.chart j).symm u).1 ∈ R.U x) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((BV.chart j).symm v).1))) u := by
  classical
  have hF := lift_analyticAt_of_mem hB x hu hU
  have hs : AnalyticAt ℂ (fun v => segre (R.lift x ((BV.chart j).symm v).1)) u := by
    rw [analyticAt_pi_iff]
    intro i
    exact Finset.univ.analyticAt_fun_prod (fun k _ => analyticAt_pi_iff.1 hF ⟨k, i k⟩)
  exact ((LinearMap.toContinuousLinearMap Ψ).analyticAt _).comp hs

end ProjRegularClosureOpen

open ProjRegularClosureOpen in

theorem ProjRegularClosureOpen.proof : ProjRegularClosureOpen.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB
  classical
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨j, hj⟩ := BV.cover x
  let S : Set (Fin n → ℂ) :=
    (BV.chart j).target ∩ (BV.chart j).symm ⁻¹' (Subtype.val ⁻¹' R.U x.1)
  have hSo : IsOpen S := (BV.chart j).isOpen_inter_preimage_symm
    ((R.isOpen_U x.1).preimage continuous_subtype_val)
  have hxS : BV.chart j x ∈ S :=
    ⟨(BV.chart j).map_source hj, by simp [(BV.chart j).left_inv hj, R.mem_U]⟩
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 hSo _ hxS
  let F : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun v => Ψ (segre (R.lift x.1 ((BV.chart j).symm v).1))
  let h : (Fin n → ℂ) → ℂ := fun v => F v 0 * (projNumMat F v).det
  have hFa : ∀ u ∈ S, AnalyticAt ℂ F u := fun u hu => proj_analyticAt_of_mem Ψ hB x.1 hu.1 hu.2
  have hha : AnalyticOnNhd ℂ h (Metric.ball (BV.chart j x) r) := fun u hu =>
    analyticAt_projDet (hFa u (hrS hu))
  have hreg : ∀ u ∈ S, (BV.chart j).symm u ∈ projRegular R Ψ BV ↔ h u ≠ 0 := by
    intro u hu
    have hy : (BV.chart j).symm u ∈ (BV.chart j).source := (BV.chart j).map_target hu.1
    have hyu : BV.chart j ((BV.chart j).symm u) = u := (BV.chart j).right_inv hu.1
    have h0iff := ProjRegular.proj_ne_zero_iff Ψ (R := R) (hu.2 : ((BV.chart j).symm u).1 ∈ R.U x.1)
    have hev : (projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm =ᶠ[𝓝 u]
        fun v (i : Fin n) => F v i.succ / F v 0 := by
      filter_upwards [hSo.mem_nhds hu] with v hv
      exact ProjRegular.projCoord_eq Ψ hv.2
    constructor
    · rintro ⟨h0, hd⟩
      have hF0 : F u 0 ≠ 0 := h0iff.1 h0
      have hdj := hd j hy
      rw [hyu, hev.fderiv_eq, det_fderiv_div (hFa u hu) hF0] at hdj
      exact mul_ne_zero hF0 (right_ne_zero_of_mul hdj)
    · intro hh
      have hF0 : F u 0 ≠ 0 := left_ne_zero_of_mul hh
      have h0 := h0iff.2 hF0
      refine ⟨h0, fun k hk => ProjRegular.det_ne_zero_of_chart Ψ hB _ h0 hk hy ?_⟩
      rw [hyu, hev.fderiv_eq, det_fderiv_div (hFa u hu) hF0]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hF0)))
        (right_ne_zero_of_mul hh)
  have hW : (BV.chart j).source ∩ (BV.chart j) ⁻¹' Metric.ball (BV.chart j x) r ∈ 𝓝 x :=
    ((BV.chart j).isOpen_inter_preimage Metric.isOpen_ball).mem_nhds ⟨hj, Metric.mem_ball_self hr⟩
  filter_upwards [hW] with y hyW
  obtain ⟨hys, hyb⟩ := hyW
  rw [mem_closure_iff_nhds]
  intro W hWy
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hz : h =ᶠ[𝓝 (BV.chart j y)] 0 := by
    have hc : ContinuousAt (BV.chart j).symm (BV.chart j y) :=
      (BV.chart j).continuousAt_symm ((BV.chart j).map_source hys)
    have hW' : W ∈ 𝓝 ((BV.chart j).symm (BV.chart j y)) := by
      rw [(BV.chart j).left_inv hys]; exact hWy
    filter_upwards [hc.preimage_mem_nhds hW', Metric.isOpen_ball.mem_nhds hyb] with v hvW hvB
    by_contra hv
    exact (Set.eq_empty_iff_forall_notMem.1 hne) _ ⟨hvW, (hreg v (hrS hvB)).2 hv⟩
  have hall := hha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hyb hz
  obtain ⟨z, hzW, hzreg⟩ := mem_closure_iff_nhds.1 hx _ hW
  exact ((hreg _ (hrS hzW.2)).1 (by rwa [(BV.chart j).left_inv hzW.1])) (hall hzW.2)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegularNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

namespace ProjRegularNull

theorem analyticAt_det_fderiv {n : ℕ} {q : (Fin n → ℂ) → Fin n → ℂ} {u : Fin n → ℂ}
    (hq : AnalyticAt ℂ q u) :
    AnalyticAt ℂ (fun v => LinearMap.det (fderiv ℂ q v : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) u := by
  classical
  have he : ∀ i k : Fin n, AnalyticAt ℂ (fun v => fderiv ℂ q v (Pi.single k 1) i) u := by
    intro i k
    let L : ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).comp
        (ContinuousLinearMap.apply ℂ (Fin n → ℂ) (Pi.single k 1))
    exact (L.analyticAt _).comp hq.fderiv
  have hm : (fun v => LinearMap.det (fderiv ℂ q v : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) =
      fun v => Matrix.det (Matrix.of fun i k => fderiv ℂ q v (Pi.single k 1) i) := by
    funext v
    rw [← LinearMap.det_toMatrix']
    congr 1
  rw [hm]
  simp only [Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  exact Finset.univ.analyticAt_fun_sum fun σ _ =>
    analyticAt_const.mul (Finset.univ.analyticAt_fun_prod fun i _ => he _ _)

end ProjRegularNull

theorem ProjRegularNull.proof : ProjRegularNull.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB _ _ j
  set T := (BV.chart j).target ∩ (BV.chart j).symm ⁻¹'
    (interior (closure (projRegular R Ψ BV)) \ projRegular R Ψ BV) with hT

  have hreg : ∀ z ∈ T, ∀ r > 0, ball z r ⊆ (BV.chart j).target →
      ∃ w ∈ ball z r, (BV.chart j).symm w ∈ projRegular R Ψ BV := by
    intro z hz r hr hWt
    obtain ⟨y, ⟨w, hw, rfl⟩, hyr⟩ := mem_closure_iff.1 (interior_subset hz.2.1) _
      ((BV.chart j).isOpen_image_symm_of_subset_target isOpen_ball hWt) ⟨z, mem_ball_self hr, rfl⟩
    exact ⟨w, hw, hyr⟩
  let Z : Set (Fin n → ℂ) := {u | Ψ (segre (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1)) 0 = 0}
  have hA : volume (T ∩ Z) = 0 := by
    refine ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set _ fun z hz => ?_
    set x0 := (BV.chart j).symm z
    have hx0 : x0 ∈ (BV.chart j).source := (BV.chart j).map_target hz.1.1
    have hz0 : BV.chart j x0 = z := (BV.chart j).right_inv hz.1.1
    have hF := analyticAt_pi_iff.1 (ProjRegular.proj_analyticAt Ψ hB x0 hx0) 0
    have hU := (ProjRegular.lift_analyticAt hB x0 hx0).2
    rw [hz0] at hF hU
    obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff_ball.1 (hF.eventually_analyticAt.and
      (hU.and ((BV.chart j).open_target.mem_nhds hz.1.1)))
    obtain ⟨w, hw, hwr⟩ := hreg z hz.1 r hr fun u hu => (hP u hu).2.2
    refine ⟨ball z r, isOpen_ball, mem_ball_self hr, (convex_ball z r).isPreconnected, _,
      fun u hu => (hP u hu).1, ⟨w, hw, ?_⟩, fun u hu => ?_⟩
    · exact (ProjRegular.proj_ne_zero_iff Ψ (hP w hw).2.1).1 hwr.1
    · by_contra h
      exact (ProjRegular.proj_ne_zero_iff Ψ (hP u hu.2).2.1).2 h hu.1.2
  have hB' : volume (T ∩ Zᶜ) = 0 := by
    refine ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set _ fun z hz => ?_
    set x0 := (BV.chart j).symm z
    have hx0 : x0 ∈ (BV.chart j).source := (BV.chart j).map_target hz.1.1
    have hz0 : BV.chart j x0 = z := (BV.chart j).right_inv hz.1.1
    have hq := ProjRegular.analyticAt_chart Ψ hB x0 hz.2 j hx0
    rw [hz0] at hq
    obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff_ball.1 (hq.eventually_analyticAt.and
      ((BV.chart j).open_target.mem_nhds hz.1.1))
    obtain ⟨w, hw, hwr⟩ := hreg z hz.1 r hr fun u hu => (hP u hu).2
    refine ⟨ball z r, isOpen_ball, mem_ball_self hr, (convex_ball z r).isPreconnected, _,
      fun u hu => ProjRegularNull.analyticAt_det_fderiv (hP u hu).1, ⟨w, hw, ?_⟩, fun u hu => ?_⟩
    · have h := hwr.2 j ((BV.chart j).map_target (hP w hw).2)
      rwa [(BV.chart j).right_inv (hP w hw).2] at h
    · by_contra hd
      refine hu.1.1.2.2 ⟨hu.1.2, fun k hk => ProjRegular.det_ne_zero_of_chart Ψ hB _ hu.1.2 hk
        ((BV.chart j).map_target hu.1.1.1) ?_⟩
      rwa [(BV.chart j).right_inv hu.1.1.1]
  refine measure_mono_null (fun u hu => ?_) (measure_union_null hA hB')
  by_cases h : u ∈ Z
  · exact Or.inl ⟨hu, h⟩
  · exact Or.inr ⟨hu, h⟩

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphFactor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftGraphFactor.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a r : ℕ) (v : Fin r → Ω),
    (∀ j, v j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) v →
    ∃ Φ : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} ∧
      (∀ w : (Σ k, ι k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → 0 < Φ w) ∧
      (∀ (c : K → ℂ) (w : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
        Φ (fun p => c p.1 * w p) = (∏ k, ‖c k‖ ^ ((a • N.a) k)) ^ 2 * Φ w) ∧
      (∀ w : (Σ k, ι k) → ℂ, Φ (fun p => (starRingEnd ℂ) (w p)) = Φ w) ∧
      (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin r,
        secNormAt y N a (v j) (basePart₂ z) * N.h (basePart₂ z) ^ a * Real.sqrt (∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2) =
          ‖z ⟨none, j⟩‖ * Real.sqrt (Φ (basePart₂ z))) ∧
      (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ ξ : (Σ k, addIdx ι r k) → ℂ,
        IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z ξ →
        leviForm (fun z => Real.log (Φ (basePart₂ z))) z ξ =
          leviForm (fun z : (Σ k, addIdx ι r k) → ℂ => Real.log (∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2)) z ξ)

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjFullRankMeetsRegular
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjFullRankMeetsRegular.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ x ∈ projFullRank R BV, ∃ y ∈ connectedComponent x, y ∈ projRegular R Ψ BV

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjMaxRank
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def projMaxRank {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {n : ℕ} (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {V : Set R.X} (BV : FinHolAtlas n V) : Set V :=
  {x | ∃ i : Fin (n + 1), Ψ (segre (R.lift x.1 x.1)) i ≠ 0 ∧ ∃ j, x ∈ (BV.chart j).source ∧
    Module.finrank ℂ (LinearMap.range (fderiv ℂ
      (fun u l => Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) l /
        Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) i) (BV.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))) = n}

end GroundTheory.Heights₂.Heights.Targets
end
end

