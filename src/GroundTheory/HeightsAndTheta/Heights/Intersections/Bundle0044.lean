import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.Intersections.PullBad
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.HasStrictFDerivAtEquiv
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set

namespace pullbackPushforward_holds

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_comm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

theorem sameOrbit_tr {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), by funext p; simp [mul_assoc]⟩

theorem segre_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ∃ μ : ℂ, μ ≠ 0 ∧ segre z = μ • segre z' := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, segre_smul c z'⟩

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem sameOrbit_comp {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {z z' : (Σ k', ι' k') → ℂ} (h : SameOrbit z z') :
    SameOrbit (fun p => z (v p)) (fun p => z' (v p)) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext p
  show c (v p).1 * z' (v p) = c (κ p.1) * z' (v p)
  rw [hv.2.2.1 p]

end Orbit

theorem hasStrictFDerivAt_equiv {n : ℕ} {Q : (Fin n → ℂ) → (Fin n → ℂ)} {u : Fin n → ℂ}
    (hQ : AnalyticAt ℂ Q u)
    (hd : LinearMap.det (fderiv ℂ Q u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0) :
    ∃ e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ), HasStrictFDerivAt Q (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) u := by
  refine ⟨(LinearMap.equivOfDetNeZero _ hd).toContinuousLinearEquiv, ?_⟩
  have h : ((LinearMap.equivOfDetNeZero _ hd).toContinuousLinearEquiv :
      (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ Q u := by
    ext1 w
    rfl
  rw [h]
  exact hQ.hasStrictFDerivAt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem pullPt_sameOrbit (hv : IsBlockMap κ v) {x z : R.X} (hz : z ∈ R.U x) :
    SameOrbit (pullPt R v z) (fun p => R.lift x z (v p)) :=
  sameOrbit_comp hv (R.compat z x z ⟨R.mem_U z, hz⟩)

theorem pullQ_eq_local (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Φ z = fun i => Φ (segre (fun p => R.lift x z (v p))) i.succ /
      Φ (segre (fun p => R.lift x z (v p))) 0 := by
  obtain ⟨μ, hμ, hseg⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv hz)
  funext i
  simp only [pullQ, hseg, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hμ

theorem analyticAt_segre_pull (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X)
    (j : Fin R.A.n) {u : Fin n → ℂ} (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun w => Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p)))) u := by
  classical
  have hl := analyticAt_lift_chart R x j hu
  have hs : AnalyticAt ℂ (fun w => segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Φ).analyticAt _ |>.comp hs

theorem analyticAt_pullQ (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (x : R.X) (j : Fin R.A.n) (hj : x ∈ (R.A.chart j).source)
    (h0 : Φ (segre (pullPt R v x)) 0 ≠ 0) :
    AnalyticAt ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hH := analyticAt_segre_pull R (v := v) Φ x j hu
  have hH0 : AnalyticAt ℂ (fun w => Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Φ (segre (fun p => R.lift x ((R.A.chart j).symm u) (v p))) 0 ≠ 0 := by
    rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun w => fun i : Fin n =>
      Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) i.succ /
        Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu] with w hw
  exact (pullQ_eq_local R hv Φ hw.2).symm

theorem det_pullQ_chart (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {x : R.X} {j k : Fin R.A.n} (hj : x ∈ (R.A.chart j).source) (hk : x ∈ (R.A.chart k).source)
    (h0 : Φ (segre (pullPt R v x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) =
      LinearMap.det (fderiv ℂ (pullQ R v Φ ∘ (R.A.chart k).symm) (R.A.chart k x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) *
      LinearMap.det (fderiv ℂ (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  set T := R.A.chart k ∘ (R.A.chart j).symm with hTdef
  have huk : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.A.chart k).source :=
    ⟨(R.A.chart j).map_source hj, by rw [mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := R.A.holo j k u huk
  have hTu : T u = R.A.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_pullQ R hv Φ x k hk h0
  have heq : pullQ R v Φ ∘ (R.A.chart j).symm =ᶠ[𝓝 u] (pullQ R v Φ ∘ (R.A.chart k).symm) ∘ T := by
    filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.A.chart k).open_source).mem_nhds
      huk] with w hw
    simp only [hTdef, Function.comp_apply, (R.A.chart k).left_inv hw.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt,
    hTu]
  exact LinearMap.det_comp _ _

theorem eval_lift_eq_zero_iff {f : MRing ι'} {a : K' → ℕ} (hf : IsMultiHomog f a) {x z : R.X}
    (hz : z ∈ R.U x) :
    eval (R.lift z z) (map (Int.castRingHom ℂ) f) = 0 ↔
      eval (R.lift x z) (map (Int.castRingHom ℂ) f) = 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  rw [hzc, eval_smul_homog f a hf c]
  have : ∏ k, c k ^ a k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  simp [this]

theorem isOpen_chart_ne {f : MRing ι'} {a : K' → ℕ} (hf : IsMultiHomog f a) (j : Fin R.A.n) :
    IsOpen ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0}) := by
  rw [isOpen_iff_mem_nhds]
  rintro u1 ⟨hu1, h1⟩
  set x1 := (R.A.chart j).symm u1
  have hV : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x1 ∈ 𝓝 u1 :=
    ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x1)).mem_nhds ⟨hu1, R.mem_U x1⟩
  have hcont : ContinuousAt (fun u => eval (R.lift x1 ((R.A.chart j).symm u))
      (map (Int.castRingHom ℂ) f)) u1 :=
    (MvPolynomial.continuous_eval _).continuousAt.comp
      (analyticAt_lift_chart R x1 j ⟨hu1, R.mem_U x1⟩).continuousAt
  have hne : eval (R.lift x1 ((R.A.chart j).symm u1)) (map (Int.castRingHom ℂ) f) ≠ 0 := h1
  filter_upwards [hV, hcont.eventually_ne hne] with u hu hne'
  exact ⟨hu.1, fun h => hne' ((eval_lift_eq_zero_iff R hf hu.2).mp h)⟩

theorem fzero_null (hP' : IsArithVar P' (n + 1)) {f : MRing ι'} {a : K' → ℕ} (hf : IsMultiHomog f a)
    (hfP : f ∉ P') (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0}) = 0 := by
  classical
  obtain ⟨Ψ', hΨ'⟩ := goodProjExists K' ι' P' n hP'
  have hJf : IsMultiHomogIdeal (Ideal.span {f}) :=
    ⟨{f}, fun g hg => ⟨a, by rw [Set.mem_singleton_iff.mp hg]; exact hf⟩, rfl⟩
  have hJP : ¬ Ideal.span {f} ≤ P' := fun h => hfP (h (Ideal.subset_span rfl))
  have hnull := projB_null Ψ' hP' hΨ' hJf hJP
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set g : (Fin n → ℂ) → ℂ := fun u => eval (R.lift x0 ((R.A.chart j).symm u))
    (map (Int.castRingHom ℂ) f) with hgdef
  have hga : AnalyticOnNhd ℂ g V := fun u hu =>
    analyticAt_eval_poly _ fun p => analyticAt_pi_iff.mp (analyticAt_lift_chart R x0 j hu) p
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, g, hga.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    set N := ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ' (segre (R.lift x x)) 0 = 0}) ∪
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ' (segre (R.lift x x)) 0 ≠ 0 ∧
        ∃ k, x ∈ (R.A.chart k).source ∧
          LinearMap.det (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart k).symm) (R.A.chart k x) :
            (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}) with hNdef
    have hN : volume N = 0 :=
      measure_union_null (psi0_null R Ψ' hP' hΨ' j) (ram_null R Ψ' hP' hΨ' j)
    obtain ⟨u1, hu1B, hu1N⟩ : ∃ u1 ∈ Metric.ball u0 r, u1 ∉ N := by
      by_contra h
      push Not at h
      exact (Metric.measure_ball_pos volume u0 hr).ne' (measure_mono_null h hN)
    have hu1t : u1 ∈ (R.A.chart j).target := (hball hu1B).1
    set x1 := (R.A.chart j).symm u1
    have hx1 : x1 ∈ (R.A.chart j).source := (R.A.chart j).map_target hu1t
    have hcx1 : R.A.chart j x1 = u1 := (R.A.chart j).right_inv hu1t
    have h01 : Ψ' (segre (R.lift x1 x1)) 0 ≠ 0 := fun h => hu1N (Or.inl ⟨hu1t, h⟩)
    have hdet1 : LinearMap.det (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u1 :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
      intro h
      exact hu1N (Or.inr ⟨hu1t, h01, j, hx1, by rw [hcx1]; exact h⟩)
    have hQa : AnalyticAt ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u1 := by
      have := analyticAt_brQ R Ψ' x1 j hx1 h01
      rwa [hcx1] at this
    obtain ⟨e, he⟩ := hasStrictFDerivAt_equiv hQa hdet1
    have hcont0 : ContinuousOn (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0) V :=
      fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ' x0 j hu) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O :=
      (hcont0.mono hball).isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu1O : u1 ∈ O := by
      refine ⟨hu1B, ?_⟩
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu1B).2 Ψ'
      show Ψ' (segre (R.lift x0 x1)) 0 ≠ 0
      intro h
      apply h01
      rw [hμeq, Pi.smul_apply, smul_eq_mul, h, mul_zero]
    have himg : (brQ R Ψ' ∘ (R.A.chart j).symm) '' O ∈
        𝓝 ((brQ R Ψ' ∘ (R.A.chart j).symm) u1) := by
      rw [← he.map_nhds_eq_of_equiv]
      exact Filter.image_mem_map (hO.mem_nhds hu1O)
    refine (Measure.measure_pos_of_mem_nhds (μ := volume) himg).ne' (measure_mono_null ?_ hnull)
    rintro _ ⟨u, huO, rfl⟩
    set x := (R.A.chart j).symm u
    have hxU : x ∈ R.U x0 := (hball huO.1).2
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R hxU Ψ'
    have h0x : Ψ' (segre (R.lift x x)) 0 ≠ 0 := by
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ huO.2
    obtain ⟨z2, hz2, hsz2, hΨz2⟩ := brW_mem_fibre R Ψ' hP'.1 hP'.2.1.2.1 h0x
    refine ⟨z2, hz2, ?_, ?_⟩
    · have hso : SameOrbit z2 (R.lift x x) :=
        sameOrbit_of_segre (R.mem x x (R.mem_U x)).1 _ (inv_ne_zero h0x) (by rw [hsz2]; rfl)
      refine mem_mcPts_of_sameOrbit hJf hso ⟨(R.mem x x (R.mem_U x)).1, fun g' hg' => ?_⟩
      obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton'.mp hg'
      rw [map_mul, eval_mul, (eval_lift_eq_zero_iff R hf hxU).mpr (hall u huO.1), mul_zero]
    · rw [hsz2, hΨz2]
      rfl
  · rintro w ⟨⟨-, hw0⟩, hwb⟩
    exact (eval_lift_eq_zero_iff R hf (hball hwb).2).mp hw0

end pullbackPushforward_holds

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsAlt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 PointVertical

theorem ArithmeticIntersectionVertical.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι')
    (hPD : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjDegStatement F ι ι')
    (hDeg : VerticalDegree.Statement) :
    ArithmeticIntersectionVertical.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n a s α W' hv hP' hP hs hsP hW' hvert
  classical

  have hs' : IsSectionOn P' (HermLine.sqMetric (ι := ι') (Function.extend κ α 0)) (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, hsP⟩
  obtain ⟨hW'm, hpr, hW'd⟩ := (divSuppArith K' ι' P' n _ _ W' hP' hs' hW').2 hvert
  set p := charOf W' with hpdef
  have : Fact p.Prime := ⟨hpr⟩
  have hpW' : ((p : ℕ) : MRing ι') ∈ W' := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W'
  have hW'p : IsProjVarF (W'.map (red p)) n :=
    ⟨isMultiProjPrime_red p hW'm hpW', by rw [ringKrullDim_red p hpW', hW'd]⟩

  have hWm : IsMultiProjPrime (imageZ v W') := isMultiProjPrime_imageZ hv hW'm
  have hpW : ((p : ℕ) : MRing ι) ∈ imageZ v W' := by
    show rename v ((p : ℕ) : MRing ι) ∈ W'
    simpa using hpW'
  have hVm := isMultiProjPrime_red p hWm hpW

  obtain ⟨I, hI, -⟩ := hR4 (ZMod p) K ι
  obtain ⟨I', hI', -⟩ := hR4 (ZMod p) K' ι'
  have hgeo' : geoNum n W' (fun j => pullDeg κ (a j)) = I' (W'.map (red p)) n (fun j => pullDeg κ (a j)) :=
    hGeo K' ι' p I' hI' W' n _ hW'm hpW' hW'p
  by_cases hmem : imageZ v W' ∈ divSupp (imageZ v P') s
  ·
    refine Or.inl ⟨hmem, fun G' J' hJ' => ?_⟩
    have hsW : IsSectionOn (imageZ v P') (HermLine.sqMetric (ι := ι) α) s := ⟨α, fun _ => rfl, hs, hsP⟩
    have hWvert : ¬ IsHorizontal (imageZ v W') := fun h => by
      have h2 : ((p : ℕ) : ℤ) ∈ (imageZ v W').comap (C : ℤ →+* MRing ι) := by
        rw [Ideal.mem_comap, map_natCast]
        exact hpW
      rw [h, Ideal.mem_bot] at h2
      exact hpr.ne_zero (by exact_mod_cast h2)
    obtain ⟨-, -, hWd⟩ := (divSuppArith K ι (imageZ v P') n _ _ _ hP hsW hmem).2 hWvert
    have hWp : IsProjVarF ((imageZ v W').map (red p)) n := ⟨hVm, by rw [ringKrullDim_red p hpW, hWd]⟩
    have hVi : IsProjVarF (imageVar (ZMod p) v (W'.map (red p))) n := by
      rw [imageVar_red p v hpW']
      exact hWp
    obtain ⟨i', hi'⟩ : ∃ i' : ∀ k', ι' k', IsChart (W'.map (red p)) i' :=
      ⟨fun k => (hW'p.1.2.2 k).choose, fun k => (hW'p.1.2.2 k).choose_spec⟩
    rw [hgeo', hPD (ZMod p) K ι K' ι' I I' hI hI' κ v _ n a i' hv hW'p hVi hi', imageVar_red p v hpW',
      ← hGeo K ι p I hI _ n a hWm hpW hWp, hDeg K ι K' ι' κ v p W' n i' hv hpW' hW'p hVi hi' G' J' hJ']
  ·
    refine Or.inr ⟨hmem, ?_⟩
    have hsW' : rename v s ∈ W' := hW'.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hle : imageZ v P' ⊔ Ideal.span {s} ≤ imageZ v W' :=
      sup_le (Ideal.comap_mono (le_sup_left.trans hW'.1.1.2))
        (Ideal.span_le.2 (Set.singleton_subset_iff.2 hsW'))
    have := hWm.1
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le hle
    have hQne : Q ≠ imageZ v W' := fun h => hmem ⟨h ▸ hQ, hWm.2.2⟩
    obtain ⟨x, hxW, hxQ⟩ : ∃ x ∈ imageZ v W', x ∉ Q := by
      by_contra hc
      exact hQne (le_antisymm hQW fun y hy => by_contra fun h => hc ⟨y, hy, h⟩)
    have := hQ.1.1
    have := hP.2.1.1
    have h1 := dim_quot_minimal_add_one (imageZ v P') Q s hsP hQ
    rw [hP.2.2.2] at h1
    have hQd : ringKrullDim (MRing ι ⧸ Q) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      withBot_eq_of_add_one (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])
    have hdim := krullDim_quot_add_one_le hQW hxW hxQ
    obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
    rw [← ringKrullDim_red p hpW, hD, hQd] at hdim
    have hD' : D + 1 ≤ n + Fintype.card K := by exact_mod_cast hdim
    have hVi : IsProjVarF (imageVar (ZMod p) v (W'.map (red p))) (D - Fintype.card K) := by
      rw [imageVar_red p v hpW']
      exact ⟨hVm, by rw [hD, Nat.sub_add_cancel hKD]⟩
    rw [hgeo']
    exact hPC (ZMod p) K ι K' ι' I' hI' κ v _ n (D - Fintype.card K) a hv hW'p hVi (by omega)

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherSide
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def VerticalDegreeAfterAdjoining.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ)
    (i' : ∀ k', ι' k'),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    IsChart (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' →
    ∀ G' : GenFibre v W',
      fnDeg v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' =
        Module.finrank G'.Φ (IntermediateField.adjoin G'.Φ
          (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G'.x' ⟨q.1.1, q.2⟩ / G'.x' ⟨q.1.1, i' q.1.1⟩))

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTail
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def FibreDimensionZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    ∀ G' : GenFibre v W', IsProjVarF (fibreIdeal κ G') 0

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalize.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsClosedPt W → P ≤ W → y ∈ locRing P W →
    ∃ s x : regRing P, (∃ z ∈ locRing P W, ((s : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1) ∧
      y * ((s : funField P) : FractionRing (MRing ι ⧸ P)) = ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsSide
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open ReciprocityTheory.AnForm.M

theorem projectiveLineZeroForm_holds.proof : projectiveLineZeroForm_holds.Statement := by
  intro e X _ _ _ A L s W B hL hs hSNC hB v hv Φ hΦ
  have h := poincareLelong A L s ![1] ![W]
    (Fin.cons B (fun i => i.elim0) : ∀ k, FinHolAtlas e ((![W] : Fin 1 → Set X) k))
    hL hs hSNC (Fin.cons hB (fun i => i.elim0)) v hv Φ hΦ
  rw [Fin.sum_univ_one] at h
  have h1 : (((![1] : Fin 1 → ℕ) 0 : ℕ) : ℝ) = 1 := by simp
  rw [h1, one_mul] at h
  exact h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Over

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def ptsOverPt (P' : Ideal (MRing ι')) (v : (Σ k, ι k) → (Σ k', ι' k')) (z : (Σ k, ι k) → ℂ) :
    Set (Set ((Σ k', ι' k') → ℂ)) :=
  {O | ∃ z' ∈ mcPts P', O = {z'' | SameOrbit z'' z'} ∧ SameOrbit (fun p => z' (v p)) z}

end Over

def GenericPointsAvoidBadLocus.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (i : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) →
    ∃ (D : MRing ι) (a : K → ℕ), IsMultiHomog D a ∧ D ∉ imageZ v P' ∧
      ∀ z ∈ mcPts (imageZ v P'), eval z (map (Int.castRingHom ℂ) D) ≠ 0 →
        (ptsOverPt P' v z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
          (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩))

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StResExists
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

def ResExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ), IsProjVar P e → Nonempty (Res ι P e)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

