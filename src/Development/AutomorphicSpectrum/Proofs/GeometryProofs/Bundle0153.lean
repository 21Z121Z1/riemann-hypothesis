import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0101
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0021
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0146
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0139
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0147
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0148
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0144
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusOverLieModelBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalChartCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartParams

theorem eval_unren_eq_zero {σ : Type} [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ))
    (v : Fin (Fintype.card σ) → ℂ)
    (hv : v ∈ ReciprocityTheory.AnForm.R.zeroSet (Q.map (ReciprocityTheory.AnForm.R.renR σ : MvPolynomial σ ℂ →+* _))) :
    ∀ f ∈ Q, eval (fun q => v (Fintype.equivFin σ q)) f = 0 := by
  intro f hf
  have h1 := hv (ReciprocityTheory.AnForm.R.renC σ f) (Ideal.mem_map_of_mem _ hf)
  have h2 := ReciprocityTheory.AnForm.R.eval_renC (fun q => v (Fintype.equivFin σ q)) f
  have h3 : ReciprocityTheory.AnForm.R.renPt (fun q => v (Fintype.equivFin σ q)) = v := by
    funext j; simp [ReciprocityTheory.AnForm.R.renPt]
  rw [h3, h1] at h2
  exact h2.symm

theorem analyticOnNhd_rescale {σ : Type} {n m : ℕ} (e : σ ≃ Fin m) (g : (Fin n → ℂ) → Fin m → ℂ)
    (V : Set (Fin n → ℂ)) (hg : AnalyticOnNhd ℂ g V) (ε : ℝ) (hεV : Metric.ball 0 ε ⊆ V) (hε : 0 < ε) :
    ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ q, AnalyticAt ℂ (fun s => g ((ε : ℂ) • s) (e q)) t := by
  intro t ht q
  have hmem : (ε : ℂ) • t ∈ V := by
    apply hεV
    rw [mem_ball_zero_iff] at ht ⊢
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith
  have h1 : AnalyticAt ℂ (fun s : Fin n → ℂ => (ε : ℂ) • s) t :=
    ((ε : ℂ) • ContinuousLinearMap.id ℂ (Fin n → ℂ)).analyticAt t
  have h2 : AnalyticAt ℂ (fun s => g ((ε : ℂ) • s)) t :=
    AnalyticAt.comp (f := fun s : Fin n → ℂ => (ε : ℂ) • s) (hg _ hmem) h1
  exact (analyticAt_pi_iff (f := fun l s => g ((ε : ℂ) • s) l)).mp h2 (e q)

theorem eq_zero_of_fderiv_eq_zero {σ : Type} [Fintype σ] {n m : ℕ} (e : σ ≃ Fin m)
    (r : Fin n → MvPolynomial (Fin m) ℂ) (gm : (Fin n → ℂ) → σ → ℂ) (ε : ℂ) (hε : ε ≠ 0)
    (t : Fin n → ℂ) (hgm : DifferentiableAt ℂ gm t)
    (hr : ∀ᶠ s in nhds t, ReciprocityTheory.AnForm.R.evalFam r (fun j => gm s (e.symm j)) = ε • s)
    (v : Fin n → ℂ) (hv : fderiv ℂ gm t v = 0) : v = 0 := by
  let R : (σ → ℂ) → Fin n → ℂ := fun y i => eval (fun j => y (e.symm j)) (r i)
  have hR : DifferentiableAt ℂ R (gm t) := by
    have han : AnalyticAt ℂ R (gm t) := by
      rw [analyticAt_pi_iff]
      intro i
      refine ReciprocityTheory.AnForm.R.analyticAt_eval_of_pi
        (f := fun (y : σ → ℂ) (j : Fin m) => y (e.symm j)) (fun l => ?_) (r i)
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm l)).analyticAt _
    exact han.differentiableAt
  have hc : HasFDerivAt (R ∘ gm) ((fderiv ℂ R (gm t)).comp (fderiv ℂ gm t)) t :=
    hR.hasFDerivAt.comp t hgm.hasFDerivAt
  have hs : HasFDerivAt (R ∘ gm) (ε • ContinuousLinearMap.id ℂ (Fin n → ℂ)) t := by
    have h0 : HasFDerivAt (fun s : Fin n → ℂ => ε • s)
        (ε • ContinuousLinearMap.id ℂ (Fin n → ℂ)) t :=
      (hasFDerivAt_id t).const_smul ε
    exact h0.congr_of_eventuallyEq hr
  have heq := hc.unique hs
  have h1 := congrArg (fun L => L v) heq
  simp only [ContinuousLinearMap.comp_apply, hv, map_zero, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hε

theorem sncChart_of_regular_parameters : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (c : (k : K) → J k)
    (w : (Σ k, J k) → ℂ), w ∈ mcPts P → (∀ k, w ⟨k, c k⟩ ≠ 0) →
    ∀ (a : ℕ) (r : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (h : MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      [IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)))],
    ringKrullDim (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) = n → a ≤ n →
    Ideal.span (Set.range fun i => algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) (r i)) =
      Ideal.map (algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))))
        (ReciprocityTheory.AnForm.R.ptIdeal (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) →
    (∀ i, eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) (r i) = 0) →
    eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) h ≠ 0 →
    (∀ v ∈ ReciprocityTheory.AnForm.R.zeroSet (Cmp.SncRes.ideal (pC P) c), eval v h ≠ 0 →
      ((fun q => v (Fintype.equivFin (Σ k, J k) q)) ∈ Bd ↔ ∃ i : Fin n, (i : ℕ) < a ∧ eval v (r i) = 0)) →
    ∃ (χ : SncChart P n Bd) (O : Set ((Σ k, J k) → ℂ)), IsOpen O ∧ w ∈ O ∧
      ∀ z ∈ O ∩ mcPts P, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c' : K → ℂ, (∀ k, c' k ≠ 0) ∧
        z = torusSmul c' (χ.γ t) := by
  intro K _ J _ P hP n Bd c w hw hwc a r h _ hdim haN hspan hr0 hh0 hbd
  classical
  set I := Cmp.SncRes.ideal (pC P) c with hI
  set p := ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w) with hp
  have hcone : ∀ z, z ∈ mcPts P → (∀ k, z ⟨k, c k⟩ ≠ 0) →
      ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) ∈ ReciprocityTheory.AnForm.R.zeroSet I := by
    intro z hz hzc
    have h1 := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hP c z hzc).1
      ((mem_mcPts_iff_conePts_pC P z).1 hz)
    exact ReciprocityTheory.AnForm.R.renPt_zero _ _ h1
  have hpz : p ∈ ReciprocityTheory.AnForm.R.zeroSet I := hcone w hw hwc
  obtain ⟨U, V, g, hU, hpU, hV, hg, hbij, hrg⟩ :=
    ReciprocityTheory.AnForm.R.exists_holo_coords I p n hdim r hspan

  have hsolve : ∀ v ∈ U ∩ ReciprocityTheory.AnForm.R.zeroSet I,
      ReciprocityTheory.AnForm.R.evalFam r v ∈ V ∧ g (ReciprocityTheory.AnForm.R.evalFam r v) = v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hbij.surjOn hv
    rw [hrg u hu]
    exact ⟨hu, rfl⟩
  have hr0' : ReciprocityTheory.AnForm.R.evalFam r p = 0 := funext hr0
  obtain ⟨h0V, hg0⟩ := hsolve p ⟨hpU, hpz⟩
  rw [hr0'] at h0V hg0

  have hcont0 : ContinuousAt g 0 := (hg 0 h0V).continuousAt
  have hnear : ∀ᶠ u in nhds (0 : Fin n → ℂ), u ∈ V ∧ eval (g u) h ≠ 0 := by
    have hVn : ∀ᶠ u in nhds (0 : Fin n → ℂ), u ∈ V := hV.mem_nhds h0V
    refine hVn.and ?_
    have hc : ContinuousAt (fun u => eval (g u) h) 0 :=
      (MvPolynomial.continuous_eval h).continuousAt.comp hcont0
    refine hc.eventually_ne ?_
    rw [hg0]; exact hh0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  have hεV : Metric.ball (0 : Fin n → ℂ) ε ⊆ V := fun u hu => (hball u hu).1
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hsc : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, (ε : ℂ) • t ∈ Metric.ball (0 : Fin n → ℂ) ε := by
    intro t ht
    rw [mem_ball_zero_iff] at ht ⊢
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith
  let e := Fintype.equivFin (Σ k, J k)
  let gm : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun t q => g ((ε : ℂ) • t) (e q)

  have hzs : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, g ((ε : ℂ) • t) ∈ ReciprocityTheory.AnForm.R.zeroSet I :=
    fun t ht => (hbij.mapsTo (hεV (hsc t ht))).2
  have hchart : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1,
      gm t ∈ ReciprocityTheory.AnForm.R.conePts (pC P) ∧ ∀ k, gm t ⟨k, c k⟩ = 1 := by
    intro t ht
    have h1 := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hP c (gm t)
      (eval_unren_eq_zero _ _ (hzs t ht))
    exact ⟨h1.1, h1.2.1⟩
  have hcoord : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1,
      ReciprocityTheory.AnForm.R.evalFam r (g ((ε : ℂ) • t)) = (ε : ℂ) • t :=
    fun t ht => hrg _ (hεV (hsc t ht))
  have han : AnalyticOnNhd ℂ gm (Metric.ball 0 1) := fun t ht =>
    AnalyticAt.pi (f := fun q s => g ((ε : ℂ) • s) (e q))
      (analyticOnNhd_rescale e g V hg ε hεV hε t ht)
  refine ⟨SncChart.mk gm a haN han ?_ ?_ ?_ ?_, {z | (∀ k, z ⟨k, c k⟩ ≠ 0) ∧
              ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) ∈ U ∧
              ‖ReciprocityTheory.AnForm.R.evalFam r (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z))‖ < ε / 2},
            ?_, ⟨hwc, hpU, ?_⟩, ?_⟩
  · exact fun t ht => (mem_mcPts_iff_conePts_pC P _).2 (hchart t ht).1
  · intro t ht v ⟨c', hc'⟩
    have hdiff : DifferentiableAt ℂ gm t := (han t ht).differentiableAt
    have hcomp : ∀ k, c' k = 0 := by
      intro k
      have h1 := congrFun hc' ⟨k, c k⟩
      have h2 : (fun s => gm s ⟨k, c k⟩) =ᶠ[nhds t] fun _ => (1 : ℂ) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs using (hchart s hs).2 k
      have h3 : HasFDerivAt (fun s => gm s ⟨k, c k⟩)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) ⟨k, c k⟩).comp
            (fderiv ℂ gm t)) t :=
        (hasFDerivAt_pi'.1 hdiff.hasFDerivAt) ⟨k, c k⟩
      have h4 := h3.unique ((hasFDerivAt_const (1 : ℂ) t).congr_of_eventuallyEq h2)
      have h5 := congrArg (fun L => L v) h4
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.zero_apply] at h5
      rw [h1] at h5
      simpa [torusSmul, (hchart t ht).2 k] using h5
    have hzero : fderiv ℂ gm t v = 0 := by
      rw [hc']; funext q; simp [torusSmul, hcomp q.1]
    refine eq_zero_of_fderiv_eq_zero e r gm (ε : ℂ) hεc t hdiff ?_ v hzero
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
    have : (fun j => gm s (e.symm j)) = g ((ε : ℂ) • s) := by
      funext j; simp [gm]
    rw [this]
    exact hcoord s hs
  · intro t ht t' ht' c' hc' he
    have hone : ∀ k, c' k = 1 := by
      intro k
      have h1 := congrFun he ⟨k, c k⟩
      simpa [torusSmul, (hchart t ht).2 k, (hchart t' ht').2 k] using h1.symm
    have hgg : g ((ε : ℂ) • t) = g ((ε : ℂ) • t') := by
      funext j
      have h1 := congrFun he (e.symm j)
      simpa [gm, torusSmul, hone] using h1
    have h2 := (hcoord t ht).symm.trans ((congrArg _ hgg).trans (hcoord t' ht'))
    exact smul_right_injective _ hεc h2
  · intro t ht
    have h1 := hbd (g ((ε : ℂ) • t)) (hzs t ht) (hball _ (hsc t ht)).2
    refine h1.trans ?_
    have h2 : ∀ i, eval (g ((ε : ℂ) • t)) (r i) = (ε : ℂ) * t i := fun i =>
      congrFun (hcoord t ht) i
    simp only [h2, mul_eq_zero, hεc, false_or]
  · have hA : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      have : {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} = ⋂ k, {z | z ⟨k, c k⟩ ≠ 0} := by
        ext z; simp
      rw [this]
      exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
    have hf : ContinuousOn (fun z : (Σ k, J k) → ℂ =>
        ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z))
        {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      refine continuousOn_pi.2 fun j => ?_
      simp only [ReciprocityTheory.AnForm.R.renPt, ReciprocityTheory.AnForm.R.affCoord, Function.comp_apply]
      exact (continuous_apply _).continuousOn.div (continuous_apply _).continuousOn
        fun z hz => hz _
    have hev : Continuous (ReciprocityTheory.AnForm.R.evalFam r) :=
      continuous_pi fun l => MvPolynomial.continuous_eval (p := r l)
    have hT : IsOpen (U ∩ ReciprocityTheory.AnForm.R.evalFam r ⁻¹' {u | ‖u‖ < ε / 2}) :=
      hU.inter (isOpen_lt continuous_norm continuous_const |>.preimage hev)
    have := hf.isOpen_inter_preimage hA hT
    exact this
  · show ‖ReciprocityTheory.AnForm.R.evalFam r p‖ < ε / 2
    rw [hr0', norm_zero]; positivity
  · rintro z ⟨⟨hzc, hzU, hzn⟩, hzm⟩
    obtain ⟨hv1, hv2⟩ := hsolve _ ⟨hzU, hcone z hzm hzc⟩
    set v := ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) with hv
    set u := ReciprocityTheory.AnForm.R.evalFam r v with hu
    refine ⟨(ε : ℂ)⁻¹ • u, ?_, fun k => z ⟨k, c k⟩, hzc, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      rw [inv_mul_le_iff₀ hε]
      linarith
    · funext q
      show z q = z ⟨q.1, c q.1⟩ * g ((ε : ℂ) • (ε : ℂ)⁻¹ • u) (e q)
      rw [smul_inv_smul₀ hεc, hv2]
      have hvq : v (e q) = ReciprocityTheory.AnForm.R.affCoord c z q := by
        show ReciprocityTheory.AnForm.R.affCoord c z (e.symm (e q)) = _
        rw [Equiv.symm_apply_apply]
      rw [hvq]
      simp only [ReciprocityTheory.AnForm.R.affCoord]
      rw [mul_div_cancel₀ _ (hzc q.1)]

end GlobalTheory.CompanionTheory.Ar.ChartParams
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreProductAffineChartStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segre_product_affine_chart : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (N r : ℕ) (Z : Scheme.{0}) (j : Z ⟶ pullback (PSpace.str ℚ N) (PSpace.str ℚ r)) [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z) (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0) (h₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx) (h₂ : ζ ≫ j ≫ pullback.snd _ _ = point ℚ x' hx') (a : Fin (N + 1)) (l : Fin (r + 1)) (ha : x a ≠ 0) (hl : x' l ≠ 0), IsAffineOpen ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) ∧ ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l), Set.range (valMap ζ _ h).hom = Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart.prod_chart | exact GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart.prod_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart.prod_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothAlgebraEqZeroOfVanishOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_algebra_eq_zero_of_vanish_open : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ)) (f : Fin D → A) (a : A), IsOpen O → O.Nonempty → (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.eq_zero_of_forall_points_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.eq_zero_of_forall_points_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.eq_zero_of_forall_points_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoordsStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_of_smooth_coords : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z) (hsm : SmoothOfRelativeDimension e g) (hc : HasSncCoords g e T) (W : Z.Opens) (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ), SncChart A e (valR ζ W σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.sncChart_of_coords | exact GlobalTheory.CompanionTheory.Ar.SncRes.sncChart_of_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.sncChart_of_coords <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPointsTransferDominatingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_points_transfer_dominating : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ₁ κ₂ : Type) (x₁ : κ₁ → Ω) (x₂ : κ₂ → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (g : X₂ ⟶ X₁) (e : ℕ) (Ab : Set X₁), (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ x₁ → CoordTie ℤ ξ₂ x₂ → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SncPts ξ₁ e {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} → SncPts ξ₂ e {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt | exact GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothBasicOpenStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_smooth_basic_open : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (W : Z.Opens) (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (g₀ : A) (hg : (g₀ : Ω) = valR ζ W σ) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)], SmoothOfRelativeDimension e ((Z.basicOpen σ).ι ≫ g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.smoothOfRelativeDimension_basicOpen_of_away | exact GlobalTheory.CompanionTheory.Ar.SncRes.smoothOfRelativeDimension_basicOpen_of_away | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.smoothOfRelativeDimension_basicOpen_of_away <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorEquivOfBasisExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_equiv_of_basis_extension : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (V V' : Type) [AddCommGroup V]
    [Module Ω₀ V] [AddCommGroup V'] [Module Ω V'] (j : V →+ V'),
    (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω₀ Ω a • j e) →
    (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) →
    Submodule.span Ω (Set.range j) = ⊤ →
    ∃ Φ : TensorProduct Ω₀ Ω V ≃ₗ[Ω] V', ∀ e, Φ (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.exists_tensor_equiv_of_semilinear | exact GlobalTheory.CompanionTheory.Ar.FlagStep.exists_tensor_equiv_of_semilinear | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.exists_tensor_equiv_of_semilinear <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSectionEqOfConnectedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_section_eq_of_connected : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1 ∧ (x b).left ≫ G.hom = (x' b).left ≫ G.hom) → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → ∀ b ∈ B, GlobalTheory.UU.CubWeil c N (x b) (x' b) (unitOn ζ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.cubWeil_const_of_isHolTo_family | exact GlobalTheory.CompanionTheory.Ar.Flat.cubWeil_const_of_isHolTo_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.cubWeil_const_of_isHolTo_family <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusInjectiveLieMap
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TsClosed

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

theorem exists_transport (u : splitTorus S X ⟶ G) {A : Type} [CommRing A] {a a' : Sp A ⟶ S} (e : a = a')
    (t : Over.mk a ⟶ splitTorus S X) :
    ∃ t' : Over.mk a' ⟶ splitTorus S X, (∀ χ, charVal t' χ = charVal t χ) ∧ (t' ≫ u = 1 → t ≫ u = 1) := by
  subst e
  exact ⟨t, fun _ => rfl, id⟩

theorem killsOver_comp (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) {B B' : Type} [CommRing B] [CommRing B']
    (b : Sp B ⟶ S) (c : B →+* B') (h : KillsOver u Y b) : KillsOver u Y (spMap c ≫ b) := by
  intro A _ g t ht
  have e : spMap g ≫ spMap c ≫ b = spMap (g.comp c) ≫ b := by
    rw [← Category.assoc, spMap_comp_eq]
  obtain ⟨t', h1, h2⟩ := exists_transport u e t
  exact h2 (h A (g.comp c) t' fun y hy => by rw [h1]; exact ht y hy)

theorem killsOver_pow (u : splitTorus S X ⟶ G) [IsMonHom u] (Y : AddSubgroup X) {R : Type} [CommRing R]
    [IsLocalRing R] (b : Sp R ⟶ S) (h : KillsOver u Y (spMap (IsLocalRing.residue R) ≫ b)) (n : ℕ) :
    KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b) := by
  induction n with
  | zero =>
    let c : IsLocalRing.ResidueField R →+* R ⧸ (IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.lift _ (Ideal.Quotient.mk _)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha))
    have hc : c.comp (IsLocalRing.residue R) = Ideal.Quotient.mk _ := by
      ext x; rfl
    have key := killsOver_comp u Y _ c h
    rw [← Category.assoc, spMap_comp_eq, hc] at key
    exact key
  | succ n ih =>
    have hJ : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≠ ⊤ := by
      intro e
      have h1 : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≤ IsLocalRing.maximalIdeal R :=
        Ideal.pow_le_self (by omega)
      rw [e] at h1
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 h1)
    haveI : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      Ideal.Quotient.nontrivial_iff.2 hJ
    haveI : IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    let I : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      (IsLocalRing.maximalIdeal R ^ (n + 1)).map (Ideal.Quotient.mk _)
    have hI : I ^ 2 = ⊥ := by
      simp only [I]
      rw [← Ideal.map_pow, ← pow_mul, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      exact Ideal.pow_le_pow_right (by omega)
    refine GlobalTheory.T.killsOver_square_zero_lift S G X u Y _ _ I hI ?_
    let c : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)) →+*
        (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) ⧸ I :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp (Ideal.Quotient.mk _))
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))
    have hc : c.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk I).comp (Ideal.Quotient.mk _) := by
      ext x; rfl
    have key := killsOver_comp u Y _ c ih
    rw [← Category.assoc, spMap_comp_eq, hc, ← spMap_comp_eq, Category.assoc] at key
    exact key

theorem diff_injective_mod_pi : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ M : LieModel (splitTorus S X) (spMap (IsLocalRing.residue R) ≫ b) (X →+ IsLocalRing.ResidueField R), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  intro R K _ _ _ _ _ _ S b G _ _ X _ _ u _ hK M hM δ hδ
  by_contra hne
  obtain ⟨l, hl, ψ, hψ, hk⟩ := GlobalTheory.T.torus_kernel_prime_quotient S G X u (IsLocalRing.ResidueField R)
    (spMap (IsLocalRing.residue R) ≫ b) M hM δ hne hδ
  have hR := GlobalTheory.T.killsOver_of_adic_completion S G X u ψ.ker R b (killsOver_pow u ψ.ker b hk)
  have hKk := killsOver_comp u ψ.ker b (algebraMap R K) hR
  haveI := Fact.mk hl
  obtain ⟨-, -, h1, -, hex, -⟩ := GlobalTheory.T.charVal_multiplicative S X (AddMonoidAlgebra K (ZMod l))
    (spMap (algebraMap K (AddMonoidAlgebra K (ZMod l))) ≫ spMap (algebraMap R K) ≫ b)
  let w : Multiplicative X →* AddMonoidAlgebra K (ZMod l) :=
    (AddMonoidAlgebra.of K (ZMod l)).comp (AddMonoidHom.toMultiplicative ψ)
  obtain ⟨t, ht⟩ := hex w
  have hu : t ≫ u = 1 := hKk _ (algebraMap K (AddMonoidAlgebra K (ZMod l))) t fun y hy => by
    rw [ht]
    have hy0 : ψ y = 0 := hy
    simp [w, hy0, AddMonoidAlgebra.one_def]
  have ht1 := hK _ (algebraMap K (AddMonoidAlgebra K (ZMod l))) t hu
  obtain ⟨χ, hχ⟩ := hψ 1
  have key := ht χ
  rw [ht1, h1] at key
  simp only [w, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, hχ] at key
  rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_left_inj one_ne_zero] at key
  exact zero_ne_one key

end GlobalTheory.CompanionTheory.Ar.TsClosed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusOverLieModelBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_over_lie_model_base_change : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (τ : TorusExtension G) (τ' : TorusExtension G'), IsGrpPullback G' G (spMap e) φ → GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.TorusOver e τ τ' φ → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → ∀ I : AddSubgroup V, (letI := τ.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L), IsCocharLie MT ∧ ∀ x, x ∈ I ↔ ∃ δ : τ.X →+ ℤ, MV.pt x = MT.pt ((Int.castAddHom L).comp δ) ≫ τ.i) → (letI := τ'.addCommGroup; ∃ MT : LieModel (splitTorus (Sp L') τ'.X) (𝟙 _) (τ'.X →+ L'), IsCocharLie MT ∧ ∀ x, x ∈ I.map j ↔ ∃ δ : τ'.X →+ ℤ, MV'.pt x = MT.pt ((Int.castAddHom L').comp δ) ≫ τ'.i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC.cochars_baseChange | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC.cochars_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.CocharsBC.cochars_baseChange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusSplitPullbackGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_split_pullback_generic : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare <;> assumption)
end

