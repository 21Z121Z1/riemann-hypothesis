import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviChartRegularityStatementHolds
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0160
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0120

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContinuousAtOfHolo
section
open Filter Topology Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)

namespace LevelTowerAlt.Charts

theorem an_of_diff {σ τ : Type} [Fintype σ] [Fintype τ] {U : Set (σ → ℂ)} {f : (σ → ℂ) → τ → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := fun x hx => analyticAt_pi_iff.2 fun i =>
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ParametricCircleIntegralAnalytic.analyticOnNhd_of_differentiableOn_fd hU
    (differentiableOn_pi.1 hf i) x hx

theorem an_star_star {σ τ : Type} [Fintype σ] [Fintype τ] {U : Set (σ → ℂ)} {f : (σ → ℂ) → τ → ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) : AnalyticOnNhd ℂ (fun t => star (f (star t))) (star ⁻¹' U) :=
  an_of_diff (hU.preimage continuous_star) fun t ht => by
    have := (hf (star t) ht).differentiableAt.star_star
    rw [star_star] at this
    exact this.differentiableWithinAt

theorem continuousAt_of_holo {n : ℕ} {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : FinHolAtlas n X} {U : Set X} {f : X → E}
    (hf : ∀ j, AnalyticOnNhd ℂ (f ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {x : X} (hx : x ∈ U) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 := (hf j (A.chart j x) ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hx]⟩).continuousAt
  refine (h1.comp ((A.chart j).continuousAt hj)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

section Good

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {n : ℕ}

structure Good (P : Ideal (MRing J)) (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) : Prop where
  an : AnalyticOnNhd ℂ γ (ball 0 1)
  mem : ∀ t ∈ ball (0 : Fin n → ℂ) 1, γ t ∈ mcPts P
  inj : ∀ t ∈ ball (0 : Fin n → ℂ) 1, ∀ t' ∈ ball (0 : Fin n → ℂ) 1,
    ∀ c : K → ℂ, (∀ k, c k ≠ 0) → γ t = torusSmul c (γ t') → t = t'
  loc : ∀ t₀ ∈ ball (0 : Fin n → ℂ) 1, ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin n → ℂ),
    IsOpen V ∧ γ t₀ ∈ V ∧ AnalyticOnNhd ℂ T V ∧ T (γ t₀) = t₀ ∧
      ∀ z ∈ V ∩ mcPts P, T z ∈ ball 0 1 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (γ (T z))

variable {P : Ideal (MRing J)} {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ}

theorem Good.affine (h : Good P γ) {t₀ : Fin n → ℂ} {ε : ℝ} (h₀ : ‖t₀‖ ≤ 1 / 2) (hε : 0 < ε) (hε' : ε ≤ 1 / 4) :
    Good P fun t => γ (t₀ + (ε : ℂ) • t) := by
  have hb : ∀ t ∈ ball (0 : Fin n → ℂ) 1, t₀ + (ε : ℂ) • t ∈ ball (0 : Fin n → ℂ) 1 := fun t ht =>
    SncPiece.add_smul_mem_ball h₀ hε hε' ((mem_ball_zero_iff.1 ht).trans one_lt_two)
  have hne : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε.ne'
  refine ⟨fun t ht => (h.an _ (hb t ht)).comp_of_eq
      (analyticAt_const.add (analyticAt_id.const_smul (c := (ε : ℂ)))) rfl, fun t ht => h.mem _ (hb t ht),
    fun t ht t' ht' c hc e => smul_right_injective _ hne (add_left_cancel (h.inj _ (hb t ht) _ (hb t' ht') c hc e)),
    fun s hs => ?_⟩
  obtain ⟨V, T, hV, hm, hT, hTe, hz⟩ := h.loc _ (hb s hs)
  refine ⟨V ∩ T ⁻¹' ball t₀ ε, fun z => (ε : ℂ)⁻¹ • (T z - t₀),
    hT.continuousOn.isOpen_inter_preimage hV isOpen_ball, ⟨hm, ?_⟩,
    fun z hz => ((hT z hz.1).sub (analyticAt_const (v := t₀))).const_smul (c := (ε : ℂ)⁻¹), ?_, fun z hz' => ⟨?_, ?_⟩⟩
  · rw [mem_preimage, hTe, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hε.le]
    exact mul_lt_of_lt_one_right hε (mem_ball_zero_iff.1 hs)
  · simp only [hTe, add_sub_cancel_left, inv_smul_smul₀ hne]
  · have h1 : ‖T z - t₀‖ < ε := by simpa [dist_eq_norm] using hz'.1.2
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hε.le,
      inv_mul_lt_iff₀ hε, mul_one]
    exact h1
  · simp only [smul_inv_smul₀ hne, add_sub_cancel]
    exact (hz z ⟨hz'.1.1, hz'.2⟩).2

def cj (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun t => conjVec (γ (star t))

omit [Fintype K] [∀ k, Fintype (J k)] in
theorem cj_cj (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) : cj (cj γ) = γ := by
  funext t
  simp only [cj, star_star, SncPiece.conj_conj]

omit [Fintype K] [∀ k, Fintype (J k)] in
theorem conj_torus (c : K → ℂ) (z : (Σ k, J k) → ℂ) :
    conjVec (torusSmul c z) = torusSmul (fun k => starRingEnd ℂ (c k)) (conjVec z) := by
  funext p
  simp [conjVec, torusSmul]

theorem star_mem_ball {t : Fin n → ℂ} {r : ℝ} : star t ∈ ball (0 : Fin n → ℂ) r ↔ t ∈ ball (0 : Fin n → ℂ) r := by
  simp only [mem_ball_zero_iff, norm_star]

theorem Good.cj (h : Good P γ) : Good P (cj γ) := by
  refine ⟨fun t ht => an_star_star isOpen_ball h.an t (star_mem_ball.2 ht),
    fun t ht => SncPiece.conj_mem (h.mem _ (star_mem_ball.2 ht)), fun t ht t' ht' c hc e => ?_, fun s hs => ?_⟩
  · have e' := congrArg conjVec e
    simp only [Charts.cj, conj_torus, SncPiece.conj_conj] at e'
    exact star_injective (h.inj _ (star_mem_ball.2 ht) _ (star_mem_ball.2 ht') _
      (fun k => (map_ne_zero _).2 (hc k)) e')
  · obtain ⟨V, T, hV, hm, hT, hTe, hz⟩ := h.loc _ (star_mem_ball.2 hs)
    have hcc : star (Charts.cj γ s) = γ (star s) := SncPiece.conj_conj _
    refine ⟨star ⁻¹' V, fun z => star (T (star z)), hV.preimage continuous_star, by rwa [mem_preimage, hcc],
      an_star_star hV hT, by simp only [hcc, hTe, star_star], fun z hz' => ?_⟩
    obtain ⟨h1, c, hc, e⟩ := hz (conjVec z) ⟨hz'.1, SncPiece.conj_mem hz'.2⟩
    refine ⟨star_mem_ball.2 h1, fun k => starRingEnd ℂ (c k), fun k => (map_ne_zero _).2 (hc k), ?_⟩
    have e' := congrArg conjVec e
    rw [SncPiece.conj_conj, conj_torus] at e'
    simp only [Charts.cj, star_star]
    exact e'

theorem sec_diff (M : CxModel P n) (L : HermLine J) {U U' : Set M.Xc} (hU : IsOpen U) (hU' : IsOpen U')
    {s s' : M.Xc → (Σ k, J k) → ℂ} (hs : ∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y)
    (hs' : ∀ y ∈ U', s' y ∈ mcPts P ∧ M.proj (s' y) = y) (hh : ∀ p, M.atlas.HoloOn U fun y => s y p)
    (hh' : ∀ p, M.atlas.HoloOn U' fun y => s' y p) {y : M.Xc} (hy' : y ∈ U ∩ U') :
    ∃ W : Set M.Xc, IsOpen W ∧ y ∈ W ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn W G ∧
      ∀ z ∈ W ∩ U ∩ U', Real.log (L.h (s z)) - Real.log (L.h (s' z)) = (G z).re := by
  classical
  have ext : ∀ z ∈ U ∩ U', ∃ t : K → ℂ, (∀ k, t k ≠ 0) ∧ s z = fun q => t q.1 * s' z q := fun z hz =>
    (M.fibre _ (hs' z hz.2).1 _ (hs z hz.1).1).mp ((hs' z hz.2).2.trans (hs z hz.1).2.symm)
  choose p hp using (hs' y hy'.2).1.1
  obtain ⟨c, hc, hcy⟩ := ext y hy'
  have hnum : ∀ k, s y ⟨k, p k⟩ ≠ 0 := fun k => by
    rw [hcy]; exact mul_ne_zero (hc k) (hp k)
  have hr : ∀ k, s y ⟨k, p k⟩ / s' y ⟨k, p k⟩ ≠ 0 := fun k => div_ne_zero (hnum k) (hp k)
  have hO : IsOpen (U ∩ U') := hU.inter hU'
  let q : K → M.Xc → ℂ := fun k z => s z ⟨k, p k⟩ / s' z ⟨k, p k⟩ / (s y ⟨k, p k⟩ / s' y ⟨k, p k⟩)
  let W : Set M.Xc := {z | z ∈ U ∩ U' ∧ ∀ k, s' z ⟨k, p k⟩ ≠ 0 ∧ q k z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ∀ k, ContinuousAt (fun z => s z ⟨k, p k⟩) z := fun k => continuousAt_of_holo (hh _) hz.1.1
    have hd : ∀ k, ContinuousAt (fun z => s' z ⟨k, p k⟩) z := fun k => continuousAt_of_holo (hh' _) hz.1.2
    filter_upwards [hO.mem_nhds hz.1, eventually_all.mpr fun k => (hd k).eventually_ne (hz.2 k).1,
      eventually_all.mpr fun k => (((hn k).div (hd k) (hz.2 k).1).div_const _).eventually_mem
        (Complex.isOpen_slitPlane.mem_nhds (hz.2 k).2)] with w h1 h2 h3
    exact ⟨h1, fun k => ⟨h2 k, h3 k⟩⟩
  have hyW : y ∈ W := by
    refine ⟨hy', fun k => ⟨hp k, ?_⟩⟩
    have : q k y = 1 := div_self (hr k)
    rw [this]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
  let G : M.Xc → ℂ := fun z => ∑ k, ((L.a k : ℝ) : ℂ) *
    (Complex.log (q k z) + ((Real.log ‖s y ⟨k, p k⟩ / s' y ⟨k, p k⟩‖ : ℝ) : ℂ))
  refine ⟨W, hW, hyW, G, fun j y' hy'' => ?_, fun z hz => ?_⟩
  · have hz : (M.atlas.chart j).symm y' ∈ W := hy''.2
    have hterm : ∀ k, AnalyticAt ℂ (fun y'' => ((L.a k : ℝ) : ℂ) *
        (Complex.log (q k ((M.atlas.chart j).symm y'')) +
          ((Real.log ‖s y ⟨k, p k⟩ / s' y ⟨k, p k⟩‖ : ℝ) : ℂ))) y' := by
      intro k
      have hn : AnalyticAt ℂ (fun y'' => s ((M.atlas.chart j).symm y'') ⟨k, p k⟩) y' :=
        hh _ j y' ⟨hy''.1, hz.1.1⟩
      have hd : AnalyticAt ℂ (fun y'' => s' ((M.atlas.chart j).symm y'') ⟨k, p k⟩) y' :=
        hh' _ j y' ⟨hy''.1, hz.1.2⟩
      have hq : AnalyticAt ℂ (fun y'' => q k ((M.atlas.chart j).symm y'')) y' :=
        (hn.div hd (hz.2 k).1).div analyticAt_const (hr k)
      have hl : AnalyticAt ℂ (Complex.log ∘ fun y'' => q k ((M.atlas.chart j).symm y'')) y' :=
        AnalyticAt.comp (f := fun y'' => q k ((M.atlas.chart j).symm y''))
          (analyticAt_clog (hz.2 k).2) hq
      exact analyticAt_const.mul (hl.add analyticAt_const)
    exact Finset.analyticAt_fun_sum _ fun k _ => hterm k
  · have hzW : z ∈ W := hz.1.1
    obtain ⟨c', hc', hcz⟩ := ext z hzW.1
    have hpos : 0 < L.h (s' z) := L.pos _ (hs' z hzW.1.2).1.1
    have hprod : (∏ k, ‖c' k‖ ^ L.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))
    have hterm : ∀ k, Real.log ‖q k z‖ + Real.log ‖s y ⟨k, p k⟩ / s' y ⟨k, p k⟩‖ = Real.log ‖c' k‖ := by
      intro k
      have hqz : q k z = c' k / (s y ⟨k, p k⟩ / s' y ⟨k, p k⟩) := by
        simp only [q]
        rw [hcz, mul_div_assoc, div_self (hzW.2 k).1, mul_one]
      rw [hqz, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k)) (norm_ne_zero_iff.mpr (hr k))]
      ring
    rw [hcz, L.smul c' _ hc', Real.log_mul hprod hpos.ne', add_sub_cancel_right,
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))]
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re, Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k, Real.log_zpow]

end Good

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} (M : XModel D) {γ : (Fin D.n → ℂ) → (Σ k, J k) → ℂ}

theorem Good.locInv (h : Good (mCoordIdeal D.y) γ) {t₀ : Fin D.n → ℂ} (ht : t₀ ∈ ball (0 : Fin D.n → ℂ) 1) :
    ∃ U : Set M.Xc, IsOpen U ∧ M.proj (γ t₀) ∈ U ∧ ∃ ψ : M.Xc → Fin D.n → ℂ,
      (∀ j, AnalyticOnNhd ℂ (ψ ∘ (M.atlas.chart j).symm)
        ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' U)) ∧
      ∀ x ∈ U, ψ x ∈ ball (0 : Fin D.n → ℂ) 1 ∧ M.proj (γ (ψ x)) = x := by
  obtain ⟨V, T, hV, hm, hT, -, hz⟩ := h.loc t₀ ht
  obtain ⟨U, hU, hx, s, hs, hh⟩ := M.sections (M.proj (γ t₀))
  obtain ⟨c, hc, e⟩ := (M.fibre _ (hs _ hx).1 _ (h.mem _ ht)).1 (hs _ hx).2
  have hs' : ∀ j, AnalyticOnNhd ℂ ((fun x => torusSmul c (s x)) ∘ (M.atlas.chart j).symm)
      ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' U) := fun j y hy =>
    analyticAt_pi_iff.2 fun p => analyticAt_const.mul (hh p j y hy)
  have hmem : ∀ x ∈ U, torusSmul c (s x) ∈ mcPts (mCoordIdeal D.y) := fun x hx =>
    mcPts_smul D.arith.2.1.2.1 c hc (hs x hx).1
  refine ⟨U ∩ (fun x => torusSmul c (s x)) ⁻¹' V, ContinuousOn.isOpen_inter_preimage
    (fun x hx => (continuousAt_of_holo hs' hx).continuousWithinAt) hU hV, ⟨hx, by rw [mem_preimage, ← e]; exact hm⟩,
    fun x => T (torusSmul c (s x)), fun j y hy => (hT _ hy.2.2).comp_of_eq (hs' j y ⟨hy.1, hy.2.1⟩) rfl,
    fun x hx => ?_⟩
  obtain ⟨h1, c', hc', e'⟩ := hz _ ⟨hx.2, hmem x hx.1⟩
  refine ⟨h1, ?_⟩
  rw [(M.fibre _ (h.mem _ h1) _ (hmem x hx.1)).2 ⟨c', hc', e'⟩,
    ← (M.fibre _ (hs x hx.1).1 _ (hmem x hx.1)).2 ⟨c, hc, rfl⟩, (hs x hx.1).2]

theorem Good.exists_chart (h : Good (mCoordIdeal D.y) γ) :
    ∃ e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ), e.target = ball 0 1 ∧ (∀ t, e.symm t = M.proj (γ t)) ∧
      IsCompatChart M.atlas e := by
  let g : (Fin D.n → ℂ) → M.Xc := fun t => M.proj (γ t)
  have hinj : InjOn g (ball 0 1) := fun t ht t' ht' e => by
    obtain ⟨c, hc, e'⟩ := (M.fibre _ (h.mem _ ht') _ (h.mem _ ht)).1 e.symm
    exact h.inj t ht t' ht' c hc e'
  have hloc : ∀ x ∈ g '' ball 0 1, ∃ U : Set M.Xc, IsOpen U ∧ x ∈ U ∧ U ⊆ g '' ball 0 1 ∧
      ∀ j, AnalyticOnNhd ℂ (Function.invFunOn g (ball 0 1) ∘ (M.atlas.chart j).symm)
        ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' U) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨U, hU, hx, ψ, hψ, hi⟩ := h.locInv M ht
    refine ⟨U, hU, hx, fun x hx => ⟨ψ x, hi x hx⟩, fun j => ?_⟩
    refine (hψ j).congr ((M.atlas.chart j).isOpen_inter_preimage_symm hU) fun y hy => ?_
    have h1 := hi _ hy.2
    have h2 := hinj.leftInvOn_invFunOn h1.1
    simp only [g, h1.2] at h2
    exact h2.symm
  have hall : ∀ j, AnalyticOnNhd ℂ (Function.invFunOn g (ball 0 1) ∘ (M.atlas.chart j).symm)
      ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (g '' ball 0 1)) := fun j y hy => by
    obtain ⟨U, -, hx, -, ha⟩ := hloc _ hy.2
    exact ha j y ⟨hy.1, hx⟩
  refine ⟨{ toPartialEquiv := (hinj.toPartialEquiv g (ball 0 1)).symm
            open_source := ?_
            open_target := isOpen_ball
            continuousOn_toFun := fun x hx => (continuousAt_of_holo hall hx).continuousWithinAt
            continuousOn_invFun := M.cont.comp h.an.continuousOn h.mem }, rfl, fun _ => rfl,
    fun j => ⟨hall j, fun t ht => ?_⟩⟩
  · refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    obtain ⟨U, hU, hxU, hsub, -⟩ := hloc x hx
    exact mem_of_superset (hU.mem_nhds hxU) hsub
  · have ht1 : t ∈ ball (0 : Fin D.n → ℂ) 1 := ht.1
    obtain ⟨V, hV, hz, F, hF, hFe⟩ := GlobalTheory.CompanionTheory.Ar.Giv.projHoloLocal II Ψ K J Ω W D M (M.atlas.chart j)
      (fun k => ⟨M.atlas.holo k j, M.atlas.holo j k⟩) (γ t) (h.mem t ht1) ht.2
    refine (((an_of_diff hV hF) _ hz).comp (h.an t ht1)).congr ?_
    filter_upwards [isOpen_ball.mem_nhds ht1, (h.an t ht1).continuousAt.preimage_mem_nhds (hV.mem_nhds hz)]
      with t' h1 h2
    exact ((hFe _ ⟨h2, h.mem t' h1⟩).2).symm

end LevelTowerAlt.Charts
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.FinrankOfLieMult
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open TensorProduct

namespace LevelTowerAlt

theorem mem_eigSp {R W O : Type} [CommRing R] [AddCommGroup W] [Module R W] [CommRing O] (ρ : O →+* Module.End R W)
    (σ : O →+* R) (x : W) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem eigSp_baseChange {E : Type} [Field E] [NumberField E] {O R M W : Type} [CommRing O] [CommRing R] [Algebra O R]
    [Module.Flat O R] [AddCommGroup M] [Module O M] [AddCommGroup W] [Module R W] [Module O W] [IsScalarTower O R W]
    (j : M →ₗ[O] W) (hj : IsBaseChange R j) (ρM : 𝓞 E →+* Module.End O M) (ρW : 𝓞 E →+* Module.End R W)
    (h : ∀ a z, ρW a (j z) = j (ρM a z)) (s : 𝓞 E →+* O) :
    eigSp ρW ((algebraMap O R).comp s) = Submodule.span R (j '' (eigSp ρM s : Set M)) := by
  classical
  refine le_antisymm (fun w hw => ?_) (Submodule.span_le.2 ?_)
  · let b := RingOfIntegers.basis E
    let Φ := fun i => ρM (b i) - s (b i) • (LinearMap.id : M →ₗ[O] M)
    have hker : LinearMap.ker (LinearMap.pi Φ) ≤ eigSp ρM s := by
      intro z hz
      have h1 : ∀ i, ρM (b i) z = s (b i) • z := fun i => sub_eq_zero.1 (congrFun hz i)
      rw [mem_eigSp]
      intro a
      rw [← b.sum_repr a]
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, h1, Finset.sum_smul, smul_assoc]
    obtain ⟨u, rfl⟩ := hj.equiv.surjective w
    have h2 : ∀ i (u : R ⊗[O] M), hj.equiv ((Φ i).lTensor R u) =
        ρW (b i) (hj.equiv u) - algebraMap O R (s (b i)) • hj.equiv u := by
      intro i u
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r z =>
        rw [LinearMap.lTensor_tmul, hj.equiv_tmul, hj.equiv_tmul, map_smul, h, smul_comm, ← smul_sub, algebraMap_smul,
          ← j.map_smul, ← j.map_sub]
        rfl
      | add x y hx hy =>
        rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
        abel
    have h3 : ∀ i, (Φ i).lTensor R u = 0 := fun i => by
      apply hj.equiv.injective
      rw [h2, map_zero, (mem_eigSp _ _ _).1 hw]
      exact sub_self _
    have h4 : LinearMap.pi Φ = ∑ i, LinearMap.single O (fun _ => M) i ∘ₗ Φ i := by
      ext z i
      simp [Finset.sum_apply, Pi.single_apply]
    have h5 : (LinearMap.pi Φ).lTensor R u = 0 := by
      rw [h4, ← LinearMap.coe_lTensorHom, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.coe_lTensorHom, LinearMap.lTensor_comp, LinearMap.comp_apply, h3, map_zero]
    obtain ⟨u', rfl⟩ := (Module.Flat.lTensor_exact R (LinearMap.exact_subtype_ker_map (LinearMap.pi Φ)) u).1 h5
    clear hw h3 h5
    induction u' using TensorProduct.induction_on with
    | zero => simp
    | tmul r z =>
      rw [LinearMap.lTensor_tmul, hj.equiv_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hker z.2, rfl⟩)
    | add x y hx hy =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hx hy
  · rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp] at hz ⊢
    intro a
    rw [h, hz, map_smul, RingHom.comp_apply, algebraMap_smul]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

theorem spDual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← spMap_comp]
  congr 1
  exact RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem spDual_alg {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ spMap (algebraMap A (DualNumber A)) = spMap (algebraMap B (DualNumber B)) ≫ spMap f := by
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  exact RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem left_eq_of_cart {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) {x : Sp A ⟶ S'} {x' : Sp B ⟶ S'} (hx : x' = spMap g ≫ x)
    (v : epsAt x ⟶ t'.G) (v' : epsAt x' ⟶ t'.G) (h : v'.left ≫ m.φ = spMap (dualMap g) ≫ v.left ≫ m.φ) :
    v'.left = spMap (dualMap g) ≫ v.left := by
  refine m.cart.1.hom_ext (h.trans (Category.assoc _ _ _).symm) ?_
  have h1 : v'.left ≫ t'.G.hom = spMap (algebraMap B (DualNumber B)) ≫ x' := Over.w v'
  have h2 : v.left ≫ t'.G.hom = spMap (algebraMap A (DualNumber A)) ≫ x := Over.w v
  rw [h1, Category.assoc, h2, ← Category.assoc, spDual_alg, hx, Category.assoc]

theorem push_model {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {R : Type} [CommRing R] {x' : Sp R ⟶ S'} {x : Sp R ⟶ S} (hx : x = x' ≫ f) {W : Type} [AddCommGroup W] [Module R W]
    (M' : LieModel t'.G x' W) (ρ : 𝓞 E →+* Module.End R W) (hρ : M'.IsActOf t'.act.act ρ) :
    ∃ M : LieModel t.G x W, M.IsActOf t.act.act ρ ∧ ∀ u, (M'.pt u).left ≫ m.φ = (M.pt u).left := by
  subst hx
  obtain ⟨M, hM⟩ := (GlobalTheory.T.lie_model_pullback_equivalence S S' t.G t'.G f m.φ m.cart R x' W).2 M'
  refine ⟨M, fun a e => Over.OverMorphism.ext ?_, hM⟩
  rw [← hM, hρ a e, Over.comp_left, Over.comp_left, ← hM, Category.assoc, Category.assoc, m.act a]

variable {L : Type} [Field L] [NumberField L] {t' : SAB H (Sp (𝓞 L))} {M : Type} [AddCommGroup M] [Module (𝓞 L) M]
  (MB : LieModel t'.G (𝟙 _) M) {ρM : 𝓞 E →+* Module.End (𝓞 L) M}

theorem exists_model (hρ : MB.IsActOf t'.act.act ρM) {S : Scheme.{0}} {t : SAB H S} {f : S ⟶ Sp (𝓞 L)}
    (m : SABMap t t' f) {R : Type} [CommRing R] [IsDomain R] (g : 𝓞 L →+* R) (hg : Function.Injective g)
    (x : Sp R ⟶ S) (hx : x ≫ f = spMap g) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (MW : LieModel t.G x W) (ρW : 𝓞 E →+* Module.End R W)
      (j : M →+ W), MW.IsActOf t.act.act ρW ∧
      (∀ z, (MW.pt (j z)).left ≫ m.φ = spMap (dualMap g) ≫ (MB.pt z).left) ∧ (∀ a z, j (a • z) = g a • j z) ∧
      ∀ (s : 𝓞 E →+* 𝓞 L) (n : ℕ) (y : Fin n → M), (∀ k, y k ∈ eigSp ρM s) → LinearIndependent (𝓞 L) y →
        (∀ z ∈ eigSp ρM s, ∃ u, IsUnit (g u) ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y)) →
        LinearIndependent R (fun k => j (y k)) ∧
          Submodule.span R (Set.range fun k => j (y k)) = eigSp ρW (g.comp s) := by
  letI : Algebra (𝓞 L) R := g.toAlgebra
  haveI : Smooth t'.G.hom := t'.semi.smooth
  obtain ⟨W, _, _, ⟨M₁⟩⟩ := lieModel_exists _ t'.G R (spMap g ≫ 𝟙 _)
  letI : Module (𝓞 L) W := Module.compHom W g
  haveI : IsScalarTower (𝓞 L) R W := ⟨fun a b e => by
    show (g a * b) • e = g a • b • e
    rw [mul_smul]⟩
  obtain ⟨j₀, hj₀, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear _ t'.G (𝓞 L) R g (𝟙 _) M W MB M₁
  let j : M →ₗ[𝓞 L] W := { toFun := j₀, map_add' := map_add j₀, map_smul' := fun a e => j₀.map_smulₛₗ a e }
  have hbc : IsBaseChange R j := GlobalTheory.T.lie_model_isBaseChange _ t'.G (𝓞 L) R (𝟙 _) M W MB M₁ j hj₀
  have key : ∀ (x₀ : Sp R ⟶ Sp (𝓞 L)) (M₀ : LieModel t'.G x₀ W), x₀ = x ≫ f →
      ∃ M' : LieModel t.G x W, ∀ e, (M'.pt e).left ≫ m.φ = (M₀.pt e).left := by
    rintro _ M₀ rfl
    exact (GlobalTheory.T.lie_model_pullback_equivalence _ S t'.G t.G f m.φ m.cart R x W).1 M₀
  obtain ⟨MW, hMW⟩ := key _ M₁ (by rw [hx, Category.comp_id])
  have hl : ∀ z, (MW.pt (j z)).left ≫ m.φ = spMap (dualMap g) ≫ (MB.pt z).left := fun z =>
    (hMW _).trans ((Category.comp_id _).symm.trans (hj₀ z))
  obtain ⟨ρW, hρW, -⟩ := lieModel_exists_unique_act S t.G R x W MW _ t.act.act t.act.hom t.act.one t.act.mul t.act.add
  have heq : ∀ a z, ρW a (j z) = j (ρM a z) := by
    intro a z
    refine MW.inj ?_
    rw [hρW a (j z)]
    refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ?_)
    · have h1 : (MB.pt (ρM a z)).left = (MB.pt z).left ≫ (t'.act.act a).left := by
        rw [hρ a z]
        rfl
      change ((MW.pt (j z)).left ≫ (t.act.act a).left) ≫ m.φ = (MW.pt (j (ρM a z))).left ≫ m.φ
      rw [Category.assoc, m.act a, ← Category.assoc, hl z, hl (ρM a z), h1, Category.assoc]
    · rw [Over.w, Over.w]
  haveI : Module.IsTorsionFree (𝓞 L) R := .of_smul_eq_zero fun a r h =>
    (mul_eq_zero.1 h).imp_left fun h0 => hg (h0.trans (map_zero g).symm)
  refine ⟨W, inferInstance, inferInstance, MW, ρW, j.toAddMonoidHom, hρW, hl, fun a z => j.map_smul a z,
    fun s n y hy hli hsp => ⟨?_, ?_⟩⟩
  · have h1 := (Module.Flat.linearIndependent_one_tmul (S := R) hli).map' hbc.equiv.toLinearMap hbc.equiv.ker
    have h2 : (hbc.equiv.toLinearMap ∘ fun k => (1 : R) ⊗ₜ[𝓞 L] y k) = fun k => j (y k) := by
      funext k
      exact (hbc.equiv_tmul 1 (y k)).trans (one_smul _ _)
    rwa [h2] at h1
  · refine Eq.trans ?_ (eigSp_baseChange j hbc ρM ρW heq s).symm
    refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      exact ⟨y k, hy k, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨u, hu, h1⟩ := hsp z hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 L)).1 h1
      have h2 : g u • j z = ∑ k, g (c k) • j (y k) := by
        refine (j.map_smul u z).symm.trans ?_
        rw [← hc, map_sum]
        exact Finset.sum_congr rfl fun k _ => j.map_smul _ _
      refine (Submodule.smul_mem_iff_of_isUnit _ hu).1 ?_
      rw [h2]
      exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem finrank_of_lieMult {S : Scheme.{0}} {t : SAB H S} {k : Type} [Field k] {x : Sp k ⟶ S} {W : Type}
    [AddCommGroup W] [Module k W] (MW : LieModel t.G x W) {ρW : 𝓞 E →+* Module.End k W}
    (hρ : MW.IsActOf t.act.act ρW) {τ : 𝓞 E →+* k} {n : ℕ} (h : LieMult t.act x τ n) :
    Module.finrank k (eigSp ρW τ) = n := by
  obtain ⟨v, hv⟩ := h
  have hv' : IsEigFrame t.act x τ v := hv
  choose u hu using fun i => MW.onto (v i) (hv'.1 i).1
  have e : v = fun i => MW.pt (u i) := funext fun i => (hu i).symm
  rw [e] at hv'
  obtain ⟨h1, h2⟩ := (((GlobalTheory.T.lie_model_eigenvectors_action S k t.G x W MW).2 _ t.act ρW τ hρ).2 n u).1 hv'
  rw [← h2, finrank_span_eq_card h1, Fintype.card_fin]

end LevelTowerAlt
end

