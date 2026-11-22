import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0074
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0126
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0008
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import Development.WeilBound.CoreStatements.RationalSupMetrics.PullRatiosAlgebraic

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEigenFramePlurisubharmonic
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Corr

open ReciprocityTheory.AnForm.A (IsPsh)

theorem psh_add {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (hφ : IsPsh U φ) (hψ : IsPsh U ψ) :
    IsPsh U (fun z => φ z + ψ z) := by
  refine ⟨hφ.1.add hψ.1, fun z w hd => ?_⟩
  obtain ⟨h1, h2⟩ := hφ.2 z w hd
  obtain ⟨h3, h4⟩ := hψ.2 z w hd
  refine ⟨h1.add h3, ?_⟩
  rw [Real.circleAverage_fun_add h1 h3]
  exact add_le_add h2 h4

theorem psh_const {d : ℕ} (U : Set (Fin d → ℂ)) (c : ℝ) : IsPsh U (fun _ => c) := by
  refine ⟨upperSemicontinuousOn_const, fun z w _ => ⟨circleIntegrable_const c 0 1, ?_⟩⟩
  rw [Real.circleAverage_const]

theorem psh_sum {d : ℕ} {U : Set (Fin d → ℂ)} {ι : Type} (S : Finset ι) {f : ι → (Fin d → ℂ) → ℝ}
    (h : ∀ i ∈ S, IsPsh U (f i)) : IsPsh U (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using psh_const U 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact psh_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem psh_congr {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (h : ∀ z ∈ U, φ z = ψ z)
    (hφ : IsPsh U φ) : IsPsh U ψ := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in nhdsWithin z U, φ x < y := hφ.1 z hz y (by show φ z < y; rw [h z hz]; exact hy)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
    rwa [← h x hxU]
  · obtain ⟨h1, h2⟩ := hφ.2 z w hd
    have e : ∀ θ : ℝ, φ (z + circleMap 0 1 θ • w) = ψ (z + circleMap 0 1 θ • w) := fun θ =>
      h _ (hd _ (by simp))
    have hz : z ∈ U := by simpa using hd 0 (by simp)
    refine ⟨?_, ?_⟩
    · unfold CircleIntegrable at h1 ⊢
      simpa only [e] using h1
    · rw [← h z hz]
      simpa only [Real.circleAverage_def, e] using h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ]

noncomputable def term (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (F : Finset (Submodule (𝓞 E) Λ)) :
    Option F → ℝ
  | none => 0
  | some I => -Real.log (R.nz σ I.1)

theorem cuspW_eq (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (F : Finset (Submodule (𝓞 E) Λ))
    (h1 : ∀ I ∈ F, R.IsCusp I) (h2 : ∀ I, R.IsCusp I → R.nz σ I ≤ 1 → I ∈ F) :
    R.cuspW σ = Finset.univ.sup' Finset.univ_nonempty (term R σ F) := by
  have h0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F) :=
    Finset.le_sup' (term R σ F) (Finset.mem_univ none)
  have hb : ∀ x ∈ {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)},
      x ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F) := by
    rintro x ⟨I, hI, rfl⟩
    by_cases h : R.nz σ I ≤ 1
    · exact Finset.le_sup' (term R σ F) (Finset.mem_univ (some ⟨I, h2 I hI h⟩))
    · have := Real.log_nonneg (not_le.1 h).le
      linarith
  unfold RiemLat.cuspW
  refine le_antisymm (max_le h0 (Real.sSup_le hb h0)) (Finset.sup'_le _ _ fun o _ => ?_)
  cases o with
  | none => exact le_max_left _ _
  | some I => exact le_max_of_le_right (le_csSup ⟨_, hb⟩ ⟨I.1, h1 I.1 I.2, rfl⟩)

theorem add_sup {ι : Type} [Fintype ι] [Nonempty ι] (a : ℝ) (f : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun j => a + f j) = a + Finset.univ.sup' Finset.univ_nonempty f := by
  refine le_antisymm (Finset.sup'_le _ _ fun j hj => ?_) ?_
  · have := Finset.le_sup' f hj
    linarith
  · obtain ⟨j, hj, e⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) f
    rw [e]
    exact Finset.le_sup' (fun j => a + f j) hj

end GlobalTheory.CompanionTheory.Ar.Cusp.Corr

open GlobalTheory.CompanionTheory.Ar.Cusp.Corr in
theorem _root_.GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) ∧ ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧ ContinuousOn (fun t => (R t).cuspW σ) U := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m b hU hH hσ hb
  have hrank : ∀ t ∈ U, (R t).HasRank σ m := by
    intro t ht τ
    have h := hb.2 t ht τ
    have e : Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => b τ i t)) = m := by
      rw [finrank_span_eq_card h.1, Fintype.card_fin]
    rw [h.2] at e
    exact e
  have hL : ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) :=
    psh_sum Finset.univ fun τ _ =>
      (GlobalTheory.CompanionTheory.Relay.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hH).2.2 m (b τ) (hb.1 τ) (fun t ht => (hb.2 t ht τ).1)
  have hloc : ∀ t₀ ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ t₀ ∈ W ∧
      ReciprocityTheory.AnForm.A.IsPsh (U ∩ W) (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧
      ContinuousOn (fun t => (R t).cuspW σ) (U ∩ W) := by
    intro t₀ ht₀
    obtain ⟨ε, F, hε, hF⟩ := GlobalTheory.T.cusp_submodules_locally_finite E g Λ Ψ n U R σ m hU hH hσ hrank t₀ ht₀
    have hVo : IsOpen (U ∩ Metric.ball t₀ ε) := hU.inter Metric.isOpen_ball
    have hVU : U ∩ Metric.ball t₀ ε ⊆ U := Set.inter_subset_left
    have hphi := fun I : F => GlobalTheory.T.log_det_cusp_frame_plurisubharmonic E g Λ Ψ n (U ∩ Metric.ball t₀ ε) R σ m b I.1 hVo
      ⟨fun t ht t' ht' => hH.1 t ht.1 t' ht'.1, fun x => (hH.2 x).mono hVU⟩ hσ
      ⟨fun τ i => (hb.1 τ i).mono hVU, fun t ht => hb.2 t ht.1⟩ (fun t ht => (hF t ht).1 I.1 I.2)
    have heq : ∀ t ∈ U ∩ Metric.ball t₀ ε,
        (R t).cuspW σ = Finset.univ.sup' Finset.univ_nonempty (term (R t) σ F) :=
      fun t ht => cuspW_eq (R t) σ F (hF t ht).1 (hF t ht).2
    refine ⟨Metric.ball t₀ ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_, ?_⟩
    · have hs := ReciprocityTheory.AnForm.A.isPsh_sup_thm n (Option F) (U ∩ Metric.ball t₀ ε)
        (fun o t => (R t).logDet (fun τ i => b τ i t) + term (R t) σ F o) hVo (fun o => by
          cases o with
          | none =>
            exact psh_congr (fun z _ => (add_zero _).symm) (GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_mono hVU hL)
          | some I => exact psh_congr (fun z _ => sub_eq_add_neg _ _) (hphi I).1)
      refine psh_congr (fun t ht => ?_) hs
      rw [heq t ht]
      exact add_sup _ _
    · have hc : ∀ o : Option F, ContinuousOn (fun t => term (R t) σ F o) (U ∩ Metric.ball t₀ ε) := by
        intro o
        cases o with
        | none => exact continuousOn_const
        | some I =>
          refine ContinuousOn.neg ((hphi I).2.log fun t ht => ?_)
          have hI := (hF t ht).1 I.1 I.2
          obtain ⟨⟨r, v, hv⟩, h2⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I.1 hσ hI.2.2 hI.1
          exact (h2 r v hv).2.1.ne'
      have hs : ContinuousOn (fun t => Finset.univ.sup' Finset.univ_nonempty (fun o => term (R t) σ F o))
          (U ∩ Metric.ball t₀ ε) :=
        ContinuousOn.finset_sup'_apply Finset.univ_nonempty fun o _ => hc o
      exact hs.congr heq
  refine ⟨hL, GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally n U _ hU fun z hz => ?_,
    continuousOn_of_locally_continuousOn fun z hz => ?_⟩
  · obtain ⟨W, h1, h2, h3, -⟩ := hloc z hz
    exact ⟨U ∩ W, hU.inter h1, ⟨hz, h2⟩, h3⟩
  · obtain ⟨W, h1, h2, -, h4⟩ := hloc z hz
    exact ⟨W, h1, h2, h4⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositive
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace PosFs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fsHerm_one_h (y : (Σ k, ι k) → ℂ) :
    (fsHerm ι fun _ => 1).h y = (GroundTheory.Heights₂.Heights.fsMulti ι).h y := by
  rw [fsHerm_h]
  unfold refNorm
  simp only [GroundTheory.Heights₂.Heights.fsMulti, HermLine.ofMetrics, zpow_one]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ‖WithLp.toLp 2 (fun i => y ⟨k, i⟩)‖
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
  norm_num

theorem levi_fs_pos {z w : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    0 < levi (fun y => Real.log ((fsHerm ι fun _ => 1).h y)) z w := by
  have h := GlobalTheory.CompanionTheory.Ar.FS.levi_fsMulti_pos hz hw
  have e : (fun y => Real.log ((fsHerm ι fun _ => 1).h y)) =
      fun y => Real.log ((GroundTheory.Heights₂.Heights.fsMulti ι).h y) := by
    funext y
    rw [fsHerm_one_h]
  rw [e]
  exact h

theorem contDiffAt_log_h {A : HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have hopen : ∀ᶠ y in 𝓝 z, ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    refine Filter.eventually_all.mpr fun k => ?_
    obtain ⟨i, hi⟩ := hz k
    exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
      fun y hy => ⟨i, hy⟩
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h z := hA.contDiffAt hopen
  exact (h1.of_le (by first | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) | (rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) by norm_cast]; exact WithTop.coe_le_coe.2 le_top))).log (A.pos z hz).ne'

theorem fderiv_affCoord_torus {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {γ : E → (Σ k, ι k) → ℂ} {y : E} (p : (k : K) → ι k) (hγ : DifferentiableAt ℂ γ y)
    (hp : ∀ k, γ y ⟨k, p k⟩ ≠ 0) {w : E} {c : K → ℂ} (hc : fderiv ℂ γ y w = torusSmul c (γ y)) :
    fderiv ℂ (fun y' => affCoord p (γ y')) y w = 0 := by
  have hd := hγ.hasFDerivAt
  have hq : ∀ q : Σ k, ι k, HasFDerivAt (fun y' => γ y' q)
      ((ContinuousLinearMap.proj q).comp (fderiv ℂ γ y)) y := fun q => hasFDerivAt_pi'.1 hd q
  have hu : ∀ q : Σ k, ι k, HasFDerivAt (fun y' => affCoord p (γ y') q)
      ((γ y q) • ((-((γ y ⟨q.1, p q.1⟩) ^ 2)⁻¹) •
          ((ContinuousLinearMap.proj ⟨q.1, p q.1⟩).comp (fderiv ℂ γ y))) +
        ((γ y ⟨q.1, p q.1⟩)⁻¹) • ((ContinuousLinearMap.proj q).comp (fderiv ℂ γ y))) y := by
    intro q
    have hinv := (hasDerivAt_inv (hp q.1)).comp_hasFDerivAt y (hq ⟨q.1, p q.1⟩)
    have hm := (hq q).mul hinv
    refine hm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y' => ?_)
    simp [affCoord, div_eq_mul_inv]
  have hall : fderiv ℂ (fun y' => affCoord p (γ y')) y = ContinuousLinearMap.pi _ :=
    (hasFDerivAt_pi.2 hu).fderiv
  rw [hall]
  funext q
  have h1 : fderiv ℂ γ y w q = c q.1 * γ y q := congrFun hc q
  have h2 : fderiv ℂ γ y w ⟨q.1, p q.1⟩ = c q.1 * γ y ⟨q.1, p q.1⟩ := congrFun hc _
  have hr := hp q.1
  simp only [ContinuousLinearMap.coe_pi', ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    h1, h2, smul_eq_mul, Pi.zero_apply]
  field_simp
  ring

theorem isPosPot_fs (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D) :
    IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) := by
  classical
  intro x j y hy w hw
  obtain ⟨hyt, hyU⟩ := hy
  have hx₀ : (R.A.chart j).symm y ∈ (R.A.chart j).source := (R.A.chart j).map_target hyt
  have hex₀ : R.A.chart j ((R.A.chart j).symm y) = y := (R.A.chart j).right_inv hyt
  have hxU : (R.A.chart j).symm y ∈ R.U x := hyU
  let γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y')
  have hγ : AnalyticAt ℂ γ y := analyticAt_pi_iff.2 fun q => R.holo x q j y ⟨hyt, hyU⟩
  have hz : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := (R.mem x _ hxU).1
  have hc2 := contDiffAt_log_h (GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm K ι fun _ => 1) hz
  have heq : levi ((potOf R (fsHerm ι fun _ => 1)).φ x ∘ (R.A.chart j).symm) y w =
      levi (fun z => Real.log ((fsHerm ι fun _ => 1).h z)) (γ y) (fderiv ℂ γ y w) :=
    levi_comp w hγ hc2
  rw [heq]
  refine levi_fs_pos hz fun c hc => hw ?_
  choose p hp using (R.mem _ _ (R.mem_U ((R.A.chart j).symm y))).1
  have hnot : R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y) ∉ mcPts (⊤ : Ideal (MRing ι)) := by
    intro h
    have := h.2 1 trivial
    simp at this
  have himm := R.immersion _ hnot p hp j hx₀
  rw [hex₀] at himm
  have hev : (fun y' => affCoord p (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y'))) =ᶠ[𝓝 y]
      fun y' => affCoord p (γ y') := by
    have hmem : (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U ((R.A.chart j).symm y)) ∈ 𝓝 y :=
      ((R.A.chart j).continuousAt_symm hyt).preimage_mem_nhds
        (((R.isOpen_U x).inter (R.isOpen_U _)).mem_nhds ⟨hxU, R.mem_U _⟩)
    filter_upwards [hmem] with y' hy'
    obtain ⟨c', hc', h⟩ := R.compat _ x _ ⟨hy'.2, hy'.1⟩
    funext q
    simp only [affCoord, γ]
    rw [h]
    exact mul_div_mul_left _ _ (hc' q.1)
  rw [hev.fderiv_eq] at himm
  have hpγ : ∀ k, γ y ⟨k, p k⟩ ≠ 0 := by
    intro k
    obtain ⟨c', hc', h⟩ := R.compat _ x _ ⟨R.mem_U _, hxU⟩
    have := hp k
    rw [h] at this
    exact right_ne_zero_of_mul this
  have hk := fderiv_affCoord_torus p hγ.differentiableAt hpγ hc
  have hmem : w ∈ (fderiv ℂ (fun y' => affCoord p (γ y')) y).ker := hk
  rw [himm] at hmem
  exact (Submodule.mem_bot _).1 hmem

end PosFs

theorem fs_pos_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D), (∀ A : HermLine ι, IsSmoothHerm A → IsPotential R.A (potOf R A)) ∧ IsSmoothHerm (fsHerm ι fun _ => 1) ∧ IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) :=
  fun K _ ι _ P D R => ⟨fun _ hA => isPotential_potOf R hA,
    GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm K ι _, PosFs.isPosPot_fs P D R⟩

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MapMemChartIdealOfAevalEqZero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.KerChart

open MvPolynomial ReciprocityTheory.AnForm.R

variable {σ : Type}

theorem exists_int_clear (G : MvPolynomial σ ℚ) :
    ∃ (n : ℤ) (G₀ : MvPolynomial σ ℤ), n ≠ 0 ∧
      map (Int.castRingHom ℚ) G₀ = C (n : ℚ) * G := by
  induction G using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, C a.num, by exact_mod_cast a.den_nz, ?_⟩
    rw [map_C, ← C_mul]
    congr 1
    simp [Rat.den_mul_eq_num]
  | add f g hf hg =>
    obtain ⟨n₁, F, h₁, e₁⟩ := hf
    obtain ⟨n₂, F', h₂, e₂⟩ := hg
    refine ⟨n₁ * n₂, C n₂ * F + C n₁ * F', mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add, map_mul, map_C, e₁, e₂]
    simp only [eq_intCast, Int.cast_mul, C_mul]
    ring
  | mul_X f i hf =>
    obtain ⟨n, F, h, e⟩ := hf
    exact ⟨n, F * X i, h, by rw [map_mul, map_X, e, mul_assoc]⟩

theorem exists_homog (s : σ → σ) (G₀ : MvPolynomial σ ℤ) :
    ∃ H m : MvPolynomial σ ℤ, ∀ (T : Type) [CommRing T] (f : MvPolynomial σ ℤ →+* T) (w : σ → T),
      (∀ q, IsUnit (f (X (s q)))) → (∀ q, f (X q) = f (X (s q)) * w q) →
      IsUnit (f m) ∧ eval₂Hom (Int.castRingHom T) w G₀ * f m = f H := by
  classical
  let M : Submonoid (MvPolynomial σ ℤ) :=
    Submonoid.closure (Set.range fun q => (X (s q) : MvPolynomial σ ℤ))
  let B := Localization M
  have hs : ∀ q, (X (s q) : MvPolynomial σ ℤ) ∈ M := fun q => Submonoid.subset_closure ⟨q, rfl⟩
  let ψ : MvPolynomial σ ℤ →+* B := eval₂Hom (Int.castRingHom B)
    (fun q => IsLocalization.mk' B (X q : MvPolynomial σ ℤ) ⟨X (s q), hs q⟩)
  obtain ⟨⟨H, m⟩, hHm⟩ := IsLocalization.surj M (ψ G₀)
  refine ⟨H, m, fun T _ f w hu hw => ?_⟩
  have hM : ∀ y : M, IsUnit (f y) := by
    rintro ⟨y, hy⟩
    induction hy using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      exact hu q
    | one => simp
    | mul a b _ _ ha hb => simpa using ha.mul hb
  let L : B →+* T := IsLocalization.lift hM
  have hL : ∀ r, L (algebraMap _ B r) = f r := IsLocalization.lift_eq hM
  have hcomp : L.comp ψ = eval₂Hom (Int.castRingHom T) w := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ]
    · intro q
      simp only [RingHom.comp_apply, ψ, eval₂Hom_X']
      exact (IsLocalization.lift_mk'_spec _ _ _ _).2 (hw q)
  refine ⟨hM m, ?_⟩
  have h := congrArg L hHm
  rw [map_mul, hL, hL] at h
  rw [← h, ← hcomp]
  rfl

theorem map_mem_chartIdeal_of_aeval_eq_zero :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (p : (k : K) → ι k), (∀ k, y ⟨k, p k⟩ ≠ 0) →
      ∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G = 0 →
        map (algebraMap ℚ ℂ) G ∈
          chartIdeal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p := by
  intro K _ ι _ Ω _ _ y p hy G hG
  classical
  obtain ⟨n, G₀, hn, hG₀⟩ := exists_int_clear G
  obtain ⟨H, m, hHm⟩ := exists_homog (fun q : Σ k, ι k => (⟨q.1, p q.1⟩ : Σ k, ι k)) G₀
  have hz : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G₀ = (0 : Ω) := by
    have h1 : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩)
        (map (algebraMap ℤ ℚ) G₀) = (0 : Ω) := by
      have : (algebraMap ℤ ℚ) = Int.castRingHom ℚ := rfl
      rw [this, hG₀, map_mul, hG, mul_zero]
    rwa [aeval_map_algebraMap] at h1

  have hH : H ∈ ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y := by
    let F := FractionRing (MvPolynomial K Ω)
    let f : MvPolynomial (Σ k, ι k) ℤ →+* F :=
      (algebraMap (MvPolynomial K Ω) F).comp (ReciprocityTheory.ChartRestriction.G.Geo.mConeMap y).toRingHom
    let w : (Σ k, ι k) → F := fun q => algebraMap (MvPolynomial K Ω) F (C (y q / y ⟨q.1, p q.1⟩))
    have hfX : ∀ q, f (X q) = algebraMap (MvPolynomial K Ω) F (C (y q) * X q.1) := by
      intro q
      simp [f, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]
    have hinj : Function.Injective (algebraMap (MvPolynomial K Ω) F) :=
      IsFractionRing.injective _ _
    have hu : ∀ q : Σ k, ι k, IsUnit (f (X ⟨q.1, p q.1⟩)) := by
      intro q
      rw [hfX, isUnit_iff_ne_zero]
      intro h0
      have := hinj (h0.trans (map_zero _).symm)
      exact mul_ne_zero (C_ne_zero.mpr (hy q.1)) (X_ne_zero _) this
    have hw : ∀ q, f (X q) = f (X ⟨q.1, p q.1⟩) * w q := by
      intro q
      rw [hfX, hfX, ← map_mul]
      congr 1
      have : y q = y ⟨q.1, p q.1⟩ * (y q / y ⟨q.1, p q.1⟩) := by
        field_simp [hy q.1]
      show C (y q) * X q.1 = C (y ⟨q.1, p q.1⟩) * X q.1 * C (y q / y ⟨q.1, p q.1⟩)
      rw [mul_right_comm, ← C_mul, ← this]
    obtain ⟨-, h⟩ := hHm F f w hu hw
    have hev : eval₂Hom (Int.castRingHom F) w G₀ = 0 := by
      have : eval₂Hom (Int.castRingHom F) w =
          ((algebraMap (MvPolynomial K Ω) F).comp C).comp
            (aeval (R := ℤ) (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩)).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp
        · intro q
          simp [w]
      rw [this]
      simp [hz]
    rw [hev, zero_mul] at h
    exact hinj (h.symm.trans (map_zero _).symm)

  set P := ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) with hP
  let A := MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p
  let f : MvPolynomial (Σ k, ι k) ℤ →+* A :=
    (Ideal.Quotient.mk (chartIdeal P p)).comp (map (Int.castRingHom ℂ))
  let w : (Σ k, ι k) → A := fun q => Ideal.Quotient.mk _ (X q)
  have hone : ∀ k, f (X ⟨k, p k⟩) = 1 := by
    intro k
    have : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal P p :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    simpa [f, sub_eq_zero] using Ideal.Quotient.eq_zero_iff_mem.mpr this
  obtain ⟨hm, h⟩ := hHm A f w (fun q => by rw [hone]; exact isUnit_one)
    (fun q => by rw [hone, one_mul]; simp [f, w])
  have hfH : f H = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.subset_span ⟨H, hH, rfl⟩))
  have hev : eval₂Hom (Int.castRingHom A) w = f := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f]
    · intro q
      simp [f, w]
  rw [hev, hfH] at h
  have hG₀0 : f G₀ = 0 := hm.mul_left_eq_zero.mp h
  have hmem : map (Int.castRingHom ℂ) G₀ ∈ chartIdeal P p :=
    Ideal.Quotient.eq_zero_iff_mem.mp hG₀0
  have hmap : map (Int.castRingHom ℂ) G₀ = C (n : ℂ) * map (algebraMap ℚ ℂ) G := by
    have h1 : map (Int.castRingHom ℂ) G₀ = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) G₀) := by
      rw [map_map]
      congr 1
    rw [h1, hG₀, map_mul, map_C]
    simp
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [hmap] at hmem
  have := (chartIdeal P p).mul_mem_left (C (n : ℂ)⁻¹) hmem
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hn', C_1, one_mul] at this

end GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinimalPrimesOfMultihomogSup
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.MinHom

open MvPolynomial ReciprocityTheory.AnForm.R

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_of_mem_minimalPrimes_sup :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)),
      IsMultiHomogIdeal P → IsMultiHomogIdeal D →
        ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by
  intro K _ ι _ P D hP hD Q hQ
  classical
  have toGeo : ∀ I : Ideal (MvPolynomial (Σ k, ι k) ℂ), IsMultiHomogIdeal I →
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) I := fun I h => h
  have hQ' : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) Q :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_isHomogeneous fun k =>
      ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_mem_minimalPrimes _
        ((ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo P hP) k).sup
          (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo D hD) k)) hQ
  exact hQ'

end GlobalTheory.CompanionTheory.Ar.Cmp.MinHom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NefOnFibresAddNonneg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.nef_on_fibres_add_nonneg : PB.Inputs → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (a a' : K → ℤ) (p q : ℕ), NefOnFibres P a → (∀ k, 0 ≤ a' k) → NefOnFibres P ((q : ℤ) • a + (p : ℤ) • a') := by
  first | exact @LevelTowerAlt.nef_fibres_combination | exact LevelTowerAlt.nef_fibres_combination
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingAlt
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem packing : PackingStatement := MultiProjectiveCoordinates.packing_statement

end GlobalTheory.CompanionTheory.Ar.Small
end

