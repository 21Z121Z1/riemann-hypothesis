import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ChartFun
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0027

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric Set

namespace MuRegSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smoothAlong_mul {S : Set ((Σ k, ι k) → ℂ)} {f g : ((Σ k, ι k) → ℂ) → ℝ} (hf : SmoothAlong S f)
    (hg : SmoothAlong S g) : SmoothAlong S fun z => f z * g z := by
  intro z hz
  obtain ⟨U, hU, F, hF, hfF⟩ := hf z hz
  obtain ⟨V, hV, G, hG, hgG⟩ := hg z hz
  refine ⟨U ∩ V, Filter.inter_mem hU hV, fun w => F w * G w,
    (hF.mono inter_subset_left).mul (hG.mono inter_subset_right), fun w hw => ?_⟩
  show f w * g w = F w * G w
  rw [hfF w ⟨hw.1.1, hw.2⟩, hgG w ⟨hw.1.2, hw.2⟩]

theorem smoothAlong_prod {S : Set ((Σ k, ι k) → ℂ)} {α : Type} (s : Finset α)
    {f : α → ((Σ k, ι k) → ℂ) → ℝ} (hf : ∀ p ∈ s, SmoothAlong S (f p)) :
    SmoothAlong S fun z => ∏ p ∈ s, f p z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro z _
    exact ⟨univ, univ_mem, fun _ => 1, contDiffOn_const, fun w _ => by simp⟩
  | insert a s ha ih =>
    have h := smoothAlong_mul (hf a (Finset.mem_insert_self a s))
      (ih fun p hp => hf p (Finset.mem_insert_of_mem hp))
    intro z hz
    obtain ⟨U, hU, G, hG, hfG⟩ := h z hz
    exact ⟨U, hU, G, hG, fun w hw => by
      show ∏ p ∈ insert a s, f p w = G w
      rw [Finset.prod_insert ha]; exact hfG w hw⟩

theorem smoothAlong_exp {S : Set ((Σ k, ι k) → ℂ)} {f : ((Σ k, ι k) → ℂ) → ℝ} (hf : SmoothAlong S f) :
    SmoothAlong S fun z => Real.exp (f z) := by
  intro z hz
  obtain ⟨U, hU, F, hF, hfF⟩ := hf z hz
  exact ⟨U, hU, fun w => Real.exp (F w), Real.contDiff_exp.comp_contDiffOn hF,
    fun w hw => by show Real.exp (f w) = Real.exp (F w); rw [hfF w hw]⟩

omit [∀ k, Fintype (ι k)] in

theorem isOpen_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem smoothAlong_of_contDiffOn {P : Ideal (MRing ι)} {f : ((Σ k, ι k) → ℂ) → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) : SmoothAlong (mcPts P) f :=
  fun _ hz => ⟨_, isOpen_blocks.mem_nhds hz.1, f, hf, fun _ _ => rfl⟩

theorem regWeight_smooth {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)}
    {A : HermLine ι} (S : LogLogRegularisationSetting M Xo A) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) := by
  have hball : ∀ j, ∃ δ : ℝ, 0 < δ ∧
      cthickening δ (S.R.chart j '' closure (S.R.mid j)) ⊆ (S.R.chart j).target := by
    intro j
    have hK : IsCompact (S.R.chart j '' closure (S.R.mid j)) :=
      isClosed_closure.isCompact.image_of_continuousOn
        ((S.R.chart j).continuousOn.mono (S.R.closure_mid j))
    have hsub : S.R.chart j '' closure (S.R.mid j) ⊆ (S.R.chart j).target :=
      image_subset_iff.2 fun x hx => (S.R.chart j).map_source (S.R.closure_mid j hx)
    exact hK.exists_cthickening_subset_open (S.R.chart j).open_target hsub
  choose δ hδ hδs using hball
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, t < δ j :=
    Filter.eventually_all.2 fun j => nhdsWithin_le_nhds (gt_mem_nhds (hδ j))
  filter_upwards [hev, hS.compare, self_mem_nhdsWithin] with t htδ hcmp ht
  have ht0 : (0 : ℝ) < t := ht
  exact (Regular.GlueRegularised.proof M.Xc d M.atlas S.R S.ρ S.η S.Cη (S.K t) t (S.e1 t) S.cutoff ht0
    (ht0.trans_le (S.e1_ge t ht0))
    (fun j x hx => ((closedBall_subset_closedBall (htδ j).le).trans
      (closedBall_subset_cthickening (mem_image_of_mem _ hx) _)).trans (hδs j)) hcmp).1

theorem prod_norm_zpow_add_sum {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a : K → ℤ) (s : Finset ℕ) (b : ℕ → K → ℤ) :
    (∏ k, ‖c k‖ ^ (a + ∑ p ∈ s, b p) k) = (∏ k, ‖c k‖ ^ a k) * ∏ p ∈ s, ∏ k, ‖c k‖ ^ b p k := by
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
  have hsum : ∀ s' : Finset ℕ, ‖c k‖ ^ (∑ p ∈ s', b p k) = ∏ p ∈ s', ‖c k‖ ^ b p k := by
    intro s'
    induction s' using Finset.induction_on with
    | empty => simp
    | insert q s' hq ih => rw [Finset.sum_insert hq, Finset.prod_insert hq, zpow_add₀ h0, ih]
  rw [Pi.add_apply, Finset.sum_apply, zpow_add₀ h0, hsum]

end MuRegSmooth

open MuRegSmooth TopNPoly in

theorem MuRegSmooth.proof (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement)
    (hVS : VertFactorSmooth.Statement) (hV : VertFactorPos.Statement) : MuRegSmooth.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B
  filter_upwards [regWeight_smooth X.S X.S_tied] with t ht
  have hPm : IsMultiHomogIdeal (mCoordIdeal D.y) := D.arith.2.1.2.1
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z with hFdef
  have hpos : ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < F z := fun z hz =>
    mul_pos (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _))
      (Finset.prod_pos fun p hp => hV II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1 z hz)
  have hhom : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts (mCoordIdeal D.y) := mcPts_smul hPm c hc hz
    have hproj : X.M.proj (torusSmul c z) = X.M.proj z :=
      ((X.M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * X.S.ref.h z := by
      rw [show torusSmul c z = fun p => c p.1 * z p from rfl, X.S.ref.smul c z hc, X.S.ref_deg]
      rfl
    have hvf : ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
        (∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k) * ∏ p ∈ D.SB B, D.vertFactor p z := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p hp =>
        (hVS II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1).1 z hz c hc
    simp only [hFdef]
    rw [href, hproj, hvf, muTwDeg, prod_norm_zpow_add_sum hc]
    ring
  have hsm : SmoothAlong (mcPts (mCoordIdeal D.y)) F :=
    smoothAlong_mul (smoothAlong_mul (smoothAlong_of_contDiffOn X.S.ref_smooth)
      (smoothAlong_exp (hP II Ψ K ι Ω E D X.M _ ht)))
      (smoothAlong_prod _ fun p hp => (hVS II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1).2)
  obtain ⟨Z, hZa, hZs, hZh⟩ := hE K ι (mCoordIdeal D.y) (muTwDeg X.H B) F hPm hpos hhom hsm
  unfold muReg
  refine smoothRep_smooth_of (Z := Z) hZa hZs fun z hz => ?_
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  have hw0 := orbitRep_blocks hz.1
  have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul hPm (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
    convert h using 1
    funext p
    have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)
  have hreg : (X.S.regLine t).h (orbitRep z) =
      X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    hermOfFun_h_orbitRep hz.1 hG0
  have hFw : (X.S.regLine t).h (orbitRep z) * ∏ p ∈ D.SB B, D.vertFactor p (orbitRep z) = F (orbitRep z) := by
    rw [hreg]
  rw [hZh z hz, hermOfFun_h_smul hc hzc hz.1 (by rw [hFw]; exact hpos _ hwP), hFw]
  conv_lhs => rw [hzc]
  exact hhom _ hwP c hc

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ContDiff

theorem ProjSmoothAlong.proof (hO : HoloInjDerivInj.Statement) (hL : LocalOrbitChart.Statement) :
    ProjSmoothAlong.Statement := by
  intro II Ψ hΨ K hK ι hι Ω hΩ hQΩ E hE1 hE2 D M g hg z₀ hz₀
  set S := mcPts (mCoordIdeal D.y) with hS
  set x₀ := M.proj z₀ with hx₀
  obtain ⟨j, hj⟩ := M.atlas.cover x₀
  set e := M.atlas.chart j with he
  obtain ⟨W, hWo, hxW, s, hs, hsh⟩ := M.sections x₀
  obtain ⟨N, hNo, hzN, κ, hκa, hκt, hκi⟩ := hL K ι Ω D.y D.n D.arith D.smoothGeneric z₀ hz₀
  set σ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (e.symm u) with hσ
  set f : (Fin D.n → ℂ) → (Fin D.n → ℂ) := fun u => κ (σ u) with hf
  set u₀ := e x₀ with hu₀
  set T := e.target ∩ e.symm ⁻¹' W with hT
  have hTo : IsOpen T := e.isOpen_inter_preimage_symm hWo
  have hσa : AnalyticOnNhd ℂ σ T := fun u hu => AnalyticAt.pi fun p => hsh p j u hu
  have hu₀t : u₀ ∈ e.target := e.map_source hj
  have hsymm₀ : e.symm u₀ = x₀ := e.left_inv hj
  have hu₀T : u₀ ∈ T := ⟨hu₀t, by simp only [Set.mem_preimage, hsymm₀]; exact hxW⟩

  have hσ₀ : σ u₀ = s x₀ := by simp only [hσ, hsymm₀]
  obtain ⟨hsx₀S, hsx₀p⟩ := hs x₀ hxW
  obtain ⟨c₀, hc₀, hc₀e⟩ := (M.fibre z₀ hz₀ (s x₀) hsx₀S).1 hsx₀p.symm
  have hsx₀N : s x₀ ∈ N := hc₀e ▸ (hκt z₀ hzN c₀ hc₀).1
  have hκs₀ : κ (s x₀) = κ z₀ := hc₀e ▸ (hκt z₀ hzN c₀ hc₀).2

  set T' := T ∩ σ ⁻¹' N with hT'
  have hT'o : IsOpen T' := hσa.continuousOn.isOpen_inter_preimage hTo hNo
  have hu₀T' : u₀ ∈ T' := ⟨hu₀T, by simp only [Set.mem_preimage, hσ₀]; exact hsx₀N⟩
  have hfa : AnalyticOnNhd ℂ f T' := fun u hu => (hκa (σ u) hu.2).comp (hσa u hu.1)
  have hinj : Set.InjOn f T' := by
    intro u hu u' hu' hfu
    obtain ⟨hmS, hmp⟩ := hs (e.symm u) hu.1.2
    obtain ⟨hmS', hmp'⟩ := hs (e.symm u') hu'.1.2
    obtain ⟨c, hc, hce⟩ := hκi (σ u) ⟨hu.2, hmS⟩ (σ u') ⟨hu'.2, hmS'⟩ hfu
    have hpe : M.proj (σ u) = M.proj (σ u') := (M.fibre (σ u) hmS (σ u') hmS').2 ⟨c, hc, hce⟩
    have h2 : e.symm u = e.symm u' := by
      simp only [hσ] at hpe
      rw [← hmp, ← hmp', hpe]
    rw [← e.right_inv hu.1.1, ← e.right_inv hu'.1.1, h2]

  have hDinj : Function.Injective (fderiv ℂ f u₀) := hO D.n f T' hT'o hfa hinj u₀ hu₀T'
  set Lc : (Fin D.n → ℂ) ≃L[ℂ] (Fin D.n → ℂ) :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℂ f u₀ : (Fin D.n → ℂ) →ₗ[ℂ] (Fin D.n → ℂ)) hDinj).toContinuousLinearEquiv
    with hLc
  have hFD : HasFDerivAt f (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) u₀ := by
    have hcoe : (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) = fderiv ℂ f u₀ := by
      ext v; rfl
    rw [hcoe]
    exact (hfa u₀ hu₀T').differentiableAt.hasFDerivAt
  have hcd : ContDiffAt ℂ ω f u₀ := (hfa u₀ hu₀T').contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set linv := hcd.localInverse hFD hn with hlinv
  have hlinv_cd : ContDiffAt ℂ ω linv (f u₀) := hcd.to_localInverse hFD hn
  have hlinv₀ : linv (f u₀) = u₀ := hcd.localInverse_apply_image hFD hn
  have hleft : ∀ᶠ u in 𝓝 u₀, linv (f u) = u := (hcd.hasStrictFDerivAt' hFD hn).eventually_left_inverse
  have hfu₀ : f u₀ = κ z₀ := by simp only [hf, hσ₀, hκs₀]

  set Φ : ((Σ k, ι k) → ℂ) → (Fin D.n → ℂ) := fun z => linv (κ z) with hΦ
  have hΦcd : ContDiffAt ℂ ω Φ z₀ := by
    have h1 : ContDiffAt ℂ ω linv (κ z₀) := hfu₀ ▸ hlinv_cd
    exact h1.comp z₀ (hκa z₀ hzN).contDiffAt
  have hΦ₀ : Φ z₀ = u₀ := by simp only [hΦ, ← hfu₀, hlinv₀]
  obtain ⟨V₁, hV₁, hΦV₁⟩ := hΦcd.contDiffOn (m := ∞) le_top (fun _ => rfl)
  have hΦV₁R : ContDiffOn ℝ ∞ Φ V₁ := hΦV₁.restrict_scalars ℝ
  set V₂ := V₁ ∩ Φ ⁻¹' e.target with hV₂
  have hV₂n : V₂ ∈ 𝓝 z₀ :=
    inter_mem hV₁ (hΦcd.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hΦ₀ ▸ hu₀t)))
  have hgs : ContDiffOn ℝ ∞ (g ∘ e.symm) e.target := by
    have := hg j
    simpa [ReciprocityTheory.AnForm.M.FinHolAtlas.Smooth, ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn] using this
  have hGV₂ : ContDiffOn ℝ ∞ (fun z => g (e.symm (Φ z))) V₂ :=
    hgs.comp (hΦV₁R.mono Set.inter_subset_left) (fun z hz => hz.2)

  have hcont : ContinuousWithinAt M.proj S z₀ := M.cont z₀ hz₀
  have htend : Tendsto (fun w => e (M.proj w)) (𝓝[S] z₀) (𝓝 u₀) :=
    (e.continuousAt hj).tendsto.comp hcont.tendsto
  have hev1 : ∀ᶠ w in 𝓝[S] z₀, M.proj w ∈ e.source ∩ W :=
    hcont.tendsto ((e.open_source.inter hWo).mem_nhds ⟨hj, hxW⟩)
  have hev2 : ∀ᶠ w in 𝓝[S] z₀, linv (f (e (M.proj w))) = e (M.proj w) := htend.eventually hleft
  have hev3 : ∀ᶠ w in 𝓝[S] z₀, w ∈ N := nhdsWithin_le_nhds (hNo.mem_nhds hzN)
  have hev : ∀ᶠ w in 𝓝[S] z₀, (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N :=
    (hev1.and hev2).and hev3
  rw [eventually_nhdsWithin_iff] at hev
  refine ⟨V₂ ∩ {w | w ∈ S → (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N},
    inter_mem hV₂n hev, fun z => g (e.symm (Φ z)), hGV₂.mono Set.inter_subset_left, ?_⟩
  rintro w ⟨⟨-, hw⟩, hwS⟩
  obtain ⟨⟨⟨hxe, hxW'⟩, hli⟩, hwN⟩ := hw hwS
  obtain ⟨hsS, hsp⟩ := hs (M.proj w) hxW'
  obtain ⟨c, hc, hce⟩ := (M.fibre w hwS (s (M.proj w)) hsS).1 hsp.symm
  have hfe : f (e (M.proj w)) = κ w := by
    simp only [hf, hσ, e.left_inv hxe]
    rw [hce]
    exact (hκt w hwN c hc).2
  have hΦw : Φ w = e (M.proj w) := by
    simp only [hΦ]
    rw [← hfe, hli]
  simp only [hΦw, e.left_inv hxe]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRegAboveWeight
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem RegAboveWeight.proof (hBd : BdPtsNull.Statement) (hDiv : DivisorPreimageNull.Statement) :
    RegAboveWeight.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨C, t₀, ht₀, hb⟩ := GroundTheory.Heights₂.Heights.Regular.ChartMollifiedBounds.proof
    GroundTheory.Heights₂.Heights.Regular.TruncPsh.proof X.M.Xc D.n X.M.atlas X.S.R X.S.ρ
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < t₀ ∧ 0 ≤ X.S.K t :=
    (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀)).and
      (X.S_tied.K_tendsto.eventually_ge_atTop 0)
  obtain ⟨t₂, ht₂, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  refine ⟨t₂, ht₂, D.Bd ∪ {z | X.M.proj z ∉ X.S.R.Yo}, ?_, fun t ht htt z hz hzN => ?_⟩
  ·
    intro Ψ' hΨ'
    refine measure_mono_null (fun y hy => ?_)
      (measure_union_null (hBd II Ψ K ι Ω E D Ψ' hΨ') (hDiv K ι _ _ X.M X.S.R Ψ' hΨ'))
    obtain ⟨z, hz, hzN, hzy⟩ := hy
    rcases hzN with h | h
    · exact Or.inl ⟨z, hz, h, hzy⟩
    · exact Or.inr ⟨z, hz, h, hzy⟩
  obtain ⟨htt₀, hK⟩ : t < t₀ ∧ 0 ≤ X.S.K t := hsub ⟨ht, htt⟩
  have hBdz : z ∉ D.Bd := fun h => hzN (Or.inl h)
  have hY : X.M.proj z ∈ X.S.R.Yo := by
    by_contra h
    exact hzN (Or.inr h)
  have hXo : z ∈ D.Xo := Set.mem_sdiff_of_mem hz hBdz

  obtain ⟨k, hk⟩ := X.S.R.cover (X.M.proj z)
  have hkm := X.S.R.inner_subset_mid k hk
  have hε : 0 ≤ X.S.e1 t := ht.le.trans (X.S.e1_ge t ht)

  have h1 := ((hb t ht htt₀).2 (X.S.K t) hK k (X.M.proj z) hkm).2.2 hY

  have h2 := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.le_glue X.S.R.toPotentialCharts
    (fun j x => X.S.R.phReg X.S.ρ (X.S.K t) t j x + 4 * X.S.e1 t * X.S.η j x) hε hkm
  have h3 : X.S.regWeight t (X.M.proj z) = X.S.R.glue
      (fun j x => X.S.R.phReg X.S.ρ (X.S.K t) t j x + 4 * X.S.e1 t * X.S.η j x) (X.S.e1 t) (X.M.proj z) := rfl
  have hη := X.S.cutoff.eq_zero k (X.M.proj z) hk
  simp only [hη, mul_zero, add_zero] at h2

  have h4 := X.S.ph_eq z ⟨hXo, hz⟩ hY
  have h5 : phMu X.H z = Real.log ((muLine X.H).h z) := rfl
  rw [h3, h5]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem ComponentSetting.mixN_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
    (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) : X.mixN B (D.n + 1) t = arLimFun X.H X.S B t := by
  unfold ComponentSetting.mixN arLimFun
  congr 1
  funext j
  simp [j.is_lt]

theorem StokesLimitTTop.proof (hE : TopNMixedExpand.Statement) (hM : TopNMixedLimit.Statement) :
    StokesLimitTTop.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hAr hp hpq
  have hlim : ∀ k ∈ Finset.range (D.n + 2), ∃ L : ℝ, Tendsto (X.mixN B k) (𝓝[>] 0) (𝓝 L) := by
    intro k hk
    rcases Nat.lt_or_ge k (D.n + 1) with h | h
    · exact hM II Ψ K ι Ω E D O Lt X B hII hAr k (Nat.lt_succ_iff.1 h)
    · have hk' : k = D.n + 1 := le_antisymm (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) h
      subst hk'
      obtain ⟨L, hL⟩ := hAr
      exact ⟨L, hL.congr fun t => (X.mixN_top B t).symm⟩
  choose! L hL using hlim
  refine ⟨∑ k ∈ Finset.range (D.n + 2), ((D.n + 1).choose k : ℝ) * ((p : ℝ) / q) ^ (D.n + 1 - k) * L k, ?_⟩
  refine Tendsto.congr' ((hE II Ψ K ι Ω E D O Lt X B p q hII hp hpq).mono fun t ht => ht.symm) ?_
  exact tendsto_finsetSum _ fun k hk => (hL k hk).const_mul _

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTp
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem ComponentSetting.wSt_torusSmul (X : ComponentSetting D O Lt) (B p q : ℕ) (t t' : ℝ) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    X.wSt B p q t t' (torusSmul c z) = X.wSt B p q t t' z := by
  have ha : (X.MUq B p q t').a = (X.NbarQ B p q t).a := by
    simp only [ComponentSetting.MUq, MUc, ComponentSetting.NbarQ, smoothRepConj_a, smoothRep_a]
    rfl
  have hpos : 0 < ∏ k, ‖c k‖ ^ (X.NbarQ B p q t).a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  have e : torusSmul c z = fun x => c x.1 * z x := rfl
  have h1 := (X.MUq B p q t').smul c z hc
  have h2 := (X.NbarQ B p q t).smul c z hc
  rw [ha] at h1
  unfold ComponentSetting.wSt
  rw [e, h1, h2, Real.log_mul hpos.ne' ((X.MUq B p q t').pos z hz.1).ne',
    Real.log_mul hpos.ne' ((X.NbarQ B p q t).pos z hz.1).ne']
  ring

theorem StokesLimitTp.proof (hLim : TpIntegrandLimit.Statement) (hAbove : RegAboveWeight.Statement)
    (hU : TpCuspIntegrable.Statement) (hConv : PtsBddConv.Statement) (hMono : PtsMonoSemipos.Statement) :
    StokesLimitTp.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hp hpq
  have hq : 1 ≤ q := hp.trans hpq
  have hr : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨t₁, ht₁, hL⟩ := hLim II Ψ K ι Ω E D O Lt X B p q hq
  obtain ⟨t₃, ht₃, N₂, hN₂, hA⟩ := hAbove II Ψ K ι Ω E D O Lt X
  refine ⟨min t₁ t₃, lt_min ht₁ ht₃, fun t ht0 ht hsp => ?_⟩
  obtain ⟨N₁, C, s₀, hs₀, hN₁, hbd, hpt⟩ := hL t ht0 (ht.trans (min_le_left _ _))
  obtain ⟨hint, hlim⟩ := hConv K ι (mCoordIdeal D.y) D.n (X.NbarQ B p q t) q (X.wSt B p q t)
    (fun z => cuspCorr X.H X.Cd z - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z))) N₁ C s₀
    D.arith hsp.1 hr hN₁ hs₀
    (fun s hs hs' => ⟨(hbd s hs hs').1, (hbd s hs hs').2, fun c hc z hz => X.wSt_torusSmul B p q t s c hc z hz⟩) hpt
  refine ⟨hlim, ?_⟩
  refine hMono K ι (mCoordIdeal D.y) D.n (X.NbarQ B p q t) q _ (fun z => X.Cd.cuspWeight z / 2) N₂ D.arith hsp hr
    hN₂ (fun z hz hzN => ?_) hint (hU II Ψ K ι Ω E D O Lt X B p q t hsp.1)
  have h := hA t ht0 (ht.trans (min_le_right _ _)) z hz hzN
  show phMu X.H z + X.Cd.cuspWeight z / 2 - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z)) ≤
    X.Cd.cuspWeight z / 2
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarSmooth
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ) (t : ℝ),
    X.M.atlas.Smooth (X.S.regWeight t) → IsSmoothHerm (X.NbarQ B p q t)

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem NbarSmooth.hyps_of_setting (X : ComponentSetting D O Lt) :
    ∃ t : ℝ, 0 < t ∧ X.M.atlas.Smooth (X.S.regWeight t) := by
  obtain ⟨t, -, ht, hs, -⟩ := NbarChartSemipos.hyps_of_setting X one_pos
  exact ⟨t, ht, hs⟩

theorem Line.NbarSmooth.hyps_inhabited :
    ∃ t : ℝ, 0 < t ∧ (Line.projLineComponentSetting Line.zeroSystem Line.zero_hII).M.atlas.Smooth
      ((Line.projLineComponentSetting Line.zeroSystem Line.zero_hII).S.regWeight t) :=
  LowerBoundFree.NbarSmooth.hyps_of_setting _

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelPtsIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart)

def ModelPtsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (n : ℕ) (ψ : Fin n → OpenPartialHomeomorph M.Xc (Fin e → ℂ)) (L : HermLine ι) (c : ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (E : Set M.Xc) (v : M.Xc → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsSmoothHerm L → IsPtsNull P e N →
    (∀ j, IsCompatChart M.atlas (ψ j)) → (∀ x, ∃ j, x ∈ (ψ j).source) →
    (∀ j, volume ((ψ j).target ∩ (ψ j).symm ⁻¹' E) = 0) →
    (∀ j, ∀ Q ⊆ (ψ j).target, IsCompact Q → IntegrableOn (fun y => v ((ψ j).symm y)) Q) →
    (∀ z ∈ mcPts P, z ∉ N → M.proj z ∉ E → g z = v (M.proj z)) →
      IsPtsIntegrable P (fun (_ : Fin e) z => c * Real.log (L.h z)) g

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

