import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0035
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0058
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0062
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0058
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0025
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsMulNe
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics

namespace GlobalTheory.UpperModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem pnorm_pos (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  refine mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_)
  exact Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _

theorem isBddSec_sum (X : Data E r) {la : Wt X.Ψ r} {m : ℕ} {f : Fin m → Frame X.Ψ r → ℂ}
    (hf : ∀ q, X.IsBddSec la (f q)) (u : Fin m → ℂ) : X.IsBddSec la fun x => ∑ q, u q * f q x := by
  refine ⟨⟨DifferentiableOn.fun_sum fun q _ => (hf q).1.1.const_mul _, fun x hx b hb => ?_,
    fun γ hγ x hx => ?_⟩, ?_⟩
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [(hf q).1.2.1 x hx b hb]; ring
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [(hf q).1.2.2 γ hγ x hx]; ring
  · choose C hC using fun q => (hf q).2
    refine ⟨∑ q, ‖u q‖ * C q, fun x hx => ?_⟩
    have hN : 0 ≤ ∏ τ, ∏ i : Fin r,
        ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by positivity
    calc X.pnorm la (fun x => ∑ q, u q * f q x) x
        ≤ (∑ q, ‖u q * f q x‖) * _ := mul_le_mul_of_nonneg_right (norm_sum_le _ _) hN
      _ = ∑ q, ‖u q‖ * X.pnorm la (f q) x := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun q _ => by rw [norm_mul, mul_assoc]; rfl
      _ ≤ _ := Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hC q x hx) (norm_nonneg _)

theorem s_xs {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) (k : Fin (nd X)) :
    Fl.s k (Fl.xs j) = 0 :=
  (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, one_mem _, nmat X 0, LeadJets.nmat_zero_mem_Bor X, by
      rw [LeadJets.rmul_nmat_zero, LeadJets.lact_one]⟩ k

theorem zero_mem_OmF {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) : (0 : V (nd X)) ∈ OmF X x := by
  show cpt X x 0 ∈ X.dom
  rw [LeadJets.cpt_zero]; exact hx

theorem exists_s_ne {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) :
    ∃ k, ∃ x ∈ X.dom, Fl.s k x ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, -⟩ := Xa.et_ne
  obtain ⟨j, -⟩ := (Fl.S_eq x hx).1 fun k => h k x hx
  apply Fl.coord j
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [(OntoB.isOpen_OmF X (Fl.xs j)).mem_nhds (zero_mem_OmF (Fl.xs_mem j))] with z hz
    ext k
    simp [h k _ hz]
  rw [hev.fderiv_eq, fderiv_const_apply]
  have hn := Xa.n_ge
  haveI : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  have := LinearMap.det_zero' (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis
  simpa [ContinuousLinearMap.det] using this

theorem exists_comb {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (e m : ℕ)
    (f : Fin m → Frame X.Ψ r → ℂ) (hf : ∀ q, DifferentiableOn ℂ (f q) X.dom)
    (hm : Fl.δ * (e + nd X).choose (nd X) < m) :
    ∃ u : Fin m → ℂ, u ≠ 0 ∧ ∀ j, (fun z : V (nd X) => ∑ q, u q * f q (cpt X (Fl.xs j) z))
      =O[𝓝 0] fun z => ‖z‖ ^ (e + 1) := by
  classical
  have hj := fun q => LeadJets.jets (T := e) (a0 := e + 1) (U := fun j => OmF X (Fl.xs j))
    (f := fun j z => f q (cpt X (Fl.xs j) z))
    (w := fun j z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun j z k => Fl.s k (cpt X (Fl.xs j) z))
    (t := fun j _ k => if k = j then 1 else 0) le_rfl
    (fun j => OntoB.isOpen_OmF X _)
    (fun j => zero_mem_OmF (Fl.xs_mem j))
    (fun j => OntoB.hol_comp X _ (hf q))
    (fun j => OntoB.hol_comp X _ Fl.weightForm_vanishes.1.1.1.1)
    (fun j k => OntoB.hol_comp X _ (Fl.s_van k).1.1.1.1)
    (fun j k => differentiableOn_const _)
    (fun j => by simpa only [LeadJets.cpt_zero] using Fl.w0_ne j)
    (fun j k => by simpa only [LeadJets.cpt_zero] using s_xs Fl j k)
    Fl.coord
    (fun v => ⟨v, fun j => by simp⟩)
  choose cc hcc using hj
  let v : Fin m → (Fin Fl.δ × multiLt (nd X) (e + 1) → ℂ) := fun q p => cc q p.2.1 p.1
  have hdep : ¬ LinearIndependent ℂ v := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe, ManyForms.card_multiLt_succ] at this
    omega
  obtain ⟨u, hu, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hu' : ∀ α ∈ multiLt (nd X) (e + 1), ∀ k, ∑ q, u q * cc q α k = 0 := fun α hα k => by
    simpa [v] using congrFun hu (k, ⟨α, hα⟩)
  refine ⟨u, fun h => hi (by simp [h]), fun j => ?_⟩
  have hz : ∀ (s : Fin (nd X) → ℂ) (w : ℂ) (t : Fin Fl.δ → ℂ),
      ∑ q, u q * LeadJets.leadVal s w t e (e + 1) (cc q) = 0 := fun s w t => by
    unfold LeadJets.leadVal
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun α hα => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [← mul_assoc, ← Finset.sum_mul, hu' α hα k, zero_mul]
  have hsum := IsBigO.sum (s := Finset.univ) fun q _ => (hcc q j).const_mul_left (u q)
  refine hsum.congr_left fun z => ?_
  simp only [Finset.sum_apply, mul_sub, Finset.sum_sub_distrib, hz, sub_zero]

theorem exists_mul_ne {X : Data E r} {f g : Frame X.Ψ r → ℂ} (hf : DifferentiableOn ℂ f X.dom)
    (hg : DifferentiableOn ℂ g X.dom) (hf0 : ∃ x ∈ X.dom, f x ≠ 0) (hg0 : ∃ x ∈ X.dom, g x ≠ 0) :
    ∃ x ∈ X.dom, f x * g x ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, hfx⟩ := hf0
  obtain ⟨y, hy, hgy⟩ := hg0
  exact hgy (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hf hg h hx hfx y hy)

theorem upper : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, X.IsBddSec (Xa.Fp + Xa.T • Xa.L) (f q)) → (∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0) → m ≤ Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X) := by
  intro E _ _ _ r X Xa Fl m f hf hind
  by_contra hm
  obtain ⟨u, hu, hO⟩ := exists_comb Fl (Xa.T + nd X + 6) m f (fun q => (hf q).1.1) (by
    rw [show Xa.T + nd X + 6 + nd X = Xa.T + 2 * nd X + 6 by ring]; omega)
  have hg := isBddSec_sum X hf u
  have hg0 : ∃ x ∈ X.dom, ∑ q, u q * f q x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (hind u h)
  obtain ⟨k, hk⟩ := exists_s_ne Fl
  have d1 := hg.1.1
  have d2 := Xa.secondTheta_vanishes.1.1.1.1
  have d3 := Xa.firstTheta_vanishes.1.1.1.1
  have d4 := Xa.et_sec.1
  have d5 := (Fl.s_van k).1.1.1.1
  obtain ⟨x, hx, hne⟩ := exists_mul_ne (((d1.mul d2).mul d3).mul d4) d5
    (exists_mul_ne ((d1.mul d2).mul d3) d4 (exists_mul_ne (d1.mul d2) d3
      (exists_mul_ne d1 d2 hg0 Xa.secondTheta_ne_zero) Xa.firstTheta_ne_zero) Xa.et_ne) hk
  simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or] at hne
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hne
  obtain ⟨x0, hx0, hs0, hpos, hmax⟩ := GlobalTheory.T.normQuotientThetaFlat_attains_sup_off_common_zeros E r X Xa Fl _ hg hO ⟨x, hx, by
    have p1 := pnorm_pos X (Xa.Fp + Xa.T • Xa.L) (P := fun x => ∑ q, u q * f q x) hx h1
    have p2 := pnorm_pos X ((nd X + 4) • Xa.L - Xa.Fp) hx h2
    have p3 := pnorm_pos X (2 • Xa.L - Xa.de) hx h3
    have p4 := pnorm_pos X ((Xa.i * (Xa.g0 / 2)) • Xa.de) hx h4
    have p5 : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨k, Finset.mem_univ _, pow_pos (pnorm_pos X _ hx h5) 2⟩
    positivity⟩
  exact GlobalTheory.T.quotient_no_positive_max_off_common_zeros E r X Xa Fl _ hg.1 x0 hx0 hs0 hpos hmax

end GlobalTheory.UpperModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRankOneCuspDataLogBounds
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.CuspDataBounds

theorem exists_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xx : DataX E r) (X : Data E r)
    (hX : Xx.toData = X) (S : Set E)
    (hΛ : Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ Xx.L', v = a • u})
    (NA NC : ℕ) (hA : 0 < NA) (hC : 0 < NC) (hAi : ∀ a ∈ S, IsIntegral ℤ ((NA : E) * a)) (hCS : (NC : E) ∈ S) :
    ∃ e : XExt X, e.NA = NA ∧ e.NC = NC ∧ e.g = Xx.g ∧ e.k0 = Xx.k0 := by
  subst hX
  refine ⟨⟨Xx.k0, Xx.minWeight_pos, Xx.k0_le, Xx.ξ0_abs, Xx.EF_int, Xx.EF_perf, Xx.L', Xx.L'_fg, Xx.L'_int,
      Xx.L'_dual, NA, NC, hA, hC, ?_, ?_, Xx.g, Xx.g_pos, Xx.cong⟩, rfl, rfl, rfl, rfl⟩
  ·
    intro x hx
    rw [hΛ] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hy
      rw [smul_smul]
      have h1 : ((NA : E) * a) • u = (⟨(NA : E) * a, hAi a ha⟩ : 𝓞 E) • u := by
        rw [← algebraMap_smul E (⟨(NA : E) * a, hAi a ha⟩ : 𝓞 E) u]
        rfl
      rw [h1]
      exact Xx.L'.smul_mem _ hu
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact Xx.L'.add_mem hy hz
    | smul c y _ hy =>
      rw [smul_comm]
      exact Xx.L'.smul_mem c hy
  ·
    intro x hx
    rw [hΛ]
    exact Submodule.subset_span ⟨(NC : E), hCS, x, hx, rfl⟩

theorem weight_bounds (L f r n d : ℝ) (hL : 2 ≤ L) (hf : 1 ≤ f) (hfr : f ≤ r) (hrn : r ≤ n) (hd : 0 ≤ d)
    (hn : Real.log n ≤ L) (hD : Real.log (1 + d) ≤ 2 * L) :
    Real.log (d + f * n + 1) ≤ 3 * L ∧ Real.log (f * (d + f * n + 1) + 2) ≤ 5 * L ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ d + f * r * n / 2 → Real.log (1 + s) ≤ 3 * L := by
  have hx3 : 3 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have e2 : Real.exp (2 * L) = Real.exp L ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp (3 * L) = Real.exp L ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have e5 : Real.exp (5 * L) = Real.exp L ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  set x := Real.exp L with hx
  have hn0 : 0 < n := by linarith
  have hnx : n ≤ x := (Real.log_le_iff_le_exp hn0).1 hn
  have hdx : 1 + d ≤ x ^ 2 := by rw [← e2]; exact (Real.log_le_iff_le_exp (by linarith)).1 hD
  have hfx : f ≤ x := by linarith
  have hrx : r ≤ x := by linarith
  have hfn : f * n ≤ x ^ 2 := by nlinarith
  have hfn0 : 0 ≤ f * n := by nlinarith
  have hx2 : 9 ≤ x ^ 2 := by nlinarith
  have hx23 : 3 * x ^ 2 ≤ x ^ 3 := by nlinarith
  have hx35 : 9 * x ^ 3 ≤ x ^ 5 := by nlinarith
  have hA : d + f * n + 1 ≤ 2 * x ^ 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.log_le_iff_le_exp (by linarith), e3]
    linarith
  · have hB : f * (d + f * n + 1) ≤ x * (2 * x ^ 2) := mul_le_mul hfx hA (by linarith) (by linarith)
    rw [Real.log_le_iff_le_exp (by nlinarith), e5]
    nlinarith
  · intro s hs0 hs
    have hfr0 : 0 ≤ f * r := by nlinarith
    have hC : f * r * n ≤ x ^ 3 := by
      have h1 : f * r ≤ x * x := mul_le_mul hfx hrx (by linarith) (by linarith)
      have h2 : f * r * n ≤ x * x * x := mul_le_mul h1 hnx hn0.le (by positivity)
      nlinarith
    rw [Real.log_le_iff_le_exp (by linarith), e3]
    nlinarith

private theorem level_M_eq_g_zero_mul_g_one_of_lawsM {D : D7} (T : Core D) (h : Formalism.L2.Pj.LawsM T) :
    T.Q.l.M = D.host.g 0 * D.host.g 1 := by
  have p := h.pins.2.1
  unfold Formalism.L2.Pj.Par.PinLevel at p
  exact p.1

theorem cusp_data_bounds : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (e : ∀ k : (T.U j σ).Comp, XExt ((T.U j σ).X k)) (M wg : ℝ), 1 ≤ M ∧ Real.log M ≤ 30 * large₂.sc.L ∧ 0 < wg ∧ Real.log wg ≤ 3 * large₂.sc.L ∧ Real.log ((fdeg D.host.E : ℝ) * wg + 2) ≤ 5 * large₂.sc.L ∧ ∀ k, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ wg ∧ (∀ v ∈ (e k).L', herm ((T.U j σ).X k).Gm v v = 0 → ∀ b : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc b = b → IsIntegral ℤ b → ∃ γ ∈ ((T.U j σ).X k).Γ, ((T.U j σ).X k).χ (laU (T.U j σ) (wtA w) w.n k) γ = 1 ∧ ∀ τ : ((T.U j σ).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j σ).X k).flowMat v τ ((M : ℂ) * τ.1 b)) ∧ Real.log (1 + ∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ 3 * large₂.sc.L ∧ Real.log (e k).NA ≤ 4 * large₂.sc.L ∧ Real.log (e k).NC ≤ 2 * large₂.sc.L ∧ Real.log (e k).g ≤ 19 * large₂.sc.L ∧ Real.log (1 / (e k).k0) ≤ 3 * large₂.sc.L := by
  intro D T h hGam large₂ j hj w hP hL hrn σ hσ
  obtain ⟨hgi, hlrd, hdd, hcc, -, -, -, hDF, hn⟩ := hP
  obtain ⟨⟨NA, hNA0, hNAi, hNAL⟩, hccA, hcc0, ⟨m, hm0, hmi, hmL⟩, hk0L, hfdeg, -, -, hfr, hf1, hxicc, -,
    hxiabs⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L hL hlrd hdd hcc
  have h10 := GlobalTheory.T.modelWeight_size_spread_bound D T h j hj w σ hσ
  obtain ⟨hW1, hW2, hW3⟩ := weight_bounds large₂.sc.L (D.R.f : ℝ) (D.R.r : ℝ) (w.n : ℝ) (WeightAlgebra.DF w : ℝ) hL
    (by exact_mod_cast hf1) (by exact_mod_cast hfr) (by exact_mod_cast hrn) (by positivity) hn hDF
  have hwg0 : 0 < (WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1 := by positivity
  have hwgF : Real.log ((fdeg D.host.E : ℝ) * ((WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1) + 2) ≤ 5 * large₂.sc.L := by
    rw [hfdeg]; exact hW2
  have hspread : ∀ k, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤
      (WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1 := fun k => by linarith [(h10 k).1]
  have hla : ∀ k, Real.log (1 + ∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ 3 * large₂.sc.L :=
    fun k => hW3 _ (by positivity) (h10 k).2
  rcases isEmpty_or_nonempty (T.U j σ).Comp with hE | ⟨⟨k₁⟩⟩
  · exact ⟨fun k => isEmptyElim k, 1, _, le_rfl, by simp; positivity, hwg0, hW1, hwgF, fun k => isEmptyElim k⟩
  have hPr : GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M :=
    fun k γ h1 h2 => hGam j hj σ hσ k γ h1 h2
  choose Xx hXx hXg hXΛ hXk0 hXNA hXNC using GlobalTheory.T.exists_rankOneCuspLatticeData_of_principal D T.toCore h.toLawsCore j hj σ hσ hPr
  choose e heNA heNC heg hek0 using fun k => exists_ext (Xx k) _ (hXx k) _ (hXΛ k) NA
    (Ideal.absNorm D.host.ccK) hNA0 hcc0 hNAi hccA
  have hMpos : 0 < T.Q.l.M := by rw [← hXg k₁]; exact (Xx k₁).g_pos
  have hlev : T.Q.l.M = D.host.g 0 * D.host.g 1 := level_M_eq_g_zero_mul_g_one_of_lawsM T.toCore h.toLawsCore.toLawsM

  have hgL : Real.log (T.Q.l.M : ℝ) ≤ 19 * large₂.sc.L := by
    have h0 : D.host.g 0 ≠ 0 := fun h0 => by simp [hlev, h0] at hMpos
    have h1 : D.host.g 1 ≠ 0 := fun h1 => by simp [hlev, h1] at hMpos
    rw [hlev, Nat.cast_mul, Real.log_mul (by exact_mod_cast h0) (by exact_mod_cast h1)]
    linarith [hgi 0, hgi 1]

  have hmX : ∀ k, IsIntegral ℤ ((m : D.host.E) * (2 * ((T.U j σ).X k).ξ0)) := by
    intro k
    rcases GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq D.host.E D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀
      hxicc ((T.U j σ).X k).ξ0_im (by rw [hxiabs, h.xiAbs j hj σ hσ k]) with h1 | h1
    · rw [h1]; exact hmi
    · rw [h1]; convert hmi.neg using 1; ring
  have hMk : ∀ k, ((e k).toX.g * (e k).toX.NA * (e k).toX.NC * m : ℕ) =
      T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m := by
    intro k
    show (e k).g * (e k).NA * (e k).NC * m = _
    rw [heg, heNA, heNC, hXg]
  have hM1 : 1 ≤ T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hMpos hNA0) hcc0) hm0
  refine ⟨e, ((T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m : ℕ) : ℝ), _, by exact_mod_cast hM1, ?_, hwg0, hW1,
    hwgF, fun k => ⟨hspread k, ?_, hla k, ?_, ?_, ?_, ?_⟩⟩
  · push_cast
    have hN : (0 : ℝ) < NA := by exact_mod_cast hNA0
    have hC : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hcc0
    have hm : (0 : ℝ) < m := by exact_mod_cast hm0
    have hg : (0 : ℝ) < T.Q.l.M := by exact_mod_cast hMpos
    rw [Real.log_mul (by positivity) hm.ne', Real.log_mul (by positivity) hC.ne',
      Real.log_mul hg.ne' hN.ne']
    linarith
  · intro v hv hv0 b hb hbi
    obtain ⟨γ, hγ, hγf⟩ := GlobalTheory.TransvLevel.transv_mem D.host.E D.R.r (e k).toX m (hmX k) v hv hv0 b hb hbi
    refine ⟨γ, hγ, h.chiTriv j hj σ hσ _ _ (Formalism.L2.Pj.dom_wtA w) k γ hγ, fun τ => ?_⟩
    have := hγf τ
    rw [hMk k] at this
    exact this
  · rw [heNA]; exact hNAL
  · rw [heNC]; exact hcc
  · rw [heg, hXg]; exact hgL
  · rw [hek0, hXk0]; exact hk0L

end GlobalTheory.CuspDataBounds
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValueCanonicalConnectionEqPolyDeriv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem sum_support_natCast_smul {σ K : Type} [Field K] [Algebra K ℂ] (N : ℕ) (P : MvPolynomial σ K)
    (hs : ((N : K) • P).support = P.support) (v : (σ →₀ ℕ) → ℂ) :
    ∑ m ∈ ((N : K) • P).support, algebraMap K ℂ (((N : K) • P).coeff m) * v m =
      (N : ℂ) * ∑ m ∈ P.support, algebraMap K ℂ (P.coeff m) * v m := by
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, map_natCast, _root_.mul_assoc]

theorem harm_nab_eq_polyDeriv : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : Fin n → (Fin g → ℂ) → ℂ), (∀ b, Φ.toAnFr.Rd k (F b) (θ b)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y k (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, θ b (z b)) 0 := by
  intro hC E _ _ _ H Dw l Xo c _ _ y g ty el Φ nab hnab k n F θ hθ a P hP
  classical
  obtain ⟨N, hN, hNP, hs⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  obtain ⟨C₁, hex₁, hpin₁⟩ := hnab.2 ℂ y
  choose f₁ hf₁ using fun b => hex₁ k (F b)
  obtain ⟨C, hd, hh, hF, hu, hgerm⟩ := GlobalTheory.T.exists_analytic_biextension_chart_complex_point E H Dw l Xo c y g ty el Φ hnab.1
  subst hd
  have hdiff : ∀ b, Differentiable ℂ (θ b) := fun b =>
    ((GlobalTheory.T.section_reading_existsUnique_isTheta _ _ _ _ _ Φ.toAnFr k (F b)).2.1 (θ b) (hθ b)).1
  have hg : ∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (tay (θ b) 0) := fun b => by
    have h := hgerm k (F b) (θ b) (hθ b)
    have e : (fun p : Fin 1 × Fin C.d => (p.1, Fin.cast (rfl : C.d = C.d).symm p.2)) = id := rfl
    simp only [e, MvPowerSeries.rename_id, AlgHom.id_apply] at h
    exact h
  have h := hC E H Dw l Xo c hnab.1 ℂ y C₁ C k n F f₁ (fun b => tay (θ b) 0) hf₁ hg a _ hNP
  unfold chartVal at h
  rw [sum_support_natCast_smul N P hs, sum_support_natCast_smul N P hs] at h
  have h' := mul_left_cancel₀ (Nat.cast_ne_zero.2 hN.ne' : (N : ℂ) ≠ 0) h
  have e₁ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C₁.B.nabVal ℂ C₁.h H.w0 k (f₁ b) C₁.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₁ k (F b) (f₁ b) (hf₁ b) (colOf m b)
  simp only [e₁]
  rw [h']
  have huu : C.uvec = fun ℓ : Lt1 Dw => (Pi.single (el.symm ℓ) 1 : Fin C.d → ℂ) := by
    funext ℓ i
    rw [hu ℓ i, Pi.single_apply]
    rfl
  have hpd := GlobalTheory.T.polyDeriv_prod_column_functions (Fin C.d → ℂ) (E →+* ℂ) Dw.mult n
    (fun ℓ : Lt1 Dw => (Pi.single (el.symm ℓ) 1 : Fin C.d → ℂ)) θ hdiff
    (MvPolynomial.map (algebraMap c.F ℂ) P)
  refine Eq.trans ?_ hpd.symm
  rw [MvPolynomial.support_map_of_injective P (algebraMap c.F ℂ).injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [hh, huu]
  exact nabVal_additive C.B hF H.w0 k ((GlobalTheory.SCV.contDiff_of_differentiable (hdiff b) _).contDiffAt) _ _

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortValue

theorem finite_levelQuotient {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem map_weighted_finsum {F S₁ S₂ T Q : Type} [Field F] [CommRing S₁] [CommRing S₂] [CommRing T]
    [Algebra F S₁] [Algebra F S₂] [Algebra F T] [Finite Q] (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T)
    (k : F) (w : Q → F) (A₁ : Q → S₁) (A₂ : Q → S₂) (h : ∀ q, ψ₁ (A₁ q) = ψ₂ (A₂ q)) :
    ψ₁ (algebraMap F S₁ k * ∑ᶠ q, algebraMap F S₁ (w q) * A₁ q) =
      ψ₂ (algebraMap F S₂ k * ∑ᶠ q, algebraMap F S₂ (w q) * A₂ q) := by
  haveI := Fintype.ofFinite Q
  simp only [finsum_eq_sum_of_fintype, map_mul, map_sum, AlgHom.commutes, h]

end GlobalTheory.ShortValue

namespace GlobalTheory

theorem shortThetaValue_existsUnique_natural : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, ShortValAt Xo c nab w Λ β N P y v) ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 → ShortValAt Xo c nab w Λ β N P y v → φ v0 = v := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hN a P hP w β
  haveI := ShortValue.finite_levelQuotient Dw l
  have cmp := GlobalTheory.T.shortThetaSum_eq_of_witnesses_common_algebra hL hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hP
  have nat : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 →
      ShortValAt Xo c nab w Λ β N P y v → φ v0 = v := by
    intro S T _ _ _ _ φ y0 y hφ v0 v h0 h1
    obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, e1⟩ := h0
    obtain ⟨S2, _, _, φ2, y2, z2, tp2, F2, hf2, hm2, hz2, hg2, ht2, hu2, e2⟩ := h1
    obtain ⟨U, _, _, ψ2, ψ1, hc, -, hinj⟩ :=
      exists_faithfullyFlat_pushout c.F S S2 S1 (φ2.comp φ) φ1 hf1
    have key := cmp S y0 S1 φ1 y1 z1 tp1 F1 S2 (φ2.comp φ) y2 z2 tp2 F2 hm1
      (FramedBaseChange.trans φ φ2 hφ hm2) hz1 hg1 ht1 hu1 hz2 hg2 ht2 hu2 U ψ1 ψ2 hc.symm
    have hinj2 : Function.Injective φ2 := hf2.injective
    apply hinj2
    apply hinj
    have e0 : ψ2 (φ2 (φ v0)) = ψ1 (φ1 v0) := AlgHom.congr_fun hc v0
    rw [e0, e1, e2]
    exact ShortValue.map_weighted_finsum ψ1 ψ2 _ w _ _ key
  refine ⟨fun S _ _ y => ?_, nat⟩
  obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1⟩ :=
    GlobalTheory.T.exists_faithfullyFlat_cover_shortThetaValue_data hL E H Dw l Xo c n Λ N hU hT hN S y
  obtain ⟨v, hv, -⟩ := existsUnique_preimage_of_faithfullyFlat c.F S S1 φ1 hf1
    (algebraMap c.F S1 (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S1 (w q) *
        ∑ i, ∑ m ∈ P.support, algebraMap c.F S1 (P.coeff m) *
          ∏ b, nab y1 ((N : ℤ) ^ 2) (F1 q i b) (colOf m b))
    (fun T _ _ ψ1 ψ2 hc => ShortValue.map_weighted_finsum ψ1 ψ2 _ w _ _
      (cmp S y S1 φ1 y1 z1 tp1 F1 S1 φ1 y1 z1 tp1 F1 hm1 hm1 hz1 hg1 ht1 hu1 hz1 hg1 ht1 hu1 T ψ1 ψ2 hc))
  have hv' : ShortValAt Xo c nab w Λ β N P y v :=
    ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, hv⟩
  exact ⟨v, hv', fun v' h' => nat S S (AlgHom.id c.F S) y y (FramedBaseChange.refl y) v' v h' hv'⟩

end GlobalTheory
end

