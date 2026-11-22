import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0028
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0002

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferentiableOnAvg
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DHolH

variable {D : D7} {n : ℕ} {V : HSp D}

structure Fam (V : HSp D) (ν : Measure (GA D V)) (U : Set ℂ) (f : ℂ → Mx D V.rank n → ℂ) : Prop where
  diff : ∀ x, DifferentiableOn ℂ (fun z => f z x) U
  maj : ∀ z₀ ∈ U, ∃ ε > 0, Metric.ball z₀ ε ⊆ U ∧ ∃ M : Mx D V.rank n → ℂ, Continuous M ∧ absThetaInt V ν M < ⊤ ∧
    ∀ z ∈ Metric.ball z₀ ε, ∀ x, ‖f z x‖ ≤ ‖M x‖
  meas : ∀ z ∈ U, AEStronglyMeasurable (descend (GQ V) (thS V (f z))) (autMeasure V ν)

def dF (f : ℂ → Mx D V.rank n → ℂ) : ℂ → Mx D V.rank n → ℂ := fun z x => deriv (fun w => f w x) z

def iF (f : ℂ → Mx D V.rank n → ℂ) (r : ℕ) : ℂ → Mx D V.rank n → ℂ := fun z x => iteratedDeriv r (fun w => f w x) z

theorem iF_zero (f : ℂ → Mx D V.rank n → ℂ) : iF f 0 = f := by
  funext z x; simp [iF]

theorem iF_succ (f : ℂ → Mx D V.rank n → ℂ) (r : ℕ) : iF f (r + 1) = dF (iF f r) := by
  funext z x; simp only [iF, dF, iteratedDeriv_succ]

theorem cauchy_le {g : ℂ → ℂ} {U : Set ℂ} (hg : DifferentiableOn ℂ g U) {z : ℂ} {r C : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall z r ⊆ U) (hC : ∀ w ∈ Metric.sphere z r, ‖g w‖ ≤ C) : ‖deriv g z‖ ≤ C / r := by
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ hC
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball z hr.ne']
  exact hg.mono hsub

theorem fam_hasDeriv (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    AEStronglyMeasurable (descend (GQ V) (thS V (dF f z₀))) (autMeasure V ν) ∧
    HasDerivAt (fun z => ∫ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν)
      (∫ q, descend (GQ V) (thS V (dF f z₀)) q ∂autMeasure V ν) z₀ := by
  obtain ⟨ε, hε, hball, M, hMc, hMfin, hMb⟩ := hf.maj z₀ hz₀
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hsubU : ∀ z ∈ Metric.ball z₀ r, Metric.closedBall z r ⊆ U := by
    intro z hz w hw
    apply hball
    rw [Metric.mem_ball] at hz ⊢
    rw [Metric.mem_closedBall] at hw
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < r + r := by linarith
      _ ≤ ε := by rw [hr]; linarith
  have hmemM : ∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.sphere z r, w ∈ Metric.ball z₀ ε := by
    intro z hz w hw
    rw [Metric.mem_ball] at hz ⊢
    rw [Metric.mem_sphere] at hw
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < r + r := by linarith
      _ ≤ ε := by rw [hr]; linarith
  have hcb : ∀ z ∈ Metric.ball z₀ r, ∀ x, ‖dF f z x‖ ≤ ‖M x‖ / r := fun z hz x =>
    cauchy_le (hf.diff x) hr0 (hsubU z hz) fun w hw => hMb w (hmemM z hz w hw) x
  have hballU : Metric.ball z₀ r ⊆ U := fun z hz => hsubU z hz (Metric.mem_closedBall_self hr0.le)
  have hz₀r : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr0
  have hz₀ε : z₀ ∈ Metric.ball z₀ ε := Metric.mem_ball_self hε

  have hfinq := ae_absTheta_lt V ν hMc hMfin
  have hsumM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
      Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => ‖M (invPt V q.out ξ)‖ := by
    intro q hq
    refine Summable.of_enorm ?_
    simpa [GlobalTheory.AutomorphicL2Unitary.descend, absTheta] using hq.ne
  have htsM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖M (invPt V q.out ξ)‖ = (descend (GQ V) (absTheta V M) q).toReal := by
    intro q hq
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, absTheta]
    rw [ENNReal.tsum_toReal_eq fun ξ => enorm_ne_top]
    simp

  have hdiff : ∀ᵐ q ∂autMeasure V ν, ∀ z ∈ Metric.ball z₀ r,
      HasDerivAt (fun z => descend (GQ V) (thS V (f z)) q) (descend (GQ V) (thS V (dF f z)) q) z := by
    filter_upwards [hfinq] with q hq z hz
    have hs := hsumM q hq
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS]
    refine hasDerivAt_tsum_of_isPreconnected (u := fun ξ => ‖M (invPt V q.out ξ)‖ / r) (hs.div_const r)
      Metric.isOpen_ball (convex_ball z₀ r).isPreconnected (fun ξ y hy => ?_) (fun ξ y hy => hcb y hy _) hz₀r ?_ hz
    · exact ((hf.diff _).differentiableAt (hU.mem_nhds (hballU hy))).hasDerivAt
    · exact Summable.of_norm_bounded hs fun ξ => hMb z₀ hz₀ε _

  have hmeas' : AEStronglyMeasurable (descend (GQ V) (thS V (dF f z₀))) (autMeasure V ν) := by
    let s : ℕ → ℂ := fun k => z₀ + ((r / 2 / ((k : ℝ) + 1) : ℝ) : ℂ)
    have hs_ne : ∀ k, s k ≠ z₀ := by
      intro k h
      have : ((r / 2 / ((k : ℝ) + 1) : ℝ) : ℂ) = 0 := by simpa [s] using h
      have h2 : r / 2 / ((k : ℝ) + 1) ≠ 0 := by positivity
      exact h2 (by exact_mod_cast this)
    have hs_mem : ∀ k, s k ∈ Metric.ball z₀ r := by
      intro k
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [s, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      calc r / 2 / ((k : ℝ) + 1) ≤ r / 2 := div_le_self (by positivity) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
        _ < r := by linarith
    have hs_lim : Tendsto s atTop (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hs_ne⟩
      have : Tendsto (fun k : ℕ => r / 2 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (r / 2)
        rw [mul_zero] at h0
        refine h0.congr fun k => ?_
        ring
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp this
      simpa [s] using (tendsto_const_nhds (x := z₀)).add h2
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun k q => (s k - z₀)⁻¹ • (descend (GQ V) (thS V (f (s k))) q - descend (GQ V) (thS V (f z₀)) q))
      (fun k => ((hf.meas _ (hballU (hs_mem k))).sub (hf.meas _ hz₀)).const_smul (s k - z₀)⁻¹) ?_
    filter_upwards [hdiff] with q hq
    have hd := hq z₀ hz₀r
    exact (hasDerivAt_iff_tendsto_slope.1 hd).comp hs_lim
  refine ⟨hmeas', ?_⟩
  have hint0 : Integrable (descend (GQ V) (thS V (f z₀))) (autMeasure V ν) := by
    refine ⟨hf.meas _ hz₀, lt_of_le_of_lt (lintegral_mono fun q => ?_) (lt_of_le_of_lt (le_refl _) hMfin)⟩
    exact (enorm_thS_le V _ q.out).trans (absTheta_mono V (hMb z₀ hz₀ε) q.out)
  have hbound : ∀ᵐ q ∂autMeasure V ν, ∀ z ∈ Metric.ball z₀ r,
      ‖descend (GQ V) (thS V (dF f z)) q‖ ≤ (descend (GQ V) (absTheta V M) q).toReal / r := by
    filter_upwards [hfinq] with q hq z hz
    have hs := hsumM q hq
    have hs' : Summable fun ξ => ‖dF f z (invPt V q.out ξ)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hcb z hz _) (hs.div_const r)
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS] at *
    calc ‖∑' ξ, dF f z (invPt V q.out ξ)‖ ≤ ∑' ξ, ‖dF f z (invPt V q.out ξ)‖ := norm_tsum_le_tsum_norm hs'
      _ ≤ ∑' ξ, ‖M (invPt V q.out ξ)‖ / r := hs'.tsum_le_tsum (fun ξ => hcb z hz _) (hs.div_const r)
      _ = (∑' ξ, ‖M (invPt V q.out ξ)‖) / r := tsum_div_const
      _ = _ := by rw [htsM q hq]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ hr0) (Eventually.mono (hU.mem_nhds hz₀) fun z hz => hf.meas z hz)
    hint0 hmeas' hbound ((integrable_absTheta_toReal V ν hMc hMfin).div_const r) hdiff).2

theorem fam_dF (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) : Fam V ν U (dF f) where
  diff x := (hf.diff x).deriv hU
  maj z₀ hz₀ := by
    obtain ⟨ε, hε, hball, M, hMc, hMfin, hMb⟩ := hf.maj z₀ hz₀
    refine ⟨ε / 2, by positivity, (Metric.ball_subset_ball (by linarith)).trans hball, ((2 / ε : ℝ) : ℂ) • M,
      hMc.const_smul _, absThetaInt_smul_lt V ν _ hMfin, ?_⟩
    intro z hz x
    have hsub : Metric.closedBall z (ε / 2) ⊆ U := by
      intro w hw
      apply hball
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_closedBall] at hw
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    have hmem : ∀ w ∈ Metric.sphere z (ε / 2), w ∈ Metric.ball z₀ ε := by
      intro w hw
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_sphere] at hw
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    have h := cauchy_le (hf.diff x) (by positivity : (0 : ℝ) < ε / 2) hsub fun w hw => hMb w (hmem w hw) x
    calc ‖dF f z x‖ ≤ ‖M x‖ / (ε / 2) := h
      _ = ‖(((2 / ε : ℝ) : ℂ) • M) x‖ := by
        rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        field_simp
  meas z hz := (fam_hasDeriv V ν hU hf hz).1

theorem fam_iF (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) (r : ℕ) : Fam V ν U (iF f r) := by
  induction r with
  | zero => rwa [iF_zero]
  | succ r ih => rw [iF_succ]; exact fam_dF V ν hU ih

theorem iteratedDeriv_avg (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) (r : ℕ) :
    ∀ z ∈ U, iteratedDeriv r (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) z =
      ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν := by
  have hder : ∀ r, ∀ z ∈ U, HasDerivAt (fun z => ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν)
      (⨍ q, descend (GQ V) (thS V (iF f (r + 1) z)) q ∂autMeasure V ν) z := by
    intro r z hz
    simp only [average_eq]
    rw [iF_succ]
    exact (fam_hasDeriv V ν hU (fam_iF V ν hU hf r) hz).2.const_smul _
  induction r with
  | zero => intro z _; simp [iF_zero]
  | succ r ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv r (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) =ᶠ[𝓝 z]
        fun z => ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν :=
      Eventually.mono (hU.mem_nhds hz) fun w hw => ih w hw
    rw [heq.deriv_eq]
    exact (hder r z hz).deriv

theorem differentiableOn_avg (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) :
    DifferentiableOn ℂ (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) U := by
  intro z hz
  simp only [average_eq]
  exact ((fam_hasDeriv V ν hU hf hz).2.const_smul _).differentiableAt.differentiableWithinAt

end PositivityTheory.Rg.Sw.Glob.DHolH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocE
section
noncomputable section

set_option linter.unusedSectionVars false

open scoped TensorProduct
open IsDedekindDomain NumberField GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def sigI (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : intLoc F E v →+* intLoc F E v :=
  (sigR (Fv F v) σ).restrict (intLoc F E v) (intLoc F E v) (fun _ hx => sigR_mem_intLoc σ hx)

theorem sigI_coe (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : intLoc F E v) :
    ((sigI σ v z : intLoc F E v) : Fv F v ⊗[F] E) = sigR (Fv F v) σ z := rfl

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem sigI_sigI (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F)) (z : intLoc F E v) :
    sigI σ v (sigI σ v z) = z := Subtype.ext (sigR_sigR σ hσ (Fv F v) (z : Fv F v ⊗[F] E))

theorem fixed_eq_tmul (σ : E →ₐ[F] E) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F))
    (z : Fv F v ⊗[F] E) (hz : sigR (Fv F v) σ z = z) : ∃ a : Fv F v, z = a ⊗ₜ[F] (1 : E) := by
  let φ : E →ₗ[F] E := σ.toLinearMap - LinearMap.id
  have hex : Function.Exact (Algebra.linearMap F E) φ := by
    intro y
    constructor
    · intro hy
      have : σ y = y := by have := hy; simp only [φ, LinearMap.sub_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply,
        sub_eq_zero] at this; exact this
      obtain ⟨c, hc⟩ := (hfix y).1 this
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      simp [φ]
  have hex' := Module.Flat.lTensor_exact (Fv F v) hex
  have hφ : φ.lTensor (Fv F v) z = 0 := by
    have key : ∀ w : Fv F v ⊗[F] E, φ.lTensor (Fv F v) w = sigR (Fv F v) σ w - w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => simp [φ, sigR, TensorProduct.tmul_sub]
      | add y w hy hw => rw [map_add, hy, hw, map_add]; abel
    rw [key, hz, sub_self]
  obtain ⟨w, hw⟩ := (hex' z).1 hφ
  refine ⟨TensorProduct.rid F (Fv F v) w, ?_⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [LinearMap.lTensor_tmul, Algebra.linearMap_apply, TensorProduct.rid_tmul]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add y w hy hw => rw [map_add, hy, hw, map_add, TensorProduct.add_tmul]

theorem mem_of_tmul_mem (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (h : a ⊗ₜ[F] (1 : E) ∈ intLoc F E v) :
    a ∈ v.adicCompletionIntegers F := by
  have h1 := absFin_le_one_of_mem_intLoc h
  rw [absFin_tmul_one] at h1
  exact (Valued.toNormedField.norm_le_one_iff).1 (by exact_mod_cast h1)

theorem tmul_one_mem (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (h : a ∈ v.adicCompletionIntegers F) :
    a ⊗ₜ[F] (1 : E) ∈ intLoc F E v := by
  simpa using tmul_mem_intLoc (E := E) h (1 : 𝓞 E)

theorem nontrivial_intLoc (v : HeightOneSpectrum (𝓞 F)) : Nontrivial (intLoc F E v) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' : ((0 : intLoc F E v) : Fv F v ⊗[F] E) = ((1 : intLoc F E v) : Fv F v ⊗[F] E) := congrArg Subtype.val h
  have := congrArg (absFin F v) h'
  rw [ZeroMemClass.coe_zero, OneMemClass.coe_one, absFin_zero, absFin_one] at this
  exact zero_ne_one this

theorem orbit_abs {R : Type} [CommRing R] (s : R →+* R) (hss : ∀ z, s (s z) = z)
    (hloc : ∀ z, s z = z → IsUnit z ∨ IsUnit (1 - z)) (𝔪 𝔫 : Ideal R) (h𝔪 : 𝔪.IsMaximal) (h𝔫 : 𝔫.IsMaximal) :
    𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap s := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hn1, hn2⟩ := hne
  have hsurj : Function.Surjective s := fun y => ⟨s y, hss y⟩
  have hcc : ∀ I : Ideal R, (I.comap s).comap s = I := by
    intro I; ext z; rw [Ideal.mem_comap, Ideal.mem_comap, hss]
  have hm' : (𝔪.comap s).IsMaximal := Ideal.comap_isMaximal_of_surjective s hsurj
  have hn' : (𝔫.comap s).IsMaximal := Ideal.comap_isMaximal_of_surjective s hsurj
  have hn3 : 𝔫.comap s ≠ 𝔪 := by
    intro h; apply hn2; rw [← h, hcc]
  have hn4 : 𝔫.comap s ≠ 𝔪.comap s := by
    intro h; apply hn1; rw [← hcc 𝔫, h, hcc]
  have c1 : 𝔪 ⊔ 𝔫 = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 h𝔫 (Ne.symm hn1)
  have c2 : 𝔪 ⊔ 𝔫.comap s = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 hn' (Ne.symm hn3)
  have c3 : 𝔪.comap s ⊔ 𝔫 = ⊤ := Ideal.IsMaximal.coprime_of_ne hm' h𝔫 (Ne.symm hn2)
  have c4 : 𝔪.comap s ⊔ 𝔫.comap s = ⊤ := Ideal.IsMaximal.coprime_of_ne hm' hn' (Ne.symm hn4)
  have d1 : 𝔪 ⊔ 𝔫 * 𝔫.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left c1).trans c2
  have d2 : 𝔪.comap s ⊔ 𝔫 * 𝔫.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left c3).trans c4
  have e1 : 𝔫 * 𝔫.comap s ⊔ 𝔪 = ⊤ := by rw [sup_comm]; exact d1
  have e2 : 𝔫 * 𝔫.comap s ⊔ 𝔪.comap s = ⊤ := by rw [sup_comm]; exact d2
  have d3 : 𝔫 * 𝔫.comap s ⊔ 𝔪 * 𝔪.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left e1).trans e2
  have h1 : (1 : R) ∈ 𝔫 * 𝔫.comap s ⊔ 𝔪 * 𝔪.comap s := by rw [d3]; exact Submodule.mem_top
  obtain ⟨y, hy, x, hx, hxy⟩ := Submodule.mem_sup.1 h1
  have hxm : x ∈ 𝔪 := (Ideal.mul_le_left : 𝔪 * 𝔪.comap s ≤ 𝔪) hx
  have hyn : y ∈ 𝔫 := (Ideal.mul_le_left : 𝔫 * 𝔫.comap s ≤ 𝔫) hy
  have hyn'' : y ∈ 𝔫.comap s := (Ideal.mul_le_right : 𝔫 * 𝔫.comap s ≤ 𝔫.comap s) hy
  have hyn' : s y ∈ 𝔫 := Ideal.mem_comap.1 hyn''
  have hzm : x * s x ∈ 𝔪 := Ideal.mul_mem_right _ _ hxm
  have hfz : s (x * s x) = x * s x := by rw [map_mul, hss, mul_comm]
  have h1z : 1 - x * s x ∈ 𝔫 := by
    have hx' : x = 1 - y := by rw [← hxy]; ring
    have e : 1 - x * s x = y + s y - y * s y := by rw [hx', map_sub, map_one]; ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hyn hyn') (Ideal.mul_mem_right _ _ hyn)
  rcases hloc _ hfz with hu | hu
  · exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ hzm hu)
  · exact h𝔫.ne_top (Ideal.eq_top_of_isUnit_mem _ h1z hu)

theorem isUnit_tmul (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletionIntegers F)ˣ) :
    IsUnit (⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ :
      intLoc F E v) := by
  refine ⟨⟨_, ⟨((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) ⊗ₜ[F] (1 : E),
    tmul_one_mem v _ (u⁻¹ : (v.adicCompletionIntegers F)ˣ).1.2⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · show ((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) * (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) :
      v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Subring.coe_mul, Units.mul_inv]; rfl
  · show (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) *
      ((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Subring.coe_mul, Units.inv_mul]; rfl

theorem fixed_local (σ : E →ₐ[F] E) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F))
    (z : intLoc F E v) (hz : sigI σ v z = z) : IsUnit z ∨ IsUnit (1 - z) := by
  obtain ⟨a, ha⟩ := fixed_eq_tmul σ hfix v (z : Fv F v ⊗[F] E) (by rw [← sigI_coe]; exact congrArg Subtype.val hz)
  have haO : a ∈ v.adicCompletionIntegers F := mem_of_tmul_mem v a (ha ▸ z.2)
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨a, haO⟩ : v.adicCompletionIntegers F) with hu | hu
  · left
    obtain ⟨u, hu⟩ := hu
    have e : z = ⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ :=
      Subtype.ext (by rw [ha, hu])
    rw [e]; exact isUnit_tmul v u
  · right
    obtain ⟨u, hu⟩ := hu
    have e : 1 - z = ⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ := by
      apply Subtype.ext
      rw [hu]
      show (1 : Fv F v ⊗[F] E) - (z : Fv F v ⊗[F] E) = (1 - a) ⊗ₜ[F] (1 : E)
      rw [ha, TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]
    rw [e]; exact isUnit_tmul v u

theorem orbit (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ 𝔪 : Ideal (intLoc F E v), 𝔪.IsMaximal ∧ ∀ 𝔫 : Ideal (intLoc F E v), 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap (sigI σ v) := by
  have := nontrivial_intLoc (E := E) v
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (intLoc F E v)
  exact ⟨𝔪, h𝔪, fun 𝔫 h𝔫 => orbit_abs (sigI σ v) (sigI_sigI σ hσ v) (fixed_local σ hfix v) 𝔪 𝔫 h𝔪 h𝔫⟩

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenOps
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenOpsH

theorem gen_nbar (hU : UnipTau) (hW : WEx) (hS : SchOps) (hF : FTfact)
    {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (y : GR n) (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c)
    (hyc : mR y = nbar c) :
    ∃ κ γ : ℂ, κ ≠ 0 ∧ ((∃ (Ψ : Mx D V.rank n → ℂ) (x₀ : Mx D V.rank n), AwayCls θ τ fr Ψ ∧ Ψ x₀ ≠ 0) → γ ≠ 0) ∧
      (∀ f : (Fin V.rank → Fin n → ℂ) → ℂ, IsSch f → IsSch (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) ∧
        IsSch (fun u => κ * ftLoc ε (tLoc l τ) f u)) ∧
      ∀ (Ψ : Mx D V.rank n → ℂ) (hΨ : AwayCls θ τ fr Ψ) (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => γ⁻¹ * (κ * ftLoc ε (tLoc l τ)
          (fun v => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε v).trace) *
            (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)) u)) Ψ := by
  have hfr : IsUnit fr.det := hC.hfr.1
  obtain ⟨w, hw⟩ := hW D n
  obtain ⟨yn, hyn⟩ := OG.exists_nU n (-c) (by rw [Matrix.conjTranspose_neg, hc])
  have hιn : ι yn = w⁻¹ * ι y * w := OG.iota_conj hC.hθ hC.hι w hw y yn c hyc hyn
  have hιy : ι y = w * ι yn * w⁻¹ := by rw [hιn]; group
  obtain ⟨κ, A, A', hκ, hFT⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC w hw
  obtain ⟨f0, hf0, hf00⟩ := (hS V.rank n).2.2.2.2
  have h0 := hFT 0 (OG.awayCls_zero τ fr)
  let e : (Fin V.rank → Fin n → ℂ) → ℂ := fun u =>
    Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u).trace)
  let F' : ((Fin V.rank → Fin n → ℂ) → ℂ) → (Fin V.rank → Fin n → ℂ) → ℂ := fun f u =>
    κ⁻¹ * ftLoc ε (-tLoc l τ) f u
  let Fw : ((Fin V.rank → Fin n → ℂ) → ℂ) → (Fin V.rank → Fin n → ℂ) → ℂ := fun f u => κ * ftLoc ε (tLoc l τ) f u
  have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
  have hE : ∀ f, IsSch f → IsSch (fun u => e u * F' f u) := fun f hf =>
    (hS V.rank n).2.2.2.1 ε (tLoc l τ) (-c) (F' f) hc' ((h0.2.2 f hf).2.1)
  set γ : ℂ := Fw (F' f0) (0 : Matrix (Fin V.rank) (Fin n) ℂ) with hγdef

  have hrelAll : ∀ Ψ (hΨ : AwayCls θ τ fr Ψ), ∀ x, Ψ x = γ * A (A' Ψ) x := by
    intro Ψ hΨ
    obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
    have kA := hFT (A' Ψ) hA'Ψ
    have hcons : ∀ g (hg : IsSch g), tens θ τ fr g Ψ = tens θ τ fr (Fw (F' g)) (A (A' Ψ)) := by
      intro g hg
      have k1g := (hFΨ g hg).2.2.2
      have kcg := (kA.2.2 (F' g) ((hFΨ g hg).2.1)).2.2.1
      have hΦ1 : ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ = ⟨tens θ τ fr (F' g) (A' Ψ), hA'Ψ.2 _ ((hFΨ g hg).2.1)⟩ :=
        Subtype.ext k1g
      have hid : ω w (ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩) = ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [hΦ1] at hid
      rw [← kcg, hid]
    intro x
    obtain ⟨x', hx'1, hx'2, hx'3⟩ := OG.exists_slice hC.hθ τ x (fr * (0 : Matrix (Fin V.rank) (Fin n) ℂ))
    have h1 := congrFun (hcons f0 hf0) x'
    have hf00' : f0 (0 : Matrix (Fin V.rank) (Fin n) ℂ) = 1 := hf00
    rw [OG.tens_at τ hfr _ _ x' 0 hx'1, OG.tens_at τ hfr _ _ x' 0 hx'1, hf00', one_mul, hΨ.1 x' x hx'2 hx'3,
      kA.1.1 x' x hx'2 hx'3] at h1
    exact h1
  refine ⟨κ, γ, hκ, ?_, fun f hf => ⟨(h0.2.2 f hf).2.1, (h0.2.2 f hf).1⟩, ?_⟩
  · rintro ⟨Ψ, x₀, hΨ, hx₀⟩ hγ
    exact hx₀ (by rw [hrelAll Ψ hΨ x₀, hγ, zero_mul])
  intro Ψ hΨ f hf
  obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
  have k1 := (hFΨ f hf).2.2.2
  have kA := hFT (A' Ψ) hA'Ψ
  have kr := (kA.2.2 (fun u => e u * F' f u) (hE f hf)).2.2.1
  have hrel := hrelAll Ψ hΨ
  by_cases hγ : γ = 0
  · have hΨ0 : Ψ = 0 := funext fun x => by rw [hrel x, hγ, zero_mul]; rfl
    subst hΨ0
    have hz : (⟨tens θ τ fr f 0, hΨ.2 f hf⟩ : schwartzA θ V.rank n) = 0 := Subtype.ext (by funext x; simp [tens])
    rw [hz, map_zero]
    funext x
    simp [tens]
  · have hstep : ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ =
        ω w ⟨tens θ τ fr (fun u => e u * F' f u) (A' Ψ), hA'Ψ.2 _ (hE f hf)⟩ := by
      rw [hιy, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      congr 1
      apply Subtype.ext
      funext x
      rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC yn (-c) hc' hyn, k1]
      simp only [tens, e, F', mul_assoc]
    funext x
    rw [hstep, kr]
    simp only [tens]
    rw [hrel x]
    simp only [e, F']
    field_simp

end PositivityTheory.Rg.Sw.Glob.GenOpsH
end
end

