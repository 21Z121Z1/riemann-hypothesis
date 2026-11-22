import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0079
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0085
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOffZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

theorem hessC_half_log_normSq_add {D : ℕ} (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ)
    (hh : AnalyticAt ℂ h y) (hy : h y ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    hessC (fun w => Real.log (‖h w‖ ^ 2 + ε) / 2) y =
      ((ε / (2 * (‖h y‖ ^ 2 + ε) ^ 2) : ℝ) : ℂ) • hessC (fun w => ‖h w‖ ^ 2) y := by
  set L : (Fin D → ℂ) → ℝ := fun w => Real.log ‖h w‖ with hLdef
  set F : ℝ → ℝ := fun t => Real.log (Real.exp (2 * t) + ε) / 2 with hFdef
  set G : ℝ → ℝ := fun t => Real.exp (2 * t) with hGdef
  have hhc : ContDiffAt ℝ 2 h y := (hh.contDiffAt (n := 2)).restrict_scalars ℝ
  have hLc : ContDiffAt ℝ 2 L y := (hhc.norm ℝ hy).log (norm_ne_zero_iff.2 hy)
  have hL0 : hessC L y = 0 := ReciprocityTheory.AnForm.A.hessC_log_norm h y hh hy
  have he : ∀ t, HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * 2) t := fun t => by
    simpa using ((hasDerivAt_id t).const_mul 2).exp
  have hFc : ContDiff ℝ 2 F :=
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).add contDiff_const).log
      (fun t => by simp only [Function.comp_apply, id]; positivity) |>.div_const 2
  have hGc : ContDiff ℝ 2 G := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hF := HessCCompPluri.proof D F L y hFc.contDiffAt hLc hL0
  have hG := HessCCompPluri.proof D G L y hGc.contDiffAt hLc hL0
  have hdF : deriv F = fun t => Real.exp (2 * t) / (Real.exp (2 * t) + ε) := by
    funext t
    have hp : Real.exp (2 * t) + ε ≠ 0 := by positivity
    refine (((he t).add_const ε).log hp |>.div_const 2).deriv.trans ?_
    field_simp
  have hddF : ∀ t, deriv (deriv F) t = 2 * ε * Real.exp (2 * t) / (Real.exp (2 * t) + ε) ^ 2 := by
    intro t
    have hp : Real.exp (2 * t) + ε ≠ 0 := by positivity
    rw [hdF]
    refine ((he t).div ((he t).add_const ε) hp).deriv.trans ?_
    field_simp
    ring
  have hdG : deriv G = fun t => Real.exp (2 * t) * 2 := funext fun t => (he t).deriv
  have hddG : ∀ t, deriv (deriv G) t = Real.exp (2 * t) * 2 * 2 := fun t => by
    rw [hdG]
    exact ((he t).mul_const 2).deriv
  have hexp : ∀ w, h w ≠ 0 → Real.exp (2 * L w) = ‖h w‖ ^ 2 := fun w hw => by
    rw [hLdef, show 2 * Real.log ‖h w‖ = Real.log (‖h w‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  have hev : ∀ᶠ w in 𝓝 y, h w ≠ 0 := hh.continuousAt.eventually_ne hy
  have eF : hessC (fun w => Real.log (‖h w‖ ^ 2 + ε) / 2) y = hessC (fun w => F (L w)) y :=
    ReciprocityTheory.AnForm.A.hessC_congr' (hev.mono fun w hw => by simp only [hFdef, hexp w hw])
  have eG : hessC (fun w => ‖h w‖ ^ 2) y = hessC (fun w => G (L w)) y :=
    ReciprocityTheory.AnForm.A.hessC_congr' (hev.mono fun w hw => by simp only [hGdef, hexp w hw])
  rw [eF, eG, hF, hG, hddF, hddG, hexp y hy, smul_smul]
  congr 1
  have ha : 0 < ‖h y‖ ^ 2 := by positivity
  push_cast
  field_simp

theorem LelongLimitOffZero.proof (hM : ChartMassCompact.Statement) : LelongLimitOffZero.Statement := by
  classical
  intro n d J u f φ hJ hdim hu hf hfc hφ hdisj
  unfold varInt
  split_ifs with hA
  swap
  · exact tendsto_const_nhds
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection J A := hA.choose_spec
  have hZc : IsClosed (zeroSet J) := by
    have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
      ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hK : IsCompact (tsupport f ∩ zeroSet J) := hfc.isCompact.inter_right hZc
  have hu0 : ∀ x ∈ tsupport f ∩ zeroSet J, linEval u x ≠ 0 := fun x hx h0 =>
    Set.disjoint_left.1 hdisj hx.1 ⟨hx.2, h0⟩
  set q : (Fin n → ℂ) → ℝ := fun x => ‖linEval u x‖ ^ 2 with hq
  have hqc : ContDiff ℝ ∞ q := (contDiff_norm_sq ℝ).comp (contDiff_linEval u)
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ tsupport f ∩ zeroSet J, m ≤ q x := by
    rcases (tsupport f ∩ zeroSet J).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hqc.continuous.continuousOn
      exact ⟨q x₀, by have := hu0 x₀ hx₀; simp only [hq]; positivity, fun x hx => hmin hx⟩
  have hGi : Integrable (chartAbsDens J A f (vecCons q φ)) := by
    refine hM n (d + 1) J A f _ hJ hdim hAf hf.continuous.continuousOn (fun i => ?_) (Or.inl hfc)
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) hqc
    · simpa using hφ j
  have hb : ∀ ε : ℝ, 0 < ε → ∀ y, ‖chartDens J A f (vecCons (logReg u ε) φ) y‖ ≤
      ε / (2 * m ^ 2) * chartAbsDens J A f (vecCons q φ) y := by
    intro ε hε y
    rw [Real.norm_eq_abs]
    refine (abs_chartDens_le J A f _ y).trans ?_
    have hfin := (FibreBound.proof n (d + 1) J A hJ hdim hAf y).2.1
    unfold chartAbsDens
    refine sheetSum_le_mul hfin _ _ _ fun x hx s hs => ?_
    by_cases hfx : f x = 0
    · simp [hfx]
    have hxK : x ∈ tsupport f ∩ zeroSet J := ⟨subset_tsupport _ hfx, hx.1⟩
    obtain rfl : A *ᵥ x = y := hx.2
    obtain ⟨U, hU, hxU, hsd, hsx, -, -⟩ := hs
    have hsa : AnalyticAt ℂ s (A *ᵥ x) := analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ U (fun z => s z i) hU (differentiableOn_pi.1 hsd i) _ hxU
    have hha : AnalyticAt ℂ (fun w => linEval u (s w)) (A *ᵥ x) := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 hsa) j)
    have hne : linEval u (s (A *ᵥ x)) ≠ 0 := by rw [hsx]; exact hu0 x hxK
    have hH0 := hessC_half_log_normSq_add (fun w => linEval u (s w)) _ hha hne hε
    simp only [hsx] at hH0
    have hH : hessC (logReg u ε ∘ s) (A *ᵥ x) =
        ((ε / (2 * (q x + ε) ^ 2) : ℝ) : ℂ) • hessC (q ∘ s) (A *ᵥ x) := hH0
    rw [vecCons_comp, vecCons_comp, maDens_cons_of_hessC_eq_smul (logReg u ε ∘ s) (q ∘ s) _ _ _ hH]
    have ha : m ≤ q x := hm x hxK
    have hc0 : 0 ≤ ε / (2 * (q x + ε) ^ 2) := by positivity
    have hc : ε / (2 * (q x + ε) ^ 2) ≤ ε / (2 * m ^ 2) :=
      div_le_div_of_nonneg_left hε.le (by positivity) (by nlinarith)
    calc |f x * (ε / (2 * (q x + ε) ^ 2) * maDens (Fin.cons (q ∘ s) fun k => φ k ∘ s) (A *ᵥ x))|
        = ε / (2 * (q x + ε) ^ 2) * |f x * maDens (Fin.cons (q ∘ s) fun k => φ k ∘ s) (A *ᵥ x)| := by
          rw [mul_left_comm, abs_mul, abs_of_nonneg hc0]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have hlim : Tendsto (fun ε : ℝ => ε / (2 * m ^ 2) * ∫ y, chartAbsDens J A f (vecCons q φ) y)
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ε / (2 * m ^ 2) * ∫ y, chartAbsDens J A f (vecCons q φ) y) := by
      fun_prop
    exact tendsto_nhdsWithin_of_tendsto_nhds (hc.tendsto' 0 0 (by simp))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  unfold chartInt
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le (hGi.const_mul _) (Eventually.of_forall (hb ε hε))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOnZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

theorem mem_minimalPrimes_sup_linForm {n : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)}
    {u : Fin n → ℂ} (hWm : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) :
    W.IsPrime ∧ zeroSet W ⊆ zeroSet J ∧ ∀ x ∈ zeroSet W, linEval u x = 0 := by
  have hle : J ⊔ Ideal.span {linForm u} ≤ W := hWm.1.2
  refine ⟨hWm.1.1, fun x hx q hq => hx q (hle (Ideal.mem_sup_left hq)), fun x hx => ?_⟩
  have := hx _ (hle (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  simpa [linForm, linEval] using this

theorem lelongSides_add (hAdd : VarIntAdd.Statement) {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {u : Fin n → ℂ} {φ : Fin d → (Fin n → ℂ) → ℝ} (hJ : J.IsPrime)
    (hφ : ∀ i, SmoothNear (zeroSet J) (φ i)) (g₁ g₂ : (Fin n → ℂ) → ℝ) (h1 : ContDiff ℝ ∞ g₁)
    (h1c : HasCompactSupport g₁) (h2 : ContDiff ℝ ∞ g₂) (h2c : HasCompactSupport g₂) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), varInt J (d + 1) (g₁ + g₂) (vecCons (logReg u ε) φ) =
      varInt J (d + 1) g₁ (vecCons (logReg u ε) φ) + varInt J (d + 1) g₂ (vecCons (logReg u ε) φ)) ∧
    (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d (g₁ + g₂) φ) =
      (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g₁ φ) +
      ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g₂ φ := by
  classical
  refine ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine hAdd n (d + 1) J g₁ g₂ _ hJ h1.continuous h1c h2.continuous h2c fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
    · simpa using hφ j
  · rw [← finsum_mem_add_distrib (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)]
    refine finsum_mem_congr rfl fun W hWm => ?_
    obtain ⟨hWp, hWJ, -⟩ := mem_minimalPrimes_sup_linForm hWm
    have hφW : ∀ i, SmoothNear (zeroSet W) (φ i) := fun i => by
      obtain ⟨U, hU, hSU, hC⟩ := hφ i
      exact ⟨U, hU, hWJ.trans hSU, hC⟩
    rw [hAdd n d W g₁ g₂ φ hWp h1.continuous h1c h2.continuous h2c hφW, mul_add]

theorem lelongLimit_off_small (hOff : LelongLimitOffZero.Statement) (hAdd : VarIntAdd.Statement)
    {n d : ℕ} {J I : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ} {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ))
    (hu : linForm u ∉ J) (hφ : ∀ i, SmoothNear (zeroSet J) (φ i))
    (hloc : ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
      ∃ N ∈ 𝓝 q, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
          (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
              (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
            (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ)))
    (g : (Fin n → ℂ) → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgI : Disjoint (tsupport g) (zeroSet I)) :
    Tendsto (fun ε => varInt J (d + 1) g (vecCons (logReg u ε) φ)) (𝓝[>] 0)
      (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
          (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ)) := by
  classical
  have hclosed : IsClosed (zeroSet J ∩ {x | linEval u x = 0}) := by
    refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
    · have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
    · exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  refine tendsto_of_forall_local_on_tsupport
    (fun ε g => varInt J (d + 1) g (vecCons (logReg u ε) φ))
    (fun g => ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
      (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ)
    (fun g₁ g₂ h1 h1c h2 h2c => (lelongSides_add hAdd hJ hφ g₁ g₂ h1 h1c h2 h2c).1)
    (fun g₁ g₂ h1 h1c h2 h2c => (lelongSides_add hAdd (u := u) hJ hφ g₁ g₂ h1 h1c h2 h2c).2)
    g hg hgc fun q hq => ?_
  by_cases hq0 : q ∈ zeroSet J ∩ {x | linEval u x = 0}
  · exact hloc q hq0.1 hq0.2 (Set.disjoint_left.1 hgI hq)
  · refine ⟨_, hclosed.isOpen_compl.mem_nhds hq0, fun g' hg' hg'c hg'N => ?_⟩
    have h0 : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
        (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g' φ) = 0 := by
      refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
      rw [finsum_eq_dif]
      by_cases hWm : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes
      · obtain ⟨-, hWJ, hWu⟩ := mem_minimalPrimes_sup_linForm hWm
        rw [dif_pos hWm, varInt_eq_zero_of_vanish W g' φ fun x hx =>
          image_eq_zero_of_notMem_tsupport fun hxs => hg'N hxs ⟨hWJ hx, hWu x hx⟩, mul_zero]
      · rw [dif_neg hWm]
    simp only [h0]
    exact hOff n d J u g' φ hJ hdim hu hg' hg'c hφ
      (Set.disjoint_left.2 fun x hx hx' => hg'N hx hx')

theorem LelongLimitOnZero.proof (hOff : LelongLimitOffZero.Statement)
    (hGood : LelongLimitGoodPoints.Statement) (hSmall : LelongMassNearSmall.Statement)
    (hAdd : VarIntAdd.Statement) : LelongLimitOnZero.Statement := by
  classical
  intro n d J u φ p hJ hdim hu hφ _ _
  refine ⟨Set.univ, Filter.univ_mem, fun f hf hfc _ => ?_⟩
  obtain ⟨I, hI, hIdim, hloc⟩ := hGood n d J u φ hJ hdim hu hφ
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨χ, hχ, ⟨U, hU, hIU, hχ1⟩, hTχ, hLχ⟩ :=
    hSmall n d J I u φ f hJ hdim hu hφ hI hIdim hf hfc (δ / 3) (by positivity)
  have hχf : ContDiff ℝ ∞ (fun x => χ x * f x) := hχ.mul hf
  have hχfc : HasCompactSupport (fun x => χ x * f x) := hfc.mul_left
  have hg : ContDiff ℝ ∞ (fun x => (1 - χ x) * f x) := (contDiff_const.sub hχ).mul hf
  have hgc : HasCompactSupport (fun x => (1 - χ x) * f x) := hfc.mul_left
  have hgI : Disjoint (tsupport fun x => (1 - χ x) * f x) (zeroSet I) := by
    refine Disjoint.mono_right hIU (Disjoint.closure_left ?_ hU)
    refine Set.disjoint_left.2 fun x hx hxU => hx ?_
    simp [hχ1 x hxU]
  have hsum : (fun x => χ x * f x) + (fun x => (1 - χ x) * f x) = f := by
    funext x
    simp only [Pi.add_apply]
    ring
  obtain ⟨hTadd, hLadd⟩ := lelongSides_add hAdd (u := u) hJ hφ _ _ hχf hχfc hg hgc
  rw [hsum] at hTadd hLadd
  refine ((Metric.tendsto_nhds.1
    (lelongLimit_off_small hOff hAdd hJ hdim hu hφ hloc _ hg hgc hgI) (δ / 3) (by positivity)).and
    (hTχ.and hTadd)).mono fun ε ⟨h1, h2, h3⟩ => ?_
  rw [Real.dist_eq] at h1 ⊢
  rw [h3, hLadd]
  rw [abs_lt] at h1 ⊢
  rw [abs_le] at h2 hLχ
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hLχ.1, hLχ.2]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimComponentBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

theorem comap_curveLocalRing_strictMono (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    StrictMono (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q))) := by
  refine Monotone.strictMono_of_injective (fun P Q h ↦ Ideal.comap_mono h) ?_
  intro P Q h
  apply PrimeSpectrum.comap_injective_of_surjective _ (Ideal.Quotient.mk_surjective (I := I.map
    (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))
  apply PrimeSpectrum.localization_comap_injective _ (RingHom.ker (eval q)).primeCompl
  exact h

theorem le_comap_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    I ≤ (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal := by
  intro x hx
  have h0 : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q)))))
      (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hx)
  change algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x ∈ P.asIdeal
  rw [show algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x = 0 from h0]
  exact P.asIdeal.zero_mem

theorem comap_curveLocalRing_le (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal ≤
      RingHom.ker (eval q) := by
  intro x hx
  by_contra h
  exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
    (isUnit_algebraMap_curveLocalRing I q x fun h' ↦ h (RingHom.mem_ker.2 h')))

theorem LocalDimComponentBound.proof : LocalDimComponentBound.Statement := by
  intro n I q hq
  rcases subsingleton_or_nontrivial (curveLocalRing I q) with hO | hO
  · refine ⟨RingHom.ker (eval q), inferInstance, fun x hx ↦ RingHom.mem_ker.2 (hq x hx),
      fun x hx ↦ RingHom.mem_ker.1 hx, ?_⟩
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set f := algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)
  set p := LTSeries.longestOf (PrimeSpectrum (curveLocalRing I q))
  set W := (PrimeSpectrum.comap f p.head).asIdeal with hW
  have hWle : ∀ i, W ≤ (PrimeSpectrum.comap f (p i)).asIdeal := fun i ↦
    Ideal.comap_mono (p.monotone (Fin.zero_le i))
  let p' : LTSeries (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) W) :=
    { length := p.length
      toFun := fun i ↦ ⟨PrimeSpectrum.comap f (p i), hWle i⟩
      step := fun i ↦ comap_curveLocalRing_strictMono I q (p.step i) }
  refine ⟨W, (PrimeSpectrum.comap f p.head).isPrime, le_comap_curveLocalRing I q _,
    fun x hx ↦ RingHom.mem_ker.1 (comap_curveLocalRing_le I q _ hx), ?_⟩
  rw [ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder, ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim p'

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogNormGradDensNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ContDiff

noncomputable section

namespace LogNormGradDensNonneg

theorem log_fs_eq_std (n : ℕ) :
    (fun z : Fin n → ℂ => Real.log ((ReciprocityTheory.ChartRestriction.G.Geo.fsMetric (Fin n)).ρ z)) =
      fun z => Real.log ((HermNorm.std n).dualNorm z) := by
  funext z
  simp [ReciprocityTheory.ChartRestriction.G.Geo.fsMetric, HermNorm.dualNorm, HermNorm.std, EuclideanSpace.norm_eq]

theorem levi_log_dualNorm_nonneg {n : ℕ} (h : HermNorm n) {x : Fin n → ℂ} (hx : x ≠ 0)
    (w : Fin n → ℂ) : 0 ≤ levi (fun x => Real.log (h.dualNorm x)) x w := by
  set T : (Fin n → ℂ) → Fin n → ℂ := fun x => (h.matᵀ)⁻¹ *ᵥ x with hT
  set F : (Fin n → ℂ) → ℝ := fun z => Real.log ((ReciprocityTheory.ChartRestriction.G.Geo.fsMetric (Fin n)).ρ z) with hF
  have hTx : T x ≠ 0 := by
    intro h0
    have : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact h.isUnit_det),
        Matrix.one_mulVec]
    exact hx (by rw [← this]; simp only [hT] at h0; rw [h0, Matrix.mulVec_zero])
  have hcomp : (fun x => Real.log (h.dualNorm x)) = F ∘ T := by
    funext z
    simp [hF, hT, ReciprocityTheory.ChartRestriction.G.Geo.fsMetric, HermNorm.dualNorm, EuclideanSpace.norm_eq]
  have hTa : AnalyticAt ℂ T x := by
    have := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h.matᵀ)⁻¹)).analyticAt x
    simp only [LinearMap.coe_toContinuousLinearMap'] at this
    convert this using 1
    funext z
    rw [Matrix.mulVecLin_apply]
  have hFc : ContDiffAt ℝ 2 F (T x) := by
    rw [hF, log_fs_eq_std]
    exact (((contDiffOn_log_dualNorm (HermNorm.std n)).contDiffAt
      (isOpen_compl_singleton.mem_nhds hTx)).of_le (WithTop.coe_le_coe.mpr le_top))
  rw [hcomp, levi_comp w hTa hFc]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hTx _

end LogNormGradDensNonneg

theorem LogNormGradDensNonneg.proof : LogNormGradDensNonneg.Statement := by
  intro n e h s y v hs hsy
  set t : (Fin n → ℂ) → ℝ := fun x => Real.log (h.dualNorm x) with ht
  set V : Set (Fin (e + 1) → ℂ) := {z | AnalyticAt ℂ s z ∧ s z ≠ 0} with hVdef
  have hV : IsOpen V := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    filter_upwards [hz.1.eventually_analyticAt,
      hz.1.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hz.2)] with u hu hu'
    exact ⟨hu, hu'⟩
  have htc : ∀ x : Fin n → ℂ, x ≠ 0 → ContDiffAt ℝ 2 t x := fun x hx =>
    ((contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds hx)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hC : ∀ z ∈ V, ContDiffAt ℝ 2 (t ∘ s) z := fun z hz =>
    (htc (s z) hz.2).comp z (hz.1.restrictScalars (𝕜 := ℝ)).contDiffAt
  refine gradDensNonneg_thm e (fun _ => t ∘ s) v V hV
    (fun _ => fun z hz => (hC z hz).contDiffWithinAt) ?_ y ⟨hs, hsy⟩
  intro _ z hz ξ
  rw [levi_comp ξ hz.1 (htc (s z) hz.2)]
  exact LogNormGradDensNonneg.levi_log_dualNorm_nonneg h hz.2 _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.POneComponentGeneralPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem OneComponentGeneralPoint.proof (hV : VanishNearPoint.Statement) :
    OneComponentGeneralPoint.Statement := by
  classical
  intro n I W hW
  have hWp : W.IsPrime := hW.1.1
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I

  have hsep : ∀ W' ∈ I.minimalPrimes, W' ≠ W → ∃ g ∈ W', g ∉ W := by
    intro W' hW' hne
    by_contra h
    push Not at h
    exact hne (le_antisymm h (hW.2 hW'.1 h))
  choose! g hgW' hgW using hsep
  set S := hfin.toFinset.erase W with hS
  set f : MvPolynomial (Fin n) ℂ := ∏ W' ∈ S, g W' with hfdef
  have hf : f ∉ W := by
    intro hmem
    obtain ⟨W', hW'S, hgm⟩ := (Ideal.IsPrime.prod_mem_iff (p := W)).1 hmem
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hW'S
    exact hgW W' hW'S.2 hW'S.1 hgm
  have hUo : IsOpen {x : Fin n → ℂ | eval x f ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval (p := f)) continuous_const
  refine ⟨{x | eval x f ≠ 0}, hUo, ?_, ?_⟩
  ·
    intro x hx
    rw [mem_closure_iff_nhds]
    intro t ht
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hf
    refine hV n W f x hWp hx ?_
    filter_upwards [ht] with y hyt hyW
    by_contra hne
    have hy : y ∈ t ∩ (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ {x | eval x f ≠ 0}) :=
      ⟨hyt, hyW, hne⟩
    rw [hempty] at hy
    exact hy
  ·
    rintro x ⟨-, hxf⟩
    refine ⟨{x | eval x f ≠ 0}, hUo.mem_nhds hxf, ?_⟩
    rintro y ⟨hyI, hyf⟩
    have : (RingHom.ker (eval y : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
    have hker : I ≤ RingHom.ker (eval y : MvPolynomial (Fin n) ℂ →+* ℂ) :=
      fun q hq => RingHom.mem_ker.2 (hyI q hq)
    obtain ⟨W', hW', hle⟩ := Ideal.exists_minimalPrimes_le hker
    by_cases hne : W' = W
    · rw [hne] at hle
      intro q hq
      exact RingHom.mem_ker.1 (hle hq)
    · exfalso
      apply hyf
      have hmem : W' ∈ S := by
        rw [hS, Finset.mem_erase, Set.Finite.mem_toFinset]
        exact ⟨hne, hW'⟩
      show eval y (∏ W' ∈ S, g W') = 0
      rw [map_prod]
      exact Finset.prod_eq_zero hmem (RingHom.mem_ker.1 (hle (hgW' W' hW' hne)))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMGeneralPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CMGeneralPoint.Statement : Prop :=
  ∀ (n : ℕ) (I W : Ideal (MvPolynomial (Fin n) ℂ)), W ∈ I.minimalPrimes →
    ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
      (∀ W' ∈ I.minimalPrimes, q ∈ zeroSet W' → W' = W) ∧ IsCohenMacaulayAt I q

end GroundTheory.Heights₂.Heights
end

