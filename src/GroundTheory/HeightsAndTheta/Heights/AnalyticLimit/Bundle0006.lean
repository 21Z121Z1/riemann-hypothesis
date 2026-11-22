import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Convergence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

theorem rpow_third_le {t : ℝ} (ht : 0 < t) (hℓ : Real.exp 1 ≤ ell t) (n : ℕ) :
    t ^ (1 / 3 : ℝ) ≤ 2 * (Real.log (ell t) ^ n / ell t) := by
  have hℓ1 : 1 ≤ ell t := (Real.one_le_exp zero_le_one).trans hℓ
  have hℓ0 : 0 < ell t := by linarith
  have hlog : Real.log t = -ell t := by
    rw [ell, Real.log_inv, neg_neg]
  have hL : 1 ≤ Real.log (ell t) := by
    have := Real.log_le_log (Real.exp_pos 1) hℓ
    rwa [Real.log_exp] at this
  have hLn : 1 ≤ Real.log (ell t) ^ n := one_le_pow₀ hL
  have hq := Real.quadratic_le_exp_of_nonneg (x := ell t / 3) (by positivity)
  have hE0 : 0 < Real.exp (ell t / 3) := Real.exp_pos _
  have hE : ell t ≤ 2 * Real.exp (ell t / 3) := by nlinarith [sq_nonneg (ell t - 3 / 2)]
  have h1 : t ^ (1 / 3 : ℝ) = (Real.exp (ell t / 3))⁻¹ := by
    rw [Real.rpow_def_of_pos ht, hlog, ← Real.exp_neg]
    congr 1
    ring
  rw [h1, inv_eq_one_div, div_le_iff₀ hE0]
  have h2 : 1 ≤ 2 * Real.exp (ell t / 3) / ell t := by
    rw [le_div_iff₀ hℓ0]
    linarith
  calc (1 : ℝ) ≤ 2 * Real.exp (ell t / 3) / ell t := h2
    _ ≤ 2 * Real.exp (ell t / 3) / ell t * Real.log (ell t) ^ n :=
        le_mul_of_one_le_right (by positivity) hLn
    _ = 2 * (Real.log (ell t) ^ n / ell t) * Real.exp (ell t / 3) := by ring

theorem Convergence.proof (hW : WeightCocycle.Statement) : Convergence.Statement := by
  intro X _ _ _ _ _ D A F a a₀ δ Λ M CE L₀ ha hδ hL hM hCE hTV
  obtain ⟨C', ℓ₁, hT⟩ := TelescopingFamily.proof D A F Λ
  refine ⟨(D + 1) * (C' ^ 2 * M + 2 * |C'| * M + |C'| * CE) / δ, max (max L₀ ℓ₁) (Real.exp 1),
    fun x hx t t' ht' htt hl => ?_⟩
  have hl0 : L₀ ≤ ell t := (le_max_left _ _).trans ((le_max_left _ _).trans hl)
  have hl1 : ℓ₁ ≤ ell t := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
  have hle : Real.exp 1 ≤ ell t := (le_max_right _ _).trans hl
  have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hℓ0 : 0 < ell t := by linarith
  have ht : 0 < t := ht'.trans_le htt
  have hA : F.Admissible t := ⟨ht, fun i => (hL i).trans hl0⟩
  have hA' : F.Admissible t' := ⟨ht', fun i => ((hL i).trans hl0).trans (ell_anti ht' htt)⟩
  have hc : ∑ i, |x (some i)| ≤ Λ := by
    refine le_trans ?_ hx
    rw [Fintype.sum_option]
    linarith [abs_nonneg (x none)]
  have hu0 : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
  have hL1 : 1 ≤ Real.log (ell t) := by
    have := Real.log_le_log (Real.exp_pos 1) hle
    rwa [Real.log_exp] at this
  obtain ⟨aN, haN⟩ : ∃ aN : ℝ,
      aN = |C'| * t ^ (1 / 3 : ℝ) + C' ^ 2 * (Real.log (ell t) / ell t) := ⟨_, rfl⟩
  have haN0 : 0 ≤ aN := by
    rw [haN]
    have : 0 ≤ Real.log (ell t) / ell t := div_nonneg (by linarith) hℓ0.le
    positivity
  obtain ⟨f, hf⟩ : ∃ f : X → ℝ, f = fun p => F.coefWeight x t p - F.coefWeight x t' p := ⟨_, rfl⟩
  have hfeq : ∀ p, f p = ∑ i, x (some i) * ((F.sys i).ph t p - (F.sys i).ph t' p) := by
    intro p
    simp only [hf, Family.coefWeight, mul_sub, Finset.sum_sub_distrib]
  have hnear : ∀ p ∈ F.Yo, F.r p ≤ ell t → |f p| ≤ aN := by
    intro p hp hr
    rw [hfeq]
    refine ((hT (fun i => x (some i)) hc t t' ht' htt hl1 p hp).1 hr).trans ?_
    have hCu : C' * t ^ (1 / 3 : ℝ) ≤ |C'| * t ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self C') hu0
    have e : C' * (t ^ (1 / 3 : ℝ) + errE C' t) =
        C' * t ^ (1 / 3 : ℝ) + C' ^ 2 * (Real.log (ell t) / ell t) := by
      rw [errE]
      ring
    rw [e, haN]
    linarith
  have hfar : ∀ p ∈ F.Yo, ell t < F.r p → |f p| ≤ |C'| * Real.log (F.r p) := by
    intro p hp hr
    rw [hfeq]
    refine ((hT (fun i => x (some i)) hc t t' ht' htt hl1 p hp).2 hr).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self C') (Real.log_nonneg (by linarith))
  have hfc : Continuous f := by
    rw [hf]
    refine Continuous.sub ?_ ?_ <;>
      refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    · exact ReciprocityTheory.AnForm.M.PLAux.smooth_continuous ((F.sys i).smooth t ht (hA.2 i))
    · exact ReciprocityTheory.AnForm.M.PLAux.smooth_continuous ((F.sys i).smooth t' ht' (hA'.2 i))
  have hterm : ∀ k ∈ Finset.range (D + 1), |mInt A (F.mixedProduct a x t t' k) f| ≤
      aN * M + |C'| * (CE * Real.log (ell t) ^ (D + 1) / ell t) := by
    intro k hk
    have hkD : k ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hΦ := F.mixedProduct_isPotential ha x hA hA' k
    exact ConvergenceSigned.proof A _ hΦ F.Yo F.r M CE (hTV x hx t t' ht' htt hl0 k hkD) f
      hfc.measurable (ReciprocityTheory.AnForm.M.mIntegrableCont A _ hΦ f hfc) aN |C'| (ell t) haN0
      (abs_nonneg _) hle hnear hfar
  have hsum := hW D A F a ha x t t' hA hA'
  rw [← hf] at hsum
  have hdiff : F.arithSelfInt a a₀ δ x t - F.arithSelfInt a a₀ δ x t' =
      (∑ k ∈ Finset.range (D + 1), mInt A (F.mixedProduct a x t t' k) f) / δ := by
    rw [← hsum]
    unfold Family.arithSelfInt
    ring
  rw [hdiff, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
  have hP : 0 ≤ Real.log (ell t) / ell t := div_nonneg (by linarith) hℓ0.le
  have hQ : 0 ≤ Real.log (ell t) ^ (D + 1) / ell t := by positivity
  have hu2 := rpow_third_le ht hle (D + 1)
  have hC0 : 0 ≤ |C'| := abs_nonneg C'
  have key : aN * M + |C'| * (CE * Real.log (ell t) ^ (D + 1) / ell t) ≤
      (C' ^ 2 * M + 2 * |C'| * M + |C'| * CE) *
        (Real.log (ell t) / ell t + Real.log (ell t) ^ (D + 1) / ell t) := by
    rw [haN, mul_div_assoc CE]
    nlinarith [mul_nonneg (mul_nonneg hC0 hM) (sub_nonneg.2 hu2), mul_nonneg (sq_nonneg C') hM,
      mul_nonneg (mul_nonneg (sq_nonneg C') hM) hQ, mul_nonneg (mul_nonneg hC0 hM) hP,
      mul_nonneg (mul_nonneg hC0 hCE) hP, mul_nonneg (mul_nonneg hC0 hM) hQ]
  have e2 : convRate D ((D + 1) * (C' ^ 2 * M + 2 * |C'| * M + |C'| * CE) / δ) t * δ =
      (D + 1) * ((C' ^ 2 * M + 2 * |C'| * M + |C'| * CE) *
        (Real.log (ell t) / ell t + Real.log (ell t) ^ (D + 1) / ell t)) := by
    unfold convRate
    field_simp
  rw [e2]
  calc |∑ k ∈ Finset.range (D + 1), mInt A (F.mixedProduct a x t t' k) f|
      ≤ ∑ k ∈ Finset.range (D + 1), |mInt A (F.mixedProduct a x t t' k) f| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (D + 1),
          (aN * M + |C'| * (CE * Real.log (ell t) ^ (D + 1) / ell t)) :=
        Finset.sum_le_sum hterm
    _ = (D + 1) * (aN * M + |C'| * (CE * Real.log (ell t) ^ (D + 1) / ell t)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)

def evalLin (σ : Type*) (N : ℕ) :
    MvPolynomial.restrictTotalDegree σ ℝ N →ₗ[ℝ] ((σ → ℝ) → ℝ) where
  toFun p x := MvPolynomial.eval x p.1
  map_add' p q := by
    funext x
    simp
  map_smul' c p := by
    funext x
    simp [MvPolynomial.smul_eval]

theorem evalLin_injective (σ : Type*) (N : ℕ) : Function.Injective (evalLin σ N) :=
  fun _ _ h => Subtype.ext (MvPolynomial.funext fun x => congrFun h x)

theorem CoefficientLimit.proof (hW : WeightCocycle.Statement)
    (hPol : PolynomialInWeights.Statement) : CoefficientLimit.Statement := by
  classical
  intro X _ _ _ _ _ D A F a a₀ δ L₀ ha ha₀ hδ hL hTV
  have hlim : ∀ x : Option (Fin F.m) → ℝ,
      ∃ y, Tendsto (fun t => F.arithSelfInt a a₀ δ x t) (𝓝[>] 0) (𝓝 y) := by
    intro x
    obtain ⟨M, CE, hM, hCE, hT⟩ := hTV (∑ o, |x o|)
    obtain ⟨C, L₁, hC⟩ :=
      Convergence.proof hW D A F a a₀ δ (∑ o, |x o|) M CE L₀ ha hδ hL hM hCE hT
    obtain ⟨y, hy, -⟩ := ConvergenceRate.proof D (fun t => F.arithSelfInt a a₀ δ x t) C L₁
      fun t t' h1 h2 h3 => hC x le_rfl t t' h1 h2 h3
    exact ⟨y, hy⟩
  choose g hg using hlim
  have hadm : ∀ᶠ t in 𝓝[>] (0 : ℝ), F.Admissible t := by
    filter_upwards [self_mem_nhdsWithin, tendsto_ell.eventually_ge_atTop L₀] with t ht hl
    exact ⟨ht, fun i => (hL i).trans hl⟩
  let V := MvPolynomial.restrictTotalDegree (Option (Fin F.m)) ℝ (D + 1)
  let ev := evalLin (Option (Fin F.m)) (D + 1)
  let W := LinearMap.range ev
  have hWc : IsClosed (W : Set ((Option (Fin F.m) → ℝ) → ℝ)) :=
    Submodule.closed_of_finiteDimensional W
  have ha₀V : a₀ ∈ V := (MvPolynomial.mem_restrictTotalDegree (m := D + 1) (p := a₀)).2 ha₀
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), (fun x => F.arithSelfInt a a₀ δ x t) ∈ W := by
    filter_upwards [hadm] with t ht
    obtain ⟨q, hq, hqe⟩ := hPol D A F a ha t ht
    have hqV : q ∈ V := (MvPolynomial.mem_restrictTotalDegree (m := D + 1) (p := q)).2 hq
    refine ⟨⟨δ⁻¹ • (a₀ + q), V.smul_mem _ (V.add_mem ha₀V hqV)⟩, ?_⟩
    funext x
    show MvPolynomial.eval x (δ⁻¹ • (a₀ + q)) = F.arithSelfInt a a₀ δ x t
    rw [MvPolynomial.smul_eval, MvPolynomial.eval_add, hqe, Family.arithSelfInt, div_eq_inv_mul]
  have htend : Tendsto (fun t => fun x => F.arithSelfInt a a₀ δ x t) (𝓝[>] 0) (𝓝 g) :=
    tendsto_pi_nhds.2 hg
  have hgW : g ∈ W := hWc.mem_of_tendsto htend hmem
  obtain ⟨P', hP'⟩ := LinearMap.mem_range.1 hgW
  have hevalP : ∀ x, MvPolynomial.eval x P'.1 = g x := fun x => congrFun hP' x
  refine ⟨P'.1, (MvPolynomial.mem_restrictTotalDegree (m := D + 1) (p := P'.1)).1 P'.2, fun x => ?_, fun p hp α => ?_⟩
  · rw [hevalP]
    exact hg x
  · let e := LinearEquiv.ofInjective ev (evalLin_injective _ _)
    let ψ : W →ₗ[ℝ] ℝ := (MvPolynomial.lcoeff ℝ α) ∘ₗ V.subtype ∘ₗ e.symm.toLinearMap
    have hψ : Continuous ψ := LinearMap.continuous_of_finiteDimensional ψ
    have hψe : ∀ v : V, ψ (e v) = (v : MvPolynomial (Option (Fin F.m)) ℝ).coeff α := by
      intro v
      simp [ψ]
    let G : ℝ → W := fun t =>
      if h : (fun x => F.arithSelfInt a a₀ δ x t) ∈ W then ⟨_, h⟩ else 0
    have hG : Tendsto G (𝓝[>] 0) (𝓝 (e P')) := by
      rw [tendsto_subtype_rng]
      have he : ((e P' : W) : (Option (Fin F.m) → ℝ) → ℝ) = g := by
        rw [LinearEquiv.ofInjective_apply]
        exact hP'
      rw [he]
      refine htend.congr' ?_
      filter_upwards [hmem] with t ht
      show _ = ((G t : W) : (Option (Fin F.m) → ℝ) → ℝ)
      simp only [G, dif_pos ht]
    have hlimψ := (hψ.tendsto _).comp hG
    rw [hψe] at hlimψ
    refine hlimψ.congr' ?_
    filter_upwards [hp, hmem] with t hpt ht
    have hpV : p t ∈ V := (MvPolynomial.mem_restrictTotalDegree (m := D + 1) (p := p t)).2 hpt.1
    have hGt : G t = e ⟨p t, hpV⟩ := by
      apply Subtype.ext
      rw [LinearEquiv.ofInjective_apply]
      simp only [G, dif_pos ht]
      funext x
      exact (hpt.2 x).symm
    simp only [Function.comp_apply, hGt, hψe]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts errorWithLinear)

noncomputable section

theorem ArgumentConvergenceC2.proof : ArgumentConvergenceC2.Statement := by
  intro X _ _ D A R ρ Cη η hη C hC j k L hL hLsub
  have hV'open : IsOpen (R.V' j) := (R.ψ j).isOpen_inter_preimage (R.isOpen_alt j)
  set O : Set (Fin D → ℂ) := (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.Yo ∩ R.V' j) with hO_def
  have hO : IsOpen O := (A.chart k).isOpen_inter_preimage_symm (R.isOpen_Yo.inter hV'open)
  have hOsrc : ∀ y ∈ O, (A.chart k).symm y ∈ (R.ψ j).source := fun y hy => hy.2.2.1

  obtain ⟨T, hT_def⟩ : ∃ T : (Fin D → ℂ) → (Fin D → ℂ), T = fun y => R.ψ j ((A.chart k).symm y) :=
    ⟨_, rfl⟩
  have hTy : ∀ y, T y = R.ψ j ((A.chart k).symm y) := fun y => by rw [hT_def]
  have hT : ∀ y ∈ O, ContDiffAt ℝ ∞ T y := by
    intro y hy
    have h := ((R.compat j k).1 y ⟨hy.1, hOsrc y hy⟩).restrictScalars (𝕜 := ℝ)
    rw [hT_def]
    exact h.contDiffAt
  have hTO : ContDiffOn ℝ ∞ T O := fun y hy => (hT y hy).contDiffWithinAt
  have hTc : ContinuousOn T O := hTO.continuousOn

  set P : Set (Fin D → ℂ) := ((R.ψ j).target ∩ (R.ψ j).symm ⁻¹' R.Yo) ∩ R.W j with hP_def
  have hP : IsOpen P := ((R.ψ j).isOpen_inter_preimage_symm R.isOpen_Yo).inter (R.isOpen_kappaOpenNeighbourhood j)
  have hu : ContDiffOn ℝ ∞ (R.u R.φ j) P := by
    intro z hz
    refine ContDiffAt.contDiffWithinAt ?_
    have hzs : (R.ψ j).symm z ∈ (R.ψ j).source := (R.ψ j).map_target hz.1.1
    have h1 := GroundTheory.Heights₂.Heights.Regular.contDiffAt_comp_symm_of_smoothOn (R.compat j)
      R.isOpen_Yo R.φ_smooth hz.1.2 hzs
    rw [(R.ψ j).right_inv hz.1.1] at h1
    exact ((R.q_smooth j).contDiffAt ((R.isOpen_kappaOpenNeighbourhood j).mem_nhds hz.2)).add h1
  have hTP : MapsTo T O P := by
    intro y hy
    rw [hTy]
    have hs := hOsrc y hy
    refine ⟨⟨(R.ψ j).map_source hs, ?_⟩, ?_⟩
    · rw [mem_preimage, (R.ψ j).left_inv hs]
      exact hy.2.1
    · exact R.closure_W'_subset j (subset_closure hy.2.2.2)
  have hfeq : ∀ y ∈ O, R.φ ((A.chart k).symm y) = R.u R.φ j (T y) - R.q j (T y) := by
    intro y hy
    simp only [RegCharts.u, hTy]
    rw [(R.ψ j).left_inv (hOsrc y hy)]
    ring
  have hF : ∀ t y, R.regArg R.φ ρ η C t j ((A.chart k).symm y) =
      molli ρ t (R.u R.φ j) (T y) - R.q j (T y) + 4 * errorWithLinear C t * η j ((A.chart k).symm y) := by
    intro t y
    rw [hTy]
    rfl
  have hf : ContDiffOn ℝ ∞ (fun y => R.φ ((A.chart k).symm y)) O :=
    (R.φ_smooth k).mono fun y hy => ⟨hy.1, hy.2.1⟩
  have hH : ContDiffOn ℝ ∞ (fun y => η j ((A.chart k).symm y)) O :=
    ((hη j).1 k).mono fun y hy => ⟨hy.1, hy.2.2⟩
  have hqT : ContDiffOn ℝ ∞ (fun y => R.q j (T y)) O :=
    (R.q_smooth j).comp hTO fun y hy => (hTP hy).2

  obtain ⟨δ, hδ, hδO⟩ := hL.exists_cthickening_subset_open hO hLsub
  have hKc : IsCompact (cthickening (δ / 2) L) := hL.cthickening
  have hKcO : cthickening (δ / 2) L ⊆ O := (cthickening_mono (by linarith) L).trans hδO
  have hLU : L ⊆ thickening (δ / 2) L := self_subset_thickening (by linarith) L
  have hUK : thickening (δ / 2) L ⊆ cthickening (δ / 2) L := thickening_subset_cthickening _ _
  have hK' : IsCompact (T '' cthickening (δ / 2) L) := hKc.image_of_continuousOn (hTc.mono hKcO)
  have hK'P : T '' cthickening (δ / 2) L ⊆ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact hTP (hKcO hy)
  have hle : ∀ m : ℕ, (m : WithTop ℕ∞) ≤ ∞ := fun m => by exact_mod_cast le_top
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := hle 3
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := hle 2
  obtain ⟨C₀, ε₀, hε₀, hmol⟩ := ReciprocityTheory.AnForm.A.mollification_second_order D ρ P (T '' cthickening (δ / 2) L)
    (R.u R.φ j) hP (hu.of_le h3) hK' hK'P
  obtain ⟨BT, hBT⟩ := ArgumentConvergenceLemmas.exists_bound_iteratedFDeriv hO (hTO.of_le h2) hL hLsub
  obtain ⟨BH, hBH⟩ := ArgumentConvergenceLemmas.exists_bound_iteratedFDeriv hO (hH.of_le h2) hL hLsub
  set d : ℝ := max 1 BT with hd_def
  have hd1 : 1 ≤ d := le_max_left _ _
  set C₁ : ℝ := max C₀ 0 with hC₁_def
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  set B₁ : ℝ := max BH 0 with hB₁_def
  have hB₁ : 0 ≤ B₁ := le_max_right _ _
  set M : ℝ := 2 * C₁ * d ^ 2 + 4 * B₁ with hM_def

  have key : ∀ t ∈ Ioo 0 (min ε₀ (Real.exp (-1))),
      ContDiffOn ℝ 2 (fun y => R.regArg R.φ ρ η C t j ((A.chart k).symm y)) (thickening (δ / 2) L) ∧
      ∀ y ∈ L, ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (fun y =>
        R.regArg R.φ ρ η C t j ((A.chart k).symm y) - R.φ ((A.chart k).symm y)) y‖ ≤
          M * (t + errorWithLinear C t) := by
    rintro t ⟨ht0, ht⟩
    have htε : t < ε₀ := ht.trans_le (min_le_left _ _)
    have hte : t < Real.exp (-1) := ht.trans_le (min_le_right _ _)
    have he1 : 0 < errorWithLinear C t := ArgumentConvergenceLemmas.logErrorBound_pos hC ht0 hte
    have hShr : IsOpen (shrink P t) := ReciprocityTheory.AnForm.A.isOpen_shrink hP ht0
    have hShrP : shrink P t ⊆ P := fun z hz => hz (mem_closedBall_self ht0.le)
    have hm : ContDiffOn ℝ ∞ (molli ρ t (R.u R.φ j)) (shrink P t) := fun z hz =>
      (ArgumentConvergenceLemmas.molli_contDiffAt ρ hP hu.continuousOn ht0 hz).contDiffWithinAt
    have hK'S : ∀ y ∈ cthickening (δ / 2) L, T y ∈ shrink P t := fun y hy =>
      (hmol t ht0 htε (T y) ⟨y, hy, rfl⟩).1
    set s : Set (Fin D → ℂ) := O ∩ T ⁻¹' shrink P t with hs_def
    have hs : IsOpen s := hTc.isOpen_inter_preimage hO hShr
    have hKs : cthickening (δ / 2) L ⊆ s := fun y hy => ⟨hKcO hy, hK'S y hy⟩
    have hTs : ContDiffOn ℝ ∞ T s := hTO.mono inter_subset_left
    have hmT : ContDiffOn ℝ ∞ (fun y => molli ρ t (R.u R.φ j) (T y)) s :=
      hm.comp hTs fun y hy => hy.2
    have hFs : ContDiffOn ℝ ∞ (fun y => R.regArg R.φ ρ η C t j ((A.chart k).symm y)) s := by
      have : ContDiffOn ℝ ∞ (fun y => molli ρ t (R.u R.φ j) (T y) - R.q j (T y) +
          4 * errorWithLinear C t * η j ((A.chart k).symm y)) s :=
        (hmT.sub (hqT.mono inter_subset_left)).add
          (contDiffOn_const.mul (hH.mono inter_subset_left))
      exact this.congr fun y _ => hF t y
    refine ⟨(hFs.of_le h2).mono (hUK.trans hKs), ?_⟩
    intro y hyL n hn
    have hyO : y ∈ O := hLsub hyL
    have hyK : y ∈ cthickening (δ / 2) L := self_subset_cthickening L hyL
    have hys : y ∈ s := hKs hyK
    set G : (Fin D → ℂ) → ℝ := fun z => molli ρ t (R.u R.φ j) z - R.u R.φ j z with hG_def
    have hGs : ContDiffOn ℝ ∞ G (shrink P t) := hm.sub (hu.mono hShrP)
    have heq : (fun y => R.regArg R.φ ρ η C t j ((A.chart k).symm y) - R.φ ((A.chart k).symm y))
        =ᶠ[𝓝 y] (G ∘ T) + (4 * errorWithLinear C t) • (fun y => η j ((A.chart k).symm y)) := by
      filter_upwards [hO.mem_nhds hyO] with y' hy'
      simp only [Pi.add_apply, Function.comp, Pi.smul_apply, smul_eq_mul, hG_def]
      rw [hF, hfeq y' hy']
      ring
    have hn' : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hGT : ContDiffAt ℝ n (G ∘ T) y :=
      ((hGs.comp hTs fun y hy => hy.2).contDiffAt (hs.mem_nhds hys)).of_le hn'
    have hHy : ContDiffAt ℝ n (fun y => η j ((A.chart k).symm y)) y :=
      (hH.contDiffAt (hO.mem_nhds hyO)).of_le hn'
    have hcH : ContDiffAt ℝ n ((4 * errorWithLinear C t) • fun y => η j ((A.chart k).symm y)) y :=
      hHy.const_smul (4 * errorWithLinear C t)
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_add_apply hGT hcH,
      iteratedFDeriv_const_smul_apply hHy]

    have hmb := hmol t ht0 htε (T y) ⟨y, hyK, rfl⟩
    have hGC : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i G (T y)‖ ≤ C₁ * t := by
      have hCt : C₀ * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (le_max_left _ _) ht0.le
      obtain ⟨e0, e1, e2⟩ := ArgumentConvergenceLemmas.norm_iteratedFDeriv_sub_eq hShr (hm.of_le h2)
        ((hu.mono hShrP).of_le h2) (hK'S y hyK)
      intro i hi
      interval_cases i
      · rw [e0, Real.norm_eq_abs]
        exact hmb.2.1.trans hCt
      · rw [e1]
        exact hmb.2.2.1.trans hCt
      · rw [e2]
        exact hmb.2.2.2.trans hCt
    have hTd : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i T y‖ ≤ d ^ i := by
      intro i hi1 hi2
      interval_cases i
      · rw [pow_one]
        exact (hBT 1 (by norm_num) y hyL).trans (le_max_right _ _)
      · exact (hBT 2 le_rfl y hyL).trans ((le_max_right _ _).trans (le_self_pow₀ hd1 (by norm_num)))
    have hGb : ‖iteratedFDeriv ℝ n (G ∘ T) y‖ ≤ n.factorial * (C₁ * t) * d ^ n :=
      ArgumentConvergenceLemmas.norm_iteratedFDeriv_comp_le_of_isOpen hs hShr (hGs.of_le h2) (hTs.of_le h2)
        (fun y hy => hy.2) hys hn hGC hTd
    have hfac : (n.factorial : ℝ) ≤ 2 := by
      interval_cases n <;> norm_num [Nat.factorial]
    have hpow : d ^ n ≤ d ^ 2 := pow_le_pow_right₀ hd1 hn
    have hGb' : ‖iteratedFDeriv ℝ n (G ∘ T) y‖ ≤ 2 * C₁ * d ^ 2 * t := by
      have hCt0 : 0 ≤ C₁ * t := mul_nonneg hC₁ ht0.le
      calc ‖iteratedFDeriv ℝ n (G ∘ T) y‖ ≤ n.factorial * (C₁ * t) * d ^ n := hGb
        _ ≤ 2 * (C₁ * t) * d ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hfac hCt0) hpow (by positivity) (by positivity)
        _ = 2 * C₁ * d ^ 2 * t := by ring

    have hHb : ‖(4 * errorWithLinear C t) • iteratedFDeriv ℝ n (fun y => η j ((A.chart k).symm y)) y‖ ≤
        4 * B₁ * errorWithLinear C t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have := (hBH n hn y hyL).trans (le_max_left BH 0)
      nlinarith
    have hsum := norm_add_le (iteratedFDeriv ℝ n (G ∘ T) y)
      ((4 * errorWithLinear C t) • iteratedFDeriv ℝ n (fun y => η j ((A.chart k).symm y)) y)
    have hx1 : 0 ≤ 2 * C₁ * d ^ 2 * errorWithLinear C t := by positivity
    have hx2 : 0 ≤ 4 * B₁ * t := by positivity
    have hexp : M * (t + errorWithLinear C t) = 2 * C₁ * d ^ 2 * t + 2 * C₁ * d ^ 2 * errorWithLinear C t +
        4 * B₁ * t + 4 * B₁ * errorWithLinear C t := by
      rw [hM_def]; ring
    linarith

  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (min ε₀ (Real.exp (-1))) :=
    Ioo_mem_nhdsGT (lt_min hε₀ (Real.exp_pos _))
  have hβ : Tendsto (fun t => M * (t + errorWithLinear C t)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((tendsto_id.mono_left nhdsWithin_le_nhds).add (ArgumentConvergenceLemmas.tendsto_logErrorBound_nhdsWithin C)).const_mul M
    simpa using h
  have hfU : ContDiffOn ℝ 2 (fun y => R.φ ((A.chart k).symm y)) (thickening (δ / 2) L) :=
    (hf.of_le h2).mono (hUK.trans hKcO)
  have three : ∀ t ∈ Ioo 0 (min ε₀ (Real.exp (-1))), ∀ y ∈ L,
      ‖R.regArg R.φ ρ η C t j ((A.chart k).symm y) - R.φ ((A.chart k).symm y)‖ ≤ M * (t + errorWithLinear C t) ∧
      ‖fderiv ℝ (fun y' => R.regArg R.φ ρ η C t j ((A.chart k).symm y')) y -
          fderiv ℝ (fun y' => R.φ ((A.chart k).symm y')) y‖ ≤ M * (t + errorWithLinear C t) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y' => R.regArg R.φ ρ η C t j ((A.chart k).symm y'))) y -
          fderiv ℝ (fderiv ℝ (fun y' => R.φ ((A.chart k).symm y'))) y‖ ≤ M * (t + errorWithLinear C t) := by
    intro t ht y hy
    obtain ⟨e0, e1, e2⟩ := ArgumentConvergenceLemmas.norm_iteratedFDeriv_sub_eq isOpen_thickening (key t ht).1 hfU
      (hLU hy)
    refine ⟨?_, ?_, ?_⟩
    · rw [← e0]; exact (key t ht).2 y hy 0 (by norm_num)
    · rw [← e1]; exact (key t ht).2 y hy 1 (by norm_num)
    · rw [← e2]; exact (key t ht).2 y hy 2 le_rfl
  refine ⟨thickening (δ / 2) L, isOpen_thickening, hLU, hfU, ?_, ⟨?_, ?_, ?_⟩, M, ?_⟩
  · filter_upwards [hev] with t ht using (key t ht).1
  · refine ArgumentConvergenceLemmas.tendstoUniformlyOn_of_norm_le hβ ?_
    filter_upwards [hev] with t ht y hy using (three t ht y hy).1
  · refine ArgumentConvergenceLemmas.tendstoUniformlyOn_of_norm_le (α := (Fin D → ℂ) →L[ℝ] ℝ) hβ ?_
    filter_upwards [hev] with t ht y hy using (three t ht y hy).2.1
  · refine ArgumentConvergenceLemmas.tendstoUniformlyOn_of_norm_le
      (α := (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) hβ ?_
    filter_upwards [hev] with t ht y hy using (three t ht y hy).2.2
  · filter_upwards [hev] with t ht y hy using (three t ht y hy).2.1

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt MIntegrable locDens)

def ListMono.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Yo : Set X) (r : X → ℝ) (Om : KaehlerForm A) (C₁ : ℝ) (th : Fin D → LocPot X)
    (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsBoundedPotForm A Yo r Om C₁ (th i) (u i)) →
    (∀ i, FormNonneg A Yo (potForm Om.pot (u i))) ∧
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo →
      0 ≤ locDens A (fun i => potForm (th i) (u i)) j y) ∧
    ∀ g : X → ℝ, (∀ x, 0 ≤ g x) → (∀ x, x ∉ Yo → g x = 0) →
      MIntegrable A (fun i => potForm Om.pot (u i)) g →
      MIntegrable A (fun i => potForm (th i) (u i)) g ∧
        mInt A (fun i => potForm (th i) (u i)) g ≤ mInt A (fun i => potForm Om.pot (u i)) g

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

