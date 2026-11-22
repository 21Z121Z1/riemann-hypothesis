import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpreadRead
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace LiftSpread

theorem exists_common {α : Type} [Fintype α] (Q : α → ℕ → Prop) (hQ : ∀ a n k, Q a n → Q a (k * n))
    (h : ∀ a, ∃ n, 1 ≤ n ∧ Q a n) : ∃ n, 1 ≤ n ∧ ∀ a, Q a n := by
  classical
  choose N hN1 hN using h
  refine ⟨∏ a, N a, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => by
    have := hN1 a; omega), fun a => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ a)
  rw [hm, mul_comm]
  exact hQ a _ m (hN a)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [∀ k, Fintype (ι k)] in

theorem prod_zpow_nsmul (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (t : ℕ) (a : K → ℤ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(t • a) k) = ∏ _l : Fin t, ∏ k, y ⟨k, c k⟩ ^ (-a k) := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring

theorem prod_mem_chartLat (y : (Σ k, ι k) → Ω) {σ : Type} (t : ℕ) (a : K → ℤ) (x : σ → Ω)
    (hx : ∀ j, x j ∈ chartLat y a 1) (f : Fin t → σ) : ∏ l, x (f l) ∈ chartLat y (t • a) 1 := by
  intro c hc
  have hW : ∀ j, x j * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := fun j => by
    have h := hx j c hc
    simpa only [Nat.cast_one, one_mul] using h
  simp only [Nat.cast_one, one_mul]
  rw [prod_zpow_nsmul, ← Finset.prod_mul_distrib]
  exact Subalgebra.prod_mem _ fun l _ => hW (f l)

end LiftSpread

theorem LiftSpread.proof : LiftSpread.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D N _ hA
  classical
  obtain ⟨q, hq, hgen, -⟩ := hA
  obtain ⟨σ, _, s, hs, hrel⟩ := GenRead.exists_sections_of_generatedV y hgen

  obtain ⟨M, hM1, hM⟩ := LiftSpread.exists_common (fun j n => (n : Ω) * s j ∈ chartLat y (q • N) 1)
    (fun j n k h => by
      have e : ((k * n : ℕ) : Ω) * s j = k • ((n : Ω) * s j) := by
        rw [nsmul_eq_mul]; push_cast; ring
      rw [e]
      exact AddSubgroup.nsmul_mem _ h k)
    (fun j => ChartDenominator.proof K ι Ω y (q • N) 1 (s j) (hs j))

  have hrel' : ∀ c : ∀ k, ι k, ∃ v : σ → Ω, (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ j, v j ∈ chartRingQ y c) ∧
      ∑ j, v j * (s j * ∏ k, y ⟨k, c k⟩ ^ (-(q • N) k)) = 1 := fun c => by
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨v, hv⟩ := hrel c hc
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose v hv using hrel'
  obtain ⟨Δ, hΔ1, hΔ⟩ := LiftSpread.exists_common (α := (∀ k, ι k) × σ)
    (fun p n => (∀ k, y ⟨k, p.1 k⟩ ≠ 0) → (n : Ω) * v p.1 p.2 ∈ chartRingZ y p.1)
    (fun p n k h hc => by
      rw [Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ k) (h hc))
    (fun p => by
      by_cases hc : ∀ k, y ⟨k, p.1 k⟩ ≠ 0
      · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin_int _ ((hv p.1 hc).1 p.2)
        exact ⟨n, hn, fun _ => h⟩
      · exact ⟨1, le_rfl, fun h => absurd h hc⟩)
  refine ⟨q, Δ * M, 0, hq, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), fun t _ => ?_⟩

  let e := Fintype.equivFin (Fin t → σ)
  refine ⟨Fintype.card (Fin t → σ), fun i => ∏ l, (M : Ω) * s (e.symm i l), fun i => ?_, fun c hc => ?_⟩
  · rw [mul_smul]
    exact LiftSpread.prod_mem_chartLat y t (q • N) _ hM (e.symm i)
  · refine ⟨t, fun i => ∏ l, (Δ : Ω) * v c (e.symm i l), fun i => ?_, ?_⟩
    · exact Subalgebra.prod_mem _ fun l _ => hΔ (c, e.symm i l) hc
    · set w := ∏ k, y ⟨k, c k⟩ ^ (-(q • N) k) with hw
      have hbase : ∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w) = ((Δ * M : ℕ) : Ω) := by
        have h1 := (hv c hc).2
        calc ∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w) = (Δ : Ω) * M * ∑ j, v c j * (s j * w) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = ((Δ * M : ℕ) : Ω) := by rw [h1]; push_cast; ring
      rw [e.symm.sum_comp (fun f : Fin t → σ =>
        (∏ l, (Δ : Ω) * v c (f l)) * ((∏ l, (M : Ω) * s (f l)) *
          ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k)))]
      calc ∑ f : Fin t → σ, (∏ l, (Δ : Ω) * v c (f l)) * ((∏ l, (M : Ω) * s (f l)) *
            ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k))
          = ∑ f : Fin t → σ, ∏ l, ((Δ : Ω) * v c (f l) * ((M : Ω) * s (f l) * w)) := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [mul_smul, LiftSpread.prod_zpow_nsmul, ← hw, ← Finset.prod_mul_distrib,
              ← Finset.prod_mul_distrib]
        _ = (∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w)) ^ t := by
            rw [Finset.sum_pow', Fintype.piFinset_univ]
        _ = ((Δ * M : ℕ) : Ω) ^ t := by rw [hbase]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights
open scoped ContDiff

noncomputable section

namespace MetricChange

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

theorem weight_continuousAt (W : Weight L) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    ContinuousAt (W.φ j) x := by
  have hy : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hx⟩
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart j).open_source
  have h1 : ContinuousAt (W.φ j ∘ (A.chart j).symm) (A.chart j x) :=
    ((W.smooth j j).continuousOn).continuousAt (hopen.mem_nhds hy)
  have h2 : ContinuousAt ((W.φ j ∘ (A.chart j).symm) ∘ A.chart j) x :=
    h1.comp ((A.chart j).continuousAt hx)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy
  simp [(A.chart j).left_inv hy]

theorem diff_continuous (W₁ W₀ : Weight L) : Continuous (Weight.diff W₁ W₀) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hx : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have h := (weight_continuousAt W₁ _ hx).sub (weight_continuousAt W₀ _ hx)
  refine h.congr ?_
  filter_upwards [(A.chart (chartIdx A x)).open_source.mem_nhds hx] with y hy
  exact (Weight.diff_eq W₁ W₀ _ hy).symm

theorem levi_lerp {ι : Type*} [Fintype ι] {f₀ f₁ : (ι → ℂ) → ℝ} {y : ι → ℂ}
    (h₀ : ContDiffAt ℝ 2 f₀ y) (h₁ : ContDiffAt ℝ 2 f₁ y) (t : ℝ) (w : ι → ℂ) :
    levi (fun z ↦ f₀ z + t * (f₁ z - f₀ z)) y w = (1 - t) * levi f₀ y w + t * levi f₁ y w := by
  have e₀ := h₀.eventually (by simp)
  have e₁ := h₁.eventually (by simp)
  have hfun : (fun z ↦ f₀ z + t * (f₁ z - f₀ z)) = fun z ↦ (1 - t) * f₀ z + t * f₁ z := by
    funext z; ring
  have hfd : fderiv ℝ (fun z ↦ (1 - t) * f₀ z + t * f₁ z) =ᶠ[𝓝 y]
      fun z ↦ (1 - t) • fderiv ℝ f₀ z + t • fderiv ℝ f₁ z := by
    filter_upwards [e₀, e₁] with z hz₀ hz₁
    have d₀ := hz₀.differentiableAt (by norm_num)
    have d₁ := hz₁.differentiableAt (by norm_num)
    rw [fderiv_fun_add (d₀.const_mul _) (d₁.const_mul _), fderiv_const_mul d₀, fderiv_const_mul d₁]
  have D₀ : DifferentiableAt ℝ (fderiv ℝ f₀) y :=
    (h₀.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have D₁ : DifferentiableAt ℝ (fderiv ℝ f₁) y :=
    (h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fun z ↦ (1 - t) • fderiv ℝ f₀ z + t • fderiv ℝ f₁ z) y =
      (1 - t) • fderiv ℝ (fderiv ℝ f₀) y + t • fderiv ℝ (fderiv ℝ f₁) y :=
    ((D₀.hasFDerivAt.const_smul (1 - t)).add (D₁.hasFDerivAt.const_smul t)).fderiv
  rw [hfun, levi, levi, levi, hfd.fderiv_eq, h2]
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem lerp_isSemipositive {W₀ W₁ : Weight L} (h₀ : W₀.IsSemipositive) (h₁ : W₁.IsSemipositive)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (W₀.lerp W₁ t).IsSemipositive := by
  intro j y hy w
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart j).open_source
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source :=
    ⟨hy, (A.chart j).map_target hy⟩
  have c₀ : ContDiffAt ℝ 2 (W₀.φ j ∘ (A.chart j).symm) y :=
    ((W₀.smooth j j).contDiffAt (hopen.mem_nhds hy')).of_le (by norm_cast)
  have c₁ : ContDiffAt ℝ 2 (W₁.φ j ∘ (A.chart j).symm) y :=
    ((W₁.smooth j j).contDiffAt (hopen.mem_nhds hy')).of_le (by norm_cast)
  have key : levi ((W₀.lerp W₁ t).φ j ∘ (A.chart j).symm) y w =
      (1 - t) * levi (W₀.φ j ∘ (A.chart j).symm) y w +
        t * levi (W₁.φ j ∘ (A.chart j).symm) y w :=
    levi_lerp c₀ c₁ t w
  rw [key]
  have a₀ := h₀ j y hy w
  have a₁ := h₁ j y hy w
  have : 0 ≤ 1 - t := by linarith [ht.2]
  exact add_nonneg (mul_nonneg this a₀) (mul_nonneg ht.1 a₁)

theorem proof (hG : GramChiDerivative.Statement) (hBI : BergmanIntegrable.Statement)
    (hBD : BergmanDensIntegrable.Statement) (hU : UniformBergmanBound.Statement)
    (hL : BergmanL1Convergence.Statement) : MetricChange.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV h₀ h₁ V _ hV hdim e ε hε
  have := dV.isProb
  set u := Weight.diff W₁ W₀ with hu_def
  have hu_cont : Continuous u := diff_continuous W₁ W₀
  obtain ⟨M₀, hM₀⟩ := isCompact_univ.exists_bound_of_continuousOn hu_cont.continuousOn
  set M := max M₀ 0 with hM_def
  have hM : ∀ x, ‖u x‖ ≤ M := fun x ↦ (hM₀ x (mem_univ x)).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  have hu_meas : AEStronglyMeasurable u dV.μ := hu_cont.aestronglyMeasurable
  obtain ⟨C, hC⟩ := hU A L W₀ W₁ dV h₀ h₁
  let B : ℕ → ℝ → X → ℝ := fun n t x ↦ bergman (W₀.lerp W₁ t) dV (V n) n x
  let b : ℝ → X → ℝ := fun t x ↦ bergmanDens (W₀.lerp W₁ t) dV x
  let F : ℕ → ℝ → ℝ := fun n t ↦ ∫ x, u x * (((n : ℝ) ^ D)⁻¹ * B n t x) ∂dV.μ
  let f : ℝ → ℝ := fun t ↦ ∫ x, u x * b t x ∂dV.μ
  let χ : ℕ → ℝ → ℝ := fun n s ↦
    chiGram (W₀.lerp W₁ s) dV n (fun a ↦ (e n a : Fin A.n → X → ℂ))
  have hB0 : ∀ n t x, 0 ≤ B n t x := by
    intro n t x
    refine Real.iSup_nonneg fun s ↦ div_nonneg ?_ (integral_nonneg fun y ↦ ?_)
    · unfold ptNormSq; positivity
    · unfold ptNormSq; positivity
  have hderiv : ∀ n t, HasDerivAt (χ n) ((n : ℝ) / 2 * ∫ x, u x * B n t x ∂dV.μ) t :=
    fun n t ↦ hG A L W₀ W₁ dV n (V n) (hV n) (e n) t
  have hF : ∀ n t, F n t = ((n : ℝ) ^ D)⁻¹ * ∫ x, u x * B n t x ∂dV.μ := by
    intro n t
    show ∫ x, u x * (((n : ℝ) ^ D)⁻¹ * B n t x) ∂dV.μ = _
    rw [← integral_const_mul]
    congr 1; funext x; ring
  have hderiv' : ∀ n, 1 ≤ n → ∀ t, HasDerivAt (χ n) ((n : ℝ) ^ (D + 1) / 2 * F n t) t := by
    intro n hn t
    convert hderiv n t using 1
    have : (n : ℝ) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0))
    rw [hF]; field_simp; ring
  have hFmeas : ∀ n, 1 ≤ n → Measurable (F n) := by
    intro n hn
    have hpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) / 2 := by
      have : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
      positivity
    have : F n = fun t ↦ ((n : ℝ) ^ (D + 1) / 2)⁻¹ * deriv (χ n) t := by
      funext t; rw [(hderiv' n hn t).deriv]; field_simp
    rw [this]; exact (measurable_deriv _).const_mul _
  have hFbound : ∀ n, 1 ≤ n → ∀ t ∈ Icc (0 : ℝ) 1, ‖F n t‖ ≤ M * C := by
    intro n hn t ht
    have hnD : (0 : ℝ) < (n : ℝ) ^ D := pow_pos (Nat.cast_pos.2 (by omega)) _
    have hg : ∀ x, ‖u x * (((n : ℝ) ^ D)⁻¹ * B n t x)‖ ≤ M * C := by
      intro x
      have h1 : B n t x ≤ C * (n : ℝ) ^ D := hC n hn t ht (V n) (hV n) x
      have h2 : 0 ≤ ((n : ℝ) ^ D)⁻¹ * B n t x := mul_nonneg (inv_nonneg.2 hnD.le) (hB0 n t x)
      have h3 : ((n : ℝ) ^ D)⁻¹ * B n t x ≤ C := by
        rw [inv_mul_le_iff₀ hnD]; linarith [mul_comm C ((n : ℝ) ^ D)]
      rw [norm_mul, Real.norm_of_nonneg h2]
      exact mul_le_mul (hM x) h3 h2 hM0
    calc ‖F n t‖ ≤ ∫ x, ‖u x * (((n : ℝ) ^ D)⁻¹ * B n t x)‖ ∂dV.μ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, M * C ∂dV.μ :=
          integral_mono_of_nonneg (ae_of_all _ fun x ↦ norm_nonneg _) (integrable_const _)
            (ae_of_all _ hg)
      _ = M * C := by simp
  have hlim : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n ↦ F n t) atTop (𝓝 (f t)) := by
    intro t ht
    have hL1 := hL A L (W₀.lerp W₁ t) dV (lerp_isSemipositive h₀ h₁ ht) V hV (hdim t ht)
    have hbt : Integrable (b t) dV.μ := hBD A L (W₀.lerp W₁ t) dV
    have hub : Integrable (fun x ↦ u x * b t x) dV.μ := hbt.bdd_mul hu_meas (ae_of_all _ hM)
    have key : ∀ n, ‖F n t - f t‖ ≤ M * ∫ x, |((n : ℝ) ^ D)⁻¹ * B n t x - b t x| ∂dV.μ := by
      intro n
      have hg : Integrable (fun x ↦ ((n : ℝ) ^ D)⁻¹ * B n t x) dV.μ :=
        (hBI A L (W₀.lerp W₁ t) dV n (V n) (hV n)).const_mul _
      have hug : Integrable (fun x ↦ u x * (((n : ℝ) ^ D)⁻¹ * B n t x)) dV.μ :=
        hg.bdd_mul hu_meas (ae_of_all _ hM)
      have hd : Integrable (fun x ↦ |((n : ℝ) ^ D)⁻¹ * B n t x - b t x|) dV.μ := (hg.sub hbt).abs
      calc ‖F n t - f t‖ = ‖∫ x, u x * (((n : ℝ) ^ D)⁻¹ * B n t x - b t x) ∂dV.μ‖ := by
            rw [← integral_sub hug hub]; congr 2; funext x; ring
        _ ≤ ∫ x, ‖u x * (((n : ℝ) ^ D)⁻¹ * B n t x - b t x)‖ ∂dV.μ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x, M * |((n : ℝ) ^ D)⁻¹ * B n t x - b t x| ∂dV.μ := by
            refine integral_mono_of_nonneg (ae_of_all _ fun x ↦ norm_nonneg _) (hd.const_mul M)
              (ae_of_all _ fun x ↦ ?_)
            dsimp only
            rw [norm_mul, Real.norm_eq_abs (_ - _)]
            exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)
        _ = M * ∫ x, |((n : ℝ) ^ D)⁻¹ * B n t x - b t x| ∂dV.μ := integral_const_mul _ _
    have h0 : Tendsto (fun n : ℕ ↦ M * ∫ x, |((n : ℝ) ^ D)⁻¹ * B n t x - b t x| ∂dV.μ) atTop
        (𝓝 0) := by
      simpa using hL1.const_mul M
    exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n ↦ norm_nonneg _) key h0)
  have hI : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, F n t) atTop (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M * C) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact (hFmeas n hn).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with n hn
      refine ae_of_all _ fun t ht ↦ hFbound n hn t ?_
      rw [uIoc_of_le zero_le_one] at ht; exact Ioc_subset_Icc_self ht
    · refine ae_of_all _ fun t ht ↦ hlim t ?_
      rw [uIoc_of_le zero_le_one] at ht; exact Ioc_subset_Icc_self ht
  have hsmall : ∀ᶠ n in atTop,
      |(∫ t in (0 : ℝ)..1, F n t) - ∫ t in (0 : ℝ)..1, f t| ≤ 2 * ε := by
    have := (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 hI)).2 (2 * ε) (by positivity)
    filter_upwards [this] with n hn
    rw [← Real.norm_eq_abs]; exact hn.le
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  have hint : IntervalIntegrable (F n) volume 0 1 := by
    refine (intervalIntegrable_const (c := M * C)).mono_fun (hFmeas n hn1).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun t ht ↦ ?_)
    rw [uIoc_of_le zero_le_one] at ht
    exact (hFbound n hn1 t (Ioc_subset_Icc_self ht)).trans (Real.le_norm_self _)
  have hftc : χ n 1 - χ n 0 = ∫ t in (0 : ℝ)..1, (n : ℝ) ^ (D + 1) / 2 * F n t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv' n hn1 t)
      (hint.const_mul _)).symm
  rw [intervalIntegral.integral_const_mul] at hftc
  have hχ1 : χ n 1 = chiGram W₁ dV n (fun a ↦ (e n a : Fin A.n → X → ℂ)) := by
    simp [χ, chiGram, gram, Weight.lerp]
  have hχ0 : χ n 0 = chiGram W₀ dV n (fun a ↦ (e n a : Fin A.n → X → ℂ)) := by
    simp [χ, chiGram, gram, Weight.lerp]
  rw [hχ1, hχ0] at hftc
  change |chiGram W₁ dV n (fun a ↦ (e n a : Fin A.n → X → ℂ)) -
      chiGram W₀ dV n (fun a ↦ (e n a : Fin A.n → X → ℂ)) -
      (n : ℝ) ^ (D + 1) / 2 * ∫ t in (0 : ℝ)..1, f t| ≤ ε * (n : ℝ) ^ (D + 1)
  rw [hftc, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  calc (n : ℝ) ^ (D + 1) / 2 * |(∫ t in (0 : ℝ)..1, F n t) - ∫ t in (0 : ℝ)..1, f t|
      ≤ (n : ℝ) ^ (D + 1) / 2 * (2 * ε) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ε * (n : ℝ) ^ (D + 1) := by ring

end MetricChange

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleiman
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleiman.atDim_of_steps (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    ∀ d, MixedKleiman.AtDim d := by
  intro d
  induction d with
  | zero => exact MixedKleiman.atDim_zero
  | succ n ih =>
    have ih' : MixedKleiman.AtDim (n + 1 - 1) := by simpa using ih
    have hLow : MixedKleiman.LowAt (n + 1) := hL (n + 1) ih'
    intro K _ ι _ P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact hLow K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    · have hlist : (fun i : Fin (n + 1) => if (i : ℕ) < n + 1 then M else A) = fun _ => M :=
        funext fun i => if_pos i.isLt
      rw [hlist]
      rcases Nat.lt_or_ge n 1 with hn | hn
      · obtain rfl : n = 0 := by omega
        have hW := hhM P hP le_rfl
        have e : (fun _ : Fin 1 => M) = ![M] := by
          funext i
          fin_cases i
          rfl
        simpa [e] using hW
      · exact hT (n + 1) (by omega) ih' hLow K ι P P0 M II hII h1 hP h0 hsM hnM hcM hhM

theorem MixedKleiman.proof (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    MixedKleiman.Statement := by
  intro K _ ι _ P P0 d M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
  exact MixedKleiman.atDim_of_steps hL hT d K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleimanTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleimanTop.proof (hFS : ScaledFSHProps.Statement) (hE : ZCombExpand.Statement)
    (hSec : MixedSectionStep.Statement) (hH : ScaledFSTopPos.Statement) (hA : MixedTopAlgebra.Statement) :
    MixedKleimanTop.Statement := by
  intro d hd hAt hLow K _ ι _ P P0 M II hII h1 hP h0 hsM hnM hcM hhM
  obtain ⟨hsH, hcH, hmH⟩ := hFS K ι P P0
  have haH : (scaledFSH ι).a = fun k => (((fun _ => 1 : K → ℕ) k : ℕ) : ℤ) := by
    rw [scaledFSH_a]; rfl
  have e0 : II K ι P d (fun _ => M) =
      (fun i : ℕ => II K ι P d (fun j : Fin d => if (j : ℕ) < d - i then M else scaledFSH ι)) 0 := by
    simp
  rw [e0]
  refine hA d (fun i : ℕ => II K ι P d (fun j : Fin d => if (j : ℕ) < d - i then M else scaledFSH ι)) hd
    (fun i hi1 hid => hLow K ι P P0 M (scaledFSH ι) (fun _ => 1) II hII h1 hP h0 hsM hnM hcM hhM haH hsH hmH hcH
      (d - i) (by omega)) ?_ ?_
  · simpa using hH K ι P d II hII h1 hP
  · intro q p _ hp hpos
    obtain ⟨e1, e2⟩ := hE K ι (II K ι) (hII K ι) P d M (scaledFSH ι) q p hP hsM.1 hsH.1
    rw [← e2 h1]
    exact hSec K ι P P0 d M (scaledFSH ι) II hII hd hP h0 hsM hnM hcM hhM (scaledFSH_a ι) hsH hmH hcH hAt q p hp
      (by rw [e1]; exact hpos)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameImage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameImage

variable {D : ℕ} {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

theorem linForm_projMat (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [linForm, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

def coneEval (x : Ix κ → Ω) :
    MvPolynomial Unit (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* Polynomial Ω :=
  eval₂Hom (Ideal.Quotient.lift (coordIdeal ℤ x) (coneMap ℤ x).toRingHom
    (fun _a ha => (RingHom.mem_ker).1 ha)) (fun _ => 1)

theorem coneEval_graphMap (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (f : MRing (GlobalTheory (Fin (D + 1)))) :
    coneEval x (graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
        (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f)) =
      coneMap ℤ (x ∘ e) (rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap, coneEval, coneMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp =>
    obtain ⟨⟨⟩, k⟩ := q
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [graphMap, inrV, coneEval, coneMap, linForm_projMat]

end ProjFrameImage

open ProjFrameImage in

theorem ProjFrameImage.proof : ProjFrameImage.Statement := by
  intro D Ω _ _ κ _ x e hP
  refine le_antisymm (fun f hf => ?_) bot_le
  have h0 : graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
      (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f) = 0 :=
    (RingHom.mem_ker).1 (Ideal.mem_comap.1 hf)
  have h1 : rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f ∈ coordIdeal ℤ (x ∘ e) := by
    rw [coordIdeal, RingHom.mem_ker, ← coneEval_graphMap x e f, h0, map_zero]
  rw [hP.free, Ideal.mem_bot] at h1
  have hinj : Function.Injective (fun q : Σ _ : Unit, Fin (D + 1) => q.2) := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    cases h
    rfl
  exact (Ideal.mem_bot).2 (rename_injective _ hinj (by rw [h1, map_zero]))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBigIffGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def BigIffGenDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (M : HermLine ι) (P₀ : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → P₀ ≤ mCoordIdeal y →
    IsSemipositiveRel P₀ (mCoordIdeal y) M →
    (IndefiniteRowSideFullHecke.HilbertSamuel.IsBig y M.a D ↔ 0 < genDeg (mCoordIdeal y) D M.a)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

