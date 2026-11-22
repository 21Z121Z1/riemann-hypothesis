import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0035
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0003
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeOfDet
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrderToIntegral

open Filter Metric

theorem norm_le_of_det {n : ℕ} {f : V n → V n} {f' : V n →L[ℂ] V n} (hf : HasFDerivAt f f' 0)
    (hdet : f'.det ≠ 0) (h0 : f 0 = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ z in 𝓝 (0 : V n), ‖z‖ ≤ K * ‖f z‖ := by
  obtain ⟨K, hKpos, hK⟩ := (f' : V n →ₗ[ℂ] V n).exists_antilipschitzWith (HE.ker_bot_of_det hdet)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hK' : ∀ z : V n, ‖z‖ ≤ K * ‖f' z‖ := fun z => by
    have := hK.le_mul_dist z 0
    simpa using this
  have hlo := hf.isLittleO.bound (c := 1 / (2 * K)) (by positivity)
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [hlo] with z hz
  rw [h0, sub_zero, sub_zero] at hz
  have h1 : ‖f' z‖ ≤ ‖f z‖ + 1 / (2 * K) * ‖z‖ := by
    have : ‖f' z‖ ≤ ‖f z‖ + ‖f z - f' z‖ := by
      calc ‖f' z‖ = ‖f z - (f z - f' z)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  have h2 : (K : ℝ) * (1 / (2 * K) * ‖z‖) = ‖z‖ / 2 := by field_simp
  have h3 := mul_le_mul_of_nonneg_left h1 hK0.le
  have h4 := hK' z
  rw [mul_add, h2] at h3
  linarith

theorem sum_sq_lower {n : ℕ} (hn : 0 < n) {w : V n → ℂ} {s : Fin n → V n → ℂ}
    (hw : ContinuousAt w 0) (hw0 : w 0 ≠ 0) (hs0 : ∀ k, s k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0).det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ^ 2 ≤ ∑ k, ‖s k z‖ ^ 2 := by
  have hF : DifferentiableAt ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0 := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hdet
    apply hdet
    show LinearMap.det (0 : V n →ₗ[ℂ] V n) = 0
    rw [LinearMap.det_zero, finrank_euclideanSpace, Fintype.card_fin, zero_pow (by omega)]
  obtain ⟨K, hK, hle⟩ := norm_le_of_det hF.hasFDerivAt hdet (by ext k; simp [hs0])
  have hpos : 0 < ‖w 0‖ := norm_pos_iff.2 hw0
  have hg : ∀ᶠ z in 𝓝 (0 : V n), ‖w 0‖ / 2 ≤ ‖w z‖ :=
    (hw.norm.tendsto.eventually (lt_mem_nhds (half_lt_self hpos))).mono fun z hz => le_of_lt hz
  refine ⟨(‖w 0‖ / 2) ^ 2 / K ^ 2, by positivity, ?_⟩
  filter_upwards [hle, hg] with z hz hwz
  have hwz0 : 0 < ‖w z‖ := lt_of_lt_of_le (half_pos hpos) hwz
  have e1 : ‖(WithLp.toLp 2 fun k => s k z / w z : V n)‖ ^ 2 = (∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_div]
    simp [div_pow]
  have h1 : ‖z‖ ^ 2 ≤ K ^ 2 * ((∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2) := by
    rw [← e1, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have h2 : (‖w 0‖ / 2) ^ 2 ≤ ‖w z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hwz 2
  calc (‖w 0‖ / 2) ^ 2 / K ^ 2 * ‖z‖ ^ 2
      ≤ ‖w z‖ ^ 2 / K ^ 2 * (K ^ 2 * ((∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2)) := by gcongr
    _ = ∑ k, ‖s k z‖ ^ 2 := by field_simp

theorem lintegral_lt_top {n : ℕ} (hn : 0 < n) {g : V n → ℂ} {S : V n → ℝ} {a : ℕ} {c : ℝ}
    (hc : 0 < c) (hS : ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ^ 2 ≤ S z)
    (hg : g =O[𝓝 0] fun z => ‖z‖ ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∫⁻ z in ball (0 : V n) ρ,
      ENNReal.ofReal (‖g z‖ ^ 2 * S z ^ (-((a : ℝ) + (n : ℝ) - 1 / 2))) < ⊤ := by
  obtain ⟨C, hC, hO⟩ := hg.exists_pos
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hO.bound.and hS)
  have : Nontrivial (V n) := ⟨⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℂ), 0, by
    intro h
    have h1 := congrArg (fun v : V n => v ⟨0, hn⟩) h
    simp at h1⟩⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set e : ℝ := (a : ℝ) + (n : ℝ) - 1 / 2 with he
  have he0 : 0 ≤ e := by
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  have hint := (mvInt n hn ((n : ℝ) - 1 / 2)).2 (by linarith)
  refine ⟨min ε 1, lt_min hε one_pos, ?_⟩
  have hfin : ENNReal.ofReal (C ^ 2 * c ^ (-e)) *
      ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * ((n : ℝ) - 1 / 2)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  refine lt_of_le_of_lt ?_ hfin
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans ?_ (lintegral_mono_set (ball_subset_ball (min_le_right ε 1)))
  refine lintegral_mono_ae ?_
  have h0 : ∀ᵐ z ∂(volume.restrict (ball (0 : V n) (min ε 1))), z ≠ 0 :=
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (0 : V n)))
  filter_upwards [h0, ae_restrict_mem measurableSet_ball] with z hz0 hz
  obtain ⟨h1, h2⟩ := hball z (ball_subset_ball (min_le_left ε 1) hz)
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  rw [ENNReal.ofReal_rpow_of_pos hz, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_pow, norm_norm] at h1
  have h3 : ‖g z‖ ^ 2 ≤ (C * ‖z‖ ^ a) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 : S z ^ (-e) ≤ (c * ‖z‖ ^ 2) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  have hSz : 0 ≤ S z := le_trans (by positivity) h2
  have h5 : (‖z‖ ^ a) ^ 2 * (‖z‖ ^ 2) ^ (-e) = ‖z‖ ^ (-2 * ((n : ℝ) - 1 / 2)) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hz.le,
      ← Real.rpow_add hz]
    congr 1
    rw [he]
    push_cast
    ring
  calc ‖g z‖ ^ 2 * S z ^ (-e) ≤ (C * ‖z‖ ^ a) ^ 2 * (c * ‖z‖ ^ 2) ^ (-e) :=
        mul_le_mul h3 h4 (Real.rpow_nonneg hSz _) (by positivity)
    _ = C ^ 2 * c ^ (-e) * ((‖z‖ ^ a) ^ 2 * (‖z‖ ^ 2) ^ (-e)) := by
        rw [Real.mul_rpow hc.le (by positivity)]
        ring
    _ = _ := by rw [h5]

end GlobalTheory.OrderToIntegral

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem vanS_of_isBigO : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (a : ℕ)
    (g : Frame X.Ψ r → ℂ), ContinuousOn g X.dom →
    (∀ j, (fun z : V (nd X) => g (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ a) →
    VanS X Fl.xs Fl.s a g := by
  intro r X Xa Fl a g _ hO j
  have hn : 0 < nd X := lt_of_lt_of_le (by norm_num) Xa.n_ge
  have hw0 : X.IsSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1.1
  have hs0 : ∀ k, Fl.s k (Fl.xs j) = 0 :=
    (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, by
      rw [FundSetPf.lact_one, ExtFPf.rmul_oneF]⟩
  have hw : ContinuousAt (fun z : V (nd X) => Fl.w0 (cpt X (Fl.xs j) z)) 0 := by
    refine ContinuousAt.comp (g := Fl.w0) ?_ (FundSetPf.cont_cpt X (Fl.xs j)).continuousAt
    rw [IW.cpt_zero]
    exact hw0.1.continuousOn.continuousAt ((FourierCoefficientDomain.isOpen_dom X).mem_nhds (Fl.xs_mem j))
  obtain ⟨c, hc, hS⟩ := OrderToIntegral.sum_sq_lower
    (w := fun z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun k z => Fl.s k (cpt X (Fl.xs j) z)) hn hw
    (by simpa only [IW.cpt_zero] using Fl.w0_ne j) (by simpa only [IW.cpt_zero] using hs0)
    (Fl.coord j)
  exact OrderToIntegral.lintegral_lt_top hn hc hS (hO j)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.VanishOfSimpleZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.VanishAtSimpleZero

open Filter Metric

theorem lintegral_eq_top {n : ℕ} (hn : 0 < n) {g S : V n → ℝ} {a c ρ : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hρ : 0 < ρ) (hg : ∀ᶠ z in 𝓝 (0 : V n), a ≤ g z)
    (hS : ∀ᶠ z in 𝓝 (0 : V n), z ≠ 0 → 0 < S z ∧ S z ≤ c * ‖z‖ ^ 2) :
    ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (g z * S z ^ (-(n : ℝ))) = ⊤ := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hg.and hS)
  have hr0 : 0 < min ε ρ := lt_min hε hρ
  have hsubε : ball (0 : V n) (min ε ρ) ⊆ ball 0 ε := ball_subset_ball (min_le_left _ _)
  have hsubρ : ball (0 : V n) (min ε ρ) ⊆ ball 0 ρ := ball_subset_ball (min_le_right _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h0 : ∀ᵐ z ∂(volume : Measure (V n)), z ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton 0
  have hinf : ∫⁻ z in ball (0 : V n) (min ε ρ), ENNReal.ofReal ((c * ‖z‖ ^ 2) ^ (-(n : ℝ))) = ⊤ := by
    have hδ : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)⟩
    have hT := ReciprocityTheory.L2DbarEstimates.I.vanish_div n hn ReciprocityTheory.L2DbarEstimates.C.mvDiv hr0 hc hδ
    refine top_unique (le_of_tendsto' hT fun k => ?_)
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (h0.mono fun z hz _ => ?_))
    have hpos : 0 < c * ‖z‖ ^ 2 := mul_pos hc (pow_pos (norm_pos_iff.2 hz) 2)
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hpos ?_ ?_)
    · have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · simp
  have hlow : ENNReal.ofReal a * ∫⁻ z in ball (0 : V n) (min ε ρ),
      ENNReal.ofReal ((c * ‖z‖ ^ 2) ^ (-(n : ℝ))) ≤
      ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (g z * S z ^ (-(n : ℝ))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans ?_ (lintegral_mono_set hsubρ)
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (h0.mono fun z hz hzb => ?_))
    obtain ⟨hgz, hSz⟩ := hball z (hsubε hzb)
    obtain ⟨hS0, hSle⟩ := hSz hz
    rw [← ENNReal.ofReal_mul ha.le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul hgz (Real.rpow_le_rpow_of_nonpos hS0 hSle (by simp))
      (Real.rpow_nonneg (by positivity) _) (ha.le.trans hgz))
  rw [hinf, ENNReal.mul_top (by simpa using ha)] at hlow
  exact top_unique hlow

theorem vanish_of_simple_zero {n : ℕ} (hn : 0 < n) {u w : V n → ℂ} {s : Fin n → V n → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hu : ContinuousAt u 0) (hs : ∀ k, DifferentiableAt ℂ (s k) 0)
    (hw : DifferentiableAt ℂ w 0) (hw0 : w 0 ≠ 0) (hs0 : ∀ k, s k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0).det ≠ 0)
    (hint : ∫⁻ z in ball (0 : V n) ρ,
      ENNReal.ofReal (‖u z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-(n : ℝ))) < ⊤) : u 0 = 0 := by
  by_contra hu0
  set f : V n → V n := fun z => (WithLp.toLp 2 fun k => s k z / w z : V n) with hf
  have hfd : DifferentiableAt ℂ f 0 := by
    by_contra hnd
    apply hdet
    rw [fderiv_zero_of_not_differentiableAt hnd]
    simp [ContinuousLinearMap.det, LinearMap.det_zero, hn.ne']
  have hf0 : f 0 = 0 := by
    ext k
    simp [hf, hs0 k]
  obtain ⟨δ, hδ, hiso⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.iso_zero hfd.hasFDerivAt hdet hf0
  have hSpos : ∀ᶠ z in 𝓝 (0 : V n), z ≠ 0 → 0 < ∑ k, ‖s k z‖ ^ 2 := by
    filter_upwards [closedBall_mem_nhds (0 : V n) hδ] with z hz hz0
    refine lt_of_le_of_ne (Finset.sum_nonneg fun k _ => by positivity) (Ne.symm fun hsum => hz0 ?_)
    refine hiso z hz ?_
    have hk : ∀ k, s k z = 0 := fun k => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 hsum k (Finset.mem_univ _)
      simpa using this
    ext k
    simp [hf, hk k]
  have hbig : ∀ k, ∃ C > 0, ∀ᶠ z in 𝓝 (0 : V n), ‖s k z‖ ≤ C * ‖z‖ := fun k => by
    obtain ⟨C, hC, hCw⟩ := ((hs k).hasFDerivAt.isBigO_sub).exists_pos
    refine ⟨C, hC, hCw.bound.mono fun z hz => ?_⟩
    simpa [hs0 k] using hz
  choose C hC hCb using hbig
  have hSle : ∀ᶠ z in 𝓝 (0 : V n), ∑ k, ‖s k z‖ ^ 2 ≤ (∑ k, C k ^ 2 + 1) * ‖z‖ ^ 2 := by
    filter_upwards [Filter.eventually_all.2 hCb] with z hz
    calc ∑ k, ‖s k z‖ ^ 2 ≤ ∑ k, (C k * ‖z‖) ^ 2 :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hz k) 2
      _ = (∑ k, C k ^ 2) * ‖z‖ ^ 2 := by rw [Finset.sum_mul]; simp [mul_pow]
      _ ≤ _ := by nlinarith [sq_nonneg ‖z‖]
  have hpos : 0 < ‖u 0‖ ^ 2 := pow_pos (norm_pos_iff.2 hu0) 2
  have hcont : ContinuousAt (fun z => ‖u z‖ ^ 2) 0 := hu.norm.pow 2
  have hg : ∀ᶠ z in 𝓝 (0 : V n), ‖u 0‖ ^ 2 / 2 ≤ ‖u z‖ ^ 2 :=
    hcont.eventually (le_mem_nhds (show ‖u 0‖ ^ 2 / 2 < ‖u 0‖ ^ 2 by linarith))
  have htop := lintegral_eq_top hn (g := fun z => ‖u z‖ ^ 2) (S := fun z => ∑ k, ‖s k z‖ ^ 2)
    (by positivity) (by positivity : (0 : ℝ) < ∑ k, C k ^ 2 + 1) hρ hg
    (by filter_upwards [hSpos, hSle] with z h1 h2 hz0 using ⟨h1 hz0, h2⟩)
  exact absurd hint (by rw [htop]; exact lt_irrefl _)

end GlobalTheory.VanishAtSimpleZero

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem vanishAtS_holds : VanishAtSStatement (E := E) := by
  intro r X x1 hn _ _ u w0 s ρ hρ hdu hds hdw hw0 hs0 hdet hint
  have h0 := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero X x1
  have hb : Metric.ball (0 : V (nd X)) ρ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hρ
  have key := VanishAtSimpleZero.vanish_of_simple_zero hn (u := fun z => u (cpt X x1 z))
    (w := fun z => w0 (cpt X x1 z)) (s := fun k z => s k (cpt X x1 z)) hρ
    ((hdu.differentiableAt hb).continuousAt) (fun k => (hds k).differentiableAt hb)
    (hdw.differentiableAt hb) (by simpa [h0] using hw0) (fun k => by simpa [h0] using hs0 k) hdet hint
  simpa [h0] using key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightContDiffOn
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.KronSolve

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def weight (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb : ℝ)
    (z : V (nd X)) : ℝ :=
  phla X la (cpt X x0 z) + ((-1) * Real.log (densF X x0 z) +
    ((-(nd X : ℝ)) * phla X L (cpt X x0 z) + (ψ (cpt X x0 z) + (-bb) * rhF X x0 z)))

theorem weight_contDiffOn (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r)
    (bb : ℝ) (hψ : ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) :
    ContDiffOn ℝ ∞ (weight X la L ψ x0 bb) (OmF X x0) := by
  intro z hz
  have h1 := IW.phla_cpt_cdAt X x0 hz la
  have h2 := IW.logDens_cdAt X x0 hz
  have h3 := IW.phla_cpt_cdAt X x0 hz L
  have h4 := hψ.contDiffAt ((OntoB.isOpen_OmF X x0).mem_nhds hz)
  have h5 := OntoB.rhF_contDiffAt hz
  exact (h1.add ((contDiffAt_const.mul h2).add ((contDiffAt_const.mul h3).add
    (h4.add (contDiffAt_const.mul h5))))).contDiffWithinAt

theorem levi_weight (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r)
    (bb : ℝ) (hψ : ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    (leviV (nd X) (fun w => ((weight X la L ψ x0 bb w : ℝ) : ℂ)) z ξ).re =
      leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X L) z ξ +
        leviO X x0 ψ z ξ - bb * leviRh X x0 z ξ := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz la).of_le HE.two_le_inf
  have h2 := (IW.logDens_cdAt X x0 hz).of_le HE.two_le_inf
  have h3 := (IW.phla_cpt_cdAt X x0 hz L).of_le HE.two_le_inf
  have h4 := (hψ.contDiffAt ((OntoB.isOpen_OmF X x0).mem_nhds hz)).of_le HE.two_le_inf
  have h5 : ContDiffAt ℝ 2 (fun w => rhF X x0 w) z := (OntoB.rhF_contDiffAt hz).of_le HE.two_le_inf
  unfold weight leviO leviM leviDens leviRh
  rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 ((contDiffAt_const.mul h2).add ((contDiffAt_const.mul h3).add
      (h4.add (contDiffAt_const.mul h5)))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2) ((contDiffAt_const.mul h3).add
      (h4.add (contDiffAt_const.mul h5))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h3) (h4.add (contDiffAt_const.mul h5)),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add h4 (contDiffAt_const.mul h5),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h5]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  ring

theorem pnorm_sq (X : Data E r) (L : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x0 : Frame X.Ψ r)
    {z : V (nd X)} (hz : z ∈ OmF X x0) :
    X.pnorm L P (cpt X x0 z) ^ 2 =
      Complex.normSq (P (cpt X x0 z)) * Real.exp (-phla X L (cpt X x0 z)) := by
  have hp := OntoE.nfac_pos X x0 (la := L) hz
  have e : X.pnorm L P (cpt X x0 z) = ‖P (cpt X x0 z)‖ * X.nfac L (cpt X x0 z) := rfl
  have e2 : Real.exp (-phla X L (cpt X x0 z)) = X.nfac L (cpt X x0 z) ^ 2 := by
    have : -phla X L (cpt X x0 z) = Real.log (X.nfac L (cpt X x0 z) ^ 2) := by
      rw [Real.log_pow]; unfold phla; push_cast; ring
    rw [this, Real.exp_log (pow_pos hp 2)]
  rw [e, e2, Complex.normSq_eq_norm_sq, mul_pow]

theorem integrand_eq (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r)
    (bb : ℝ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (A : ℝ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    densF X x0 z * (A * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z *
      (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) =
    A * Real.exp (-weight X la L ψ x0 bb z) *
      HE.nsq (fun k w => s k (cpt X x0 w)) z ^ (-(nd X : ℝ)) := by
  have hs : ∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2 =
      HE.nsq (fun k w => s k (cpt X x0 w)) z * Real.exp (-phla X L (cpt X x0 z)) := by
    unfold HE.nsq
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => pnorm_sq X L (s k) x0 hz
  rw [hs, Real.mul_rpow (HE.nsq_nonneg _ _) (Real.exp_pos _).le, ← Real.exp_mul]
  have hd : densF X x0 z = Real.exp (Real.log (densF X x0 z)) :=
    (Real.exp_log (OntoB.densF_pos hz)).symm
  have hw : Real.exp (-weight X la L ψ x0 bb z) =
      Real.exp (Real.log (densF X x0 z)) * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) *
        Real.exp (-(-bb * rhF X x0 z)) * Real.exp (-phla X L (cpt X x0 z) * -(nd X : ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold weight
    ring
  rw [hw, ← hd, kaF, Real.exp_neg (-bb * rhF X x0 z), div_eq_mul_inv]
  ring

end

end GlobalTheory.KronSolve

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kronSolve : (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb m η : ℝ), 0 < nd X → IsOrth X x0 → X.IsSec L w0 → (∀ k, X.IsSec L (s k)) → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0) → 0 ≤ bb → bb < m → 0 < η → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X L) z ξ + leviO X x0 ψ z ξ) → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 2 * η * leviO X x0 (phla X L) z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X L) z ξ + leviO X x0 ψ z ξ) → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 → 0 < leviO X x0 (phla X L) z ξ) → w0 x0 ≠ 0 → (∀ k, s k x0 = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x0) z) / w0 (cpt X (x0) z) : V (nd X))) 0).det ≠ 0 → ∃ (ε : ℝ) (χ F : V (nd X) → ℂ), 0 < ε ∧ Metric.closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0 ∧ (∀ z ∈ Metric.closedBall (0 : V (nd X)) (2 * ε), (∀ k, s k (cpt X x0 z) = 0) → z = 0) ∧ Continuous χ ∧ (∀ z, ‖z‖ ≤ ε → χ z = 1) ∧ (∀ z, 2 * ε ≤ ‖z‖ → χ z = 0) ∧ DifferentiableOn ℂ F (OmF X x0) ∧ ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤) := by
  intro r X la L w0 s ψ x0 bb m η hn ho hw0 hs hψ hbb hbm hη hm h2 hL hw00 hs0 hdet
  have hU := OntoB.isOpen_OmF X x0
  have h0 := IW.zero_mem_OmF X x0 ho
  have hc0 := IW.cpt_zero X x0
  have hsd : ∀ k, DifferentiableOn ℂ (fun z => s k (cpt X x0 z)) (OmF X x0) :=
    fun k => OntoB.hol_comp X x0 (hs k).1
  have hwd : DifferentiableOn ℂ (fun z => w0 (cpt X x0 z)) (OmF X x0) := OntoB.hol_comp X x0 hw0.1
  set f : V (nd X) → V (nd X) := fun z =>
    (WithLp.toLp 2 fun k => s k (cpt X x0 z) / w0 (cpt X x0 z) : V (nd X)) with hf
  have hfd : DifferentiableAt ℂ f 0 := by
    rw [differentiableAt_euclidean]
    intro k
    have hne : w0 (cpt X x0 0) ≠ 0 := by rw [hc0]; exact hw00
    have h1 := (hsd k).differentiableAt (hU.mem_nhds h0)
    have h2 := (hwd.differentiableAt (hU.mem_nhds h0)).inv hne
    have h3 := h1.mul h2
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp [hf, div_eq_mul_inv]
  have hf0 : f 0 = 0 := by
    ext k
    simp [hf, hc0, hs0 k]
  obtain ⟨δ, hδ, hiso⟩ := HE.iso_zero hfd.hasFDerivAt hdet hf0
  obtain ⟨k0, hk0⟩ := HE.coord_ne_of_det (f := f) hn hdet
  have hk0' : ¬ (fun z => s k0 (cpt X x0 z)) =ᶠ[𝓝 0] 0 := by
    intro h
    apply hk0
    filter_upwards [h] with z hz
    have hz' : s k0 (cpt X x0 z) = 0 := hz
    simp [hf, hz']
  have hgn := HE.hgn_of hU (OmFConnStatement_holds r X x0 ho) (hsd k0) h0 hk0'
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  set ε : ℝ := min δ ρ / 4 with hεdef
  have hmin : 0 < min δ ρ := lt_min hδ hρ
  have hε : 0 < ε := by positivity
  have hε1 : 2 * ε ≤ δ := by have := min_le_left δ ρ; linarith
  have hε2 : 2 * ε < ρ := by have := min_le_right δ ρ; linarith
  have hcb : Metric.closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0 :=
    (Metric.closedBall_subset_ball hε2).trans hball
  have hiso' : ∀ z ∈ Metric.closedBall (0 : V (nd X)) (2 * ε),
      (∀ k, s k (cpt X x0 z) = 0) → z = 0 := by
    intro z hz hsz
    refine hiso z (Metric.closedBall_subset_closedBall hε1 hz) ?_
    ext k
    simp [hf, hsz k]
  have hW := KronSolve.weight_contDiffOn X la L ψ x0 bb hψ
  have hWpos : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < (leviV (nd X) (fun w => ((KronSolve.weight X la L ψ x0 bb w : ℝ) : ℂ)) z ξ).re := by
    intro z hz ξ hξ
    rw [KronSolve.levi_weight X la L ψ x0 bb hψ hz ξ]
    have a1 := hm z hz ξ
    have a2 := h2 z hz ξ
    have a3 := hL z hz ξ hξ
    set Q := leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ -
      (nd X : ℝ) * leviO X x0 (phla X L) z ξ + leviO X x0 ψ z ξ
    set R := leviRh X x0 z ξ
    have hQ : 0 < Q := lt_of_lt_of_le (by positivity) a2
    have hm0 : 0 < m := lt_of_le_of_lt hbb hbm
    have : 0 < m * (Q - bb * R) := by
      have b1 : 0 < (m - bb) * Q := mul_pos (by linarith) hQ
      have b2 : 0 ≤ bb * (Q - m * R) := mul_nonneg hbb (by linarith)
      nlinarith
    exact (mul_pos_iff_of_pos_left hm0).1 this
  have hWnn : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((KronSolve.weight X la L ψ x0 bb w : ℝ) : ℂ)) z ξ).re := by
    intro z hz ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp [leviV]
    · exact (hWpos z hz ξ hξ).le
  obtain ⟨c, hc, hunif⟩ := HE.levi_unif hU hW (isCompact_closedBall (0 : V (nd X)) (2 * ε)) hcb
    (fun z hz => hWpos z (hcb hz))
  have he : ContDiffOn ℝ ∞ (eF X x0) (OmF X x0) :=
    fun z hz => (ExF.eF_contDiffAt X x0 ho hz).contDiffWithinAt
  have hel : ∀ y ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((eF X x0 w : ℝ) : ℂ)) y ξ).re := by
    intro y hy ξ
    have e1 : (fun y : V (nd X) => ((eF X x0 y : ℝ) : ℂ)) =
        fun y => ((rhF X x0 y + Real.log (1 + ‖y‖ ^ 2) : ℝ) : ℂ) := rfl
    rw [e1, Y.LocalMaximumSecondDerivative.leviV_ofReal_add
      ((ExF.rhF_contDiffAt X x0 ho hy).of_le HE.two_le_inf)
      (ExF.T_cd.contDiffAt.of_le HE.two_le_inf) ξ, Complex.add_re]
    exact add_nonneg (ExF.levi_rhF_nonneg X x0 ho hy ξ) (ExF.leviT_nonneg _ ξ)
  have he0 : ∀ y ∈ OmF X x0, 0 ≤ eF X x0 y := fun y hy =>
    add_nonneg (ExF.rhF_nonneg X x0 ho hy) (Real.log_nonneg (by nlinarith [sq_nonneg ‖y‖]))
  obtain ⟨F, hFd, hF⟩ := HE.interp_euclid hU (eF X x0) he hel (ExF.isCompact_subF X x0 ho) he0
    (fun k w => s k (cpt X x0 w)) hsd k0 hgn (KronSolve.weight X la L ψ x0 bb) hW hWnn ε hε hcb hiso'
    c hc hunif
  refine ⟨ε, HE.cut ε hε, F, hε, hcb, hiso', (HE.cut_contDiff ε hε).continuous,
    fun z hz => HE.cut_one ε hε hz, fun z hz => HE.cut_zero ε hε hz, hFd, ?_⟩
  refine lt_of_eq_of_lt ?_ hF
  unfold muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (OntoC.measurable_densF X x0)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (OntoB.densF_pos hz).le, KronSolve.integrand_eq X la L ψ x0 bb s _ hz]

end GlobalTheory
end

