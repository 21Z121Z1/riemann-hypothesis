import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0031
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0625
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlurisubharmonicDecreasingLimitExtension
section
open ReciprocityTheory.L2DbarEstimates MeasureTheory Metric Set Filter
open scoped ENNReal ContDiff Topology

namespace GlobalTheory.HormanderLimit

theorem exists_tendstoLocallyUniformlyOn_ultrafilter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} {F : ℕ → E → ℂ} (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ c ∈ U, ∃ r > 0, ∃ M : ℝ, ball c r ⊆ U ∧ ∀ k, ∀ z ∈ ball c r, ‖F k z‖ ≤ M)
    (𝒰 : Ultrafilter ℕ) : ∃ f : E → ℂ, TendstoLocallyUniformlyOn F f (𝒰 : Filter ℕ) U := by
  have hpt : ∀ c, ∃ a : ℂ, c ∈ U → Tendsto (fun k => F k c) (𝒰 : Filter ℕ) (𝓝 a) := by
    intro c
    by_cases hc : c ∈ U
    · obtain ⟨r, hr, M, -, hM⟩ := hb c hc
      obtain ⟨a, -, ha⟩ := (isCompact_closedBall (0 : ℂ) M).ultrafilter_le_nhds
        (𝒰.map fun k => F k c) (by
          rw [le_principal_iff, Ultrafilter.coe_map, mem_map]
          exact Eventually.of_forall fun k => by
            simpa using hM k c (mem_ball_self hr))
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose f hf using hpt
  refine ⟨f, Metric.tendstoLocallyUniformlyOn_iff.2 fun ε hε c hc => ?_⟩
  obtain ⟨r, hr, M, hrU, hM⟩ := hb c hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 c (mem_ball_self hr))
  set L : ℝ := (2 * M + 1) / r with hL
  have hL0 : 0 < L := by positivity
  have hlip : ∀ k, ∀ z ∈ ball c r, dist (F k z) (F k c) ≤ L * dist z c := by
    intro k z hz
    refine Complex.dist_le_div_mul_dist_of_mapsTo_ball ((hF k).mono hrU) (fun w hw => ?_) hz
    have := norm_sub_le (F k w) (F k c)
    have h2 : dist (F k w) (F k c) < 2 * M + 1 := by
      rw [dist_eq_norm]
      linarith [hM k w hw, hM k c (mem_ball_self hr)]
    first
      | exact mem_ball.2 h2
      | exact mem_closedBall.2 h2.le
  have hlipf : ∀ z ∈ ball c r, dist (f z) (f c) ≤ L * dist z c := fun z hz =>
    le_of_tendsto ((hf z (hrU hz)).dist (hf c hc)) (Eventually.of_forall fun k => hlip k z hz)
  refine ⟨ball c (min r (ε / (3 * L))), nhdsWithin_le_nhds (ball_mem_nhds c (by positivity)), ?_⟩
  filter_upwards [(Metric.tendsto_nhds.1 (hf c hc)) (ε / 3) (by positivity)] with k hk y hy
  have hy1 : y ∈ ball c r := ball_subset_ball (min_le_left _ _) hy
  have hy2 : dist y c < ε / (3 * L) := (mem_ball.1 hy).trans_le (min_le_right _ _)
  have hy3 : L * dist y c < ε / 3 := by
    rw [lt_div_iff₀ (by positivity)] at hy2
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have h1 := hlipf y hy1
  have h2 := hlip k y hy1
  have h3 := dist_triangle4 (f y) (f c) (F k c) (F k y)
  rw [dist_comm (F k y)] at h2
  rw [dist_comm] at hk
  linarith

theorem enorm_sq_le_lintegral {n : ℕ} {g : V n → ℂ} {c : V n} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) :
    ‖g c‖ₑ ^ 2 ≤ (volume (closedBall (0 : V n) r))⁻¹ * ∫⁻ z in closedBall c r, ‖g z‖ₑ ^ 2 := by
  have hd : DifferentiableOn ℂ (fun z => g (c + z)) (ball 0 r) :=
    hg.comp (by fun_prop) fun z hz => by simpa [mem_ball_iff_norm] using hz
  obtain ⟨-, h1, -⟩ := GlobalTheory.submean_sq_closedBall hr hd
  have h2 := (measurePreserving_add_left (volume : Measure (V n)) c).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addLeft c).measurableEmbedding (fun z => ‖g z‖ₑ ^ 2) (closedBall c r)
  have h3 : (fun z => c + z) ⁻¹' closedBall c r = closedBall 0 r := by
    ext z
    simp [mem_closedBall_iff_norm]
  rw [h3] at h2
  rw [← h2]
  simpa using h1

theorem locally_bounded_of_lintegral {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {F : ℕ → V n → ℂ}
    (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k, ∫⁻ z in K, ‖F k z‖ₑ ^ 2 ≤ C) :
    ∀ c ∈ U, ∃ r > 0, ∃ M : ℝ, ball c r ⊆ U ∧ ∀ k, ∀ z ∈ ball c r, ‖F k z‖ ≤ M := by
  intro c hc
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU c hc
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  have hK : closedBall c (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  obtain ⟨C, hC, hCk⟩ := hb _ hK (isCompact_closedBall _ _)
  set B : ℝ≥0∞ := (volume (closedBall (0 : V n) r))⁻¹ * C with hB
  have hBt : B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (measure_closedBall_pos _ _ hr0).ne') hC
  refine ⟨r, hr0, Real.sqrt B.toReal, (ball_subset_ball (by linarith)).trans hRU,
    fun k z hz => ?_⟩
  have hsub : closedBall z r ⊆ closedBall c (2 * r) :=
    closedBall_subset_closedBall' (by linarith [mem_ball.1 hz])
  have h1 := enorm_sq_le_lintegral hr0
    ((hF k).mono (ball_subset_closedBall.trans (hsub.trans hK)))
  have h2 : ‖F k z‖ₑ ^ 2 ≤ B :=
    h1.trans (by
      rw [hB]
      gcongr
      exact (lintegral_mono_set hsub).trans (hCk k))
  refine Real.le_sqrt_of_sq_le ?_
  have h3 := ENNReal.toReal_mono hBt h2
  simpa using h3

theorem exists_limit {n : ℕ} {U : Set (V n)} (hU : IsOpen U) (K : ℕ → Set (V n))
    (hKc : ∀ j, IsCompact (K j)) (hKU : ∀ j, K j ⊆ U) (hK : ∀ y ∈ U, ∀ᶠ j in atTop, y ∈ K j)
    {φ : ℕ → V n → ℝ} (hφ : ∀ k, ContinuousOn (φ k) U) (hdec : ∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y)
    {F0 : V n → ℂ} (hF0 : ContinuousOn F0 U) {A : ℝ≥0∞} (hA : A ≠ ⊤) {F : ℕ → V n → ℂ}
    (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hest : ∀ k, ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F k y‖ ^ 2 * Real.exp (-φ k y)) ≤ A) :
    ∃ f : V n → ℂ, DifferentiableOn ℂ f U ∧
      ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  have hanti : ∀ y ∈ U, Antitone fun k => φ k y := fun y hy =>
    antitone_nat_of_succ_le fun k => hdec k y hy
  have hloc : ∀ S ⊆ U, IsCompact S → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k, ∫⁻ z in S, ‖F k z‖ₑ ^ 2 ≤ C := by
    intro S hSU hS
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn ((hφ 0).mono hSU)
    obtain ⟨N, hN⟩ := hS.exists_bound_of_continuousOn (hF0.mono hSU)
    refine ⟨ENNReal.ofReal (2 * N ^ 2) * volume S + ENNReal.ofReal (2 * Real.exp M) * A,
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_lt_top.ne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA⟩, fun k => ?_⟩
    calc ∫⁻ z in S, ‖F k z‖ₑ ^ 2
        ≤ ∫⁻ z in S, (ENNReal.ofReal (2 * N ^ 2) + ENNReal.ofReal (2 * Real.exp M) *
            ENNReal.ofReal (‖F0 z - F k z‖ ^ 2 * Real.exp (-φ k z))) := by
          refine setLIntegral_mono' hS.measurableSet fun z hz => ?_
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : φ k z ≤ M :=
            (hanti z (hSU hz) (Nat.zero_le k)).trans ((le_abs_self _).trans (hM z hz))
          have h2 : 1 ≤ Real.exp M * Real.exp (-φ k z) := by
            rw [← Real.exp_add]
            exact Real.one_le_exp (by linarith)
          have h3 : ‖F k z‖ ≤ N + ‖F0 z - F k z‖ := by
            have := norm_sub_le (F0 z) (F0 z - F k z)
            rw [sub_sub_cancel] at this
            linarith [hN z hz]
          have h4 : ‖F k z‖ ^ 2 ≤ (N + ‖F0 z - F k z‖) ^ 2 := by gcongr
          have h5 : ‖F0 z - F k z‖ ^ 2 * 1 ≤
              ‖F0 z - F k z‖ ^ 2 * (Real.exp M * Real.exp (-φ k z)) := by gcongr
          nlinarith [sq_nonneg (N - ‖F0 z - F k z‖)]
      _ ≤ _ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          exact (lintegral_mono_set hSU).trans (hest k)
  obtain ⟨f, hf⟩ := exists_tendstoLocallyUniformlyOn_ultrafilter hF
    (locally_bounded_of_lintegral hU hF hloc) (hyperfilter ℕ)
  have hfd : DifferentiableOn ℂ f U :=
    GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn hU hf (Eventually.of_forall hF)
  have hsel : ∀ j : ℕ, ∃ k, j ≤ k ∧ ∀ y ∈ K j, dist (f y) (F k y) < 1 / ((j : ℝ) + 1) := by
    intro j
    have h1 := Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hf (K j) (hKU j) (hKc j))
      (1 / ((j : ℝ) + 1)) (by positivity)
    have h2 : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), j ≤ k :=
      Nat.hyperfilter_le_atTop (eventually_ge_atTop j)
    exact (h2.and h1).exists
  choose σ hσ hσK using hsel
  have hlim : ∀ y ∈ U, Tendsto (fun j => F (σ j) y) atTop (𝓝 (f y)) := by
    intro y hy
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hK y hy] with j hj
    rw [dist_comm]
    exact (hσK j y hj).le
  have hmeas : ∀ {g : V n → ℂ}, ContinuousOn g U → ∀ m, AEMeasurable
      (fun y => ENNReal.ofReal (‖F0 y - g y‖ ^ 2 * Real.exp (-φ m y))) (volume.restrict U) := by
    intro g hg m
    exact (ContinuousOn.aemeasurable ((((hF0.sub hg).norm).pow 2).mul (hφ m).neg.rexp)
      hU.measurableSet).ennreal_ofReal
  have hm : ∀ m, ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ m y)) ≤ A := by
    intro m
    calc ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ m y))
        = ∫⁻ y in U, liminf (fun j =>
            ENNReal.ofReal (‖F0 y - F (σ j) y‖ ^ 2 * Real.exp (-φ m y))) atTop := by
          refine setLIntegral_congr_fun hU.measurableSet fun y hy => ?_
          refine (Tendsto.liminf_eq ?_).symm
          exact ENNReal.tendsto_ofReal
            (((tendsto_const_nhds.sub (hlim y hy)).norm.pow 2).mul_const _)
      _ ≤ liminf (fun j => ∫⁻ y in U,
            ENNReal.ofReal (‖F0 y - F (σ j) y‖ ^ 2 * Real.exp (-φ m y))) atTop :=
          lintegral_liminf_le' fun j => hmeas (hF _).continuousOn m
      _ ≤ A := by
          refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
          filter_upwards [eventually_ge_atTop m] with j hj
          refine le_trans (setLIntegral_mono' hU.measurableSet fun y hy => ?_) (hest (σ j))
          refine ENNReal.ofReal_le_ofReal ?_
          have := hanti y hy (hj.trans (hσ j))
          gcongr
  refine ⟨f, hfd, ?_⟩
  have e : ∀ y, ENNReal.ofReal (‖F0 y - f y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) =
      ⨆ k, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ k y)) := by
    intro y
    rw [ENNReal.mul_iSup]
    exact iSup_congr fun k => (ENNReal.ofReal_mul (by positivity)).symm
  simp_rw [e]
  rw [lintegral_iSup' (hmeas hfd.continuousOn)]
  · exact iSup_le hm
  · filter_upwards [ae_restrict_mem hU.measurableSet] with y hy a b hab
    refine ENNReal.ofReal_le_ofReal ?_
    have := hanti y hy hab
    gcongr

theorem hormander_limit : ∀ {n : ℕ} {U : Set (V n)}, IsOpen U → ∀ (e : V n → ℝ), ContDiffOn ℝ ∞ e U → (∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re) → (∀ a : ℝ, IsCompact {y | y ∈ U ∧ e y ≤ a}) → ∀ (φ : ℕ → V n → ℝ), (∀ k, ContDiffOn ℝ ∞ (φ k) U) → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → (∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y) → ∀ (F0 : V n → ℂ), ContDiffOn ℝ ∞ F0 U → ∀ (h : V n → ℝ≥0∞), Measurable h → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤ h y * ENNReal.ofReal (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → ∀ A : ℝ≥0∞, (∀ k, ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ k y)) ≤ A) → ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧ ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  intro n U hU e he hel hec φ hφ hφl hdec F0 hF0 h hh hb A hA
  by_cases hAt : A = ⊤
  · exact ⟨0, differentiableOn_const 0, hAt ▸ le_top⟩
  choose F hF hest using fun k => ReciprocityTheory.ChartRestriction.G.AR.Up.HE.hormander_open hU e he hel hec (φ k)
    (hφ k) (hφl k) F0 hF0 h hh (hb k)
  refine exists_limit hU (fun j => {y | y ∈ U ∧ e y ≤ (j : ℝ)}) (fun j => hec j)
    (fun j y hy => hy.1) (fun y hy => ?_) (fun k => (hφ k).continuousOn) hdec hF0.continuousOn hAt
    hF fun k => (hest k).trans (hA k)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (e y)] with j hj
  exact ⟨hy, hj⟩

end GlobalTheory.HormanderLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetTwoCocycleEqCechImageAddCoboundary
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechPoset

namespace CechPosetH2Surjective

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

def wv (w : C2 F) (a b d : (NE κ)ᵒᵖ) : F.obj d :=
  if h : sub a ⊆ sub b ∧ sub b ⊆ sub d then w a b d (homOf h.1) (homOf h.2) else 0

theorem wv_eq (w : C2 F) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) : wv w a b d = w a b d f g := by
  rw [wv, dif_pos ⟨sub_subset f, sub_subset g⟩]
  congr 1 <;> exact Subsingleton.elim _ _

theorem wv_cocycle (w : Z2 F) {a b d e : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) (h : d ⟶ e) :
    mp F h (wv w.1 a b d) + wv w.1 a d e = wv w.1 a b e + wv w.1 b d e := by
  rw [wv_eq _ f g, wv_eq _ (f ≫ g) h, wv_eq _ f (g ≫ h), wv_eq _ g h]
  exact w.2 f g h

abbrev pt (i : κ) : (NE κ)ᵒᵖ := ne {i} (Finset.singleton_nonempty i)

abbrev pa (i j : κ) : (NE κ)ᵒᵖ := ne {i, j} (Finset.insert_nonempty _ _)

def u (w : C2 F) (i j : κ) (x : (NE κ)ᵒᵖ) : F.obj x := wv w (pt i) (pa i j) x - wv w (pt j) (pa i j) x

def V (w : C2 F) (i j k : κ) (x : (NE κ)ᵒᵖ) : F.obj x := u w i j x - u w i k x + u w j k x

theorem pa_subset {i j : κ} {t : (NE κ)ᵒᵖ} (hi : i ∈ sub t) (hj : j ∈ sub t) :
    ({i, j} : Finset κ) ⊆ sub t := by
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl <;> assumption

theorem u_res (w : Z2 F) {i j : κ} {t x : (NE κ)ᵒᵖ} (hi : i ∈ sub t) (hj : j ∈ sub t) (φ : t ⟶ x) :
    u w.1 i j x = mp F φ (u w.1 i j t) + wv w.1 (pt i) t x - wv w.1 (pt j) t x := by
  have e1 := wv_cocycle w (homOf (a := pt i) (b := pa i j) (by simp)) (homOf (a := pa i j) (b := t) (pa_subset hi hj)) φ
  have e2 := wv_cocycle w (homOf (a := pt j) (b := pa i j) (by simp)) (homOf (a := pa i j) (b := t) (pa_subset hi hj)) φ
  simp only [u, map_sub]
  linear_combination -e1 + e2

theorem V_res (w : Z2 F) {i j k : κ} {t x : (NE κ)ᵒᵖ} (hi : i ∈ sub t) (hj : j ∈ sub t) (hk : k ∈ sub t)
    (φ : t ⟶ x) : mp F φ (V w.1 i j k t) = V w.1 i j k x := by
  simp only [V, map_add, map_sub, u_res w hi hj φ, u_res w hi hk φ, u_res w hj hk φ]
  ring

theorem pt_hom (a : (NE κ)ᵒᵖ) : sub (pt (mn a)) ⊆ sub a := Finset.singleton_subset_iff.2 (mn_mem a)

def fc (w : C2 F) : C1 F := fun a b _ => wv w (pt (mn a)) a b - u w (mn a) (mn b) b

theorem posetTwoCocycle_sub_correcting_coboundary (w : Z2 F) {a b d : (NE κ)ᵒᵖ} (φ : a ⟶ b) (ψ : b ⟶ d) :
    w.1 a b d φ ψ - d1 F (fc w.1) a b d φ ψ = V w.1 (mn a) (mn b) (mn d) d := by
  have ha : mn a ∈ sub b := sub_subset φ (mn_mem a)
  have hb : mn b ∈ sub b := mn_mem b
  have hq := pa_subset ha hb
  have c1 := wv_cocycle w (homOf (a := pt (mn a)) (pt_hom a)) φ ψ
  have c3 := wv_cocycle w (homOf (a := pt (mn a)) (b := pa (mn a) (mn b)) (by simp))
    (homOf (a := pa (mn a) (mn b)) (b := b) hq) ψ
  have c4 := wv_cocycle w (homOf (a := pt (mn b)) (b := pa (mn a) (mn b)) (by simp))
    (homOf (a := pa (mn a) (mn b)) (b := b) hq) ψ
  rw [d1_apply, ← wv_eq w.1 φ ψ]
  simp only [fc, V, u, map_sub]
  linear_combination -c1 + c3 - c4

theorem V_self_left (w : C2 F) (i k : κ) (x : (NE κ)ᵒᵖ) : V w i i k x = 0 := by simp [V, u]

theorem V_self_right (w : C2 F) (i j : κ) (x : (NE κ)ᵒᵖ) : V w i j j x = 0 := by simp [V, u]

def mid3 (t : Finset κ) (h : t.card = 2 + 1) : κ :=
  (t.erase (t.min' (Finset.card_pos.1 (by omega)))).min'
    (Finset.card_pos.1 (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _), h]; omega))

theorem tri {t : Finset κ} {i j k : κ} (e : t = {i, j, k}) (hij : i < j) (hjk : j < k)
    (h : t.card = 2 + 1) (hne : t.Nonempty) :
    t.min' hne = i ∧ mid3 t h = j ∧ t.max' hne = k := by
  subst e
  have hmin : ({i, j, k} : Finset κ).min' hne = i := by
    refine le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ ?_)
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> order
  refine ⟨hmin, ?_, ?_⟩
  · unfold mid3
    have e : ({i, j, k} : Finset κ).erase (({i, j, k} : Finset κ).min' (Finset.card_pos.1 (by omega))) = {j, k} := by
      rw [hmin, Finset.erase_insert (by simp [hij.ne, (hij.trans hjk).ne])]
    have key : ∀ (s : Finset κ) (hs : s.Nonempty), s = {j, k} → s.min' hs = j := by
      intro s hs es; subst es
      refine le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ ?_)
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> order
    exact key _ _ e
  · refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> order

def yc (w : C2 F) : CC F 2 := fun t =>
  -V w (t.1.max' (card_nonempty t)) (mid3 t.1 t.2) (t.1.min' (card_nonempty t)) (ne t.1 (card_nonempty t))

theorem alternatingToOrderedCech_cechTwoCochainOfPoset (w : Z2 F) {a b d : (NE κ)ᵒᵖ} (φ : a ⟶ b) (ψ : b ⟶ d) :
    e2 F (yc w.1) a b d φ ψ = V w.1 (mn a) (mn b) (mn d) d := by
  simp only [e2, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply, yc]
    obtain ⟨h1, h2, h3⟩ := tri (t := ({mn d, mn b, mn a} : Finset κ)) rfl h.1 h.2 (card_three h.1 h.2)
      (Finset.insert_nonempty _ _)
    rw [h1, h2, h3, map_neg, neg_neg]
    have hs := triple_subset φ ψ
    have V' := V_res w (i := mn a) (j := mn b) (k := mn d) (t := ne {mn d, mn b, mn a} (Finset.insert_nonempty _ _))
      (show mn a ∈ ({mn d, mn b, mn a} : Finset κ) by simp) (show mn b ∈ ({mn d, mn b, mn a} : Finset κ) by simp)
      (show mn d ∈ ({mn d, mn b, mn a} : Finset κ) by simp) (homOf hs)
    exact V'
  · have hdb := mn_le_of_hom ψ
    have hba := mn_le_of_hom φ
    rw [LinearMap.zero_apply]
    rcases (not_and_or.1 h) with h' | h'
    · rw [le_antisymm (not_lt.1 h') hdb, V_self_right]
    · rw [le_antisymm (not_lt.1 h') hba, V_self_left]

theorem four {S : Finset κ} (hS : S.card = 2 + 1 + 1) :
    ∃ i0 i1 i2 i3 : κ, i0 < i1 ∧ i1 < i2 ∧ i2 < i3 ∧ S = {i0, i1, i2, i3} := by
  let e := S.orderEmbOfFin hS
  refine ⟨e 0, e 1, e 2, e 3, e.strictMono (by decide), e.strictMono (by decide),
    e.strictMono (by decide), ?_⟩
  ext y
  have hr := Finset.range_orderEmbOfFin S hS
  constructor
  · intro hy
    have : y ∈ Set.range e := by rw [hr]; exact hy
    obtain ⟨k, rfl⟩ := this
    fin_cases k <;> simp
  · intro hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    have mem : ∀ k, e k ∈ S := fun k => by
      have : e k ∈ Set.range e := ⟨k, rfl⟩
      rw [hr] at this; exact this
    rcases hy with rfl | rfl | rfl | rfl <;> exact mem _

theorem yc_term (w : Z2 F) (t : {s : Finset κ // s.card = 2 + 1 + 1}) (x : t.1) {i j k : κ}
    (e : t.1.erase x.1 = {i, j, k}) (hij : i < j) (hjk : j < k) :
    mp F (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx t x))) (b := ne _ (card_nonempty t))
      (Finset.erase_subset x.1 t.1)) (yc w.1 (GlobalTheory.Cube.eraseIdx t x)) =
      -V w.1 k j i (ne t.1 (card_nonempty t)) := by
  obtain ⟨h1, h2, h3⟩ := tri (t := (GlobalTheory.Cube.eraseIdx t x).1) e hij hjk (GlobalTheory.Cube.eraseIdx t x).2
    (card_nonempty (GlobalTheory.Cube.eraseIdx t x))
  simp only [yc]
  rw [h1, h2, h3, map_neg]
  have mem : ∀ y ∈ ({i, j, k} : Finset κ), y ∈ sub (ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx t x))) := by
    intro y hy; show y ∈ t.1.erase x.1; rw [e]; exact hy
  rw [V_res w (mem k (by simp)) (mem j (by simp)) (mem i (by simp))]

theorem erase4 {i0 i1 i2 i3 : κ} (h01 : i0 < i1) (h12 : i1 < i2) (h23 : i2 < i3) :
    ({i0, i1, i2, i3} : Finset κ).erase i0 = {i1, i2, i3} ∧
    ({i0, i1, i2, i3} : Finset κ).erase i1 = {i0, i2, i3} ∧
    ({i0, i1, i2, i3} : Finset κ).erase i2 = {i0, i1, i3} ∧
    ({i0, i1, i2, i3} : Finset κ).erase i3 = {i0, i1, i2} := by
  have := h01.ne; have := h12.ne; have := h23.ne; have := (h01.trans h12).ne; have := (h12.trans h23).ne
  have := (h01.trans (h12.trans h23)).ne
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext y; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    grind

theorem sign4 {i0 i1 i2 i3 : κ} (h01 : i0 < i1) (h12 : i1 < i2) (h23 : i2 < i3) :
    GlobalTheory.cubeSign ({i0, i1, i2, i3} : Finset κ) i0 = 1 ∧ GlobalTheory.cubeSign ({i0, i1, i2, i3} : Finset κ) i1 = -1 ∧
    GlobalTheory.cubeSign ({i0, i1, i2, i3} : Finset κ) i2 = 1 ∧ GlobalTheory.cubeSign ({i0, i1, i2, i3} : Finset κ) i3 = -1 := by
  have h02 := h01.trans h12; have h13 := h12.trans h23; have h03 := h01.trans h13
  simp [GlobalTheory.cubeSign, Finset.filter_insert, h01, h12, h23, h02, h13, h03, not_lt.2 h01.le,
    not_lt.2 h12.le, not_lt.2 h23.le, not_lt.2 h02.le, not_lt.2 h13.le, not_lt.2 h03.le,
    Finset.filter_singleton, h01.ne, h12.ne, h23.ne, h02.ne, h13.ne, h03.ne, lt_irrefl]

theorem δ_yc (w : Z2 F) : δ F 2 (yc w.1) = 0 := by
  funext t
  obtain ⟨S, hS⟩ := t
  obtain ⟨i0, i1, i2, i3, h01, h12, h23, rfl⟩ := four hS
  rw [δ_apply, Pi.zero_apply]
  obtain ⟨e0, e1', e2', e3⟩ := erase4 h01 h12 h23
  obtain ⟨s0, s1, s2, s3⟩ := sign4 h01 h12 h23
  let T : {s : Finset κ // s.card = 2 + 1 + 1} := ⟨{i0, i1, i2, i3}, hS⟩
  let G : κ → F.obj (ne T.1 (card_nonempty T)) := fun y => if h : y ∈ T.1 then
    GlobalTheory.cubeSign T.1 y • mp F (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx T ⟨y, h⟩)))
      (b := ne _ (card_nonempty T)) (Finset.erase_subset y T.1)) (yc w.1 (GlobalTheory.Cube.eraseIdx T ⟨y, h⟩)) else 0
  have hG : ∀ y (h : y ∈ T.1) {i j k : κ}, T.1.erase y = {i, j, k} → i < j → j < k →
      G y = GlobalTheory.cubeSign T.1 y • -V w.1 k j i (ne T.1 (card_nonempty T)) := by
    intro y h i j k e hij hjk
    simp only [G, dif_pos h]
    rw [yc_term w T ⟨y, h⟩ e hij hjk]
  rw [show (∑ i : T.1, _) = ∑ i : T.1, G i from Finset.sum_congr rfl fun i _ => (dif_pos i.2).symm]
  rw [Finset.sum_coe_sort T.1 G]
  have m : ∀ y ∈ ({i0, i1, i2, i3} : Finset κ), y ∈ T.1 := fun _ h => h
  have h02 := h01.trans h12; have h13 := h12.trans h23; have h03 := h01.trans h13
  show ∑ y ∈ ({i0, i1, i2, i3} : Finset κ), G y = 0
  rw [Finset.sum_insert (by simp [h01.ne, h02.ne, h03.ne]), Finset.sum_insert (by simp [h12.ne, h13.ne]),
    Finset.sum_pair h23.ne]
  rw [hG i0 (m _ (by simp)) e0 h12 h23, hG i1 (m _ (by simp)) e1' h02 h23, hG i2 (m _ (by simp)) e2' h01 h13,
    hG i3 (m _ (by simp)) e3 h01 h12]
  simp only [T, s0, s1, s2, s3, V, one_smul, neg_smul]
  abel

end CechPosetH2Surjective

open CechPosetH2Surjective in

theorem posetTwoCocycle_eq_cechImage_add_coboundary : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (w : Z2 F), ∃ y : CC F 2, δ F 2 y = 0 ∧ ∃ f : C1 F, w.1 - e2 F y = d1 F f := by
  intro κ _ R _ F w
  refine ⟨yc w.1, δ_yc w, fc w.1, ?_⟩
  funext a b d φ ψ
  simp only [Pi.sub_apply]
  rw [alternatingToOrderedCech_cechTwoCochainOfPoset w φ ψ, ← posetTwoCocycle_sub_correcting_coboundary w φ ψ]
  ring

end GlobalTheory.CechPoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorValueHighestWeightVectorStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projector_value_highest_weight_vector : GlobalTheory.LeviCut.StepScalar := by
  first | exact @GlobalTheory.LeviCut.StepScalarProof.stepScalar | exact GlobalTheory.LeviCut.StepScalarProof.stepScalar | (intros; apply GlobalTheory.LeviCut.StepScalarProof.stepScalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantEigenProperty
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem lead_valuation_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N : ℕ) (Δ Δ' : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N Δ' → HasOrders C ε N Δ a c → HasOrders C ε N Δ' a c' → ∀ τ, v (c τ) = v (c' τ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ N Δ Δ' a c c' hΔ hΔ' hO hO' τ
  obtain ⟨f, hf, -, hfξ, -⟩ := GlobalTheory.DetInv.theta_tensor_exists p C v O hv ε hε Λ τ
  have hξ0 : xi ε ≠ 0 := (GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε).2.2.2.2.2.1
  have hreg : (inA (xi ε) : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) :=
    GlobalTheory.T.ainf_element_theta_compatible p C v O hv ε hε Λ (xi ε) hξ0
  obtain ⟨y, hy⟩ := GlobalTheory.T.psi_determinant_orders_property p C v O hv ε hε Λ ψ hψ N Δ Δ' a c c' hΔ hΔ' hO hO'
  obtain ⟨y', hy'⟩ := GlobalTheory.T.psi_determinant_orders_property p C v O hv ε hε Λ ψ hψ N Δ' Δ a c' c hΔ' hΔ hO' hO
  obtain ⟨-, -, hL⟩ := hO τ f hf
  obtain ⟨-, -, hL'⟩ := hO' τ f hf
  set F := (algebraMap O C).comp f
  have hL2 : Lead F (inA (xi ε)) (y * Δ) (a τ) (c' τ) := by rw [mul_comm, ← hy]; exact hL'
  have hL2' : Lead F (inA (xi ε)) (y' * Δ') (a τ) (c τ) := by rw [mul_comm, ← hy']; exact hL
  have e1 := GlobalTheory.DetInv.lead_mul_unique _ _ F _ _ _ _ _ _ hreg hL hL2
  have e2 := GlobalTheory.DetInv.lead_mul_unique _ _ F _ _ _ _ _ _ hreg hL' hL2'
  have b1 : v (F y) ≤ 1 := hv.map_le_one (f y)
  have b2 : v (F y') ≤ 1 := hv.map_le_one (f y')
  apply le_antisymm
  · rw [e2, map_mul]; exact mul_le_of_le_one_left' b2
  · rw [e1, map_mul]; exact mul_le_of_le_one_left' b1

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClosedFormClassStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_closed_form_class : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (hc : Closed1 (OAff s) = ⊤) (hc' : Closed1 (OAff s') = ⊤) (w : GlobForm s), pullHH1 h (clAll (OAff s) hc w) = clAll (OAff s') hc' (GlobalTheory.CechDR.pullForm h w) := by
  first | exact @GlobalTheory.AbCoh.pullHH1_clAll | exact GlobalTheory.AbCoh.pullHH1_clAll | (intros; apply GlobalTheory.AbCoh.pullHH1_clAll <;> assumption)
end

