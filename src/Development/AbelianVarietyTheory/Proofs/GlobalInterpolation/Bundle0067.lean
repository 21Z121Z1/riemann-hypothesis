import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0062
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibreIntegralPiProdEqProdFibreIntegral
section
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Set Topology
open scoped ENNReal

namespace GlobalTheory.FibreProd

theorem le_of_lintegral_ball_eq {X : Type} [PseudoMetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (G H : X → ℝ≥0∞) (b : X) (hG : ContinuousAt G b) (hH : ContinuousAt H b)
    (h : ∀ r > 0, ∫⁻ x in Metric.ball b r, G x ∂ν = ∫⁻ x in Metric.ball b r, H x ∂ν) :
    H b ≤ G b := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  obtain ⟨d, hd1, hd2⟩ := exists_between hc2
  have e : ∀ᶠ x in 𝓝 b, G x < c ∧ d < H x :=
    (hG.eventually (gt_mem_nhds hc1)).and (hH.eventually (lt_mem_nhds hd2))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 e
  have h1 : ∫⁻ x in Metric.ball b r, G x ∂ν ≤ c * ν (Metric.ball b r) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).1.le
  have h2 : d * ν (Metric.ball b r) ≤ ∫⁻ x in Metric.ball b r, H x ∂ν := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).2.le
  have h3 : c * ν (Metric.ball b r) < d * ν (Metric.ball b r) :=
    ENNReal.mul_lt_mul_left (Metric.measure_ball_pos ν b hr).ne' measure_ball_lt_top.ne hd1
  exact absurd (h2.trans ((h r hr).symm.le.trans h1)) h3.not_ge

theorem lintegral_preimage {V X : Type} [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X}
    {f : V → X} {U : Set V} {B : Set X} {fib : X → Measure V}
    (hf : Measurable f) (hU : IsOpen U) (h : IsFibreFamily μ f id U ν B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ U → φ v = 0)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))
  have e1 : ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ v in U, (f ⁻¹' S).indicator φ v ∂μ := by
    rw [← lintegral_indicator hU.measurableSet]
    congr 1
    funext v
    by_cases hv : v ∈ U
    · rw [indicator_of_mem hv]
    · rw [indicator_of_notMem hv]
      exact indicator_apply_eq_zero.2 fun _ => hs v hv
  rw [e1, h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb : ∀ᵐ v ∂(fib b), f v = b := by
    have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ U := h.1 b
    filter_upwards [this] with v hv using hv.1
  by_cases hbS : b ∈ S
  · rw [indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_mem (by simpa [hv] using hbS) _
  · rw [indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_notMem (by simpa [hv] using hbS) _

theorem lintegral_fibre_prod : ∀ (T V : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ₀ : Measure V) [SigmaFinite μ₀] (q : V → ℝ), Continuous q → ∀ U : Set V, IsOpen U → ∀ fib : ℝ → Measure V, IsFibreFamily μ₀ q id U (volume : Measure ℝ) Set.univ fib → ∀ B : Set (T → ℝ), IsOpen B → ∀ Fib : (T → ℝ) → Measure (T → V), IsFibreFamily (Measure.pi fun _ : T => μ₀) (fun x ρ => q (x ρ)) id Set.univ (volume : Measure (T → ℝ)) B Fib → ∀ b ∈ B, ∀ φ : T → V → ℝ, (∀ ρ, Continuous (φ ρ) ∧ HasCompactSupport (φ ρ) ∧ tsupport (φ ρ) ⊆ U ∧ ∀ y, 0 ≤ φ ρ y) → ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b) = ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
  intro T V _ _ _ _ _ _ μ₀ _ q hq U hU fib hfib B hB Fib hFib b hb φ hφ
  classical
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  have hΦc : Continuous fun x : T → V => ∏ ρ, φ ρ (x ρ) :=
    continuous_finset_prod _ fun ρ _ => (hφ ρ).1.comp (continuous_apply ρ)
  have hΦs : HasCompactSupport fun x : T → V => ∏ ρ, φ ρ (x ρ) := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun ρ => (hφ ρ).2.1) fun x hx => ?_
    rw [mem_univ_pi, not_forall] at hx
    obtain ⟨ρ, hρ⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ ρ) (image_eq_zero_of_notMem_tsupport hρ)
  obtain ⟨hI, hC⟩ := hFib.2.2 _ hΦc hΦs (subset_univ _)
  have hm : ∀ ρ, Measurable fun y => ENNReal.ofReal (φ ρ y) := fun ρ =>
    ENNReal.measurable_ofReal.comp (hφ ρ).1.measurable
  have hGc : ContinuousOn (fun b => ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b)) B := by
    refine (ENNReal.continuous_ofReal.comp_continuousOn hC).congr fun b hb => ?_
    have := ofReal_integral_eq_lintegral_ofReal (hI b hb)
      (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun ρ _ => (hφ ρ).2.2.2 _)
    simp only [Function.comp_apply]
    rw [this]
    congr 1
    funext x
    rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => (hφ ρ).2.2.2 _]
  have hg : ∀ ρ t, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) = ENNReal.ofReal (∫ y, φ ρ y ∂(fib t)) :=
    fun ρ t => (ofReal_integral_eq_lintegral_ofReal
      ((hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).1 t (mem_univ _))
      (Filter.Eventually.of_forall (hφ ρ).2.2.2)).symm
  have hgc : ∀ ρ, Continuous fun t => ∫ y, φ ρ y ∂(fib t) := fun ρ =>
    continuousOn_univ.1 (hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).2
  have hgm : ∀ ρ, Measurable fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) := fun ρ => by
    simp only [hg]
    exact ENNReal.measurable_ofReal.comp (hgc ρ).measurable
  have hHc : Continuous fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
    have : (fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ))) =
        fun b => ENNReal.ofReal (∏ ρ, ∫ y, φ ρ y ∂(fib (b ρ))) := by
      funext b
      rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => integral_nonneg (hφ ρ).2.2.2]
      simp only [hg]
    rw [this]
    exact ENNReal.continuous_ofReal.comp
      (continuous_finset_prod _ fun ρ _ => (hgc ρ).comp (continuous_apply ρ))
  have key : ∀ r > 0, ∫⁻ c in Metric.ball b r, ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib c) =
      ∫⁻ c in Metric.ball b r, ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ)) := by
    intro r hr
    have hQ : Measurable fun (x : T → V) ρ => q (x ρ) :=
      (continuous_pi fun ρ => hq.comp (continuous_apply ρ)).measurable
    rw [← lintegral_preimage hQ isOpen_univ hFib (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)))
      (Finset.measurable_prod _ fun ρ _ => (hm ρ).comp (measurable_pi_apply ρ))
      (fun v hv => absurd (mem_univ v) hv) _ measurableSet_ball,
      ← lintegral_indicator measurableSet_ball, ball_pi b hr]
    have e1 : ∀ x : T → V, ((fun (x : T → V) ρ => q (x ρ)) ⁻¹'
        (Set.pi univ fun ρ => Metric.ball (b ρ) r)).indicator
        (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ))) x =
        ∏ ρ, (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)) (x ρ) := by
      intro x
      by_cases hx : ∀ ρ, x ρ ∈ q ⁻¹' Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    have e2 : ∀ c : T → ℝ, (Set.pi univ fun ρ => Metric.ball (b ρ) r).indicator
        (fun c => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ))) c =
        ∏ ρ, (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)) (c ρ) := by
      intro c
      by_cases hx : ∀ ρ, c ρ ∈ Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    simp only [e1, e2]
    rw [volume_pi, GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)))
        (fun ρ => (hm ρ).indicator (hq.measurable measurableSet_ball)),
      GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)))
        (fun ρ => (hgm ρ).indicator measurableSet_ball)]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [lintegral_indicator (s := Metric.ball (b ρ) r) measurableSet_ball]
    refine lintegral_preimage hq.measurable hU hfib _ (hm ρ) (fun v hv => ?_) _ measurableSet_ball
    rw [image_eq_zero_of_notMem_tsupport fun h => hv ((hφ ρ).2.2.1 h), ENNReal.ofReal_zero]
  have hGb := hGc.continuousAt (hB.mem_nhds hb)
  exact le_antisymm
    (le_of_lintegral_ball_eq volume _ _ b hHc.continuousAt hGb fun r hr => (key r hr).symm)
    (le_of_lintegral_ball_eq volume _ _ b hGb hHc.continuousAt key)

end GlobalTheory.FibreProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem goodTopCount_le_const_mul_log (r : ℕ) (de h x : ℝ) (hde : 0 < de) (hde1 : de ≤ 1)
    (hh : 0 ≤ h) (hL : 1 ≤ Real.log x) :
    (G.orbitWindowCount r de h x : ℝ) ≤
      (6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2) * Real.log x := by
  set L := Real.log x with hLdef
  have hu : (G.goodU de : ℝ) * de ≤ 2 := by
    unfold G.goodU
    have h1 : (⌈1 / de⌉₊ : ℝ) < 1 / de + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (⌈1 / de⌉₊ : ℝ) * de ≤ (1 / de + 1) * de := mul_le_mul_of_nonneg_right h1.le hde.le
    have h3 : (1 / de + 1) * de = 1 + de := by field_simp
    linarith
  have hT : (0 : ℝ) < 10 ^ (6 * r + 1) := by positivity
  have hM : (G.orbitSmallMultiplicity r h x : ℝ) + 5 ≤ ((h + 3) * 10 ^ (6 * r + 1) + 6) * L := by
    unfold G.orbitSmallMultiplicity
    have he : (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) =
        (h + 3) * 10 ^ (6 * r + 1) * L := by
      rw [zpow_neg, zpow_natCast, div_inv_eq_mul]; ring
    rw [he]
    have h1 : (⌈(h + 3) * 10 ^ (6 * r + 1) * L⌉₊ : ℝ) < (h + 3) * 10 ^ (6 * r + 1) * L + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    nlinarith
  have hG : (G.goodG' r de h x : ℝ) * de ≤
      (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) * L := by
    unfold G.goodG' G.goodEll
    have he : (((G.orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * G.goodU de) : ℕ) : ℝ) * de =
        ((G.orbitSmallMultiplicity r h x : ℝ) + 5) * (((6 * r + 1 : ℕ) : ℝ) * ((G.goodU de : ℝ) * de)) := by
      push_cast; ring
    rw [he]
    calc _ ≤ (((h + 3) * 10 ^ (6 * r + 1) + 6) * L) * (((6 * r + 1 : ℕ) : ℝ) * 2) := by
          apply mul_le_mul hM (mul_le_mul_of_nonneg_left hu (by positivity)) (by positivity)
          positivity
      _ = _ := by ring
  have hb : (h + 3) * Real.logb 2 x ≤ (h + 3) * 2 * L := by
    have h2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have : Real.logb 2 x ≤ 2 * L := by
      unfold Real.logb
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (by linarith)
  unfold G.orbitWindowCount
  set A := ((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hE : 0 < 6 * Real.exp 1 := by positivity
  have h1 : 6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de ≤ 6 * Real.exp 1 * A * L := by
    rw [mul_assoc (6 * Real.exp 1), mul_assoc (6 * Real.exp 1)]
    exact mul_le_mul_of_nonneg_left hG hE.le
  have h1' : 0 ≤ 6 * Real.exp 1 * A * L := by positivity
  have h2' : 0 ≤ (h + 3) * 2 * L := by positivity
  have hmax : max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x) ≤
      6 * Real.exp 1 * A * L + (h + 3) * 2 * L := max_le (by linarith) (by linarith)
  have hc := Nat.ceil_lt_add_one (a := max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de)
    ((h + 3) * Real.logb 2 x)) (le_max_of_le_left (by positivity))
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem topCount_and_lambda_bounds : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ CN x0 : ℝ, ∀ s : Scale,
    s.eps = eps → x0 ≤ s.x → 1 ≤ G.N1 s ∧ (G.N1 s : ℝ) ≤ CN * Real.log s.x ∧
      ∀ K : G.Consts, 1 ≤ K.La → s.x ^ s.eps ≤ G.La K s ∧
        G.La K s ≤ K.La * CN ^ 2 * Real.log s.x ^ 2 * (2 * s.x ^ s.eps) := by
  intro eps he _
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.1 ((isLittleO_log_rpow_atTop he).bound one_pos)
  set h : ℝ := 2 + 8 * eps with hh
  set r : ℕ := ⌈8 * (h + 2) / eps⌉₊ + 1 with hr
  refine ⟨6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2, max x1 (Real.exp 1), ?_⟩
  intro s hs hx
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hL : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]; exact le_trans (le_max_right _ _) hx
  have hP : 0 < s.x ^ s.eps := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log s.x ≤ s.x ^ s.eps := by
    have := hx1 s.x (le_trans (le_max_left _ _) hx)
    rw [one_mul, ← hs, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hP.le] at this
    exact this
  have hhG : G.hG s = h := by unfold G.hG; rw [hs]
  have hrG : G.rG s = r := by unfold G.rG G.KG; rw [hhG, hs]
  have hN1 : 1 ≤ G.N1 s := by unfold G.N1 G.orbitWindowCount; exact Nat.le_add_left _ _
  have hN := goodTopCount_le_const_mul_log r s.delta1 h s.x (Real.rpow_pos_of_pos hx0 _)
    (Real.rpow_le_one_of_one_le_of_nonpos s.one_lt_alt.le (by have := s.eps_pos; linarith))
    (by positivity) hL
  have hNe : G.N1 s = G.orbitWindowCount r s.delta1 h s.x := by unfold G.N1; rw [hhG, hrG]
  rw [← hNe] at hN
  generalize 6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2 = CN at hN ⊢
  refine ⟨hN1, hN, fun K hK => ?_⟩
  have ha : Real.log s.a = Real.log s.x + s.x ^ s.eps := by
    unfold Scale.a Scale.b Scale.L
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hN1' : (1 : ℝ) ≤ (G.N1 s : ℝ) := by exact_mod_cast hN1
  have hsq : (1 : ℝ) ≤ (G.N1 s : ℝ) ^ 2 := one_le_pow₀ hN1'
  have hsq' : (G.N1 s : ℝ) ^ 2 ≤ (CN * Real.log s.x) ^ 2 := pow_le_pow_left₀ (by linarith) hN 2
  unfold G.La
  rw [ha]
  constructor
  · have h1 : 1 ≤ K.La * (G.N1 s : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hK hsq
    nlinarith
  · calc K.La * (G.N1 s : ℝ) ^ 2 * (Real.log s.x + s.x ^ s.eps)
        ≤ K.La * (CN * Real.log s.x) ^ 2 * (2 * s.x ^ s.eps) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hsq' (by linarith)) (by linarith) (by linarith)
          have : 0 ≤ K.La := by linarith
          positivity
      _ = _ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransport
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

noncomputable section

namespace GlobalTheory.JetTransport

section Formal

variable {σ : Type} [Fintype σ] [DecidableEq σ] {p : ℕ} [Fact p.Prime]

def factP (n : σ →₀ ℕ) : ℂ_[p] := ∏ i, ((n i).factorial : ℂ_[p])

theorem multiIndexFactorial_zero : (factP (0 : σ →₀ ℕ) : ℂ_[p]) = 1 := by simp [factP]

theorem multiIndexFactorial_add_single (n : σ →₀ ℕ) (k : σ) :
    (factP (n + Finsupp.single k 1) : ℂ_[p]) = factP n * ((n k : ℂ_[p]) + 1) := by
  unfold factP
  have h : ∀ i, (((n + Finsupp.single k 1 : σ →₀ ℕ) i).factorial : ℂ_[p]) =
      ((n i).factorial : ℂ_[p]) * (if i = k then (n k : ℂ_[p]) + 1 else 1) := by
    intro i
    by_cases hi : i = k
    · subst hi
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, if_pos rfl]
      push_cast; ring
    · rw [Finsupp.add_apply, if_neg hi]
      simp [Finsupp.single_apply, Ne.symm hi]
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k]
  simp

theorem coeff_pd (k : σ) (F : MvPowerSeries σ ℂ_[p]) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff n (pd k F) = ((n k : ℂ_[p]) + 1) * MvPowerSeries.coeff (n + Finsupp.single k 1) F := rfl

def cntL (l : List σ) : σ →₀ ℕ := (l.map fun k => Finsupp.single k 1).sum

theorem coeff_foldr_pd (F : MvPowerSeries σ ℂ_[p]) : ∀ (l : List σ) (n : σ →₀ ℕ),
    factP n * MvPowerSeries.coeff n (l.foldr (fun k G => pd k G) F) =
      factP (n + cntL l) * MvPowerSeries.coeff (n + cntL l) F
  | [], n => by simp [cntL]
  | k :: l, n => by
    have hc : cntL (k :: l) = Finsupp.single k 1 + cntL l := by simp [cntL]
    rw [List.foldr_cons, coeff_pd, ← mul_assoc, ← multiIndexFactorial_add_single, coeff_foldr_pd F l, hc, add_assoc]

theorem pd_sum_smul {ι : Type} (s : Finset ι) (a : ι → ℂ_[p]) (P : ι → MvPowerSeries σ ℂ_[p]) (k : σ) :
    pd k (∑ i ∈ s, a i • P i) = ∑ i ∈ s, a i • pd k (P i) := by
  ext n
  simp only [coeff_pd, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem foldr_expand {β : Type} (c : β → σ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) : ∀ (m : ℕ) (y : Fin m → β),
    (List.ofFn y).foldr (fun b G => ∑ k, algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) (c b k) * pd k G) F =
      ∑ f : Fin m → σ, (∏ j, c (y j) (f j)) • (List.ofFn f).foldr (fun k G => pd k G) F
  | 0, y => by simp
  | m + 1, y => by
    rw [List.ofFn_succ, List.foldr_cons, foldr_expand c F m]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => σ)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.smul_def, pd_sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have e : (Fin.consEquiv (fun _ : Fin (m + 1) => σ)) (k, f) = Fin.cons k f := rfl
    rw [e, List.ofFn_cons, List.foldr_cons, Fin.prod_univ_succ, smul_smul]
    simp only [Fin.cons_zero, Fin.cons_succ]

theorem cntL_ofFn {m : ℕ} (f : Fin m → σ) : cntL (List.ofFn f) = ∑ j, Finsupp.single (f j) 1 := by
  simp [cntL, List.map_ofFn, List.sum_ofFn]

end Formal

section Cplx

variable {σ : Type} [Fintype σ]

def cnt {k : ℕ} (f : Fin k → σ) (i : σ) : ℕ := (Finset.univ.filter fun j => f j = i).card

theorem perm_of_cnt {k : ℕ} (f l : Fin k → σ) (h : ∀ i, cnt f i = cnt l i) :
    ∃ e : Equiv.Perm (Fin k), f = l ∘ e := by
  have e : ∀ c, {a // f a = c} ≃ {b // l b = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h c)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map e a).symm

theorem cnt_toList (α : σ →₀ ℕ) (i : σ) :
    cnt (fun j : Fin (Multiset.card α.toMultiset) => α.toMultiset.toList.get ⟨j, by simpa using j.2⟩) i = α i := by
  set l := fun j : Fin (Multiset.card α.toMultiset) => α.toMultiset.toList.get ⟨j, by simpa using j.2⟩
  have hmap : Multiset.map l Finset.univ.val = α.toMultiset := by
    rw [Fin.univ_val_map]
    have : List.ofFn l = α.toMultiset.toList := by
      refine List.ext_get (by simp) ?_
      intro n h1 h2
      simp [l]
    rw [this, Multiset.coe_toList]
  have h := congrArg (Multiset.count i) hmap
  rw [Multiset.count_map, Finsupp.count_toMultiset] at h
  rw [← h]
  unfold cnt
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun j _ => eq_comm

def cntF {m : ℕ} (f : Fin m → σ) : σ →₀ ℕ := ∑ j, Finsupp.single (f j) 1

theorem cntF_apply {m : ℕ} (f : Fin m → σ) (i : σ) : cntF f i = cnt f i := by
  rw [cntF, cnt, Finsupp.finset_sum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : f j = i
  · rw [h, if_pos rfl, Finsupp.single_eq_same]
  · rw [if_neg h, Finsupp.single_apply, if_neg h]

theorem card_cntF {m : ℕ} (f : Fin m → σ) : Multiset.card (cntF f).toMultiset = m := by
  rw [cntF, map_sum, Multiset.card_sum]
  simp

end Cplx

section Main

variable {D : D7} {N N' : ℕ}

theorem vec_eq (v : VC D N N') :
    v = ∑ k : D.what₂.Tau × Fin N' × Fin N, v k.1 k.2.1 k.2.2 • coordV D k := by
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, coordV, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (τ, i, j)]
  · simp
  · rintro ⟨a, b, c⟩ _ hb
    rw [if_neg]
    rintro ⟨rfl, rfl, rfl⟩
    exact hb rfl
  · simp

theorem mlin_expand {m : ℕ} (A : ContinuousMultilinearMap ℂ (fun _ : Fin m => VC D N N') ℂ) (v : Fin m → VC D N N') :
    A v = ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N,
      (∏ j, v j (f j).1 (f j).2.1 (f j).2.2) * A (fun j => coordV D (f j)) := by
  have hv : v = fun j => ∑ k : D.what₂.Tau × Fin N' × Fin N, v j k.1 k.2.1 k.2.2 • coordV D k :=
    funext fun j => vec_eq (v j)
  conv_lhs => rw [hv]
  rw [A.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [A.map_smul_univ, smul_eq_mul]

theorem iFD_coord (G : VC D N N' → ℂ) (hG : ContDiff ℂ ⊤ G) {m : ℕ} (f : Fin m → D.what₂.Tau × Fin N' × Fin N) :
    iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) =
      (∏ i, ((cntF f i).factorial : ℂ)) * taylor D G (cntF f) := by
  have key : ∀ (k : ℕ) (hk : k = m) (l : Fin k → D.what₂.Tau × Fin N' × Fin N), (∀ i, cnt l i = cntF f i) →
      iteratedFDeriv ℂ k G 0 (fun j => coordV D (l j)) = iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) := by
    rintro k rfl l hl
    obtain ⟨e, he⟩ := perm_of_cnt f l (fun i => by rw [hl, cntF_apply])
    rw [he]
    exact (hG.contDiffAt.iteratedFDeriv_comp_perm (fun j => coordV D (l j)) e).symm
  have e1 : iteratedFDeriv ℂ (Multiset.card (cntF f).toMultiset) G 0
      (fun i => coordV D ((cntF f).toMultiset.toList.get ⟨i, by simpa using i.2⟩)) =
      iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) :=
    key _ (card_cntF f) _ (cnt_toList (cntF f))
  have h0 : ((cntF f).prod fun _ n => (n.factorial : ℂ)) = ∏ i, ((cntF f i).factorial : ℂ) :=
    Finsupp.prod_fintype _ _ (by simp)
  have hne : (∏ i, ((cntF f i).factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  unfold taylor
  rw [e1, h0, mul_div_cancel₀ _ hne]

theorem embT_mem (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)

theorem lam_mk {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : ℂ) (h : a ∈ Qbar) :
    lam ⟨a, h⟩ = lamC lam a := by
  unfold lamC; rw [dif_pos h]

end Main

end GlobalTheory.JetTransport

namespace GlobalTheory.JetTransport

theorem jet_pSer : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (G : VC D N N' → ℂ), ContDiff ℂ ⊤ G → CoefIn D G Qbar → ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E), iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) ∈ Qbar ∧ jet D lam y (pSer D lam G) = lamC lam (iteratedFDeriv ℂ m G 0 fun j => embV D (tor0 D cc δ) (y j)) := by
  intro D cc δ p _ lam N N' G hG hco m y
  have hC : iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) =
      ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N, (∏ j, embT D (f j).1 (y j (f j).2.1 (f j).2.2)) *
        ((∏ i, ((cntF f i).factorial : ℂ)) * taylor D G (cntF f)) := by
    rw [mlin_expand]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [iFD_coord G hG f]
    rfl
  have hP : jet D lam y (pSer D lam G) =
      ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N, (∏ j, lamC lam (embT D (f j).1 (y j (f j).2.1 (f j).2.2))) *
        ((∏ i, ((cntF f i).factorial : ℂ_[p])) * lamC lam (taylor D G (cntF f))) := by
    unfold jet
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hx := foldr_expand (fun (b : Matrix (Fin N') (Fin N) D.host.E) (k : D.what₂.Tau × Fin N' × Fin N) =>
      lamC lam (embT D k.1 (b k.2.1 k.2.2))) (pSer D lam G) m y
    erw [hx, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_smul, smul_eq_mul]
    congr 1
    have h := coeff_foldr_pd (pSer D lam G) (List.ofFn f) 0
    rw [zero_add, cntL_ofFn, multiIndexFactorial_zero, one_mul] at h
    rw [h]
    rfl
  set z : Qbar := ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N,
    (∏ j, (⟨embT D (f j).1 (y j (f j).2.1 (f j).2.2), embT_mem _ _⟩ : Qbar)) *
      ((∏ i, ((cntF f i).factorial : Qbar)) * ⟨taylor D G (cntF f), hco _⟩) with hzdef
  have hz : (z : ℂ) = iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) := by
    rw [hC, hzdef, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_prod, IntermediateField.coe_prod]
    simp
  have hl : lam z = jet D lam y (pSer D lam G) := by
    rw [hP, hzdef, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [map_mul, map_prod, map_natCast, lam_mk]
  refine ⟨hz ▸ z.2, ?_⟩
  rw [← hz, ← hl]
  exact lam_mk lam _ z.2

end GlobalTheory.JetTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParahoricLeIntegralGlStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_le_integral_gl : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  first | exact @GlobalTheory.Proof.parahoric_le_integral_gl.prCat_le_GLint | exact GlobalTheory.Proof.parahoric_le_integral_gl.prCat_le_GLint | (intros; apply GlobalTheory.Proof.parahoric_le_integral_gl.prCat_le_GLint <;> assumption)
end

