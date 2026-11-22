import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AeEqOfDenseOfLocalSqBoundStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_eq_of_dense_of_local_sq_bound_alt : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Set H), Dense D → ∀ P Q : H → X → E,
    (∀ u u', (fun x => P u x - P u' x) =ᵐ[μ] P (u - u')) →
    (∀ u u', (fun x => Q u x - Q u' x) =ᵐ[μ] Q (u - u')) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (P u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖P u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (Q u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖Q u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ u ∈ D, P u =ᵐ[μ] Q u) → ∀ u, P u =ᵐ[μ] Q u := by
  first | exact @GlobalTheory.ae_eq_of_dense_of_local_sq_bound | exact GlobalTheory.ae_eq_of_dense_of_local_sq_bound | (intros; apply GlobalTheory.ae_eq_of_dense_of_local_sq_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianMatricesDvdSq
section
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem card_hermitian_dvd_sq {A : Type} [CommRing A] [Finite A] (c : A →+* A)
    (hc : ∀ u, c (c u) = u) (ω : A) (hω : IsUnit (ω - c ω)) (p : A) (hp : c p = p) (m : ℕ) :
    Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ^ 2
      = Nat.card {u : A // p ∣ u} ^ (m * m) := by
  have hmem : ∀ u : A, u ∈ Ideal.span {p} → c u ∈ Ideal.span {p} := by
    intro u hu
    rw [Ideal.mem_span_singleton] at hu ⊢
    have := map_dvd c hu
    rwa [hp] at this
  let σ : (Fin m → Fin m → Ideal.span {p}) →+ (Fin m → Fin m → Ideal.span {p}) :=
    { toFun := fun H a b => ⟨c (H b a).1, hmem _ (H b a).2⟩
      map_zero' := by
        funext a b
        exact Subtype.ext (by simp)
      map_add' := fun H K => by
        funext a b
        exact Subtype.ext (by simp) }
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    funext a b
    exact Subtype.ext (hc _)
  have hs : ∀ (r : A) x, σ (r • x) = c r • σ x := fun r x => by
    funext a b
    exact Subtype.ext (map_mul c r _)
  have h := (card_fixed_sq c hc hω σ hσ hs).1
  let e : {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ≃
      {x : Fin m → Fin m → Ideal.span {p} // σ x = x} :=
    { toFun := fun H => ⟨fun a b => ⟨H.1 a b, Ideal.mem_span_singleton.2 (H.2.2 a b)⟩, by
        funext a b
        exact Subtype.ext (H.2.1 a b)⟩
      invFun := fun x => ⟨fun a b => (x.1 a b).1,
        fun a b => congrArg Subtype.val (congrFun (congrFun x.2 a) b),
        fun a b => Ideal.mem_span_singleton.1 (x.1 a b).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : {u : A // p ∣ u} ≃ Ideal.span {p} :=
    Equiv.subtypeEquivRight fun u => Ideal.mem_span_singleton.symm
  rw [Nat.card_congr e, h, Nat.card_congr e2, Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp

end GlobalTheory.GramCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberLeMinkowskiCount
section
open NumberField

namespace GlobalTheory

theorem classNumber_le_minkowski_count :
    ∀ (K : Type) [Field K] [NumberField K], (classNumber K : ℝ) ≤
      Real.sqrt |(discr K : ℝ)| * (1 + Real.log (Real.sqrt |(discr K : ℝ)|)) ^ Module.finrank ℚ K :=
  fun K _ _ => classNumber_le_sqrt_discr_mul_pow K

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAtZeroOfSqueezePowBounds
section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory

theorem squeeze_continuousAt_zero (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ)
    (f : V → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η →
      ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) :
    f 0 = c ∧ ContinuousAt f 0 := by
  have h1 : Tendsto (fun ε : ℝ => (1 + ε)⁻¹ ^ d) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun ε : ℝ => (1 + ε)⁻¹ ^ d) 0 :=
      ((continuous_const.add continuous_id).continuousAt.inv₀ (by norm_num)).pow d
    simpa using this.tendsto
  have h2 : Tendsto (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ d) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ d) 0 :=
      ((continuous_const.add continuous_id).continuousAt.div
        (continuous_const.sub continuous_id).continuousAt (by norm_num)).pow d
    simpa using this.tendsto
  have hL : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c) (𝓝 0) (𝓝 c) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hc)
    simpa using this
  have hU : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) (𝓝 0) (𝓝 c) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h2) (Or.inr hc)
    simpa using this
  have hI : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  have hf : Tendsto f (𝓝 0) (𝓝 c) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a < ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c :=
        nhdsWithin_le_nhds (hL.eventually (lt_mem_nhds ha))
      obtain ⟨ε, hε, hεI⟩ := (e1.and hI).exists
      obtain ⟨η, hη, hx⟩ := h ε hεI.1 hεI.2
      filter_upwards [Metric.ball_mem_nhds (0 : V) hη] with x hxb
      rw [mem_ball_zero_iff] at hxb
      exact lt_of_lt_of_le hε (hx x hxb).1
    · intro a ha
      have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c < a :=
        nhdsWithin_le_nhds (hU.eventually (gt_mem_nhds ha))
      obtain ⟨ε, hε, hεI⟩ := (e1.and hI).exists
      obtain ⟨η, hη, hx⟩ := h ε hεI.1 hεI.2
      filter_upwards [Metric.ball_mem_nhds (0 : V) hη] with x hxb
      rw [mem_ball_zero_iff] at hxb
      exact lt_of_le_of_lt (hx x hxb).2 hε
  have h0 : f 0 = c := tendsto_nhds_unique (tendsto_pure_nhds f 0) (hf.mono_left (pure_le_nhds 0))
  refine ⟨h0, ?_⟩
  unfold ContinuousAt
  rw [h0]
  exact hf

example : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (f : V → ℝ≥0∞) (c : ℝ≥0∞), c ≠ ⊤ → (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) → f 0 = c ∧ ContinuousAt f 0 :=
  squeeze_continuousAt_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqZeroOfExpDecayOfFourierEqZeroOnHalfLine
section
open MeasureTheory Filter Set
open scoped Topology FourierTransform

namespace GlobalTheory

theorem integrable_exp_neg_mul_abs_line {c : ℝ} (hc : 0 < c) :
    Integrable (fun s : ℝ => Real.exp (-(c * |s|))) := by
  first
  | exact @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | (apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs ..)

theorem eq_zero_of_exp_decay_of_fourier_eq_zero_on_halfLine :
    ∀ (φ : ℝ → ℂ) (R : ℝ), Continuous φ →
      (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) →
      (∀ ξ : ℝ, R ≤ ξ → ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s = 0) → φ = 0 := by
  rintro φ R hφ ⟨A, e, he, hb⟩ hz
  set U : Set ℂ := {z | -(e / 2) < z.im} ∩ {z | z.im < e / 2} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hUc : Convex ℝ U := (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)
  have hre : ∀ x : ℝ, (x : ℂ) ∈ U := fun x => by
    simp only [hUdef, mem_inter_iff, mem_setOf_eq, Complex.ofReal_im]
    constructor <;> linarith
  have hint : Integrable (fun s : ℝ => A * Real.exp (-(e / 2 * |s|))) :=
    (integrable_exp_neg_mul_abs_line (half_pos he)).const_mul A
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hb 0)
    simpa using this
  have hbound : ∀ s : ℝ, ∀ y ∈ U,
      ‖Complex.exp (-(Complex.I * y * s)) * φ s‖ ≤ A * Real.exp (-(e / 2 * |s|)) := by
    intro s y hy
    have hy' : |y.im| ≤ e / 2 := abs_le.2 ⟨hy.1.le, hy.2.le⟩
    have h1 : (-(Complex.I * y * s)).re = y.im * s := by simp
    have h2 : y.im * s ≤ e / 2 * |s| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hy' (abs_nonneg _)
    rw [norm_mul, Complex.norm_exp, h1]
    calc Real.exp (y.im * s) * ‖φ s‖
        ≤ Real.exp (e / 2 * |s|) * (A * Real.exp (-(e * |s|))) :=
          mul_le_mul (Real.exp_le_exp.2 h2) (hb s) (norm_nonneg _) (Real.exp_pos _).le
      _ = A * Real.exp (-(e / 2 * |s|)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hdiff := (differentiableOn_integral_of_holomorphic_of_locally_dominated
    (μ := (volume : Measure ℝ))
    (F := fun (s : ℝ) (y : ℂ) => Complex.exp (-(Complex.I * y * s)) * φ s) hUo
    (fun y _ => Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun s => Differentiable.differentiableOn (by fun_prop))
    (fun x hx => ⟨U, hUo.mem_nhds hx, _, hint, Eventually.of_forall hbound⟩)).1
  have han := hdiff.analyticOnNhd hUo
  have hfr : ∃ᶠ y in 𝓝[≠] (R : ℂ),
      ∫ s : ℝ, Complex.exp (-(Complex.I * y * s)) * φ s = 0 := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] R) (𝓝[≠] (R : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto R).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using (ne_of_gt hx)
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hz x (le_of_lt hx)
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc.isPreconnected
    (hre R) hfr
  have hF : 𝓕 φ = 0 := by
    funext w
    rw [Real.fourier_real_eq_integral_exp_smul]
    have := hzero (hre (2 * Real.pi * w))
    simp only [Pi.zero_apply] at this ⊢
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [smul_eq_mul]
    congr 2
    push_cast
    ring
  have hφi : Integrable φ :=
    ((integrable_exp_neg_mul_abs_line he).const_mul A).mono' hφ.aestronglyMeasurable
      (Eventually.of_forall hb)
  have hinv := hφ.fourierInv_fourier_eq hφi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  funext x
  simp [Real.fourierInv_eq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDyadicShellIndex
section
open Finset

namespace GlobalTheory

theorem exists_dyadic_shell_index (ep : ℝ) (hep : 0 < ep) :
    ∃ sh : ℝ → ℕ, (∀ s, s ≤ 2 ^ sh s * ep) ∧ ∀ s j, j < sh s → 2 ^ j * ep < s := by
  classical
  have hex : ∀ s : ℝ, ∃ n : ℕ, s ≤ 2 ^ n * ep := by
    intro s
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / ep) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hep] at hn
    exact hn.le
  refine ⟨fun s => Nat.find (hex s), fun s => Nat.find_spec (hex s), fun s j hj => ?_⟩
  exact not_le.mp (Nat.find_min (hex s) hj)

theorem sum_prod_box_erase_zero (ι : Type) [Fintype ι] [DecidableEq ι] (W : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ (Fintype.piFinset (fun _ : ι => range (N + 1))).erase (fun _ => 0), ∏ v, W (k v)
      = (W 0 + ∑ i ∈ range N, W (i + 1)) ^ Fintype.card ι - W 0 ^ Fintype.card ι := by
  classical
  have hz : (fun _ : ι => (0 : ℕ)) ∈ Fintype.piFinset (fun _ : ι => range (N + 1)) := by
    simp [Fintype.mem_piFinset]
  rw [Finset.sum_erase_eq_sub hz,
    ← Finset.prod_univ_sum (fun _ : ι => range (N + 1)) (fun _ j => W j),
    Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.sum_range_succ', add_comm]

theorem sum_over_dyadic_shells :
    ∀ (Γ ι : Type) [Fintype ι] (d : Γ → ι → ℝ) (w : Γ → ℝ) (A κ h ep c : ℝ), 0 ≤ A → 0 ≤ κ → 0 < ep → 0 < c → ep ≤ 1 / c → κ * ep ≤ Real.log 2 → 32 * κ ≤ h * ep → 1 ≤ h * ep ^ 2 / 16 → (∀ γ v, 0 ≤ d γ v) → (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) → {γ | ∀ v, d γ v ≤ r v}.Finite ∧ (({γ | ∀ v, d γ v ≤ r v}.ncard : ℕ) : ℝ) ≤ A * Real.exp (κ * ∑ v, r v)) → (∀ γ, ∃ v, ep < d γ v) → (∀ γ, 0 ≤ w γ ∧ w γ ≤ ∏ v, Real.exp (-(h / 8) * min (d γ v ^ 2) (d γ v / c))) → Summable w ∧ ∑' γ, w γ ≤ A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
  intro Γ ι _ d w A κ h ep c hA hκ hep hc hepc hκep hh hT hd hcount hfar hw
  classical
  obtain ⟨sh, hsh1, hsh2⟩ := exists_dyadic_shell_index ep hep
  obtain ⟨hineq, -, hpow⟩ := shell_sum_elementary_inequalities
  set T : ℝ := h * ep ^ 2 / 16 with hTdef
  have hhpos : 0 < h := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have h1 : h * ep ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg ep)
    linarith
  have hκT : κ * ep ≤ T / 2 := by
    have h1 : 32 * κ * ep ≤ h * ep * ep := mul_le_mul_of_nonneg_right hh hep.le
    rw [hTdef]
    nlinarith

  let F : ℕ → ℝ := fun j => if j = 0 then 1 else Real.exp (-T * 2 ^ j)
  let W : ℕ → ℝ := fun j => Real.exp (κ * (2 ^ j * ep)) * F j
  let K : Γ → ι → ℕ := fun γ v => sh (d γ v)
  have hF0 : ∀ j, 0 ≤ F j := by
    intro j
    simp only [F]
    split_ifs
    · exact zero_le_one
    · exact (Real.exp_pos _).le
  have hW0 : ∀ j, 0 ≤ W j := fun j => mul_nonneg (Real.exp_pos _).le (hF0 j)

  have hwF : ∀ γ, w γ ≤ ∏ v, F (K γ v) := by
    intro γ
    refine (hw γ).2.trans (Finset.prod_le_prod (fun v _ => (Real.exp_pos _).le) (fun v _ => ?_))
    have hmin0 : 0 ≤ min (d γ v ^ 2) (d γ v / c) := le_min (sq_nonneg _) (div_nonneg (hd γ v) hc.le)
    simp only [F, K]
    split_ifs with hk
    · rw [Real.exp_le_one_iff]
      nlinarith
    · rw [Real.exp_le_exp]
      have hlt : sh (d γ v) - 1 < sh (d γ v) := Nat.sub_lt (Nat.pos_of_ne_zero hk) one_pos
      have hbig := hsh2 (d γ v) _ hlt
      have hp1 : (1 : ℝ) ≤ 2 ^ (sh (d γ v) - 1) := one_le_pow₀ (by norm_num)
      have hge : ep ≤ d γ v := by nlinarith
      have hm := hineq (d γ v) ep c hep hge hc hepc
      have h2 : (2 : ℝ) ^ sh (d γ v) = 2 * 2 ^ (sh (d γ v) - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hm2 : ep ^ 2 * 2 ^ (sh (d γ v) - 1) ≤ min (d γ v ^ 2) (d γ v / c) := by
        have : ep * (2 ^ (sh (d γ v) - 1) * ep) ≤ ep * d γ v :=
          mul_le_mul_of_nonneg_left hbig.le hep.le
        nlinarith
      have hm3 := mul_le_mul_of_nonneg_left hm2 hhpos.le
      rw [h2, hTdef]
      nlinarith

  have hfib : ∀ (u : Finset Γ) (k : ι → ℕ),
      ((u.filter fun γ => K γ = k).card : ℝ) ≤ A * ∏ v, Real.exp (κ * (2 ^ k v * ep)) := by
    intro u k
    have hr : ∀ v, 0 ≤ (2 : ℝ) ^ k v * ep := fun v => mul_nonneg (pow_nonneg (by norm_num) _) hep.le
    obtain ⟨hfin, hcard⟩ := hcount (fun v => 2 ^ k v * ep) hr
    have hsub : ((u.filter fun γ => K γ = k : Finset Γ) : Set Γ) ⊆ {γ | ∀ v, d γ v ≤ 2 ^ k v * ep} := by
      intro γ hγ
      have hγ' := Finset.mem_filter.mp (Finset.mem_coe.mp hγ)
      intro v
      have := hsh1 (d γ v)
      rw [← hγ'.2]
      exact this
    have hle := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at hle
    calc ((u.filter fun γ => K γ = k).card : ℝ)
        ≤ (({γ | ∀ v, d γ v ≤ 2 ^ k v * ep}.ncard : ℕ) : ℝ) := by exact_mod_cast hle
      _ ≤ A * Real.exp (κ * ∑ v, 2 ^ k v * ep) := hcard
      _ = A * ∏ v, Real.exp (κ * (2 ^ k v * ep)) := by
        rw [Finset.mul_sum, Real.exp_sum]

  have hpart : ∀ u : Finset Γ, ∑ γ ∈ u, w γ
      ≤ A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
    intro u
    set N : ℕ := u.sup fun γ => Finset.univ.sup (K γ) with hN
    set B := (Fintype.piFinset fun _ : ι => range (N + 1)).erase (fun _ => 0) with hB
    have hmaps : ∀ γ ∈ u, K γ ∈ B := by
      intro γ hγ
      rw [hB, Finset.mem_erase, Fintype.mem_piFinset]
      refine ⟨?_, fun v => ?_⟩
      · intro h0
        obtain ⟨v, hv⟩ := hfar γ
        have h1 : K γ v = 0 := congrFun h0 v
        have h2 := hsh1 (d γ v)
        simp only [K] at h1
        rw [h1, pow_zero, one_mul] at h2
        linarith
      · rw [Finset.mem_range, Nat.lt_succ_iff]
        exact (Finset.le_sup (f := K γ) (Finset.mem_univ v)).trans
          (Finset.le_sup (f := fun γ => Finset.univ.sup (K γ)) hγ)
    have hal0 : 0 ≤ W 0 := hW0 0
    have hal2 : W 0 ≤ 2 := by
      show Real.exp (κ * (2 ^ 0 * ep)) * (if (0 : ℕ) = 0 then 1 else Real.exp (-T * 2 ^ 0)) ≤ 2
      rw [if_pos rfl, pow_zero, one_mul, mul_one]
      calc Real.exp (κ * ep) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hκep
        _ = 2 := Real.exp_log (by norm_num)
    have hT1 : 1 ≤ T := hT
    have hWs : ∀ i, W (i + 1) ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i := by
      intro i
      refine le_trans ?_ (exp_neg_mul_two_pow_le_geometric T hT1 i)
      simp only [W, F, if_neg (Nat.succ_ne_zero i)]
      rw [← Real.exp_add, Real.exp_le_exp, pow_succ]
      have hp : (0 : ℝ) ≤ 2 ^ i := pow_nonneg (by norm_num) _
      nlinarith
    have hexpT : Real.exp (-T) ≤ 1 / 2 := by
      have h1 : Real.exp (-T) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have h2 : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
      have h4 : 0 < Real.exp (-1) := Real.exp_pos _
      nlinarith
    have hbe : ∑ i ∈ range N, W (i + 1) ≤ 2 * Real.exp (-T) := by
      calc ∑ i ∈ range N, W (i + 1) ≤ ∑ i ∈ range N, Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
            Finset.sum_le_sum fun i _ => hWs i
        _ = Real.exp (-T) * ∑ i ∈ range N, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
        _ ≤ Real.exp (-T) * 2 :=
            mul_le_mul_of_nonneg_left (sum_geometric_two_le N) (Real.exp_pos _).le
        _ = 2 * Real.exp (-T) := mul_comm _ _
    have hbe0 : 0 ≤ ∑ i ∈ range N, W (i + 1) := Finset.sum_nonneg fun i _ => hW0 _
    have hbe1 : ∑ i ∈ range N, W (i + 1) ≤ 1 := by linarith
    have hbox := sum_prod_box_erase_zero ι W N
    have key := hpow (W 0) (∑ i ∈ range N, W (i + 1)) (Fintype.card ι) hal0 hal2 hbe0 hbe1
    calc ∑ γ ∈ u, w γ ≤ ∑ γ ∈ u, ∏ v, F (K γ v) := Finset.sum_le_sum fun γ _ => hwF γ
      _ = ∑ k ∈ B, ∑ γ ∈ u with K γ = k, ∏ v, F (k v) :=
          (Finset.sum_fiberwise_of_maps_to' hmaps (fun k => ∏ v, F (k v))).symm
      _ = ∑ k ∈ B, ((u.filter fun γ => K γ = k).card : ℝ) * ∏ v, F (k v) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ B, (A * ∏ v, Real.exp (κ * (2 ^ k v * ep))) * ∏ v, F (k v) :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (hfib u k) (Finset.prod_nonneg fun v _ => hF0 _)
      _ = A * ∑ k ∈ B, ∏ v, W (k v) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_assoc, ← Finset.prod_mul_distrib]
      _ = A * ((W 0 + ∑ i ∈ range N, W (i + 1)) ^ Fintype.card ι - W 0 ^ Fintype.card ι) := by
          rw [hB, hbox]
      _ ≤ A * (Fintype.card ι * (2 * Real.exp (-T)) * 3 ^ Fintype.card ι) := by
          refine mul_le_mul_of_nonneg_left (key.trans ?_) hA
          have h3 : (0 : ℝ) ≤ 3 ^ Fintype.card ι := pow_nonneg (by norm_num) _
          have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbe hn) h3
      _ = A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
          rw [hTdef]
          ring
  have hw0 : 0 ≤ w := fun γ => (hw γ).1
  exact ⟨summable_of_sum_le hw0 hpart, Real.tsum_le_of_sum_le hw0 hpart⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCosetSectionStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_coset_section' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G), IsClosed (L : Set G) → ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  first | exact @GlobalTheory.exists_measurable_coset_section | exact GlobalTheory.exists_measurable_coset_section | (intros; apply GlobalTheory.exists_measurable_coset_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableLintegralCosetEqOneClosedSubgrouStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_lintegral_coset_eq_one_closedSubgroup : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∃ b : G → ENNReal, Measurable b ∧ ∀ g, ∫⁻ h, b (j h * g) ∂ν = 1 := by
  first | exact @GlobalTheory.exists_measurable_lintegral_coset_eq_one | exact GlobalTheory.exists_measurable_lintegral_coset_eq_one | (intros; apply GlobalTheory.exists_measurable_lintegral_coset_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealGeneratorAtPrimesOverStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_fractionalIdeal_generator_at_primes_over' : ∀ (E : Type) [Field E] [NumberField E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ ∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  first | exact @GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over | exact GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over | (intros; apply GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNetCardLeOfSubsetClosedBall
section
open Metric

namespace GlobalTheory

theorem exists_net_card_le_of_subset_closedBall :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (S : Set E)
      (R δ : ℝ), 0 < δ → 0 ≤ R → S ⊆ closedBall 0 R →
      ∃ T : Finset E, (T : Set E) ⊆ S ∧ (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E ∧
        ∀ x ∈ S, ∃ t ∈ T, dist x t ≤ δ := by
  intro E _ _ _ S R δ hδ hR hS
  classical
  let P : Finset E → Prop := fun T =>
    (T : Set E) ⊆ S ∧ (T : Set E).Pairwise fun a b => δ ≤ dist a b
  have hb : ∀ T, P T → (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E := fun T hT =>
    finset_card_le_of_separated T hδ hR 0 (fun a ha => hS (hT.1 ha)) hT.2
  obtain ⟨N, hN⟩ := exists_nat_ge ((1 + 2 * R / δ) ^ Module.finrank ℝ E)
  let Q : ℕ → Prop := fun n => ∃ T, P T ∧ T.card = n
  have hQ0 : Q 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨T, hT, hTc⟩ : Q (Nat.findGreatest Q N) := Nat.findGreatest_spec (Nat.zero_le N) hQ0
  refine ⟨T, hT.1, hb T hT, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have hxT : x ∉ T := fun h => by
    have := hcon x h
    rw [dist_self] at this
    linarith
  have hP : P (insert x T) := by
    refine ⟨?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hx hT.1
    · rw [Finset.coe_insert]
      refine hT.2.insert fun b hb' _ => ⟨(hcon b hb').le, ?_⟩
      rw [dist_comm]
      exact (hcon b hb').le
  have hle : (insert x T).card ≤ N := by
    exact_mod_cast (hb _ hP).trans hN
  have := Nat.le_findGreatest (P := Q) hle ⟨_, hP, rfl⟩
  rw [Finset.card_insert_of_notMem hxT] at this
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryMulVecEqOfFormEqStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_mulVec_eq_of_form_eq' : ∀ (E : Type) [Field E] [CharZero E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Jᴴ = J → J.det ≠ 0 → ∀ x y : Fin n → E, star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y) → star x ⬝ᵥ (J *ᵥ x) ≠ 0 → ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  first | exact @GlobalTheory.exists_unitary_mulVec_eq_of_form_eq | exact GlobalTheory.exists_unitary_mulVec_eq_of_form_eq | (intros; apply GlobalTheory.exists_unitary_mulVec_eq_of_form_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpQuadraticLowerAndLogLinearLowerStatement
section
open Matrix Finset Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_quadratic_lower_and_log_linear_lower' : (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) := by
  first | exact @GlobalTheory.exp_quadratic_lower_and_log_linear_lower | exact GlobalTheory.exp_quadratic_lower_and_log_linear_lower | (intros; apply GlobalTheory.exp_quadratic_lower_and_log_linear_lower <;> assumption)
end

