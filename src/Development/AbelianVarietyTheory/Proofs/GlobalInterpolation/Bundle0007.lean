import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormSubOneMulRiemannZetaLe
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology

namespace GlobalTheory.ZetaLeft

noncomputable def emT (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (1 - s) - (1 - s) * (x : ℂ) ^ (1 - s - 1) / 2
    + (1 - s) * (1 - s - 1) * (x : ℂ) ^ (1 - s - 1 - 1) / 12

noncomputable def emE (x : ℝ) (s : ℂ) : ℂ :=
  emT (x + 1) s - emT x s - (1 - s) * (x : ℂ) ^ (1 - s - 1)

lemma hasDerivAt_shift_cpow {a t : ℝ} (h : 0 < a + t) (c : ℂ) :
    HasDerivAt (fun z : ℂ => ((a : ℂ) + z) ^ c) (c * ((a : ℂ) + t) ^ (c - 1)) (t : ℂ) := by
  have h1 : HasDerivAt (fun z : ℂ => (a : ℂ) + z) 1 (t : ℂ) := (hasDerivAt_id _).const_add _
  have h2 : ((a : ℂ) + t) ∈ slitPlane := by
    left; simpa using h
  simpa using h1.cpow_const (c := c) h2

lemma norm_emE_le {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : -(15/8 : ℝ) ≤ s.re) :
    ‖emE a s‖ ≤ (‖s‖ + 2) ^ 4 * a ^ (-(9/8 : ℝ)) := by
  set w : ℂ := 1 - s with hw
  let G : ℂ → ℂ := fun z => ((a : ℂ) + z) ^ w - (z - 1/2) * (w * ((a : ℂ) + z) ^ (w - 1))
    + (z ^ 2 - z + 1/6) / 2 * (w * (w - 1) * ((a : ℂ) + z) ^ (w - 1 - 1))
    - (z ^ 3 - 3/2 * z ^ 2 + z / 2) / 6 * (w * (w - 1) * (w - 1 - 1) * ((a : ℂ) + z) ^ (w - 1 - 1 - 1))
  let G' : ℝ → ℂ := fun t => - (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6) *
    (w * (w - 1) * (w - 1 - 1) * (w - 1 - 1 - 1) * ((a : ℂ) + t) ^ (w - 1 - 1 - 1 - 1))
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun y : ℝ => G y) (G' t) t := by
    intro t ht
    have h : 0 < a + t := by linarith
    have p1 : HasDerivAt (fun z : ℂ => z - 1/2) 1 (t : ℂ) := (hasDerivAt_id _).sub_const _
    have p2 : HasDerivAt (fun z : ℂ => (z ^ 2 - z + 1/6) / 2) ((t : ℂ) - 1/2) (t : ℂ) := by
      have := ((((hasDerivAt_id (t : ℂ)).pow 2).sub (hasDerivAt_id _)).add_const (1/6)).div_const 2
      exact this.congr_deriv (by simp; ring)
    have p3 : HasDerivAt (fun z : ℂ => (z ^ 3 - 3/2 * z ^ 2 + z / 2) / 6)
        (((t : ℂ) ^ 2 - t + 1/6) / 2) (t : ℂ) := by
      have := ((((hasDerivAt_id (t : ℂ)).pow 3).sub
        (((hasDerivAt_id (t : ℂ)).pow 2).const_mul (3/2))).add
        ((hasDerivAt_id (t : ℂ)).div_const 2)).div_const 6
      exact this.congr_deriv (by simp; ring)
    have hG : HasDerivAt G (G' t) (t : ℂ) := by
      have := (((hasDerivAt_shift_cpow h w).sub
        (p1.mul ((hasDerivAt_shift_cpow h (w - 1)).const_mul w))).add
        (p2.mul ((hasDerivAt_shift_cpow h (w - 1 - 1)).const_mul (w * (w - 1))))).sub
        (p3.mul ((hasDerivAt_shift_cpow h (w - 1 - 1 - 1)).const_mul (w * (w - 1) * (w - 1 - 1))))
      exact this.congr_deriv (by simp only [G']; ring)
    exact hG.comp_ofReal
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖G' t‖ ≤ (‖s‖ + 2) ^ 4 * a ^ (-(9/8 : ℝ)) := by
    intro t ht
    have h : 0 < a + t := by linarith [ht.1]
    have b1 : ‖- (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6)‖ ≤ 1 := by
      have : - (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6)
          = ((- ((t ^ 3 - 3/2 * t ^ 2 + t / 2) / 6) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have h2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2.le
      have h3 : t ^ 3 ≤ 1 := pow_le_one₀ ht.1 ht.2.le
      have h4 : 0 ≤ t ^ 2 := by positivity
      have h5 : 0 ≤ t ^ 3 := pow_nonneg ht.1 _
      constructor <;> linarith [ht.1, ht.2]
    have key : ∀ c : ℝ, |c| ≤ 2 → ‖(c : ℂ) - s‖ ≤ ‖s‖ + 2 := by
      intro c hc
      have := norm_sub_le (c : ℂ) s
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have c0 : ‖w‖ ≤ ‖s‖ + 2 := by simpa using key 1 (by norm_num)
    have c1 : ‖w - 1‖ ≤ ‖s‖ + 2 := by
      convert key 0 (by norm_num) using 2; rw [hw]; push_cast; ring
    have c2 : ‖w - 1 - 1‖ ≤ ‖s‖ + 2 := by
      convert key (-1) (by norm_num) using 2; rw [hw]; push_cast; ring
    have c3 : ‖w - 1 - 1 - 1‖ ≤ ‖s‖ + 2 := by
      convert key (-2) (by norm_num) using 2; rw [hw]; push_cast; ring
    have c4 : ‖((a : ℂ) + t) ^ (w - 1 - 1 - 1 - 1)‖ ≤ a ^ (-(9/8 : ℝ)) := by
      rw [← Complex.ofReal_add, Complex.norm_cpow_eq_rpow_re_of_pos h]
      have e : (w - 1 - 1 - 1 - 1).re ≤ -(9/8 : ℝ) := by
        simp [hw]; linarith
      calc _ ≤ (a + t) ^ (-(9/8 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) e
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [ht.1]) (by norm_num)
    simp only [G', norm_mul]
    calc _ ≤ 1 * ((‖s‖ + 2) * (‖s‖ + 2) * (‖s‖ + 2) * (‖s‖ + 2) * a ^ (-(9/8 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun y : ℝ => G y) (f' := G')
    (fun t ht => (hd t ht.1).hasDerivWithinAt) hb
  refine le_of_eq_of_le (congrArg _ ?_) this
  simp only [G, emE, emT, ← hw]
  push_cast
  simp only [add_zero]
  ring

lemma summable_nine_pow_mul_inv_sq_succ : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(9/8 : ℝ))) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num : -(9/8 : ℝ) < -1))
  simpa using this

lemma differentiable_emT {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emT x) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have : NeZero (x : ℂ) := ⟨hx'⟩
  unfold emT
  fun_prop

lemma differentiable_emE {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emE x) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have : NeZero (x : ℂ) := ⟨hx'⟩
  have h1 := differentiable_emT hx
  have h2 := differentiable_emT (x := x + 1) (by linarith)
  unfold emE
  fun_prop

lemma differentiableOn_tsum_emE :
    DifferentiableOn ℂ (fun s => ∑' n : ℕ, emE ((n : ℝ) + 1) s) {s : ℂ | -(15/8 : ℝ) < s.re} := by
  intro s hs
  have ho : IsOpen ({z : ℂ | -(15/8 : ℝ) < z.re} ∩ Metric.ball 0 (‖s‖ + 1)) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (n : ℕ) (z : ℂ) => emE ((n : ℝ) + 1) z)
    (summable_nine_pow_mul_inv_sq_succ.mul_left ((‖s‖ + 3) ^ 4))
    (fun n => (differentiable_emE (by positivity)).differentiableOn) ho (by
      intro n z hz
      have h1 : ‖z‖ < ‖s‖ + 1 := by simpa using hz.2
      refine (norm_emE_le (by simp) (le_of_lt hz.1)).trans ?_
      have h2 : ‖z‖ + 2 ≤ ‖s‖ + 3 := by linarith
      gcongr)
  exact (this.differentiableAt (ho.mem_nhds ⟨hs, by simp⟩)).differentiableWithinAt

lemma tendsto_cpow_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have := (tendsto_rpow_neg_atTop (y := -c.re) (by linarith)).comp h1
  refine this.congr fun n => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

lemma eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * riemannZeta s = emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s := by
  have hsum : Summable (fun n : ℕ => emE ((n : ℝ) + 1) s) :=
    Summable.of_norm_bounded (summable_nine_pow_mul_inv_sq_succ.mul_left ((‖s‖ + 2) ^ 4))
      (fun n => norm_emE_le (by simp) (by linarith))
  have hT : Tendsto (fun n : ℕ => emT ((n : ℝ) + 1) s) atTop (𝓝 0) := by
    have := ((tendsto_cpow_zero (c := 1 - s) (by simp; linarith)).sub
      (((tendsto_cpow_zero (c := 1 - s - 1) (by simp; linarith)).const_mul (1 - s)).div_const 2)).add
      (((tendsto_cpow_zero (c := 1 - s - 1 - 1) (by simp; linarith)).const_mul
        ((1 - s) * (1 - s - 1))).div_const 12)
    simpa [emT] using this
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
    exact (by simpa using this : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s)).hasSum
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, emE ((n : ℝ) + 1) s =
      emT ((N : ℝ) + 1) s - emT 1 s + (s - 1) * ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ s := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, emE]
      have : (1 - s - 1) = -s := by ring
      rw [this, Complex.cpow_neg]
      push_cast
      ring
  have h1 := (hT.sub_const (emT 1 s)).add (hz.tendsto_sum_nat.const_mul (s - 1))
  have h2 := hsum.hasSum.tendsto_sum_nat
  simp only [hpart] at h2
  rw [tendsto_nhds_unique h2 h1]
  ring

lemma eq_of_lt {s : ℂ} (hs : -(15/8 : ℝ) < s.re) (h1 : s ≠ 1) :
    (s - 1) * riemannZeta s = emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s := by
  have ho : IsOpen {z : ℂ | -(15/8 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : ∀ z : ℂ, z ≠ 1 → LFunctionTrivChar₁ 1 z = (z - 1) * riemannZeta z := by
    intro z hz
    rw [LFunctionTrivChar₁, Function.update_of_ne hz, LFunctionTrivChar, LFunction_modOne_eq]
  have hA : AnalyticOnNhd ℂ (LFunctionTrivChar₁ 1) {z : ℂ | -(15/8 : ℝ) < z.re} :=
    (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd ho
  have hB : AnalyticOnNhd ℂ (fun s => emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s)
      {z : ℂ | -(15/8 : ℝ) < z.re} :=
    ((differentiable_emT one_pos).differentiableOn.add differentiableOn_tsum_emE).analyticOnNhd ho
  have := hA.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_halfSpace_re_gt _).isPreconnected (z₀ := 2) (by simp; norm_num) (by
      have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
      filter_upwards [this] with z hz
      rw [hf z (by rintro rfl; simp at hz), eq_of_one_lt hz])
  rw [← hf s h1]
  exact this hs

theorem norm_sub_one_mul_riemannZeta_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(7/4 : ℝ) ≤ s.re → s ≠ 1 →
      ‖(s - 1) * riemannZeta s‖ ≤ C * (‖s‖ + 2) ^ 5 := by
  set K : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(9/8 : ℝ)) with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun n => by positivity
  refine ⟨3 + K, by linarith, fun s hs h1 => ?_⟩
  rw [eq_of_lt (by linarith) h1]
  set R := ‖s‖ + 2 with hR
  have hR1 : 1 ≤ R := by have := norm_nonneg s; linarith
  have h2 : ‖∑' n : ℕ, emE ((n : ℝ) + 1) s‖ ≤ R ^ 4 * K :=
    tsum_of_norm_bounded (summable_nine_pow_mul_inv_sq_succ.hasSum.mul_left (R ^ 4))
      (fun n => norm_emE_le (by simp) (by linarith))
  have c0 : ‖1 - s‖ ≤ R := by
    have := norm_sub_le 1 s
    rw [norm_one] at this; linarith
  have c1 : ‖1 - s - 1‖ ≤ R := by simp [hR]
  have h3 : ‖emT 1 s‖ ≤ 1 + R / 2 + R * R / 12 := by
    simp only [emT, Complex.ofReal_one, Complex.one_cpow, mul_one]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
    · simp only [norm_one, norm_div, Complex.norm_ofNat]; gcongr
    · simp only [norm_mul, norm_div, Complex.norm_ofNat]; gcongr
  have p0 : 1 ≤ R ^ 5 := one_le_pow₀ hR1
  have p1 : R ^ 1 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p2 : R ^ 2 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p5 : R ^ 4 * K ≤ R ^ 5 * K := by gcongr
  refine (norm_add_le _ _).trans ?_
  nlinarith

end GlobalTheory.ZetaLeft
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticAtMostTwoPrimesOver
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem quadratic_at_most_two_primes_over (K : Type) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (q : ℕ) (hq : q.Prime)
    (P₁ P₂ P₃ : HeightOneSpectrum (𝓞 K))
    (h₁ : ((q : ℕ) : 𝓞 K) ∈ P₁.asIdeal) (h₂ : ((q : ℕ) : 𝓞 K) ∈ P₂.asIdeal)
    (h₃ : ((q : ℕ) : 𝓞 K) ∈ P₃.asIdeal) : P₁ = P₂ ∨ P₁ = P₃ ∨ P₂ = P₃ := by
  by_contra hne
  push Not at hne
  obtain ⟨h12, h13, h23⟩ := hne
  have hN : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 K)}) = q ^ 2 := by
    rw [Ideal.absNorm_span_singleton]
    have : ((q : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hK]
    simp
  have hd : ∀ P : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P.asIdeal →
      P.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 K)} := fun P hP =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hP)
  have hqd : ∀ P : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P.asIdeal →
      q ∣ Ideal.absNorm P.asIdeal := by
    intro P hP
    have h1 : Ideal.absNorm P.asIdeal ∣ q ^ 2 := hN ▸ map_dvd Ideal.absNorm (hd P hP)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hq).mp h1
    rcases i with _ | i
    · exfalso
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hi
      exact P.isPrime.ne_top hi
    · rw [hi]; exact dvd_pow_self q (Nat.succ_ne_zero i)
  have hc : ∀ P Q : HeightOneSpectrum (𝓞 K), P ≠ Q → IsCoprime P.asIdeal Q.asIdeal := by
    intro P Q h
    rw [Ideal.isCoprime_iff_sup_eq]
    exact P.isMaximal.coprime_of_ne Q.isMaximal (fun e => h (HeightOneSpectrum.ext e))
  have hprod : P₁.asIdeal * P₂.asIdeal * P₃.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 K)} :=
    IsCoprime.mul_dvd (IsCoprime.mul_left (hc _ _ h13) (hc _ _ h23))
      (IsCoprime.mul_dvd (hc _ _ h12) (hd _ h₁) (hd _ h₂)) (hd _ h₃)
  have h4 := map_dvd Ideal.absNorm hprod
  rw [hN, map_mul, map_mul] at h4
  have h5 : q * q * q ∣ q ^ 2 :=
    (mul_dvd_mul (mul_dvd_mul (hqd _ h₁) (hqd _ h₂)) (hqd _ h₃)).trans h4
  have h6 : q ^ 3 ∣ q ^ 2 := by rwa [show q ^ 3 = q * q * q by ring]
  have := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp h6
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticUnramifiedIffInertOrSplit
section
open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory

open scoped TensorProduct in
open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.quadratic_unramified_iff_inert_or_split (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) :
    ((∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔
      ((v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime ∨
        (v.asIdeal.primesOver (𝓞 E)).ncard = 2)) := by
  classical
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  set I := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) with hIdef
  set M := UniqueFactorizationMonoid.normalizedFactors I with hMdef
  set s := IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) with hsdef
  have hv : v.asIdeal ≠ ⊥ := v.ne_bot
  have hI : I ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).not.mpr hv
  have hs : ∀ P, P ∈ s ↔ P ∈ v.asIdeal.primesOver (𝓞 E) :=
    fun P => IsDedekindDomain.mem_primesOverFinset_iff hv (𝓞 E)
  have hM : ∀ P, P ∈ v.asIdeal.primesOver (𝓞 E) ↔ P ∈ M :=
    fun P => Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 E) hv
  have hcount : ∀ P ∈ v.asIdeal.primesOver (𝓞 E), P.ramificationIdx (𝓞 F) = M.count P := by
    intro P hP
    haveI : P.LiesOver v.asIdeal := hP.2
    exact Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count v.asIdeal P hI
  have hsum : ∑ P ∈ s, P.ramificationIdx (𝓞 F) * v.asIdeal.inertiaDeg' P = 2 := by
    rw [← h2, ← Ideal.sum_ramification_inertia (𝓞 E) F E hv]
    refine Finset.sum_congr rfl fun P hP => ?_
    have hP' := (hs P).1 hP
    haveI : P.IsPrime := hP'.1
    haveI : P.LiesOver v.asIdeal := hP'.2
    rw [Ideal.ramificationIdx_eq_ramificationIdx' v.asIdeal P hv]
  have hterm : ∀ P ∈ s, 1 ≤ P.ramificationIdx (𝓞 F) * v.asIdeal.inertiaDeg' P := by
    intro P hP
    have hP' := (hs P).1 hP
    haveI : P.IsPrime := hP'.1
    haveI : P.LiesOver v.asIdeal := hP'.2
    have h1 : 0 < P.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos P (𝓞 F)
    have h2 : 0 < v.asIdeal.inertiaDeg' P := Ideal.inertiaDeg'_pos v.asIdeal P
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h1.ne' h2.ne')
  have hncard : (v.asIdeal.primesOver (𝓞 E)).ncard = s.card := by
    rw [← Set.ncard_coe_finset, hsdef, IsDedekindDomain.coe_primesOverFinset hv]
  have hcard_le : s.card ≤ 2 := by
    have := Finset.card_nsmul_le_sum s _ 1 hterm
    simpa [hsum] using this
  have hcard_pos : 0 < s.card := by
    rw [← hncard]
    exact Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero v.asIdeal (𝓞 E))
  have hU : (∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔ ∀ P ∈ s, P.ramificationIdx (𝓞 F) = 1 := by
    constructor
    · intro h P hP
      have hP' := (hs P).1 hP
      haveI : P.IsPrime := hP'.1
      haveI : P.LiesOver v.asIdeal := hP'.2
      have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hv P
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 (h ⟨P, hP'.1, hPb⟩ hP'.2)
    · intro h w hw
      have hmem : w.asIdeal ∈ s := (hs _).2 ⟨w.isPrime, hw⟩
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.2 (h _ hmem)
  rw [hU, hncard]
  have hI0 : I ≠ 0 := hI
  constructor
  · intro he
    by_cases h2c : s.card = 2
    · exact Or.inr h2c
    left
    have h1 : s.card = 1 := by omega
    obtain ⟨P, hsP⟩ := Finset.card_eq_one.1 h1
    have hPs : P ∈ s := by simp [hsP]
    have hallM : ∀ Q ∈ M, Q = P := by
      intro Q hQ
      have : Q ∈ s := (hs Q).2 ((hM Q).2 hQ)
      simpa [hsP] using this
    have hcP : M.count P = 1 := by
      rw [← hcount P ((hs P).1 hPs)]
      exact he P hPs
    have hcardM : M.card = 1 := by
      rw [← hcP]
      exact (Multiset.count_eq_card.2 fun x hx => (hallM x hx).symm).symm
    have hMP : M = {P} := by
      rw [Multiset.eq_replicate_of_mem hallM, hcardM, Multiset.replicate_one]
    have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hI0
    rw [← hMdef, hMP, Multiset.prod_singleton] at hassoc
    rw [← associated_iff_eq.1 hassoc]
    exact ((hs P).1 hPs).1
  · rintro (hp | h2c)
    · intro P hP
      have hirr : Irreducible I := (Ideal.prime_of_isPrime hI hp).irreducible
      have hMI : M = {I} := by
        rw [hMdef, UniqueFactorizationMonoid.normalizedFactors_irreducible hirr, normalize_eq]
      have hPI : P = I := by
        have := (hM P).1 ((hs P).1 hP)
        rw [hMI] at this
        simpa using this
      rw [hcount P ((hs P).1 hP), hMI, hPI, Multiset.count_singleton_self]
    · intro P hP
      by_contra hne
      have hP' := (hs P).1 hP
      haveI : P.IsPrime := hP'.1
      haveI : P.LiesOver v.asIdeal := hP'.2
      have he : 0 < P.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos P (𝓞 F)
      have hf : 0 < v.asIdeal.inertiaDeg' P := Ideal.inertiaDeg'_pos v.asIdeal P
      have hge : 2 * 1 ≤ P.ramificationIdx (𝓞 F) * v.asIdeal.inertiaDeg' P :=
        Nat.mul_le_mul (by omega) hf
      have hrest := Finset.card_nsmul_le_sum (s.erase P) _ 1
        (fun Q hQ => hterm Q (Finset.mem_of_mem_erase hQ))
      rw [← Finset.add_sum_erase s _ hP] at hsum
      rw [Finset.card_erase_of_mem hP, h2c] at hrest
      simp only [smul_eq_mul, mul_one] at hrest
      omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitsAlgebraMap
section
namespace GlobalTheory.SplittingAdditive

open BigOperators

def Splits {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) (p : G → ℂ) : Prop :=
  ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
    (∀ i : Fin m, a i ∈ A ∧ b i ∈ A) ∧ ∀ x k : G, p (x * k) = ∑ i : Fin m, a i x * b i k

theorem splits_add {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) {p q : G → ℂ}
    (hp : Splits A p) (hq : Splits A q) : Splits A (p + q) := by
  obtain ⟨m, a, b, hab, h⟩ := hp
  obtain ⟨n, c, d, hcd, h'⟩ := hq
  refine ⟨m + n, Fin.append a c, Fin.append b d, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hab j
    · simpa using hcd j
  · intro x k
    rw [Fin.sum_univ_add]
    simp [h, h']

theorem splits_mul {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) {p q : G → ℂ}
    (hp : Splits A p) (hq : Splits A q) : Splits A (p * q) := by
  obtain ⟨m, a, b, hab, h⟩ := hp
  obtain ⟨n, c, d, hcd, h'⟩ := hq
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  refine ⟨m * n, fun j => a (e.symm j).1 * c (e.symm j).2,
    fun j => b (e.symm j).1 * d (e.symm j).2, ?_, ?_⟩
  · intro j
    exact ⟨A.mul_mem (hab _).1 (hcd _).1, A.mul_mem (hab _).2 (hcd _).2⟩
  · intro x k
    have key : ∀ f : Fin m × Fin n → ℂ, ∑ j : Fin (m * n), f (e.symm j) = ∑ q, f q :=
      fun f => Equiv.sum_comp e.symm f
    simp only [Pi.mul_apply]
    rw [key (fun q => a q.1 x * c q.2 x * (b q.1 k * d q.2 k)), h, h', Finset.sum_mul_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring

theorem splits_algebraMap {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) (r : ℂ) :
    Splits A (algebraMap ℂ (G → ℂ) r) := by
  refine ⟨1, fun _ => algebraMap ℂ (G → ℂ) r, fun _ => 1, ?_, ?_⟩
  · intro _
    exact ⟨A.algebraMap_mem r, A.one_mem⟩
  · intro x k
    simp

theorem main :
    ∀ {G : Type} [inst : Mul G] (S : Set (G → ℂ)),
      (∀ p ∈ S, ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
        (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
          ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k) →
      ∀ p ∈ Algebra.adjoin ℂ S, ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
        (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
          ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k := by
  intro G _ S hS p hp
  change Splits (Algebra.adjoin ℂ S) p
  induction hp using Algebra.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap r => exact splits_algebraMap _ r
  | add x y _ _ hx hy => exact splits_add _ hx hy
  | mul x y _ _ hx hy => exact splits_mul _ hx hy

end GlobalTheory.SplittingAdditive
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationOfGeneratorOfPow
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem valuation_of_generator_of_pow (K : Type) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (n : ℕ) (π : 𝓞 K) (h : 𝔭.asIdeal ^ n = Ideal.span {π}) :
    𝔭.valuation K (π : K) = WithZero.exp (-(n : ℤ)) := by
  have hπ : π ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at h
    exact 𝔭.ne_bot (pow_eq_zero_iff'.mp h).1
  rw [show (π : K) = algebraMap (𝓞 K) K π from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    𝔭.intValuation_if_neg hπ, ← h, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr 𝔭.ne_bot) 𝔭.associates_irreducible,
    Associates.count_self 𝔭.associates_irreducible, mul_one]

end GlobalTheory
end

