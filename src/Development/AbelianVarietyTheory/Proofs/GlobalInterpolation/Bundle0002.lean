import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompletedLFunctionNeZeroOfReNonpos
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

theorem inv_Gammaℝ_eq_mul_inv_add_two (s : ℂ) :
    (Gammaℝ s)⁻¹ = s / (2 * Real.pi) * (Gammaℝ (s + 2))⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Gammaℝ_def]
  · have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [Gammaℝ_add_two hs]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    generalize (Gammaℝ s)⁻¹ = g
    field_simp

private lemma deriv_inv_Gammaℝ_eq_shift (x : ℂ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) x =
      1 / (2 * Real.pi) * (Gammaℝ (x + 2))⁻¹ +
        x / (2 * Real.pi) * deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (x + 2) := by
  have hF : (fun s : ℂ => (Gammaℝ s)⁻¹) = fun s => s / (2 * Real.pi) * (Gammaℝ (s + 2))⁻¹ :=
    funext inv_Gammaℝ_eq_mul_inv_add_two
  have h1 : HasDerivAt (fun s : ℂ => s / (2 * (Real.pi : ℂ))) (1 / (2 * Real.pi)) x :=
    (hasDerivAt_id' x).div_const _
  have h2 : HasDerivAt (fun s : ℂ => (Gammaℝ (s + 2))⁻¹)
      (deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (x + 2)) x :=
    HasDerivAt.comp_add_const x 2 (differentiable_Gammaℝ_inv (x + 2)).hasDerivAt
  conv_lhs => rw [hF]
  exact (h1.mul h2).deriv

theorem deriv_inv_Gammaℝ_ne_zero (n : ℕ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (-(2 * n)) ≠ 0 := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  induction n with
  | zero =>
    rw [deriv_inv_Gammaℝ_eq_shift]
    have h2 : Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num)
    simp [h2, Real.pi_ne_zero]
  | succ n ih =>
    rw [deriv_inv_Gammaℝ_eq_shift]
    have e : (-(2 * ((n + 1 : ℕ) : ℂ))) + 2 = -(2 * (n : ℂ)) := by push_cast; ring
    rw [e, inv_eq_zero.mpr (Gammaℝ_eq_zero_iff.mpr ⟨n, rfl⟩), mul_zero, zero_add]
    refine mul_ne_zero (div_ne_zero ?_ hπ) ih
    have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    push_cast
    exact neg_ne_zero.mpr (mul_ne_zero two_ne_zero this)

theorem rootNumber_ne_zero_of_isPrimitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : rootNumber χ ≠ 0 := by
  have hG : gaussSum χ ZMod.stdAddChar ≠ 0 := by
    intro h
    have h1 : ZMod.dft (χ : ZMod q → ℂ) = 0 := by
      funext k
      rw [hχ.fourierTransform_eq_inv_mul_gaussSum k, h, mul_zero]
      rfl
    have h2 := congr_fun (ZMod.dft_dft (χ : ZMod q → ℂ)) (-1)
    rw [h1, _root_.map_zero] at h2
    simp only [Pi.zero_apply, neg_neg, map_one, smul_eq_mul, mul_one] at h2
    exact NeZero.ne q (by exact_mod_cast h2.symm)
  unfold rootNumber
  refine div_ne_zero (div_ne_zero hG (pow_ne_zero _ I_ne_zero)) ?_
  rw [Ne, cpow_eq_zero_iff]
  exact fun h => NeZero.ne q (Nat.cast_eq_zero.mp h.1)

theorem completedLFunction_ne_zero_of_re_nonpos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {s : ℂ} (hs : s.re ≤ 0) (h0 : s ≠ 0 ∨ χ ≠ 1) :
    completedLFunction χ s ≠ 0 := by
  have hFE := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hFE
  rw [hFE]
  have hw : 1 ≤ (1 - s).re := by rw [sub_re, one_re]; linarith
  refine mul_ne_zero (mul_ne_zero ?_ (rootNumber_ne_zero_of_isPrimitive hχ)) ?_
  · rw [Ne, cpow_eq_zero_iff]
    exact fun h => NeZero.ne q (Nat.cast_eq_zero.mp h.1)
  · intro hC
    have hne : χ⁻¹ ≠ 1 ∨ 1 - s ≠ 1 := by
      rcases h0 with h | h
      · exact Or.inr (by intro h'; apply h; linear_combination -h')
      · exact Or.inl (inv_ne_one.mpr h)
    apply LFunction_ne_zero_of_one_le_re χ⁻¹ hne hw
    have h1s : 1 - s ≠ 0 := by
      intro h'; rw [h'] at hw; norm_num at hw
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inl h1s), hC, zero_div]

theorem LFunction_zero_of_re_nonpos : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ s : ℂ, s.re ≤ 0 → LFunction χ s = 0 → (∃ n : ℕ, s = -n) ∧ analyticOrderNatAt (LFunction χ) s = 1 ∧ (s = 0 → χ.Even ∧ χ ≠ 1) ∧ (s = -1 → χ.Odd) := by
  intro q _ χ hχ s hs hL
  have h0 : s ≠ 0 ∨ χ ≠ 1 := by
    by_contra! h
    obtain ⟨rfl, rfl⟩ := h
    have hq : q = 1 := by rw [IsPrimitive, conductor_one] at hχ; exact hχ.symm
    subst hq
    rw [LFunction_modOne_eq, riemannZeta_zero] at hL
    norm_num at hL
  have h0' : s ≠ 0 ∨ q ≠ 1 := h0.imp id (fun h hq => h (level_one' χ hq))
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hC : completedLFunction χ s ≠ 0 := completedLFunction_ne_zero_of_re_nonpos hχ hs h0
  have hCd : DifferentiableAt ℂ (completedLFunction χ) s :=
    differentiableAt_completedLFunction χ s h0' (Or.inl hs1)
  obtain ⟨a, ha, hpar⟩ : ∃ a : ℕ, (∀ w, gammaFactor χ w = Gammaℝ (w + a)) ∧
      (a = 0 ∧ χ.Even ∨ a = 1 ∧ χ.Odd) := by
    rcases χ.even_or_odd with h | h
    · exact ⟨0, fun w => by simp [h.gammaFactor_def], Or.inl ⟨rfl, h⟩⟩
    · exact ⟨1, fun w => by simp [h.gammaFactor_def], Or.inr ⟨rfl, h⟩⟩
  have hev : LFunction χ =ᶠ[nhds s] fun w => completedLFunction χ w * (Gammaℝ (w + a))⁻¹ := by
    have : ∀ᶠ w in nhds s, w ≠ 0 ∨ q ≠ 1 := by
      rcases h0' with h | h
      · exact (eventually_ne_nhds h).mono fun w hw => Or.inl hw
      · exact Filter.Eventually.of_forall fun _ => Or.inr h
    exact this.mono fun w hw => by
      rw [LFunction_eq_completed_div_gammaFactor χ w hw, div_eq_mul_inv, ha]
  have hG : Gammaℝ (s + a) = 0 := by
    have := hev.self_of_nhds
    rw [hL] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hC
    · exact inv_eq_zero.mp h
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hG
  have hh : HasDerivAt (fun w : ℂ => (Gammaℝ (w + a))⁻¹)
      (deriv (fun w : ℂ => (Gammaℝ w)⁻¹) (s + a)) s :=
    HasDerivAt.comp_add_const s (a : ℂ) (differentiable_Gammaℝ_inv (s + a)).hasDerivAt
  have hder : deriv (LFunction χ) s ≠ 0 := by
    rw [hev.deriv_eq, (hCd.hasDerivAt.fun_mul hh).deriv, inv_eq_zero.mpr hG, mul_zero, zero_add]
    refine mul_ne_zero hC ?_
    rw [hn]
    exact deriv_inv_Gammaℝ_ne_zero n
  have hAn : AnalyticAt ℂ (LFunction χ) s :=
    analyticAt_iff_eventually_differentiableAt.mpr
      ((eventually_ne_nhds hs1).mono fun w hw => differentiableAt_LFunction χ w (Or.inl hw))
  have hord : analyticOrderAt (LFunction χ) s = 1 :=
    hAn.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hL hder
  have hs_eq : s = -((2 * n + a : ℕ) : ℂ) := by push_cast; linear_combination hn
  refine ⟨⟨2 * n + a, hs_eq⟩, by simp [analyticOrderNatAt, hord], fun h => ?_, fun h => ?_⟩
  · rw [h] at hs_eq
    have hk : ((2 * n + a : ℕ) : ℂ) = 0 := by linear_combination hs_eq
    have hk' : 2 * n + a = 0 := by exact_mod_cast hk
    refine ⟨?_, h0.resolve_left (not_not.mpr h)⟩
    rcases hpar with ⟨_, he⟩ | ⟨ha1, _⟩
    · exact he
    · omega
  · rw [h] at hs_eq
    have hk : ((2 * n + a : ℕ) : ℂ) = 1 := by linear_combination hs_eq
    have hk' : 2 * n + a = 1 := by exact_mod_cast hk
    rcases hpar with ⟨ha0, _⟩ | ⟨_, ho⟩
    · omega
    · exact ho

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableAtMellinSummatory
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LGrowth

open Filter Topology Asymptotics

theorem norm_partialSum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤ q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hper : ∀ m : ℕ, ∑ k ∈ Finset.range q, χ ((m + k : ℕ) : ZMod q) = 0 := by
    intro m
    have h0 : ∑ a : ZMod q, χ a = 0 := χ.sum_eq_zero_of_ne_one hχ
    rw [← h0, ← Equiv.sum_comp (Equiv.addLeft (m : ZMod q))]
    refine Finset.sum_bij (fun k _ => (k : ZMod q)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb hab
      have := (ZMod.natCast_eq_natCast_iff' a b q).1 hab
      rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
        at this
    · intro b _
      exact ⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
    · intro a _
      simp
  have hI : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)
      = ∑ k ∈ Finset.range n, χ ((1 + k : ℕ) : ZMod q) := by
    intro n
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp
  rw [hI]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n q with h | h
    · refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => χ.norm_le_one _).trans ?_
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast h.le
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
      rw [Finset.sum_range_add]
      have := hper (1 + m)
      simp only [← add_assoc]
      rw [this, add_zero]
      exact ih m (by omega)

section General

variable {f : ℕ → ℂ} {C : ℝ}

noncomputable def summatory (f : ℕ → ℂ) (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k

theorem measurable_summatory (f : ℕ → ℂ) : Measurable (summatory f) :=
  (measurable_from_top (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor

theorem summatory_eq_zero {t : ℝ} (ht : t < 1) : summatory f t = 0 := by
  simp [summatory, Nat.floor_eq_zero.2 ht]

theorem mellin_summatory (s : ℂ) :
    mellin (summatory f) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin, setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (s := Set.Ici (1 : ℝ)) (fun t ht => Set.mem_Ioi.2 (zero_lt_one.trans_le (Set.mem_Ici.1 ht))), integral_Ici_eq_integral_Ioi]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [summatory, smul_eq_mul]
    rw [mul_comm]
    congr 2
    ring
  · intro t ht
    rw [summatory_eq_zero (not_le.1 ht.2), smul_zero]

theorem differentiableAt_mellin_summatory (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => mellin (summatory f) (-z)) s := by
  have h : DifferentiableAt ℂ (mellin (summatory f)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      refine (locallyIntegrable_const C).mono (measurable_summatory f).aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => (hC _).trans (Real.le_norm_self C)
    · refine IsBigO.of_bound C (Eventually.of_forall fun t => ?_)
      simpa [summatory] using hC ⌊t⌋₊
    · simpa using hs
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht
      simp [summatory_eq_zero ht]
    · simp
  exact h.comp s differentiableAt_id.neg

theorem norm_mellin_summatory_le (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    ‖mellin (summatory f) (-s)‖ ≤ C / s.re := by
  rw [mellin_summatory]
  have hlt : -(s.re + 1) < -1 := by linarith
  refine (norm_integral_le_of_norm_le (g := fun t : ℝ => C * t ^ (-(s.re + 1)))
    ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul C) ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.rpow_nonneg ht0.le _)
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt zero_lt_one, Real.one_rpow]
    refine le_of_eq ?_
    have : -(s.re + 1) + 1 = -s.re := by ring
    rw [this]
    field_simp

end General

theorem LFunction_eq_mul_mellin (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = s * mellin (summatory fun n => χ (n : ZMod q)) (-s) := by
  have hC := norm_partialSum_le q χ hχ
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have h1 : AnalyticOnNhd ℂ (LFunction χ) {z : ℂ | 0 < z.re} :=
    (differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
  have h2 : AnalyticOnNhd ℂ (fun z => z * mellin (summatory fun n => χ (n : ZMod q)) (-z))
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    exact (differentiableAt_id.mul
      (differentiableAt_mellin_summatory hC hz)).differentiableWithinAt
  refine h1.eqOn_of_preconnected_of_eventuallyEq h2 (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 2) (by simp) ?_ hs
  have hV : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hV.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by simp)] with z hz
  rw [LFunction_eq_LSeries χ hz, mellin_summatory]
  refine LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hz)
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz) ?_
  refine IsBigO.of_bound q (Eventually.of_forall fun n => ?_)
  simpa using hC n

theorem norm_LFunction_le : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ s : ℂ, 0 < s.re → ‖LFunction χ s‖ ≤ q * ‖s‖ / s.re := by
  intro q _ χ hχ s hs
  rw [LFunction_eq_mul_mellin q χ hχ hs, norm_mul]
  refine (mul_le_mul_of_nonneg_left
    (norm_mellin_summatory_le (norm_partialSum_le q χ hχ) hs) (norm_nonneg s)).trans ?_
  exact le_of_eq (by ring)

end GlobalTheory.LGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfNormSubOneLt
section
namespace GlobalTheory.CharacterConductorBall

private lemma norm_sub_one_le_norm_mul_self_sub_one (w : ℂ) (h : ‖w - 1‖ < 1 / 2) :
    3 / 2 * ‖w - 1‖ ≤ ‖w * w - 1‖ := by
  have h1 : w * w - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (2 : ℝ) ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have := norm_sub_le (w + 1) (w - 1)
    have e : (w + 1) - (w - 1) = (2 : ℂ) := by ring
    rw [e] at this
    simpa using this
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (w - 1)]

theorem eq_one_of_norm_sub_one_lt {A : Type} [AddMonoid A] (ψ : AddChar A ℂ) (B : Set A)
    (hB : ∀ x ∈ B, x + x ∈ B) (hψ : ∀ x ∈ B, ‖ψ x - 1‖ < 1 / 2) : ∀ x ∈ B, ψ x = 1 := by

  have key : ∀ k : ℕ, ∀ x ∈ B, (3 / 2 : ℝ) ^ k * ‖ψ x - 1‖ < 1 / 2 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hψ x hx
    | succ k ih =>
      intro x hx
      have h2 := ih (x + x) (hB x hx)
      have h3 := norm_sub_one_le_norm_mul_self_sub_one (ψ x) (hψ x hx)
      rw [AddChar.map_add_eq_mul] at h2
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖ψ x - 1‖ = (3 / 2) ^ k * (3 / 2 * ‖ψ x - 1‖) := by ring
        _ ≤ (3 / 2) ^ k * ‖ψ x * ψ x - 1‖ := by gcongr
        _ < 1 / 2 := h2
  intro x hx
  by_contra hne
  have hpos : 0 < ‖ψ x - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖ψ x - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have := key k x hx
  rw [div_lt_iff₀ hpos] at hk
  linarith

theorem exists_ball_trivial {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous (ψ : K → ℂ)) :
    ∃ m : ℤ, ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1 := by

  have hnhds : (ψ : K → ℂ) ⁻¹' {w : ℂ | ‖w - 1‖ < 1 / 2} ∈ nhds (0 : K) := by
    apply hc.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hnhds
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc_def
  have hc0 : c ≠ 0 := by
    have := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (zero_lt_iff.2 γ.ne_zero)
    rw [map_zero] at this
    exact this.ne'

  have hlt : ∀ y ∈ {y : K | Valued.v y < c}, ψ y = 1 := by
    refine eq_one_of_norm_sub_one_lt ψ _ (fun y hy => ?_) (fun y hy => ?_)
    · exact lt_of_le_of_lt ((Valued.v.map_add y y).trans (max_self _).le) hy
    · apply hγ
      simpa [Valuation.restrict_lt_iff_lt_embedding] using hy
  refine ⟨WithZero.log c - 1, fun x hx => hlt x ?_⟩
  calc Valued.v x ≤ WithZero.exp (WithZero.log c - 1) := hx
    _ < WithZero.exp (WithZero.log c) := WithZero.exp_lt_exp.2 (by omega)
    _ = c := WithZero.exp_log hc0

private lemma addChar_trivial_mul_of_valuation_le {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) {t t' : K}
    (ht : ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1)
    (hle : Valued.v t' ≤ Valued.v t) :
    ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t' * s) = 1 := by
  intro s hs
  by_cases h0 : t = 0
  · subst h0
    have : t' = 0 := by simpa using hle
    simp [this, AddChar.map_zero_eq_one]
  · have hv : Valued.v t ≠ 0 := by simpa using h0
    have e : t' * s = t * (t' * t⁻¹ * s) := by field_simp
    rw [e]
    apply ht
    rw [map_mul, map_mul, map_inv₀]
    calc Valued.v t' * (Valued.v t)⁻¹ * Valued.v s ≤ Valued.v t * (Valued.v t)⁻¹ * 1 := by
          gcongr
      _ = 1 := by rw [mul_one, mul_inv_cancel₀ hv]

theorem exists_conductor {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous (ψ : K → ℂ)) (hψ : ∃ t : K, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K,
      (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
        Valued.v t ≤ WithZero.exp n := by
  classical
  obtain ⟨m, hm⟩ := exists_ball_trivial ψ hc
  obtain ⟨t₀, ht₀⟩ := hψ
  have ht₀0 : t₀ ≠ 0 := by rintro rfl; simp [AddChar.map_zero_eq_one] at ht₀
  have hnot : ¬ ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t₀ * s) = 1 :=
    fun h => ht₀ (by simpa using h 1 (by simp))

  have hmem : ∀ t : K, Valued.v t ≤ WithZero.exp m →
      ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1 := by
    intro t ht s hs
    apply hm
    rw [map_mul]
    calc Valued.v t * Valued.v s ≤ WithZero.exp m * 1 := by gcongr
      _ = WithZero.exp m := mul_one _
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, (∀ t : K, Valued.v t ≤ WithZero.exp k →
      ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) → k ≤ b := by
    refine ⟨WithZero.log (Valued.v t₀), fun k hk => ?_⟩
    by_contra hlt
    apply hnot
    apply hk
    have hv : Valued.v t₀ ≠ 0 := by simpa using ht₀0
    rw [← WithZero.exp_log hv]
    exact WithZero.exp_le_exp.2 (by omega)
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd ⟨m, hmem⟩
  refine ⟨n, fun t => ⟨fun hS => ?_, fun ht => hn t ht⟩⟩
  by_contra hgt
  rw [not_le] at hgt
  have hv : Valued.v t ≠ 0 := ne_of_gt (lt_trans WithZero.exp_pos hgt)
  have hj : WithZero.log (Valued.v t) ≤ n := by
    apply hmax
    intro t' ht'
    rw [WithZero.exp_log hv] at ht'
    exact addChar_trivial_mul_of_valuation_le ψ hS ht'
  have : Valued.v t ≤ WithZero.exp n := by
    rw [← WithZero.exp_log hv]
    exact WithZero.exp_le_exp.2 hj
  exact absurd hgt (not_lt.2 this)

end GlobalTheory.CharacterConductorBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFactorOrder
section
namespace GlobalTheory.FactorOrderExistence

open Filter Topology

theorem exists_factor_order {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) {w : ℂ}
    (hw : w ∈ U) (hord : analyticOrderAt g w ≠ ⊤) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧
      (∀ z : ℂ, g z = (z - w) ^ analyticOrderNatAt g w * h z) ∧ h w ≠ (0 : ℂ) := by
  classical
  obtain ⟨h0, h0a, h0ne, hev⟩ := ((hg w hw).analyticOrderAt_ne_top).1 hord
  set n := analyticOrderNatAt g w with hn
  refine ⟨fun z => if z = w then h0 w else g z / (z - w) ^ n, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzw : z = w
    · subst hzw
      refine h0a.congr ?_
      filter_upwards [hev] with y hy
      by_cases hyz : y = z
      · simp [hyz]
      · have hne : (y - z) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hyz)
        simp only [hyz, if_false]
        rw [hy, smul_eq_mul, mul_div_cancel_left₀ _ hne]
    · have ha : AnalyticAt ℂ (fun y => g y / (y - w) ^ n) z :=
        (hg z hz).div ((analyticAt_id.sub analyticAt_const).pow n)
          (pow_ne_zero _ (sub_ne_zero.2 hzw))
      refine ha.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hzw] with y hy
      simp [hy]
  · intro z
    by_cases hzw : z = w
    · subst hzw
      have := hev.self_of_nhds
      simpa using this
    · have hne : (z - w) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hzw)
      simp only [hzw, if_false]
      field_simp
  · simpa using h0ne

end GlobalTheory.FactorOrderExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsPrimitiveRootOfAddCharNeOne
section
namespace GlobalTheory

theorem exists_isPrimitiveRoot_of_addChar_ne_one :
    ∀ (R K : Type) [CommRing R] [Field K] (p : ℕ), p.Prime → (p : R) = 0 →
      ∀ ψ : AddChar R K, ψ ≠ 1 → ∃ ζ : K, IsPrimitiveRoot ζ p := by
  intro R K _ _ p hp hpR ψ hψ
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hψ
  have hpow : ψ x ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hpR, zero_mul, AddChar.map_zero_eq_one]
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (ψ x) = p := orderOf_eq_prime hpow hx
  exact ⟨ψ x, hord ▸ IsPrimitiveRoot.orderOf (ψ x)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsPrimitiveRootOfInjectiveCharacter
section
namespace GlobalTheory

theorem exists_isPrimitiveRoot_of_injective_character (K : Type) [Field K] (p : ℕ) (hp : p.Prime)
    (om : (ZMod p)ˣ →* Kˣ) (hom : Function.Injective om) :
    ∃ ζ : K, IsPrimitiveRoot ζ (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  refine ⟨(om g : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, ← hg, ← orderOf_injective om hom g]
  exact IsPrimitiveRoot.orderOf _

end GlobalTheory
end

