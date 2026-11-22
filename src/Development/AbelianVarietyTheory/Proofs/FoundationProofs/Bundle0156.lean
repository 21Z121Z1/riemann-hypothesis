import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Mathlib
import Formalism.DirichletDensity.DirichletDensityProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqEqOfPosCoeffEq
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma summable_norm_qterm_of_polyB (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := by
  obtain ⟨C, A, hC⟩ := ha
  set r : ℝ := Real.exp (-2 * π * τ.im) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero, Real.exp_lt_exp]
    have := τ.im_pos
    nlinarith [Real.pi_pos]
  have hnorm : ∀ n : ℕ, ‖cexp (2 * π * Complex.I * n * τ)‖ = r ^ n := by
    intro n
    rw [Complex.norm_exp, hr, ← Real.exp_nat_mul]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hg : Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r ^ n := by
    have h0 : Summable fun n : ℕ => (n : ℝ) ^ A * r ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    have h1 := (summable_nat_add_iff 1).mpr h0
    have h2 := h1.mul_left r⁻¹
    refine h2.congr fun n => ?_
    push_cast
    rw [pow_succ]
    field_simp
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hg.mul_left C)
  rw [norm_mul, hnorm n, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg hr0.le n)

end GlobalTheory.EisM

namespace GlobalTheory.EisM

lemma qs_sub_eq_const (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) (hab : ∀ n, n ≠ 0 → a n = b n) (τ : ℍ) :
    qs a τ - qs b τ = a 0 - b 0 := by
  unfold qs
  rw [← (summable_norm_qterm_of_polyB a ha τ).of_norm.tsum_sub (summable_norm_qterm_of_polyB b hb τ).of_norm]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    rw [hab n hn, sub_self]

theorem eq_of_coeff_pos_eq : ∀ (k L : ℕ) (χ : ℤ → ℂ) (a b : ℕ → ℂ), 1 ≤ k → 0 < L → MF k L χ a → MF k L χ b →
    (∀ n, n ≠ 0 → a n = b n) → a = b := by
  intro k L χ a b hk hL ha hb hab
  set c : ℂ := a 0 - b 0 with hc
  have hconst := qs_sub_eq_const a b ha.1 hb.1 hab
  let γ : SL(2, ℤ) := ⟨!![1, 0; (L : ℤ), 1], by simp [Matrix.det_fin_two]⟩
  have hγ10 : γ 1 0 = (L : ℤ) := rfl
  have hγ11 : γ 1 1 = 1 := rfl
  have key : ∀ τ : ℍ, c = χ 1 * ((L : ℂ) * τ + 1) ^ k * c := by
    intro τ
    have h1 := ha.2 γ (by rw [hγ10]) τ
    have h2 := hb.2 γ (by rw [hγ10]) τ
    rw [hγ10, hγ11] at h1 h2
    have e1 := hconst (γ • τ)
    rw [h1, h2, ← mul_sub, hconst τ, ← hc] at e1
    push_cast at e1
    exact e1.symm
  by_contra hne
  have hc0 : c ≠ 0 := by
    intro h0
    apply hne
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · exact sub_eq_zero.mp h0
    · exact hab n hn
  have hone : ∀ τ : ℍ, ‖χ 1‖ * ‖(L : ℂ) * τ + 1‖ ^ k = 1 := by
    intro τ
    have h := key τ
    have h' : χ 1 * ((L : ℂ) * τ + 1) ^ k = 1 := by
      have : (χ 1 * ((L : ℂ) * τ + 1) ^ k - 1) * c = 0 := by rw [sub_mul, ← h]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc0)
    rw [← norm_pow, ← norm_mul, h', norm_one]
  let τ₁ : ℍ := ⟨Complex.I, by simp⟩
  let τ₂ : ℍ := ⟨2 * Complex.I, by simp⟩
  have e1 := hone τ₁
  have e2 := hone τ₂
  have hχ : ‖χ 1‖ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e1; exact zero_ne_one e1
  have heq : ‖(L : ℂ) * τ₁ + 1‖ ^ k = ‖(L : ℂ) * τ₂ + 1‖ ^ k :=
    mul_left_cancel₀ hχ (e1.trans e2.symm)
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hlt : ‖(L : ℂ) * τ₁ + 1‖ < ‖(L : ℂ) * τ₂ + 1‖ := by
    have s1 : ‖(L : ℂ) * τ₁ + 1‖ ^ 2 = 1 + (L : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [τ₁, UpperHalfPlane.coe_mk]
      ring
    have s2 : ‖(L : ℂ) * τ₂ + 1‖ ^ 2 = 1 + 4 * (L : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [τ₂, UpperHalfPlane.coe_mk]
      ring
    have : ‖(L : ℂ) * τ₁ + 1‖ ^ 2 < ‖(L : ℂ) * τ₂ + 1‖ ^ 2 := by
      rw [s1, s2]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
  have := pow_lt_pow_left₀ hlt (norm_nonneg _) (by omega : k ≠ 0)
  exact absurd heq (ne_of_lt this)

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructure
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.Lin

theorem norm_term (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = (Real.exp (-2 * π * τ.im)) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem summ_norm (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := by
  obtain ⟨C, A, hC⟩ := ha
  set r := Real.exp (-2 * π * τ.im) with hr
  have r0 : 0 < r := Real.exp_pos _
  have r1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have := τ.im_pos
    have := Real.pi_pos
    nlinarith
  have hs : Summable fun n : ℕ => ((n : ℝ)) ^ A * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos r0]; exact r1)
  have hs1 : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ A * r ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hs
  have hs2 : Summable fun n : ℕ => C * (((n : ℝ) + 1) ^ A * r ^ n) := by
    apply Summable.mul_left
    have := hs1.mul_right r⁻¹
    refine this.congr (fun n => ?_)
    push_cast
    rw [pow_succ]
    field_simp
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs2
  rw [norm_mul, norm_term, ← hr, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg r0.le _)

theorem summ (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) :=
  (summ_norm a ha τ).of_norm

theorem polyB_zero : PolyB (0 : ℕ → ℂ) := ⟨0, 0, fun n => by simp⟩

theorem polyB_add (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : PolyB (a + b) := by
  obtain ⟨C, A, hC⟩ := ha
  obtain ⟨D, B, hD⟩ := hb
  refine ⟨|C| + |D|, A + B, fun n => ?_⟩
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
  have hA : ((n : ℝ) + 1) ^ A ≤ ((n : ℝ) + 1) ^ (A + B) := pow_le_pow_right₀ h1 (by omega)
  have hB : ((n : ℝ) + 1) ^ B ≤ ((n : ℝ) + 1) ^ (A + B) := pow_le_pow_right₀ h1 (by omega)
  have p0 : 0 ≤ ((n : ℝ) + 1) ^ A := by positivity
  have p1 : 0 ≤ ((n : ℝ) + 1) ^ B := by positivity
  calc ‖(a + b) n‖ ≤ ‖a n‖ + ‖b n‖ := norm_add_le _ _
    _ ≤ C * ((n : ℝ) + 1) ^ A + D * ((n : ℝ) + 1) ^ B := add_le_add (hC n) (hD n)
    _ ≤ |C| * ((n : ℝ) + 1) ^ (A + B) + |D| * ((n : ℝ) + 1) ^ (A + B) := by
        apply add_le_add
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) p0).trans
            (mul_le_mul_of_nonneg_left hA (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self D) p1).trans
            (mul_le_mul_of_nonneg_left hB (abs_nonneg D))
    _ = (|C| + |D|) * ((n : ℝ) + 1) ^ (A + B) := by ring

theorem polyB_smul (c : ℂ) (a : ℕ → ℂ) (ha : PolyB a) : PolyB (c • a) := by
  obtain ⟨C, A, hC⟩ := ha
  refine ⟨‖c‖ * C, A, fun n => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg c)

theorem qs_zero : qs (0 : ℕ → ℂ) = 0 := by
  funext τ; simp [qs]

theorem qs_add (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : qs (a + b) = qs a + qs b := by
  funext τ
  simp only [qs, Pi.add_apply, add_mul]
  exact (summ a ha τ).tsum_add (summ b hb τ)

theorem qs_smul (c : ℂ) (a : ℕ → ℂ) : qs (c • a) = c • qs a := by
  funext τ
  simp only [qs, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem coprime_of_level (L : ℕ) (γ : SL(2, ℤ)) (h : (L : ℤ) ∣ γ 1 0) : IsCoprime (γ 1 1) (L : ℤ) := by
  obtain ⟨m, hm⟩ := h
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  refine ⟨γ 0 0, -(γ 0 1 * m), ?_⟩
  rw [hm] at hdet
  linear_combination hdet

end GlobalTheory.EisM.Lin

open GlobalTheory.EisM.Lin in
theorem GlobalTheory.EisM.mf_linear : ∀ (k L : ℕ) (χ : ℤ → ℂ), (MF k L χ 0) ∧ (∀ a b, MF k L χ a → MF k L χ b → MF k L χ (a + b) ∧ qs (a + b) = qs a + qs b) ∧ (∀ (c : ℂ) a, MF k L χ a → MF k L χ (c • a) ∧ qs (c • a) = c • qs a) ∧ (∀ χ' a, (∀ d : ℤ, IsCoprime d L → χ d = χ' d) → MF k L χ a → MF k L χ' a) ∧ (∀ L' a, L ∣ L' → MF k L χ a → MF k L' χ a) ∧ (∀ L' a, L ∣ L' → CF k L χ a → CF k L' χ a) := by
  intro k L χ
  have lev : ∀ L' a, L ∣ L' → MF k L χ a → MF k L' χ a := by
    intro L' a hL ⟨hp, hi⟩
    refine ⟨hp, fun γ hγ τ => hi γ ?_ τ⟩
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hL) hγ
  refine ⟨⟨polyB_zero, fun γ _ τ => by simp [qs_zero]⟩, ?_, ?_, ?_, lev, ?_⟩
  · intro a b ⟨ha, ia⟩ ⟨hb, ib⟩
    have e := qs_add a b ha hb
    refine ⟨⟨polyB_add a b ha hb, fun γ hγ τ => ?_⟩, e⟩
    rw [e, Pi.add_apply, Pi.add_apply, ia γ hγ τ, ib γ hγ τ]
    ring
  · intro c a ⟨ha, ia⟩
    have e := qs_smul c a
    refine ⟨⟨polyB_smul c a ha, fun γ hγ τ => ?_⟩, e⟩
    rw [e, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ia γ hγ τ]
    ring
  · intro χ' a hχ ⟨ha, ia⟩
    refine ⟨ha, fun γ hγ τ => ?_⟩
    rw [ia γ hγ τ, hχ _ (coprime_of_level L γ hγ)]
  · intro L' a hL ⟨hm, hc⟩
    exact ⟨lev L' a hL hm, hc⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotSummableInvPrimesCongrNegOne
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem sub_one_mul_log_div_rpow_le (n : ℕ) (hn : 1 < n) {x : ℝ} (hx : 1 < x) :
    (x - 1) * (Real.log n / (n : ℝ) ^ x) ≤ 1 / n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans hn)
  have e : (n : ℝ) ^ x = (n : ℝ) ^ (x - 1) * n := by
    rw [Real.rpow_sub_one hp.ne' x]; field_simp
  have hq : 0 < (n : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hp _
  have hl : (x - 1) * Real.log n ≤ (n : ℝ) ^ (x - 1) := by
    rw [Real.rpow_def_of_pos hp]
    have := Real.add_one_le_exp (Real.log n * (x - 1))
    nlinarith [this]
  have hrw : (x - 1) * (Real.log n / (n : ℝ) ^ x) =
      ((x - 1) * Real.log n / (n : ℝ) ^ (x - 1)) * (1 / n) := by
    rw [e]; field_simp
  rw [hrw]
  refine mul_le_of_le_one_left (by positivity) ((div_le_one hq).2 hl)

theorem not_summable_one_div_primes_eq_neg_one :
    ∀ M : ℕ, 0 < M → ¬ Summable fun p : ℕ =>
      if p.Prime ∧ (p : ZMod M) = -1 then (1 : ℝ) / p else 0 := by
  intro M hM hs
  haveI : NeZero M := ⟨hM.ne'⟩
  have hD := Formalism.HF.apLogDensity M (-1 : ZMod M) isUnit_one.neg
  unfold Formalism.HF.LogDensity at hD
  set S := {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod M) = -1}} with hS
  have h0 : Tendsto (fun x : ℝ => ∑' n : ℕ,
      (x - 1) * S.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) (𝓝[>] 1)
      (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun n => ?_) ?_
    · by_cases hn : n ∈ S
      · simp only [Set.indicator_of_mem hn]
        have hp : (0 : ℝ) < n := by exact_mod_cast hn.1.pos
        have hc : Continuous fun x : ℝ => (x - 1) * (Real.log n / (n : ℝ) ^ x) := by
          refine (continuous_id.sub continuous_const).mul (continuous_const.div ?_ ?_)
          · exact continuous_const.rpow continuous_id (fun _ => Or.inl hp.ne')
          · intro x; exact (Real.rpow_pos_of_pos hp x).ne'
        have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
        simpa using this
      · simp only [Set.indicator_of_notMem hn, mul_zero]
        exact tendsto_const_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx n
      have hx : (1 : ℝ) < x := hx
      by_cases hn : n ∈ S
      · have hc : n.Prime ∧ (n : ZMod M) = -1 := hn
        simp only [Set.indicator_of_mem hn, if_pos hc]
        have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hc.1.one_lt.le)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith)
          (div_nonneg hlog (Real.rpow_nonneg n.cast_nonneg _)))]
        exact sub_one_mul_log_div_rpow_le n hc.1.one_lt hx
      · have hc : ¬ (n.Prime ∧ (n : ZMod M) = -1) := hn
        simp only [Set.indicator_of_notMem hn, if_neg hc, mul_zero, norm_zero, le_refl]
  simp only [tsum_zero, tsum_mul_left] at h0
  have hu := tendsto_nhds_unique hD h0
  have ht : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.2 hM
  rw [one_div] at hu
  exact (inv_pos.2 ht).ne' hu

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowth
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem polyB_summable_norm_mul_pow {a : ℕ → ℂ} (ha : PolyB a) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ‖a n‖ * r ^ n := by
  obtain ⟨C, A, h⟩ := ha
  have hs : Summable fun n : ℕ => C * 2 ^ A * ((n : ℝ) ^ A * r ^ n + r ^ n) := by
    refine Summable.mul_left _ (Summable.add ?_ ?_)
    · exact summable_pow_mul_geometric_of_norm_lt_one A (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    · exact summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 _)) (fun n => ?_) hs
  have hb : ((n : ℝ) + 1) ^ A ≤ 2 ^ A * ((n : ℝ) ^ A + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_add, one_pow]
      have : (1 : ℝ) ≤ 2 ^ A := one_le_pow₀ (by norm_num)
      nlinarith [pow_nonneg (le_refl (0:ℝ)) A]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : ((n : ℝ) + 1) ^ A ≤ (2 * n) ^ A := pow_le_pow_left₀ (by positivity) (by linarith) A
      rw [mul_pow] at this
      nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) A]
  have hC : 0 ≤ C := le_trans (norm_nonneg _) ((h 0).trans (by simp))
  calc ‖a n‖ * r ^ n ≤ C * ((n : ℝ) + 1) ^ A * r ^ n :=
        mul_le_mul_of_nonneg_right (h n) (pow_nonneg hr0 _)
    _ ≤ C * (2 ^ A * ((n : ℝ) ^ A + 1)) * r ^ n := by gcongr
    _ = C * 2 ^ A * ((n : ℝ) ^ A * r ^ n + r ^ n) := by ring

theorem exists_upperHalfPlane_exp_eq {q : ℂ} (h0 : q ≠ 0) (h1 : ‖q‖ < 1) :
    ∃ τ : ℍ, ∀ n : ℕ, cexp (2 * π * Complex.I * n * τ) = q ^ n := by
  have hπ : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have him : 0 < (Complex.log q / (2 * π * Complex.I)).im := by
    have e : Complex.log q / (2 * π * Complex.I) = -Complex.I * Complex.log q / (2 * π) := by
      field_simp
      ring_nf
      simp [Complex.I_sq]
    rw [e]
    have : (-Complex.I * Complex.log q / (2 * π)).im = - (Complex.log q).re / (2 * π) := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]
      simp
    rw [this, Complex.log_re]
    have hl : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.mpr h0) h1
    have : 0 < 2 * π := by positivity
    apply div_pos (by simpa using hl) this
  refine ⟨⟨_, him⟩, fun n => ?_⟩
  have : 2 * π * Complex.I * (n : ℂ) * ((⟨_, him⟩ : ℍ) : ℂ) = n * Complex.log q := by
    simp only [UpperHalfPlane.coe_mk]
    field_simp
  rw [this, Complex.exp_nat_mul, Complex.exp_log h0]

theorem qs_injective : ∀ a b : ℕ → ℂ, PolyB a → PolyB b → qs a = qs b → a = b := by
  intro a b ha hb hab
  set c : ℕ → ℂ := fun n => a n - b n with hcdef
  have hsum : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun n : ℕ => ‖c n‖ * r ^ n := by
    intro r h0 h1
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg h0 _)) (fun n => ?_)
      ((polyB_summable_norm_mul_pow ha h0 h1).add (polyB_summable_norm_mul_pow hb h0 h1))
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg h0 _)
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hrad : ((1 / 2 : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable_norm ?_
    have := hsum (1 / 2) (by norm_num) (by norm_num)
    refine this.congr (fun n => ?_)
    rw [hp, FormalMultilinearSeries.ofScalars_norm]
    simp
  have hpos : 0 < p.radius := lt_of_lt_of_le (by simp) hrad
  have hP := p.hasFPowerSeriesOnBall hpos
  have hval : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → p.sum q = 0 := by
    intro q h0 h1
    obtain ⟨τ, hτ⟩ := exists_upperHalfPlane_exp_eq h0 h1
    have ha' : Summable fun n => a n * q ^ n := Summable.of_norm (by
      simpa [norm_mul, norm_pow] using polyB_summable_norm_mul_pow ha (norm_nonneg q) h1)
    have hb' : Summable fun n => b n * q ^ n := Summable.of_norm (by
      simpa [norm_mul, norm_pow] using polyB_summable_norm_mul_pow hb (norm_nonneg q) h1)
    have e := congrFun hab τ
    simp only [qs, hτ] at e
    show ∑' n, p n (fun _ => q) = 0
    simp only [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, hcdef, sub_mul]
    rw [Summable.tsum_sub ha' hb', e, sub_self]
  have hcont : ContinuousAt p.sum 0 := hP.continuousOn.continuousAt (EMetric.ball_mem_nhds 0 hpos)
  have h0 : p.sum 0 = 0 := by
    have hev : p.sum =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)]
        with q hq0 hq1
      exact hval q hq0 (by simpa using hq1)
    exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hev.symm)
  have hloc : p.sum =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact h0
    · exact hval q hq0 (by simpa using hq)
  have hpz : p = 0 := hP.hasFPowerSeriesAt.eq_zero_of_eventually hloc
  funext n
  have hn : p n = 0 := by rw [hpz]; rfl
  have : c n = 0 := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp hn
  exact sub_eq_zero.mp this

end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuous
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem qterm_norm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-2 * π * τ.im) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem summable_succ_pow_mul_geom (A : ℕ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r ^ n := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ A * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos h0]; exact h1)
  have hs' : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ A * r ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hs
  have := hs'.mul_left r⁻¹
  refine this.congr fun n => ?_
  push_cast
  rw [pow_succ]
  field_simp

theorem qterm_bound {a : ℕ → ℂ} {C : ℝ} {A : ℕ} (hC : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A)
    {y₀ : ℝ} (n : ℕ) (τ : ℍ) (hτ : y₀ ≤ τ.im) :
    ‖a n * cexp (2 * π * Complex.I * n * τ)‖ ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
  rw [norm_mul, qterm_norm]
  have h1 : Real.exp (-2 * π * τ.im) ^ n ≤ Real.exp (-2 * π * y₀) ^ n := by
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos]
  calc ‖a n‖ * Real.exp (-2 * π * τ.im) ^ n ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * τ.im) ^ n :=
        mul_le_mul_of_nonneg_right (hC n) (by positivity)
    _ ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
        apply mul_le_mul_of_nonneg_left h1
        exact le_trans (norm_nonneg _) (hC n)

theorem qterm_summable_bound {C : ℝ} (A : ℕ) {y₀ : ℝ} (hy : 0 < y₀) :
    Summable fun n : ℕ => C * ((n : ℝ) + 1) ^ A * Real.exp (-2 * π * y₀) ^ n := by
  have h := summable_succ_pow_mul_geom A (r := Real.exp (-2 * π * y₀)) (Real.exp_pos _)
    (Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos]))
  simpa [mul_assoc] using h.mul_left C

theorem qs_summable_continuous : ∀ a : ℕ → ℂ, PolyB a →
    (∀ τ : ℍ, Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖) ∧ Continuous (qs a) := by
  intro a ⟨C, A, hC⟩
  refine ⟨fun τ => ?_, ?_⟩
  · exact (qterm_summable_bound (C := C) A τ.im_pos).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => qterm_bound hC n τ le_rfl)
  · rw [continuous_iff_continuousAt]
    intro τ₀
    have hy : 0 < τ₀.im / 2 := half_pos τ₀.im_pos
    have hopen : IsOpen {τ : ℍ | τ₀.im / 2 < τ.im} :=
      isOpen_lt continuous_const UpperHalfPlane.continuous_im
    have hmem : τ₀ ∈ {τ : ℍ | τ₀.im / 2 < τ.im} := by
      show τ₀.im / 2 < τ₀.im
      linarith [τ₀.im_pos]
    have hon : ContinuousOn (qs a) {τ : ℍ | τ₀.im / 2 < τ.im} := by
      unfold qs
      refine continuousOn_tsum (fun n => ?_) (qterm_summable_bound (C := C) A hy) ?_
      · apply Continuous.continuousOn
        fun_prop
      · intro n τ hτ
        exact qterm_bound hC n τ (le_of_lt hτ)
    exact hon.continuousAt (hopen.mem_nhds hmem)

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSumIccInvResidueCotStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_sum_Icc_inv_add_mul_eq_pi_div_mul_cot : ∀ (L : ℕ) (z : ℂ) (r : ℕ), 0 < L → 0 < z.im → Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹) atTop (𝓝 (π / L * Complex.cot (π * ((z + r) / L)))) := by
  first | exact @GlobalTheory.tendsto_sum_Icc_inv_residue_cot | exact GlobalTheory.tendsto_sum_Icc_inv_residue_cot | (intros; apply GlobalTheory.tendsto_sum_Icc_inv_residue_cot <;> assumption)
end

