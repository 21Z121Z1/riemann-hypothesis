import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PNormUbar
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

theorem NormUbar.proof : NormUbar.Statement := by
  intro d u τ
  have hN : (d.N : ℝ) ≠ 0 := by
    have := d.two_le_N
    exact_mod_cast (by omega : d.N ≠ 0)
  have hNpos : (0 : ℝ) ≤ d.N := Nat.cast_nonneg _
  have key : (d.N : ℝ) * |ubar d u τ| = |∑ i : Fin d.N, u (τ, i)| := by
    unfold ubar
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (d.N : ℝ)), ← mul_assoc,
      mul_one_div_cancel hN, one_mul]
  rw [key]
  exact abs_sum_le_sum_abs _ _

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PRestPBound
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

def restCoeffBound (d : IndexData) (Q : ℕ → Fin d.f → XPoly d) (τ : Fin d.f) (k : ℕ) : ℝ :=
  ∑ e : Emb d, |((((k : ℚ) * intFl d (liePowerSum d (k - 1) e * Q k τ) : ℚ) : ℝ))|

theorem restCoeffBound_nonneg (d : IndexData) (Q : ℕ → Fin d.f → XPoly d) (τ : Fin d.f) (k : ℕ) :
    0 ≤ restCoeffBound d Q τ k :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem restSeries_abs_le (d : IndexData) (p : ℕ) (hp : 1 ≤ p) (φ : Equiv.Perm (Emb d))
    (Q : ℕ → Fin d.f → XPoly d) (τ : Fin d.f) (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    |restSeries d p φ Q τ k n| ≤ restCoeffBound d Q τ k * ((p : ℝ) ^ 2)⁻¹ ^ (n + 1) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < p := by linarith
  calc |restSeries d p φ Q τ k n|
      = |((((k : ℚ) * intFl d (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * Q k τ) : ℚ) : ℝ))| *
          ((p : ℝ) ^ ((n + 1) * k))⁻¹ := by
        unfold restSeries
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((p : ℝ) ^ ((n + 1) * k))⁻¹), mul_comm]
    _ ≤ restCoeffBound d Q τ k * ((p : ℝ) ^ 2)⁻¹ ^ (n + 1) := by
        apply mul_le_mul
        · unfold restCoeffBound
          exact Finset.single_le_sum
            (f := fun e : Emb d => |((((k : ℚ) * intFl d (liePowerSum d (k - 1) e * Q k τ) : ℚ) : ℝ))|)
            (fun e _ => abs_nonneg _) (mem_univ ((φ ^ (n + 1)) (τ, false)))
        · rw [inv_pow, ← pow_mul]
          apply inv_anti₀ (by positivity)
          apply pow_le_pow_right₀ hp'
          rw [mul_comm]
          exact Nat.mul_le_mul_left _ hk
        · positivity
        · exact restCoeffBound_nonneg d Q τ k

theorem restSeries_tsum_bound (d : IndexData) (p : ℕ) (hp : p.Prime) (φ : Equiv.Perm (Emb d))
    (Q : ℕ → Fin d.f → XPoly d) (τ : Fin d.f) (k : ℕ) (hk : 2 ≤ k) :
    Summable (restSeries d p φ Q τ k) ∧
      |∑' n : ℕ, restSeries d p φ Q τ k n| ≤ restCoeffBound d Q τ k * (2 * ((p : ℝ) ^ 2)⁻¹) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ((p : ℝ) ^ 2)⁻¹ := ⟨_, rfl⟩
  rw [← hr]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 / 2 := by
    have h4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    rw [hr]
    calc ((p : ℝ) ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h4
      _ ≤ 1 / 2 := by norm_num
  have hM := restCoeffBound_nonneg d Q τ k
  have hb : ∀ n : ℕ, |restSeries d p φ Q τ k n| ≤ restCoeffBound d Q τ k * (r * r ^ n) := by
    intro n
    rw [← pow_succ', hr]
    exact restSeries_abs_le d p hp.one_lt.le φ Q τ k hk n
  have hg : Summable (fun n : ℕ => restCoeffBound d Q τ k * (r * r ^ n)) :=
    ((summable_geometric_of_lt_one hr0 (by linarith)).mul_left r).mul_left _
  have hs : Summable (restSeries d p φ Q τ k) :=
    Summable.of_norm_bounded hg (fun n => by rw [Real.norm_eq_abs]; exact hb n)
  have habs : Summable (fun n : ℕ => |restSeries d p φ Q τ k n|) :=
    Summable.of_norm_bounded hg (fun n => by rw [Real.norm_eq_abs, abs_abs]; exact hb n)
  refine ⟨hs, ?_⟩
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc |∑' n : ℕ, restSeries d p φ Q τ k n|
      ≤ ∑' n : ℕ, |restSeries d p φ Q τ k n| := by
        have := norm_tsum_le_tsum_norm (f := restSeries d p φ Q τ k)
          (by simpa only [Real.norm_eq_abs] using habs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' n : ℕ, restCoeffBound d Q τ k * (r * r ^ n) := Summable.tsum_le_tsum hb habs hg
    _ = restCoeffBound d Q τ k * (r * (1 - r)⁻¹) := by
        rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
    _ ≤ restCoeffBound d Q τ k * (2 * r) := by
        apply mul_le_mul_of_nonneg_left _ hM
        calc r * (1 - r)⁻¹ ≤ r * 2 := mul_le_mul_of_nonneg_left hinv hr0
          _ = 2 * r := mul_comm _ _

theorem RestPBound.proof : RestPBound.Statement := by
  intro d vol F Q _
  refine ⟨2 * |vol| * ∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, restCoeffBound d Q τ k, ?_⟩
  intro p φ hp
  have key : ∀ τ : Fin d.f, ∀ k ∈ Icc 2 d.N,
      Summable (restSeries d p φ Q τ k) ∧
        |∑' n : ℕ, restSeries d p φ Q τ k n| ≤ restCoeffBound d Q τ k * (2 * ((p : ℝ) ^ 2)⁻¹) :=
    fun τ k hk => restSeries_tsum_bound d p hp φ Q τ k (mem_Icc.mp hk).1
  refine ⟨fun τ k hk => (key τ k hk).1, ?_⟩
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hsum : |∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, ∑' n : ℕ, restSeries d p φ Q τ k n| ≤
      ∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, restCoeffBound d Q τ k * (2 * ((p : ℝ) ^ 2)⁻¹) :=
    calc |∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, ∑' n : ℕ, restSeries d p φ Q τ k n|
        ≤ ∑ τ : Fin d.f, |∑ k ∈ Icc 2 d.N, ∑' n : ℕ, restSeries d p φ Q τ k n| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, |∑' n : ℕ, restSeries d p φ Q τ k n| :=
          sum_le_sum fun τ _ => abs_sum_le_sum_abs _ _
      _ ≤ _ := sum_le_sum fun τ _ => sum_le_sum fun k hk => (key τ k hk).2
  calc |rest₂ d vol p φ Q|
      = Real.log p * |vol| * |∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, ∑' n : ℕ, restSeries d p φ Q τ k n| := by
        unfold rest₂
        rw [abs_mul, abs_mul, abs_of_nonneg hlog]
    _ ≤ Real.log p * |vol| *
          ∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, restCoeffBound d Q τ k * (2 * ((p : ℝ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hlog (abs_nonneg _))
    _ = 2 * |vol| * (∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, restCoeffBound d Q τ k) * Real.log p /
          (p : ℝ) ^ 2 := by
        simp only [← Finset.sum_mul]
        rw [div_eq_mul_inv]
        ring

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PRestSummable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

theorem summable_log_div_sq : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _))
    (fun n => ?_) ((Real.summable_nat_rpow.2 (by norm_num : (-(3 / 2) : ℝ) < -1)).mul_left 2)
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Real.log_le_rpow_div hx.le one_half_pos
  have key : (n : ℝ) ^ (-(3 / 2) : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hx]
    norm_num
  rw [key]
  calc Real.log n / (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ = 2 * ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2) := by ring

theorem RestSummable.proof (hB : RestPBound.Statement) : RestSummable.Statement := by
  intro d S B0 F Q hQ
  obtain ⟨c, hc⟩ := hB d S.vol F Q hQ
  have hg : Summable (fun p : primesAbove S B0 =>
      |c| * (Real.log (p : ℕ) / (((p : ℕ) : ℝ)) ^ 2)) :=
    (summable_log_div_sq.subtype (primesAbove S B0)).mul_left |c|
  refine Summable.of_nonneg_of_le (fun p => abs_nonneg _) (fun p => ?_) hg
  have h := (hc p.1 (S.frob p.1) p.2.1).2
  calc |rest₂ d S.vol p (S.frob p) Q| ≤ c * Real.log (p : ℕ) / (((p : ℕ) : ℝ)) ^ 2 := h
    _ ≤ |c| * (Real.log (p : ℕ) / (((p : ℕ) : ℝ)) ^ 2) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (le_abs_self c)
          (div_nonneg (Real.log_natCast_nonneg _) (sq_nonneg _))

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PShTotIndependent
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

variable (d : IndexData)

def shTotForm (a b : Fin d.f → ℚ) : MvPolynomial (Idx d) ℚ :=
  ∑ τ : Fin d.f, (C (a τ) * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), X (τ, i) +
    C (b τ) * ∑ i : Fin d.N, X (τ, i))

theorem lineClass_isHomogeneous (u : Idx d → ℚ) : (lineClass d u).IsHomogeneous 1 :=
  (IsHomogeneous.sum _ _ _ (fun p _ => isHomogeneous_C_mul_X (u p) p)).neg

theorem lineClass_pow_mem (u : Idx d → ℚ) : lineClass d u ^ (d.D + 1) ∈ topSpace d := by
  rw [mem_homogeneousSubmodule]
  simpa using (lineClass_isHomogeneous d u).pow (d.D + 1)

theorem eval_shTotForm_single (a b : Fin d.f → ℚ) (τ : Fin d.f) (i : Fin d.N) :
    eval (fun p => if p = (τ, i) then (1 : ℚ) else 0) (shTotForm d a b) =
      (if i.val < d.j then a τ else 0) + b τ := by
  simp only [shTotForm, map_sum, map_add, map_mul, eval_C, eval_X]
  rw [Finset.sum_eq_single τ]
  · simp [Finset.mem_filter]
  · intro τ' _ hne
    simp [hne]
  · simp

theorem shOn_apply (τ : Fin d.f) (F : topSpace d) : shOn d τ F = shiftFl d τ F := rfl

theorem totOn_apply (τ : Fin d.f) (F : topSpace d) : totOn d τ F = totalFl d τ F := rfl

theorem shTot_relation_trivial (hSh : ShOfPower.Statement) (hTot : TotOfPower.Statement)
    (hEval : DegPolyEval.Statement) (hC : CFlPos.Statement) (a b : Fin d.f → ℚ)
    (hab : ∑ τ, a τ • shOn d τ + ∑ τ, b τ • totOn d τ = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨c, hc, hdeg⟩ := hC d
  have hD : ((d.D + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hval : ∀ u : Idx d → ℚ, eval u (degPoly d * shTotForm d a b) = 0 := by
    intro u
    have h1 := LinearMap.congr_fun hab ⟨_, lineClass_pow_mem d u⟩
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, smul_eq_mul, shOn_apply, totOn_apply, hSh d, hTot d] at h1
    rw [eval_mul, hEval, shTotForm]
    simp only [map_sum, map_add, map_mul, eval_C, eval_X]
    have h2 : -((d.D + 1 : ℕ) : ℚ) * (degAt d u * ∑ τ : Fin d.f,
        (a τ * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), u (τ, i) +
          b τ * ∑ i : Fin d.N, u (τ, i))) = 0 := by
      rw [← h1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun τ _ => by ring)
    exact (mul_eq_zero.mp h2).resolve_left (neg_ne_zero.mpr hD)
  have hzero : degPoly d * shTotForm d a b = 0 :=
    MvPolynomial.funext (fun u => by rw [hval u, map_zero])
  rw [hdeg, mul_assoc] at hzero
  have hform : shTotForm d a b = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (C_eq_zero.mp h) hc.ne'
    · exact (mul_eq_zero.mp h).resolve_left (RestTerms.Flag.blockVandermonde_ne_zero _ _)
  have hb : ∀ τ, b τ = 0 := by
    intro τ
    have h := eval_shTotForm_single d a b τ ⟨d.N - 1, by have := d.two_le_N; omega⟩
    rw [hform, map_zero, if_neg (by have := d.j_lt_N; simp; omega), zero_add] at h
    exact h.symm
  refine ⟨funext fun τ => ?_, funext hb⟩
  have h := eval_shTotForm_single d a b τ ⟨0, by have := d.two_le_N; omega⟩
  rw [hform, map_zero, if_pos (by have := d.one_le_j; simp; omega), hb τ, add_zero] at h
  exact h.symm

theorem ShTotIndependent.proof (hSh : ShOfPower.Statement) (hTot : TotOfPower.Statement)
    (hEval : DegPolyEval.Statement) (hC : CFlPos.Statement) : ShTotIndependent.Statement := by
  intro d hf
  have key := shTot_relation_trivial d hSh hTot hEval hC
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have h := key (fun τ => g (Sum.inl τ)) (fun τ => g (Sum.inr τ))
      (by simpa [Fintype.sum_sum_type] using hg)
    rintro (τ | τ)
    · exact congrFun h.1 τ
    · exact congrFun h.2 τ
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.smul_sum] at hg
    have h := key (fun _ => g 0) (fun _ => g 1) hg
    intro i
    fin_cases i
    · exact congrFun h.1 ⟨0, hf⟩
    · exact congrFun h.2 ⟨0, hf⟩

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PShTotInvertiblePair
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem ShTotInvertiblePair.proof (h : ShTotIndependent.Statement) :
    ShTotInvertiblePair.Statement := by
  intro d hf
  have hli := LinearIndependent.pair_iff.mp (h d hf).2
  set S : topSpace d →ₗ[ℚ] ℚ := ∑ τ : Fin d.f, shOn d τ with hS
  set T : topSpace d →ₗ[ℚ] ℚ := ∑ τ : Fin d.f, totOn d τ with hT
  have hSapp : ∀ x : topSpace d, S x = shSum d x.1 := by
    intro x
    simp [hS, LinearMap.sum_apply, shOn, shLin, shSum]
  have hTapp : ∀ x : topSpace d, T x = totSum d x.1 := by
    intro x
    simp [hT, LinearMap.sum_apply, totOn, totLin, totSum]
  by_contra hne
  push Not at hne
  have key : ∀ x y : topSpace d, S x * T y - T x * S y = 0 := by
    intro x y
    rw [hSapp, hSapp, hTapp, hTapp]
    exact hne x.1 y.1 ((mem_homogeneousSubmodule _ _).mp x.2)
      ((mem_homogeneousSubmodule _ _).mp y.2)
  obtain ⟨x, hx⟩ : ∃ x : topSpace d, S x ≠ 0 := by
    by_contra h0
    push Not at h0
    have h1 := hli 1 0 (by
      ext y
      simp [h0 y])
    exact one_ne_zero h1.1
  have h2 := hli (T x) (-(S x)) (by
    ext y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
    linear_combination -(key x y))
  exact hx (neg_eq_zero.mp h2.2)

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTermB
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

theorem TermB.proof : TermB.Statement := by
  intro d S u g B0 _hyp _hB0 hM5 Q hQ
  obtain ⟨hsum, hle⟩ := hM5 Q hQ
  have hsum' : Summable (fun p : primesAbove S B0 =>
      ‖rest₂ d S.vol (p : ℕ) (S.frob p) Q‖) := by
    simpa [Real.norm_eq_abs] using hsum
  have h1 : ‖restTot S B0 Q‖ ≤ ∑' p : primesAbove S B0, ‖rest₂ d S.vol (p : ℕ) (S.frob p) Q‖ :=
    norm_tsum_le_tsum_norm hsum'
  have h2 : |restTot S B0 Q| ≤ ∑' p : primesAbove S B0, |rest₂ d S.vol (p : ℕ) (S.frob p) Q| := by
    simpa [Real.norm_eq_abs] using h1
  exact h2.trans hle

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTermC
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

theorem flagNormalisation_ne_zero (f N : ℕ) : flagNormalisation f N ≠ 0 := by
  unfold flagNormalisation
  refine div_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ?_)
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

theorem flagIntegral_blockVandermonde_pos (f N : ℕ) :
    0 < RestTerms.flagIntegral f N (RestTerms.blockVandermonde f N) := by
  unfold RestTerms.flagIntegral
  have hne : (RestTerms.blockVandermonde f N).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact RestTerms.Flag.blockVandermonde_ne_zero f N
  refine Finset.sum_pos (fun α hα => ?_) hne
  have hc : coeff α (RestTerms.blockVandermonde f N) ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  refine mul_pos (mul_self_pos.mpr hc) ?_
  exact Finset.prod_pos fun i _ => by dsimp only; exact_mod_cast Nat.factorial_pos _

theorem exists_intFl_eq_one (d : IndexData) :
    ∃ Q : XPoly d, Q.IsHomogeneous d.D ∧ intFl d Q = 1 := by
  set Δ : XPoly d := RestTerms.blockVandermonde d.f d.N
  have hΔ : Δ.IsHomogeneous d.D := RestTerms.FlagVandermondeHomogeneous.proof d.f d.N
  have hval : intFl d Δ = flagNormalisation d.f d.N * RestTerms.flagIntegral d.f d.N Δ := rfl
  have hc : intFl d Δ ≠ 0 := by
    rw [hval]
    exact mul_ne_zero (flagNormalisation_ne_zero _ _)
      (flagIntegral_blockVandermonde_pos d.f d.N).ne'
  refine ⟨(intFl d Δ)⁻¹ • Δ, ?_, ?_⟩
  · have hm : Δ ∈ homogeneousSubmodule (Idx d) ℚ d.D := (mem_homogeneousSubmodule _ _).mpr hΔ
    exact (mem_homogeneousSubmodule _ _).mp (Submodule.smul_mem _ _ hm)
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hc]

theorem TermC.proof (h₁ : HeightLimitIdentity.Statement) : TermC.Statement := by
  intro d S h82 hfl B0 A0 b0 hA hb hF
  obtain ⟨Q, hQ, hQ1⟩ := exists_intFl_eq_one d
  have e := h₁ d S h82 hfl B0 A0 b0 hA hb (tau0 S) Q hQ hQ1
  have hv : S.vol ≠ 0 := S.vol_pos.ne'
  have hval : (d.j : ℝ) * A0 + (d.N : ℝ) * b0 = -S.hB B0 := by
    rw [e, hF.1 (tau0 S) Q hQ, hQ1]
    field_simp
    push_cast
    ring
  rw [hval, abs_neg]
  exact hF.2

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTermD
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset Filter Topology

theorem termD_term_le {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) ≤ 2 * (Real.log p / p) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp0 : (0 : ℝ) < p := by linarith
  rw [mul_div_assoc', div_le_div_iff₀ hden hp0]
  nlinarith [mul_nonneg hlog (by nlinarith : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 2)]

theorem TermD.proof : TermD.Statement := by
  intro C7 hC7
  refine ⟨2 + C7 / Real.log 2, ?_⟩
  intro d S B0 A0 hB0 h7 hA
  obtain ⟨hlow, -⟩ := h7 A0 hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB0r : (2 : ℝ) ≤ B0 := by exact_mod_cast hB0
  have hlogB : Real.log 2 ≤ Real.log B0 := Real.log_le_log (by norm_num) hB0r
  have hC7le : C7 ≤ C7 / Real.log 2 * Real.log B0 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hlogB hC7
  have hsum : ∑ p ∈ S.level.primeFactors.filter (fun p => B0 < p),
        (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) ≤
      2 * ∑ p ∈ S.level.primeFactors, Real.log p / (p : ℝ) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ p ∈ S.level.primeFactors.filter (fun p => B0 < p), 2 * (Real.log p / p) :=
          Finset.sum_le_sum fun p hp =>
            termD_term_le (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).two_le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => mul_nonneg zero_le_two
            (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)))
  have hS0 : 0 ≤ ∑ p ∈ S.level.primeFactors, Real.log p / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hlogB0 : 0 ≤ Real.log B0 := le_trans hl2.le hlogB
  have hCpos : 0 ≤ C7 / Real.log 2 := div_nonneg hC7 hl2.le
  nlinarith [mul_nonneg hCpos hS0]

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsHomDecomp
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial

def HomDecompExists.Statement : Prop :=
  ∀ (d : IndexData) (F : XPoly d), F.IsHomogeneous (d.D + 1) →
    ∃ Q : ℕ → Fin d.f → XPoly d, IsHomDecomp d F Q

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsShTotSmall
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

def ShTotInvertiblePairSmall.Statement : Prop :=
  ∀ d : IndexData, 0 < d.f → ¬ d.TextRange →
    ∃ F1 F2 : XPoly d, F1.IsHomogeneous (d.D + 1) ∧ F2.IsHomogeneous (d.D + 1) ∧
      shSum d F1 * totSum d F2 - totSum d F1 * shSum d F2 ≠ 0

end GroundTheory.Heights₂.Heights.TheoremB
end
end

