import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SizePowerLeInverseSquareProduct
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem sizeE_zpow_le_prod_inv_sq (r n B N : ℕ) (cs : List (Fin r)) (m : Fin r → ℕ)
    (hN : n * B + 2 ≤ N) (hc : ∀ i, cs.count i = N ∨ m i = 0) :
    sizeE (fun i => (m i : ℝ)) ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) ≤
      ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
  have hcount : ∀ l : List (Fin r), ∑ i, l.count i = l.length := by
    intro l
    first
      | simpa using Multiset.sum_count_eq_card (l : Multiset (Fin r))
      | (induction l with
          | nil => simp
          | cons a t ih => simp [List.count_cons, Finset.sum_add_distrib, ih])
  set S := sizeE (fun i => (m i : ℝ)) with hSdef
  have hSval : S = 1 + ∑ i, (m i : ℝ) := rfl
  have hsum0 : 0 ≤ ∑ i, (m i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hS1 : 1 ≤ S := by rw [hSval]; linarith
  have hmS : ∀ i, 1 + (m i : ℝ) ≤ S := by
    intro i
    rw [hSval]
    have := Finset.single_le_sum (f := fun j => (m j : ℝ)) (fun j _ => Nat.cast_nonneg (m j)) (Finset.mem_univ i)
    linarith
  set K := Finset.univ.filter (fun i => m i ≠ 0) with hKdef
  set k := K.card with hkdef
  have hg : ∏ i, (if m i ≠ 0 then (S ^ 2)⁻¹ else (1 : ℝ)) = ((S ^ 2)⁻¹) ^ k := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hle : ∏ i, (if m i ≠ 0 then (S ^ 2)⁻¹ else (1 : ℝ)) ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
    apply Finset.prod_le_prod
    · intro i _
      split_ifs
      · positivity
      · norm_num
    · intro i _
      split_ifs with hi
      · exact inv_anti₀ (by positivity) (by gcongr; exact hmS i)
      · rw [ne_eq, not_not] at hi
        simp [hi]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · have hm : ∀ i, m i = 0 := by
      intro i
      by_contra hi
      have hiK : i ∈ K := by simp [hKdef, hi]
      rw [Finset.card_eq_zero.mp hk] at hiK
      simp at hiK
    have hS : S = 1 := by rw [hSval]; simp [hm]
    calc S ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) = ((S ^ 2)⁻¹) ^ k := by rw [hS, hk]; simp
      _ ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by rw [← hg]; exact hle
  · have hKsum : ∑ i ∈ K, cs.count i = k * N := by
      have hKN : ∀ i ∈ K, cs.count i = N := fun i hi => (hc i).resolve_right (Finset.mem_filter.mp hi).2
      rw [Finset.sum_congr rfl hKN, Finset.sum_const, smul_eq_mul]
    have hLk : k * N ≤ cs.length := by
      rw [← hKsum, ← hcount cs]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ K)
    have h2 : n * B ≤ n * B * k := Nat.le_mul_of_pos_right _ hk
    have hA : n * B + 2 * k ≤ cs.length :=
      calc n * B + 2 * k ≤ n * B * k + 2 * k := Nat.add_le_add_right h2 _
        _ = (n * B + 2) * k := by ring
        _ ≤ N * k := Nat.mul_le_mul_right k hN
        _ = k * N := Nat.mul_comm _ _
        _ ≤ cs.length := hLk
    have hexp : (n : ℤ) * (B : ℤ) - (cs.length : ℤ) ≤ -(2 * (k : ℤ)) := by
      have hcast : ((n * B + 2 * k : ℕ) : ℤ) ≤ (cs.length : ℤ) := by exact_mod_cast hA
      push_cast at hcast
      linarith
    have hz : S ^ (-(2 * (k : ℤ))) = ((S ^ 2)⁻¹) ^ k := by
      rw [zpow_neg, show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul, inv_pow]
    calc S ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) ≤ S ^ (-(2 * (k : ℤ))) := zpow_le_zpow_right₀ hS1 hexp
      _ = ((S ^ 2)⁻¹) ^ k := hz
      _ = ∏ i, (if m i ≠ 0 then (S ^ 2)⁻¹ else (1 : ℝ)) := hg.symm
      _ ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := hle

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableInverseSquareProduct
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem summable_inv_one_add_sq :
    Summable (fun n : ℕ => ((1 + (n : ℝ)) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine ((summable_nat_add_iff 1).mpr h).congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one, one_div, add_comm (n : ℝ) 1]

theorem summable_prod_inv_one_add_sq :
    ∀ r : ℕ, Summable (fun m : Fin r → ℕ => ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹) := by
  intro r
  induction r with
  | zero => exact Summable.of_finite
  | succ r ih =>
    have h := GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_inv_one_add_sq.mul_of_nonneg ih
      (fun n => inv_nonneg.mpr (sq_nonneg _))
      (fun m => Finset.prod_nonneg fun i _ => inv_nonneg.mpr (sq_nonneg _))
    rw [← (Fin.consEquiv fun _ : Fin (r + 1) => ℕ).summable_iff]
    refine h.congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, mul_comm]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummationOperatorsBoundedGood
section
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.AopProps

variable {r : ℕ}

lemma update_add_single (i : Fin r) (m : Fin r → ℕ) (t k : ℕ) :
    Function.update (m + (Pi.single i t : Fin r → ℕ)) i k = Function.update m i k := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

lemma add_single_eq_update (i : Fin r) (m : Fin r → ℕ) (t : ℕ) :
    m + (Pi.single i t : Fin r → ℕ) = Function.update m i (m i + t) := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

lemma partialSum_update (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (k : ℕ) :
    partialSum i v (Function.update m i k) =
      ∑ j ∈ Finset.range k, v (Function.update m i j) := by
  simp [partialSum]

lemma partialSum_periodic {l : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (hv : GoodAt l i v)
    (m : Fin r → ℕ) (k : ℕ) :
    partialSum i v (Function.update m i (k + l)) = partialSum i v (Function.update m i k) := by
  rw [partialSum_update, partialSum_update, Finset.sum_range_add]
  have h := hv.2 (Function.update m i k)
  have h2 : ∑ x ∈ Finset.range l, v (Function.update m i (k + x)) = 0 := by
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_single_eq_update, Function.update_self, Function.update_idem]
  rw [h2, add_zero]

lemma sum_window {l : ℕ} (f : ℕ → ℚ) (hf : ∀ k, f (k + l) = f k) (a : ℕ) :
    ∑ k ∈ Finset.range l, f (a + k) = ∑ k ∈ Finset.range l, f k :=
  _root_.UpperTheory.Reformulated.B.DYdd7.main f hf a

lemma partialSumMean_add_single (l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (t : ℕ) :
    meanP l i v (m + (Pi.single i t : Fin r → ℕ)) = meanP l i v m := by
  simp only [meanP, update_add_single]

lemma partialSum_abs_le (i : Fin r) (v : (Fin r → ℕ) → ℚ) {C : ℝ}
    (hC : ∀ m, |(v m : ℝ)| ≤ C) (m : Fin r → ℕ) (k : ℕ) :
    |((partialSum i v (Function.update m i k) : ℚ) : ℝ)| ≤ k * C := by
  rw [partialSum_update]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ C fun j _ => hC _).trans ?_
  simp

lemma partialSum_bound {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ)
    (hv : GoodAt l i v) {C : ℝ} (hC : ∀ m, |(v m : ℝ)| ≤ C) (m : Fin r → ℕ) :
    |((partialSum i v m : ℚ) : ℝ)| ≤ l * C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC m)
  have hper : Function.Periodic (fun k => partialSum i v (Function.update m i k)) l :=
    fun k => partialSum_periodic i v hv m k
  have hmod : partialSum i v m = partialSum i v (Function.update m i (m i % l)) := by
    have h := hper.map_mod_nat (m i)
    simp only [Function.update_eq_self] at h
    exact h.symm
  rw [hmod]
  refine (partialSum_abs_le i v hC m _).trans ?_
  have : ((m i % l : ℕ) : ℝ) ≤ l := by exact_mod_cast (Nat.mod_lt _ hl).le
  exact mul_le_mul_of_nonneg_right this hC0

lemma abs_partialSumMean_le {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ)
    (hv : GoodAt l i v) {C : ℝ} (hC : ∀ m, |(v m : ℝ)| ≤ C) (m : Fin r → ℕ) :
    |((meanP l i v m : ℚ) : ℝ)| ≤ l * C := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  unfold meanP
  push_cast
  rw [abs_div, abs_of_pos hl', div_le_iff₀ hl']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((l : ℝ) * C) fun j _ => ?_).trans ?_
  · exact_mod_cast partialSum_bound hl i v hv hC _
  · simp [mul_comm]

lemma mul_partialSumMean {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) :
    (l : ℚ) * meanP l i v m = ∑ k ∈ Finset.range l, partialSum i v (Function.update m i k) := by
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  unfold meanP
  field_simp

lemma Aop_goodAt {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (hv : GoodAt l i v) :
    GoodAt l i (Aop l i v) := by
  have hps : ∀ (m : Fin r → ℕ) (t : ℕ), partialSum i v (m + (Pi.single i t : Fin r → ℕ)) =
      partialSum i v (Function.update m i (m i + t)) := fun m t => by
    rw [add_single_eq_update]
  refine ⟨fun m => ?_, fun m => ?_⟩
  · simp only [Aop, partialSumMean_add_single]
    have h1 : m + (Pi.single i l : Fin r → ℕ) + (Pi.single i 1 : Fin r → ℕ) =
        m + (Pi.single i (1 + l) : Fin r → ℕ) := by
      rw [add_assoc, ← Pi.single_add, add_comm l 1]
    rw [h1, hps, hps, ← add_assoc, partialSum_periodic i v hv]
  · have hterm : ∀ e, Aop l i v (m + (Pi.single i e : Fin r → ℕ)) =
        partialSum i v (Function.update m i (m i + 1 + e)) - meanP l i v m := fun e => by
      have h1 : m + (Pi.single i e : Fin r → ℕ) + (Pi.single i 1 : Fin r → ℕ) =
          m + (Pi.single i (1 + e) : Fin r → ℕ) := by
        rw [add_assoc, ← Pi.single_add, add_comm e 1]
      simp only [Aop, partialSumMean_add_single]
      rw [h1, hps, ← add_assoc]
    simp only [hterm]
    rw [Finset.sum_sub_distrib,
      sum_window (fun k => partialSum i v (Function.update m i k))
        (fun k => partialSum_periodic i v hv m k) (m i + 1), ← mul_partialSumMean hl]
    simp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.AopProps

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

open AopProps in

theorem aop_props : ∀ (r l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ), 0 < l → GoodAt l i v → BddW v →
    BddW (Aop l i v) ∧ BddW (Bop l i v) ∧ GoodAt l i (Aop l i v) := by
  intro r l i v hl hv ⟨C, hC⟩
  refine ⟨⟨l * C + l * C, fun m => ?_⟩, ⟨l * C, fun m => ?_⟩, Aop_goodAt hl i v hv⟩
  · unfold Aop
    push_cast
    exact (abs_sub _ _).trans
      (add_le_add (partialSum_bound hl i v hv hC _) (abs_partialSumMean_le hl i v hv hC _))
  · have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC m)
    unfold Bop
    split_ifs
    · exact abs_partialSumMean_le hl i v hv hC m
    · simpa using mul_nonneg (Nat.cast_nonneg l) hC0

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummationOperatorsPreserveOtherIndex
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar

variable {r : ℕ}

lemma add_single_apply_ne {i k : Fin r} (h : k ≠ i) (m : Fin r → ℕ) (e : ℕ) :
    (m + (Pi.single k e : Fin r → ℕ)) i = m i := by
  simp [Pi.single_eq_of_ne h.symm]

lemma update_add_single {i k : Fin r} (h : k ≠ i) (m : Fin r → ℕ) (e t : ℕ) :
    Function.update (m + (Pi.single k e : Fin r → ℕ)) i t = Function.update m i t + (Pi.single k e : Fin r → ℕ) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Pi.single_eq_of_ne h.symm]
  · simp [Function.update_of_ne hj]

lemma partialSum_shift {i k : Fin r} (h : k ≠ i) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (e : ℕ) :
    partialSum i v (m + (Pi.single k e : Fin r → ℕ)) =
      ∑ t ∈ Finset.range (m i), v (Function.update m i t + (Pi.single k e : Fin r → ℕ)) := by
  unfold partialSum
  rw [add_single_apply_ne h]
  exact Finset.sum_congr rfl fun t _ => by rw [update_add_single h]

lemma meanP_shift (l : ℕ) {i k : Fin r} (h : k ≠ i) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (e : ℕ) :
    meanP l i v (m + (Pi.single k e : Fin r → ℕ)) =
      (∑ t ∈ Finset.range l, partialSum i v (Function.update m i t + (Pi.single k e : Fin r → ℕ))) / l := by
  unfold meanP
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [update_add_single h]

lemma partialSum_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    partialSum i v (m + (Pi.single k l : Fin r → ℕ)) = partialSum i v m := by
  rw [partialSum_shift h]
  unfold partialSum
  exact Finset.sum_congr rfl fun t _ => hp _

lemma meanP_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    meanP l i v (m + (Pi.single k l : Fin r → ℕ)) = meanP l i v m := by
  rw [meanP_shift l h]
  unfold meanP
  congr 1
  exact Finset.sum_congr rfl fun t _ => partialSum_period h hp _

lemma partialSum_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, partialSum i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  simp_rw [partialSum_shift h]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun t _ => hz _

lemma meanP_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, meanP l i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  simp_rw [meanP_shift l h]
  rw [← Finset.sum_div, Finset.sum_comm]
  rw [Finset.sum_eq_zero fun t _ => partialSum_zero h hz _, zero_div]

lemma Aop_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    Aop l i v (m + (Pi.single k l : Fin r → ℕ)) = Aop l i v m := by
  unfold Aop
  rw [add_right_comm, partialSum_period h hp, meanP_period h hp]

lemma Bop_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    Bop l i v (m + (Pi.single k l : Fin r → ℕ)) = Bop l i v m := by
  unfold Bop
  rw [add_single_apply_ne h, meanP_period h hp]

lemma Aop_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, Aop l i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  unfold Aop
  rw [Finset.sum_sub_distrib, meanP_zero h hz, sub_zero]
  simp_rw [add_right_comm m]
  exact partialSum_zero h hz _

lemma Bop_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, Bop l i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  unfold Bop
  simp_rw [add_single_apply_ne h]
  by_cases h0 : m i = 0
  · simp only [h0, if_true]
    exact meanP_zero h hz m
  · simp [h0]

lemma partialSum_support {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hs : ∀ m, m k ≠ 0 → v m = 0) (m : Fin r → ℕ) (hm : m k ≠ 0) : partialSum i v m = 0 := by
  unfold partialSum
  refine Finset.sum_eq_zero fun t _ => hs _ ?_
  rwa [Function.update_of_ne h]

lemma meanP_support (l : ℕ) {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hs : ∀ m, m k ≠ 0 → v m = 0) (m : Fin r → ℕ) (hm : m k ≠ 0) : meanP l i v m = 0 := by
  unfold meanP
  rw [Finset.sum_eq_zero fun t _ => partialSum_support h hs _ (by rwa [Function.update_of_ne h]), zero_div]

theorem good_support_other (r l : ℕ) (i k : Fin r) (v : (Fin r → ℕ) → ℚ) (h : k ≠ i) :
    (GoodAt l k v → GoodAt l k (Aop l i v) ∧ GoodAt l k (Bop l i v)) ∧
    ((∀ m, m k ≠ 0 → v m = 0) → (∀ m, m k ≠ 0 → Aop l i v m = 0) ∧ (∀ m, m k ≠ 0 → Bop l i v m = 0)) := by
  refine ⟨fun hg => ⟨⟨Aop_period h hg.1, Aop_zero h hg.2⟩, ⟨Bop_period h hg.1, Bop_zero h hg.2⟩⟩, fun hs => ⟨fun m hm => ?_, fun m hm => ?_⟩⟩
  · unfold Aop
    rw [partialSum_support h hs _ (by simpa [Pi.single_eq_of_ne h] using hm), meanP_support l h hs m hm, sub_zero]
  · unfold Bop
    rw [meanP_support l h hs m hm, ite_self]

theorem otherVar_main : ∀ (r l : ℕ) (i k : Fin r) (v : (Fin r → ℕ) → ℚ), k ≠ i →
    (GoodAt l k v → GoodAt l k (Aop l i v) ∧ GoodAt l k (Bop l i v)) ∧
    ((∀ m, m k ≠ 0 → v m = 0) → (∀ m, m k ≠ 0 → Aop l i v m = 0) ∧ (∀ m, m k ≠ 0 → Bop l i v m = 0)) :=
  fun r l i k v h => good_support_other r l i k v h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyPositiveBasisRatioBound
section
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem finite_realEmbeddings (F : Type) [Field F] [NumberField F] : Finite (F →+* ℝ) :=
  Finite.of_injective (fun σ : F →+* ℝ => (Complex.ofRealHom.comp σ : F →+* ℂ)) (by
    intro σ τ h
    ext x
    have := congrArg (fun f : F →+* ℂ => f x) h
    simpa using this)

theorem bounded_ratio_on_basis_cone : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) →
    ∃ R : ℝ, 0 < R ∧ ∀ x : F, (∀ i, 0 < b.repr x i) → ∀ σ τ : F →+* ℝ, σ x ≤ R * τ x := by
  intro F _ _ κ _ b hb
  classical
  haveI := finite_realEmbeddings F
  haveI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  have hterm : ∀ (i : κ) (σ τ : F →+* ℝ), 0 < σ (b i) / τ (b i) := fun i σ τ => div_pos (hb i σ) (hb i τ)
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 1 + ∑ i, ∑ σ : F →+* ℝ, ∑ τ : F →+* ℝ, σ (b i) / τ (b i) := ⟨_, rfl⟩
  have hsum : 0 ≤ ∑ i, ∑ σ : F →+* ℝ, ∑ τ : F →+* ℝ, σ (b i) / τ (b i) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun τ _ => (hterm i σ τ).le
  have hR : 0 < R := by rw [hRdef]; linarith
  have hle : ∀ (i : κ) (σ τ : F →+* ℝ), σ (b i) ≤ R * τ (b i) := by
    intro i σ τ
    have h1 : σ (b i) / τ (b i) ≤ ∑ τ' : F →+* ℝ, σ (b i) / τ' (b i) :=
      Finset.single_le_sum (f := fun τ' : F →+* ℝ => σ (b i) / τ' (b i)) (fun τ' _ => (hterm i σ τ').le) (Finset.mem_univ τ)
    have h2 : ∑ τ' : F →+* ℝ, σ (b i) / τ' (b i) ≤ ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i) :=
      Finset.single_le_sum (f := fun σ' : F →+* ℝ => ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i))
        (fun σ' _ => Finset.sum_nonneg fun τ' _ => (hterm i σ' τ').le) (Finset.mem_univ σ)
    have h3 : ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i) ≤ ∑ j, ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b j) / τ' (b j) :=
      Finset.single_le_sum (f := fun j => ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b j) / τ' (b j))
        (fun j _ => Finset.sum_nonneg fun σ' _ => Finset.sum_nonneg fun τ' _ => (hterm j σ' τ').le) (Finset.mem_univ i)
    have h4 : σ (b i) / τ (b i) ≤ R := by rw [hRdef]; linarith
    exact (div_le_iff₀ (hb i τ)).1 h4
  refine ⟨R, hR, fun x hx σ τ => ?_⟩
  have hrep : ∀ ρ : F →+* ℝ, ρ x = ∑ i, (b.repr x i : ℝ) * ρ (b i) := by
    intro ρ
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
  rw [hrep σ, hrep τ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hc : (0 : ℝ) < (b.repr x i : ℝ) := by exact_mod_cast hx i
  calc (b.repr x i : ℝ) * σ (b i) ≤ (b.repr x i : ℝ) * (R * τ (b i)) := mul_le_mul_of_nonneg_left (hle i σ τ) hc.le
    _ = R * ((b.repr x i : ℝ) * τ (b i)) := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyRealFieldDenseEmbeddings
section
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density

theorem denseRange_real_places (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    DenseRange fun (x : F) (w : InfinitePlace F) =>
      InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x := by
  rw [Metric.denseRange_iff]
  intro z ε hε
  have hq : ∀ w : InfinitePlace F, ∃ q : ℚ, |(q : ℝ) - z w| < ε / 2 := by
    intro w
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show z w < z w + ε / 2 by linarith)
    exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  choose q hq using hq
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (InfinitePlace.denseRange_algebraMap_pi F)
    (fun w => WithAbs.toAbs w.1 ((q w : ℚ) : F)) (ε / 2) (by linarith)
  refine ⟨x, (dist_pi_lt_iff hε).mpr fun w => ?_⟩
  have hxw := (dist_pi_lt_iff (by linarith : (0 : ℝ) < ε / 2)).mp hx w
  try dsimp only at hxw
  rw [Pi.algebraMap_apply, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub, WithAbs.ofAbs_toAbs,
    WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs, Algebra.algebraMap_self, RingHom.id_apply] at hxw
  have h2 : w.1 ((q w : F) - x) =
      |(q w : ℝ) - InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x| := by
    have h := InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal w) ((q w : F) - x)
    rw [Real.norm_eq_abs, map_sub, map_ratCast] at h
    exact h.symm
  rw [h2] at hxw
  show dist (z w) (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x) < ε
  rw [Real.dist_eq]
  have h3 : |z w - (q w : ℝ)| < ε / 2 := by
    rw [abs_sub_comm]
    exact hq w
  linarith [abs_sub_le (z w) (q w : ℝ) (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x)]

theorem exists_place_eq (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : F →+* ℝ) :
    ∃ w : InfinitePlace F, InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) = σ := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  refine ⟨InfinitePlace.mk (Complex.ofRealHom.comp σ), ?_⟩
  ext x
  have h1 := InfinitePlace.embedding_of_isReal_apply
    (IsTotallyReal.isReal (InfinitePlace.mk (Complex.ofRealHom.comp σ))) x
  rw [InfinitePlace.embedding_mk_eq_of_isReal hφ, RingHom.comp_apply, Complex.ofRealHom_eq_coe] at h1
  exact_mod_cast h1

theorem exists_approx : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (F →+* ℝ) → ℝ) (ε : ℝ),
    0 < ε → ∃ x : F, ∀ σ : F →+* ℝ, |σ x - y σ| < ε := by
  intro F _ _ _ y ε hε
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (denseRange_real_places F)
    (fun w => y (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))) ε hε
  refine ⟨x, fun σ => ?_⟩
  obtain ⟨w, hw⟩ := exists_place_eq F σ
  have h := (dist_pi_lt_iff hε).mp hx w
  rw [Real.dist_eq, hw, abs_sub_comm] at h
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density
end

