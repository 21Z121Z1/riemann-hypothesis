import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellBru
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Matrix

section Bru

variable {K : Type} [Field K] {n : ℕ}

theorem bru_lo_one : IsLoUni (1 : Matrix (Fin n) (Fin n) K) := fun i j =>
  ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), fun h => by subst h; exact Matrix.one_apply_eq i⟩

theorem bru_up_one : IsUpUni (1 : Matrix (Fin n) (Fin n) K) := fun i j =>
  ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => by subst h; exact Matrix.one_apply_eq i⟩

theorem bru_lo_mul {A B : Matrix (Fin n) (Fin n) K} (hA : IsLoUni A) (hB : IsLoUni B) : IsLoUni (A * B) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : i < k
    · rw [(hA i k).1 hk, zero_mul]
    · rw [(hB k j).1 (lt_of_le_of_lt (not_lt.1 hk) hij), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hB k i).1 h, mul_zero]
      · rw [(hA i k).1 h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem bru_up_mul {A B : Matrix (Fin n) (Fin n) K} (hA : IsUpUni A) (hB : IsUpUni B) : IsUpUni (A * B) := by
  first | exact GlobalTheory.UpperUnipotentMul.isUpUni_mul .. | (apply GlobalTheory.UpperUnipotentMul.isUpUni_mul <;> assumption) | (intros; apply GlobalTheory.UpperUnipotentMul.isUpUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentMul.isUpUni_mul <;> assumption) | (intros; apply @GlobalTheory.UpperUnipotentMul.isUpUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentMul.isUpUni_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› n A B hA hB | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› n A B hA | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› n A B | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› n A | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› n | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K

def bruL (u : Fin n → K) (p : Fin n) : Matrix (Fin n) (Fin n) K :=
  fun a k => (if a = k then 1 else 0) + u a * (if k = p then 1 else 0)

def bruU (w : Fin n → K) (q : Fin n) : Matrix (Fin n) (Fin n) K :=
  fun k c => (if k = c then 1 else 0) + (if k = q then 1 else 0) * w c

theorem bruL_apply (u : Fin n → K) (p a k : Fin n) :
    bruL u p a k = (if a = k then 1 else 0) + u a * (if k = p then 1 else 0) := rfl

theorem bruU_apply (w : Fin n → K) (q k c : Fin n) :
    bruU w q k c = (if k = c then 1 else 0) + (if k = q then 1 else 0) * w c := rfl

theorem bru_left (u : Fin n → K) (p : Fin n) (X : Matrix (Fin n) (Fin n) K) (a c : Fin n) :
    (bruL u p * X) a c = X a c + u a * X p c := by
  simp only [Matrix.mul_apply, bruL, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp
  · simp

theorem bru_right (w : Fin n → K) (q : Fin n) (X : Matrix (Fin n) (Fin n) K) (a c : Fin n) :
    (X * bruU w q) a c = X a c + X a q * w c := by
  simp only [Matrix.mul_apply, bruU, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp
  · simp

def bruRed (m : ℕ) (M : Matrix (Fin n) (Fin n) K) (σ : Fin n → Fin n) : Prop :=
  (∀ b b' : Fin n, b.val < m → b'.val < m → σ b = σ b' → b = b') ∧
  (∀ b : Fin n, b.val < m → M (σ b) b ≠ 0) ∧
  (∀ b : Fin n, b.val < m → ∀ a, a ≠ σ b → M a b = 0) ∧
  (∀ b : Fin n, b.val < m → ∀ c, c ≠ b → M (σ b) c = 0)

theorem bru_step {m : ℕ} (hm : m < n) (M : Matrix (Fin n) (Fin n) K) (hdet : M.det ≠ 0) (σ : Fin n → Fin n)
    (h : bruRed m M σ) :
    ∃ (L U M' : Matrix (Fin n) (Fin n) K) (σ' : Fin n → Fin n), IsLoUni L ∧ IsUpUni U ∧ M = L * M' * U ∧
      bruRed (m + 1) M' σ' := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨q, hq⟩ : ∃ q : Fin n, q.val = m := ⟨⟨m, hm⟩, rfl⟩
  have hne : ∃ a, M a q ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero q hc)
  obtain ⟨p, hp, hmin⟩ : ∃ p, M p q ≠ 0 ∧ ∀ a, a < p → M a q = 0 := by
    have hs : (Finset.univ.filter (fun a => M a q ≠ 0)).Nonempty := by
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, by simp [ha]⟩
    refine ⟨(Finset.univ.filter (fun a => M a q ≠ 0)).min' hs, ?_, ?_⟩
    · have := Finset.min'_mem _ hs
      simpa using this
    · intro a ha
      by_contra hc
      have hmem : a ∈ Finset.univ.filter (fun a => M a q ≠ 0) := by simp [hc]
      exact absurd (Finset.min'_le _ a hmem) (not_le.2 ha)
  have hqb : ∀ b : Fin n, b.val < m → q ≠ b := by
    intro b hb e
    rw [← e, hq] at hb
    exact lt_irrefl _ hb
  have hpσ : ∀ b : Fin n, b.val < m → p ≠ σ b := by
    intro b hb e
    exact hp (e ▸ h4 b hb q (hqb b hb))
  have hrow : ∀ c : Fin n, c.val < m → M p c = 0 := fun c hc => h3 c hc p (hpσ c hc)
  have hcase : ∀ b : Fin n, b.val < m + 1 → b = q ∨ b.val < m := by
    intro b hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext (h.trans hq.symm))
  obtain ⟨u, hu⟩ : ∃ u : Fin n → K, ∀ a, u a = if a = p then 0 else M a q / M p q := ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin n → K, ∀ c, w c = if c = q then 0 else M p c / M p q := ⟨_, fun _ => rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : Matrix (Fin n) (Fin n) K, ∀ a c, M' a c =
      if a = p then (if c = q then M p q else 0) else M a c - M a q / M p q * M p c :=
    ⟨Matrix.of fun a c => if a = p then (if c = q then M p q else 0) else M a c - M a q / M p q * M p c,
      fun _ _ => rfl⟩
  refine ⟨bruL u p, bruU w q, M', Function.update σ q p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · rw [bruL_apply, if_neg (ne_of_lt hij), zero_add]
      by_cases hj : j = p
      · subst hj
        rw [hu, if_neg (ne_of_lt hij), hmin i hij, zero_div, zero_mul]
      · rw [if_neg hj, mul_zero]
    · subst hij
      rw [bruL_apply, if_pos rfl, hu]
      by_cases hi : i = p
      · rw [if_pos hi, zero_mul, add_zero]
      · rw [if_neg hi, if_neg hi, mul_zero, add_zero]
  · intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · rw [bruU_apply, if_neg (ne_of_gt hij), zero_add]
      by_cases hi : i = q
      · subst hi
        rw [hw, if_neg (ne_of_lt hij), hrow j (by rw [← hq]; exact hij), zero_div, mul_zero]
      · rw [if_neg hi, zero_mul]
    · subst hij
      rw [bruU_apply, if_pos rfl, hw]
      by_cases hi : i = q
      · rw [if_pos hi, if_pos hi, mul_zero, add_zero]
      · rw [if_neg hi, zero_mul, add_zero]
  · ext a c
    rw [bru_right, bru_left, bru_left, hu, hw, hM', hM', hM', hM']
    by_cases ha : a = p
    · subst ha
      by_cases hc : c = q
      · subst hc
        simp
      · simp only [if_true, if_neg hc]
        field_simp
        ring
    · by_cases hc : c = q
      · subst hc
        simp only [if_true, if_neg ha]
        field_simp
        ring
      · simp only [if_true, if_neg ha, if_neg hc]
        field_simp
        ring
  · intro b b' hb hb' e
    rcases hcase b hb with rfl | hb1
    · rcases hcase b' hb' with rfl | hb1'
      · rfl
      · rw [Function.update_self, Function.update_of_ne (hqb b' hb1').symm] at e
        exact absurd e (hpσ b' hb1')
    · rcases hcase b' hb' with rfl | hb1'
      · rw [Function.update_self, Function.update_of_ne (hqb b hb1).symm] at e
        exact absurd e.symm (hpσ b hb1)
      · rw [Function.update_of_ne (hqb b hb1).symm, Function.update_of_ne (hqb b' hb1').symm] at e
        exact h1 b b' hb1 hb1' e
  · intro b hb
    rcases hcase b hb with rfl | hb1
    · rw [Function.update_self, hM', if_pos rfl, if_pos rfl]
      exact hp
    · rw [Function.update_of_ne (hqb b hb1).symm, hM', if_neg (hpσ b hb1).symm,
        h4 b hb1 q (hqb b hb1), zero_div, zero_mul, sub_zero]
      exact h2 b hb1
  · intro b hb a ha
    rcases hcase b hb with rfl | hb1
    · rw [Function.update_self] at ha
      rw [hM', if_neg ha, div_mul_cancel₀ _ hp, sub_self]
    · rw [Function.update_of_ne (hqb b hb1).symm] at ha
      rw [hM']
      by_cases hap : a = p
      · rw [if_pos hap, if_neg (hqb b hb1).symm]
      · rw [if_neg hap, h3 b hb1 a ha, hrow b hb1, mul_zero, sub_zero]
  · intro b hb c hc
    rcases hcase b hb with rfl | hb1
    · rw [Function.update_self, hM', if_pos rfl, if_neg hc]
    · rw [Function.update_of_ne (hqb b hb1).symm, hM', if_neg (hpσ b hb1).symm,
        h4 b hb1 c hc, h4 b hb1 q (hqb b hb1), zero_div, zero_mul, sub_zero]

theorem bru_all (Z : Matrix (Fin n) (Fin n) K) (hdet : Z.det ≠ 0) : ∀ m : ℕ, m ≤ n →
    ∃ (L U M : Matrix (Fin n) (Fin n) K) (σ : Fin n → Fin n), IsLoUni L ∧ IsUpUni U ∧ Z = L * M * U ∧ bruRed m M σ := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨1, 1, Z, id, bru_lo_one, bru_up_one, by simp,
      fun b _ hb => absurd hb (Nat.not_lt_zero _), fun b hb => absurd hb (Nat.not_lt_zero _),
      fun b hb => absurd hb (Nat.not_lt_zero _), fun b hb => absurd hb (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨L, U, M, σ, hL, hU, hZ, hR⟩ := ih (Nat.le_of_succ_le hm)
    have hM : M.det ≠ 0 := by
      intro h0
      apply hdet
      rw [hZ, Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul]
    obtain ⟨L1, U1, M', σ', hL1, hU1, hM', hR'⟩ := bru_step (Nat.lt_of_succ_le hm) M hM σ hR
    refine ⟨L * L1, U1 * U, M', σ', bru_lo_mul hL hL1, bru_up_mul hU1 hU, ?_, hR'⟩
    rw [hZ, hM']
    simp only [Matrix.mul_assoc]

end Bru

theorem cell_bruhat : BruhatDecomposition := by
  intro K _ n Z hdet
  obtain ⟨L, U, M, σ, hL, hU, hZ, h1, h2, h3, _⟩ := bru_all Z hdet n le_rfl
  have hinj : Function.Injective σ := fun b b' e => h1 b b' b.isLt b'.isLt e
  refine ⟨L, U, σ, fun b => M (σ b) b, hL, hU, Finite.injective_iff_bijective.1 hinj, fun b => h2 b b.isLt, ?_⟩
  have hMm : M = mono σ (fun b => M (σ b) b) := by
    ext a b
    unfold mono
    by_cases hab : a = σ b
    · rw [if_pos hab, hab]
    · rw [if_neg hab, h3 b b.isLt a hab]
  rw [← hMm]
  exact hZ

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.PrimeIdealNormRpowSumLe
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField IsDedekindDomain Ideal

theorem sum_inv_sq_le_one_of_two_le (T : Finset ℕ) (hT : ∀ n ∈ T, 2 ≤ n) : ∑ n ∈ T, ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
  classical
  have hsub : T ⊆ Finset.Ioc 1 (T.sup id + 1) := by
    intro n hn
    rw [Finset.mem_Ioc]
    exact ⟨by have := hT n hn; omega, le_trans (Finset.le_sup (f := id) hn) (Nat.le_succ _)⟩
  calc ∑ n ∈ T, ((n : ℝ) ^ 2)⁻¹ ≤ ∑ n ∈ Finset.Ioc 1 (T.sup id + 1), ((n : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ((1 : ℕ) : ℝ)⁻¹ - ((T.sup id + 1 : ℕ) : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub one_ne_zero (by omega)
    _ ≤ 1 := by
        have : (0 : ℝ) ≤ ((T.sup id + 1 : ℕ) : ℝ)⁻¹ := by positivity
        simp only [Nat.cast_one, inv_one]
        linarith

theorem rpow_neg_le_two_pow_inv_sq (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 2 ≤ s) :
    (n : ℝ) ^ (-s) ≤ 2 ^ (2 - s) * ((n : ℝ) ^ 2)⁻¹ := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have e : (n : ℝ) ^ (-s) = (n : ℝ) ^ (2 - s) * ((n : ℝ) ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
    congr 1
    push_cast
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos zero_lt_two hn2 (by linarith)) (by positivity)

theorem sum_rpow_neg_le_two_pow (T : Finset ℕ) (hT : ∀ n ∈ T, 2 ≤ n) (s : ℝ) (hs : 2 ≤ s) :
    ∑ n ∈ T, (n : ℝ) ^ (-s) ≤ 2 ^ (2 - s) := by
  calc ∑ n ∈ T, (n : ℝ) ^ (-s) ≤ ∑ n ∈ T, 2 ^ (2 - s) * ((n : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum (fun n hn => rpow_neg_le_two_pow_inv_sq n (hT n hn) s hs)
    _ = 2 ^ (2 - s) * ∑ n ∈ T, ((n : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 2 ^ (2 - s) * 1 := mul_le_mul_of_nonneg_left (sum_inv_sq_le_one_of_two_le T hT) (by positivity)
    _ = 2 ^ (2 - s) := mul_one _

theorem card_primes_over_rational_le (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (hn : n.Prime) [DecidableEq (HeightOneSpectrum (𝓞 F))] :
    (S.filter (fun p => absNorm (under ℤ p.asIdeal) = n)).card ≤ Module.finrank ℚ F := by
  classical
  have : Fact n.Prime := ⟨hn⟩
  have hp0 : (span {(n : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, span_singleton_eq_bot]
    exact_mod_cast hn.ne_zero
  refine le_trans (Finset.card_le_card_of_injOn (t := IsDedekindDomain.primesOverFinset (span {(n : ℤ)}) (𝓞 F))
    (fun p => p.asIdeal) ?_ ?_) (Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hp0)
  · intro p hp
    have hp' : absNorm (under ℤ p.asIdeal) = n := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0]
    refine ⟨p.isPrime, ?_⟩
    have := Int.liesOver_span_absNorm p.asIdeal
    rwa [hp'] at this
  · intro p _ p' _ h
    exact HeightOneSpectrum.ext h

theorem prime_ideal_norm_rpow_sum_le (F : Type) [Field F] [NumberField F] (s : ℝ) (hs : 2 ≤ s) :
    ∑' p : HeightOneSpectrum (𝓞 F), ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-s) ≤ (Module.finrank ℚ F : ℝ) * 2 ^ (2 - s) := by
  classical
  refine Real.tsum_le_of_sum_le (fun p => by positivity) (fun S => ?_)
  have hq_prime : ∀ p : HeightOneSpectrum (𝓞 F), (absNorm (under ℤ p.asIdeal)).Prime := fun p => by
    have : NeZero p.asIdeal := ⟨p.ne_bot⟩
    have := p.isPrime
    exact Nat.absNorm_under_prime p.asIdeal
  have hq_le : ∀ p : HeightOneSpectrum (𝓞 F), absNorm (under ℤ p.asIdeal) ≤ absNorm p.asIdeal := fun p =>
    Nat.le_of_dvd (Nat.pos_of_ne_zero (by rw [Ne, absNorm_eq_zero_iff]; exact p.ne_bot))
      (Int.absNorm_under_dvd_absNorm p.asIdeal)
  calc ∑ p ∈ S, ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-s)
      ≤ ∑ p ∈ S, ((absNorm (under ℤ p.asIdeal) : ℕ) : ℝ) ^ (-s) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        refine Real.rpow_le_rpow_of_nonpos ?_ (by exact_mod_cast hq_le p) (by linarith)
        exact_mod_cast (hq_prime p).pos
    _ = ∑ n ∈ S.image (fun p => absNorm (under ℤ p.asIdeal)),
          (S.filter (fun p => absNorm (under ℤ p.asIdeal) = n)).card • ((n : ℝ) ^ (-s)) :=
        Finset.sum_comp (fun n : ℕ => (n : ℝ) ^ (-s)) (fun p : HeightOneSpectrum (𝓞 F) => absNorm (under ℤ p.asIdeal))
    _ ≤ ∑ n ∈ S.image (fun p => absNorm (under ℤ p.asIdeal)), (Module.finrank ℚ F : ℝ) * ((n : ℝ) ^ (-s)) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_primes_over_rational_le F S _ (hq_prime p)
    _ = (Module.finrank ℚ F : ℝ) * ∑ n ∈ S.image (fun p => absNorm (under ℤ p.asIdeal)), (n : ℝ) ^ (-s) := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ F : ℝ) * 2 ^ (2 - s) := by
        refine mul_le_mul_of_nonneg_left (sum_rpow_neg_le_two_pow _ (fun n hn => ?_) s hs) (by positivity)
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
        exact (hq_prime p).two_le

theorem finrank_base_field_eq_degree (D : Formalism.BasicNotions.D7) : Module.finrank ℚ D.host.F = D.R.f := by
  exact D.host.finrank_hostF

theorem error_sum_le (D : Formalism.BasicNotions.D7) (Ce : ℝ) (hCe : 0 ≤ Ce) (hk : (2 : ℝ) ≤ (D.R.k : ℝ) - 2 * D.R.rS - 3) :
    Formalism.MainNotions.S.eSum D Ce ≤ Ce * ((D.R.f : ℝ) * 2 ^ (2 - ((D.R.k : ℝ) - 2 * D.R.rS - 3))) := by
  unfold Formalism.MainNotions.S.eSum
  refine mul_le_mul_of_nonneg_left ?_ hCe
  have h := prime_ideal_norm_rpow_sum_le D.host.F ((D.R.k : ℝ) - 2 * D.R.rS - 3) hk
  rw [finrank_base_field_eq_degree D] at h
  exact h

end Formalism.MainNotions.BridgeLemma

end
end

