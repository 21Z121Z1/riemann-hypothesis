import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
import Formalism.LocalToGlobal.Columns.Bundle0015
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0517
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0497
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerMonomialFrobeniusCongrPow
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.DpGood

theorem factorial_pow_mul (q : ℕ) : ∀ j : ℕ, ∃ D : ℕ, (j * q).factorial = q.factorial ^ j * D
  | 0 => ⟨1, by simp⟩
  | j + 1 => by
    obtain ⟨D, hD⟩ := factorial_pow_mul q j
    refine ⟨((j + 1) * q).choose q * D, ?_⟩
    have h := Nat.choose_mul_factorial_mul_factorial (show q ≤ (j + 1) * q by nlinarith)
    have h2 : (j + 1) * q - q = j * q := by rw [add_mul, one_mul, Nat.add_sub_cancel]
    rw [h2, hD] at h
    rw [← h]; ring

theorem choose_eq (l q : ℕ) (hl : 1 ≤ l) (hq : 1 ≤ q) :
    (l * q).choose q = l * (l * q - 1).choose (q - 1) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hpos : 0 < l * (q' + 1) := by positivity
  have hn : l * (q' + 1) = (l * (q' + 1) - 1) + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
  have h := Nat.add_one_mul_choose_eq (l * (q' + 1) - 1) q'
  rw [← hn] at h
  simp only [Nat.add_sub_cancel]
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos q')
    (show (l * (q' + 1)).choose (q' + 1) * (q' + 1) = l * (l * (q' + 1) - 1).choose q' * (q' + 1) by
      rw [← h]; ring)

theorem fact_dvd (l q M : ℕ) (hl : 1 ≤ l) (hq : 1 ≤ q) (hM : l * q ≤ M) :
    ∃ G : ℕ, M.factorial = q.factorial ^ l * l * G := by
  obtain ⟨D, hD⟩ := factorial_pow_mul q (l - 1)
  obtain ⟨R, hR⟩ := Nat.factorial_dvd_factorial hM
  have h := Nat.choose_mul_factorial_mul_factorial (show q ≤ l * q by nlinarith)
  have h2 : l * q - q = (l - 1) * q := by rw [Nat.sub_mul, one_mul]
  rw [h2, hD, choose_eq l q hl hq] at h
  refine ⟨(l * q - 1).choose (q - 1) * D * R, ?_⟩
  have hl' : q.factorial ^ l = q.factorial ^ (l - 1) * q.factorial := by
    rw [← pow_succ]; congr 1; omega
  rw [hR, ← h, hl']; ring

theorem key (K : Type) [Field K] [CharZero K] (l : ℕ) (hl : 1 ≤ l) (q M : ℕ) (hM : l * q ≤ M) :
    ∃ c' : K, ∃ k : ℕ, (q.factorial : K)⁻¹ = (q.factorial : K)⁻¹ ^ l + (l : K) * c' ∧
      (M.factorial : K) * c' = k := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨0, 0, by simp, by simp⟩
  obtain ⟨G, hG⟩ := fact_dvd l q M hl hq hM
  obtain ⟨h, hh⟩ : ∃ h, q.factorial ^ (l - 1) = h + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (pow_pos (Nat.factorial_pos q) _)).symm⟩
  have hG0 : G ≠ 0 := by
    rintro rfl; exact Nat.factorial_ne_zero M (by simpa using hG)
  refine ⟨((G * h : ℕ) : K) / (M.factorial : K), G * h, ?_, ?_⟩
  · have hf : (q.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero q)
    have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hG0' : (G : K) ≠ 0 := Nat.cast_ne_zero.2 hG0
    have hl' : (q.factorial : K) ^ l = ((h : K) + 1) * q.factorial := by
      have : (q.factorial : K) ^ (l - 1) = (h : K) + 1 := by exact_mod_cast hh
      rw [← this, ← pow_succ]; congr 1; omega
    have hh0 : (h : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero h
    rw [hG]; push_cast
    rw [inv_pow, hl']
    field_simp
    ring
  · have hMf : (M.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero M)
    field_simp

section Mem

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem mono_mem (N : ℕ) (c : K) (k : ℕ) (h : ((N / e).factorial : K) * c = k) :
    (fun _ => monomial N c : ZMod a → K⟦X⟧) ∈ SdSet t K e := by
  refine ⟨fun m => if m = N then (k : Wq l a) else 0, fun r => ?_, fun τ m => ?_⟩
  · rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton N).subset fun m hm => ?_
    by_contra hne
    have hne' : m ≠ N := by simpa using hne
    exact hm (by simp only [if_neg hne']; exact dvd_zero _)
  · rw [coeff_monomial]
    split_ifs with hm
    · subst hm; simp [h]
    · simp [hm]

end Mem

end GlobalTheory.CrysPrism.DpGood

namespace GlobalTheory.CrysPrism

open DpGood in

theorem dpS_frob_good : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ n : ℕ,
    (dpS a e n : ZMod a → K⟦X⟧) ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e,
      frobTot K a l (dpS a e n) = (dpS a e n : ZMod a → K⟦X⟧) ^ l + (l : ZMod a → K⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t n
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  refine ⟨mono_mem t e n _ 1 ?_, ?_⟩
  · rw [Nat.cast_one]; exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have hM : l * (n / e) ≤ l * n / e := by
    rw [Nat.le_div_iff_mul_le (NeZero.pos e), mul_assoc]
    exact Nat.mul_le_mul_left l (Nat.div_mul_le_self n e)
  obtain ⟨c', k, hc, hk⟩ := key K l hl (n / e) (l * n / e) hM
  refine ⟨fun _ => monomial (l * n) c', mono_mem t e (l * n) c' k hk, ?_⟩
  funext τ
  rw [frobTot_apply, Pi.add_apply, Pi.pow_apply, Pi.mul_apply, Pi.natCast_apply]
  simp only [dpS]
  rw [frob, expand_monomial, monomial_pow, ← map_natCast (C : K →+* K⟦X⟧), ← smul_eq_C_mul,
    ← LinearMap.map_smul, ← map_add, mul_comm l n, smul_eq_mul, ← hc]

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedUniformizerPowerFrobeniusCongrPow
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem factorial_pow_dvd_factorial_mul (q k : ℕ) : q.factorial ^ k ∣ (k * q).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (Nat.mul_dvd_mul_right ih _).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem exists_factorial_quot (l q : ℕ) (hl : 0 < l) :
    ∃ (A B : ℕ) (D : ℤ), A * q.factorial = (l * q).factorial ∧ B * q.factorial ^ l = (l * q).factorial ∧
      (A : ℤ) = B + l * D := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨1, 1, 0, by simp, by simp, by simp⟩
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  obtain ⟨c, hc⟩ := factorial_pow_dvd_factorial_mul (p + 1) k
  have h1 := Nat.add_choose_mul_factorial_mul_factorial (k * (p + 1)) (p + 1)
  have h2 := Nat.add_one_mul_choose_eq (k * (p + 1) + p) p
  have h3 : (k * (p + 1) + (p + 1)).choose (p + 1) = (k + 1) * (k * (p + 1) + p).choose p := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos p)
    rw [← add_assoc, ← h2]; simp only [Nat.succ_eq_add_one]; ring
  have h4 : (k + 1) * (p + 1) = k * (p + 1) + (p + 1) := by ring
  set m := (k * (p + 1) + p).choose p
  refine ⟨(k + 1) * m * (k * (p + 1)).factorial, (k + 1) * m * c,
    (m * (k * (p + 1)).factorial : ℕ) - (m * c : ℕ), ?_, ?_, ?_⟩
  · rw [h4, ← h1, h3]
  · rw [h4, ← h1, h3, hc]; ring
  · push_cast; ring

section

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ) [NeZero e]

theorem intCast_div_factorial_mem_QSet (z : ℤ) (m : ℕ) :
    (fun _ => C (C ((z : K) / (m.factorial : K)) * X ^ (e * m)) : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  classical
  refine ⟨Pi.single (0, e * m) (z : Wq l a), ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW, coeff_C]
  by_cases hi : i = 0
  · subst hi
    rw [if_pos rfl, coeff_C_mul, coeff_X_pow]
    by_cases hn : n = e * m
    · subst hn
      simp [dpDen, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (NeZero.ne e))]
    · rw [if_neg hn, Pi.single_eq_of_ne (by simpa using hn)]; simp
  · rw [if_neg hi, Pi.single_eq_of_ne (by simp [hi])]; simp

end

theorem dFam_mem_goodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ q : ℕ, dFam a K e q ∈ GoodSet t e φ₂ := by
  intro l hl a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _ q
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  obtain ⟨A, B, D, hA, hB, hD⟩ := exists_factorial_quot l q hl.out.pos
  have hq : (q.factorial : K) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
  have hlq : ((l * q).factorial : K) ≠ 0 := by exact_mod_cast (l * q).factorial_ne_zero
  have hA' : (A : K) * q.factorial = (l * q).factorial := by exact_mod_cast hA
  have hB' : (B : K) * (q.factorial : K) ^ l = (l * q).factorial := by exact_mod_cast hB
  have hD' : (A : K) = B + l * D := by exact_mod_cast hD
  have eA : (q.factorial : K)⁻¹ = ((A : ℤ) : K) / (l * q).factorial := by
    rw [Int.cast_natCast]; field_simp; rw [← hA']; ring
  have eB : ((q.factorial : K)⁻¹) ^ l = (B : K) / (l * q).factorial := by
    rw [eq_div_iff hlq, ← hB', mul_left_comm, ← mul_pow, inv_mul_cancel₀ hq, one_pow, mul_one]
  have hf : frob2 φ₂ (dFam a K e q) =
      fun _ => C (C (((A : ℤ) : K) / ((l * q).factorial : K)) * X ^ (e * (l * q))) := by
    funext τ
    change φ₂ (dFam a K e q (τ - 1)) = _
    simp only [dFam]
    rw [hC, map_mul, map_pow, frob_C, frob_X, ← pow_mul, eA]
    congr 3; ring
  refine ⟨?_, ?_, _, intCast_div_factorial_mem_QSet t K e D (l * q), ?_⟩
  · have := intCast_div_factorial_mem_QSet t K e 1 q
    rw [Int.cast_one, one_div] at this
    exact this
  · rw [hf]; exact intCast_div_factorial_mem_QSet t K e _ _
  · rw [hf]
    funext τ
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, dFam]
    rw [← map_pow, ← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), ← map_mul, ← map_add, mul_pow, ← map_pow, eB,
      ← pow_mul, ← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc (C (l : K)), ← map_mul,
      show e * q * l = e * (l * q) by ring, ← add_mul, ← map_add, Int.cast_natCast, hD']
    congr 3; ring

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedVariablePowerFrobeniusCongrPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism.GoodX

theorem pow_factorial_dvd (i m : ℕ) : i.factorial ^ m ∣ (m * i).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (Nat.mul_dvd_mul_right ih _).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem mul_pow_factorial_dvd (l i : ℕ) (hl : l ≠ 0) (hi : i ≠ 0) :
    i.factorial ^ l * l ∣ (l * i).factorial := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  have h1 : i ≤ (m + 1) * i := by nlinarith
  have h2 := Nat.choose_mul_factorial_mul_factorial h1
  have h3 : (m + 1) * i - i = m * i := by rw [Nat.succ_mul]; omega
  rw [h3, Nat.choose_mul_right hi] at h2
  obtain ⟨c, hc⟩ := pow_factorial_dvd i m
  refine ⟨((m + 1) * i - 1).choose (i - 1) * c, ?_⟩
  rw [Nat.succ_eq_add_one, ← h2, hc]; ring

theorem exists_padic (l : ℕ) [hl : Fact l.Prime] (i : ℕ) (hi : i ≠ 0) :
    ∃ d : ℤ_[l], (i.factorial : ℤ_[l]) * d = (l : ℤ_[l]) ^ (i - 1) := by
  have hv : padicValNat l i.factorial ≤ i - 1 := by
    have h := sub_one_mul_padicValNat_factorial (p := l) i
    have h2 := hl.out.two_le
    have h3 : (l.digits i).sum ≠ 0 := by
      intro h0
      have hne : l.digits i ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 hi
      exact Nat.getLast_digit_ne_zero l hi (List.sum_eq_zero_iff.1 h0 _ (List.getLast_mem hne))
    have h4 : 1 * padicValNat l i.factorial ≤ (l - 1) * padicValNat l i.factorial :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨s, hs⟩ : l ^ padicValNat l i.factorial ∣ i.factorial := pow_padicValNat_dvd
  have hs' : ¬ l ∣ s := by
    intro h
    refine pow_succ_padicValNat_not_dvd (p := l) (Nat.factorial_ne_zero i) ?_
    rw [pow_succ]
    conv_rhs => rw [hs]
    exact Nat.mul_dvd_mul_left _ h
  have hu : IsUnit (s : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hs' ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd (p := l) (s : ℤ)).1 (by simpa using h)
    exact_mod_cast this
  obtain ⟨s', hs2⟩ := hu.exists_right_inv
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hv
  refine ⟨(l : ℤ_[l]) ^ k * s', ?_⟩
  have h5 : (i.factorial : ℤ_[l]) = (l : ℤ_[l]) ^ padicValNat l i.factorial * s := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[l]) hs
  rw [hk, pow_add]
  linear_combination ((l : ℤ_[l]) ^ k * s') * h5 + ((l : ℤ_[l]) ^ padicValNat l i.factorial * (l : ℤ_[l]) ^ k) * hs2

theorem abstract {R : Type} [CommRing R] (htf : ∀ n : ℕ, n ≠ 0 → ∀ x : R, (n : R) * x = 0 → x = 0)
    (S : Subring R) (φ : R →+* R) (l : ℕ) (hl : l ≠ 0) (u x : R) (xs : ℕ → R)
    (hxs : ∀ k : ℕ, (k.factorial : R) * xs k = x ^ k) (hu : u ∈ S) (hxS : ∀ k, xs k ∈ S)
    (hφ : φ x = (u + x) ^ l - u ^ l) (i : ℕ) (hi : i ≠ 0) (d : R) (hd : d ∈ S)
    (hdi : (i.factorial : R) * d = (l : R) ^ (i - 1)) :
    φ (xs i) ∈ S ∧ ∃ B ∈ S, φ (xs i) = xs i ^ l + (l : R) * B := by
  obtain ⟨Y, hY, hP⟩ : ∃ Y ∈ S, φ x = (l : R) * Y := by
    refine ⟨∑ m ∈ Finset.range l, ((l - 1).descFactorial m : R) * u ^ (l - (m + 1)) * xs (m + 1), ?_, ?_⟩
    · exact S.sum_mem fun m _ => S.mul_mem (S.mul_mem (natCast_mem S _) (S.pow_mem hu _)) (hxS _)
    · rw [hφ, add_comm u x, add_pow, Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
        add_sub_cancel_right]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h : (m + 1).factorial * l.choose (m + 1) = l * (l - 1).descFactorial m := by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
        exact Nat.succ_descFactorial_succ n m
      have h' : ((m + 1).factorial : R) * (l.choose (m + 1) : R) = (l : R) * ((l - 1).descFactorial m : R) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → R) h
      rw [← hxs]
      linear_combination (u ^ (l - (m + 1)) * xs (m + 1)) * h'
  have h1 : φ (xs i) = (l : R) * (d * Y ^ i) := by
    rw [← sub_eq_zero]
    apply htf _ (Nat.factorial_ne_zero i)
    have h := congrArg φ (hxs i)
    rw [map_mul, map_natCast, map_pow, hP, mul_pow] at h
    have h2 : (l : R) ^ i = l * (l : R) ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2] at h
    linear_combination h - ((l : R) * Y ^ i) * hdi
  obtain ⟨c, hc⟩ := mul_pow_factorial_dvd l i hl hi
  have h2 : xs i ^ l = (l : R) * (c * xs (l * i)) := by
    rw [← sub_eq_zero]
    apply htf _ (pow_ne_zero l (Nat.factorial_ne_zero i))
    have h := congrArg (· ^ l) (hxs i)
    have h3 := hxs (l * i)
    rw [hc] at h3
    simp only [mul_pow, ← pow_mul] at h
    rw [mul_comm i l] at h
    push_cast at h3 ⊢
    linear_combination h - h3
  have hm : d * Y ^ i ∈ S := S.mul_mem hd (S.pow_mem hY _)
  refine ⟨h1 ▸ S.mul_mem (natCast_mem S _) hm, d * Y ^ i - c * xs (l * i),
    S.sub_mem hm (S.mul_mem (natCast_mem S _) (hxS _)), ?_⟩
  rw [h1, h2]; ring

section Q

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

theorem mono_mem (c : Wq l a) (i n : ℕ) :
    (fun τ => C (C (algebraMap O K (emb t τ c) / (dpDen e i n : K)) * X ^ n) * X ^ i :
      ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨fun p => if p = (i, n) then c else 0, funext fun τ => ?_⟩
  ext j m
  rw [coeff_ofW, coeff_C_mul, coeff_X_pow]
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl, mul_one, coeff_C_mul, coeff_X_pow]
    by_cases hm : m = n
    · subst hm; simp
    · simp [hm]
  · simp [hj]

theorem add_mem {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x + y ∈ QSet t K e := by
  obtain ⟨v, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  refine ⟨v + w, funext fun τ => ?_⟩
  ext j m
  simp only [Pi.add_apply, map_add, coeff_ofW, add_div]

theorem neg_mem {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) : -x ∈ QSet t K e := by
  obtain ⟨v, rfl⟩ := hx
  refine ⟨-v, funext fun τ => ?_⟩
  ext j m
  simp only [Pi.neg_apply, map_neg, coeff_ofW, neg_div]

theorem cstW_mem (c : Wq l a) : cstW t K c ∈ QSet t K e := by
  convert mono_mem t K e c 0 0 using 1
  funext τ
  simp [cstW, dpDen]

theorem xFam_mem (i : ℕ) : xFam a K i ∈ QSet t K e := by
  convert mono_mem t K e 1 i 0 using 1
  funext τ
  simp [xFam, dpDen]

theorem uFam_mem : uFam a K ∈ QSet t K e := by
  convert mono_mem t K e 1 0 1 using 1
  funext τ
  have h : (1 / e).factorial = 1 := by
    rw [Nat.factorial_eq_one]; exact Nat.div_le_self _ _
  simp [uFam, dpDen, h]

def qSub (h : ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) : Subring (ZMod a → K⟦X⟧⟦X⟧) where
  carrier := QSet t K e
  mul_mem' := fun hx hy => h _ hx _ hy
  one_mem' := by
    convert cstW_mem t K e 1 using 1
    funext τ; simp [cstW]
  add_mem' := add_mem t K e
  zero_mem' := by
    convert cstW_mem t K e 0 using 1
    funext τ; simp [cstW]
  neg_mem' := neg_mem t K e

end Q

theorem xFam_mem_GoodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → (∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) → ∀ i : ℕ, xFam a K i ∈ GoodSet t e φ₂ := by
  intro l hl a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC hX hmul i
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨xFam_mem t K e i, ?_⟩
  by_cases hi : i = 0
  · subst hi
    have h : xFam a K 0 = 1 := by funext τ; simp [xFam]
    rw [h, map_one]
    exact ⟨(qSub t K e hmul).one_mem, 0, (qSub t K e hmul).zero_mem, by simp⟩
  obtain ⟨d, hd⟩ := exists_padic l i hi
  refine abstract (fun n hn x hx => tf_pi (natCast_ne_zero_ps (natCast_ne_zero_ps (Nat.cast_ne_zero.2 hn))) x hx)
    (qSub t K e hmul) (frob2 φ₂) l hl.out.ne_zero (uFam a K) (fun _ => X) (xFam a K) (fun k => ?_)
    (uFam_mem t K e) (xFam_mem t K e) ?_ i hi (cstW t K (algebraMap ℤ_[l] _ d)) (cstW_mem t K e _) ?_
  · funext τ
    have h : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
    simp only [Pi.mul_apply, Pi.natCast_apply, Pi.pow_apply, xFam]
    rw [← mul_assoc, ← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), ← map_natCast (C : K →+* K⟦X⟧), ← map_mul, ← map_mul,
      mul_inv_cancel₀ h]
    simp
  · funext τ
    change φ₂ X = (C X + X) ^ l - C X ^ l
    rw [hX, map_pow]
  · funext τ
    have h := congrArg (fun z => (C (C (algebraMap O K (algebraMap ℤ_[l] O z))) : K⟦X⟧⟦X⟧)) hd
    simp only [map_mul, map_natCast, map_pow] at h
    simpa [cstW] using h

end GlobalTheory.CrysPrism.GoodX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMemStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (M M' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → Submodule.IsLattice E M → Submodule.IsLattice E M' → (∀ x ∈ M, (N : 𝓞 E) • x ∈ M') → (∀ x ∈ M', (N : 𝓞 E) • x ∈ M) → ∃ a : ℕ, ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, ((N : K) ^ a) • F ∈ Formalism.L2.DIV.nabAtr emb lam M' := by
  first | exact @GlobalTheory.NabScale.nabAtr_smul_pow_mem | exact GlobalTheory.NabScale.nabAtr_smul_pow_mem | (intros; apply GlobalTheory.NabScale.nabAtr_smul_pow_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdPolyEvaluationOfMemDividedTwoVariableSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CrysEval

theorem coeff_natCast_mul_ps {R : Type} [CommRing R] (n i : ℕ) (f : R⟦X⟧) :
    coeff i ((n : R⟦X⟧) * f) = n * coeff i f := by
  rw [← map_natCast (C : R →+* R⟦X⟧) n, coeff_C_mul]

theorem dvd_fP_of_mem_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (b : Bp l a) (F : ZMod a → K⟦X⟧⟦X⟧), F ∈ PPSet t K e → ∀ n : ℕ, n ≠ 0 → (n : ZMod a → K⟦X⟧⟦X⟧) * F = iotaP K t b → ∃ y : Per.Acris l, (n : Per.Acris l) * y = fP a ϖ (g : GQ l) b := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ g b F hF n hn hnF
  obtain ⟨w, -, hw⟩ := hF
  have := charZero_K (l := l) (K := K)
  have key : ∀ i k, ((i.factorial * (k / e).factorial : ℕ) : Wq l a) * (b.coeff i).coeff k = n * w (i, k) := by
    intro i k
    apply embK_injective (K := K) t 0
    have h1 := congrArg (fun G => coeff k (coeff i (G 0))) hnF
    simp only [Pi.mul_apply, Pi.natCast_apply] at h1
    rw [coeff_natCast_mul_ps, coeff_natCast_mul_ps, coeff_iotaP] at h1
    have h2 := hw 0 i k
    change _ = embK K t 0 (w (i, k)) at h2
    rw [map_mul, map_mul, map_natCast, map_natCast]
    push_cast at h2 ⊢
    linear_combination (-((i.factorial : K) * ((k / e).factorial : K))) * h1 + (n : K) * h2
  have hμ := ϖ.theta_mu (ϖ.gal_pi a g)
  set T := ainfToAcris l ϖ.teich with hTdef
  have term : ∀ i k, ainfToAcris l (wA l a ((b.coeff i).coeff k)) * T ^ k *
      ainfToAcris l (ϖ.mu (g : GQ l) * ϖ.teich) ^ i ∈ Ideal.span {(n : Per.Acris l)} := by
    intro i k
    obtain ⟨D, hD⟩ := ϖ.exists_dpow_teich (k / e)
    have hm := factorial_mul_dpow (ϖ.mu (g : GQ l)) hμ i
    have hk := congrArg (fun x => ainfToAcris l (wA l a x)) (key i k)
    simp only [map_mul, map_natCast] at hk
    push_cast at hk
    rw [Ideal.mem_span_singleton']
    refine ⟨ainfToAcris l (wA l a (w (i, k))) * D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i, ?_⟩
    have hT : T ^ k = T ^ (k % e) * T ^ (e * (k / e)) := by rw [← pow_add, Nat.mod_add_div]
    rw [hT, ← hD, map_mul, mul_pow, ← hm]
    linear_combination (-(D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i)) * hk
  have hmem : fP a ϖ (g : GQ l) b ∈ Ideal.span {(n : Per.Acris l)} := by
    rw [fP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Ideal.sum_mem _ fun i _ => ?_
    have hev : evC a ϖ (b.coeff i) = (b.coeff i).sum fun k c => ainfToAcris l (wA l a c) * T ^ k := by
      rw [evC, RingHom.comp_apply, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, ev_coe,
        Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
      change ainfToAcris l _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_pow]
      rfl
    rw [hev, Polynomial.sum_def, Finset.sum_mul]
    exact Ideal.sum_mem _ fun k _ => term i k
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨y, by rw [mul_comm]; exact hy⟩

end GlobalTheory.CrysEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinEvalNonZeroDivisorNatCastIsUnitStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinEval_nonZeroDivisor_natCast_isUnit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), (∀ y : OD l O, GlobalTheory.GalStep.ED K t ϖ * y = 0 → y = 0) ∧ ∀ n : ℕ, n ≠ 0 → IsUnit (n : OD l O) := by
  first | exact @GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit | exact GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit | (intros; apply GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMulBijectiveShiftsFiltrationVStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → Function.Bijective (A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e))) ∧ ∀ (y : T.V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ), y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j) ↔ A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j + 1) := by
  first | exact @GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff | exact GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff | (intros; apply GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff <;> assumption)
end

