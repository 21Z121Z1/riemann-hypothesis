import Formalism.RankGapBounds.Bundle0001
import Formalism.RankGapBounds.Bundle0002

-- bundled from Formalism.RankGapBounds.RankGapProofs.CardLargePrimeFactorsLeOneHolds
section
open Real Finset

namespace Formalism.RankGapBounds.ChebyshevFactorialBounds

theorem chebyshevThetaLe_holds : ChebyshevTheta := by
  intro n
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at h
  exact h

private theorem prod_primes_pow_div_dvd_factorial (n : ℕ) : ∏ p ∈ primesUpTo n, p ^ (n / p) ∣ n.factorial := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∏ p ∈ s, p ^ (n / p) ∣ n.factorial := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | @insert a s ha ih =>
      intro hs
      rw [Finset.prod_insert ha]
      have hpa : a.Prime := hs a (Finset.mem_insert_self a s)
      have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ (ih hs')
      · exact Nat.Coprime.prod_right fun p hp =>
          Nat.Coprime.pow _ _ ((Nat.coprime_primes hpa (hs' p hp)).mpr fun h => ha (h ▸ hp))
      · rw [hpa.pow_dvd_factorial_iff (show Nat.log a n < Nat.log a n + 2 by omega)]
        calc n / a = n / a ^ 1 := by rw [pow_one]
          _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log a n + 2), n / a ^ i :=
            Finset.single_le_sum (f := fun i => n / a ^ i) (fun _ _ => Nat.zero_le _)
              (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
  exact key _ fun p hp => (Finset.mem_filter.mp hp).2

private theorem sum_primes_log_div_le_log_add_log_four (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ primesUpTo n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ p ∈ primesUpTo n, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have h1 : ∑ p ∈ primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log p ≤ (n : ℝ) * Real.log n := by
    have hd := Nat.le_of_dvd (Nat.factorial_pos n) (prod_primes_pow_div_dvd_factorial n)
    have hprod : (0 : ℝ) < ∏ p ∈ primesUpTo n, (p : ℝ) ^ (n / p) :=
      Finset.prod_pos fun p hp => pow_pos (hpos p hp) _
    calc ∑ p ∈ primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log p
        = Real.log (∏ p ∈ primesUpTo n, (p : ℝ) ^ (n / p)) := by
          rw [Real.log_prod fun p hp => (pow_pos (hpos p hp) _).ne']
          simp only [Real.log_pow]
      _ ≤ Real.log (n.factorial : ℝ) := Real.log_le_log hprod (by exact_mod_cast hd)
      _ ≤ Real.log ((n : ℝ) ^ n) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) (by exact_mod_cast Nat.factorial_le_pow n)
      _ = n * Real.log n := Real.log_pow _ _
  have h2 : ∑ p ∈ primesUpTo n, Real.log p ≤ Real.log 4 * n := chebyshevThetaLe_holds n
  have h3 : ∀ p ∈ primesUpTo n,
      (n : ℝ) * (Real.log p / p) ≤ ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have hlog : 0 ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
    have hfl : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
      rw [← Nat.floor_div_eq_div (K := ℝ)]
      exact (Nat.lt_floor_add_one _).le
    calc (n : ℝ) * (Real.log p / p) = (n : ℝ) / p * Real.log p := by ring
      _ ≤ (((n / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right hfl hlog
      _ = ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by ring
  have hsum : (n : ℝ) * ∑ p ∈ primesUpTo n, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ primesUpTo n, (n : ℝ) * (Real.log p / p)
        ≤ ∑ p ∈ primesUpTo n, (((n / p : ℕ) : ℝ) * Real.log p + Real.log p) := Finset.sum_le_sum h3
      _ = ∑ p ∈ primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ primesUpTo n, Real.log p :=
          Finset.sum_add_distrib
      _ ≤ n * Real.log n + Real.log 4 * n := add_le_add h1 h2
      _ = n * (Real.log n + Real.log 4) := by ring
  exact le_of_mul_le_mul_left hsum hn'

theorem sumLogDivPredLe_holds : MertensType := by
  refine ⟨6, fun n hn => ?_⟩
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hS := sum_primes_log_div_le_log_add_log_four n (by omega)
  have hterm : ∀ p ∈ primesUpTo n, Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log p / p) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)]
    have hd : 2 * (Real.log p / p) * (p - 1) - Real.log p = Real.log p * (p - 2) / p := by
      field_simp
      ring
    have : 0 ≤ Real.log p * (p - 2) / p := div_nonneg (mul_nonneg hlog (by linarith)) (by linarith)
    linarith
  calc ∑ p ∈ primesUpTo n, Real.log p / ((p : ℝ) - 1)
      ≤ ∑ p ∈ primesUpTo n, 2 * (Real.log p / p) := Finset.sum_le_sum hterm
    _ = 2 * ∑ p ∈ primesUpTo n, Real.log p / p := by rw [Finset.mul_sum]
    _ ≤ 2 * (Real.log n + Real.log 4) := by linarith
    _ ≤ 6 * Real.log n := by rw [h4]; linarith

theorem cardLargePrimeFactorsLeOne_holds : LargePrimeFactor := by
  intro L z hL hz hzL
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at ha hb
  by_contra hne
  have hab : a * b ∣ z := Nat.Coprime.mul_dvd_of_dvd_of_dvd
    ((Nat.coprime_primes ha.1.1 hb.1.1).mpr hne) ha.1.2.1 hb.1.2.1
  have hle : ((a * b : ℕ) : ℝ) ≤ z := by exact_mod_cast Nat.le_of_dvd (by omega) hab
  push_cast at hle
  have hLL : L * L < (a : ℝ) * b := mul_lt_mul'' ha.2 hb.2 hL hL
  rw [sq] at hzL
  linarith

theorem harmonicLeOneAddLog_holds : HarmonicLog := by
  intro n _
  have h := harmonic_le_one_add_log n
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  simpa only [one_div] using h

theorem leastPosResidueSpec_holds : LeastResFacts := by
  intro a l hl
  unfold leastRes
  set S := {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ a - (d : ℤ)} with hS
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  have h0 : 0 ≤ (a - 1) % (l : ℤ) := Int.emod_nonneg _ hl'.ne'
  have hlt0 : (a - 1) % (l : ℤ) < l := Int.emod_lt_of_pos _ hl'
  set r := ((a - 1) % (l : ℤ)).toNat with hr
  have hr' : (r : ℤ) = (a - 1) % (l : ℤ) := Int.toNat_of_nonneg h0
  have hmemd : r + 1 ∈ S := by
    refine ⟨by omega, ?_⟩
    have he : a - ((r + 1 : ℕ) : ℤ) = (l : ℤ) * ((a - 1) / l) := by
      have := Int.emod_def (a - 1) (l : ℤ)
      push_cast
      linarith
    rw [he]
    exact dvd_mul_right _ _
  have hmem := Nat.sInf_mem ⟨_, hmemd⟩
  have hle : sInf S ≤ r + 1 := Nat.sInf_le hmemd
  have hrl : r < l := by omega
  refine ⟨hmem.1, by omega, hmem.2, fun ha1 hal => ?_⟩
  set m := a.toNat with hm
  have hm' : (m : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hamem : m ∈ S := ⟨by omega, by rw [hm', sub_self]; exact dvd_zero _⟩
  have h1 : sInf S ≤ m := Nat.sInf_le hamem
  have h2 : m ≤ sInf S := by
    by_contra hlt'
    rw [not_le] at hlt'
    obtain ⟨k, hk⟩ := hmem.2
    have hpos : 0 < a - ((sInf S : ℕ) : ℤ) := by omega
    have hsmall : a - ((sInf S : ℕ) : ℤ) < l := by have := hmem.1; omega
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · nlinarith
    · rw [hk0, mul_zero] at hk
      omega
    · nlinarith
  omega

end Formalism.RankGapBounds.ChebyshevFactorialBounds
end

-- bundled from Formalism.RankGapBounds.RankGapProofs.FourNotDvdOddSqAddOne
section
namespace Formalism.RankGapBounds.LocalQuadraticParts

lemma zmod_int_eq_one_iff (n : ℕ) (x : ℤ) : ((x : ZMod n) = 1) ↔ (n : ℤ) ∣ x - 1 := by
  rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma zmod_int_eq_neg_one_iff (n : ℕ) (x : ℤ) : ((x : ZMod n) = -1) ↔ (n : ℤ) ∣ x + 1 := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← Int.cast_one, ← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma zmod_nat_eq_one_iff (n l : ℕ) : ((l : ZMod n) = 1) ↔ (n : ℤ) ∣ (l : ℤ) - 1 := by
  have h := zmod_int_eq_one_iff n (l : ℤ)
  simpa using h

lemma zmod_nat_eq_neg_one_iff (n l : ℕ) : ((l : ZMod n) = -1) ↔ (n : ℤ) ∣ (l : ℤ) + 1 := by
  have h := zmod_int_eq_neg_one_iff n (l : ℤ)
  simpa using h

lemma four_not_dvd_odd_sq_add_one (y : ℤ) (hy : Odd y) : ¬ (4 : ℤ) ∣ y ^ 2 + 1 := by
  obtain ⟨k, rfl⟩ := hy
  have h : (2 * k + 1) ^ 2 + 1 = 4 * (k ^ 2 + k) + 2 := by ring
  rw [h]
  generalize k ^ 2 + k = t
  omega

lemma sq_sub_one_dvd_iff (x : ℤ) (hx : Odd x) (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℤ) ^ (m + 1) ∣ x ^ 2 - 1 ↔ ((2 : ℤ) ^ m ∣ x - 1 ∨ (2 : ℤ) ^ m ∣ x + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k, rfl⟩ := hx
  have e1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring
  have e2 : 2 * k + 1 - 1 = 2 * k := by ring
  have e3 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
  have p1 : (2 : ℤ) ^ (n + 1 + 1) = 4 * 2 ^ n := by ring
  have p2 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [e1, e2, e3, p1, p2, mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0),
    mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0), mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)]
  constructor
  · intro h
    rcases Int.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩
    · left
      have hc : IsCoprime ((2 : ℤ) ^ n) (k + 1) := by
        apply IsCoprime.pow_left
        refine ⟨-b, 1, ?_⟩
        rw [hb]
        ring
      exact hc.dvd_of_dvd_mul_right h
    · right
      have hc : IsCoprime ((2 : ℤ) ^ n) k := by
        apply IsCoprime.pow_left
        refine ⟨-b, 1, ?_⟩
        rw [hb]
        ring
      exact hc.dvd_of_dvd_mul_left h
  · rintro (h | h)
    · exact dvd_mul_of_dvd_left h _
    · exact dvd_mul_of_dvd_right h _

lemma pow_two_pow_pm_iff (j : ℕ) : ∀ (x : ℤ), Odd x → ∀ m : ℕ, 1 ≤ m →
    (((2 : ℤ) ^ (m + j) ∣ x ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (m + j) ∣ x ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ m ∣ x - 1 ∨ (2 : ℤ) ^ m ∣ x + 1)) := by
  induction j with
  | zero => intro x _ m _; simp
  | succ j ih =>
    intro x hx m hm
    have hy : Odd (x ^ (2 ^ j)) := hx.pow
    have hpow : x ^ (2 ^ (j + 1)) = (x ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
    have hnot : ¬ (2 : ℤ) ^ (m + (j + 1)) ∣ (x ^ (2 ^ j)) ^ 2 + 1 := by
      intro h
      apply four_not_dvd_odd_sq_add_one _ hy
      refine dvd_trans ?_ h
      have : (4 : ℤ) = 2 ^ 2 := by norm_num
      rw [this]
      exact pow_dvd_pow 2 (by omega)
    rw [hpow, ← ih x hx m hm, show m + (j + 1) = m + j + 1 by omega,
      ← sq_sub_one_dvd_iff _ hy (m + j) (by omega)]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h (by rw [show m + j + 1 = m + (j + 1) by omega]; exact hnot)
    · intro h
      exact Or.inl h

lemma pm_iff (e j : ℕ) (hj : j ≤ e) (x : ℤ) (hx : Odd x) :
    (((2 : ℤ) ^ (e + 2) ∣ x ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (e + 2) ∣ x ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ (e + 2 - j) ∣ x - 1 ∨ (2 : ℤ) ^ (e + 2 - j) ∣ x + 1)) := by
  have h := pow_two_pow_pm_iff j x hx (e + 2 - j) (by omega)
  rw [show e + 2 - j + j = e + 2 by omega] at h
  exact h

lemma units_zpow_neg_one_iff (n : ℕ) (u : (ZMod n)ˣ) :
    (∃ k : ℤ, (-1 : (ZMod n)ˣ) ^ k = u) ↔ (u = 1 ∨ u = -1) := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

lemma hOf_pow_eq_one_iff (e j l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) :
    (hOf e l hl) ^ (2 ^ j) = 1 ↔
      ((((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) = 1 ∨
        (((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) = -1) := by
  unfold hOf
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff,
    units_zpow_neg_one_iff]
  have hv : ((ZMod.unitOfCoprime l hl ^ (2 ^ j) : (ZMod (4 * 2 ^ e))ˣ) : ZMod (4 * 2 ^ e)) =
      (((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) := by
    simp [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  constructor
  · rintro (h | h)
    · left
      rw [← hv, h, Units.val_one]
    · right
      rw [← hv, h, Units.val_neg, Units.val_one]
  · rintro (h | h)
    · left
      apply Units.ext
      rw [hv, h, Units.val_one]
    · right
      apply Units.ext
      rw [hv, h, Units.val_neg, Units.val_one]

lemma odd_of_coprime (e l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) : Odd (l : ℤ) := by
  have h2 : ¬ 2 ∣ l := fun h => by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h hl)
      (dvd_mul_of_dvd_left (by norm_num) _)
    omega
  exact Int.odd_iff.mpr (by omega)

theorem powTwoPowEqOneIff_holds : OrdersIff := by
  intro e j l hl hj
  rw [hOf_pow_eq_one_iff, zmod_int_eq_one_iff, zmod_int_eq_neg_one_iff, zmod_nat_eq_one_iff,
    zmod_nat_eq_neg_one_iff]
  push_cast
  rw [show (4 : ℤ) * 2 ^ e = 2 ^ (e + 2) by ring]
  exact pm_iff e j hj l (odd_of_coprime e l hl)

theorem leOfOrderOfLe_holds : OrdersBound := by
  intro e J l hl hJ hl1 hord
  have hodd := odd_of_coprime e l hl
  have hE : (hOf e l hl) ^ (2 ^ e) = 1 := by
    rw [powTwoPowEqOneIff_holds e e l hl le_rfl, show e + 2 - e = 2 by omega, zmod_nat_eq_one_iff,
      zmod_nat_eq_neg_one_iff]
    obtain ⟨k, hk⟩ := hodd
    push_cast
    rcases Int.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩
    · left
      rw [hk, hb]
      exact ⟨b, by ring⟩
    · right
      rw [hk, hb]
      exact ⟨b + 1, by ring⟩
  obtain ⟨k, hk, hko⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hE)
  have hk1 : (hOf e l hl) ^ (2 ^ k) = 1 := by
    rw [← hko]
    exact pow_orderOf_eq_one _
  have hres := (powTwoPowEqOneIff_holds e k l hl hk).mp hk1
  rw [zmod_nat_eq_one_iff, zmod_nat_eq_neg_one_iff] at hres
  have hM : ((2 : ℤ) ^ (e + 2 - k)) ≤ (l : ℤ) + 1 := by
    rcases hres with h | h
    · push_cast at h
      have hpos : (0 : ℤ) < l - 1 := by omega
      have := Int.le_of_dvd hpos h
      linarith
    · push_cast at h
      have hpos : (0 : ℤ) < l + 1 := by omega
      have := Int.le_of_dvd hpos h
      linarith
  have hJn : 2 ^ k ≤ J := hko ▸ hord
  have hJ' : (2 : ℝ) ^ k ≤ J := by exact_mod_cast hJn
  have key : (4 * 2 ^ e : ℝ) = 2 ^ (e + 2 - k) * 2 ^ k := by
    rw [← pow_add, show e + 2 - k + k = e + 2 by omega]
    ring
  have h1 : (4 * 2 ^ e : ℝ) / J ≤ 4 * 2 ^ e / 2 ^ k :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hJ'
  have h2 : (4 * 2 ^ e : ℝ) / 2 ^ k = 2 ^ (e + 2 - k) := by
    rw [key]
    field_simp
  have h3 : (2 : ℝ) ^ (e + 2 - k) ≤ l + 1 := by exact_mod_cast hM
  linarith

end Formalism.RankGapBounds.LocalQuadraticParts
end

-- bundled from Formalism.RankGapBounds.RankGapProofs.RandomSubsetLemmaCounterexample
section
namespace Formalism.RankGapBounds.LocalQuadraticParts

open Finset

lemma wt_nonneg {α : Type*} [Fintype α] {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) :
    0 ≤ wt δ T :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

lemma sum_wt {α : Type*} [Fintype α] (δ : ℝ) : ∑ T : Finset α, wt δ T = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow δ (1 - δ) (Finset.univ : Finset α)
  rw [Finset.powerset_univ, Finset.card_univ] at h
  simp only [wt]
  rw [h]
  simp

lemma sum_wt_var {α : Type*} [Fintype α] (δ : ℝ) :
    ∑ T : Finset α, wt δ T * ((T.card : ℝ) - δ * Fintype.card α) ^ 2 =
      Fintype.card α * δ * (1 - δ) := by
  have h := congrArg (Polynomial.eval δ) (bernsteinPolynomial.variance (R := ℝ) (Fintype.card α))
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, bernsteinPolynomial, nsmul_eq_mul] at h
  have h2 := Finset.sum_powerset_apply_card
    (fun k : ℕ => δ ^ k * (1 - δ) ^ (Fintype.card α - k) * ((k : ℝ) - δ * Fintype.card α) ^ 2)
    (x := (Finset.univ : Finset α))
  rw [Finset.powerset_univ, Finset.card_univ] at h2
  simp only [wt]
  refine h2.trans ?_
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nsmul_eq_mul]
  ring

lemma sum_wt_bad {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)] (hω : ∀ p, 0 ≤ ω p)
    (hBAD : ∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T),
      wt δ T ≤ β * δ) :
    ∑ T : Finset α, wt δ T * ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤
      β * δ * Fintype.card α * ∑ p, ω p := by
  have key : ∀ p, ∑ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ) ≤
      β * δ * Fintype.card α := by
    intro p
    have e : ∀ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ) =
        ∑ t : α, if t ∈ T ∧ BAD p t T then wt δ T else 0 := by
      intro T
      have hf : (Finset.univ : Finset α).filter (fun t => t ∈ T ∧ BAD p t T) =
          T.filter fun t => BAD p t T := by
        ext t; simp
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hf, mul_comm]
    calc ∑ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ)
        = ∑ T : Finset α, ∑ t : α, (if t ∈ T ∧ BAD p t T then wt δ T else 0) :=
          Finset.sum_congr rfl (fun T _ => e T)
      _ = ∑ t : α, ∑ T : Finset α, (if t ∈ T ∧ BAD p t T then wt δ T else 0) := Finset.sum_comm
      _ = ∑ t : α, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T),
            wt δ T := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [Finset.sum_filter]
      _ ≤ ∑ _t : α, β * δ := Finset.sum_le_sum (fun t _ => hBAD p t)
      _ = β * δ * Fintype.card α := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  calc ∑ T : Finset α, wt δ T * ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ)
      = ∑ p, ω p * ∑ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun T _ => ?_))
        ring
    _ ≤ ∑ p, ω p * (β * δ * Fintype.card α) :=
        Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (key p) (hω p))
    _ = β * δ * Fintype.card α * ∑ p, ω p := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)

lemma pick {γ : Type*} (s : Finset γ) (w V X : γ → ℝ) (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (hw : ∀ T ∈ s, 0 ≤ w T) (hsum : ∑ T ∈ s, w T = 1) (hV0 : ∀ T ∈ s, 0 ≤ V T)
    (hV : ∑ T ∈ s, w T * V T ≤ 2 / 3 * r) (hX0 : ∀ T ∈ s, 0 ≤ X T)
    (hXs : ∑ T ∈ s, w T * X T ≤ M) :
    ∃ T ∈ s, V T < r ∧ X T ≤ 4 * M := by
  by_contra hcon
  push Not at hcon
  have hG : ∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T ≤ 2 / 3 := by
    have hle : ∀ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T ≤ w T * V T / r := by
      intro T hT
      rw [Finset.mem_filter] at hT
      have hVT : r ≤ V T := by
        by_contra h
        push Not at h
        exact hT.2 (hcon T hT.1 h)
      rw [le_div_iff₀ hr]
      exact mul_le_mul_of_nonneg_left hVT (hw T hT.1)
    calc ∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T
        ≤ ∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T * V T / r := Finset.sum_le_sum hle
      _ = (∑ T ∈ s.filter (fun T => ¬ 4 * M < X T), w T * V T) / r := by rw [Finset.sum_div]
      _ ≤ (∑ T ∈ s, w T * V T) / r := by
          apply div_le_div_of_nonneg_right _ hr.le
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro T hT _
          exact mul_nonneg (hw T hT) (hV0 T hT)
      _ ≤ (2 / 3 * r) / r := div_le_div_of_nonneg_right hV hr.le
      _ = 2 / 3 := by field_simp
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun T => 4 * M < X T) w
  have hB : 1 / 3 ≤ ∑ T ∈ s.filter (fun T => 4 * M < X T), w T := by linarith
  obtain ⟨T0, hT0, hwT0⟩ : ∃ T ∈ s.filter (fun T => 4 * M < X T), 0 < w T := by
    by_contra h
    push Not at h
    have : ∑ T ∈ s.filter (fun T => 4 * M < X T), w T ≤ 0 := Finset.sum_nonpos h
    linarith
  have hlt : ∑ T ∈ s.filter (fun T => 4 * M < X T), w T * (4 * M) <
      ∑ T ∈ s.filter (fun T => 4 * M < X T), w T * X T := by
    apply Finset.sum_lt_sum
    · intro T hT
      rw [Finset.mem_filter] at hT
      exact mul_le_mul_of_nonneg_left hT.2.le (hw T hT.1)
    · refine ⟨T0, hT0, ?_⟩
      rw [Finset.mem_filter] at hT0
      exact mul_lt_mul_of_pos_left hT0.2 hwT0
  have hsub : ∑ T ∈ s.filter (fun T => 4 * M < X T), w T * X T ≤ ∑ T ∈ s, w T * X T := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro T hT _
    exact mul_nonneg (hw T hT) (hX0 T hT)
  rw [← Finset.sum_mul] at hlt
  nlinarith [mul_nonneg (sub_nonneg.mpr hB) hM]

theorem tops_lemma_six_holds : TopsFixed := by
  intro α ι _ _ _ δ β ω BAD _ hδ0 hδ1 hq hβ hω hBAD
  have hS : 0 ≤ ∑ p, ω p := Finset.sum_nonneg fun p _ => hω p
  have hN : 0 ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
  have hqpos : 0 < δ * Fintype.card α := by linarith
  obtain ⟨T, -, hVT, hXT⟩ := pick (Finset.univ : Finset (Finset α)) (wt δ)
    (fun T => ((T.card : ℝ) - δ * Fintype.card α) ^ 2)
    (fun T => ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ))
    ((δ * Fintype.card α / 2) ^ 2) (β * δ * Fintype.card α * ∑ p, ω p)
    (by positivity) (by positivity)
    (fun T _ => wt_nonneg hδ0.le hδ1 T) (sum_wt δ) (fun T _ => sq_nonneg _)
    (by
      rw [sum_wt_var δ]
      nlinarith [mul_nonneg hqpos.le hδ0.le,
        mul_nonneg hqpos.le (by linarith : (0 : ℝ) ≤ δ * Fintype.card α - 6)])
    (fun T _ => Finset.sum_nonneg fun p _ => mul_nonneg (hω p) (Nat.cast_nonneg _))
    (sum_wt_bad δ β ω BAD hω hBAD)
  have hab := abs_lt_of_sq_lt_sq' hVT (by positivity)
  refine ⟨T, by linarith [hab.1], by linarith [hab.2], by linarith⟩

end Formalism.RankGapBounds.LocalQuadraticParts
end

