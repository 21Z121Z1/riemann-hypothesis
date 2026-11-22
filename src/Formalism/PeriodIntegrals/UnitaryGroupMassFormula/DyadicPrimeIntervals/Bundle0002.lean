import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.SmallLoop

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.RealIneq
section
noncomputable section

namespace PI.PrimesDyadicRS.W

theorem real_dyadic_inequality : RealIneq := by
  intro y hy
  have hy0 : 0 < y := by linarith
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hL16 : 16 * Real.log 2 ≤ Real.log y := by
    have e : Real.log 65536 = 16 * Real.log 2 := by
      rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, Real.log_pow]; norm_num
    rw [← e]; exact Real.log_le_log (by norm_num) hy
  have hLpos : 0 < Real.log y := by linarith
  have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy0.ne'
  have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hs256 : (256 : ℝ) ≤ Real.sqrt y := by
    have e : Real.sqrt 65536 = 256 := by
      rw [show (65536 : ℝ) = 256 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← e]; exact Real.sqrt_le_sqrt hy
  have hsq2 : Real.sqrt (2 * y) = Real.sqrt 2 * Real.sqrt y := Real.sqrt_mul (by norm_num) y
  have hsqrt2 : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hlogsq : Real.log (Real.sqrt (2 * y)) = (Real.log 2 + Real.log y) / 2 := by
    rw [Real.log_sqrt (by positivity), hlog2y]
  have hspos : 0 < Real.sqrt y := by linarith
  have hLs : Real.log y = 2 * Real.log (Real.sqrt y) := by
    conv_lhs => rw [← hs]
    rw [Real.log_mul hspos.ne' hspos.ne']; ring
  have hlogs : Real.log (Real.sqrt y) ≤ 8 * Real.log 2 + Real.sqrt y / 256 - 1 := by
    have h := Real.log_le_sub_one_of_pos (x := Real.sqrt y / 256) (by positivity)
    rw [Real.log_div hspos.ne' (by norm_num), show (256 : ℝ) = 2 ^ 8 by norm_num,
      Real.log_pow] at h
    push_cast at h
    linarith
  have hLup : Real.log y ≤ 9.1 + Real.sqrt y / 128 := by linarith
  have hMup : Real.log 2 + Real.log y ≤ 9.8 + Real.sqrt y / 128 := by linarith
  have hL2 : Real.log y ^ 2 ≤ (9.1 + Real.sqrt y / 128) ^ 2 :=
    pow_le_pow_left₀ hLpos.le hLup 2
  have hM2 : (Real.log 2 + Real.log y) ^ 2 ≤ (9.8 + Real.sqrt y / 128) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hMup 2
  have hLHS : 3 * y / (5 * Real.log y) * Real.log (2 * y)
      = 3 / 5 * y + 3 / 5 * (y * (Real.log 2 / Real.log y)) := by
    rw [hlog2y]; field_simp; ring
  have hratio : Real.log 2 / Real.log y ≤ 1 / 16 := by
    rw [div_le_iff₀ hLpos]; linarith
  have hyr : y * (Real.log 2 / Real.log y) ≤ y * (1 / 16) :=
    mul_le_mul_of_nonneg_left hratio hy0.le
  have hs2 : Real.sqrt 2 * Real.sqrt y ≤ 1.4143 * Real.sqrt y :=
    mul_le_mul_of_nonneg_right hsqrt2.le hspos.le
  have hq : 0 ≤ (Real.sqrt y - 256) * Real.sqrt y :=
    mul_nonneg (by linarith) hspos.le
  rw [hLHS, hlogsq, hsq2, hlog2y, div_pow]
  norm_num
  nlinarith [hL2, hM2, hs2, hq, hyr, hs, hl2, hl2', hLpos, hspos]

end PI.PrimesDyadicRS.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.SmallNaturalNumbersBound
section
namespace PI.PrimesDyadicRS.K

open Real

theorem gcd_fact_iff {m k : ℕ} (h2 : 2 ≤ m) (hk : k < m) (hm : m < (k + 1) ^ 2) :
    Nat.gcd m k.factorial = 1 ↔ m.Prime := by
  constructor
  · intro hg
    by_contra hp
    have hmf := Nat.minFac_sq_le_self (by omega) hp
    have hle : m.minFac ≤ k := by
      by_contra hc
      push Not at hc
      have : (k + 1) ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hc 2
      omega
    have hd : m.minFac ∣ Nat.gcd m k.factorial :=
      Nat.dvd_gcd (Nat.minFac_dvd m) (Nat.dvd_factorial (Nat.minFac_pos m) hle)
    rw [hg, Nat.dvd_one, Nat.minFac_eq_one_iff] at hd
    omega
  · intro hp
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => by
      have := (Nat.Prime.dvd_factorial hp).1 hd
      omega

theorem pr_eq {Q m : ℕ} (hQ : Q = Nat.factorial 362) (h2 : 2 ≤ m) (hm : m < 131769) :
    pr Q m = if m.Prime then 1 else 0 := by
  by_cases h1 : m ≤ 362
  · have e := gcd_fact_iff (k := m - 1) h2 (by omega)
      (by rw [show m - 1 + 1 = m by omega]; nlinarith)
    simp only [pr, if_pos h1]
    by_cases hp : m.Prime
    · rw [if_pos (e.2 hp), if_pos hp]
    · rw [if_neg (fun h => hp (e.1 h)), if_neg hp]
  · have e := gcd_fact_iff (k := 362) h2 (by omega) (by norm_num; omega)
    simp only [pr, if_neg h1, hQ]
    by_cases hp : m.Prime
    · rw [if_pos (e.2 hp), if_pos hp]
    · rw [if_neg (fun h => hp (e.1 h)), if_neg hp]

theorem pc_succ (n : ℕ) :
    Nat.primeCounting (n + 1) = Nat.primeCounting n + if (n + 1).Prime then 1 else 0 := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]

def D (h : ℕ) : ℕ := Nat.primeCounting h - Nat.primeCounting (h / 2)

theorem D_two : D 2 = 1 := by
  have h1 := pc_succ 1
  rw [Nat.primeCounting_one, if_pos Nat.prime_two] at h1
  simp only [D, show (2 : ℕ) / 2 = 1 by norm_num, Nat.primeCounting_one]
  omega

theorem nxt_eq {Q h : ℕ} (hQ : Q = Nat.factorial 362) (h2 : 2 ≤ h) (hh : h < 131072) :
    nxt Q h (D h) = D (h + 1) := by
  have hA := pr_eq (m := h + 1) hQ (by omega) (by omega)
  have hs := pc_succ h
  unfold nxt D
  rw [hA, hs]
  by_cases he : (h + 1) % 2 = 0
  · have hq : (h + 1) / 2 = h / 2 + 1 := by omega
    have hB := pr_eq (m := (h + 1) / 2) hQ (by omega) (by omega)
    have hs2 := pc_succ (h / 2)
    have hmono : Nat.primeCounting (h / 2 + 1) ≤ Nat.primeCounting h :=
      Nat.monotone_primeCounting (by omega)
    rw [if_pos he, hB, hq, hs2]
    rw [hs2] at hmono
    split_ifs at hmono ⊢ <;> omega
  · have hq : (h + 1) / 2 = h / 2 := by omega
    have hmono : Nat.primeCounting (h / 2) ≤ Nat.primeCounting h :=
      Nat.monotone_primeCounting (by omega)
    rw [if_neg he, hq]
    split_ifs <;> omega

theorem loop_sound {Q hT dT : ℕ} (hQ : Q = Nat.factorial 362) :
    ∀ k h d : ℕ, loop Q hT dT k h d = true → 2 ≤ h → h + k ≤ 131072 → d = D h →
      (hT = h + k ∧ dT = D hT) ∧ ∀ m, h ≤ m → m < h + k → 41 ≤ m → tstR m (D m) = true := by
  intro k
  induction k with
  | zero =>
    intro h d hl _ _ hd
    simp only [loop, Bool.and_eq_true, beq_iff_eq] at hl
    obtain ⟨e1, e2⟩ := hl
    subst e1 e2 hd
    exact ⟨⟨rfl, rfl⟩, fun m h1 h2 _ => by omega⟩
  | succ k ih =>
    intro h d hl h2 hk hd
    rw [loop, force_eq, force_eq, Bool.and_eq_true] at hl
    obtain ⟨ht, hl⟩ := hl
    subst hd
    rw [nxt_eq hQ h2 (by omega)] at hl
    obtain ⟨⟨e1, e2⟩, hall⟩ := ih (h + 1) (D (h + 1)) hl (by omega) (by omega) rfl
    refine ⟨⟨by omega, e2⟩, fun m hm1 hm2 hm3 => ?_⟩
    rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
    · rw [Bool.or_eq_true, Nat.blt_eq] at ht
      rcases ht with ht | ht
      · omega
      · exact ht
    · exact hall m hlt (by omega) hm3

theorem tstR_sound {h d : ℕ} (ht : tstR h d = true) (h2 : 2 ≤ h) :
    3 * ((h : ℝ) + 1) < 10 * (d : ℝ) * Real.log ((h : ℝ) / 2) := by
  simp only [tstR, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at ht
  obtain ⟨hd, hp⟩ := ht
  have hB : 0 < 10 * d * 6931471803 := by positivity
  have hlt0 : 7680000000000 * (h + 1) < (10 * d * 6931471803) * (7680000000000 * (h + 1) / (10 * d * 6931471803) + 1) :=
    Nat.lt_mul_div_succ _ hB
  generalize 7680000000000 * (h + 1) / (10 * d * 6931471803) = q at hp hlt0
  have hlt : ((7680000000000 * (h + 1) : ℕ) : ℝ) < ((10 * d * 6931471803) * (q + 1) : ℕ) := by
    exact_mod_cast hlt0
  push_cast at hlt
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hpow : ((2 : ℝ)) ^ (q + 257) ≤ (h : ℝ) ^ 256 := by exact_mod_cast hp
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hl2 : Real.log ((h : ℝ) / 2) = Real.log h - Real.log 2 := Real.log_div hh0.ne' (by norm_num)
  have hB2 : ((q : ℝ) + 1) * Real.log 2 ≤ 256 * Real.log ((h : ℝ) / 2) := by
    rw [hl2]; push_cast at hlog; linarith
  have hL2 := Real.log_two_gt_d9
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hC : ((q : ℝ) + 1) * (10 * d) * 0.6931471803 ≤ ((q : ℝ) + 1) * (10 * d) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hL2.le (by positivity)
  have hE : (10 * (d : ℝ)) * (((q : ℝ) + 1) * Real.log 2) ≤ (10 * (d : ℝ)) * (256 * Real.log ((h : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hB2 (by positivity)
  nlinarith

theorem tests : ∀ m, 41 ≤ m → m < 131072 → tstR m (D m) = true := by
  have r1 := run1
  have r2 := run2
  have r3 := run3
  have r4 := run4
  rw [run, force_eq] at r1 r2 r3 r4
  obtain ⟨⟨_, e1⟩, t1⟩ := loop_sound rfl _ _ _ r1 (by norm_num) (by norm_num) D_two.symm
  obtain ⟨⟨_, e2⟩, t2⟩ := loop_sound rfl _ _ _ r2 (by norm_num) (by norm_num) e1
  obtain ⟨⟨_, e3⟩, t3⟩ := loop_sound rfl _ _ _ r3 (by norm_num) (by norm_num) e2
  obtain ⟨_, t4⟩ := loop_sound rfl _ _ _ r4 (by norm_num) (by norm_num) e3
  intro m h1 h2
  by_cases a1 : m < 32768
  · exact t1 m (by omega) (by omega) h1
  by_cases a2 : m < 65536
  · exact t2 m (by omega) (by omega) h1
  by_cases a3 : m < 98304
  · exact t3 m (by omega) (by omega) h1
  · exact t4 m (by omega) (by omega) h1

theorem small_natural_numbers_bound : PI.PrimesDyadicRS.W.SmallNat := by
  intro h h1 h2
  have ht := tstR_sound (tests h h1 h2) (by omega)
  have hmono : Nat.primeCounting (h / 2) ≤ Nat.primeCounting h :=
    Nat.monotone_primeCounting (Nat.div_le_self h 2)
  have hc : ((D h : ℕ) : ℝ) = (Nat.primeCounting h : ℝ) - (Nat.primeCounting (h / 2) : ℝ) := by
    rw [D, Nat.cast_sub hmono]
  rw [hc] at ht
  exact ht

end PI.PrimesDyadicRS.K
end

