import Mathlib
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0056
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumDivSubLeTwoLogOfPartialSums
section
open Finset ArithmeticFunction

namespace GlobalTheory

theorem sum_div_sub_le_two_log_of_partial_sums (a : ℕ → ℝ)
    (h : ∀ N : ℕ, ∑ n ∈ Icc 1 N, a n ≤ 2 * (N : ℝ)) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n / (n : ℝ) - (∑ n ∈ Icc 1 N, a n) / ((N : ℝ) + 1)
      ≤ 2 * Real.log ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN := h (N + 1)
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)] at hN
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    push_cast at hN ⊢
    set P := ∑ n ∈ Icc 1 N, a n
    set S := ∑ n ∈ Icc 1 N, a n / (n : ℝ)
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    have h2 : (0 : ℝ) < (N : ℝ) + 1 + 1 := by linarith
    have hlog : 1 / ((N : ℝ) + 1 + 1) ≤ Real.log ((N : ℝ) + 1 + 1) - Real.log ((N : ℝ) + 1) := by
      have := Real.log_le_sub_one_of_pos (div_pos h1 h2)
      rw [Real.log_div h1.ne' h2.ne'] at this
      have e : ((N : ℝ) + 1) / ((N : ℝ) + 1 + 1) - 1 = -(1 / ((N : ℝ) + 1 + 1)) := by
        field_simp; ring
      linarith
    have e : S + a (N + 1) / ((N : ℝ) + 1) - (P + a (N + 1)) / ((N : ℝ) + 1 + 1)
        = (S - P / ((N : ℝ) + 1)) + ((P + a (N + 1)) / ((N : ℝ) + 1)) * (1 / ((N : ℝ) + 1 + 1)) := by
      field_simp; ring
    have h3 : (P + a (N + 1)) / ((N : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ h1]; linarith
    have h4 : ((P + a (N + 1)) / ((N : ℝ) + 1)) * (1 / ((N : ℝ) + 1 + 1))
        ≤ 2 * (1 / ((N : ℝ) + 1 + 1)) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    rw [e]
    linarith

theorem chebyshev_coefficient_sum_bound : Formalism.HermitianLattices.GL2a2.SizeSumC := by
  intro hψ
  refine ⟨806, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h : ∀ N : ℕ, ∑ n ∈ Icc 1 N, (Λ n : ℝ) ≤ 2 * (N : ℝ) := fun N => by
    simpa using hψ N (Nat.cast_nonneg N)
  set N := ⌊x ^ (400 : ℝ)⌋₊ with hNdef
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hA := sum_div_sub_le_two_log_of_partial_sums (fun n => (Λ n : ℝ)) h N
  have hB : (∑ n ∈ Icc 1 N, (Λ n : ℝ)) / ((N : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ h1]; linarith [h N]
  have hz1 : 1 ≤ x ^ (400 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hNz : (N : ℝ) ≤ x ^ (400 : ℝ) := Nat.floor_le (by linarith)
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hl2' := Real.log_two_gt_d9
  have hC : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + 400 * Real.log x := by
    have : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * x ^ (400 : ℝ)) :=
      Real.log_le_log h1 (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith), Real.log_rpow hx0] at this
    exact this
  have hD : ∑ n ∈ Icc 1 N, (Λ n : ℝ) / (n : ℝ) ≤ 806 * Real.log x := by
    linarith
  calc ∑ n ∈ Icc 1 N, Formalism.HermitianLattices.GL2PrimeSums.cn x n
      ≤ ∑ n ∈ Icc 1 N, x * ((Λ n : ℝ) / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        unfold Formalism.HermitianLattices.GL2PrimeSums.cn
        calc (Λ n : ℝ) * min 1 (x / (n : ℝ)) ≤ (Λ n : ℝ) * (x / (n : ℝ)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) vonMangoldt_nonneg
          _ = x * ((Λ n : ℝ) / (n : ℝ)) := by ring
    _ = x * ∑ n ∈ Icc 1 N, (Λ n : ℝ) / (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ x * (806 * Real.log x) := mul_le_mul_of_nonneg_left hD hx0.le
    _ = 806 * x * Real.log x := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumLeProdOfTwoLeNat
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem sum_le_prod_of_two_le_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, 2 ≤ f i) : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have key : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i ∧ 2 ≤ ∏ i ∈ s, f i := by
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => simpa using h a (by simp)
    | cons a s ha hs ih =>
      rw [Finset.sum_cons, Finset.prod_cons]
      obtain ⟨h1, h2⟩ := ih (fun i hi => h i (Finset.mem_cons_of_mem hi))
      have h3 := h a (Finset.mem_cons_self _ _)
      constructor
      · have := Nat.add_le_mul h3 h2
        omega
      · nlinarith
  exact key.1

private theorem arith_four (a b c R m : ℕ) (ha : 16 ≤ a) (hb : m ≤ b) (hc : m ≤ c)
    (hbc : 16 * m ≤ b * c) (hR : 1 ≤ R) : 4 * m * (a + b + c + R) ≤ a * b * c * R := by
  have h1 : 16 * m * a ≤ b * c * a := Nat.mul_le_mul_right _ hbc
  have h2 : 16 * m * b ≤ a * c * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hc)
  have h3 : 16 * m * c ≤ a * b * c := Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hb)
  have h4 : 16 * m * R ≤ a * b * c * R := by
    apply Nat.mul_le_mul_right
    calc 16 * m ≤ b * c := hbc
      _ ≤ a * (b * c) := Nat.le_mul_of_pos_left _ (by omega)
      _ = a * b * c := by ring
  have h5 : a * b * c ≤ a * b * c * R := Nat.le_mul_of_pos_right _ hR
  nlinarith

theorem sum_primePowerParts_le :
    ∀ n q d : ℕ, 0 < n → q.Prime → d.Prime → q ≠ 2 → d ≠ 2 → q ≠ d → 16 ≤ max q d →
      16 * q * d ∣ n → (∑ l ∈ n.primeFactors, ((l ^ padicValNat l n : ℕ) : ℝ)) ≤
        (n : ℝ) / (4 * ((min q d : ℕ) : ℝ)) := by
  intro n q d hn hq hd hq2 hd2 hqd hmax hdvd
  set f : ℕ → ℕ := fun l => l ^ padicValNat l n with hf
  have hpow : ∀ p k : ℕ, p.Prime → p ^ k ∣ n → p ^ k ≤ f p := by
    intro p k hp hk
    haveI := Fact.mk hp
    exact Nat.pow_le_pow_right hp.pos ((padicValNat_dvd_iff_le hn.ne').1 hk)
  have hge : ∀ p ∈ n.primeFactors, p ≤ f p := by
    intro p hp
    have := hpow p 1 (Nat.prime_of_mem_primeFactors hp)
      (by simpa using Nat.dvd_of_mem_primeFactors hp)
    simpa using this
  have h16 : 2 ^ 4 ∣ n := Dvd.dvd.trans ⟨q * d, by ring⟩ hdvd
  have hqn : q ∣ n := Dvd.dvd.trans ⟨16 * d, by ring⟩ hdvd
  have hdn : d ∣ n := Dvd.dvd.trans ⟨16 * q, by ring⟩ hdvd
  have m2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.2 ⟨Nat.prime_two, Dvd.dvd.trans ⟨8, by norm_num⟩ h16, hn.ne'⟩
  have mq : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqn, hn.ne'⟩
  have md : d ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hd, hdn, hn.ne'⟩
  have ha : 16 ≤ f 2 := by simpa using hpow 2 4 Nat.prime_two h16
  have hb := hge q mq
  have hc := hge d md
  have hsub : ({2, q, d} : Finset ℕ) ⊆ n.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hn2 : (2 : ℕ) ∉ ({q, d} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hprod : ∏ l ∈ n.primeFactors, f l = n := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn.ne']
    rw [Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
  set s := n.primeFactors \ {2, q, d} with hs
  have hs2 : ∀ i ∈ s, 2 ≤ f i := fun i hi =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hi).1).two_le.trans
      (hge i (Finset.mem_sdiff.1 hi).1)
  have hSP := sum_le_prod_of_two_le_nat s f hs2
  have hR : 1 ≤ ∏ i ∈ s, f i :=
    Finset.prod_pos (f := f) fun i hi => lt_of_lt_of_le (by norm_num) (hs2 i hi)
  have e1 : n = f 2 * f q * f d * ∏ i ∈ s, f i := by
    rw [← hprod, ← Finset.prod_sdiff hsub, Finset.prod_insert hn2, Finset.prod_pair hqd]
    ring
  have e2 : ∑ l ∈ n.primeFactors, f l = f 2 + f q + f d + ∑ i ∈ s, f i := by
    rw [← Finset.sum_sdiff hsub, Finset.sum_insert hn2, Finset.sum_pair hqd]
    ring
  have hbc : 16 * min q d ≤ f q * f d := by
    calc 16 * min q d ≤ max q d * min q d := Nat.mul_le_mul_right _ hmax
      _ = q * d := max_mul_min q d
      _ ≤ f q * f d := Nat.mul_le_mul hb hc
  have key := arith_four (f 2) (f q) (f d) (∏ i ∈ s, f i) (min q d) ha
    ((min_le_left _ _).trans hb) ((min_le_right _ _).trans hc) hbc hR
  rw [← e1] at key
  have key2 : (∑ l ∈ n.primeFactors, f l) * (4 * min q d) ≤ n := by
    rw [e2, mul_comm]
    exact (Nat.mul_le_mul_left _ (by omega)).trans key
  have hm : 0 < min q d := lt_min hq.pos hd.pos
  rw [le_div_iff₀ (by positivity), ← Nat.cast_sum]
  exact_mod_cast key2

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPrimePowerPartPowSubOneLe
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem sum_le_prod_of_two_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, 2 ≤ f i) :
    ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha2 := h a (Finset.mem_insert_self a s)
    have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rcases s.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · simp
    · have hne : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi => by
        have := h i (Finset.mem_insert_of_mem hi)
        omega
      have hP : 2 ≤ ∏ i ∈ s, f i :=
        (h b (Finset.mem_insert_of_mem hb)).trans
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Finset.dvd_prod_of_mem f hb))
      nlinarith

private theorem prod_prime_pow_dvd_of_forall_dvd (s : Finset ℕ) (e : ℕ → ℕ) (M : ℕ)
    (hp : ∀ l ∈ s, l.Prime) (hd : ∀ l ∈ s, l ^ e l ∣ M) : ∏ l ∈ s, l ^ e l ∣ M := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hd a (Finset.mem_insert_self a s))
      (ih (fun l hl => hp l (Finset.mem_insert_of_mem hl)) (fun l hl => hd l (Finset.mem_insert_of_mem hl)))
    refine Nat.Coprime.prod_right fun l hl => ?_
    refine Nat.Coprime.pow _ _ ?_
    exact (Nat.coprime_primes (hp a (Finset.mem_insert_self a s)) (hp l (Finset.mem_insert_of_mem hl))).mpr
      (by rintro rfl; exact ha hl)

theorem sum_prime_pow_le_of_dvd (s : Finset ℕ) (e : ℕ → ℕ) (M : ℕ) (hM : M ≠ 0)
    (hp : ∀ l ∈ s, l.Prime) (he : ∀ l ∈ s, e l ≠ 0) (hd : ∀ l ∈ s, l ^ e l ∣ M) :
    ∑ l ∈ s, l ^ e l ≤ M := by
  have h2 : ∀ l ∈ s, 2 ≤ l ^ e l := fun l hl => le_trans (hp l hl).two_le (Nat.le_self_pow (he l hl) l)
  exact (sum_le_prod_of_two_le s _ h2).trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (prod_prime_pow_dvd_of_forall_dvd s e M hp hd))

private theorem padicValNat_pow_sub_one_eq_add (g d l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hd : d ≠ 0)
    (hl : l.Prime) (hlg : l ∣ g - 1) :
    padicValNat l (g ^ d - 1) = padicValNat l (g - 1) + padicValNat l d := by
  have := Fact.mk hl
  have hlg' : ¬ l ∣ g := by
    intro h
    have h' := Nat.dvd_sub h hlg
    have e : g - (g - 1) = 1 := by omega
    rw [e] at h'
    exact hl.one_lt.ne' (Nat.dvd_one.mp h')
  rcases hl.eq_two_or_odd' with rfl | hodd
  · have hx : ¬ (2 : ℤ) ∣ (g : ℤ) := by exact_mod_cast hlg'
    have h4' : (4 : ℤ) ∣ (g : ℤ) - 1 := by
      have := Int.natCast_dvd_natCast.mpr h4
      rwa [Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_one, Nat.cast_ofNat] at this
    have key := Int.two_pow_sub_pow' d h4' hx
    rw [one_pow] at key
    have e1 : (g : ℤ) ^ d - 1 = ((g ^ d - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
      push_cast
      ring
    have e2 : (g : ℤ) - 1 = ((g - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ g)]
      push_cast
      ring
    have e3 : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
    rw [e1, e2, e3, Int.natCast_emultiplicity, Int.natCast_emultiplicity, Int.natCast_emultiplicity] at key
    have hN : g ^ d - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hd (by omega))
    rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, padicValNat_eq_emultiplicity hN,
      padicValNat_eq_emultiplicity (by omega : g - 1 ≠ 0), padicValNat_eq_emultiplicity hd]
    exact key
  · have := padicValNat.pow_sub_pow hodd (by omega : 1 < g) hlg hlg' hd
    rwa [one_pow] at this

theorem pow_padicValNat_pow_sub_one_dvd (g d l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hd : d ≠ 0)
    (hl : l.Prime) (hlg : l ∣ g - 1) : l ^ padicValNat l (g ^ d - 1) ∣ d * (g - 1) := by
  rw [padicValNat_pow_sub_one_eq_add g d l hg h4 hd hl hlg, pow_add, mul_comm d]
  exact mul_dvd_mul pow_padicValNat_dvd pow_padicValNat_dvd

theorem sum_primePowerPart_pow_sub_one_le :
    ∀ g d : ℕ, 2 ≤ g → 4 ∣ g - 1 → 2 ≤ d → (∑ l ∈ (g ^ d - 1).primeFactors, ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) ≤ d * ((g : ℝ) - 1) + ((g : ℝ) ^ d - 1) / ((g : ℝ) - 1) := by
  intro g d hg h4 hd
  set N := g ^ d - 1 with hN
  have hd0 : d ≠ 0 := by omega
  have hg1 : g - 1 ≠ 0 := by omega
  have hdiv : g - 1 ∣ N := by simpa using Nat.sub_dvd_pow_sub_pow g 1 d
  have hv : ∀ l ∈ N.primeFactors, padicValNat l N ≠ 0 := by
    intro l hl
    obtain ⟨hlp, hlN, hN0⟩ := Nat.mem_primeFactors.mp hl
    have := Fact.mk hlp
    exact Nat.one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hN0 hlN)
  have hnat : ∑ l ∈ N.primeFactors, l ^ padicValNat l N ≤ d * (g - 1) + N / (g - 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (fun l => l ∣ g - 1)]
    refine add_le_add ?_ ?_
    · refine sum_prime_pow_le_of_dvd _ _ _ (mul_ne_zero hd0 hg1)
        (fun l hl => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hl).1).1)
        (fun l hl => hv l (Finset.mem_filter.mp hl).1) (fun l hl => ?_)
      obtain ⟨hl1, hlg⟩ := Finset.mem_filter.mp hl
      exact pow_padicValNat_pow_sub_one_dvd g d l hg h4 hd0 (Nat.mem_primeFactors.mp hl1).1 hlg
    · have hQ0 : N / (g - 1) ≠ 0 := by
        intro h0
        have hm := Nat.div_mul_cancel hdiv
        rw [h0, zero_mul] at hm
        have : 1 < g ^ d := Nat.one_lt_pow hd0 (by omega)
        omega
      refine sum_prime_pow_le_of_dvd _ _ _ hQ0
        (fun l hl => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hl).1).1)
        (fun l hl => hv l (Finset.mem_filter.mp hl).1) (fun l hl => ?_)
      obtain ⟨hl1, hlg⟩ := Finset.mem_filter.mp hl
      obtain ⟨hlp, -, -⟩ := Nat.mem_primeFactors.mp hl1
      have hcop : Nat.Coprime (l ^ padicValNat l N) (g - 1) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hlg)
      refine hcop.dvd_of_dvd_mul_right ?_
      rw [Nat.div_mul_cancel hdiv]
      exact pow_padicValNat_dvd
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hcast_g1 : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ g)]
    simp
  have hcast_N : ((N : ℕ) : ℝ) = (g : ℝ) ^ d - 1 := by
    rw [hN, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    simp
  have hcast_Q : ((N / (g - 1) : ℕ) : ℝ) = ((g : ℝ) ^ d - 1) / ((g : ℝ) - 1) := by
    rw [Nat.cast_div hdiv (by rw [hcast_g1]; linarith), hcast_N, hcast_g1]
  calc (∑ l ∈ N.primeFactors, ((l ^ padicValNat l N : ℕ) : ℝ))
        = ((∑ l ∈ N.primeFactors, l ^ padicValNat l N : ℕ) : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ((d * (g - 1) + N / (g - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = _ := by rw [Nat.cast_add, Nat.cast_mul, hcast_g1, hcast_Q]

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRangeMulEq
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem sum_range_mul_eq (h : ℕ → ℂ) (q r : ℕ) :
    ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range q, h (j + q * i) = ∑ m ∈ Finset.range (q * r), h m := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.add_comm]

theorem im_div_pos (τ : ℍ) (j q : ℕ) (hq : 0 < q) : 0 < (((τ : ℂ) + j) / q).im := by
  rw [Complex.div_natCast_im]
  simp only [Complex.add_im, Complex.natCast_im, add_zero]
  exact div_pos τ.im_pos (by exact_mod_cast hq)

theorem uOp_uOp_eq (f : ℍ → ℂ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (τ : ℍ) :
    uOp a (uOp b f) τ =
      ((a : ℂ) * b)⁻¹ * ∑ m ∈ Finset.range (a * b), f (ofComplex (((τ : ℂ) + m) / ((a : ℂ) * b))) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [uOp]
  rw [← sum_range_mul_eq (fun m : ℕ => f (ofComplex (((τ : ℂ) + m) / ((a : ℂ) * b)))) a b]
  conv_rhs => rw [Finset.sum_comm]
  rw [mul_inv, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofComplex_apply_of_im_pos (im_div_pos τ j a ha)]
  congr 2
  push_cast
  field_simp
  ring

theorem uOp_comm (f : ℍ → ℂ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    uOp q (uOp r f) = uOp r (uOp q f) := by
  funext τ
  rw [uOp_uOp_eq f q r hq hr, uOp_uOp_eq f r q hr hq, mul_comm (r : ℂ), Nat.mul_comm r q]

theorem sum_mul_mod (G : ℕ → ℂ) (q r : ℕ) (hq : 0 < q) (hc : Nat.Coprime q r) :
    ∑ j ∈ Finset.range q, G (r * j % q) = ∑ j ∈ Finset.range q, G j := by
  have hinj : Set.InjOn (fun j => r * j % q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h1 : a ≡ b [MOD q] := Nat.ModEq.cancel_left_of_coprime hc hab
    unfold Nat.ModEq at h1
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  have himg : (Finset.range q).image (fun j => r * j % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨a, _, rfl⟩ := hx
      exact Nat.mod_lt _ hq
    · rw [Finset.card_image_of_injOn hinj]
  rw [← Finset.sum_image hinj, himg]

theorem per_ofComplex (g : ℍ → ℂ) (hper : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) (z : ℂ) (hz : 0 < z.im) :
    g (ofComplex (z + 1)) = g (ofComplex z) := by
  have hz1 : 0 < (z + 1).im := by simpa using hz
  have h1 : ofComplex (z + 1) = (1 : ℝ) +ᵥ ofComplex z := by
    apply UpperHalfPlane.ext
    rw [coe_vadd, ofComplex_apply_of_im_pos hz1, ofComplex_apply_of_im_pos hz]
    push_cast
    ring
  rw [h1, hper]

theorem uOp_vOp (g : ℍ → ℂ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hc : Nat.Coprime q r)
    (hper : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) :
    uOp q (vOp r g) = vOp r (uOp q g) := by
  funext τ
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hw : 0 < ((r : ℂ) * τ).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hr) τ.im_pos
  simp only [uOp, vOp]
  rw [ofComplex_apply_of_im_pos hw]
  congr 1
  set w : ℂ := (r : ℂ) * τ with hwdef
  set G : ℕ → ℂ := fun m => g (ofComplex ((w + m) / q)) with hG
  have hGq : ∀ m n : ℕ, G (m + q * n) = G m := by
    intro m n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih]
      simp only [hG]
      have hpos : 0 < ((w + ((m + q * n : ℕ) : ℂ)) / q).im := by
        rw [Complex.div_natCast_im]
        simp only [Complex.add_im, Complex.natCast_im, add_zero]
        exact div_pos hw (by exact_mod_cast hq)
      rw [← per_ofComplex g hper _ hpos]
      congr 2
      push_cast
      field_simp
      ring
  have hmod : ∀ m, G m = G (m % q) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m q]
    exact hGq _ _
  calc ∑ j ∈ Finset.range q, g (ofComplex ((r : ℂ) * ↑(ofComplex (((τ : ℂ) + j) / q))))
      = ∑ j ∈ Finset.range q, G (r * j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hG]
        rw [ofComplex_apply_of_im_pos (im_div_pos τ j q hq)]
        congr 2
        rw [hwdef]
        push_cast
        field_simp
    _ = ∑ j ∈ Finset.range q, G (r * j % q) := Finset.sum_congr rfl fun j _ => hmod _
    _ = ∑ j ∈ Finset.range q, G j := sum_mul_mod G q r hq hc
    _ = _ := rfl

theorem uOp_add (q : ℕ) (f g : ℍ → ℂ) : uOp q (f + g) = uOp q f + uOp q g := by
  funext τ
  simp [uOp, Finset.sum_add_distrib, mul_add]

theorem uOp_smul (q : ℕ) (c : ℂ) (f : ℍ → ℂ) : uOp q (c • f) = c • uOp q f := by
  funext τ
  simp [uOp, Finset.mul_sum, mul_left_comm]

theorem T_mem_lev (N l : ℕ) : ModularGroup.T ∈ lev N l := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    simp [ModularGroup.T]
  · rw [Gamma0_mem]
    simp [ModularGroup.T]

theorem uOp_heckeT_comm : ∀ (N l q r : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    r.Prime → ¬ r ∣ N * l → GlobalTheory.Hk.IsDia N l r σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.uOp q (GlobalTheory.Hk.heckeT k r σ ⇑f) = GlobalTheory.Hk.heckeT k r σ (GlobalTheory.Hk.uOp q ⇑f) := by
  intro N l q r k σ hN hl hq hqd hr hrd hσ f
  have hq0 : 0 < q := hq.pos
  have hr0 : 0 < r := hr.pos
  have hne : q ≠ r := fun h => hrd (h ▸ hqd)
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hne
  have hinv : ∀ γ ∈ lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ => by
    rw [SL_slash]; exact f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  have hper : ∀ τ : ℍ, ((⇑f) ∣[k] σ) ((1 : ℝ) +ᵥ τ) = ((⇑f) ∣[k] σ) τ := by
    intro τ
    have h1 : ((⇑f) ∣[k] σ) ∣[k] ModularGroup.T = (⇑f) ∣[k] σ := by
      have e : σ * ModularGroup.T = (σ * ModularGroup.T * σ⁻¹) * σ := by group
      rw [← SlashAction.slash_mul, e, SlashAction.slash_mul,
        hinv _ (isDia_conj_mem_lev N l r σ _ hσ (T_mem_lev N l))]
    have h2 := congr_fun h1 τ
    have hden : denom (ModularGroup.T : GL (Fin 2) ℝ) τ = 1 := by
      rw [denom]; simp [ModularGroup.coe_T]
    rw [SL_slash_apply, modular_T_smul] at h2
    simpa [hden] using h2
  have hd := GlobalTheory.T.heckeUOperatorExplicit_comm_diamondOperatorOfMatrix N l q k r σ hN hl hq hqd hσ f
  unfold GlobalTheory.Hk.dia at hd
  simp only [GlobalTheory.Hk.heckeT]
  rw [uOp_add, uOp_smul, uOp_comm _ q r hq0 hr0, uOp_vOp _ q r hq0 hr0 hcop hper, hd]

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGnExponentsKummerCochainsStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerGn_exponents_kummer_cochains : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n m : ℕ), 2 * n ≤ m → ∀ lz lq : Gal p Ω → ZMod (p ^ n),
  IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq → ∀ g ∈ Gn T n,
  ∃ (i j : ℕ) (s t : ℤ), g (T.ζ m) = T.ζ m ^ i ∧ g (T.qq m) = T.ζ m ^ j * T.qq m ∧
    (i : ℤ) = 1 + p ^ n * ((lz g).val : ℤ) + p ^ (2 * n) * s ∧ (j : ℤ) = p ^ n * ((lq g).val : ℤ) + p ^ (2 * n) * t := by
  first | exact @GlobalTheory.KumExpo.exponents | exact GlobalTheory.KumExpo.exponents | (intros; apply GlobalTheory.KumExpo.exponents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WirtingerEichlerStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_eichler_sub_conj_wirtinger : ∀ (w : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → ∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun z : ℂ => (eichler w f (ofComplex z) - (eichler w h (ofComplex z)).map (starRingEnd ℂ) - p).eval z) L s ∧ L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s)) := by
  first | exact @GlobalTheory.EichlerDbar.wirtinger_eichler | exact GlobalTheory.EichlerDbar.wirtinger_eichler | (intros; apply GlobalTheory.EichlerDbar.wirtinger_eichler <;> assumption)
end

