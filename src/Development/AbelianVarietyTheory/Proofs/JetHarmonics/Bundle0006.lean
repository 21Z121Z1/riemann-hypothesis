import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAdd
section
namespace GlobalTheory.PrimeLogSum
open Finset

open Finset in
private lemma log_three_lt_one_point_one_one : Real.log 3 < 1.11 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp 0.11
  have h3 : Real.exp 1.11 = Real.exp 1 * Real.exp 0.11 := by
    rw [← Real.exp_add]; norm_num
  rw [h3]
  nlinarith

open Finset in
private lemma log_succ_div_le_telescoping_sub (n : ℕ) (hn : 3 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1))
      ≤ (Real.log n + 4 / 3) / n - (Real.log ((n + 1 : ℕ) : ℝ) + 4 / 3) / ((n + 1 : ℕ) : ℝ) := by
  push_cast
  set x : ℝ := (n : ℝ) with hx
  have hx3 : (3 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hd : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div (by positivity) hx0.ne'] at h
    have : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have h1 : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ (x + 1) * (1 / x) :=
    mul_le_mul_of_nonneg_left hd (by linarith)
  have h2 : (x + 1) * (1 / x) ≤ 4 / 3 := by
    rw [mul_one_div, div_le_iff₀ hx0]; linarith
  have key : Real.log (x + 1)
      ≤ (x + 1) * (Real.log x + 4 / 3) - x * (Real.log (x + 1) + 4 / 3) := by
    nlinarith
  have hpos : 0 < (x + 1) * x := by positivity
  calc Real.log (x + 1) / ((x + 1) * (x + 1 - 1))
      = Real.log (x + 1) / ((x + 1) * x) := by ring_nf
    _ ≤ ((x + 1) * (Real.log x + 4 / 3) - x * (Real.log (x + 1) + 4 / 3)) / ((x + 1) * x) :=
        div_le_div_of_nonneg_right key hpos.le
    _ = (Real.log x + 4 / 3) / x - (Real.log (x + 1) + 4 / 3) / (x + 1) := by
        field_simp

open Finset in
private lemma sum_log_div_mul_pred_add_le_const (N : ℕ) (hN : 3 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) + (Real.log N + 4 / 3) / N
      ≤ Real.log 2 / 2 + Real.log 3 / 6 + (Real.log 3 + 4 / 3) / 3 := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp [Finset.sum_range_succ]
    norm_num
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have := log_succ_div_le_telescoping_sub n hn
    linarith

open Finset in
private lemma div_le_factorization_factorial' (N p : ℕ) (hp : p.Prime) :
    N / p ≤ (N.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (lt_add_one (Nat.log p N))]
  rcases Nat.lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  · have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
      simp [Nat.log_pos hp.one_lt h]
    simpa using single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1

open Finset in
private lemma mul_sum_prime_log_div_le_log_factorial_add (N : ℕ) :
    (N : ℝ) * ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log (N.factorial : ℝ) + N * Real.log 4 := by
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hfac : Real.log (N.factorial : ℝ)
      = ∑ p ∈ P, ((N.factorial).factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization]
    apply Finsupp.sum_of_support_subset
    · intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      simp only [hP, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le ((hp.1.dvd_factorial).1 hp.2.1), hp.1⟩
    · intro i _
      simp
  have htheta : ∑ p ∈ P, Real.log p ≤ N * Real.log 4 := by
    rw [← Real.log_prod (fun p hp => by
      have := (Finset.mem_filter.1 hp).2.pos
      positivity), ← Real.log_pow]
    apply Real.log_le_log
    · exact Finset.prod_pos fun p hp => by
        have := (Finset.mem_filter.1 hp).2.pos
        positivity
    · have h := primorial_le_four_pow N
      have h' : ((primorial N : ℕ) : ℝ) ≤ ((4 ^ N : ℕ) : ℝ) := by exact_mod_cast h
      simpa [primorial, hP, Nat.cast_prod] using h'
  rw [Finset.mul_sum, hfac]
  calc ∑ p ∈ P, (N : ℝ) * (Real.log p / p)
      ≤ ∑ p ∈ P, (((N.factorial).factorization p : ℝ) * Real.log p + Real.log p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := (Finset.mem_filter.1 hp).2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        have hv : ((N / p : ℕ) : ℝ) ≤ ((N.factorial).factorization p : ℝ) := by
          exact_mod_cast div_le_factorization_factorial' N p hp'
        have hlt : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by
          exact_mod_cast Nat.lt_div_mul_add hp'.pos
        have hq : (N : ℝ) / p ≤ ((N.factorial).factorization p : ℝ) + 1 := by
          rw [div_le_iff₀ hp0]
          nlinarith
        calc (N : ℝ) * (Real.log p / p) = (N : ℝ) / p * Real.log p := by ring
          _ ≤ (((N.factorial).factorization p : ℝ) + 1) * Real.log p :=
            mul_le_mul_of_nonneg_right hq hlog
          _ = _ := by ring
    _ = ∑ p ∈ P, ((N.factorial).factorization p : ℝ) * Real.log p + ∑ p ∈ P, Real.log p :=
        Finset.sum_add_distrib
    _ ≤ _ := by linarith

open Finset in
private lemma log_factorial_le_stirling_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + 1 + Real.log n / 2 := by
  have h1 : Real.log (Stirling.stirlingSeq n) ≤ Real.log (Stirling.stirlingSeq 1) := by
    have := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (n - 1))
    simpa [Function.comp, Nat.sub_add_cancel hn] using this
  rw [Stirling.log_stirlingSeq_formula, Stirling.log_stirlingSeq_formula] at h1
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul (by norm_num) hn0, Real.log_div hn0 (Real.exp_pos 1).ne', Real.log_exp] at h1
  simp only [Nat.factorial_one, Nat.cast_one, mul_one, Real.log_one, one_div, Real.log_inv,
    Real.log_exp] at h1
  linarith [h1]

open Finset in

theorem _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le : ∀ N : ℕ,
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
      ≤ Real.log N + 2.2 := by
  intro N
  have hl2 := Real.log_two_lt_d9
  have hl3 := log_three_lt_one_point_one_one
  have hl3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rcases Nat.lt_or_ge N 4 with hN | hN
  · interval_cases N <;>
      simp [Finset.sum_filter, Finset.sum_range_succ, Nat.prime_two, Nat.prime_three] <;>
      norm_num <;> linarith
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hsplit : ∑ p ∈ P, Real.log p / ((p : ℝ) - 1)
      = ∑ p ∈ P, Real.log p / p + ∑ p ∈ P, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
    have h3 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h4 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hB : ∑ p ∈ P, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ n ∈ Finset.range (N + 1), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n _ _
    apply div_nonneg (Real.log_natCast_nonneg n)
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  have hC := sum_log_div_mul_pred_add_le_const N (by omega)
  have hg : 0 ≤ (Real.log N + 4 / 3) / N :=
    div_nonneg (by linarith [Real.log_natCast_nonneg N]) (Nat.cast_nonneg N)
  have hA := mul_sum_prime_log_div_le_log_factorial_add N
  have hF := log_factorial_le_stirling_bound N (by omega)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : Real.log N ≤ 0.4 * N := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / Real.exp 1 by positivity)
    rw [Real.log_div hNpos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    have he := Real.exp_one_gt_d9
    have h5 : (N : ℝ) / Real.exp 1 ≤ 0.4 * N := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      nlinarith
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hA' : ∑ p ∈ P, Real.log p / p ≤ Real.log N - 1 + 0.25 + 0.2 + Real.log 4 := by
    have h : (N : ℝ) * ∑ p ∈ P, Real.log p / p
        ≤ N * (Real.log N - 1 + 0.25 + 0.2 + Real.log 4) := by
      linarith
    exact le_of_mul_le_mul_left h hNpos
  rw [hsplit]
  linarith

end GlobalTheory.PrimeLogSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SurjectiveOfKerLeMapSupSq
section
namespace GlobalTheory.SurjectiveOfKerSq

theorem eq_of_le_sup_sq {B : Type} [CommRing B] (I K : Ideal B) (m : ℕ)
    (hnil : I ^ (m + 1) = ⊥) (h1 : K ≤ I) (h2 : I ≤ K ⊔ I ^ 2) : I = K := by
  have key : ∀ n : ℕ, I ≤ K ⊔ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine h2.trans (sup_le le_sup_left ?_)
      calc I ^ 2 = I * I := pow_two I
        _ ≤ I * (K ⊔ I ^ (n + 1)) := Ideal.mul_mono_right ih
        _ = I * K ⊔ I ^ (n + 1 + 1) := by rw [Ideal.mul_sup, ← pow_succ']
        _ ≤ K ⊔ I ^ (n + 1 + 1) := sup_le_sup_right Ideal.mul_le_right _
  have := key m
  rw [hnil, sup_bot_eq] at this
  exact le_antisymm this h1

theorem surjective_of_ker_le_map_sup_sq {V : Type} [CommRing V] {A B : Type} [CommRing A]
    [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) (aug : B →ₐ[V] V) (m : ℕ)
    (hnil : RingHom.ker aug ^ (m + 1) = ⊥) (J : Ideal A)
    (h1 : Ideal.map f J ≤ RingHom.ker aug)
    (h2 : RingHom.ker aug ≤ Ideal.map f J ⊔ RingHom.ker aug ^ 2) :
    Function.Surjective f := by
  have hI : RingHom.ker aug = Ideal.map f J := eq_of_le_sup_sq _ _ m hnil h1 h2
  have base : ∀ b : B, ∃ a : A, b - f a ∈ RingHom.ker aug := by
    intro b
    refine ⟨algebraMap V A (aug b), ?_⟩
    simp [RingHom.mem_ker]
  have step : ∀ n : ℕ, ∀ x ∈ RingHom.ker aug ^ n, ∀ b : B,
      ∃ a : A, b * x - f a ∈ RingHom.ker aug ^ (n + 1) := by
    intro n x hx
    have hpow : RingHom.ker aug ^ n = Ideal.span (f '' (J ^ n : Ideal A)) := by
      rw [hI, ← Ideal.map_pow]; rfl
    have hx' := hx
    rw [hpow] at hx'
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      intro b
      obtain ⟨j, hj, rfl⟩ := hy
      obtain ⟨a, ha⟩ := base b
      refine ⟨a * j, ?_⟩
      have hfj : f j ∈ RingHom.ker aug ^ n := by
        rw [hpow]; exact Ideal.subset_span ⟨j, hj, rfl⟩
      have e : b * f j - f (a * j) = f j * (b - f a) := by rw [map_mul]; ring
      rw [e, pow_succ]
      exact Ideal.mul_mem_mul hfj ha
    | zero => intro b; exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      intro b
      obtain ⟨a, ha⟩ := hy b
      obtain ⟨c, hc⟩ := hz b
      refine ⟨a + c, ?_⟩
      have e : b * (y + z) - f (a + c) = (b * y - f a) + (b * z - f c) := by
        rw [map_add]; ring
      rw [e]
      exact Ideal.add_mem _ ha hc
    | smul c y _ hy =>
      intro b
      obtain ⟨a, ha⟩ := hy (b * c)
      exact ⟨a, by rwa [smul_eq_mul, ← mul_assoc]⟩
  have all : ∀ n : ℕ, ∀ b : B, ∃ a : A, b - f a ∈ RingHom.ker aug ^ n := by
    intro n
    induction n with
    | zero => intro b; exact ⟨0, by simp⟩
    | succ n ih =>
      intro b
      obtain ⟨a, ha⟩ := ih b
      obtain ⟨c, hc⟩ := step n _ ha 1
      refine ⟨a + c, ?_⟩
      have e : b - f (a + c) = 1 * (b - f a) - f c := by rw [map_add]; ring
      rw [e]
      exact hc
  intro b
  obtain ⟨a, ha⟩ := all (m + 1) b
  rw [hnil, Ideal.mem_bot, sub_eq_zero] at ha
  exact ⟨a, ha.symm⟩

end GlobalTheory.SurjectiveOfKerSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitsZpowSurjective
section
namespace GlobalTheory.DivisibleUnits

theorem units_zpow_surjective {F : Type} [Field F] [IsAlgClosed F] {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Fˣ => a ^ n) := by
  have nat_root : ∀ (m : ℕ), 0 < m → ∀ x : Fˣ, ∃ y : Fˣ, y ^ m = x := by
    intro m hm x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : F) hm
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hz
      exact x.ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    ext
    simp [hz]
  intro x
  rcases Int.lt_or_gt_of_ne hn with h | h
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x⁻¹
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = -(n.natAbs : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast, hy, inv_inv]
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = (n.natAbs : ℤ) := by omega
    rw [this, zpow_natCast, hy]

noncomputable def divisibleUnits (F : Type) [Field F] [IsAlgClosed F] :
    DivisibleBy (Additive Fˣ) ℤ :=
  divisibleByOfSMulRightSurj (Additive Fˣ) ℤ (fun {n} hn x => by
    obtain ⟨y, hy⟩ := units_zpow_surjective (F := F) hn (Additive.toMul x)
    exact ⟨Additive.ofMul y, by simpa using congrArg Additive.ofMul hy⟩)

theorem exists_extension {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) :
    ∃ κ : M →* Fˣ, ∀ x : H, κ (Φ x) = χ x := by
  letI := divisibleUnits F
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this

theorem target : ∀ {H M F : Type} [inst : CommGroup H] [inst_1 : CommGroup M] [inst_2 : Field F] [IsAlgClosed F] (Φ : H →* M), Function.Injective (⇑Φ : H → M) → ∀ (χ : H →* Fˣ), ∃ (κ : M →* Fˣ), ∀ (x : H), (κ : M → Fˣ) ((Φ : H → M) x) = (χ : H → Fˣ) x :=
  fun Φ hΦ χ => exists_extension Φ hΦ χ

end GlobalTheory.DivisibleUnits
end

