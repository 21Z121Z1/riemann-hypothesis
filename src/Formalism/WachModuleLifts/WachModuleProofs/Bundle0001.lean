import Formalism.WachModuleLifts.Bundle0001

-- bundled from Formalism.WachModuleLifts.WachModuleProofs.LemmaCLower
section
open Finset

noncomputable section

namespace Formalism.CL

section SlopeTestRemainingChoices

variable {p : ℕ} [hp : Fact p.Prime]

lemma one_le_p_real : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le

lemma sum_norm_le {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p]) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

lemma term_le (N i k : ℕ) (a b : ℚ_[p]) (ha : ‖a‖ ≤ (p : ℝ) ^ (i / N))
    (hb : ‖b‖ ≤ (p : ℝ) ^ (k / N)) : ‖a * b‖ ≤ (p : ℝ) ^ ((i + k) / N) := by
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ (p : ℝ) ^ (i / N) * (p : ℝ) ^ (k / N) :=
        mul_le_mul ha hb (norm_nonneg _) (by positivity)
    _ = (p : ℝ) ^ (i / N + k / N) := by rw [pow_add]
    _ ≤ _ := pow_le_pow_right₀ one_le_p_real (Nat.div_add_div_le_add_div)

theorem content_mul (g : ℕ) (f f' : PowerSeries ℚ_[p]) (hf : Content p g f)
    (hf' : Content p g f') : Content p g (f * f') := by
  intro j
  rw [PowerSeries.coeff_mul]
  apply sum_norm_le _ _ (by positivity)
  intro x hx
  have := term_le (p ^ g) x.1 x.2 _ _ (hf x.1) (hf' x.2)
  rwa [mem_antidiagonal.mp hx] at this

theorem content_one (g : ℕ) : Content p g (1 : PowerSeries ℚ_[p]) := by
  intro j
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · rw [norm_one]; exact one_le_pow₀ one_le_p_real
  · rw [norm_zero]; positivity

theorem content_pow (g : ℕ) (f : PowerSeries ℚ_[p]) (hf : Content p g f) (y : ℕ) :
    Content p g (f ^ y) := by
  induction y with
  | zero => rw [pow_zero]; exact content_one g
  | succ y ih => rw [pow_succ]; exact content_mul g _ _ ih hf

lemma coeff_uu (g j : ℕ) :
    PowerSeries.coeff j (uu p g) = (p : ℚ_[p])⁻¹ * (phiIter p g).coeff j := by
  rw [uu, PowerSeries.coeff_smul, Polynomial.coeff_coe, smul_eq_mul]

lemma phiIter_succ' (g : ℕ) : phiIter p (g + 1) = (phiPoly p).comp (phiIter p g) := by
  unfold phiIter; rw [Function.iterate_succ_apply']

lemma phiIter_one : phiIter p 1 = phiPoly p := by
  rw [phiIter_succ', show phiIter p 0 = Polynomial.X from rfl, Polynomial.comp_X]

lemma coeff_phiPoly (j : ℕ) : (phiPoly p).coeff j =
    (if j = p then 1 else 0) - (p : ℚ_[p]) * (if j = p - 1 then 1 else 0) +
      (if j = 0 then (p : ℚ_[p]) else 0) := by
  simp only [phiPoly, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_C]

lemma content_of_unit_one : Content p 1 (uu p 1) := by
  have hp2 := hp.out.two_le
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  intro j
  rw [coeff_uu, phiIter_one, coeff_phiPoly, pow_one]
  by_cases h1 : j = p
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega), h1, Nat.div_self (by omega)]
    simp [norm_inv, Padic.norm_p]
  · rw [if_neg h1]
    have hle : (1 : ℝ) ≤ (p : ℝ) ^ (j / p) := one_le_pow₀ one_le_p_real
    by_cases h2 : j = p - 1
    · rw [if_pos h2, if_neg (by omega)]
      have : (p : ℚ_[p])⁻¹ * (0 - (p : ℚ_[p]) * 1 + 0) = -1 := by
        rw [mul_one, zero_sub, add_zero, mul_neg, inv_mul_cancel₀ hp0]
      rw [this, norm_neg, norm_one]; exact hle
    · rw [if_neg h2]
      by_cases h3 : j = 0
      · rw [if_pos h3]
        have : (p : ℚ_[p])⁻¹ * (0 - (p : ℚ_[p]) * 0 + p) = 1 := by
          rw [mul_zero, sub_zero, zero_add, inv_mul_cancel₀ hp0]
        rw [this, norm_one]; exact hle
      · rw [if_neg h3]; simp

lemma natDegree_phiPoly : (phiPoly p).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_phiPoly, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

lemma coe_phiPoly : ((phiPoly p : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]) =
    (p : ℚ_[p]) • uu p 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [uu, phiIter_one, smul_smul, mul_inv_cancel₀ hp0, one_smul]

lemma norm_coeff_phiPoly_pow (i j : ℕ) :
    ‖((phiPoly p) ^ i).coeff j‖ ≤ ((p : ℝ)⁻¹) ^ i * (p : ℝ) ^ (j / p) := by
  rw [← Polynomial.coeff_coe, Polynomial.coe_pow, coe_phiPoly, smul_pow, PowerSeries.coeff_smul,
    smul_eq_mul, norm_mul, norm_pow, Padic.norm_p]
  have := content_pow 1 _ (content_of_unit_one (p := p)) i j
  rw [pow_one] at this
  exact mul_le_mul_of_nonneg_left this (by positivity)

lemma cotangentAtUnit_tangentBijection_naturality (i k M : ℕ) (hk : k ≤ i) (hM : 0 < M) : i / M + k ≤ k / M + i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : k < M * (k / M + 1) := Nat.lt_mul_div_succ k hM
  have h2 : (k + d) / M < k / M + d + 1 := by
    rw [Nat.div_lt_iff_lt_mul hM]
    nlinarith
  omega

lemma key (g i j : ℕ) :
    (p : ℝ) ^ (i / p ^ g) * ‖((phiPoly p) ^ i).coeff j‖ ≤ (p : ℝ) ^ (j / p ^ (g + 1)) := by
  by_cases hj : p * i < j
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, norm_zero, mul_zero]
    · positivity
    · calc ((phiPoly p) ^ i).natDegree ≤ i * (phiPoly p).natDegree := Polynomial.natDegree_pow_le
        _ ≤ i * p := Nat.mul_le_mul_left _ natDegree_phiPoly
        _ < j := by rw [mul_comm]; exact hj
  · push Not at hj
    have hpos := hp.out.pos
    have hk : j / p ≤ i := Nat.div_le_of_le_mul hj
    have hn := cotangentAtUnit_tangentBijection_naturality i (j / p) (p ^ g) hk (by positivity)
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    calc (p : ℝ) ^ (i / p ^ g) * ‖((phiPoly p) ^ i).coeff j‖
        ≤ (p : ℝ) ^ (i / p ^ g) * (((p : ℝ)⁻¹) ^ i * (p : ℝ) ^ (j / p)) :=
          mul_le_mul_of_nonneg_left (norm_coeff_phiPoly_pow i j) (by positivity)
      _ = ((p : ℝ) ^ (i / p ^ g + j / p)) / (p : ℝ) ^ i := by
          rw [inv_pow, pow_add]; field_simp
      _ ≤ (p : ℝ) ^ (j / p / p ^ g) := by
          rw [div_le_iff₀ (by positivity), ← pow_add]
          exact pow_le_pow_right₀ one_le_p_real hn

end SlopeTestRemainingChoices

end Formalism.CL
end
end

-- bundled from Formalism.WachModuleLifts.WachModuleProofs.LemmaCSharp
section
open Finset

noncomputable section

namespace Formalism.CL

namespace CSharp

variable {p : ℕ} [hp : Fact p.Prime]

def Zp (p : ℕ) [Fact p.Prime] : Polynomial ℚ_[p] :=
  Polynomial.C ((p : ℚ_[p])⁻¹) * Polynomial.X ^ (p - 1) *
    (Polynomial.X + Polynomial.C (-(p : ℚ_[p])))

lemma Zp_pow (n : ℕ) : Zp p ^ n = Polynomial.C ((p : ℚ_[p])⁻¹ ^ n) *
    (Polynomial.X ^ ((p - 1) * n) * (Polynomial.X + Polynomial.C (-(p : ℚ_[p]))) ^ n) := by
  simp only [Zp, mul_pow, Polynomial.C_pow, ← pow_mul]
  ring

lemma coeff_Zp_pow (n m : ℕ) : (Zp p ^ n).coeff m =
    if (p - 1) * n ≤ m then (p : ℚ_[p])⁻¹ ^ n *
      ((-(p : ℚ_[p])) ^ (n - (m - (p - 1) * n)) * (n.choose (m - (p - 1) * n) : ℚ_[p]))
    else 0 := by
  rw [Zp_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs
  · rw [Polynomial.coeff_X_add_C_pow]
  · rw [mul_zero]

lemma norm_natCast_le_one' (m : ℕ) : ‖(m : ℚ_[p])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) (m : ℤ)

lemma norm_coeff_Zp_pow_le (n m : ℕ) (h : (p - 1) * n ≤ m) :
    ‖(Zp p ^ n).coeff m‖ ≤ (p : ℝ) ^ (m - (p - 1) * n) := by
  rw [coeff_Zp_pow, if_pos h]
  set i := m - (p - 1) * n with hi
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
  by_cases hin : i ≤ n
  · rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, norm_neg, Padic.norm_p, inv_inv]
    have hsplit : (p : ℝ) ^ n = (p : ℝ) ^ i * (p : ℝ) ^ (n - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hin]
    have hc := norm_natCast_le_one' (p := p) (n.choose i)
    rw [hsplit, inv_pow]
    have hpi : (0 : ℝ) < (p : ℝ) ^ (n - i) := pow_pos hp0 _
    calc (p : ℝ) ^ i * (p : ℝ) ^ (n - i) * (((p : ℝ) ^ (n - i))⁻¹ * ‖(n.choose i : ℚ_[p])‖)
        = (p : ℝ) ^ i * ‖(n.choose i : ℚ_[p])‖ := by field_simp
      _ ≤ (p : ℝ) ^ i * 1 := by gcongr
      _ = (p : ℝ) ^ i := mul_one _
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero, norm_zero]
    positivity

lemma coeff_Zp_pow_lt (r n : ℕ) (hn : n < r) : (Zp p ^ n).coeff (p * r) = 0 := by
  rw [coeff_Zp_pow]
  split_ifs with h
  · have h1 : p * n < p * r := Nat.mul_lt_mul_of_pos_left hn hp.1.pos
    have h2 : (p - 1) * n + n = p * n := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n hp.1.pos)]
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero]
  · rfl

lemma coeff_Zp_pow_self (r : ℕ) : (Zp p ^ r).coeff (p * r) = (p : ℚ_[p])⁻¹ ^ r := by
  have h2 : (p - 1) * r + r = p * r := by
    rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left r hp.1.pos)]
  rw [coeff_Zp_pow, if_pos (by omega)]
  have h3 : p * r - (p - 1) * r = r := by omega
  rw [h3, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, mul_one]

lemma norm_coeff_Zp_pow_gt (r n : ℕ) (hn : r < n) :
    ‖(Zp p ^ n).coeff (p * r)‖ ≤ (p : ℝ) ^ ((r : ℤ) - ((p - 1 : ℕ) : ℤ)) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.1.one_le
  by_cases h : (p - 1) * n ≤ p * r
  · refine (norm_coeff_Zp_pow_le n (p * r) h).trans ?_
    rw [← zpow_natCast]
    apply zpow_le_zpow_right₀ hp1
    have h2 : (p - 1) * r + r = p * r := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left r hp.1.pos)]
    have h3 : (p - 1) * (r + 1) ≤ (p - 1) * n := Nat.mul_le_mul_left _ hn
    rw [Nat.mul_add, mul_one] at h3
    push_cast [h]
    omega
  · rw [coeff_Zp_pow, if_neg h, norm_zero]
    positivity

lemma core (r : ℕ) (s : Finset ℕ) (hr : r ∈ s) (a : ℕ → ℚ_[p]) (ha : ∀ n, ‖a n‖ ≤ 1)
    (v : ℕ) (hv : v < p - 1) (har : ‖a r‖ = (p : ℝ) ^ (-(v : ℤ))) :
    ‖∑ n ∈ s, (Zp p ^ n).coeff (p * r) * a n‖ = (p : ℝ) ^ ((r : ℤ) - v) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt
  rw [← Finset.add_sum_erase s _ hr]
  have hmain : ‖(Zp p ^ r).coeff (p * r) * a r‖ = (p : ℝ) ^ ((r : ℤ) - v) := by
    rw [coeff_Zp_pow_self, norm_mul, har, norm_pow, norm_inv, Padic.norm_p, inv_inv,
      ← zpow_natCast, ← zpow_add₀ hp0.ne']
    congr 1
  have hrest : ‖∑ n ∈ s.erase r, (Zp p ^ n).coeff (p * r) * a n‖ ≤
      (p : ℝ) ^ ((r : ℤ) - ((p - 1 : ℕ) : ℤ)) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro n hn
    have hnr : n ≠ r := Finset.ne_of_mem_erase hn
    rw [norm_mul]
    rcases lt_or_gt_of_ne hnr with hlt | hgt
    · rw [coeff_Zp_pow_lt r n hlt, norm_zero, zero_mul]
      positivity
    · calc ‖(Zp p ^ n).coeff (p * r)‖ * ‖a n‖ ≤ ‖(Zp p ^ n).coeff (p * r)‖ * 1 := by
            gcongr; exact ha n
        _ ≤ _ := by rw [mul_one]; exact norm_coeff_Zp_pow_gt r n hgt
  have hlt : (p : ℝ) ^ ((r : ℤ) - ((p - 1 : ℕ) : ℤ)) < (p : ℝ) ^ ((r : ℤ) - v) :=
    zpow_lt_zpow_right₀ hp1 (by omega)
  have hne : ‖(Zp p ^ r).coeff (p * r) * a r‖ ≠
      ‖∑ n ∈ s.erase r, (Zp p ^ n).coeff (p * r) * a n‖ := by
    rw [hmain]; exact (lt_of_le_of_lt hrest hlt).ne'
  rw [Padic.add_eq_max_of_ne hne, hmain]
  exact max_eq_left (hrest.trans hlt.le)

end CSharp

end Formalism.CL
end
end

-- bundled from Formalism.WachModuleLifts.WachModuleProofs.LemmaCSharpOddG
section
open Finset

noncomputable section

namespace Formalism.CL

namespace CSOddG

section Digits

variable {p : ℕ} [hp : Fact p.Prime]

def S (p n : ℕ) : ℕ := (Nat.digits p n).sum

end Digits

section Poly

variable {p : ℕ} [hp : Fact p.Prime]

def U (p : ℕ) [Fact p.Prime] (g : ℕ) : Polynomial ℚ_[p] :=
  Polynomial.C ((p : ℚ_[p])⁻¹) * phiIter p g

lemma pQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.1.ne_zero

lemma phiIter_succ' (g : ℕ) : phiIter p (g + 1) = (phiPoly p).comp (phiIter p g) := by
  simp only [phiIter, Function.iterate_succ_apply']

lemma U_zero : U p 0 = Polynomial.C ((p : ℚ_[p])⁻¹) * Polynomial.X := by
  simp [U, phiIter]

lemma U_succ (g : ℕ) : U p (g + 1) =
    Polynomial.C ((p : ℚ_[p]) ^ (p - 1)) * U p g ^ (p - 1) * (U p g - 1) + 1 := by
  have hab : Polynomial.C ((p : ℚ_[p])⁻¹) * Polynomial.C (p : ℚ_[p]) = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ pQ_ne, Polynomial.C_1]
  have hQ : phiIter p g = Polynomial.C (p : ℚ_[p]) * U p g := by
    rw [U, ← mul_assoc, mul_comm (Polynomial.C (p : ℚ_[p])), hab, one_mul]
  have hpow : ∀ x : Polynomial ℚ_[p], x ^ p = x ^ (p - 1) * x := fun x => by
    rw [← pow_succ, Nat.sub_add_cancel hp.1.one_le]
  rw [U, phiIter_succ', hQ]
  simp only [phiPoly, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_pow_comp]
  rw [hpow, mul_pow, Polynomial.C_pow]
  set a := Polynomial.C (p : ℚ_[p])
  set b := Polynomial.C ((p : ℚ_[p])⁻¹)
  set u := U p g
  linear_combination (a ^ (p - 1) * u ^ (p - 1) * u - a ^ (p - 1) * u ^ (p - 1) + 1) * hab

lemma U_deg (g : ℕ) : (U p g).natDegree ≤ p ^ g ∧ (U p g).coeff (p ^ g) = (p : ℚ_[p])⁻¹ := by
  induction g with
  | zero =>
    rw [U_zero, pow_zero]
    refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans (by simp), by simp⟩
  | succ g ih =>
    obtain ⟨h1, h2⟩ := ih
    have hp1 := hp.1.one_le
    have hdegpow : (U p g ^ (p - 1)).natDegree ≤ (p - 1) * p ^ g :=
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ h1)
    have hdegsub : (U p g - 1).natDegree ≤ p ^ g :=
      (Polynomial.natDegree_sub_le _ _).trans (max_le h1 (by simp))
    have hsum : (p - 1) * p ^ g + p ^ g = p ^ (g + 1) := by
      rw [pow_succ, mul_comm (p ^ g) p]
      nth_rw 2 [← one_mul (p ^ g)]
      rw [← Nat.add_mul, Nat.sub_add_cancel hp1]
    constructor
    · rw [U_succ]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
      refine (Polynomial.natDegree_mul_le).trans ?_
      refine (Nat.add_le_add_right ((Polynomial.natDegree_C_mul_le _ _).trans hdegpow) _).trans ?_
      exact (Nat.add_le_add_left hdegsub _).trans hsum.le
    · have hform : U p (g + 1) =
          Polynomial.C ((p : ℚ_[p]) ^ (p - 1)) * (U p g ^ p - U p g ^ (p - 1)) + 1 := by
        rw [U_succ]
        have : U p g ^ p = U p g ^ (p - 1) * U p g := by
          rw [← pow_succ, Nat.sub_add_cancel hp1]
        rw [this]; ring
      have hne : p ^ (g + 1) ≠ 0 := pow_ne_zero _ hp.1.ne_zero
      have hc1 : (U p g ^ p).coeff (p ^ (g + 1)) = ((p : ℚ_[p])⁻¹) ^ p := by
        rw [pow_succ', Polynomial.coeff_pow_of_natDegree_le h1, h2]
      have hc2 : (U p g ^ (p - 1)).coeff (p ^ (g + 1)) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        refine lt_of_le_of_lt hdegpow ?_
        rw [← hsum]
        have := pow_pos hp.1.pos g
        omega
      rw [hform, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub, hc1, hc2,
        Polynomial.coeff_one, if_neg hne, sub_zero, add_zero]
      have : ((p : ℚ_[p])⁻¹) ^ p = ((p : ℚ_[p])⁻¹) ^ (p - 1) * (p : ℚ_[p])⁻¹ := by
        rw [← pow_succ, Nat.sub_add_cancel hp1]
      rw [this, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ pQ_ne, one_pow, one_mul]

lemma Z_deg (g : ℕ) : (U p g - 1).natDegree ≤ p ^ g :=
  (Polynomial.natDegree_sub_le _ _).trans (max_le (U_deg g).1 (by simp))

lemma Z_pow_top (g r : ℕ) : ((U p g - 1) ^ r).coeff (p ^ g * r) = ((p : ℚ_[p])⁻¹) ^ r := by
  rw [mul_comm, Polynomial.coeff_pow_of_natDegree_le (Z_deg g), Polynomial.coeff_sub,
    (U_deg g).2, Polynomial.coeff_one, if_neg (pow_ne_zero _ hp.1.ne_zero), sub_zero]

lemma Z_pow_lt (g r n : ℕ) (h : n < r) : ((U p g - 1) ^ n).coeff (p ^ g * r) = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  refine lt_of_le_of_lt (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (Z_deg g))) ?_
  rw [mul_comm]
  exact Nat.mul_lt_mul_of_pos_left h (pow_pos hp.1.pos g)

end Poly

section Norms

variable {p : ℕ} [hp : Fact p.Prime]

lemma norm_pinv_pow (k : ℕ) : ‖((p : ℚ_[p])⁻¹) ^ k‖ = (p : ℝ) ^ (k : ℤ) := by
  rw [norm_pow, norm_inv, Padic.norm_p, inv_inv, zpow_natCast]

lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt

end Norms

section Main

variable {p : ℕ} [hp : Fact p.Prime]

def W (p : ℕ) [Fact p.Prime] (g : ℕ) : Prop :=
  ∀ y n : ℕ, n ≤ y →
    ‖(U p g ^ y).coeff (p ^ g * n)‖ ≤ (p : ℝ) ^ ((n : ℤ) - padicValNat p (y.choose n))

def K (p : ℕ) [Fact p.Prime] (g : ℕ) : Prop :=
  ∀ r n : ℕ, r < n →
    ‖((U p g - 1) ^ n).coeff (p ^ g * r)‖ ≤ (p : ℝ) ^ ((r : ℤ) - 1) * ‖((n.choose r : ℕ) : ℚ_[p])‖

lemma core (g : ℕ) (hK : K p g) (r : ℕ) (s : Finset ℕ) (hr : r ∈ s) (a : ℕ → ℚ_[p])
    (ha : ∀ n, r < n → ‖a n‖ * ‖((n.choose r : ℕ) : ℚ_[p])‖ ≤ ‖a r‖) (har : a r ≠ 0) :
    ‖∑ n ∈ s, ((U p g - 1) ^ n).coeff (p ^ g * r) * a n‖ = (p : ℝ) ^ (r : ℤ) * ‖a r‖ := by
  rw [← Finset.add_sum_erase s _ hr]
  have hmain : ‖((U p g - 1) ^ r).coeff (p ^ g * r) * a r‖ = (p : ℝ) ^ (r : ℤ) * ‖a r‖ := by
    rw [Z_pow_top, norm_mul, norm_pinv_pow]
  have har' : 0 < ‖a r‖ := norm_pos_iff.mpr har
  have hrest : ‖∑ n ∈ s.erase r, ((U p g - 1) ^ n).coeff (p ^ g * r) * a n‖ ≤
      (p : ℝ) ^ ((r : ℤ) - 1) * ‖a r‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro n hn
    have hnr : n ≠ r := Finset.ne_of_mem_erase hn
    rw [norm_mul]
    rcases lt_or_gt_of_ne hnr with hlt | hgt
    · rw [Z_pow_lt g r n hlt, norm_zero, zero_mul]; positivity
    · calc ‖((U p g - 1) ^ n).coeff (p ^ g * r)‖ * ‖a n‖
          ≤ (p : ℝ) ^ ((r : ℤ) - 1) * ‖((n.choose r : ℕ) : ℚ_[p])‖ * ‖a n‖ := by
            gcongr; exact hK r n hgt
        _ = (p : ℝ) ^ ((r : ℤ) - 1) * (‖a n‖ * ‖((n.choose r : ℕ) : ℚ_[p])‖) := by ring
        _ ≤ (p : ℝ) ^ ((r : ℤ) - 1) * ‖a r‖ := by gcongr; exact ha n hgt
  have hlt : (p : ℝ) ^ ((r : ℤ) - 1) * ‖a r‖ < (p : ℝ) ^ (r : ℤ) * ‖a r‖ := by
    gcongr
    · exact one_lt_p
    · omega
  have hne : ‖((U p g - 1) ^ r).coeff (p ^ g * r) * a r‖ ≠
      ‖∑ n ∈ s.erase r, ((U p g - 1) ^ n).coeff (p ^ g * r) * a n‖ := by
    rw [hmain]; exact (lt_of_le_of_lt hrest hlt).ne'
  rw [Padic.add_eq_max_of_ne hne, hmain]
  exact max_eq_left (hrest.trans hlt.le)

end Main

end CSOddG

end Formalism.CL
end
end

-- bundled from Formalism.WachModuleLifts.WachModuleProofs.LemmaCSharpOddUnitInvHolds
section
open Finset

noncomputable section

namespace Formalism.CL

namespace CSharpOdd1

variable {p : ℕ} [hp : Fact p.Prime]

def Zp (p : ℕ) [Fact p.Prime] : Polynomial ℚ_[p] :=
  Polynomial.C ((p : ℚ_[p])⁻¹) * Polynomial.X ^ (p - 1) *
    (Polynomial.X + Polynomial.C (-(p : ℚ_[p])))

end CSharpOdd1

end Formalism.CL
end
end

-- bundled from Formalism.WachModuleLifts.WachModuleProofs.LemmaHLift
section
namespace Formalism.CL

open Finset

theorem legendreBound : Legendre := by
  unfold Legendre
  intro p hp m
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  have hq : 0 < q := by have := hp.out.one_lt; omega
  have key : q * padicValNat (q + 1) m.factorial ≤ m := by
    have h := sub_one_mul_padicValNat_factorial (p := q + 1) m
    rw [Nat.add_sub_cancel] at h
    omega
  have hN : (m + padicValNat (q + 1) m.factorial) * q ≤ m * (q + 1) := by nlinarith [key]
  push_cast
  try simp only [add_sub_cancel_right]
  rw [le_div_iff₀ (by exact_mod_cast hq)]
  exact_mod_cast hN

end Formalism.CL
end

