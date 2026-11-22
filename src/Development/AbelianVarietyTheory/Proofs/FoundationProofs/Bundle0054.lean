import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdSmoothedThetaQProductDistribution
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.Sieg.Distr

open Filter Topology Finset

def E (q u : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ n * u)

def T (q u : ℂ) : ℂ := E q u * E q (q * u⁻¹)

lemma summ {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : Summable fun n : ℕ => ‖-(q ^ n * u)‖ := by
  simp only [norm_neg, norm_mul, norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _

lemma mult {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : Multipliable fun n : ℕ => (1 - q ^ n * u) := by
  simp only [sub_eq_add_neg]
  exact multipliable_one_add_of_summable (summ hq u)

lemma E_ne {q : ℂ} (hq : ‖q‖ < 1) {u : ℂ} (h : ∀ n : ℕ, q ^ n * u ≠ 1) : E q u ≠ 0 := by
  unfold E
  simp only [sub_eq_add_neg]
  refine tprod_one_add_ne_zero_of_summable (fun n => ?_) (summ hq u)
  rw [← sub_eq_add_neg]
  exact sub_ne_zero.mpr (h n).symm

lemma E_tend {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) :
    Tendsto (fun N => ∏ n ∈ range N, (1 - q ^ n * u)) atTop (𝓝 (E q u)) :=
  (mult hq u).hasProd.tendsto_prod_nat

lemma E_step {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : E q u = (1 - u) * E q (q * u) := by
  have h1 := (E_tend hq u).comp (tendsto_add_atTop_nat 1)
  have h2 := (E_tend hq (q * u)).const_mul (1 - u)
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  simp only [Function.comp, prod_range_succ', pow_zero, one_mul, pow_succ, mul_assoc]
  ring

lemma E_split {q : ℂ} (hq : ‖q‖ < 1) {m : ℕ} (hm : 0 < m) (u : ℂ) :
    ∏ j ∈ range m, E (q ^ m) (q ^ j * u) = E q u := by
  have hqm : ‖q ^ m‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq hm.ne'
  have h1 := (E_tend hq u).comp (tendsto_id.const_mul_atTop' hm)
  have h2 := tendsto_finset_prod (range m) fun j _ => E_tend hqm (q ^ j * u)
  refine tendsto_nhds_unique (h2.congr fun N => ?_) h1
  simp only [Function.comp, id]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, prod_range_add, ← ih, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [prod_range_succ, ← pow_mul, pow_add, mul_assoc]

lemma T_step {q : ℂ} (hq : ‖q‖ < 1) (h0 : q ≠ 0) {u : ℂ} (hu : u ≠ 0) :
    T q u = (-u) * T q (q * u) := by
  unfold T
  have : q * (q * u)⁻¹ = u⁻¹ := by field_simp
  rw [this, E_step hq u, E_step hq u⁻¹]
  field_simp
  ring

lemma T_steps {q : ℂ} (hq : ‖q‖ < 1) (h0 : q ≠ 0) {u : ℂ} (hu : u ≠ 0) (k : ℕ) :
    T q u = (-u) ^ k * q ^ (k.choose 2) * T q (q ^ k * u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, T_step hq h0 (mul_ne_zero (pow_ne_zero k h0) hu), Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [← mul_assoc q, ← pow_succ']
    ring

lemma T_split {q : ℂ} (hq : ‖q‖ < 1) (h0 : q ≠ 0) {m : ℕ} (hm : 0 < m) {u : ℂ} (hu : u ≠ 0) :
    ∏ j ∈ range m, T (q ^ m) (q ^ j * u) = T q u := by
  unfold T
  rw [prod_mul_distrib, E_split hq hm, ← E_split hq hm (q * u⁻¹), ← prod_range_reflect _ m]
  congr 1
  refine prod_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  congr 1
  have : q ^ m = q ^ (m - 1 - j) * q ^ j * q := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  rw [this]
  field_simp

lemma cth_eq {q : ℂ} (hq : ‖q‖ < 1) (c : ℕ) {t : ℂ} (h : ∀ n : ℕ, q ^ n * t ^ c ≠ 1)
    (h' : ∀ n : ℕ, q ^ n * (q * (t ^ c)⁻¹) ≠ 1) :
    cth c q t = q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * T q t ^ (c ^ 2) / T q (t ^ c) := by
  have h1 : E q (q * t ^ c) ≠ 0 := E_ne hq fun n => by
    rw [← mul_assoc, ← pow_succ]; exact h _
  have h2 : E q (q * (t ^ c)⁻¹) ≠ 0 := E_ne hq h'
  have hp : HasProd (fun m : ℕ => cthFac c q t (m + 1))
      (E q (q * t) ^ (c ^ 2) * E q (q * t⁻¹) ^ (c ^ 2) / (E q (q * t ^ c) * E q (q * (t ^ c)⁻¹))) := by
    have a := (((mult hq (q * t)).hasProd.pow (c ^ 2)).mul ((mult hq (q * t⁻¹)).hasProd.pow (c ^ 2)))
    have b := ((mult hq (q * t ^ c)).hasProd.mul (mult hq (q * (t ^ c)⁻¹)).hasProd)
    have := Tendsto.div a b (mul_ne_zero h1 h2)
    unfold HasProd
    refine this.congr fun s => ?_
    simp only [Pi.div_apply, cthFac, prod_div_distrib, pow_succ, mul_assoc]
  unfold cth T
  rw [hp.tprod_eq, E_step hq t, E_step hq (t ^ c)]
  simp only [mul_pow, div_eq_mul_inv, mul_inv]
  ring

lemma image_mod {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) :
    (range m).image (fun j => c * j % m) = range m ∧ Set.InjOn (fun j => c * j % m) (range m : Set ℕ) := by
  have hi : Set.InjOn (fun j => c * j % m) (range m : Set ℕ) := by
    intro a ha b hb hab
    have h1 : a ≡ b [MOD m] := Nat.ModEq.cancel_left_of_coprime h.symm hab
    exact Nat.ModEq.eq_of_lt_of_lt h1 (by simpa using ha) (by simpa using hb)
  refine ⟨eq_of_subset_of_card_le (fun x hx => ?_) (by rw [card_image_of_injOn hi]), hi⟩
  obtain ⟨j, -, rfl⟩ := mem_image.mp hx
  exact mem_range.mpr (Nat.mod_lt _ hm)

lemma prod_mod {M : Type*} [CommMonoid M] {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) (f : ℕ → M) :
    ∏ j ∈ range m, f (c * j % m) = ∏ j ∈ range m, f j := by
  obtain ⟨h1, h2⟩ := image_mod hm h
  conv_rhs => rw [← h1, prod_image h2]

lemma sum_mod {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) (f : ℕ → ℤ) :
    ∑ j ∈ range m, f (c * j % m) = ∑ j ∈ range m, f j := by
  obtain ⟨h1, h2⟩ := image_mod hm h
  conv_rhs => rw [← h1, sum_image h2]

lemma two_choose (k : ℕ) : 2 * (k.choose 2 : ℤ) = k * (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    push_cast
    linear_combination ih

lemma sum_one (m : ℕ) : 2 * ∑ j ∈ range m, (j : ℤ) = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_range_succ]; push_cast; linear_combination ih

lemma sum_two (m : ℕ) : 6 * ∑ j ∈ range m, (j : ℤ) ^ 2 = m * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_range_succ]; push_cast; linear_combination ih

lemma divmod (c m j : ℕ) : (c : ℤ) * j = m * ((c * j / m : ℕ) : ℤ) + ((c * j % m : ℕ) : ℤ) := by
  exact_mod_cast (Nat.div_add_mod (c * j) m).symm

lemma smoothedTheta_distribution_t_exponent_eq {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) {b : ℤ} (hb : 2 * b = c - c ^ 2) :
    m * b + c * ((∑ j ∈ range m, c * j / m : ℕ) : ℤ) = b := by
  have h1 : m * ∑ j ∈ range m, ((c * j / m : ℕ) : ℤ) = (c - 1) * ∑ j ∈ range m, (j : ℤ) := by
    rw [sub_mul, one_mul, mul_sum, mul_sum]
    conv_rhs => rw [← sum_mod hm h (fun j => (j : ℤ)), ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by linear_combination -divmod c m j
  have hm' : (2 * m : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm'
  rw [Nat.cast_sum]
  linear_combination (2 * c) * h1 + (c * (c - 1)) * sum_one m + (m * (m - 1)) * hb

lemma expo_q {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) {a b : ℤ} (ha : 12 * a = c ^ 2 - 1) (hb : 2 * b = c - c ^ 2) :
    m * a * m + (∑ j ∈ range m, (j : ℤ)) * b +
      ((∑ j ∈ range m, ((c * j % m) * (c * j / m) + m * (c * j / m).choose 2) : ℕ) : ℤ) = a := by
  have h1 : 2 * m * ((∑ j ∈ range m, ((c * j % m) * (c * j / m) + m * (c * j / m).choose 2) : ℕ) : ℤ) =
      (c ^ 2 - 1) * ∑ j ∈ range m, (j : ℤ) ^ 2 - m * (c - 1) * ∑ j ∈ range m, (j : ℤ) := by
    have e : ∀ S₁ S₂ : ℤ, (c ^ 2 - 1) * S₂ - m * (c - 1) * S₁ = c ^ 2 * S₂ - m * c * S₁ - (S₂ - m * S₁) := by
      intros; ring
    rw [e, Nat.cast_sum, mul_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib,
      ← sum_mod hm h (fun j => (j : ℤ) ^ 2 - m * j), ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    have h2 := divmod c m j
    have h3 := two_choose (c * j / m)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul m]
    generalize ((c * j / m).choose 2 : ℤ) = C at *
    generalize ((c * j / m : ℕ) : ℤ) = k at *
    generalize ((c * j % m : ℕ) : ℤ) = r at *
    linear_combination m ^ 2 * h3 - (c * j + m * k + r - m) * h2
  have hm' : (12 * m : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm'
  linear_combination 6 * h1 + (c ^ 2 - 1) * sum_two m + (6 * m * b - 3 * m * (c - 1)) * sum_one m
    + (m ^ 3 - m) * ha + 3 * m ^ 2 * (m - 1) * hb

theorem _root_.GlobalTheory.Sieg.prod_cth_mul_pow : ∀ (c m : ℕ) (Q t : ℂ), 1 < c → Nat.Coprime c 6 → 0 < m → Nat.Coprime c m → ‖Q‖ < 1 → Q ≠ 0 → t ≠ 0 → (∀ n : ℤ, Q ^ n * t ^ c ≠ 1) → ∏ j ∈ Finset.range m, cth c (Q ^ m) (t * Q ^ j) = cth c Q t := by
  intro c m Q t hc h6 hm hcm hQ h0 ht hn
  have hqm : ‖Q ^ m‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hQ hm.ne'
  have hs : t ^ c ≠ 0 := pow_ne_zero _ ht
  have hodd : Odd c := (Nat.coprime_two_right).mp (h6.coprime_dvd_right (by norm_num))
  have hinv : ∀ n : ℤ, Q ^ n * (t ^ c)⁻¹ ≠ 1 := fun n hh => by
    apply hn (-n)
    rw [← inv_inj, mul_inv, ← zpow_neg, neg_neg, hh, inv_one]
  have h12 : 12 ∣ c ^ 2 - 1 := by
    have h2 : c % 2 = 1 := Nat.odd_iff.mp hodd
    have h3 : ¬ 3 ∣ c := fun hd => by
      have := Nat.dvd_gcd hd (show 3 ∣ 6 by norm_num)
      rw [h6] at this; omega
    have : c % 12 = 1 ∨ c % 12 = 5 ∨ c % 12 = 7 ∨ c % 12 = 11 := by omega
    have h4 : c ^ 2 % 12 = 1 := by
      rw [Nat.pow_mod]; rcases this with h | h | h | h <;> rw [h]
    omega
  obtain ⟨a, ha⟩ := h12
  have ha' : 12 * (a : ℤ) = c ^ 2 - 1 := by
    have : 1 ≤ c ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : c ^ 2 = 12 * a + 1 := by omega
    have h3 : (c : ℤ) ^ 2 = 12 * a + 1 := by exact_mod_cast h2
    linarith
  have haa : (c ^ 2 - 1) / 12 = a := by omega
  obtain ⟨b, hb⟩ : ∃ b : ℤ, 2 * b = c - c ^ 2 := by
    obtain ⟨d, hd⟩ := hodd
    exact ⟨-(c * d), by rw [hd]; push_cast; ring⟩
  have hbb : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = b := by omega
  have hL : ∀ j ∈ range m, cth c (Q ^ m) (t * Q ^ j) =
      (Q ^ m) ^ a * ((-t) ^ b * (Q ^ j) ^ b) * T (Q ^ m) (Q ^ j * t) ^ (c ^ 2) / T (Q ^ m) (Q ^ (c * j) * t ^ c) := by
    intro j _
    rw [cth_eq hqm c, haa, hbb, ← neg_mul, mul_zpow, mul_pow t, ← pow_mul Q j, mul_comm t, mul_comm (t ^ c),
      mul_comm j c]
    · intro n hh
      apply hn ((m * n + j * c : ℕ) : ℤ)
      rw [← hh, zpow_natCast]; ring
    · intro n hh
      apply hinv ((m * n + m : ℕ) - (j * c : ℕ) : ℤ)
      rw [← hh, zpow_sub₀ h0, zpow_natCast, zpow_natCast]; field_simp; ring
  have hD : T Q (t ^ c) = (-t) ^ (c * ∑ j ∈ range m, c * j / m) *
      Q ^ (∑ j ∈ range m, ((c * j % m) * (c * j / m) + m * (c * j / m).choose 2)) *
      ∏ j ∈ range m, T (Q ^ m) (Q ^ (c * j) * t ^ c) := by
    rw [← T_split hQ h0 hm hs, ← prod_mod hm hcm (fun j => T (Q ^ m) (Q ^ j * t ^ c)), mul_sum,
      ← prod_pow_eq_pow_sum, ← prod_pow_eq_pow_sum, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [T_steps hqm (pow_ne_zero _ h0) (mul_ne_zero (pow_ne_zero _ h0) hs) (c * j / m), ← mul_assoc, ← pow_mul,
      ← pow_mul, ← pow_add, Nat.div_add_mod, pow_mul (-t), hodd.neg_pow, ← mul_neg, mul_pow, ← pow_mul, pow_add]
    ring
  rw [prod_congr rfl hL, cth_eq hQ c (fun n => by simpa using hn n)
    (fun n => by rw [← mul_assoc, ← pow_succ, ← zpow_natCast]; exact hinv _), haa, hbb, hD, prod_div_distrib,
    prod_mul_distrib, prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, prod_pow, T_split hQ h0 hm ht, card_range,
    prod_zpow, prod_pow_eq_pow_sum]
  have e1 := congrArg (fun z : ℤ => (-t) ^ z) (smoothedTheta_distribution_t_exponent_eq hm hcm hb)
  have e2 := congrArg (fun z : ℤ => Q ^ z) (expo_q hm hcm ha' hb)
  have hnt : -t ≠ 0 := neg_ne_zero.mpr ht
  rw [mul_comm (m : ℤ) b, ← Nat.cast_mul c] at e1
  rw [← Nat.cast_sum] at e2
  simp only [zpow_add₀ hnt, zpow_add₀ h0, zpow_natCast, zpow_mul] at e1 e2
  conv_rhs => rw [← e1, ← e2]
  generalize (∏ j ∈ range m, T (Q ^ m) (Q ^ (c * j) * t ^ c)) = P
  by_cases hP : P = 0
  · simp [hP]
  field_simp

end GlobalTheory.Sieg.Distr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PsumGaloisUnitPiece
section
open GlobalTheory.KummerEisensteinGalois

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

lemma eisF_pow_subst {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (e : ℕ) (a₁ a₂ : ℤ) (n : ℕ) :
    eisF j M (ζ ^ e) a₁ a₂ n = eisF j M ζ a₁ ((e : ℤ) * a₂) n := by
  have h : ∀ x : ℤ, (ζ ^ e) ^ x = ζ ^ ((e : ℤ) * x) := by
    intro x; rw [← zpow_natCast, ← zpow_mul]
  simp only [eisF, const0, coefPos, h, mul_assoc, mul_neg]

lemma smF_pow_subst {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (e : ℕ) (a₁ a₂ : ℤ) (n : ℕ) :
    smF c j M (ζ ^ e) a₁ a₂ n = smF c j M ζ a₁ ((e : ℤ) * a₂) n := by
  simp only [smF, eisF_pow_subst]
  rw [mul_left_comm]

lemma eisF_congr {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M)
    (a₁ a₂ a₂' : ℤ) (h : a₂ ≡ a₂' [ZMOD M]) (n : ℕ) :
    eisF j M ζ a₁ a₂ n = eisF j M ζ a₁ a₂' n := by
  have h1 : ζ ^ a₂ = ζ ^ a₂' := zpow_congr_of_modEq hζ hM h
  simp only [eisF, const0, coefPos, zpow_neg, zpow_mul, h1]

lemma smF_congr {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M)
    (a₁ a₂ a₂' : ℤ) (h : a₂ ≡ a₂' [ZMOD M]) (n : ℕ) :
    smF c j M ζ a₁ a₂ n = smF c j M ζ a₁ a₂' n := by
  simp only [smF, eisF_congr j M ζ hζ hM a₁ a₂ a₂' h, eisF_congr j M ζ hζ hM _ _ _ (h.mul_left c)]

def diagOneUnit {R : Type} [CommRing R] (b : Rˣ) : GL (Fin 2) R :=
  ⟨Matrix.diagonal ![1, (b : R)], Matrix.diagonal ![1, ((b⁻¹ : Rˣ) : R)],
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp⟩

lemma diagOneUnit_mul {R : Type} [CommRing R] (a b : Rˣ) : diagOneUnit a * diagOneUnit b = diagOneUnit (a * b) := by
  ext i j
  simp only [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Units.val_mk, Matrix.diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp

lemma diagOneUnit_one {R : Type} [CommRing R] : diagOneUnit (1 : Rˣ) = 1 := by
  ext i j
  simp only [diagOneUnit, Units.val_mk, Matrix.GeneralLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

lemma coe_mul_diagOneUnit {R : Type} [CommRing R] (γ : GL (Fin 2) R) (b : Rˣ) (i : Fin 2) :
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 0 = (γ : Matrix (Fin 2) (Fin 2) R) i 0 ∧
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 1 = (γ : Matrix (Fin 2) (Fin 2) R) i 1 * b := by
  simp [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_diagonal]

lemma det_mul_diagOneUnit {R : Type} [CommRing R] (γ : GL (Fin 2) R) (b : Rˣ) :
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = (γ : Matrix (Fin 2) (Fin 2) R).det * b := by
  simp [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two]

lemma smF_rowT_subst {K : Type} [Field K] [CharZero K] (N p m : ℕ) [NeZero p] (c : ℤ) (j : ℕ) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (hN : 0 < N) (γ : GL (Fin 2) (ZMod (p ^ m))) (b : (ZMod (p ^ m))ˣ) (e : ℕ)
    (he : ((e : ℕ) : ZMod (p ^ m)) = b ∧ ((e : ℕ) : ZMod N) = 1) (i : Fin 2) (w : ℤ × ℤ) :
    smF c j (N * p ^ m) (ζ ^ e) (rowT N p m γ i w).1 (rowT N p m γ i w).2 =
      smF c j (N * p ^ m) ζ (rowT N p m (γ * diagOneUnit b) i w).1 (rowT N p m (γ * diagOneUnit b) i w).2 := by
  funext n
  rw [smF_pow_subst]
  have h1 : (rowT N p m (γ * diagOneUnit b) i w).1 = (rowT N p m γ i w).1 := by
    simp [rowT, (coe_mul_diagOneUnit γ b i).1]
  rw [h1]
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  apply smF_congr c j _ ζ hζ (by positivity)
  simp only [rowT, (coe_mul_diagOneUnit γ b i).2]
  rw [Int.modEq_iff_dvd]
  have h2 : ((p ^ m : ℕ) : ℤ) ∣ (e : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) i 1).val : ℤ) -
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) i 1 * b).val : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [he.1, mul_comm]
  have h3 : (N : ℤ) ∣ (e : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [he.2, sub_self]
  obtain ⟨u, hu⟩ := h2
  obtain ⟨v, hv⟩ := h3
  refine ⟨-(u + w.2 * v), ?_⟩
  push_cast at hu ⊢
  linear_combination (-(N : ℤ)) * hu - ((p : ℤ) ^ m * w.2) * hv

theorem psum_galois_unitPiece : ∀ (N p m k : ℕ) [NeZero p] (K : Type) [Field K] [CharZero K]
    (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ)
    (ζ : K) (β : (ZMod (p ^ m))ˣ → ℕ), p.Prime → 0 < N → Nat.Coprime p N → 1 ≤ m → IsPrimitiveRoot ζ (N * p ^ m) →
    (∀ b, ((β b : ℕ) : ZMod (p ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1) →
    ∀ r : ℕ, ∑ b : (ZMod (p ^ m))ˣ, ψ b * pieceT N p m m k (1 : DirichletCharacter K (p ^ m)) c d w w' (ζ ^ β b)
        ((unitSet p m).filter (fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))).det = 1)) r =
      pieceT N p m m k ψ c d w w' ζ (unitSet p m) r := by
  intro N p m k _ K _ _ ψ c d w w' ζ β _ hN _ _ hζ hβ r
  unfold pieceT
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun x => x.2 * diagOneUnit x.1)
    (fun γ => (Matrix.GeneralLinearGroup.det γ, γ * diagOneUnit (Matrix.GeneralLinearGroup.det γ)⁻¹))
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, unitSet, Finset.mem_univ, true_and] at h ⊢
    simp only [(coe_mul_diagOneUnit γ b 0).1, (coe_mul_diagOneUnit γ b 1).1]
    exact h.1
  · intro γ h
    simp only [Finset.mem_product, Finset.mem_filter, unitSet, Finset.mem_univ, true_and] at h ⊢
    simp only [(coe_mul_diagOneUnit γ _ 0).1, (coe_mul_diagOneUnit γ _ 1).1]
    refine ⟨h, ?_⟩
    rw [det_mul_diagOneUnit, ← Matrix.GeneralLinearGroup.val_det_apply, Units.mul_inv]
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have hd : Matrix.GeneralLinearGroup.det (γ * diagOneUnit b) = b := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, det_mul_diagOneUnit, h.2, one_mul]
    simp only [hd, mul_assoc, diagOneUnit_mul, mul_inv_cancel, diagOneUnit_one, mul_one]
  · intro γ _
    simp only [mul_assoc, diagOneUnit_mul, inv_mul_cancel, diagOneUnit_one, mul_one]
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
    dsimp only
    rw [smF_rowT_subst N p m c (k - 1) ζ hζ hN γ b (β b) (hβ b) 0 w,
      smF_rowT_subst N p m d 1 ζ hζ hN γ b (β b) (hβ b) 1 w', det_mul_diagOneUnit, h.2, one_mul,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, map_one, one_mul]
    ring

end GlobalTheory.KummerEisensteinGalois
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeparatingFamilySumClosedUnderProdStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separating_family_sum_closed_under_prod : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (F : Subfield L) (ι : Type) (s : Finset ι) (x y : ι → L), (∀ j ∈ s, x j ∈ F ∧ y j ∈ F ∧ v (x j) ≤ 1 ∧ v (y j) ≤ 1) → ∃ (n : ℕ) (a b : Fin n → L), (∀ i, a i ∈ F ∧ b i ∈ F ∧ v (a i) ≤ 1 ∧ v (b i) ≤ 1) ∧ ∀ σ : G, ∑ i, a i * σ • b i = ∏ j ∈ s, (x j - σ • y j) := by
  first | exact @GlobalTheory.sepFamily_prod | exact GlobalTheory.sepFamily_prod | (intros; apply GlobalTheory.sepFamily_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionNeZero
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_ne_zero : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → sg c x τ ≠ 0 :=
  fun _ _ τ h => (GlobalTheory.Sieg.Model.multipliable_and_sg_ne_zero h τ).2.2

end GlobalTheory.Sieg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashQExpansionCoeffWidthTransformStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slashQExpansionCoeffWidth_transform : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → (∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (x * ModularGroup.T) n = Complex.exp (2 * Real.pi * Complex.I / M) ^ n * co M k f x n) ∧ (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (γ * x) n = co M k f x n) ∧ (Odd k → ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (-x) n = -co M k f x n) := by
  first | exact @GlobalTheory.OddFrame.co_transform | exact GlobalTheory.OddFrame.co_transform | (intros; apply GlobalTheory.OddFrame.co_transform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashRatIsBoundedAtGamma1InterGamma0LevelStatement
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level : ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l → 0 < (g.det : ℚ) → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ, IsCusp c (GlobalTheory.Hk.lev N l) → c.IsBoundedAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  first | exact @GlobalTheory.Hk.slash_rat_isBoundedAt | exact GlobalTheory.Hk.slash_rat_isBoundedAt | (intros; apply GlobalTheory.Hk.slash_rat_isBoundedAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashSubQExpansionPartialSumIsBigOStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slash_sub_qExpansion_partialSum_isBigO : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → ∀ x : SL(2, ℤ), (fun τ : ℍ => (f ∣[k] x) τ - ∑ n ∈ Finset.range M, co M k f x n * Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ n) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  first | exact @GlobalTheory.OddFrame.slash_sub_partialSum_isBigO | exact GlobalTheory.OddFrame.slash_sub_partialSum_isBigO | (intros; apply GlobalTheory.OddFrame.slash_sub_partialSum_isBigO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxCoefficientSeqOneMemSubringStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedEisensteinFxCoefficientSeq_one_mem_subring : ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (c M : ℕ) (ζ : K) (a b : ℤ), 0 < M → Nat.Coprime c M → ¬ (M : ℤ) ∣ a → ζ ^ b ∈ R → ζ ^ (-b) ∈ R → ∀ n : ℕ, GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M ζ a b n ∈ R := by
  first | exact @GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring | exact GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring | (intros; apply GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularGroupTSmul
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem coe_T_smul (τ : ℍ) : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
  push_cast; ring

theorem ee_add_one (z : ℂ) : ee (z + 1) = ee z := by
  unfold ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (z + 1) = 2 * Real.pi * Complex.I * z + 2 * Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem rowVectorMulIntMatrixSL2_modularGroupT_apply (x : Fin 2 → ℚ) : act x ModularGroup.T 0 = x 0 ∧ act x ModularGroup.T 1 = x 0 + x 1 := by
  simp [act, ModularGroup.T, Fin.sum_univ_two]

theorem pt_T_smul (x : Fin 2 → ℚ) (τ : ℍ) : pt x (ModularGroup.T • τ) = pt (act x ModularGroup.T) τ := by
  obtain ⟨h0, h1⟩ := rowVectorMulIntMatrixSL2_modularGroupT_apply x
  simp only [pt, coe_T_smul, h0, h1]
  push_cast; ring

theorem sg_T_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), sg c x (ModularGroup.T • τ) = sg c (act x ModularGroup.T) τ := by
  intro c x τ
  simp only [sg]
  rw [pt_T_smul, coe_T_smul, ee_add_one]

end GlobalTheory.Sieg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripEvalPolynomialDecayMulImRpowStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strip_eval_polynomial_decay_mul_im_rpow : ∀ (w n : ℕ) (a : ℂ) (V : ℍ → ℂ[X]) (C' c : ℝ), 1 ≤ w → 0 < c → (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) → ∀ ε > 0, ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → 0 ≤ τ.re → τ.re ≤ n → ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) < ε := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.strip_eval_decay | exact GlobalTheory.HeckeFamilyMatrices.strip_eval_decay | (intros; apply GlobalTheory.HeckeFamilyMatrices.strip_eval_decay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankCuspFormOfFrameStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_finrank_levelOne_le_finrank_cuspForm_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (CuspForm Γ k) → (∀ j, IsCF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (CuspForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm | exact GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm | (intros; apply GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankOfFrameStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_finrank_levelOne_le_finrank_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (ModularForm Γ k) → (∀ j, IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (ModularForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.finrank_sum_le_of_frame | exact GlobalTheory.OddFrame.finrank_sum_le_of_frame | (intros; apply GlobalTheory.OddFrame.finrank_sum_le_of_frame <;> assumption)
end

