import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeMulBernoulliMem
import GroundTheory.PAdicHodge.AxLemma
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowerSeriesCompletionEmbedding

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsGluedTowerLevels
section
noncomputable section

namespace GlobalTheory.LevGlue

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem der_pow_val {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (hD : IsDer S D)
    (hS : ∀ x ∈ S, IsInt p x) (hp : (p : Ω) ≠ 0) {x c : Ω} {m j : ℕ} (hx : x ∈ S)
    (h : IsInt p (D x - c * x / (p : Ω) ^ (m + j))) :
    IsInt p (D (x ^ (p ^ j)) - c * x ^ (p ^ j) / (p : Ω) ^ m) := by
  obtain ⟨k, hk⟩ : ∃ k, p ^ j = k + 1 := ⟨p ^ j - 1, (Nat.succ_pred_eq_of_pos (ppow_pos j)).symm⟩
  have h1 := hD.pow hS hx k
  rw [← hk] at h1
  have e : c * x ^ (p ^ j) / (p : Ω) ^ m =
      ((p ^ j : ℕ) : Ω) * x ^ k * (c * x / (p : Ω) ^ (m + j)) := by
    have e1 : x ^ (p ^ j) = x ^ k * x := by rw [hk, pow_succ]
    have e2 : ((p ^ j : ℕ) : Ω) = (p : Ω) ^ j := by push_cast; ring
    rw [e1, e2, pow_add]
    field_simp
  refine int_congr (int_add h1 (int_mul (int_mul (int_nat (p ^ j)) (int_pow (hS x hx) k)) h)) ?_
  linear_combination (-1 : Ω) * e

theorem compat_gen (T : Tower p Ω) {m n : ℕ} (hmn : m ≤ n) {D D' : Ω → Ω}
    (hD : IsDer (Lev T n) D) (hD' : IsDer (Lev T m) D')
    (hz : IsInt p (D (T.ζ m) - D' (T.ζ m))) (hq : IsInt p (D (T.qq m) - D' (T.qq m))) :
    ∀ x ∈ Lev T m, IsInt p (D x - D' x) :=
  IsDer.adjoin (t := {T.ζ m, T.qq m}) (IsDer.sub (hD.mono (Lev_mono T hmn)) hD') (Lev_int T m)
    (by rintro x (rfl | rfl); exacts [zeta_mem_Lev T m, qq_mem_Lev T m])
    (by rintro x (rfl | rfl); exacts [hz, hq])

theorem vals_down (T : Tower p Ω) (hp : (p : Ω) ≠ 0) {m n : ℕ} (hmn : m ≤ n) {dz dq : Ω → Ω}
    (hz : IsDer (Lev T n) dz) (hq : IsDer (Lev T n) dq) (hv : Vals T n dz dq) : Vals T m dz dq := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hS := Lev_int T (m + j)
  have zm := zeta_mem_Lev T (m + j)
  have qm := qq_mem_Lev T (m + j)
  have z0 : ∀ {D : Ω → Ω} {x : Ω}, IsInt p (D x) → IsInt p (D x - 0 * x / (p : Ω) ^ (m + j)) :=
    fun h => int_congr h (by ring)
  have z1 : ∀ {D : Ω → Ω} {y : Ω}, IsInt p (D y - 0 * y / (p : Ω) ^ m) → IsInt p (D y) :=
    fun h => int_congr h (by ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := der_pow_val hz hS hp zm hv.1
    rwa [zeta_pow] at this
  · have := z1 (der_pow_val hz hS hp qm (z0 hv.2.1))
    rwa [qq_pow] at this
  · have := z1 (der_pow_val hq hS hp zm (z0 hv.2.2.1))
    rwa [zeta_pow] at this
  · have := der_pow_val hq hS hp qm hv.2.2.2
    rwa [qq_pow] at this

theorem glue_fam (T : Tower p Ω) (F : ℕ → Ω → Ω) (hF : ∀ m, IsDer (Lev T (m + 1)) (F m))
    (hc : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt p (F n x - F m x)) :
    ∃ G : Ω → Ω, (∀ m, ∀ x ∈ Lev T (m + 1), IsInt p (G x - F m x)) ∧
      ∀ S : Subalgebra (O0 p) Ω, (∀ x ∈ S, ∃ m, x ∈ Lev T m) → IsDer S G := by
  classical
  let M : Ω → ℕ := fun x => if h : ∃ m, x ∈ Lev T (m + 1) then Classical.choose h else 0
  have hG : ∀ m, ∀ x ∈ Lev T (m + 1), IsInt p (F (M x) x - F m x) := by
    intro m x hx
    have h : ∃ m, x ∈ Lev T (m + 1) := ⟨m, hx⟩
    have hM : M x = Classical.choose h := dif_pos h
    have ha := Classical.choose_spec h
    rw [hM]
    have h1 := hc _ (max m (Classical.choose h)) (le_max_right _ _) x ha
    have h2 := hc _ (max m (Classical.choose h)) (le_max_left _ _) x hx
    exact int_congr (int_sub h2 h1) (by ring)
  refine ⟨fun x => F (M x) x, hG, fun S hS => ?_⟩
  have two : ∀ x ∈ S, ∀ y ∈ S, ∃ n, x ∈ Lev T (n + 1) ∧ y ∈ Lev T (n + 1) := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hS x hx
    obtain ⟨b, hb⟩ := hS y hy
    exact ⟨a + b, Lev_mono T (by omega) ha, Lev_mono T (by omega) hb⟩
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    refine int_congr (int_add (int_add (int_sub (int_sub ((hF n).1 x hxn y hyn)
      (hG n x hxn)) (hG n y hyn)) (hG n _ (add_mem hxn hyn))) int_zero) ?_
    ring
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    have ix := Lev_int T _ x hxn
    have iy := Lev_int T _ y hyn
    refine int_congr (int_sub (int_sub (int_add ((hF n).2.1 x hxn y hyn)
      (hG n _ (mul_mem hxn hyn))) (int_mul ix (hG n y hyn))) (int_mul iy (hG n x hxn))) ?_
    ring
  · have hm := (Lev T (0 + 1)).algebraMap_mem c
    exact int_congr (int_add (hG 0 _ hm) ((hF 0).2.2 c)) (by ring)

theorem glue : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (B : Subalgebra (O0 p) Ω), (∀ x ∈ B, ∃ m : ℕ, x ∈ Lev T m) →
    (∀ m : ℕ, 1 ≤ m → ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq) →
    ∃ dz dq : Ω → Ω, IsDer B dz ∧ IsDer B dq ∧ ∀ m : ℕ, 1 ≤ m → Vals T m dz dq := by
  intro p _ Ω _ _ hclo T B hB hlev
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hclo
  have hp : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h' : ∀ m : ℕ, ∃ dz dq : Ω → Ω, IsDer (Lev T (m + 1)) dz ∧ IsDer (Lev T (m + 1)) dq ∧
      Vals T (m + 1) dz dq := fun m => hlev (m + 1) (by omega)
  choose Z Q hZ hQ hV using h'
  have cZ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt p (Z n x - Z m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hZ n) (hZ m)
      (int_congr (int_sub v.1 (hV m).1) (by ring)) (int_congr (int_sub v.2.1 (hV m).2.1) (by ring))
  have cQ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt p (Q n x - Q m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hQ n) (hQ m)
      (int_congr (int_sub v.2.2.1 (hV m).2.2.1) (by ring))
      (int_congr (int_sub v.2.2.2 (hV m).2.2.2) (by ring))
  obtain ⟨dz, hdz, hdzB⟩ := glue_fam T Z hZ cZ
  obtain ⟨dq, hdq, hdqB⟩ := glue_fam T Q hQ cQ
  refine ⟨dz, dq, hdzB B hB, hdqB B hB, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have v := hV k
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact int_congr (int_add (hdz k _ (zeta_mem_Lev T _)) v.1) (by ring)
  · exact int_congr (int_add (hdz k _ (qq_mem_Lev T _)) v.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (zeta_mem_Lev T _)) v.2.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (qq_mem_Lev T _)) v.2.2.2) (by ring)

end GlobalTheory.LevGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntModLevelPrimePowEqAddMul
section
open Finset GlobalTheory.KummerEisensteinGalois GlobalTheory.EisCong

namespace GlobalTheory.EisCongGen

variable {K : Type} [Field K] [CharZero K]
variable {p : ℕ} [Fact p.Prime]

lemma bernoulli_expansion_lvl (hp2 : p ≠ 2) (n m N : ℕ) (hN : 0 < N) (b : ℤ) :
    ∃ y ∈ pInt p K, ((N : K) * (p : K) ^ (n + 1)) ^ (m + 1) *
        (((Polynomial.bernoulli (m + 2)).eval ((b : ℚ) / ((N : ℚ) * (p : ℚ) ^ (n + 1))) / ((m + 2 : ℕ) : ℚ) : ℚ) : K) =
      (b : K) ^ (m + 2) / (((m : K) + 2) * ((N : K) * (p : K) ^ (n + 1))) - (b : K) ^ (m + 1) / 2 + (p : K) ^ n * y := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hN0 : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (m : K) + 2 ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
  refine ⟨∑ i ∈ range (m + 1), ((p : K) * ((bernoulli (i + 2) : ℚ) : K)) * (b : K) ^ (m - i) *
    ((m + 1).choose (i + 1) : ℕ) * (((p : K) ^ (n + 1)) ^ i / ((i : K) + 2)) * (N : K) ^ (i + 1),
    sum_mem fun i _ => mul_mem (mul_mem (mul_mem (mul_mem (prime_mul_bernoulli_mem i)
      (pow_mem (intCast_mem _ _) _)) (natCast_mem _ _)) (pow_div_add_two_mem hp2 n i))
      (pow_mem (natCast_mem _ _) _), ?_⟩
  rw [Polynomial.bernoulli, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  push_cast
  rw [sum_div, mul_sum, sum_range_succ', sum_range_succ', mul_sum]
  have : ∀ i ∈ range (m + 1), ((N : K) * (p : K) ^ (n + 1)) ^ (m + 1) *
      (((bernoulli (i + 1 + 1) : ℚ) : K) * ((m + 2).choose (i + 1 + 1) : ℕ) *
        ((b : K) / ((N : K) * (p : K) ^ (n + 1))) ^ (m + 2 - (i + 1 + 1)) / ((m : K) + 2)) =
      (p : K) ^ n * (((p : K) * ((bernoulli (i + 2) : ℚ) : K)) * (b : K) ^ (m - i) *
        ((m + 1).choose (i + 1) : ℕ) * (((p : K) ^ (n + 1)) ^ i / ((i : K) + 2)) * (N : K) ^ (i + 1)) := by
    intro i hi
    obtain ⟨l, rfl⟩ : ∃ l, m = i + l := ⟨m - i, by have := mem_range.1 hi; omega⟩
    have hi2 : (i : K) + 2 ≠ 0 := by exact_mod_cast (show i + 2 ≠ 0 by omega)
    rw [show i + l + 2 - (i + 1 + 1) = l by omega, show i + l - i = l by omega,
      show i + 1 + 1 = i + 2 by omega, choose_cast, div_pow]
    field_simp
    ring
  rw [sum_congr rfl this]
  generalize (∑ i ∈ range (m + 1), _ : K) = S
  simp [div_pow]
  field_simp
  ring

lemma inv_pow_nat_mem {N : ℕ} (hpN : ¬ p ∣ N) (k : ℕ) : ((N : K)⁻¹) ^ k ∈ pInt p K :=
  pow_mem (inv_nat_mem hpN) k

lemma const_j (hp2 : p ≠ 2) {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (n m : ℕ) (ζ : K) (a a₂ x s : ℤ)
    (hb : a % ((N * p ^ (n + 1) : ℕ) : ℤ) = N * x + s * (p : ℤ) ^ (n + 1)) :
    ∃ y ∈ pInt p K, (p : K) ^ ((n + 1) * (m + 1)) * const0 (m + 2) (N * p ^ (n + 1)) ζ a a₂ =
      -((x : K) ^ (m + 2) / (((m : K) + 2) * (p : K) ^ (n + 1)) + s * (x : K) ^ (m + 1) / N
        - (x : K) ^ (m + 1) / 2) + (p : K) ^ n * y := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hN0 : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (m : K) + 2 ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
  set b : ℤ := a % ((N * p ^ (n + 1) : ℕ) : ℤ) with hbdef
  have hbK : (b : K) = (N : K) * x + s * (p : K) ^ (n + 1) := by rw [hb]; push_cast; ring
  have f : frc (N * p ^ (n + 1)) a = (b : ℚ) / ((N : ℚ) * (p : ℚ) ^ (n + 1)) := by
    unfold frc; rw [← hbdef]; push_cast; ring
  obtain ⟨y1, hy1, E1⟩ := bernoulli_expansion_lvl (K := K) hp2 n m N hN b
  obtain ⟨y3, hy3, E3⟩ := binom_second (K := K) hp2 n m (N * x) s
  obtain ⟨y4, E4⟩ := binom_first (K := K) ((p : ℤ) ^ (n + 1)) (m + 1) (N * x) s
  push_cast at E3 E4
  rw [← hbK] at E3 E4
  have h2 : (2 : K)⁻¹ ∈ pInt p K := by
    simpa using inv_nat_mem (K := K) (p := p) (m := 2)
      fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  refine ⟨-(((N : K)⁻¹) ^ (m + 1) * (p * y3 * (N : K)⁻¹ - p * y4 * 2⁻¹ + y1)),
    neg_mem (mul_mem (inv_pow_nat_mem hpN _) (add_mem (sub_mem (mul_mem (mul_mem (natCast_mem _ _) hy3)
      (inv_nat_mem hpN)) (mul_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) h2)) hy1)), ?_⟩
  simp only [const0, if_neg (show m + 2 ≠ 1 by omega), f]
  have hZ := (eq_div_iff (pow_ne_zero (m + 1) (mul_ne_zero hN0 (pow_ne_zero (n + 1) hp0)))).2 ((mul_comm _ _).trans E1)
  rw [hZ, E3, E4]
  rw [pow_mul]
  have hQ : (p : K) ^ n ≠ 0 := pow_ne_zero _ hp0
  simp only [pow_succ (p : K) n]
  generalize (p : K) ^ n = Q at hQ ⊢
  rw [inv_pow]
  field_simp
  ring

omit [Fact p.Prime] in
lemma exists_intMod_levelPrimePow_eq_add_mul {N : ℕ} (n : ℕ) (a x : ℤ) (h : a ≡ N * x [ZMOD (p : ℤ) ^ (n + 1)]) :
    ∃ s : ℤ, a % ((N * p ^ (n + 1) : ℕ) : ℤ) = N * x + s * (p : ℤ) ^ (n + 1) := by
  have h1 : a % ((N * p ^ (n + 1) : ℕ) : ℤ) ≡ a [ZMOD (N : ℤ) * (p : ℤ) ^ (n + 1)] := by
    have := Int.mod_modEq a ((N * p ^ (n + 1) : ℕ) : ℤ)
    push_cast at this ⊢
    exact this
  have h2 := (h1.of_mul_left _).trans h
  obtain ⟨s, hs⟩ := h2.symm.dvd
  exact ⟨s, by linear_combination hs⟩

lemma not_dvd_of_congr {N : ℕ} (hpN : ¬ p ∣ N) (n : ℕ) {a α : ℤ} (h0 : 0 < α) (h1 : α < (p : ℤ) ^ (n + 1))
    (ha : a ≡ N * α [ZMOD (p : ℤ) ^ (n + 1)]) : ¬ ((p : ℤ) ^ (n + 1) ∣ a) := by
  have hp : p.Prime := Fact.out
  intro hd1
  have hd2 : (p : ℤ) ^ (n + 1) ∣ N * α := (Int.ModEq.dvd ha).elim fun t ht => by
    refine ⟨t + a / (p : ℤ) ^ (n + 1), ?_⟩
    have := Int.ediv_mul_cancel hd1
    linear_combination ht - this
  have hcop : IsCoprime ((p : ℤ) ^ (n + 1)) (N : ℤ) :=
    IsCoprime.pow_left ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2
      (fun h => hpN (Int.natCast_dvd_natCast.1 h)))
  have := hcop.dvd_of_dvd_mul_left hd2
  exact absurd (Int.le_of_dvd h0 this) (not_le.2 h1)

lemma not_dvd_lvl {N : ℕ} (n : ℕ) {a : ℤ} (h : ¬ ((p : ℤ) ^ (n + 1) ∣ a)) :
    ¬ (((N * p ^ (n + 1) : ℕ) : ℤ) ∣ a) := fun hd => h (dvd_trans (by push_cast; exact dvd_mul_left _ _) hd)

lemma not_dvd_mul {n : ℕ} {c a : ℤ} (hc : ¬ (p : ℤ) ∣ c) (h : ¬ ((p : ℤ) ^ (n + 1) ∣ a)) :
    ¬ ((p : ℤ) ^ (n + 1) ∣ c * a) := fun hd => h <|
  IsCoprime.dvd_of_dvd_mul_left (IsCoprime.pow_left
    ((Nat.prime_iff_prime_int.1 (Fact.out : p.Prime)).irreducible.coprime_iff_not_dvd.2 hc)) hd

lemma const_congr_gen (hp2 : p ≠ 2) {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (n m : ℕ) (ζ : K) {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) {α a₁ : ℤ} (a₂ : ℤ) (h0 : 0 ≤ α) (h1 : α < (p : ℤ) ^ (n + 1))
    (ha : a₁ ≡ N * α [ZMOD (p : ℤ) ^ (n + 1)]) :
    ∃ y ∈ pInt p K, (α : K) ^ (m + 1) * smF c 1 (N * p ^ (n + 1)) ζ a₁ a₂ 0 -
      (p : K) ^ ((n + 1) * (m + 1)) * smF c (m + 2) (N * p ^ (n + 1)) ζ a₁ a₂ 0 = (p : K) ^ n * y := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hN0 : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (m : K) + 2 ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
  have hc0 : (c : K) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
    exact_mod_cast this
  have hca : c * a₁ ≡ N * (c * α) [ZMOD (p : ℤ) ^ (n + 1)] := by
    have := ha.mul_left c; rwa [mul_left_comm] at this
  obtain ⟨s₁, hs₁⟩ := exists_intMod_levelPrimePow_eq_add_mul n a₁ α ha
  obtain ⟨s₂, hs₂⟩ := exists_intMod_levelPrimePow_eq_add_mul n (c * a₁) (c * α) hca
  obtain ⟨y1, hy1, E1⟩ := const_j (K := K) hp2 hN hpN n m ζ a₁ a₂ α s₁ hs₁
  obtain ⟨y2, hy2, E2⟩ := const_j (K := K) hp2 hN hpN n m ζ (c * a₁) (c * a₂) (c * α) s₂ hs₂
  have hz : (c : K) ^ ((2 : ℤ) - ((m + 2 : ℕ) : ℤ)) = ((c : K) ^ m)⁻¹ := by
    rw [show (2 : ℤ) - ((m + 2 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have hS : (p : K) ^ ((n + 1) * (m + 1)) * smF c (m + 2) (N * p ^ (n + 1)) ζ a₁ a₂ 0 =
      (c : K) ^ 2 * ((p : K) ^ ((n + 1) * (m + 1)) * const0 (m + 2) (N * p ^ (n + 1)) ζ a₁ a₂) -
      ((c : K) ^ m)⁻¹ * ((p : K) ^ ((n + 1) * (m + 1)) * const0 (m + 2) (N * p ^ (n + 1)) ζ (c * a₁) (c * a₂)) := by
    simp only [smF, eisF, ↓reduceIte, hz]; ring
  have hci : ((c : K) ^ m)⁻¹ ∈ pInt p K := by rw [← inv_pow]; exact pow_mem (inv_int_mem hc) m
  refine ⟨-((c : K) ^ 2 * y1 - ((c : K) ^ m)⁻¹ * y2),
    neg_mem (sub_mem (mul_mem (pow_mem (intCast_mem _ _) _) hy1) (mul_mem hci hy2)), ?_⟩
  rw [hS, E1, E2]
  rcases h0.eq_or_lt with h | h
  · rw [← h]; simp; ring
  have d0 := not_dvd_of_congr hpN n h h1 ha
  have d1 := not_dvd_lvl (N := N) n d0
  have d2 := not_dvd_lvl (N := N) n (not_dvd_mul hc d0)
  have f1 : frc (N * p ^ (n + 1)) a₁ = ((N * α + s₁ * (p : ℤ) ^ (n + 1) : ℤ) : ℚ) / ((N : ℚ) * (p : ℚ) ^ (n + 1)) := by
    unfold frc; rw [hs₁]; push_cast; ring
  have f2 : frc (N * p ^ (n + 1)) (c * a₁) = ((N * (c * α) + s₂ * (p : ℤ) ^ (n + 1) : ℤ) : ℚ) /
      ((N : ℚ) * (p : ℚ) ^ (n + 1)) := by
    unfold frc; rw [hs₂]; push_cast; ring
  simp only [smF, eisF, ↓reduceIte, const0, if_neg d1, if_neg d2, f1, f2]
  push_cast
  have hQ : (p : K) ^ n ≠ 0 := pow_ne_zero _ hp0
  simp only [pow_succ (p : K) n]
  generalize (p : K) ^ n = Q at hQ ⊢
  field_simp
  ring

lemma term_congr_gen (hp0 : (p : K) ≠ 0) {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (n k : ℕ) {A a₁ a : ℤ}
    (h : A ≡ a₁ [ZMOD ((N * p ^ n : ℕ) : ℤ)]) (ha : a₁ ≡ N * a [ZMOD (p : ℤ) ^ n]) :
    ∃ y ∈ pInt p K, (p : K) ^ (n * k) * ((A : K) / ((N * p ^ n : ℕ) : K)) ^ k = (a : K) ^ k + (p : K) ^ n * y := by
  have h' : A ≡ N * a [ZMOD (p : ℤ) ^ n] := by
    have : A ≡ a₁ [ZMOD (N : ℤ) * (p : ℤ) ^ n] := by push_cast at h; exact h
    exact (this.of_mul_left _).trans ha
  obtain ⟨t, ht⟩ := h'.symm.dvd
  obtain ⟨y, hy⟩ := binom_first (K := K) ((p : ℤ) ^ n) k (N * a) t
  have hN' : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨(y : K) * ((N : K) ^ k)⁻¹, mul_mem (intCast_mem _ _) (by rw [← inv_pow]; exact pow_mem (inv_nat_mem hpN) k), ?_⟩
  have hA : (A : K) = N * a + t * (p : K) ^ n := by
    have := congrArg (Int.cast : ℤ → K) ht
    push_cast at this
    linear_combination this
  push_cast at hy ⊢
  rw [hA, div_pow, hy, pow_mul]
  have hQ : (p : K) ^ n ≠ 0 := pow_ne_zero _ hp0
  generalize (p : K) ^ n = Q at hQ ⊢
  field_simp
  ring

lemma coefPos_congr_gen {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (n k : ℕ) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (N * p ^ n)) (a a₁ a₂ : ℤ) (ha : a₁ ≡ N * a [ZMOD (p : ℤ) ^ n]) (r : ℕ) :
    ∃ y ∈ pInt p K, (a : K) ^ k * coefPos 1 (N * p ^ n) ζ a₁ a₂ r -
      (p : K) ^ (n * k) * coefPos (k + 1) (N * p ^ n) ζ a₁ a₂ r = (p : K) ^ n * y := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hM : 0 < N * p ^ n := Nat.mul_pos hN (pow_pos hp.pos n)
  have key : ∀ (A e : ℤ), ∃ y ∈ pInt p K,
      (a : K) ^ k * (if A ≡ a₁ [ZMOD ((N * p ^ n : ℕ) : ℤ)] then ζ ^ e else 0) -
        (p : K) ^ (n * k) * (if A ≡ a₁ [ZMOD ((N * p ^ n : ℕ) : ℤ)] then
          ((A : K) / ((N * p ^ n : ℕ) : K)) ^ k * ζ ^ e else 0) = (p : K) ^ n * y := by
    intro A e
    split_ifs with h
    · obtain ⟨y, hy, hE⟩ := term_congr_gen hp0 hN hpN n k h ha
      refine ⟨-(y * ζ ^ e), neg_mem (mul_mem hy (root_zpow_mem hM hζ e)), ?_⟩
      rw [← mul_assoc, hE]; ring
    · exact ⟨0, zero_mem _, by simp⟩
  choose y hy hE using key
  refine ⟨∑ d ∈ r.divisors, (y ((r / d : ℕ) : ℤ) (a₂ * d) - y (-((r / d : ℕ) : ℤ)) (-(a₂ * d))),
    sum_mem fun d _ => sub_mem (hy _ _) (hy _ _), ?_⟩
  unfold coefPos
  rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_sub ((p : K) ^ n), ← hE, ← hE]
  simp only [Nat.sub_self, pow_zero, one_mul, Nat.add_sub_cancel, Int.cast_neg, Int.cast_natCast, neg_div]
  ring

theorem smF_congr_gen : ∀ (p : ℕ) [Fact p.Prime] (N n j : ℕ) (K : Type) [Field K] [CharZero K] (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ (N * p ^ n) → 0 < N → ¬ p ∣ N → 2 ≤ j → j ^ 2 * p ≤ p ^ n → ∀ (c : ℤ), ¬ (p : ℤ) ∣ c → ∀ (α a₁ a₂ : ℤ), 0 ≤ α → α < (p : ℤ) ^ n → a₁ ≡ N * α [ZMOD (p : ℤ) ^ n] → ∀ r : ℕ, ∃ D : ℕ, ¬ p ∣ D ∧ IsIntegral ℤ ((D : K) * ((α : K) ^ (j - 1) * smF c 1 (N * p ^ n) ζ a₁ a₂ r - (p : K) ^ (n * (j - 1)) * smF c j (N * p ^ n) ζ a₁ a₂ r) / (p : K) ^ (n - 1)) := by
  intro p _ N n j K _ _ ζ hp2 hζ hN hpN hj hn c hc α a₁ a₂ h0 h1 ha r
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := by
    rcases n with _ | n
    · exfalso; have := hp.two_le; rw [pow_zero] at hn; nlinarith
    · exact ⟨n, rfl⟩
  rw [show m + 2 - 1 = m + 1 from rfl, Nat.add_sub_cancel]
  suffices H : ∃ y ∈ pInt p K, (α : K) ^ (m + 1) * smF c 1 (N * p ^ (n + 1)) ζ a₁ a₂ r -
      (p : K) ^ ((n + 1) * (m + 1)) * smF c (m + 2) (N * p ^ (n + 1)) ζ a₁ a₂ r = (p : K) ^ n * y by
    obtain ⟨y, ⟨D, hD, hy⟩, E⟩ := H
    refine ⟨D, hD, ?_⟩
    rw [E, mul_left_comm, mul_div_cancel_left₀ _ (pow_ne_zero _ hp0)]
    exact hy
  rcases eq_or_ne r 0 with rfl | hr
  · exact const_congr_gen hp2 hN hpN n m ζ hc a₂ h0 h1 ha
  have hc0 : (c : K) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
    exact_mod_cast this
  have hca : c * a₁ ≡ N * (c * α) [ZMOD (p : ℤ) ^ (n + 1)] := by
    have := ha.mul_left c; rwa [mul_left_comm] at this
  obtain ⟨y1, hy1, E1⟩ := coefPos_congr_gen hN hpN (n + 1) (m + 1) hζ α a₁ a₂ ha r
  obtain ⟨y2, hy2, E2⟩ := coefPos_congr_gen hN hpN (n + 1) (m + 1) hζ (c * α) (c * a₁) (c * a₂) hca r
  have hz : (c : K) ^ ((2 : ℤ) - ((m + 2 : ℕ) : ℤ)) = ((c : K)⁻¹) ^ m := by
    rw [show (2 : ℤ) - ((m + 2 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]
  have hz1 : (c : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ)) = c := by norm_num
  refine ⟨p * ((c : K) ^ 2 * y1 - ((c : K)⁻¹) ^ m * y2), mul_mem (natCast_mem _ _)
    (sub_mem (mul_mem (pow_mem (intCast_mem _ _) _) hy1) (mul_mem (pow_mem (inv_int_mem hc) m) hy2)), ?_⟩
  simp only [smF, eisF, if_neg hr, hz, hz1]
  have hcm : ((c : K)⁻¹) ^ m * ((c * α : ℤ) : K) ^ (m + 1) = c * (α : K) ^ (m + 1) := by
    push_cast; rw [inv_pow]; field_simp; ring
  linear_combination (c : K) ^ 2 * E1 - ((c : K)⁻¹) ^ m * E2 +
    coefPos 1 (N * p ^ (n + 1)) ζ (c * a₁) (c * a₂) r * hcm

end GlobalTheory.EisCongGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearLimitOfCompatibleFamily
section
open Filter Topology

namespace GlobalTheory

theorem exists_baseChange_extension_of_flat {A K E M : Type*} [CommRing A] [Field K] [Algebra A K]
    [Module.Flat A K] [AddCommGroup E] [Module K E] [AddCommGroup M] [Module A M]
    (B : Submodule A M) (Θ : B → E)
    (h : ∀ (a a' : A) (b b' : B),
      Θ (a • b + a' • b') = algebraMap A K a • Θ b + algebraMap A K a' • Θ b') :
    ∃ L : TensorProduct A K M →ₗ[K] E, ∀ b : B, L (1 ⊗ₜ[A] (b : M)) = Θ b := by
  letI : Module A E := Module.compHom E (algebraMap A K)
  have hs : ∀ (a : A) (e : E), a • e = algebraMap A K a • e := fun _ _ => rfl
  haveI : IsScalarTower A K E := ⟨fun a k e => by rw [hs, Algebra.smul_def, mul_smul]⟩
  let Θ' : B →ₗ[A] E :=
    { toFun := Θ
      map_add' := fun b b' => by simpa using h 1 1 b b'
      map_smul' := fun a b => by
        have := h a 0 b b
        rwa [zero_smul, add_zero, map_zero, zero_smul, add_zero] at this }
  have hinj : Function.Injective (B.subtype.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ B.injective_subtype
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (B.subtype.baseChange K)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(Θ'.liftBaseChange K).comp r, fun b => ?_⟩
  have h1 : r (1 ⊗ₜ[A] (b : M)) = 1 ⊗ₜ[A] b := by
    simpa using LinearMap.congr_fun hr (1 ⊗ₜ[A] b)
  rw [LinearMap.comp_apply, h1, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem tendsto_appr_padicComplex (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) :
    Tendsto (fun n => (((a.appr n : ℕ) : PadicAlgCl l) : ℂ_[l])) atTop
      (𝓝 ((algebraMap ℤ_[l] (PadicAlgCl l) a : PadicAlgCl l) : ℂ_[l])) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hq : ‖(l : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq)
  have hn : ∀ z : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ = ‖z‖ := fun z =>
    PadicAlgCl.norm_extends l (z : ℚ_[l])
  rw [← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℤ_[l] (PadicAlgCl l)), ← map_sub, hn, norm_sub_rev]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n a)
  rw [← ht, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) t.norm_le_one

theorem exists_linear_limit_of_compatible_family :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M)
      (R : ℕ → M → PadicAlgCl l → Prop) (C : ℝ),
    (∀ n, ∀ b ∈ B, ∃ x, R n b x) →
    (∀ n, ∀ b ∈ B, ∀ x y, R (n + 1) b x → R n b y →
      ‖x - y‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖) →
    (∀ n, ∀ b ∈ B, ∀ b' ∈ B, ∀ (a a' : ℤ_[l]) (x x' : PadicAlgCl l), R n b x → R n b' x' →
      R n (a • b + a' • b')
        (((a.appr n : ℕ) : PadicAlgCl l) * x + ((a'.appr n : ℕ) : PadicAlgCl l) * x')) →
    ∃ L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l], ∀ n, ∀ b ∈ B, ∀ x,
      R n b x → ‖(x : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖ := by
  intro l _ M _ _ B R C h1 h2 h3
  simp only [norm_pow] at h2 ⊢
  set q : ℝ := ‖((l : ℕ) : PadicAlgCl l)‖ with hqdef
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q < 1 := by
    rw [hqdef, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  choose! x hx using h1
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans
      (h2 0 0 B.zero_mem _ _ (hx 1 0 B.zero_mem) (hx 0 0 B.zero_mem))
    simpa using this
  have hmono : ∀ {n m : ℕ}, n ≤ m → C * q ^ m ≤ C * q ^ n := fun h =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1.le h) hC
  have htail : ∀ n, ∀ b ∈ B, ∀ y, R n b y → ∀ m, n + 1 ≤ m → ‖x m b - y‖ ≤ C * q ^ n := by
    intro n b hb y hy m hm
    induction m, hm using Nat.le_induction with
    | base => exact h2 n b hb _ _ (hx _ b hb) hy
    | succ m hm ih =>
      have e : x (m + 1) b - y = (x (m + 1) b - x m b) + (x m b - y) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (h2 m b hb _ _ (hx _ b hb) (hx _ b hb)).trans (hmono (by omega))
  have hlim : ∀ b : B, ∃ z : ℂ_[l], Tendsto (fun n => ((x n b : PadicAlgCl l) : ℂ_[l])) atTop (𝓝 z) := by
    intro b
    refine cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric q C hq1 fun n => ?_)
    rw [dist_eq_norm, ← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends, norm_sub_rev]
    exact h2 n b b.2 _ _ (hx _ _ b.2) (hx _ _ b.2)
  choose Θ hΘ using hlim
  have hbound : ∀ n (b : B) (y : PadicAlgCl l), R n b y → ‖(y : ℂ_[l]) - Θ b‖ ≤ C * q ^ n := by
    intro n b y hy
    refine le_of_tendsto ((tendsto_const_nhds (x := (y : ℂ_[l]))).sub (hΘ b)).norm
      (eventually_atTop.2 ⟨n + 1, fun m hm => ?_⟩)
    rw [← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends, norm_sub_rev]
    exact htail n b b.2 y hy m hm
  haveI : Module.Flat ℤ_[l] ℚ_[l] := IsLocalization.flat ℚ_[l] (nonZeroDivisors ℤ_[l])
  haveI : Module.Flat ℤ_[l] (PadicAlgCl l) := Module.Flat.trans ℤ_[l] ℚ_[l] (PadicAlgCl l)
  obtain ⟨L, hL⟩ := exists_baseChange_extension_of_flat (K := PadicAlgCl l) B Θ (by
    intro a a' b b'
    have hA := ((tendsto_appr_padicComplex l a).mul (hΘ b)).add
      ((tendsto_appr_padicComplex l a').mul (hΘ b'))
    rw [Algebra.smul_def, Algebra.smul_def]
    refine tendsto_nhds_unique ?_ hA
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun n : ℕ => C * q ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have := hbound n (a • b + a' • b') _
      (h3 n b b.2 b' b'.2 a a' _ _ (hx n _ b.2) (hx n _ b'.2))
    rwa [UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_mul,
      UniformSpace.Completion.coe_mul] at this)
  refine ⟨L, fun n b hb y hy => ?_⟩
  rw [show L (1 ⊗ₜ[ℤ_[l]] b) = Θ ⟨b, hb⟩ from hL ⟨b, hb⟩]
  exact hbound n ⟨b, hb⟩ y hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowerSeriesCompletionEmbeddingStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_power_series_completion_embedding : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (Q : Ideal A), Q.IsMaximal → Q ≠ ⊥ → ∃ (σ : A →ₐ[k] PowerSeries k) (π : A), σ π = PowerSeries.X ∧ Function.Injective σ ∧ (∀ (m : ℕ) (u : A), u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ σ u) ∧ ∀ (m : ℕ) (φ : PowerSeries k), ∃ u : A, (PowerSeries.X : PowerSeries k) ^ m ∣ φ - σ u := by
  first | exact @GlobalTheory.CurveCompletion.exists_completion_embedding | exact GlobalTheory.CurveCompletion.exists_completion_embedding | (intros; apply GlobalTheory.CurveCompletion.exists_completion_embedding <;> assumption)
end

