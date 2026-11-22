import Mathlib
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0064
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumVonMangoldtDivSqTail
section
open Finset ArithmeticFunction

namespace GlobalTheory

theorem sum_von_mangoldt_div_sq_tail
    (hψ : ∀ N : ℕ, ∑ n ∈ Icc 1 N, Λ n ≤ 2 * (N : ℝ)) (M : ℕ) (hM : 1 ≤ M) (N : ℕ) (hN : M ≤ N) :
    ∑ n ∈ Ioc M N, Λ n / (n : ℝ) ^ 2 ≤ (∑ n ∈ Icc 1 N, Λ n) / (N : ℝ) ^ 2 + 4 / M - 4 / N := by
  induction N, hN using Nat.le_induction with
  | base =>
    have : 0 ≤ (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 :=
      div_nonneg (sum_nonneg fun _ _ => vonMangoldt_nonneg) (by positivity)
    simpa using this
  | succ N hN ih =>
    rw [sum_Ioc_succ_top hN, sum_Icc_succ_top (by omega)]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hA := hψ N
    set A := ∑ n ∈ Icc 1 N, Λ n
    push_cast
    have h1 : 0 ≤ 1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2 := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h2 := mul_le_mul_of_nonneg_right hA h1
    have h3 : 2 * (N : ℝ) * (1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2) ≤ 4 / N - 4 / ((N : ℝ) + 1) := by
      have e : 4 / N - 4 / ((N : ℝ) + 1) - 2 * (N : ℝ) * (1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2)
          = 2 / (N * ((N : ℝ) + 1) ^ 2) := by
        field_simp
        ring
      have : 0 ≤ 2 / (N * ((N : ℝ) + 1) ^ 2) := by positivity
      linarith
    have e1 : A * (1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2) = A / (N : ℝ) ^ 2 - A / ((N : ℝ) + 1) ^ 2 := by
      ring
    rw [add_div]
    linarith

theorem sum_vonMangoldt_div_sq_tail
    (hψ : ∀ N : ℕ, ∑ n ∈ Icc 1 N, Λ n ≤ 2 * (N : ℝ)) (M : ℕ) (hM : 1 ≤ M) (N : ℕ) :
    ∑ n ∈ Ioc M N, Λ n / (n : ℝ) ^ 2 ≤ 4 / M := by
  rcases le_or_gt M N with hN | hN
  · have h := sum_von_mangoldt_div_sq_tail hψ M hM N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h2 : (∑ n ∈ Icc 1 N, Λ n) / (N : ℝ) ^ 2 ≤ 4 / N := by
      rw [div_le_div_iff₀ (by positivity) hN0]
      nlinarith [hψ N, mul_le_mul_of_nonneg_right (hψ N) hN0.le]
    linarith
  · rw [Ioc_eq_empty (by omega)]
    simp only [sum_empty]
    positivity

theorem prime_sum_square_bound : Formalism.HermitianLattices.GL2a2.SizeSpSq := by
  intro hψ
  obtain ⟨C, hC⟩ := prime_power_von_mangoldt_sum_bound
  have hL : Formalism.HermitianLattices.GL2a2.SizeSpLarge := GlobalTheory.large_prime_sum_bound
  have hψ' : ∀ N : ℕ, ∑ n ∈ Icc 1 N, Λ n ≤ 2 * (N : ℝ) := fun N => by
    simpa using hψ N (Nat.cast_nonneg N)
  refine ⟨6 * C ^ 2 + 12800, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set N : ℕ := ⌊x ^ (400 : ℝ)⌋₊ with hN
  have hNz : (N : ℝ) ≤ x ^ (400 : ℝ) := Nat.floor_le (by positivity)
  set M : ℕ := ⌊x⌋₊ with hM
  have hM1 : 1 ≤ M := Nat.le_floor (by simpa using (by linarith : (1 : ℝ) ≤ x))
  have hMx : (M : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxM : x < M + 1 := Nat.lt_floor_add_one x
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set K : ℕ := ⌊√x⌋₊ with hK
  have hKx : (K : ℝ) ≤ √x := Nat.floor_le (Real.sqrt_nonneg x)
  have hxK : √x < K + 1 := Nat.lt_floor_add_one _
  have hs0 : 0 < √x := Real.sqrt_pos.2 hx0
  have hlogs : Real.log √x = Real.log x / 2 := Real.log_sqrt hx0.le
  have hsP : ∀ p : ℕ, 0 ≤ Formalism.HermitianLattices.GL2a2.sP x p := fun p => by
    unfold Formalism.HermitianLattices.GL2a2.sP Formalism.HermitianLattices.GL2PrimeSums.cn
    exact sum_nonneg fun i _ => mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (by positivity))
  let f₁ : ℕ → ℝ := fun n => if n ∈ Icc 1 K then C ^ 2 * Real.log x ^ 2 else 0
  let f₂ : ℕ → ℝ := fun n => if n ∈ Icc 1 M then 2 * C ^ 2 * Real.log x * Λ n else 0
  let f₃ : ℕ → ℝ := fun n => if n ∈ Ioc M N then 1600 * x ^ 2 * Real.log x * (Λ n / (n : ℝ) ^ 2) else 0
  have hf₁ : ∀ n, 0 ≤ f₁ n := fun n => by simp only [f₁]; split_ifs <;> positivity
  have hf₂ : ∀ n, 0 ≤ f₂ n := fun n => by
    have : 0 ≤ Λ n := vonMangoldt_nonneg
    simp only [f₂]; split_ifs <;> positivity
  have hf₃ : ∀ n, 0 ≤ f₃ n := fun n => by
    have : 0 ≤ Λ n := vonMangoldt_nonneg
    simp only [f₃]; split_ifs <;> positivity
  have hterm : ∀ p ∈ (Icc 1 N).filter (fun p => p.Prime),
      Formalism.HermitianLattices.GL2a2.sP x p ^ 2 ≤ f₁ p + f₂ p + f₃ p := by
    intro p hp
    simp only [mem_filter, mem_Icc] at hp
    obtain ⟨⟨hp1, hpN⟩, hp⟩ := hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hall : Formalism.HermitianLattices.GL2a2.sP x p ^ 2 ≤ C ^ 2 * Real.log x ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (hsP p) (hC x hx p hp) 2
    by_cases h1 : p ≤ K
    · have : f₁ p = C ^ 2 * Real.log x ^ 2 := if_pos (mem_Icc.2 ⟨hp1, h1⟩)
      linarith [hf₂ p, hf₃ p]
    by_cases h2 : p ≤ M
    · have e : f₂ p = 2 * C ^ 2 * Real.log x * Λ p := if_pos (mem_Icc.2 ⟨hp1, h2⟩)
      rw [vonMangoldt_apply_prime hp] at e
      have hKp : (K : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : K + 1 ≤ p)
      have : Real.log √x ≤ Real.log p := Real.log_le_log hs0 (by linarith)
      have h3 : Real.log x ≤ 2 * Real.log p := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ C ^ 2 * Real.log x)
      nlinarith [hf₁ p, hf₃ p]
    · have e : f₃ p = 1600 * x ^ 2 * Real.log x * (Λ p / (p : ℝ) ^ 2) :=
        if_pos (mem_Ioc.2 ⟨by omega, hpN⟩)
      rw [vonMangoldt_apply_prime hp] at e
      have hMp : (M : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : M + 1 ≤ p)
      have h3 : Formalism.HermitianLattices.GL2a2.sP x p ^ 2 ≤ (2 * x * Real.log p / p) ^ 2 :=
        pow_le_pow_left₀ (hsP p) (hL x hx0 p hp (by linarith)) 2
      have hpN' : (p : ℝ) ≤ N := by exact_mod_cast hpN
      have h4 : Real.log p ≤ 400 * Real.log x := by
        rw [← Real.log_rpow hx0]
        exact Real.log_le_log hp0 (hpN'.trans hNz)
      have h5 := mul_le_mul_of_nonneg_left h4
        (by positivity : 0 ≤ 4 * x ^ 2 * (Real.log p / (p : ℝ) ^ 2))
      have e2 : (2 * x * Real.log p / p) ^ 2 = 4 * x ^ 2 * (Real.log p / (p : ℝ) ^ 2) * Real.log p := by
        ring
      nlinarith [hf₁ p, hf₂ p]
  have hsum : ∀ (S T : Finset ℕ) (g : ℕ → ℝ), (∀ n, 0 ≤ g n) →
      ∑ n ∈ S, (if n ∈ T then g n else 0) ≤ ∑ n ∈ T, g n := by
    intro S T g hg
    rw [sum_ite_mem]
    exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => hg n
  have s₁ : ∑ p ∈ (Icc 1 N).filter (fun p => p.Prime), f₁ p ≤ 2 * C ^ 2 * x * Real.log x := by
    refine (hsum _ _ _ fun n => by positivity).trans ?_
    simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have h1 : Real.log √x ≤ √x - 1 := Real.log_le_sub_one_of_pos hs0
    have h2 : √x * √x = x := Real.mul_self_sqrt hx0.le
    have h3 : (K : ℝ) * Real.log x ≤ 2 * x := by
      have : (K : ℝ) * Real.log x ≤ √x * (2 * √x) :=
        mul_le_mul hKx (by linarith) hlx hs0.le
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ C ^ 2 * Real.log x)
    nlinarith
  have s₂ : ∑ p ∈ (Icc 1 N).filter (fun p => p.Prime), f₂ p ≤ 4 * C ^ 2 * x * Real.log x := by
    refine (hsum _ _ _ fun n => by
      have : 0 ≤ Λ n := vonMangoldt_nonneg
      positivity).trans ?_
    rw [← mul_sum]
    have h4 := mul_le_mul_of_nonneg_left ((hψ' M).trans (by linarith : 2 * (M : ℝ) ≤ 2 * x))
      (by positivity : 0 ≤ 2 * C ^ 2 * Real.log x)
    linarith
  have s₃ : ∑ p ∈ (Icc 1 N).filter (fun p => p.Prime), f₃ p ≤ 12800 * x * Real.log x := by
    refine (hsum _ _ _ fun n => by
      have : 0 ≤ Λ n := vonMangoldt_nonneg
      positivity).trans ?_
    rw [← mul_sum]
    have h1 : 4 / (M : ℝ) ≤ 8 / x := by
      rw [div_le_div_iff₀ (by linarith) hx0]
      linarith
    have h4 := mul_le_mul_of_nonneg_left ((sum_vonMangoldt_div_sq_tail hψ' M hM1 N).trans h1)
      (by positivity : 0 ≤ 1600 * x ^ 2 * Real.log x)
    have e : 1600 * x ^ 2 * Real.log x * (8 / x) = 12800 * x * Real.log x := by
      field_simp
      ring
    linarith
  have := sum_le_sum hterm
  rw [sum_add_distrib, sum_add_distrib] at this
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
section
noncomputable section
open scoped MatrixGroups
namespace GlobalTheory.ThAdd
open GlobalTheory.KZ GlobalTheory.Glue

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem theta_mul (s : ℚ) (x y : HahnSeries ℚ Ω) :
    theta s (x * y) = theta s x * y + x * theta s y := by
  ext a
  have hx : (theta s x).support ⊆ x.support := fun r hr h => hr (by simp [theta, h])
  have hy : (theta s y).support ⊆ y.support := fun r hr h => hr (by simp [theta, h])
  rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' x.isPWO_support hx,
    HahnSeries.coeff_mul_right' y.isPWO_support hy]
  show algebraMap ℚ Ω (s * a) * (x * y).coeff a = _
  rw [HahnSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ij hij => ?_)
  rw [Finset.mem_addAntidiagonal] at hij
  obtain ⟨-, -, h⟩ := hij
  show algebraMap ℚ Ω (s * a) * (x.coeff ij.1 * y.coeff ij.2) =
    algebraMap ℚ Ω (s * ij.1) * x.coeff ij.1 * y.coeff ij.2 + x.coeff ij.1 * (algebraMap ℚ Ω (s * ij.2) * y.coeff ij.2)
  rw [← h, mul_add, map_add]; ring

def Ig (A : ValuationSubring Ω) (φ : HahnSeries ℚ Ω) : Prop := ∀ r, φ.coeff r ∈ A

def Dv (A : ValuationSubring Ω) (l n : ℕ) (φ : HahnSeries ℚ Ω) : Prop := ∀ r, ∃ z ∈ A, φ.coeff r = (l : Ω) ^ n * z

theorem Ig.mul {A : ValuationSubring Ω} {x y : HahnSeries ℚ Ω} (hx : Ig A x) (hy : Ig A y) : Ig A (x * y) := by
  intro r; rw [HahnSeries.coeff_mul]
  exact sum_mem (fun ij _ => mul_mem (hx _) (hy _))

theorem Dv.add {A : ValuationSubring Ω} {l n : ℕ} {x y : HahnSeries ℚ Ω} (hx : Dv A l n x) (hy : Dv A l n y) :
    Dv A l n (x + y) := by
  intro r; obtain ⟨z, hz, e⟩ := hx r; obtain ⟨z', hz', e'⟩ := hy r
  exact ⟨z + z', add_mem hz hz', by rw [HahnSeries.coeff_add, e, e', mul_add]⟩

theorem Dv.mul {A : ValuationSubring Ω} {l n : ℕ} {x y : HahnSeries ℚ Ω} (hx : Dv A l n x) (hy : Ig A y) :
    Dv A l n (x * y) := by
  intro r; rw [HahnSeries.coeff_mul]
  choose z hz e using hx
  refine ⟨∑ ij ∈ Finset.addAntidiagonal x.isPWO_support y.isPWO_support r, z ij.1 * y.coeff ij.2,
    sum_mem (fun ij _ => mul_mem (hz _) (hy _)), ?_⟩
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun ij _ => ?_); rw [e]; ring

theorem dv_iff {A : ValuationSubring Ω} {l n : ℕ} {x y : HahnSeries ℚ Ω} :
    (∀ r, CgA A l n (x.coeff r) (y.coeff r)) ↔ Dv A l n (x - y) := by
  simp [CgA, Dv]

end GlobalTheory.ThAdd

namespace GlobalTheory.ThAdd
open GlobalTheory.KZ GlobalTheory.Glue
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem unit_iff (A : ValuationSubring Ω) (x : Ω) (hx : x ∈ A) : (x ≠ 0 ∧ x⁻¹ ∈ A) ↔ A.valuation x = 1 := by
  constructor
  · rintro ⟨h0, hi⟩
    have h1 := (A.valuation_le_one_iff x).2 hx
    have h2 := (A.valuation_le_one_iff _).2 hi
    rw [map_inv₀] at h2
    have hv : A.valuation x ≠ 0 := by simpa using h0
    have : 1 ≤ A.valuation x := by
      by_contra hc; push_neg at hc
      have := one_lt_inv₀ (zero_lt_iff.2 hv) |>.2 hc
      exact absurd h2 (not_le.2 this)
    exact le_antisymm h1 this
  · intro h
    have h0 : x ≠ 0 := by rintro rfl; simp at h
    refine ⟨h0, (A.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, h, inv_one]

theorem prim_iff (A : ValuationSubring Ω) (φ : HahnSeries ℚ Ω) :
    Prim A φ ↔ (∀ r, A.valuation (φ.coeff r) ≤ 1) ∧ ∃ r, A.valuation (φ.coeff r) = 1 := by
  constructor
  · rintro ⟨h1, r, h2⟩
    exact ⟨fun r => (A.valuation_le_one_iff _).2 (h1 r), r, (unit_iff A _ (h1 r)).1 h2⟩
  · rintro ⟨h1, r, h2⟩
    have h1' : ∀ r, φ.coeff r ∈ A := fun r => (A.valuation_le_one_iff _).1 (h1 r)
    exact ⟨h1', r, (unit_iff A _ (h1' r)).2 h2⟩

theorem prim_mul {A : ValuationSubring Ω} {x y : HahnSeries ℚ Ω} (hx : Prim A x) (hy : Prim A y) : Prim A (x * y) := by
  rw [prim_iff] at hx hy ⊢
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  set v := A.valuation
  have sx : {r | v (x.coeff r) = 1} ⊆ x.support := fun r hr h => by simp [Set.mem_setOf_eq, h] at hr
  have sy : {r | v (y.coeff r) = 1} ⊆ y.support := fun r hr h => by simp [Set.mem_setOf_eq, h] at hr
  have wx := x.isPWO_support.isWF.mono sx
  have wy := y.isPWO_support.isWF.mono sy
  have nx : {r | v (x.coeff r) = 1}.Nonempty := hx2
  have ny : {r | v (y.coeff r) = 1}.Nonempty := hy2
  set r0 := wx.min nx
  set s0 := wy.min ny
  have hr0 : v (x.coeff r0) = 1 := wx.min_mem nx
  have hs0 : v (y.coeff s0) = 1 := wy.min_mem ny
  have ltx : ∀ r, r < r0 → v (x.coeff r) < 1 := fun r hr =>
    lt_of_le_of_ne (hx1 r) (fun h => wx.not_lt_min nx h hr)
  have lty : ∀ r, r < s0 → v (y.coeff r) < 1 := fun r hr =>
    lt_of_le_of_ne (hy1 r) (fun h => wy.not_lt_min ny h hr)
  have int : ∀ r, v ((x * y).coeff r) ≤ 1 := by
    intro r; rw [HahnSeries.coeff_mul]
    exact v.map_sum_le (fun ij _ => by rw [map_mul]; exact mul_le_one' (hx1 _) (hy1 _))
  refine ⟨int, r0 + s0, ?_⟩
  rw [HahnSeries.coeff_mul, ← Finset.add_sum_erase _ _ ((Finset.mem_addAntidiagonal (x := (r0, s0))).2 ⟨sx (show r0 ∈ {r | v (x.coeff r) = 1} from hr0), sy (show s0 ∈ {r | v (y.coeff r) = 1} from hs0), rfl⟩)]
  have hmain : v (x.coeff r0 * y.coeff s0) = 1 := by rw [map_mul, hr0, hs0, one_mul]
  rw [Valuation.map_add_eq_of_lt_left, hmain]
  rw [hmain]
  refine v.map_sum_lt one_ne_zero (fun ij hij => ?_)
  rw [Finset.mem_erase] at hij
  obtain ⟨hne, hij⟩ := hij
  obtain ⟨-, -, hsum⟩ := Finset.mem_addAntidiagonal.1 hij
  rw [map_mul]
  rcases lt_trichotomy ij.1 r0 with h | h | h
  · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hy1 _)) (ltx _ h)
  · exfalso; apply hne; ext
    · exact h
    · simp only; rw [h] at hsum; exact add_left_cancel hsum
  · have : ij.2 < s0 := by
      by_contra hc; push_neg at hc
      have := add_lt_add_of_lt_of_le h hc
      rw [hsum] at this; exact lt_irrefl _ this
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hx1 _)) (lty _ this)

end GlobalTheory.ThAdd

namespace GlobalTheory.ThAdd
open GlobalTheory.KZ GlobalTheory.Glue
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem isDl_mul {X : Tower Ω ε} {A : ValuationSubring Ω} {l n : ℕ} {s : ℚ} {f f' : X.K} {φ φ' : HahnSeries ℚ Ω}
    (h : IsDl X A l n s f φ) (h' : IsDl X A l n s f' φ') : IsDl X A l n s (f * f') (φ + φ') := by
  obtain ⟨hφ, a, b, κ, hκ, e, pa, pb, c⟩ := h
  obtain ⟨hφ', a', b', κ', hκ', e', pa', pb', c'⟩ := h'
  refine ⟨fun r => by rw [HahnSeries.coeff_add]; exact add_mem (hφ r) (hφ' r),
    a * a', b * b', κ * κ', mul_ne_zero hκ hκ', ?_, ?_, ?_, ?_⟩
  · calc f * f' * (b * b') = (f * b) * (f' * b') := by ring
      _ = _ := by rw [e, e', map_mul]; ring
  · rw [map_mul]; exact prim_mul pa pa'
  · rw [map_mul]; exact prim_mul pb pb'
  · rw [dv_iff] at c c' ⊢
    rw [map_mul, map_mul, theta_mul, theta_mul]
    have key : (φ + φ') * (X.exp a * X.exp a') * (X.exp b * X.exp b') -
        ((theta s (X.exp a) * X.exp a' + X.exp a * theta s (X.exp a')) * (X.exp b * X.exp b') -
          X.exp a * X.exp a' * (theta s (X.exp b) * X.exp b' + X.exp b * theta s (X.exp b'))) =
        (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) * (X.exp a' * X.exp b') +
        (φ' * X.exp a' * X.exp b' - (theta s (X.exp a') * X.exp b' - X.exp a' * theta s (X.exp b'))) * (X.exp a * X.exp b) := by
      ring
    rw [key]
    exact (c.mul (Ig.mul pa'.1 pb'.1)).add (c'.mul (Ig.mul pa.1 pb.1))

theorem isDl_one (X : Tower Ω ε) (A : ValuationSubring Ω) (l n : ℕ) (s : ℚ) : IsDl X A l n s 1 0 := by
  refine ⟨fun r => by simp, 1, 1, 1, one_ne_zero, by simp, ?_, ?_, ?_⟩
  · rw [map_one]; exact ⟨fun r => by rw [HahnSeries.coeff_one]; split_ifs <;> simp, 0, by simp⟩
  · rw [map_one]; exact ⟨fun r => by rw [HahnSeries.coeff_one]; split_ifs <;> simp, 0, by simp⟩
  · intro r
    refine ⟨0, zero_mem A, ?_⟩
    have : theta s (1 : HahnSeries ℚ Ω) = theta s 1 * 1 + 1 * theta s 1 := by
      rw [← theta_mul, mul_one]
    have h0 : theta s (1 : HahnSeries ℚ Ω) = 0 := by
      have : theta s (1 : HahnSeries ℚ Ω) + theta s 1 = theta s 1 + 0 := by
        rw [add_zero]; nth_rewrite 3 [this]; simp
      exact add_left_cancel this
    simp [h0]

theorem isDl_pow {X : Tower Ω ε} {A : ValuationSubring Ω} {l n : ℕ} {s : ℚ} {f : X.K} {φ : HahnSeries ℚ Ω}
    (h : IsDl X A l n s f φ) (k : ℕ) : IsDl X A l n s (f ^ k) ((k : Ω) • φ) := by
  induction k with
  | zero => simpa using isDl_one X A l n s
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ, add_smul, one_smul]
    exact isDl_mul ih h

end GlobalTheory.ThAdd

namespace GlobalTheory.ThAdd
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem inv_mul {X : Tower Ω ε} {H : Subgroup SL(2, ℤ)} {f g : X.K} (hf : Inv X H f) (hg : Inv X H g) :
    Inv X H (f * g) := fun γ hγ => by rw [map_mul, hf γ hγ, hg γ hγ]

theorem inv_pow {X : Tower Ω ε} {H : Subgroup SL(2, ℤ)} {f : X.K} (hf : Inv X H f) (k : ℕ) :
    Inv X H (f ^ k) := fun γ hγ => by rw [map_pow, hf γ hγ]

theorem cls_comb (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (c c' : ℤ_[l]) (f f' : X.Kˣ) :
    c • X.cls l n f + c' • X.cls l n f' = X.cls l n (f ^ (c.appr n) * f' ^ (c'.appr n)) := by
  have red : ∀ (d : ℤ_[l]) (q : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))),
      d • q = ((d.appr n : ℕ) : ℤ_[l]) • q := by
    intro d q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← sub_smul]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    rw [Ideal.span_singleton_pow]
    exact PadicInt.appr_spec n d
  rw [red c, red c']
  simp only [Tower.cls, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  rw [ofMul_mul, ofMul_pow, ofMul_pow, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
    Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem isThB_add : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (b b' : X.Fn l), (l : Ω) ∈ A.nonunits → b ∈ X.B N l w → b' ∈ X.B N l w →
    ∀ (c c' : ℤ_[l]) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l n b φ → IsThB X A N l n b' φ' →
    IsThB X A N l n (c • b + c' • b') (((c.appr n : ℕ) : Ω) • φ + ((c'.appr n : ℕ) : Ω) • φ') := by
  intro Ω _ _ _ ε X A N l _ n w b b' _ _ _ c c' φ φ' h h'
  obtain ⟨f, hfi, hfc, hfd, hfl⟩ := h
  obtain ⟨f', hfi', hfc', hfd', hfl'⟩ := h'
  refine ⟨f ^ (c.appr n) * f' ^ (c'.appr n), ?_, ?_, ?_, ?_⟩
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact inv_mul (inv_pow hfi _) (inv_pow hfi' _)
  · rw [← cls_comb, ← hfc, ← hfc', ← map_smul, ← map_smul, ← map_add]
    rfl
  · intro δ hδ hδ'
    obtain ⟨g, hgi, hg⟩ := hfd δ hδ hδ'
    obtain ⟨g', hgi', hg'⟩ := hfd' δ hδ hδ'
    refine ⟨g ^ (c.appr n) * g' ^ (c'.appr n), inv_mul (inv_pow hgi _) (inv_pow hgi' _), ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    calc (f : X.K) ^ (c.appr n) * (f' : X.K) ^ (c'.appr n) *
          (X.sl (ofSL δ) f ^ (c.appr n) * X.sl (ofSL δ) f' ^ (c'.appr n))
        = ((f : X.K) * X.sl (ofSL δ) f) ^ (c.appr n) * ((f' : X.K) * X.sl (ofSL δ) f') ^ (c'.appr n) := by ring
      _ = _ := by rw [hg, hg']; ring
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact isDl_mul (isDl_pow hfl _) (isDl_pow hfl' _)

end GlobalTheory.ThAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerExpSlashUpperTriangularEqSubstStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_exp_slash_upperTriangular_eq_subst : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (g : GQ), ent g 1 0 = 0 → ∀ f : X.K,
  X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.exp_sl_upper | exact GlobalTheory.CyclotomicQExpansion.exp_sl_upper | (intros; apply GlobalTheory.CyclotomicQExpansion.exp_sl_upper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisActionPreservesGammaLevel
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem Tower.gal_level {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ)
    (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) (hM : 0 < M) (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) :
    ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.gal s f) = X.gal s f := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic M Ω) (Polynomial.degree_cyclotomic_pos M Ω hM).ne'
  rw [Polynomial.isRoot_cyclotomic_iff] at hζ
  have hsζ : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hsζ.pow_eq_one
  intro γ hγ
  have hγ' := hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ'
  obtain ⟨-, h01, h10, -⟩ := hγ'
  have key := X.recip M f hM hf ζ hζ s (i : ℤ) (by rw [zpow_natCast, hi]) γ γ
    ⟨rfl, by simp [en, h01], by simp [en, h10], rfl⟩
  rw [hf γ hγ] at key
  exact key.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerJInvariantTranscendental
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem hahnSeries_order_eq_neg_one_of_coeff {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (h0 : ∀ r : ℚ, r < -1 → h.coeff r = 0) : h.order = -1 := by
  have h1' : h.coeff (-1) ≠ 0 := by rw [h1]; exact one_ne_zero
  have hne : h ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1'
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1') ?_
  exact le_of_not_gt fun hlt => hne (HahnSeries.coeff_order_eq_zero.mp (h0 _ hlt))

theorem hahnSeries_pow_order_of_order_neg_one {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (ho : h.order = -1) (n : ℕ) :
    (h ^ n).order = -(n : ℚ) ∧ (h ^ n).coeff (-(n : ℚ)) = 1 := by
  have hord : ∀ k : ℕ, (h ^ k).order = -(k : ℚ) := fun k => by
    rw [HahnSeries.order_pow, ho]
    simp
  refine ⟨hord n, ?_⟩
  induction n with
  | zero => simp
  | succ k ih =>

    have hm := HahnSeries.coeff_mul_order_add_order (h ^ k) h
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hord k, ho, ih, h1, mul_one] at hm
    have e : -((k + 1 : ℕ) : ℚ) = -(k : ℚ) + -1 := by push_cast; ring
    rw [pow_succ, e, hm]

private theorem hahnSeries_coeff_algebra_smul {Ω : Type} [Field Ω] [Algebra ℚ Ω] (r : Ω) (y : HahnSeries ℚ Ω) (a : ℚ) :
    (@HSMul.hSMul Ω (HahnSeries ℚ Ω) (HahnSeries ℚ Ω) (@instHSMul _ _ Algebra.toSMul) r y).coeff a =
      r * y.coeff a := by
  rw [Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

theorem Tower.jK_transcendental {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    Transcendental Ω X.jK := by
  unfold Transcendental IsAlgebraic
  rintro ⟨p, hp0, hp⟩
  obtain ⟨h1, h0, -⟩ := X.j_exp
  have ho := hahnSeries_order_eq_neg_one_of_coeff h1 h0
  have hz : Polynomial.aeval (X.exp X.jK) p = 0 := by
    rw [Polynomial.aeval_algHom_apply, hp, map_zero]

  have hc : (Polynomial.aeval (X.exp X.jK) p).coeff (-(p.natDegree : ℚ)) = p.leadingCoeff := by
    rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single p.natDegree]
    · rw [hahnSeries_coeff_algebra_smul, (hahnSeries_pow_order_of_order_neg_one h1 ho _).2, mul_one]
      rfl
    · intro i hi hne
      have hlt : i < p.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      have hlt' : (i : ℚ) < p.natDegree := by exact_mod_cast hlt
      rw [hahnSeries_coeff_algebra_smul, HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [(hahnSeries_pow_order_of_order_neg_one h1 ho i).1]
      linarith
    · intro hn
      exact absurd (Finset.self_mem_range_succ _) hn
  rw [hz, HahnSeries.coeff_zero] at hc
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hc.symm)

end GlobalTheory.KZ
end

