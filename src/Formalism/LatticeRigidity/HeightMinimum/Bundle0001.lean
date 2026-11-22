import Formalism.LatticeRigidity.Bundle0001
import Mathlib

-- bundled from Formalism.LatticeRigidity.HeightMinimum.BlockEquationHolds
section
namespace Formalism.SA.P

open Matrix Formalism.SA.A

section Blocks

variable {R : Type} [CommRing R] {m : ℕ}

lemma blk_mul_blk (A A' : Matrix (Fin (m+1)) (Fin (m+1)) R) (b c b' c' : Fin (m+1) → R) (d d' : R) :
    blk A b c d * blk A' b' c' d' =
      blk (A * A' + vecMulVec b c') (A *ᵥ b' + d' • b) (c ᵥ* A' + d • c') (c ⬝ᵥ b' + d * d') := by
  unfold blk
  rw [fromBlocks_multiply]
  congr 1
  · ext i j
    simp [Matrix.mul_apply, vecMulVec]
  · ext i j
    simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]
  · ext i j
    simp [Matrix.mul_apply, vecMul, dotProduct]
  · ext i j
    simp [Matrix.mul_apply, dotProduct]

end Blocks

end Formalism.SA.P
end

-- bundled from Formalism.LatticeRigidity.HeightMinimum.ChebyshevLeadingCoeffHolds
section
namespace Formalism.SA.P

open Finset Real Polynomial Polynomial.Chebyshev

lemma node_sub_node_ge {n i k : ℕ} (hn : 1 ≤ n) (hik : i < k) (hk : k ≤ n) :
    2 * ((k:ℝ) - i) ^ 2 / (n:ℝ) ^ 2 ≤ node n i - node n k := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hik' : (i:ℝ) < k := by exact_mod_cast hik
  have hkn : (k:ℝ) ≤ n := by exact_mod_cast hk
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg i
  have hpi := Real.pi_pos
  set S := ((i:ℝ) + k) * π / (2 * n) with hS
  set D := ((k:ℝ) - i) * π / (2 * n) with hD
  have hcos : node n i - node n k = 2 * sin S * sin D := by
    unfold node
    rw [Real.cos_sub_cos]
    have h1 : ((i:ℝ) * π / n + (k:ℝ) * π / n) / 2 = S := by
      rw [hS]; field_simp; try ring
    have h2 : ((i:ℝ) * π / n - (k:ℝ) * π / n) / 2 = -D := by
      rw [hD]; field_simp; try ring
    rw [h1, h2, Real.sin_neg]; ring
  have h2n : (0:ℝ) < 2 * n := by positivity
  have hD0 : 0 ≤ D := div_nonneg (mul_nonneg (by linarith) hpi.le) h2n.le
  have hDle : D ≤ π / 2 := by
    rw [hD, div_le_iff₀ h2n]
    have : (k:ℝ) - i ≤ n := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this hpi.le]
  have hq : 0 ≤ ((k:ℝ) - i) / n := div_nonneg (by linarith) hnpos.le
  have hsinD : ((k:ℝ) - i) / n ≤ sin D := by
    have := Real.mul_le_sin hD0 hDle
    have e : 2 / π * D = ((k:ℝ) - i) / n := by rw [hD]; field_simp; try ring
    linarith
  have hsinS : ((k:ℝ) - i) / n ≤ sin S := by
    have hS0 : 0 ≤ S := div_nonneg (mul_nonneg (by linarith) hpi.le) h2n.le
    by_cases hS2 : S ≤ π / 2
    · have := Real.mul_le_sin hS0 hS2
      have e : 2 / π * S = ((i:ℝ) + k) / n := by rw [hS]; field_simp; try ring
      have : ((k:ℝ) - i) / n ≤ ((i:ℝ) + k) / n := by
        apply div_le_div_of_nonneg_right _ hnpos.le; linarith
      linarith
    · push Not at hS2
      have hSle : S ≤ π := by
        rw [hS, div_le_iff₀ h2n]
        have : (i:ℝ) + k ≤ 2 * n := by linarith
        nlinarith [mul_le_mul_of_nonneg_right this hpi.le]
      have h0' : 0 ≤ π - S := by linarith
      have h1' : π - S ≤ π / 2 := by linarith
      have := Real.mul_le_sin h0' h1'
      rw [Real.sin_pi_sub] at this
      have e : 2 / π * (π - S) = (2 * (n:ℝ) - i - k) / n := by rw [hS]; field_simp; try ring
      have : ((k:ℝ) - i) / n ≤ (2 * (n:ℝ) - i - k) / n := by
        apply div_le_div_of_nonneg_right _ hnpos.le; linarith
      linarith
  rw [hcos]
  have e : 2 * ((k:ℝ) - i) ^ 2 / (n:ℝ) ^ 2 = 2 * (((k:ℝ) - i) / n) * (((k:ℝ) - i) / n) := by
    field_simp
  rw [e]
  have := mul_le_mul hsinS hsinD hq (hq.trans hsinS)
  nlinarith

end Formalism.SA.P
end

-- bundled from Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
section
open MeasureTheory Metric Module

namespace Formalism.SA.P

theorem card_le_of_separated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {α : Type*} (S : Finset α) (g : α → E) (lam R : ℝ)
    (hlam : 0 < lam) (hR : 0 ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → lam ≤ ‖g x - g y‖)
    (hbd : ∀ x ∈ S, ‖g x‖ ≤ R) :
    (S.card : ℝ) ≤ (1 + 2 * R / lam) ^ finrank ℝ E := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar with hμ
  have hr : 0 < lam / 2 := by positivity
  have hR2 : 0 < R + lam / 2 := by positivity
  have hdisj : Set.PairwiseDisjoint (↑S : Set α) (fun x => ball (g x) (lam / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr ?_
    intro z hz1 hz2
    simp only [mem_ball, dist_eq_norm] at hz1 hz2
    have h1 := hsep x hx y hy hxy
    have h2 : ‖g x - g y‖ < lam := by
      calc ‖g x - g y‖ = ‖(z - g y) - (z - g x)‖ := by congr 1; abel
        _ ≤ ‖z - g y‖ + ‖z - g x‖ := norm_sub_le _ _
        _ < lam / 2 + lam / 2 := add_lt_add hz2 hz1
        _ = lam := by ring
    linarith
  have hsub : (⋃ x ∈ S, ball (g x) (lam / 2)) ⊆ ball (0 : E) (R + lam / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    simp only [mem_ball, dist_eq_norm, sub_zero] at hz ⊢
    calc ‖z‖ = ‖(z - g x) + g x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - g x‖ + ‖g x‖ := norm_add_le _ _
      _ < lam / 2 + R := add_lt_add_of_lt_of_le hz (hbd x hx)
      _ = R + lam / 2 := by ring
  have hball : ∀ c : E, ∀ r : ℝ, 0 < r →
      μ (ball c r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) :=
    fun c r hr' => Measure.addHaar_ball_of_pos μ c hr'
  have hb1 : ∀ x, μ (ball (g x) (lam / 2)) =
      ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) * μ (ball 0 1) := fun x => hball _ _ hr
  have hV0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ (0 : E) one_pos).ne'
  have hVtop : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have key : (S.card : ENNReal) * ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + lam / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
    calc (S.card : ENNReal) * ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) * μ (ball 0 1)
        = ∑ x ∈ S, μ (ball (g x) (lam / 2)) := by
          simp only [hb1, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ = μ (⋃ x ∈ S, ball (g x) (lam / 2)) :=
          (measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)).symm
      _ ≤ μ (ball 0 (R + lam / 2)) := measure_mono hsub
      _ = _ := hball 0 _ hR2
  have key2 : (S.card : ENNReal) * ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + lam / 2) ^ finrank ℝ E) := by
    exact (ENNReal.mul_le_mul_iff_left hV0 hVtop).mp key
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at key2
  have key3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key2
  have hpos : 0 < (lam / 2) ^ finrank ℝ E := pow_pos hr _
  have hq : 1 + 2 * R / lam = (R + lam / 2) / (lam / 2) := by
    first
    | (field_simp; done)
    | (field_simp; ring)
  rw [hq, div_pow, le_div_iff₀ hpos]
  exact key3

theorem packing_count_geometric_mean : Formalism.SA.P7.PackCount := by
  unfold Formalism.SA.P7.PackCount
  intro ι _ _ V _ _ _ N hN S lam X hlam hX hsep hbd
  have hnpos : 0 < Fintype.card ι := Fintype.card_pos
  have hnR : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hnpos
  have hQpos : 0 < ∏ v, X v := Finset.prod_pos (fun v _ => hX v)
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (∏ v, X v) ^ (1 / (Fintype.card ι : ℝ)) := ⟨_, rfl⟩
  have hPpos : 0 < P := by rw [hP]; exact Real.rpow_pos_of_pos hQpos _
  have hPn : P ^ Fintype.card ι = ∏ v, X v := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hQpos.le, one_div_mul_cancel hnR.ne',
      Real.rpow_one]
  obtain ⟨c, hcdef⟩ : ∃ c : ι → ℝ, c = fun v => P / X v := ⟨_, rfl⟩
  have hc : ∀ v, 0 < c v := by
    intro v
    rw [hcdef]
    exact div_pos hPpos (hX v)
  have hcX : ∀ v, c v * X v = P := by
    intro v
    rw [hcdef]
    exact div_mul_cancel₀ P (hX v).ne'
  have hprodc : ∏ v, c v = 1 := by
    rw [hcdef]
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
    rw [hPn, div_self hQpos.ne']
  obtain ⟨g, hg⟩ : ∃ g : ((v : ι) → V v) → ((v : ι) → V v),
      ∀ x, g x = fun v => c v • x v := ⟨_, fun _ => rfl⟩
  have hbdg : ∀ x ∈ S, ‖g x‖ ≤ P := by
    intro x hx
    refine (pi_norm_le_iff_of_nonneg hPpos.le).mpr fun v => ?_
    have hgv : g x v = c v • x v := by rw [hg]
    rw [hgv, norm_smul, Real.norm_eq_abs, abs_of_pos (hc v)]
    calc c v * ‖x v‖ ≤ c v * X v := mul_le_mul_of_nonneg_left (hbd x hx v) (hc v).le
      _ = P := hcX v
  have hsepg : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → lam ≤ ‖g x - g y‖ := by
    intro x hx y hy hxy
    have h1 := hsep x hx y hy hxy
    have hM0 : 0 ≤ ‖g x - g y‖ := norm_nonneg _
    have hcoord : ∀ v, c v * ‖x v - y v‖ ≤ ‖g x - g y‖ := by
      intro v
      have hd : (g x - g y) v = c v • (x v - y v) := by
        simp only [Pi.sub_apply, hg, smul_sub]
      have h2 := norm_le_pi_norm (g x - g y) v
      rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (hc v)] at h2
      exact h2
    have hprod : ∏ v, ‖x v - y v‖ ≤ ‖g x - g y‖ ^ Fintype.card ι := by
      calc ∏ v, ‖x v - y v‖ = (∏ v, c v) * ∏ v, ‖x v - y v‖ := by rw [hprodc, one_mul]
        _ = ∏ v, (c v * ‖x v - y v‖) := by rw [Finset.prod_mul_distrib]
        _ ≤ ∏ _v : ι, ‖g x - g y‖ :=
            Finset.prod_le_prod (fun v _ => mul_nonneg (hc v).le (norm_nonneg _))
              (fun v _ => hcoord v)
        _ = ‖g x - g y‖ ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
    calc lam ≤ (∏ v, ‖x v - y v‖) ^ (1 / (Fintype.card ι : ℝ)) := h1
      _ ≤ (‖g x - g y‖ ^ Fintype.card ι) ^ (1 / (Fintype.card ι : ℝ)) :=
          Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => norm_nonneg _) hprod (by positivity)
      _ = ‖g x - g y‖ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hM0, mul_one_div_cancel hnR.ne',
            Real.rpow_one]
  have main := Formalism.SA.P.card_le_of_separated S g lam P hlam hPpos.le hsepg hbdg
  have hdim : finrank ℝ ((v : ι) → V v) = N * Fintype.card ι := by
    rw [Module.finrank_pi_fintype]
    simp only [hN, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  rw [hdim] at main
  rw [← hP]
  exact main

end Formalism.SA.P
end

