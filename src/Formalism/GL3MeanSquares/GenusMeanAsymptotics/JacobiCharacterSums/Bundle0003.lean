import Mathlib

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHFinishA
section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF

theorem near_far (c : ℝ) (A B : ℕ) (hc : 0 < c)
    (hT : ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K →
      (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) →
      ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c ^ K ≤ (∑ i, z i ^ k).re)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (N : ℕ) (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re) (hi : ∃ i, 1 / 2 ≤ ‖u i‖)
    (K : ℕ) (hK2 : 2 ≤ K) (hKB : (B : ℝ) * (∑ i, (u i).re) ≤ ε ^ 2 * K) :
    ∃ j : ℕ, K ≤ j ∧ j ≤ A * K ∧
      c ^ K * (1 / 2) ^ j ≤ (∑ i, u i ^ j).re + ε ^ (j - 2) * ∑ i, (u i).re := by
  have hre : ∀ i, 0 ≤ (u i).re := fun i => le_trans (by positivity) (hu i)
  have hle1 : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h1 := hu i
    have h2 : (u i).re ≤ ‖u i‖ := Complex.re_le_norm _
    nlinarith [norm_nonneg (u i)]
  set near := (univ : Finset (Fin N)).filter (fun i => ε ≤ ‖u i‖) with hnear
  obtain ⟨i0, hi0⟩ := hi
  have hi0n : i0 ∈ near := by simp [hnear]; linarith
  have hne : near.Nonempty := ⟨i0, hi0n⟩
  obtain ⟨is, his, hmax⟩ := near.exists_max_image (fun i => ‖u i‖) hne
  set R := ‖u is‖ with hR
  have hR2 : 1 / 2 ≤ R := le_trans hi0 (hmax i0 hi0n)
  have hR0 : 0 < R := by linarith
  have hR1 : R ≤ 1 := hle1 is
  set n := near.card with hn

  have hcount : (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re := by
    calc (n : ℝ) * ε ^ 2 = ∑ i ∈ near, ε ^ 2 := by simp [hn]
      _ ≤ ∑ i ∈ near, ‖u i‖ ^ 2 := by
          apply sum_le_sum; intro i hi
          have : ε ≤ ‖u i‖ := by simpa [hnear] using hi
          exact pow_le_pow_left₀ hε0.le this 2
      _ ≤ ∑ i ∈ near, (u i).re := sum_le_sum (fun i _ => hu i)
      _ ≤ ∑ i, (u i).re := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hre i)
  have hBn : B * n ≤ K := by
    have h1 : (B : ℝ) * n * ε ^ 2 ≤ ε ^ 2 * K := by
      calc (B : ℝ) * n * ε ^ 2 = B * (n * ε ^ 2) := by ring
        _ ≤ B * ∑ i, (u i).re := mul_le_mul_of_nonneg_left hcount (by positivity)
        _ ≤ _ := hKB
    have h2 : (B : ℝ) * n ≤ K := by
      have : 0 < ε ^ 2 := by positivity
      nlinarith
    exact_mod_cast h2
  have hn1 : 1 ≤ n := Finset.card_pos.mpr hne
  let e := near.equivFin
  let z : Fin n → ℂ := fun k => u (e.symm k) / (R : ℂ)
  have hz : ∀ k, z k = u (e.symm k) / (R : ℂ) := fun k => rfl
  have hzn : ∀ k, ‖z k‖ = ‖u (e.symm k)‖ / R := by
    intro k; rw [hz, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
  obtain ⟨j, hKj, hjA, hj⟩ := hT n K z hn1 hBn
    (by
      intro k; rw [hzn, div_le_one hR0]
      exact hmax _ (e.symm k).2)
    (by
      refine ⟨e ⟨is, his⟩, ?_⟩
      rw [hzn]; simp [R, div_self (ne_of_gt hR0)])
    (by
      intro k
      rw [hzn, hz, Complex.div_ofReal_re]
      have h1 := hu (e.symm k)
      have h2 : ‖u (e.symm k)‖ ≤ R := hmax _ (e.symm k).2
      rw [div_pow, div_le_iff₀ (by positivity)]
      calc ‖u (e.symm k)‖ ^ 2 ≤ (u (e.symm k)).re := h1
        _ ≤ 2 * ((u (e.symm k)).re / R) * R ^ 2 := by
          rw [show 2 * ((u (e.symm k)).re / R) * R ^ 2 = (u (e.symm k)).re * (2 * R) by
            field_simp]
          have : 1 ≤ 2 * R := by linarith
          nlinarith [hre (e.symm k)])
  refine ⟨j, hKj, hjA, ?_⟩

  have hsumz : (∑ k, z k ^ j) * (R : ℂ) ^ j = ∑ i ∈ near, u i ^ j := by
    rw [Finset.sum_mul]
    rw [← Finset.sum_coe_sort near (fun i => u i ^ j)]
    rw [← e.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro k _
    rw [hz, div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ (by exact_mod_cast hR0.ne')
  have hnear_re : c ^ K * (1 / 2) ^ j ≤ (∑ i ∈ near, u i ^ j).re := by
    rw [← hsumz, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    have : (1 / 2 : ℝ) ^ j ≤ R ^ j := pow_le_pow_left₀ (by norm_num) hR2 j
    have hcK : 0 < c ^ K := pow_pos hc K
    nlinarith [pow_pos hR0 j]
  have hfar : -(ε ^ (j - 2) * ∑ i, (u i).re) ≤ (∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), u i ^ j).re := by
    rw [Complex.re_sum]
    have hj2 : 2 ≤ j := le_trans hK2 hKj
    have : ∀ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), -(ε ^ (j - 2) * (u i).re) ≤ (u i ^ j).re := by
      intro i hi
      have hlt : ‖u i‖ < ε := by simpa using hi
      have h1 : -(u i ^ j).re ≤ ‖u i‖ ^ j := by
        have := Complex.abs_re_le_norm (u i ^ j); rw [norm_pow] at this
        linarith [neg_abs_le (u i ^ j).re]
      have h2 : ‖u i‖ ^ j = ‖u i‖ ^ (j - 2) * ‖u i‖ ^ 2 := by
        rw [← pow_add]; congr 1; omega
      have h3 : ‖u i‖ ^ (j - 2) ≤ ε ^ (j - 2) := pow_le_pow_left₀ (norm_nonneg _) hlt.le _
      have h4 : ‖u i‖ ^ (j - 2) * ‖u i‖ ^ 2 ≤ ε ^ (j - 2) * (u i).re :=
        mul_le_mul h3 (hu i) (by positivity) (by positivity)
      linarith
    calc -(ε ^ (j - 2) * ∑ i, (u i).re) ≤ -(ε ^ (j - 2) * ∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), (u i).re) := by
          have : ∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), (u i).re ≤ ∑ i, (u i).re :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hre i)
          have : 0 ≤ ε ^ (j - 2) := by positivity
          nlinarith
      _ = ∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), -(ε ^ (j - 2) * (u i).re) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ _ := sum_le_sum this
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin N)) (fun i => ε ≤ ‖u i‖) (fun i => u i ^ j)
  have hnr : (∑ x ∈ univ.filter (fun x => ε ≤ ‖u x‖), u x ^ j) = ∑ i ∈ near, u i ^ j := rfl
  rw [← hsplit, Complex.add_re, hnr]
  linarith

theorem pow_small_a (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) (hK3 : 3 ≤ K) :
    (K : ℝ) * (q ^ 2 / 8) ^ (K - 1) ≤ q ^ K / 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 3 := ⟨K - 3, by omega⟩
  have hB : (1 : ℝ) + (m + 1 : ℕ) * 7 ≤ (1 + 7) ^ (m + 1) := one_add_mul_le_pow (by norm_num) _
  push_cast at hB ⊢
  rw [div_pow, ← pow_mul]
  have h8 : (0 : ℝ) < 8 ^ (m + 2) := by positivity
  have hq' : q ^ (2 * (m + 2)) = q ^ (m + 3) * q ^ (m + 1) := by rw [← pow_add]; congr 1; ring
  have hqm : q ^ (m + 1) ≤ 1 := pow_le_one₀ hq0 hq1
  have hq3 : 0 ≤ q ^ (m + 3) := by positivity
  rw [hq', mul_div_assoc', div_le_div_iff₀ h8 (by norm_num)]
  have : (8 : ℝ) ^ (m + 2) = 8 * 8 ^ (m + 1) := by ring
  rw [this]
  have h1 : ((m : ℝ) + 3) ≤ 8 ^ (m + 1) := by norm_num at hB; linarith
  have h2 : ((m : ℝ) + 3) * (q ^ (m + 3) * q ^ (m + 1)) ≤ ((m : ℝ) + 3) * q ^ (m + 3) := by
    have : 0 ≤ (m : ℝ) + 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hqm hq3]
  nlinarith [mul_le_mul_of_nonneg_right h1 hq3]

theorem pow_small_b (q : ℝ) (hq0 : 0 ≤ q) (K : ℕ) (hK3 : 3 ≤ K) :
    (K : ℝ) * (q / 4) ^ K ≤ q ^ K / 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 3 := ⟨K - 3, by omega⟩
  have hB : (1 : ℝ) + (m : ℕ) * 3 ≤ (1 + 3) ^ m := one_add_mul_le_pow (by norm_num) _
  rw [div_pow]
  have h4 : (4 : ℝ) ^ (m + 3) = 64 * 4 ^ m := by ring
  rw [h4]
  have hq3 : 0 ≤ q ^ (m + 3) := by positivity
  have h4p : (0 : ℝ) < 4 ^ m := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  push_cast
  norm_num at hB
  have : ((m : ℝ) + 3) * 8 ≤ 64 * 4 ^ m := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hq3]

theorem final_contra (q A K0 a b l : ℝ) (K : ℕ) (hq0 : 0 < q) (hq : q ≤ 1 / 4) (hl : l = -Real.log q)
    (hA : 1 ≤ A) (hK3 : 3 ≤ K) (hK0 : 0 < K0) (ha0 : 0 ≤ a) (ha : a * (2 * l + 2) ≤ 1) (hb : 0 ≤ b)
    (hKab : (K : ℝ) ≤ a * K0 + b) (hbig : b + 64 * A * Real.exp (l * b) < K0)
    (hmain : q ^ K ≤ 2 * A * K * Real.exp (-K0) + K * (q ^ 2 / 8) ^ (K - 1) + K * (q / 4) ^ K) : False := by
  have h1 := pow_small_a q hq0.le (by linarith) K hK3
  have h2 := pow_small_b q hq0.le K hK3
  have hl0 : 0 ≤ l := by
    rw [hl]; have := Real.log_nonpos hq0.le (by linarith); linarith
  have h3 : (3 / 4) * q ^ K ≤ 2 * A * K * Real.exp (-K0) := by linarith
  have hqK : Real.exp (-(K0 / 2) - l * b) ≤ q ^ K := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hq0, Real.exp_le_exp]
    have hlog : Real.log q = -l := by rw [hl]; ring
    rw [hlog]
    have hla : 2 * l * a ≤ 1 := by nlinarith
    nlinarith
  have hE := Real.exp_pos (l * b)
  have hsplit : Real.exp (-(K0 / 2) - l * b) * Real.exp (l * b) * Real.exp K0 = Real.exp (K0 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hexp : K0 ^ 2 / 8 ≤ Real.exp (K0 / 2) := by
    have := Real.pow_div_factorial_le_exp (x := K0 / 2) (by positivity) 2
    norm_num [Nat.factorial] at this; nlinarith
  have hKK : (K : ℝ) ≤ 2 * K0 := by
    have : a ≤ 1 / 2 := by nlinarith
    nlinarith
  have hexpK : Real.exp (-K0) * Real.exp K0 = 1 := by rw [← Real.exp_add]; simp

  have h4 : (3 / 4) * Real.exp (K0 / 2) ≤ 2 * A * K * Real.exp (l * b) := by
    have hx := mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_left hqK (by norm_num)) h3)
      (le_of_lt (mul_pos hE (Real.exp_pos K0)))
    rw [← hsplit]
    have : 2 * A * K * Real.exp (-K0) * (Real.exp (l * b) * Real.exp K0) = 2 * A * K * Real.exp (l * b) * (Real.exp (-K0) * Real.exp K0) := by ring
    rw [this, hexpK] at hx
    linarith
  have hAE : 0 ≤ A * Real.exp (l * b) := by positivity
  have h5 : (3 / 32) * K0 ^ 2 ≤ 4 * K0 * (A * Real.exp (l * b)) := by nlinarith
  have h6 : (3 / 32) * K0 ≤ 4 * (A * Real.exp (l * b)) := by nlinarith
  nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeB
section
open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

lemma dhpr_pow_exp_le (m : ℕ) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    b ^ m * (t ^ m * Real.exp (-(b * t))) ≤ (m.factorial : ℝ) := by
  have hx : 0 ≤ b * t := mul_nonneg hb ht
  have hf : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h1 : (b * t) ^ m ≤ Real.exp (b * t) * (m.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (b * t) hx m
    rwa [div_le_iff₀ hf] at h
  calc b ^ m * (t ^ m * Real.exp (-(b * t))) = (b * t) ^ m * Real.exp (-(b * t)) := by
        rw [mul_pow]; ring
    _ ≤ (Real.exp (b * t) * (m.factorial : ℝ)) * Real.exp (-(b * t)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (m.factorial : ℝ) := by
        rw [mul_comm (Real.exp (b * t)), mul_assoc, ← Real.exp_add]; simp

lemma dhpr_one_sub_exp_neg {a : ℝ} (ha : 0 < a) : a / (1 + a) ≤ 1 - Real.exp (-a) := by
  have hpos : 0 < 1 + a := by linarith
  have h4 : Real.exp (-a) * (1 + a) ≤ 1 := by
    calc Real.exp (-a) * (1 + a) ≤ Real.exp (-a) * Real.exp a :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp a]) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [div_le_iff₀ hpos]
  have e : (1 - Real.exp (-a)) * (1 + a) = (1 + a) - Real.exp (-a) * (1 + a) := by ring
  rw [e]; linarith

lemma dhpr_pow_ratio (m : ℕ) : ((m : ℝ) + 1) ^ m ≤ Real.exp 1 * (m : ℝ) ^ m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp only [pow_zero, mul_one]
    linarith [Real.add_one_le_exp (1:ℝ)]
  · have hm : (0:ℝ) < m := by exact_mod_cast h
    have hm' : (m:ℝ) ≠ 0 := hm.ne'
    have key : (m:ℝ) + 1 ≤ m * Real.exp (1 / m) := by
      have h1 := Real.add_one_le_exp (1 / (m:ℝ))
      have h2 : (m:ℝ) * (1 / m + 1) = m + 1 := by
        rw [mul_add, mul_one_div_cancel hm', mul_one, add_comm]
      calc (m:ℝ) + 1 = m * (1 / m + 1) := h2.symm
        _ ≤ m * Real.exp (1 / m) := mul_le_mul_of_nonneg_left h1 hm.le
    calc ((m:ℝ) + 1) ^ m ≤ ((m:ℝ) * Real.exp (1 / m)) ^ m := by gcongr
      _ = Real.exp 1 * (m:ℝ) ^ m := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_one_div_cancel hm', mul_comm]

lemma dhpr_wsup (m : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (v : ℕ) :
    ((v : ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤ Real.exp 1 * m.factorial / η ^ m := by
  have hηm : 0 < η ^ m := pow_pos hη m
  have ht : (0:ℝ) ≤ (v:ℝ) + 1 := by positivity
  have h1 := dhpr_pow_exp_le m hη.le ht
  have h2 : Real.exp (-(η * v)) ≤ Real.exp 1 * Real.exp (-(η * ((v:ℝ) + 1))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : -(η * (v:ℝ)) = 1 + -(η * ((v:ℝ) + 1)) - (1 - η) := by ring
    rw [e]; linarith
  calc ((v : ℝ) + 1) ^ m * Real.exp (-(η * v))
      ≤ ((v : ℝ) + 1) ^ m * (Real.exp 1 * Real.exp (-(η * ((v:ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp 1 * (((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1)))) := by ring
    _ ≤ Real.exp 1 * ((m.factorial : ℝ) / η ^ m) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
        rw [le_div_iff₀ hηm]
        calc ((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1))) * η ^ m
            = η ^ m * (((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1)))) := by ring
          _ ≤ (m.factorial : ℝ) := h1
    _ = Real.exp 1 * m.factorial / η ^ m := by ring

lemma dhpr_wsum (m : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (v0 V : ℕ) :
    ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤
      2 * Real.exp 2 * ((m : ℝ) + 1) * (m.factorial : ℝ) / η ^ (m + 1) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / ((m:ℝ) + 1) := ⟨_, rfl⟩
  have hm1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hm1ne : (m:ℝ) + 1 ≠ 0 := hm1.ne'
  have hδη : ((m:ℝ) + 1) * δ = η := by rw [hδ]; field_simp
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hη hm1
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hη'nn : 0 ≤ (m:ℝ) * δ := mul_nonneg hm0 hδpos.le
  have hsplit : (m:ℝ) * δ + δ = η := by rw [← hδη]; ring
  have hη'le : (m:ℝ) * δ ≤ 1 := by linarith
  have hpow : η ^ m ≤ Real.exp 1 * ((m:ℝ) * δ) ^ m := by
    rw [← hδη, mul_pow, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (dhpr_pow_ratio m) (pow_nonneg hδpos.le m)
  have hterm : ∀ v : ℕ, η ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) ≤
      Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
    intro v
    have ht : (0:ℝ) ≤ (v:ℝ) + 1 := by positivity
    have h1 := dhpr_pow_exp_le m hη'nn ht
    have hexp : Real.exp (-(η * v)) ≤
        Real.exp 1 * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))) * Real.exp (-(δ * v)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [← hsplit]
      have e : -(((m:ℝ) * δ + δ) * (v:ℝ)) =
          1 + -((m:ℝ) * δ * ((v:ℝ) + 1)) + -(δ * v) - (1 - (m:ℝ) * δ) := by ring
      rw [e]; linarith
    calc η ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-(η * v)))
        ≤ (Real.exp 1 * ((m:ℝ) * δ) ^ m) * (((v:ℝ) + 1) ^ m *
            (Real.exp 1 * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))) * Real.exp (-(δ * v)))) := by
          refine mul_le_mul hpow ?_ (by positivity) (mul_nonneg (Real.exp_pos 1).le (pow_nonneg hη'nn m))
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp 1 * Real.exp 1 * (((m:ℝ) * δ) ^ m * (((v:ℝ) + 1) ^ m *
            Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))))) * Real.exp (-(δ * v)) := by ring
      _ ≤ Real.exp 1 * Real.exp 1 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
          rw [← Real.exp_add]; norm_num
  have hsum : η ^ m * ∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤
      Real.exp 2 * (m.factorial : ℝ) * ∑ v ∈ Ico v0 V, Real.exp (-(δ * v)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun v _ => hterm v)
  have hG : (∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * δ ≤ 1 + δ := by
    have hrw : ∀ v : ℕ, Real.exp (-(δ * v)) = Real.exp (-δ) ^ v := by
      intro v; rw [← Real.exp_nat_mul]; congr 1; ring
    simp only [hrw]
    have hr0 : 0 < Real.exp (-δ) := Real.exp_pos _
    have hsub : ∑ v ∈ Ico v0 V, Real.exp (-δ) ^ v ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_Ico] at hx
        rw [Finset.mem_range]
        exact hx.2
      · intro i _ _
        exact pow_nonneg hr0.le i
    have hG0 : 0 ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v :=
      Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)
    have hgeo : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) ≤ 1 := by
      have h := geom_sum_mul (Real.exp (-δ)) V
      have hV : 0 ≤ Real.exp (-δ) ^ V := pow_nonneg hr0.le V
      have e : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) =
          -((∑ v ∈ range V, Real.exp (-δ) ^ v) * (Real.exp (-δ) - 1)) := by ring
      rw [e, h]; linarith
    have h2 := dhpr_one_sub_exp_neg hδpos
    have h2' : δ ≤ (1 - Real.exp (-δ)) * (1 + δ) := by
      rwa [div_le_iff₀ (by linarith)] at h2
    calc (∑ v ∈ Ico v0 V, Real.exp (-δ) ^ v) * δ
        ≤ (∑ v ∈ range V, Real.exp (-δ) ^ v) * δ := mul_le_mul_of_nonneg_right hsub hδpos.le
      _ ≤ (∑ v ∈ range V, Real.exp (-δ) ^ v) * ((1 - Real.exp (-δ)) * (1 + δ)) :=
          mul_le_mul_of_nonneg_left h2' hG0
      _ = ((∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ))) * (1 + δ) := by ring
      _ ≤ 1 * (1 + δ) := mul_le_mul_of_nonneg_right hgeo (by linarith)
      _ = 1 + δ := one_mul _
  rw [le_div_iff₀ (pow_pos hη (m + 1))]
  calc (∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) * η ^ (m + 1)
      = (η ^ m * ∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) * η := by ring
    _ ≤ (Real.exp 2 * (m.factorial : ℝ) * ∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * η :=
        mul_le_mul_of_nonneg_right hsum hη.le
    _ = Real.exp 2 * (m.factorial : ℝ) * ((∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * δ) *
          ((m:ℝ) + 1) := by rw [← hδη]; ring
    _ ≤ Real.exp 2 * (m.factorial : ℝ) * (1 + δ) * ((m:ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ hm1.le
        exact mul_le_mul_of_nonneg_left hG (by positivity)
    _ = Real.exp 2 * (m.factorial : ℝ) * ((m:ℝ) + 1 + η) := by rw [← hδη]; ring
    _ ≤ Real.exp 2 * (m.factorial : ℝ) * (2 * ((m:ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = 2 * Real.exp 2 * ((m : ℝ) + 1) * (m.factorial : ℝ) := by ring

lemma dhpr_esum (v0 V : ℕ) :
    ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)) ≤
      20 * Real.exp (-((v0 : ℝ) / 4)) := by
  have hr0 : 0 < Real.exp (-(1/4:ℝ)) := Real.exp_pos _
  have hterm : ∀ v : ℕ, ((v:ℝ) + 1) * Real.exp (-((v:ℝ) / 2)) ≤ 4 * Real.exp (-(1/4:ℝ)) ^ v := by
    intro v
    have h1 := Real.add_one_le_exp ((v:ℝ) / 4)
    have hv : (0:ℝ) ≤ v := Nat.cast_nonneg v
    calc ((v:ℝ) + 1) * Real.exp (-((v:ℝ) / 2))
        ≤ (4 * Real.exp ((v:ℝ) / 4)) * Real.exp (-((v:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 4 * (Real.exp ((v:ℝ) / 4) * Real.exp (-((v:ℝ) / 2))) := by ring
      _ = 4 * Real.exp (-(1/4:ℝ)) ^ v := by
          rw [← Real.exp_add, ← Real.exp_nat_mul]
          congr 2
          ring
  have h15 : (1:ℝ) / 5 ≤ 1 - Real.exp (-(1/4:ℝ)) := by
    have h := dhpr_one_sub_exp_neg (show (0:ℝ) < 1/4 by norm_num)
    have e : (1/4:ℝ) / (1 + 1/4) = 1 / 5 := by norm_num
    rw [e] at h
    exact h
  have hgeo : ∑ v ∈ Ico v0 V, Real.exp (-(1/4:ℝ)) ^ v ≤ 5 * Real.exp (-(1/4:ℝ)) ^ v0 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [pow_add]
    rw [← Finset.mul_sum, mul_comm (Real.exp (-(1/4:ℝ)) ^ v0)]
    have hG0 : 0 ≤ ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k :=
      Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)
    have h := geom_sum_mul (Real.exp (-(1/4:ℝ))) (V - v0)
    have hV : 0 ≤ Real.exp (-(1/4:ℝ)) ^ (V - v0) := pow_nonneg hr0.le _
    have hmul := mul_le_mul_of_nonneg_left h15 hG0
    have hle : ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k ≤ 5 := by
      have e : (∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (1 - Real.exp (-(1/4:ℝ))) =
          -((∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (Real.exp (-(1/4:ℝ)) - 1)) := by ring
      rw [h] at e
      linarith
    exact mul_le_mul_of_nonneg_right hle (pow_nonneg hr0.le _)
  calc ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))
      ≤ ∑ v ∈ Ico v0 V, 4 * Real.exp (-(1/4:ℝ)) ^ v := Finset.sum_le_sum (fun v _ => hterm v)
    _ = 4 * ∑ v ∈ Ico v0 V, Real.exp (-(1/4:ℝ)) ^ v := by rw [Finset.mul_sum]
    _ ≤ 4 * (5 * Real.exp (-(1/4:ℝ)) ^ v0) := mul_le_mul_of_nonneg_left hgeo (by norm_num)
    _ = 20 * Real.exp (-((v0 : ℝ) / 4)) := by
        rw [← Real.exp_nat_mul]
        have e : (v0:ℝ) * -(1/4) = -((v0:ℝ) / 4) := by ring
        rw [e]; ring

lemma dhpr_floor_mono {v w : ℕ} (h : v ≤ w) :
    ⌊Real.exp (v : ℝ)⌋₊ ≤ ⌊Real.exp (w : ℝ)⌋₊ :=
  Nat.floor_mono (Real.exp_le_exp.mpr (by exact_mod_cast h))

lemma dhpr_blocks (g : ℕ → ℝ) (v0 : ℕ) : ∀ V, v0 ≤ V →
    ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp (V : ℝ)⌋₊, g n =
      ∑ v ∈ Ico v0 V, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊, g n := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ← ih]
    exact (Finset.sum_Ioc_consecutive g (dhpr_floor_mono hn)
      (dhpr_floor_mono (by omega : n ≤ n + 1))).symm

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TpCoeffNorm
section
open Finset Complex Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

def tp (n : ℕ) (z : Fin n → ℂ) : ℂ[X] := ∏ i, (X - C (z i))

theorem tp_natDeg (n : ℕ) (z : Fin n → ℂ) : (tp n z).natDegree ≤ n := by
  unfold tp
  exact (natDegree_prod_le _ _).trans (by simp [natDegree_X_sub_C])

theorem tp_eval (n : ℕ) (z : Fin n → ℂ) (x : ℂ) : (tp n z).eval x = ∏ i, (x - z i) := by
  simp [tp, eval_prod]

theorem tp_eval_sum (n : ℕ) (z : Fin n → ℂ) (x : ℂ) :
    (tp n z).eval x = ∑ a ∈ range (n + 1), (tp n z).coeff a * x ^ a :=
  eval_eq_sum_range' (Nat.lt_succ_of_le (tp_natDeg n z)) x

theorem tp_coeff_norm (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (a : ℕ) (ha : a ≤ n) :
    ‖(tp n z).coeff a‖ ≤ n.choose a := by
  classical
  set s : Multiset ℂ := Finset.univ.val.map z with hs
  have hcard : Multiset.card s = n := by simp [hs]
  have htp : tp n z = (s.map fun t => X - C t).prod := by
    rw [tp, Finset.prod_eq_multiset_prod, hs, Multiset.map_map]
    rfl
  have hprod : ∀ t : Multiset ℂ, (∀ x ∈ t, ‖x‖ ≤ 1) → ‖t.prod‖ ≤ 1 := by
    intro t
    induction t using Multiset.induction_on with
    | empty => intro _; simp
    | cons x t ih =>
      intro h
      rw [Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (h x (Multiset.mem_cons_self x t)) (norm_nonneg _)
        (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))
  have hmem : ∀ t ∈ s, ‖t‖ ≤ 1 := by
    intro t ht
    rw [hs, Multiset.mem_map] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact hz i
  rw [htp, Multiset.prod_X_sub_C_coeff s (by rw [hcard]; exact ha), hcard, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul, ← Nat.choose_symm ha, Multiset.esymm]
  calc ‖((s.powersetCard (n - a)).map Multiset.prod).sum‖
      ≤ (((s.powersetCard (n - a)).map Multiset.prod).map norm).sum := norm_multiset_sum_le _
    _ = ((s.powersetCard (n - a)).map fun t => ‖t.prod‖).sum := by rw [Multiset.map_map]; rfl
    _ ≤ ((s.powersetCard (n - a)).map fun _ => (1 : ℝ)).sum := by
        refine Multiset.sum_map_le_sum_map _ _ fun t ht => hprod t fun x hx => hmem x ?_
        exact Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hx
    _ = n.choose (n - a) := by simp [Multiset.card_powersetCard, hcard]

theorem tp_sum_norm (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ ≤ 2 ^ n := by
  calc ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ ≤ ∑ a ∈ range (n + 1), (n.choose a : ℝ) :=
        Finset.sum_le_sum fun a ha => tp_coeff_norm n z hz a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
    _ = 2 ^ n := by exact_mod_cast Nat.sum_range_choose n

theorem tp_rev (n : ℕ) (z : Fin n → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0) :
    ∏ i, (1 - z i * ζ) = ∑ a ∈ range (n + 1), (tp n z).coeff a * ζ ^ (n - a) := by
  have h1 : ∏ i, (1 - z i * ζ) = ζ ^ n * (tp n z).eval ζ⁻¹ := by
    rw [tp_eval, ← Fin.prod_const n ζ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_sub, mul_inv_cancel₀ hζ]
    ring
  rw [h1, tp_eval_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [inv_pow, pow_sub₀ _ hζ ha']
  ring

theorem tp_root (n : ℕ) (z : Fin n → ℂ) (i : Fin n) :
    ∑ a ∈ range (n + 1), (tp n z).coeff a * z i ^ a = 0 := by
  rw [← tp_eval_sum, tp_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
end
end

