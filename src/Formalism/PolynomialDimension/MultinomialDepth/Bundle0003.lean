import Mathlib
import Formalism.PolynomialDimension.Bundle0002

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.ParamsI
section
noncomputable section

namespace Formalism.CountingSumsFrames

open Real

namespace ParamsIProof

theorem one_le_log_of_three_le (a : ℝ) (ha : 3 ≤ a) : 1 ≤ Real.log a := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

theorem margin (C Cm N1 k Q c La b' Ib X Nr Y : ℝ)
    (hCm : 1 ≤ Cm) (hC : 1000 * Cm ≤ C) (hN1 : 1 ≤ N1) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hLa : 1 ≤ La) (hIb : 0 ≤ Ib) (hb : 0 < b') (hc0 : 0 ≤ c) (hc : c ≤ 4 * X) (hX : 0 ≤ X)
    (hN : 1 ≤ Nr) (hY : 1 ≤ Y) (hb' : C * k ^ 3 * Nr * Q ^ 4 * X * Y ≤ b') :
    ∀ Ai : ℝ, b' / (2 * Q) ≤ Ai →
      2 * (Cm * k * N1 * Q * c) + 12 * c ≤ (C * N1 * La / k + 2 * Ib / b') * Ai / 4 := by
  intro Ai hAi
  have hQ0 : 0 < Q := by linarith
  have hk0 : 0 < k := by linarith
  have hC1 : 1 ≤ C := by linarith
  have hP : 1 ≤ Cm * k * N1 * Q :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hCm hk) hN1) hQ
  have h1 : 2 * (Cm * k * N1 * Q * c) + 12 * c ≤ 56 * Cm * k * N1 * Q * X := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hP),
      mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ Cm * k * N1 * Q)]
  have hq4 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
  have hq : Q ^ 2 ≤ Nr * Q ^ 4 * Y := by
    have h2 : Q ^ 4 ≤ Nr * Q ^ 4 := le_mul_of_one_le_left (by positivity) hN
    have h3 : Nr * Q ^ 4 ≤ Nr * Q ^ 4 * Y := le_mul_of_one_le_right (by nlinarith) hY
    linarith
  have hCk3 : 0 ≤ C * k ^ 3 := mul_nonneg (by linarith) (by positivity)
  have hb2 : C * k ^ 3 * Q ^ 2 * X ≤ b' := by
    have h4 : C * k ^ 3 * Q ^ 2 * X ≤ C * k ^ 3 * (Nr * Q ^ 4 * Y) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hCk3) hX
    linarith
  have hCLak : 1 ≤ C * La * k :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC1 hLa) hk
  have hW : 0 ≤ N1 * k ^ 2 * Q ^ 2 * X := mul_nonneg (by positivity) hX
  have h2 : 56 * Cm * k * N1 * Q * X * (8 * k * Q) ≤ C * N1 * La * b' := by
    calc 56 * Cm * k * N1 * Q * X * (8 * k * Q) = 448 * Cm * (N1 * k ^ 2 * Q ^ 2 * X) := by ring
      _ ≤ C * (N1 * k ^ 2 * Q ^ 2 * X) := mul_le_mul_of_nonneg_right (by linarith) hW
      _ ≤ (C * La * k) * (C * (N1 * k ^ 2 * Q ^ 2 * X)) :=
          le_mul_of_one_le_left (mul_nonneg (by linarith) hW) hCLak
      _ = C * N1 * La * (C * k ^ 3 * Q ^ 2 * X) := by ring
      _ ≤ C * N1 * La * b' :=
          mul_le_mul_of_nonneg_left hb2 (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  have h3 : 56 * Cm * k * N1 * Q * X ≤ (C * N1 * La / k) * (b' / (2 * Q)) / 4 := by
    rw [show (C * N1 * La / k) * (b' / (2 * Q)) / 4 = (C * N1 * La * b') / (8 * k * Q) by
      field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    exact h2
  have hde0 : 0 ≤ C * N1 * La / k :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) hk0.le
  have hde : C * N1 * La / k ≤ C * N1 * La / k + 2 * Ib / b' :=
    le_add_of_nonneg_right (div_nonneg (by linarith) hb.le)
  have hA0 : 0 ≤ b' / (2 * Q) := div_nonneg hb.le (by linarith)
  have h4 : (C * N1 * La / k) * (b' / (2 * Q)) ≤ (C * N1 * La / k + 2 * Ib / b') * Ai :=
    mul_le_mul hde hAi hA0 (by linarith)
  linarith

theorem share (C k Y M a b' Ib Yb Nr La L : ℝ) (hC : 2 ≤ C) (hk : 2 ≤ k) (hY : 1 ≤ Y)
    (hM0 : 0 ≤ M) (hM : C * k ^ 3 * Y * M ≤ b') (hb : 0 < b') (hYb : 1 ≤ Yb) (hN : 1 ≤ Nr)
    (hLa : 1 ≤ La) (hL : 1 ≤ L) (ha : k * Y ^ 2 * Yb * Nr * La * L ≤ a / b')
    (hIb : Yb * Nr * La * b' / k ≤ Ib) : M * (k * Y / a + 1 / Ib) ≤ 1 / Y := by
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hC0 : 0 < C := by linarith
  have hA : k * Y ^ 2 * Yb * Nr * La * L * b' ≤ a := (le_div_iff₀ hb).mp ha
  have hR : 1 ≤ Y * Yb * Nr * La * L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hY hYb) hN) hLa) hL
  have hR2 : 2 * Y ≤ k * Y ^ 2 * Yb * Nr * La * L := by
    have h1 : 2 * Y ≤ k * Y := by nlinarith
    have h2 : k * Y * 1 ≤ k * Y * (Y * Yb * Nr * La * L) :=
      mul_le_mul_of_nonneg_left hR (by nlinarith)
    linarith
  have ha0 : 0 < a := by nlinarith
  have hCk : 1 ≤ C * k ^ 2 := by nlinarith
  have p1 : M * (k * Y / a) ≤ 1 / (2 * Y) := by
    rw [show M * (k * Y / a) = M * k * Y / a by ring, div_le_div_iff₀ ha0 (by linarith)]
    have e1 : M * k * Y * (2 * Y) * 1 ≤ M * k * Y * (2 * Y) * (C * k ^ 2) :=
      mul_le_mul_of_nonneg_left hCk (by positivity)
    have e2 : C * k ^ 3 * Y * M * (2 * Y) ≤ b' * (2 * Y) := mul_le_mul_of_nonneg_right hM (by linarith)
    have e3 : b' * (2 * Y) ≤ b' * (k * Y ^ 2 * Yb * Nr * La * L) := mul_le_mul_of_nonneg_left hR2 hb.le
    linarith
  have hIb' : Yb * Nr * La * b' ≤ Ib * k := (div_le_iff₀ hk0).mp hIb
  have hYNL : 1 ≤ Yb * Nr * La :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hYb hN) hLa
  have e2 : b' ≤ Yb * Nr * La * b' := le_mul_of_one_le_left hb.le hYNL
  have hIb0 : 0 < Ib := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have p2 : M * (1 / Ib) ≤ 1 / (2 * Y) := by
    rw [show M * (1 / Ib) = M / Ib by ring, div_le_div_iff₀ hIb0 (by linarith)]
    have hCk3 : 0 < C * k ^ 3 := by positivity
    apply le_of_mul_le_mul_right _ hCk3
    have e1 : 2 * b' ≤ C * k ^ 2 * b' := mul_le_mul_of_nonneg_right (by nlinarith) hb.le
    have e3 : C * k ^ 2 * b' ≤ C * k ^ 2 * (Yb * Nr * La * b') := mul_le_mul_of_nonneg_left e2 (by positivity)
    have e4 : C * k ^ 2 * (Yb * Nr * La * b') ≤ C * k ^ 2 * (Ib * k) := mul_le_mul_of_nonneg_left hIb' (by positivity)
    linarith
  have e : 1 / (2 * Y) + 1 / (2 * Y) = 1 / Y := by field_simp; ring
  rw [mul_add]
  linarith

theorem cnkc (C Ck k Y Nr cl b' : ℝ) (hCk : 1 ≤ Ck) (hC : 1000 * Ck ≤ C) (hk : 1 ≤ k) (hY : 1 ≤ Y)
    (hN : 0 ≤ Nr) (hcl : 0 ≤ cl) (hb : 0 < b') (hM : C * k ^ 3 * Y * (Nr * cl) ≤ b') :
    Ck * Nr * k * (2 * cl) / b' ≤ 1 / Y := by
  rw [div_le_div_iff₀ hb (by linarith)]
  have hk3 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have h1 : 2 * Ck * k ≤ C * k ^ 3 := by nlinarith
  have h2 : 2 * Ck * k * (Y * (Nr * cl)) ≤ C * k ^ 3 * (Y * (Nr * cl)) :=
    mul_le_mul_of_nonneg_right h1 (mul_nonneg (by linarith) (mul_nonneg hN hcl))
  linarith

theorem sumP (k Y Yb Nr La L a b' : ℝ) (hk : 1 ≤ k) (hY : 1 ≤ Y) (hYb : 1 ≤ Yb) (hN : 1 ≤ Nr)
    (hLa : 0 ≤ La) (hL : 1 ≤ L) (hb : 0 < b') (ha0 : 0 < a)
    (ha : k * Y ^ 2 * Yb * Nr * La * L ≤ a / b')
    (hexp : Real.exp (-La / 3) ≤ 1 / a) (hYbNa : Yb * Nr ≤ a) :
    ∀ al : ℝ, a ≤ al →
      1 - 2 / (Yb * Nr) ≤ (1 - (k - 1) * (La * b' / k) / al) * (1 - Real.exp (-La / 3)) := by
  intro al hal
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hYb0 : 0 < Yb := by linarith
  have hN0 : 0 < Nr := by linarith
  have hal0 : 0 < al := by linarith
  have hA : k * Y ^ 2 * Yb * Nr * La * L * b' ≤ a := (le_div_iff₀ hb).mp ha
  have hJ0 : 0 ≤ La * b' / k := by positivity
  have hx0 : 0 ≤ (k - 1) * (La * b' / k) / al :=
    div_nonneg (mul_nonneg (by linarith) hJ0) hal0.le
  have hx : (k - 1) * (La * b' / k) / al ≤ 1 / (Yb * Nr) := by
    rw [div_le_div_iff₀ hal0 (by positivity)]
    have e0 : k * (La * b' / k) = La * b' := by field_simp
    have e1 : (k - 1) * (La * b' / k) ≤ La * b' := by linarith
    have e2 : (k - 1) * (La * b' / k) * (Yb * Nr) ≤ La * b' * (Yb * Nr) :=
      mul_le_mul_of_nonneg_right e1 (by positivity)
    have h1 : 1 ≤ k * Y ^ 2 * L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk (one_le_pow₀ hY)) hL
    have e3 : La * b' * (Yb * Nr) ≤ La * b' * (Yb * Nr) * (k * Y ^ 2 * L) :=
      le_mul_of_one_le_right (by positivity) h1
    linarith
  have hy0 : 0 ≤ Real.exp (-La / 3) := (Real.exp_pos _).le
  have hy : Real.exp (-La / 3) ≤ 1 / (Yb * Nr) :=
    le_trans hexp (one_div_le_one_div_of_le (by positivity) hYbNa)
  have e : 2 / (Yb * Nr) = 2 * (1 / (Yb * Nr)) := by ring
  nlinarith [mul_nonneg hx0 hy0]

theorem half (Yb : ℝ) (N : ℕ) (hYb : 4 ≤ Yb) (hN : 1 ≤ N) :
    1 / 2 ≤ (1 - 2 / (Yb * N)) ^ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hYb0 : 0 < Yb := by linarith
  have h2 : 2 / (Yb * N) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have key := one_add_mul_le_pow (a := -(2 / (Yb * N))) (by linarith) N
  have e1 : (N : ℝ) * (-(2 / (Yb * N))) = -(2 / Yb) := by field_simp
  have e2 : 2 / Yb ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hYb0 (by norm_num)]
    linarith
  rw [show (1 : ℝ) - 2 / (Yb * N) = 1 + -(2 / (Yb * N)) by ring]
  linarith

end ParamsIProof

end Formalism.CountingSumsFrames
end
end

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.SecondParameterSlackBoundsHolds
section
noncomputable section

namespace Formalism.CountingSumsFrames

open Real

lemma slack_ge_half {Y B : ℝ} {k : ℕ} (hM : 0 < Y * (k : ℝ) ^ 2) (hB : 2 * (Y * (k : ℝ) ^ 2) ≤ B) :
    B / (Y * (k : ℝ) ^ 2) / 2 ≤ slII Y k B := by
  unfold slII
  have h1 := Int.sub_one_lt_floor (B / (Y * (k : ℝ) ^ 2))
  have h2 : 2 ≤ B / (Y * (k : ℝ) ^ 2) := by rw [le_div_iff₀ hM]; linarith
  linarith

lemma slackBound_coeff {M P B c : ℝ} (hM : 0 < M) (hc : 0 < c) (hB : 0 ≤ B) (hP : 16 * c * M ≤ P) :
    c * P⁻¹ * B ≤ B / M / 2 / 8 := by
  have hP0 : 0 < 16 * c * M := by positivity
  have hc' : c ≠ 0 := hc.ne'
  have hM' : M ≠ 0 := hM.ne'
  have hcB : 0 ≤ c * B := by positivity
  calc c * P⁻¹ * B = (c * B) / P := by ring
    _ ≤ (c * B) / (16 * c * M) := div_le_div_of_nonneg_left hcB hP0 hP
    _ = B / M / 2 / 8 := by field_simp; ring

theorem secondParameterSlackBounds_holds : ParamsII5 := by
  intro CE C₂ _ _
  refine ⟨100, by norm_num, ?_⟩
  intro p r N N₁ Nₛ J k n' L₁ G' Y a c₀ c'' D cStar h
  obtain ⟨hp, hr, hrN1, hN1sq, hrY, hk1, hk2, hL, hD, hcS, ha, hL1, hL1G, hNs1, hNs2, hJ, hJr⟩ := h
  have hN2 : 2 ≤ N := by
    calc 2 ≤ r := hr
      _ = 1 * r := (one_mul _).symm
      _ ≤ J * r := Nat.mul_le_mul_right _ hJ
      _ ≤ N := hJr
  have hrk : r ≤ k := by omega
  have hk8 : 8 ≤ k := by omega
  have hpR : (13 : ℝ) ≤ p := by exact_mod_cast hp
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hrkR : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hkR : (8 : ℝ) ≤ k := by exact_mod_cast hk8
  have hN1rkR : (N₁ : ℝ) + r ≤ k := by exact_mod_cast (by omega : N₁ + r ≤ k)
  have hJrR : (J : ℝ) * r ≤ N := by exact_mod_cast hJr
  have hcSR : 8 * ((D : ℝ) + 1) ≤ cStar := by exact_mod_cast hcS
  have hD0 : (0 : ℝ) ≤ D := by positivity
  have hc00 : (0 : ℝ) ≤ c₀ := by positivity
  have hY : (2 : ℝ) ≤ Y := le_trans hrR hrY
  have hY0 : 0 < Y := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q, QII p G' = Q := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', cPrII r N n' c₀ c'' cStar = c' := ⟨_, rfl⟩
  rw [hQ, hc'] at ha
  rw [hQ, hc']
  have hQp : (p : ℝ) ≤ Q := by
    rw [← hQ, QII]
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ G' := pow_le_pow_right₀ hp1.le (by omega)
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hc'ge : (cStar : ℝ) + r * N * c₀ ≤ c' := by
    rw [← hc', cPrII, omII]
    have : (0 : ℝ) ≤ 2 * r * n' * c'' := by positivity
    linarith
  have hrNc : (0 : ℝ) ≤ r * N * c₀ := by positivity
  have hc0c : (c₀ : ℝ) ≤ c' := by
    have h1 : (1 : ℝ) ≤ r * N := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have h2 : (c₀ : ℝ) ≤ r * N * c₀ := le_mul_of_one_le_left hc00 h1
    linarith
  have hc'8 : (8 : ℝ) ≤ c' := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hM : 0 < Y * (k : ℝ) ^ 2 := by positivity
  have hM1 : (1 : ℝ) ≤ Y * (k : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))
  have hbig : 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) ≤ a := by
    have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 * N * Q ^ 3 := by
      have e1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ (by linarith)
      have e2 : (1 : ℝ) ≤ Q ^ 3 := one_le_pow₀ hQ1
      have e3 : (1 : ℝ) ≤ N := by linarith
      have e4 : (1 : ℝ) ≤ (r : ℝ) ^ 2 * N := one_le_mul_of_one_le_of_one_le e1 e3
      exact one_le_mul_of_one_le_of_one_le e4 e2
    have h2 : (0 : ℝ) ≤ 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) := by positivity
    calc 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2)
        ≤ 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) * ((r : ℝ) ^ 2 * N * Q ^ 3) :=
          le_mul_of_one_le_right h2 h1
      _ = 100 * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * Q ^ 5 * c' * Y := by ring
      _ ≤ a := ha
  have hkc : (1 : ℝ) ≤ k * c' := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hQQ : (1 : ℝ) ≤ Q ^ 2 := one_le_pow₀ hQ1
  have h2M : 2 * (Y * (k : ℝ) ^ 2) * (Q * Q) ≤ a := by
    calc 2 * (Y * (k : ℝ) ^ 2) * (Q * Q) ≤ 2 * (Y * (k : ℝ) ^ 2) * (Q * Q) * (50 * (k * c')) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
      _ = 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) := by ring
      _ ≤ a := hbig
  have hpa : (p : ℝ) ≤ a := by
    have e1 : Q ≤ Q * Q := le_mul_of_one_le_right hQ0.le hQ1
    have e2 : Q * Q ≤ 2 * (Y * (k : ℝ) ^ 2) * (Q * Q) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    linarith
  have ha0 : 0 < a := by linarith
  have hka : (k : ℝ) ≤ a := by
    have e1 : (1 : ℝ) ≤ c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hQQ) hM1
    calc (k : ℝ) ≤ k * (100 * (c' * Q ^ 2 * (Y * (k : ℝ) ^ 2))) :=
          le_mul_of_one_le_right hk0.le (by linarith)
      _ = 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) := by ring
      _ ≤ a := hbig
  have hPa : (p : ℝ) ^ (L₁ - 1) ≤ (p : ℝ) ^ L₁ := pow_le_pow_right₀ hp1.le (by omega)
  have hPb : (p : ℝ) ^ (L₁ - 1) ≤ (p : ℝ) ^ (L₁ + 1) := pow_le_pow_right₀ hp1.le (by omega)
  have h48 : 16 * 3 * (Y * (k : ℝ) ^ 2) ≤ (p : ℝ) ^ L₁ := by
    have e : (1 : ℝ) ≤ N * Y := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have e1 : Y * (k : ℝ) ^ 2 ≤ Y * (k : ℝ) ^ 2 * (N * Y) := le_mul_of_one_le_right hM.le e
    have e2 : 256 * (k : ℝ) ^ 2 * N * Y ^ 2 = 256 * (Y * (k : ℝ) ^ 2 * (N * Y)) := by ring
    linarith
  have h48r : 16 * (3 * r) * (Y * (k : ℝ) ^ 2) ≤ (p : ℝ) ^ (L₁ + 1) := by
    have e1 : (r : ℝ) * (Y * (k : ℝ) ^ 2) ≤ Y * (Y * (k : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hrY hM.le
    have e0 : 0 ≤ Y * (Y * (k : ℝ) ^ 2) := by positivity
    have e2 : Y * (Y * (k : ℝ) ^ 2) ≤ Y * (Y * (k : ℝ) ^ 2) * N :=
      le_mul_of_one_le_right e0 (by linarith)
    have e3 : 256 * (k : ℝ) ^ 2 * N * Y ^ 2 = 256 * (Y * (Y * (k : ℝ) ^ 2) * N) := by ring
    linarith
  have hdivX : ∀ X : ℝ, 0 < X → X ≤ Q * Q → 2 * (Y * (k : ℝ) ^ 2) ≤ a / X := by
    intro X hX0 hXQ
    rw [le_div_iff₀ hX0]
    have : 2 * (Y * (k : ℝ) ^ 2) * X ≤ 2 * (Y * (k : ℝ) ^ 2) * (Q * Q) :=
      mul_le_mul_of_nonneg_left hXQ (by positivity)
    linarith
  have hQQQ : Q ≤ Q * Q := le_mul_of_one_le_right hQ0.le hQ1
  have h24 : 24 * k * c' ≤ a / Q / (Y * (k : ℝ) ^ 2) / 2 := by
    rw [div_div, div_div, le_div_iff₀ (by positivity)]
    have e0 : (0 : ℝ) ≤ 24 * k * c' * (Q * (Y * (k : ℝ) ^ 2) * 2) := by positivity
    have e1 := le_mul_of_one_le_right e0 hQ1
    have e2 : 24 * k * c' * (Q * (Y * (k : ℝ) ^ 2) * 2) * Q
        = 48 * (k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2)) := by ring
    have e3 : (0 : ℝ) ≤ k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) := by positivity
    have e4 : 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2)
        = 100 * (k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2)) := by ring
    linarith
  have hslQ : ∀ B : ℝ, a / Q ≤ B → 24 * k * c' ≤ slII Y k B := by
    intro B hB
    have e1 := slack_ge_half hM (le_trans (hdivX Q hQ0 hQQQ) hB)
    have e2 : a / Q / (Y * (k : ℝ) ^ 2) / 2 ≤ B / (Y * (k : ℝ) ^ 2) / 2 := by gcongr
    linarith
  obtain ⟨lA, hlA⟩ : ∃ x, Real.logb p a = x := ⟨_, rfl⟩
  rw [hlA] at hD
  have hlA1 : 1 ≤ lA := by
    rw [← hlA, ← Real.logb_self_eq_one hp1]
    exact Real.logb_le_logb_of_le hp1 (by linarith) hpa
  obtain ⟨lg, hlg⟩ : ∃ x, lgII p a k = x := ⟨_, rfl⟩
  have hlg0 : 0 ≤ lg := by
    rw [← hlg, lgII]
    have : 0 ≤ Real.logb p (2 * a + k) := Real.logb_nonneg hp1 (by linarith)
    linarith
  have hlg3 : lg ≤ 3 * lA := by
    rw [← hlg, lgII]
    have e1 : Real.logb p (2 * a + k) ≤ Real.logb p (p * a) := by
      apply Real.logb_le_logb_of_le hp1 (by linarith)
      have : 13 * a ≤ p * a := mul_le_mul_of_nonneg_right hpR ha0.le
      linarith
    have e2 : Real.logb p (p * a) = 1 + lA := by
      rw [Real.logb_mul (by linarith) ha0.ne', Real.logb_self_eq_one hp1, hlA]
    linarith
  have hNk0 : (0 : ℝ) ≤ N * (k : ℝ) ^ 2 := by positivity
  have hD1 : degreeLoss p a k N r J ≤ 15 * (N * (k : ℝ) ^ 2 * lA) := by
    have e : degreeLoss p a k N r J
        = lg * (N * (k : ℝ) ^ 2 + 2 * (N * (r : ℝ) ^ 2) + J * r * (r : ℝ) ^ 2 + N * (2 * k)) := by
      rw [degreeLoss, hlg]; ring
    have f1 : (r : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hrkR 2
    have f2 : (N : ℝ) * (r : ℝ) ^ 2 ≤ N * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left f1 (by linarith)
    have f3 : (J : ℝ) * r * (r : ℝ) ^ 2 ≤ N * (k : ℝ) ^ 2 :=
      mul_le_mul hJrR f1 (by positivity) (by linarith)
    have f4 : (2 : ℝ) * k ≤ (k : ℝ) ^ 2 := by
      rw [pow_two]; exact mul_le_mul_of_nonneg_right (by linarith) hk0.le
    have f5 : (N : ℝ) * (2 * k) ≤ N * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left f4 (by linarith)
    have f6 : lg * (N * (k : ℝ) ^ 2 + 2 * (N * (r : ℝ) ^ 2) + J * r * (r : ℝ) ^ 2 + N * (2 * k))
        ≤ lg * (5 * (N * (k : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left (by linarith) hlg0
    have f7 : lg * (5 * (N * (k : ℝ) ^ 2)) ≤ 3 * lA * (5 * (N * (k : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hlg3 (by positivity)
    rw [e]
    calc _ ≤ _ := f6
      _ ≤ _ := f7
      _ = 15 * (N * (k : ℝ) ^ 2 * lA) := by ring
  have hk1' : kappaSecondRegime p a k N ≤ 3 * (N * (k : ℝ) ^ 2 * lA) := by
    rw [kappaSecondRegime, hlg]
    calc (N : ℝ) * (k : ℝ) ^ 2 * lg ≤ N * (k : ℝ) ^ 2 * (3 * lA) := mul_le_mul_of_nonneg_left hlg3 hNk0
      _ = 3 * (N * (k : ℝ) ^ 2 * lA) := by ring
  have hXl : 0 ≤ N * (k : ℝ) ^ 2 * lA := mul_nonneg hNk0 (by linarith)
  have hD' : 100 * (N * (k : ℝ) ^ 2 * lA) ≤ D := by
    have e : 100 * (N * (k : ℝ) ^ 2 * lA) = 100 * N * (k : ℝ) ^ 2 * lA := by ring
    rw [e]; exact hD
  have hkap0 : 0 ≤ kappaSecondRegime p a k N := by
    rw [kappaSecondRegime, hlg]; exact mul_nonneg hNk0 hlg0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q' B dw hQ'1 hQ'Q hdw hB
    have hz : (p : ℝ) ^ (-(L₁ : ℤ)) = ((p : ℝ) ^ L₁)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [hz]
    have hPL : 0 < (p : ℝ) ^ L₁ := by positivity
    have hPL1 : 1 ≤ (p : ℝ) ^ L₁ := one_le_pow₀ hp1.le
    have hQ'0 : 0 < Q' := by linarith
    have haQ' : 2 * (Y * (k : ℝ) ^ 2) ≤ a / Q' := hdivX Q' hQ'0 (le_trans hQ'Q hQQQ)
    have haQ'0 : 0 ≤ a / Q' := by positivity
    have hB1 : a / Q' ≤ B := by
      have e1 : a / Q' ≤ (p : ℝ) ^ L₁ * (a / Q') := le_mul_of_one_le_left haQ'0 hPL1
      have e2 : (p : ℝ) ^ L₁ * a / Q' = (p : ℝ) ^ L₁ * (a / Q') := mul_div_assoc _ _ _
      linarith
    constructor
    · calc dw ≤ 3 * a / Q' := hdw
        _ = 3 * ((p : ℝ) ^ L₁)⁻¹ * ((p : ℝ) ^ L₁ * a / Q') := by field_simp
        _ ≤ 3 * ((p : ℝ) ^ L₁)⁻¹ * B := mul_le_mul_of_nonneg_left hB (by positivity)
    · have e1 := slack_ge_half hM (le_trans haQ' hB1)
      have e2 := slackBound_coeff (c := 3) (B := B) hM (by norm_num) (by linarith) h48
      linarith
  · intro Dd Qj dj B hDd hQj1 hQjQ hdj hB
    have hz1 : (p : ℝ) ^ (-(L₁ : ℤ) - 1) = ((p : ℝ) ^ (L₁ + 1))⁻¹ := by
      rw [show -(L₁ : ℤ) - 1 = -((L₁ + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    have hz2 : (p : ℝ) ^ (-(Dd : ℤ) - L₁ - 1) = ((p : ℝ) ^ Dd * (p : ℝ) ^ (L₁ + 1))⁻¹ := by
      rw [show -(Dd : ℤ) - L₁ - 1 = -((Dd + (L₁ + 1) : ℕ) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast, pow_add]
    rw [hz2] at hdj
    rw [hz1]
    have hPD : 0 < (p : ℝ) ^ Dd := by positivity
    have hP1 : 0 < (p : ℝ) ^ (L₁ + 1) := by positivity
    have hQj0 : 0 < Qj := by linarith
    have hX : (p : ℝ) ^ Dd * Qj ≤ Q * Q := mul_le_mul hDd hQjQ hQj0.le hQ0.le
    have haX : 2 * (Y * (k : ℝ) ^ 2) ≤ a / ((p : ℝ) ^ Dd * Qj) := hdivX _ (by positivity) hX
    have hr0 : (0 : ℝ) < r := by linarith
    constructor
    · calc (r : ℝ) * dj / Qj ≤ r * (3 * a * ((p : ℝ) ^ Dd * (p : ℝ) ^ (L₁ + 1))⁻¹) / Qj :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdj hr0.le) hQj0.le
        _ = 3 * r * ((p : ℝ) ^ (L₁ + 1))⁻¹ * (a / ((p : ℝ) ^ Dd * Qj)) := by field_simp
        _ ≤ 3 * r * ((p : ℝ) ^ (L₁ + 1))⁻¹ * B := mul_le_mul_of_nonneg_left hB (by positivity)
    · have e1 := slack_ge_half hM (le_trans haX hB)
      have e2 := slackBound_coeff (c := 3 * r) (B := B) hM (by positivity) (by linarith) h48r
      linarith
  · linarith
  · intro B ms hB
    have e1 := hslQ B hB
    have e2 : 2 * c' ≤ k * c' := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  · intro B hB
    have e1 := hslQ B hB
    have e2 : ((N₁ : ℝ) + r) * c₀ ≤ k * c' := mul_le_mul hN1rkR hc0c hc00 hk0.le
    linarith
  · linarith
  · linarith

end Formalism.CountingSumsFrames
end
end

