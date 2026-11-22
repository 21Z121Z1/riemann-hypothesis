import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0021
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0015
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTZSum

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiC
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction

theorem main_lower {θ β η l X : ℝ} (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hX : 16 ≤ X)
    (hl : l ≤ Real.log X) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : θ ≤ 0 ∨ η ≤ (1 - β) * l) :
    X * η / (2 * Real.log X) ≤ liX X - θ * liX (X ^ β) := by
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < Real.log X := Real.log_pos (by linarith)
  have h2 : 2 ≤ X ^ β := by
    calc (2 : ℝ) ≤ 4 := by norm_num
      _ = √16 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ √X := Real.sqrt_le_sqrt hX
      _ = X ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow X
      _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ
  have hXβ : X ^ β ≤ X := by
    calc X ^ β ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ1
      _ = X := Real.rpow_one X
  have hli := liX_nonneg h2
  rcases hη with h | h
  · have h1 := liX_lower (by linarith : 4 ≤ X)
    have h3 : X * η / (2 * Real.log X) ≤ X / (2 * Real.log X) := by
      gcongr
      nlinarith
    nlinarith
  · have h1 := liX_sub_ge h2 hXβ
    have hθ1 : θ ≤ 1 := (abs_le.1 hθ).2
    have h3 : liX X - liX (X ^ β) ≤ liX X - θ * liX (X ^ β) := by nlinarith
    have hw : η ≤ (1 - β) * Real.log X := h.trans (mul_le_mul_of_nonneg_left hl (by linarith))
    have he : X ^ β = X * Real.exp (-((1 - β) * Real.log X)) := by
      rw [Real.rpow_def_of_pos hX0]
      nth_rw 2 [← Real.exp_log hX0]
      rw [← Real.exp_add]
      congr 1
      ring
    have he2 : Real.exp (-((1 - β) * Real.log X)) ≤ 1 - η / 2 :=
      (Real.exp_le_exp.2 (by linarith)).trans (exp_neg_le_one_sub_half hη0 hη1)
    have h4 : X * η / 2 ≤ X - X ^ β := by
      rw [he]
      nlinarith
    have h5 : X * η / (2 * Real.log X) ≤ (X - X ^ β) / Real.log X := by
      rw [show X * η / (2 * Real.log X) = (X * η / 2) / Real.log X by field_simp]
      gcongr
    linarith

theorem exp_sum_le_min_exponent {c l L u : ℝ} (hc : 0 < c) (hl : 0 < l) (hL : 0 ≤ L) (hu : L / 2 ≤ u) :
    Real.exp (-(c * u / l)) + Real.exp (-(c * Real.sqrt u)) ≤
      Real.exp (-(min (c / 2) (c ^ 2 / 2) * L / l)) + Real.exp (-Real.sqrt (min (c / 2) (c ^ 2 / 2) * L)) := by
  have hu0 : 0 ≤ u := by linarith
  have hm1 : min (c / 2) (c ^ 2 / 2) ≤ c / 2 := min_le_left _ _
  have hm2 : min (c / 2) (c ^ 2 / 2) ≤ c ^ 2 / 2 := min_le_right _ _
  have hm0 : 0 ≤ min (c / 2) (c ^ 2 / 2) := le_min (by positivity) (by positivity)
  apply add_le_add
  · apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    apply div_le_div_of_nonneg_right _ hl.le
    have h1 := mul_le_mul_of_nonneg_right hm1 hL
    nlinarith
  · apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    rw [show c * Real.sqrt u = Real.sqrt (c ^ 2 * u) by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]]
    apply Real.sqrt_le_sqrt
    have h1 := mul_le_mul_of_nonneg_right hm2 hL
    nlinarith

theorem small_terms {c₃ c₁ L l η φ : ℝ} (hc₃ : 0 ≤ c₃) (hc₁ : 0 < c₁) (hL : 16 * l ≤ L) (hL1 : 1 ≤ L)
    (hη : c₁ * Real.exp (-l) ≤ η) (hφ0 : 0 < φ) (hφ : φ ≤ Real.exp l) :
    44 * Real.exp (L / 2) * L ≤
      5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) * (Real.exp L * η / (2 * L) / φ) := by
  have hL0 : 0 < L := by linarith
  have hsq : Real.sqrt (c₃ * L) ≤ 2 * c₃ + L / 8 := by
    calc Real.sqrt (c₃ * L) ≤ Real.sqrt ((2 * c₃ + L / 8) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (2 * c₃ - L / 8)])
      _ = 2 * c₃ + L / 8 := Real.sqrt_sq (by positivity)
  have hexpL : L ^ 2 ≤ 64 * Real.exp (L / 4) := by
    have h := Real.quadratic_le_exp_of_nonneg (x := L / 4) (by positivity)
    nlinarith
  have hsplit : Real.exp (3 * L / 4) = Real.exp (L / 2) * Real.exp (L / 4) := by
    rw [← Real.exp_add]
    ring_nf
  have key : 2816 * Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) / L =
      5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) *
        (Real.exp L * (c₁ * Real.exp (-l)) / (2 * L) / Real.exp l) := by
    have e : Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) =
        Real.exp (2 * c₃) * Real.exp (-Real.sqrt (c₃ * L)) * Real.exp L * Real.exp (-l) / Real.exp l := by
      rw [show 2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l = 2 * c₃ + -Real.sqrt (c₃ * L) + L + -l - l by ring,
        Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_add]
    rw [e]
    field_simp
    ring
  calc 44 * Real.exp (L / 2) * L ≤ 2816 * Real.exp (3 * L / 4) / L := by
        rw [le_div_iff₀ hL0, hsplit]
        have hp := Real.exp_pos (L / 2)
        nlinarith
    _ ≤ 2816 * Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) / L := by
        apply div_le_div_of_nonneg_right _ hL0.le
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        linarith
    _ = 5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) *
        (Real.exp L * (c₁ * Real.exp (-l)) / (2 * L) / Real.exp l) := key
    _ ≤ 5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) * (Real.exp L * η / (2 * L) / φ) := by
        gcongr
        exact div_nonneg (mul_nonneg (Real.exp_pos L).le (le_trans (mul_pos hc₁ (Real.exp_pos _)).le hη)) (by positivity)

theorem pi_core (M : ℕ) [NeZero M] (h8 : 8 ∣ M) (b : ℕ) (hb : b.Coprime M)
    (e : Option (DirichletCharacter ℂ M × ℝ)) {θ β η c A c₁ X : ℝ}
    (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1)
    (hmain : ∀ t : ℝ, 0 ≤ t → ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi e χ t =
      ((t - θ * t ^ β / β : ℝ) : ℂ))
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : θ ≤ 0 ∨ η ≤ (1 - β) * Real.log M) (hc₁ : 0 < c₁)
    (hηl : c₁ * (M : ℝ) ^ (-1 : ℝ) ≤ η) (hc : 0 < c) (hA : 0 ≤ A) (hX : 0 < X)
    (hL : 16 * Real.log M ≤ Real.log X)
    (hP : ∀ y : ℝ, √X ≤ y → y ≤ X → ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi e χ y‖ ≤
      A * y * η * (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y))))) :
    |(piAP X M b : ℝ) - (liX X - θ * liX (X ^ β)) / (M.totient : ℝ)| ≤
      (10 * A + 5632 * Real.exp (2 * min (c / 2) (c ^ 2 / 2)) / c₁) *
        (Real.exp (-(min (c / 2) (c ^ 2 / 2) * Real.log X / Real.log M)) +
          Real.exp (-Real.sqrt (min (c / 2) (c ^ 2 / 2) * Real.log X))) *
        ((liX X - θ * liX (X ^ β)) / (M.totient : ℝ)) := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hMpos h8
  have hM0 : (0 : ℝ) < M := by linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl : 2 ≤ Real.log M := by
    have h88 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hM8
    linarith
  have hX16 : 16 ≤ X := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    rw [← Real.log_le_log_iff (by norm_num) hX]
    linarith
  have hφ1 : (1 : ℝ) ≤ M.totient := by exact_mod_cast Nat.totient_pos.2 hMpos
  have hφM : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hφ0 : (0 : ℝ) < M.totient := by linarith
  set l := Real.log M with hldef
  set L := Real.log X with hLdef
  set φ : ℝ := (M.totient : ℝ) with hφdef
  set c₃ := min (c / 2) (c ^ 2 / 2) with hc₃def
  have hc₃ : 0 ≤ c₃ := le_min (by positivity) (by positivity)
  set E := Real.exp (-(c₃ * L / l)) + Real.exp (-Real.sqrt (c₃ * L)) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hL32 : 32 ≤ L := by linarith
  have hs0 : 0 ≤ √X := Real.sqrt_nonneg X
  have hcore := abel_core (cAP M b) (vonMangoldtAP_nonneg M b) (vonMangoldtAP_le M b) (K := 1 / φ) (θ := θ) (β := β)
    (D := A * η * E / φ) (X := X) (by positivity) (by rw [div_le_one hφ0]; exact hφ1) hθ hβ hβ1 hX16
    (by positivity) (by
      intro t h1 h2
      have hs4 : 0 < √X := Real.sqrt_pos.2 hX
      have ht0 : 0 < t := by linarith
      have hu : L / 2 ≤ Real.log t := by
        rw [hLdef, ← Real.log_sqrt hX.le]
        exact Real.log_le_log hs4 h1
      rw [sum_cAP]
      calc |psiAP M b t - Fm (1 / φ) θ β t|
          ≤ (∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖) / φ :=
            abs_psiAP_sub_le M b hb e θ β t (hmain t ht0.le)
        _ ≤ (A * t * η * E) / φ := by
            gcongr
            refine (hP t h1 h2).trans ?_
            gcongr
            exact exp_sum_le_min_exponent hc (by linarith) (by linarith) hu
        _ = A * η * E / φ * t := by ring)
  have hpp := abs_piAP_sub_le M b (by linarith : 1 ≤ X)
  have hm := main_lower hθ hβ hβ1 hX16 (by linarith : l ≤ L) hη0 hη1 hη
  have hexpl : Real.exp l = M := Real.exp_log hM0
  have hst := small_terms (c₃ := c₃) (c₁ := c₁) (L := L) (l := l) (η := η) (φ := φ) hc₃ hc₁ hL (by linarith)
    (by
      have : (M : ℝ) ^ (-1 : ℝ) = Real.exp (-l) := by
        rw [Real.rpow_def_of_pos hM0]; congr 1; ring
      rw [← this]; exact hηl) hφ0 (by rw [hexpl]; exact hφM)
  rw [Real.exp_half, Real.exp_log hX] at hst
  set m := liX X - θ * liX (X ^ β) with hmdef
  set P := X * η / (2 * L) / φ with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hPm : P ≤ m / φ := by
    rw [hPdef]
    gcongr
  have hKm : 1 / φ * m = m / φ := by ring
  rw [hKm] at hcore
  have h5 : 5 * (A * η * E / φ) * X / L = 10 * A * E * P := by
    rw [hPdef]
    field_simp
    ring
  rw [h5] at hcore
  have h40 : 40 * √X ≤ 40 * √X * L := by nlinarith
  have hEs : Real.exp (-Real.sqrt (c₃ * L)) ≤ E := by
    rw [hEdef]
    have := Real.exp_pos (-(c₃ * L / l))
    linarith
  have hA2 : 0 ≤ 5632 * Real.exp (2 * c₃) / c₁ := by positivity
  have hst2 : 44 * √X * L ≤ 5632 * Real.exp (2 * c₃) / c₁ * E * P :=
    hst.trans (by gcongr)
  have htot : |(piAP X M b : ℝ) - m / φ| ≤ (10 * A + 5632 * Real.exp (2 * c₃) / c₁) * E * P := by
    have hexp : (10 * A + 5632 * Real.exp (2 * c₃) / c₁) * E * P =
        10 * A * E * P + 5632 * Real.exp (2 * c₃) / c₁ * E * P := by ring
    have h44 : 44 * √X * L = 4 * √X * L + 40 * √X * L := by ring
    rw [hexp]
    rw [abs_le] at hcore hpp ⊢
    constructor <;> linarith [hcore.1, hcore.2, hpp.1, hpp.2]
  exact htot.trans (by gcongr)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTZSumL
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem pow_absorb (N : ℕ) (c l large₂ : ℝ) (hc : 0 < c) (hl : 2 ≤ l)
    (hL : 2 * N / c * l * Real.log (l + 2) ≤ large₂) :
    l ^ N * Real.exp (-(c / 2 * large₂ / l)) ≤ 1 := by
  have hl0 : 0 < l := by linarith
  have hpow : Real.exp (N * Real.log l) = l ^ N := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hl0 N)]
  have key : (N : ℝ) * Real.log l ≤ c / 2 * large₂ / l := by
    rw [le_div_iff₀ hl0]
    have hlog : Real.log l ≤ Real.log (l + 2) := Real.log_le_log hl0 (by linarith)
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc (N : ℝ) * Real.log l * l ≤ N * Real.log (l + 2) * l := by gcongr
      _ = c / 2 * (2 * N / c * l * Real.log (l + 2)) := by field_simp
      _ ≤ c / 2 * large₂ := by gcongr
  calc l ^ N * Real.exp (-(c / 2 * large₂ / l))
      = Real.exp (N * Real.log l + -(c / 2 * large₂ / l)) := by rw [Real.exp_add, hpow]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem zero_sum_bound_lossy : ZeroSumOfB := by
  intro hLD hDH
  obtain ⟨a, B, C, ha, hB, hC, hdens⟩ := density_norm hLD
  obtain ⟨c₀, c₁, c₂, N, hc₀, hc₁, hc₂, hdh⟩ := hDH
  refine ⟨min c₀ (1 / 20), lt_min hc₀ (by norm_num), min_le_right _ _, ?_⟩
  intro C₁ A₁ hA₁
  have hk : 0 < A₁ + 2 := by linarith
  have hcZ := cZ_pos
  have hcZ' := cZ_le
  set η0 : ℝ := min (cZ / 2) (c₁ / (A₁ + 2)) with hη0
  have hη0pos : 0 < η0 := lt_min (by linarith) (by positivity)
  have hη0a : η0 ≤ cZ / 2 := min_le_left _ _
  have hη0b : η0 ≤ c₁ / (A₁ + 2) := min_le_right _ _
  have hη0c : η0 ≤ c₁ := hη0b.trans (div_le_self hc₁.le (by linarith))
  have hη01 : η0 ≤ 1 := by linarith
  set A' : ℝ := 4 * |C₁| * C * Real.exp (a + a * cZ / 2) * (A₁ + 2) ^ (B + 1) with hA'
  have hA'0 : 0 ≤ A' := by
    have h1 : 0 ≤ (A₁ + 2) ^ (B + 1) := Real.rpow_nonneg hk.le _
    have h2 : 0 ≤ C := by linarith
    positivity
  set c : ℝ := cZ / (4 * (A₁ + 2)) with hc
  have hc0 : 0 < c := by positivity
  set K0 : ℝ := (A₁ + 2) * (a + 1 + 2 / c₂) + (B + 1) / c with hK0
  have hK00 : 0 ≤ K0 := by
    have h1 : 0 ≤ a + 1 + 2 / c₂ := by positivity
    have h2 : 0 ≤ (B + 1) / c := by positivity
    positivity
  refine ⟨c / 2, A' * (A₁ + 2) ^ N / η0, K0 + 2 * N / c, by positivity, ?_⟩
  intro M _ Z m h8 hZ _ hms hwin y hy hL
  have hM8 : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM8' : (8 : ℝ) ≤ M := by exact_mod_cast hM8
  have hM0 : (0 : ℝ) < M := by linarith
  have hpw : 0 < (M : ℝ) ^ A₁ := Real.rpow_pos_of_pos hM0 _
  obtain ⟨hl2, hlℓ, hℓk⟩ := ell_bounds M hM8 A₁ hA₁
  set ℓ : ℝ := Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) with hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓN : 1 ≤ ℓ ^ N := one_le_pow₀ hℓ1
  have hll : 0 ≤ Real.log M * Real.log (Real.log M + 2) :=
    mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  have hL1 : K0 * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    have : 0 ≤ 2 * N / c * (Real.log M * Real.log (Real.log M + 2)) :=
      mul_nonneg (by positivity) hll
    nlinarith
  have hL2 : 2 * N / c * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    have : 0 ≤ K0 * (Real.log M * Real.log (Real.log M + 2)) := mul_nonneg hK00 hll
    nlinarith
  have habs := pow_absorb N c (Real.log M) (Real.log y) hc0 hl2 hL2
  suffices h : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) by
    obtain ⟨θ, h0, h1, hη, hθ⟩ := h
    have key := zeroSum_core a B C ha hB hC hdens (min c₀ (1 / 20)) c₂ C₁ A₁ (min_le_right _ _) hc₂ hA₁
      M Z m h8 hZ hms hwin y hy hL1 θ h0 h1 hθ
    refine key.trans ?_
    have hηpos : 0 < etaOf M := etaOf_pos M (by omega)
    set E : ℝ := Real.exp (-(c / 2 * Real.log y / Real.log M)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hEE : Real.exp (-(c * Real.log y / Real.log M)) = E * E := by
      rw [hE, ← Real.exp_add]
      congr 1
      ring
    rw [hEE]
    have hpow : ℓ ^ N ≤ (A₁ + 2) ^ N * Real.log M ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hℓ0.le hℓk N
    have hθle : θ ≤ etaOf M * ((A₁ + 2) ^ N * Real.log M ^ N) / η0 := by
      rw [le_div_iff₀ hη0pos]
      calc θ * η0 = η0 * θ := by ring
        _ ≤ etaOf M * ℓ ^ N := hη
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hηpos.le
    have hkN : 0 ≤ (A₁ + 2) ^ N := by positivity
    calc A' * θ * (E * E)
        ≤ A' * (etaOf M * ((A₁ + 2) ^ N * Real.log M ^ N) / η0) * (E * E) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hθle hA'0
      _ = (A' * (A₁ + 2) ^ N / η0 * etaOf M * E) * (Real.log M ^ N * E) := by ring
      _ ≤ (A' * (A₁ + 2) ^ N / η0 * etaOf M * E) * 1 := by
          apply mul_le_mul_of_nonneg_left habs
          positivity
      _ = _ := by ring
  have hone' : η0 ≤ etaOf M * ℓ ^ N → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) := by
    intro hη
    refine ⟨1, one_pos, le_refl _, by linarith, ?_⟩
    intro χ ρ _ hr
    unfold InRegion at hr
    replace hr := not_le.mp hr
    have habs := abs_nonneg ρ.im
    have h1 : (1 : ℝ) ≤ (M : ℝ) * (|ρ.im| + 2) := by nlinarith
    have h2 : 0 ≤ cZ / Real.log ((M : ℝ) * (|ρ.im| + 2)) := div_nonneg hcZ.le (Real.log_nonneg h1)
    have h3 : 0 ≤ ℓ * (1 - ρ.re) := mul_nonneg hℓ0.le (by linarith)
    simpa using h3
  have hone : η0 ≤ etaOf M → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) := by
    intro hη
    apply hone'
    calc η0 ≤ etaOf M := hη
      _ = etaOf M * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hℓN (hη0pos.le.trans hη)
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · apply hone
    rw [etaOf_none M he]
    exact hη01
  · obtain ⟨hsq, hne, hL0, _, hβ1⟩ := eOf_exc M (χ₁, β₁) he
    simp only at hsq hne hL0 hβ1
    have hβ : 0 < 1 - β₁ := by linarith
    have hlow : (1 - β₁) * ℓ / (A₁ + 2) ≤ (1 - β₁) * Real.log M := by
      rw [div_le_iff₀ hk]
      calc (1 - β₁) * ℓ ≤ (1 - β₁) * ((A₁ + 2) * Real.log M) := mul_le_mul_of_nonneg_left hℓk hβ.le
        _ = _ := by ring
    have hup : (1 - β₁) * ℓ ^ N ≤ (1 - β₁) * Real.log M * ℓ ^ N := by
      have h0 : 0 ≤ (1 - β₁) * ℓ ^ N := by positivity
      calc (1 - β₁) * ℓ ^ N = (1 - β₁) * ℓ ^ N * 1 := (mul_one _).symm
        _ ≤ (1 - β₁) * ℓ ^ N * Real.log M := mul_le_mul_of_nonneg_left (by linarith) h0
        _ = _ := by ring
    by_cases hr : InRegion cZ M (β₁ : ℂ)
    · by_cases hcc : c₁ ≤ (1 - β₁) * ℓ
      · apply hone
        rw [etaOf_some M χ₁ β₁ he]
        apply le_min hη01
        have : c₁ / (A₁ + 2) ≤ (1 - β₁) * ℓ / (A₁ + 2) := div_le_div_of_nonneg_right hcc hk.le
        linarith
      · replace hcc := not_le.mp hcc
        by_cases hu : c₁ ≤ (1 - β₁) * ℓ ^ N
        · apply hone'
          rw [etaOf_some M χ₁ β₁ he, min_mul_of_nonneg (1 : ℝ) ((1 - β₁) * Real.log M) (by positivity : (0 : ℝ) ≤ ℓ ^ N)]
          apply le_min
          · linarith
          · linarith
        · replace hu := not_le.mp hu
          have hθ0 : 0 < (1 - β₁) * ℓ ^ N / c₁ := by positivity
          have hθ1 : (1 - β₁) * ℓ ^ N / c₁ ≤ 1 := by
            rw [div_le_one hc₁]; exact hu.le
          refine ⟨(1 - β₁) * ℓ ^ N / c₁, hθ0, hθ1, ?_, ?_⟩
          · rw [etaOf_some M χ₁ β₁ he, min_mul_of_nonneg (1 : ℝ) ((1 - β₁) * Real.log M) (by positivity : (0 : ℝ) ≤ ℓ ^ N)]
            apply le_min
            · calc η0 * ((1 - β₁) * ℓ ^ N / c₁) ≤ 1 * 1 := mul_le_mul hη01 hθ1 hθ0.le zero_le_one
                _ ≤ 1 * ℓ ^ N := by linarith
            · calc η0 * ((1 - β₁) * ℓ ^ N / c₁) ≤ c₁ * ((1 - β₁) * ℓ ^ N / c₁) :=
                    mul_le_mul_of_nonneg_right hη0c hθ0.le
                _ = (1 - β₁) * ℓ ^ N := by field_simp
                _ ≤ _ := hup
          · intro χ ρ hρ hnr
            obtain ⟨hz, hre, him⟩ := hZ χ ρ hρ
            have hd := hdh M χ₁ χ β₁ ((M : ℝ) ^ A₁ + 3) ρ (by omega) (by linarith) hsq hne hL0
              (by
                have : 1 - β₁ < c₁ / ℓ := by rw [lt_div_iff₀ hℓ0]; exact hcc
                linarith)
              hβ1 hz
              (by
                have := min_le_left c₀ (1 / 20 : ℝ)
                linarith)
              (by linarith)
              (by
                intro heq
                have h2 : ρ = (β₁ : ℂ) := (Prod.mk.inj heq).2
                rw [h2] at hnr
                exact hnr hr)
            rw [one_div_div]
            rw [div_le_iff₀ hℓ0] at hd
            linarith
    · apply hone
      have := etaOf_far M (by omega) χ₁ β₁ he hr
      linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

