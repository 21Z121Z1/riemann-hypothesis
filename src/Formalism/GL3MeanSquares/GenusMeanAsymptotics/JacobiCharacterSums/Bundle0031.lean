import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0029
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0019
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0028

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDens
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem re_lt_one_of_isLZero {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M} {s : ℂ}
    (h : IsLZero χ s) : s.re < 1 := by
  by_contra hc
  push Not at hc
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h.1 hc h.2

theorem log_density_bound : Formalism.HermitianLattices.Ext.PrimesInProgressions.LogDensityM := by
  classical
  obtain ⟨C0, q0, h0⟩ := zero_count_first
  obtain ⟨C1, q1, h1⟩ := zero_count_second
  refine ⟨24, 10, |C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ), ?_⟩
  intro M _ T σ S hM hT hσ hS hsp
  suffices key : (S.card : ℝ) ≤ (|C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ)) *
      ((M * T : ℝ) ^ (24 * (1 - σ)) * Real.log (M * T) ^ (10 : ℕ)) by
    have hpow : Real.log (M * T) ^ (10 : ℝ) = Real.log (M * T) ^ (10 : ℕ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [hpow, mul_assoc]
    exact key
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX : (6 : ℝ) ≤ M * T := by nlinarith
  have hX0 : (0 : ℝ) < M * T := by linarith
  have hL : (1 : ℝ) ≤ Real.log (M * T) := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have hL10 : (1 : ℝ) ≤ Real.log (M * T) ^ 10 := one_le_pow₀ hL
  have hq0 : (0 : ℝ) ≤ ((max q0 q1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hCnn : 0 ≤ |C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ) := by positivity
  have htriv : (S.card : ℝ) ≤ 3 * (M * T) := by
    have h := trivial_bound M T S (by linarith) (fun p hp => (hS p hp).2.1) hsp
    have hMnn : (0 : ℝ) ≤ M := by linarith
    nlinarith
  rcases S.eq_empty_or_nonempty with hE | ⟨p0, hp0⟩
  · rw [hE]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hCnn (mul_nonneg (Real.rpow_nonneg hX0.le _) (by positivity))
  have hσ1 : σ ≤ 1 := by
    have h1' := re_lt_one_of_isLZero (hS p0 hp0).2.2
    linarith [(hS p0 hp0).1]
  have hR1 : (1 : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) := Real.one_le_rpow (by linarith) (by linarith)
  have hP : (1 : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 := by nlinarith
  have hXP : σ < 3 / 4 → (M * T : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 := by
    intro hs
    have hXe : (M * T : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) := by
      calc (M * T : ℝ) = (M * T) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    nlinarith
  have h0' := fun S hσ' hq => h0 M T σ S hM hT hσ' hq
  have h1' := fun S hσ' hq => h1 M T σ S hM hT hσ' hq
  simp only [mul_assoc] at h0' h1'
  set P := (M * T : ℝ) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 with hPdef
  have hP0 : (0 : ℝ) ≤ P := by linarith
  set q : ℝ := ((max q0 q1 : ℕ) : ℝ) with hqdef
  have hexp : (|C0| + |C1| + 3 + 3 * q) * P = |C0| * P + |C1| * P + 3 * P + 3 * q * P := by ring
  rw [hexp]
  have eC0 := mul_le_mul_of_nonneg_right (le_abs_self C0) hP0
  have eC1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hP0
  have a0 : 0 ≤ |C0| * P := mul_nonneg (abs_nonneg _) hP0
  have a1 : 0 ≤ |C1| * P := mul_nonneg (abs_nonneg _) hP0
  have aq : q ≤ q * P := by nlinarith
  by_cases hq : max q0 q1 ≤ qd M T
  · by_cases hσ34 : 3 / 4 ≤ σ
    · have hA0 := h0' (S.filter (fun p => p.1 = 1)) hσ34 (le_trans (le_max_left _ _) hq)
        (by
          intro p hp
          rw [Finset.mem_filter] at hp
          have hs := hS p hp.1
          exact ⟨hp.2, hs.1, re_lt_one_of_isLZero hs.2.2, hs.2.1, hs.2.2⟩)
        (by
          intro p hp p' hp' hne
          rw [Finset.mem_filter] at hp hp'
          exact hsp p hp.1 p' hp'.1 hne (hp.2.trans hp'.2.symm))
      have hA1 := h1' (S.filter (fun p => ¬ p.1 = 1)) hσ34 (le_trans (le_max_right _ _) hq)
        (by
          intro p hp
          rw [Finset.mem_filter] at hp
          have hs := hS p hp.1
          exact ⟨hp.2, hs.1, re_lt_one_of_isLZero hs.2.2, hs.2.1, hs.2.2.2⟩)
        (by
          intro p hp p' hp' hne heq
          rw [Finset.mem_filter] at hp hp'
          exact hsp p hp.1 p' hp'.1 hne heq)
      have hcast : (S.card : ℝ) = ((S.filter (fun p => p.1 = 1)).card : ℝ) +
          ((S.filter (fun p => ¬ p.1 = 1)).card : ℝ) := by
        rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
      linarith
    · push_neg at hσ34
      have := hXP hσ34
      linarith
  · push_neg at hq
    have hXq : (M * T : ℝ) < q := by
      refine lt_of_le_of_lt (Nat.le_ceil _) ?_
      rw [hqdef]
      unfold qd at hq
      exact_mod_cast hq
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplPick
section
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_pick (S : Finset ℝ) (a b : ℝ) (hab : a < b) :
    ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ ∀ s ∈ S, (b - a) / (2 * ((S.card : ℝ) + 1)) ≤ |x - s| := by
  set h : ℝ := (b - a) / (2 * ((S.card : ℝ) + 1)) with hh
  have hn : (0 : ℝ) < 2 * ((S.card : ℝ) + 1) := by positivity
  have hpos : 0 < h := div_pos (by linarith) hn
  have hmul : h * (2 * ((S.card : ℝ) + 1)) = b - a := by
    rw [hh]; field_simp
  by_contra hcon
  push Not at hcon
  have key : ∀ i ∈ Finset.range (S.card + 1), ∃ s ∈ S, |a + (2 * (i : ℝ) + 1) * h - s| < h := by
    intro i hi
    have hi' : (i : ℝ) ≤ S.card := by
      have := Finset.mem_range.mp hi
      exact_mod_cast Nat.lt_succ_iff.mp this
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    apply hcon
    · nlinarith
    · nlinarith
  choose! f hfS hf using key
  have hcard : S.card < (Finset.range (S.card + 1)).card := by simp
  obtain ⟨i, hi, j, hj, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun i hi => hfS i hi)
  have h1 := hf i hi
  have h2 := hf j hj
  rw [hfij] at h1
  rw [abs_lt] at h1 h2
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
    nlinarith
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
    nlinarith

theorem ex_choose : ∃ C : ℝ, 0 < C ∧ ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 20 →
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T : ℝ), 3 ≤ M → 2 ≤ T →
    ∃ σ₁ T' δ : ℝ, 1 - κ ≤ σ₁ ∧ σ₁ ≤ 1 - 3 * κ / 4 ∧ T ≤ T' ∧ T' ≤ T + 1 ∧ 0 < δ ∧ δ ≤ 1 / 20 ∧
      κ / (C * (T + 1) * Real.log ((M : ℝ) * (T + 2))) ≤ δ ∧
      (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → |ρ.im| ≤ T + 3 → δ ≤ |σ₁ - ρ.re|) ∧
      (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → δ ≤ |(|ρ.im| - T')|) := by
  obtain ⟨C0, hC0, hbox⟩ := ex_box
  refine ⟨8 * (4 * C0 + 1), by positivity, ?_⟩
  intro κ hκ hκ' M _ χ T hM hT
  obtain ⟨Z, hZ, -, hcard⟩ := hbox M χ (T + 3) hM (by linarith)
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  set N : ℝ := (Z.card : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set lg : ℝ := Real.log ((M : ℝ) * (T + 2)) with hlg
  have hx12 : (12 : ℝ) ≤ (M : ℝ) * (T + 2) := by nlinarith
  have hlg1 : 1 ≤ lg := by
    rw [hlg, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlg2 : Real.log ((M : ℝ) * (T + 3 + 2)) ≤ 2 * lg := by
    have h1 : (M : ℝ) * (T + 3 + 2) ≤ ((M : ℝ) * (T + 2)) ^ 2 := by nlinarith
    have h2 : Real.log (((M : ℝ) * (T + 2)) ^ 2) = 2 * lg := by
      rw [Real.log_pow]; push_cast; ring
    rw [← h2]
    exact Real.log_le_log (by nlinarith) h1
  have hNb : 8 * (N + 1) ≤ 8 * (4 * C0 + 1) * (T + 1) * lg := by
    have h1 : C0 * (T + 3 + 1) * Real.log ((M : ℝ) * (T + 3 + 2)) ≤ C0 * (2 * (T + 1)) * (2 * lg) := by
      apply mul_le_mul _ hlg2 _ (by positivity)
      · apply mul_le_mul_of_nonneg_left (by linarith) hC0.le
      · apply Real.log_nonneg; nlinarith
    have h2 : 1 ≤ (T + 1) * lg := by nlinarith
    nlinarith

  obtain ⟨σ₁, hσa, hσb, hσ⟩ := ex_pick (Z.image Complex.re) (1 - κ) (1 - 3 * κ / 4) (by linarith)
  obtain ⟨T', hTa, hTb, hT'⟩ := ex_pick (Z.image (fun ρ => |ρ.im|)) T (T + 1) (by linarith)
  have hc1 : (((Z.image Complex.re).card : ℕ) : ℝ) ≤ N := by
    rw [hN]; exact Nat.cast_le.mpr Finset.card_image_le
  have hc2 : (((Z.image (fun ρ : ℂ => |ρ.im|)).card : ℕ) : ℝ) ≤ N := by
    rw [hN]; exact Nat.cast_le.mpr Finset.card_image_le
  have hδpos : 0 < κ / (8 * (N + 1)) := by positivity
  have hg1 : κ / (8 * (N + 1)) ≤
      (1 - 3 * κ / 4 - (1 - κ)) / (2 * (((Z.image Complex.re).card : ℝ) + 1)) := by
    have e : (1 - 3 * κ / 4 - (1 - κ)) = κ / 4 := by ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hg2 : κ / (8 * (N + 1)) ≤
      (T + 1 - T) / (2 * (((Z.image (fun ρ : ℂ => |ρ.im|)).card : ℝ) + 1)) := by
    have e : (T + 1 - T) = 1 := by ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hδle : κ / (8 * (N + 1)) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨σ₁, T', κ / (8 * (N + 1)), hσa, hσb, hTa, hTb, hδpos, hδle, ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left hκ.le (by positivity) hNb
  · intro ρ h0 hre him
    have hmem : ρ ∈ Z := (hZ ρ).2 ⟨h0, hre, him⟩
    exact hg1.trans (hσ _ (Finset.mem_image_of_mem _ hmem))
  · intro ρ h0 hre
    by_cases him : |ρ.im| ≤ T + 3
    · have hmem : ρ ∈ Z := (hZ ρ).2 ⟨h0, hre, him⟩
      have := hT' _ (Finset.mem_image_of_mem (fun ρ : ℂ => |ρ.im|) hmem)
      rw [abs_sub_comm] at this
      exact hg2.trans this
    · push Not at him
      have : (2 : ℝ) ≤ |ρ.im| - T' := by linarith
      have h3 := le_abs_self (|ρ.im| - T')
      linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

