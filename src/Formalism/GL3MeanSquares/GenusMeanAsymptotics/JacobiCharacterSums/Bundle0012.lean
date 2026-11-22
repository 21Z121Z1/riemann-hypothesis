import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqCount
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0011
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0004
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0010
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContourB
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0005
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0002

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistA
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

def clsB (m₀ s a₀ : ℕ) : Finset ℕ :=
  (range (m₀ * s)).filter (fun b => b % m₀ = a₀ % m₀ ∧ b.Coprime s)

def smallCnt (X : ℝ) (M b : ℕ) : ℕ :=
  (((Icc (1 : ℕ) ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).filter (fun p => p % M = b)).card

theorem sum_jacobiSym_eq_sum_residueClass (m₀ s a₀ : ℕ) (X : ℝ) (hm : 0 < m₀) (hs : 0 < s) :
    ∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) =
      ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
        (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ) := by
  have hM : 0 < m₀ * s := Nat.mul_pos hm hs
  have : NeZero s := ⟨hs.ne'⟩
  have hcongr : ∀ q : ℕ, (jacobiSym (q : ℤ) s : ℝ) = (jacobiSym ((q % (m₀ * s) : ℕ) : ℤ) s : ℝ) := by
    intro q
    have h : q ≡ q % (m₀ * s) [MOD s] :=
      Nat.ModEq.of_dvd (dvd_mul_left s m₀) (Nat.mod_modEq q (m₀ * s)).symm
    rw [jacobi_congr h]
  have hzero : ∀ q ∈ PPset m₀ a₀ X, q % (m₀ * s) ∉ clsB m₀ s a₀ →
      (jacobiSym (q : ℤ) s : ℝ) = 0 := by
    intro q hq hnot
    have hqm : q % m₀ = a₀ % m₀ := (Finset.mem_filter.mp hq).2.2.1
    have hnc : ¬ q.Coprime s := by
      intro hc
      apply hnot
      simp only [clsB, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hM, by rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m₀ s), hqm], ?_⟩
      have hg := (Nat.ModEq.of_dvd (dvd_mul_left s m₀) (Nat.mod_modEq q (m₀ * s))).gcd_eq
      rw [Nat.Coprime, hg]
      exact hc
    have h0 : jacobiSym (q : ℤ) s = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hnc
    rw [h0]
    simp
  symm
  calc ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
        (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ)
      = ∑ b ∈ clsB m₀ s a₀, ∑ q ∈ PPset m₀ a₀ X,
          if q % (m₀ * s) = b then (jacobiSym (q : ℤ) s : ℝ) else 0 := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [← Finset.sum_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        have hqb := (Finset.mem_filter.mp hq).2
        rw [hcongr q, hqb]
        simp
    _ = ∑ q ∈ PPset m₀ a₀ X, ∑ b ∈ clsB m₀ s a₀,
          if q % (m₀ * s) = b then (jacobiSym (q : ℤ) s : ℝ) else 0 := Finset.sum_comm
    _ = ∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) := by
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [Finset.sum_ite_eq]
        by_cases h : q % (m₀ * s) ∈ clsB m₀ s a₀
        · rw [if_pos h]
        · rw [if_neg h, hzero q hq h]

theorem cnt_add_small (m₀ s a₀ : ℕ) (X : ℝ) (b : ℕ) (hb : b ∈ clsB m₀ s a₀) :
    ((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card + smallCnt X (m₀ * s) b = piAP X (m₀ * s) b := by
  obtain ⟨hbr, hbm, -⟩ : b < m₀ * s ∧ b % m₀ = a₀ % m₀ ∧ b.Coprime s := by
    simpa [clsB] using hb
  have hbM : b % (m₀ * s) = b := Nat.mod_eq_of_lt hbr
  have hmod : ∀ p : ℕ, p % (m₀ * s) = b → p % m₀ = a₀ % m₀ := fun p h => by
    rw [← Nat.mod_mod_of_dvd p (dvd_mul_right m₀ s), h, hbm]
  have key := Finset.card_filter_add_card_filter_not
    (s := (Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ p % (m₀ * s) = b))
    (fun p : ℕ => X ^ (1 / 2 : ℝ) < (p : ℝ))
  unfold piAP
  rw [hbM, ← key]
  congr 1
  · congr 1
    ext p
    simp only [PPset, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2, -, h4⟩, h5⟩
      exact ⟨⟨h1, h2, h5⟩, h4⟩
    · rintro ⟨⟨h1, h2, h5⟩, h4⟩
      exact ⟨⟨h1, h2, hmod p h5, h4⟩, h5⟩
  · unfold smallCnt
    congr 1
    ext p
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨⟨h1, h2, h4⟩, h5⟩
      exact ⟨⟨h1, h2, h5⟩, h4⟩
    · rintro ⟨⟨h1, h2, h5⟩, h4⟩
      exact ⟨⟨h1, h2, h4⟩, h5⟩

private theorem sum_card_filter_mod_le_card (T B : Finset ℕ) (M : ℕ) :
    ∑ b ∈ B, (T.filter (fun p => p % M = b)).card ≤ T.card := by
  calc ∑ b ∈ B, (T.filter (fun p => p % M = b)).card
      = ∑ b ∈ B, ∑ p ∈ T, if p % M = b then 1 else 0 := by simp only [Finset.card_filter]
    _ = ∑ p ∈ T, ∑ b ∈ B, if p % M = b then 1 else 0 := Finset.sum_comm
    _ = ∑ p ∈ T, if p % M ∈ B then 1 else 0 := by simp only [Finset.sum_ite_eq]
    _ ≤ ∑ p ∈ T, 1 := Finset.sum_le_sum (fun p _ => by split_ifs <;> simp)
    _ = T.card := by simp

theorem sum_small_le (m₀ s a₀ : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    (∑ b ∈ clsB m₀ s a₀, (smallCnt X (m₀ * s) b : ℝ)) ≤ X ^ (1 / 2 : ℝ) := by
  have h1 : ∑ b ∈ clsB m₀ s a₀, smallCnt X (m₀ * s) b ≤
      ((Finset.Icc (1 : ℕ) ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).card :=
    sum_card_filter_mod_le_card _ _ _
  have h2 : ((Finset.Icc (1 : ℕ) ⌊X⌋₊).filter
      (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).card ≤ ⌊X ^ (1 / 2 : ℝ)⌋₊ := by
    calc _ ≤ (Finset.Icc (1 : ℕ) ⌊X ^ (1 / 2 : ℝ)⌋₊).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨hp.1.1, Nat.le_floor hp.2.2⟩
      _ = ⌊X ^ (1 / 2 : ℝ)⌋₊ := by simp
  have h3 : (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hX _)
  have h4 : ((∑ b ∈ clsB m₀ s a₀, smallCnt X (m₀ * s) b : ℕ) : ℝ) ≤ (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast h1.trans h2
  push_cast at h4
  linarith

theorem sum_cnt_le (m₀ s a₀ : ℕ) (X : ℝ) :
    (∑ b ∈ clsB m₀ s a₀, (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ)) ≤
      ((PPset m₀ a₀ X).card : ℝ) := by
  exact_mod_cast sum_card_filter_mod_le_card (PPset m₀ a₀ X) (clsB m₀ s a₀) (m₀ * s)

theorem abs_jac_le (a : ℤ) (s : ℕ) : |(jacobiSym a s : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy a s with h | h | h <;> simp [h]

theorem main_le_two_pi {P m k : ℝ} (hP : 0 ≤ P) (hk : |k| ≤ 1 / 2) (h : |P - m| ≤ k * m) :
    |m| ≤ 2 * P ∧ |P - m| ≤ 2 * |k| * P := by
  have h0 : k * m ≤ |k| * |m| := by rw [← abs_mul]; exact le_abs_self _
  have h1 : |k| * |m| ≤ 1 / 2 * |m| := mul_le_mul_of_nonneg_right hk (abs_nonneg m)
  have h2 : |m| - |P| ≤ |m - P| := abs_sub_abs_le_abs_sub m P
  rw [abs_sub_comm, abs_of_nonneg hP] at h2
  have hm : |m| ≤ 2 * P := by linarith
  refine ⟨hm, ?_⟩
  have h3 : |k| * |m| ≤ |k| * (2 * P) := mul_le_mul_of_nonneg_left hm (abs_nonneg k)
  linarith

private theorem twist_decomposition_bound_of_sum_bounds (C : Finset ℕ) (J N S main : ℕ → ℝ) (k A B : ℝ)
    (hJ : ∀ b, |J b| ≤ 1) (hS0 : ∀ b, 0 ≤ S b)
    (hNb : ∀ b ∈ C, |N b + S b - main b| ≤ 2 * |k| * (N b + S b))
    (hMb : ∀ b ∈ C, |main b| ≤ 2 * (N b + S b))
    (hN : ∑ b ∈ C, N b ≤ A) (hS : ∑ b ∈ C, S b ≤ B) :
    |∑ b ∈ C, J b * N b - ∑ b ∈ C, J b * main b| ≤ 2 * |k| * (A + B) + B ∧
      ∑ b ∈ C, |main b| ≤ 2 * (A + B) := by
  have hk := abs_nonneg k
  constructor
  · rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have step : ∀ b ∈ C, |J b * N b - J b * main b| ≤ 2 * |k| * N b + (2 * |k| * S b + S b) := by
      intro b hb
      rw [← mul_sub, abs_mul]
      have h' := abs_le.mp (hNb b hb)
      have e : |N b - main b| ≤ 2 * |k| * N b + (2 * |k| * S b + S b) :=
        abs_le.mpr ⟨by linarith [h'.1, hS0 b], by linarith [h'.2, hS0 b]⟩
      calc |J b| * |N b - main b| ≤ 1 * |N b - main b| :=
            mul_le_mul_of_nonneg_right (hJ b) (abs_nonneg _)
        _ = |N b - main b| := one_mul _
        _ ≤ _ := e
    refine (Finset.sum_le_sum step).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hA := mul_le_mul_of_nonneg_left hN (by linarith : (0 : ℝ) ≤ 2 * |k|)
    have hB := mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ 2 * |k|)
    linarith
  · calc ∑ b ∈ C, |main b| ≤ ∑ b ∈ C, 2 * (N b + S b) := Finset.sum_le_sum hMb
      _ = 2 * (∑ b ∈ C, N b + ∑ b ∈ C, S b) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * (A + B) := by linarith

theorem twist_decomp (m₀ s a₀ : ℕ) (X : ℝ) (hm : 0 < m₀) (hs : 0 < s) (hX : 0 ≤ X)
    (main : ℕ → ℝ) (k : ℝ) (hk : |k| ≤ 1 / 2)
    (hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - main b| ≤ k * main b) :
    |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) -
        ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * main b| ≤
      2 * |k| * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) + X ^ (1 / 2 : ℝ) ∧
    ∑ b ∈ clsB m₀ s a₀, |main b| ≤ 2 * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) := by
  have hmain := twist_decomposition_bound_of_sum_bounds (clsB m₀ s a₀) (fun b => (jacobiSym (b : ℤ) s : ℝ))
    (fun b => (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ))
    (fun b => (smallCnt X (m₀ * s) b : ℝ)) main k ((PPset m₀ a₀ X).card : ℝ) (X ^ (1 / 2 : ℝ))
    (fun b => abs_jac_le _ _) (fun b => Nat.cast_nonneg _)
    (fun b hbC => by
      have h := (main_le_two_pi (Nat.cast_nonneg _) hk (hb b hbC)).2
      rw [← cnt_add_small m₀ s a₀ X b hbC] at h
      push_cast at h
      exact h)
    (fun b hbC => by
      have h := (main_le_two_pi (Nat.cast_nonneg _) hk (hb b hbC)).1
      rw [← cnt_add_small m₀ s a₀ X b hbC] at h
      push_cast at h
      exact h)
    (sum_cnt_le m₀ s a₀ X) (sum_small_le m₀ s a₀ X hX)
  rw [sum_jacobiSym_eq_sum_residueClass m₀ s a₀ X hm hs]
  exact hmain

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContour
section
open Complex MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_contour (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 800) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (Q z η : ℝ), χ ≠ 1 → 2 ≤ Q → (N : ℝ) ≤ Q →
      Formalism.HermitianLattices.ZeroFreeRegionGL2.ZeroFreeBox Q χ → 1 ≤ z → 0 < η → η ≤ 1 →
      ‖Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1‖ ≤
        K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + δ) + z ^ 2 / Q) := by
  obtain ⟨KB, hKB0, hKB⟩ := tail_box_negLD δ hδ
  obtain ⟨C₀, hC₀, hR⟩ := Formalism.ZeroFreeDirichlet.l_log_deriv_right
  refine ⟨160 * KB + 32 * (1 + C₀), by positivity, ?_⟩
  intro N _ χ Q z η hχ hQ hNQ hbox hz hη hη1
  have hbox' : ∀ s : ℂ, 1 - 1 / 400 + δ ≤ s.re → |s.im| ≤ Q - 1 →
      ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ KB * Real.log Q := hKB N χ Q hχ hQ hNQ hbox
  set σ₁ : ℝ := 1 - 1 / 400 + δ with hσ₁
  set T : ℝ := Q / 2 with hTdef
  set Lq : ℝ := Real.log Q with hLq
  have hT0 : 0 < T := by rw [hTdef]; linarith
  have hTQ : T ≤ Q - 1 := by rw [hTdef]; linarith
  have hσa : 0 < σ₁ := by rw [hσ₁]; linarith
  have hσb : σ₁ < 1 := by rw [hσ₁]; linarith
  have hσc : 1 / 2 ≤ σ₁ := by rw [hσ₁]; linarith
  have hσd : σ₁ ≤ 1 - 1 / 800 := by rw [hσ₁]; linarith
  have hLq2 : 1 / 2 ≤ Lq := by
    have := Real.log_le_log (by norm_num) hQ
    linarith [Real.log_two_gt_d9]
  have hzf : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ 2 → |w.im| ≤ T →
      DirichletCharacter.LFunction χ w ≠ 0 := fun w h1 _ h3 =>
    hbox w (by rw [hσ₁] at h1; linarith) (by linarith)
  have hz0 : 0 < z := by linarith
  set y1 : ℝ := z + z * η with hy1def
  have hy1 : 1 ≤ y1 := by rw [hy1def]; nlinarith
  have hy12 : y1 ≤ 2 * z := by rw [hy1def]; nlinarith
  have I1 := tail_shift_identity χ hχ y1 σ₁ T hy1 hσa hσb hT0 hzf
  have I0 := tail_shift_identity χ hχ z σ₁ T hz hσa hσb hT0 hzf
  have key : (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1)
      = (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.negLD χ 1 * y1)
        - (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ z - Formalism.ZeroFreeDirichlet.negLD χ 1 * z) := by
    rw [hy1def]; push_cast; ring
  rw [I1, I0] at key
  have hcomb := (congrArg norm key).le.trans (tc_norm_comb _ _ _ _ _ _ _ _)

  have hE : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * z →
      ‖∫ t in (Set.Ioc (-T) T)ᶜ, Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        2 * Real.pi * (8 * (1 + C₀) * (z ^ 2 / Q)) := by
    intro y hy hy2
    have h := Formalism.ZF.norm_integral_compl_le (fun t => Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I))
      ((1 + C₀) * (4 * z ^ 2)) T (by positivity) hT0 (fun t ht => by
        have ht0 : t ≠ 0 := by intro h0; rw [h0, abs_zero] at ht; linarith
        refine (tc_right_pt χ C₀ (fun s hs => hR N χ s hs) y t (by linarith) ht0).trans ?_
        have hyy : y ^ 2 ≤ 4 * z ^ 2 := by nlinarith
        gcongr)
    refine h.trans (le_of_eq ?_)
    rw [hTdef]; field_simp; ring

  have hH : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * z → ∀ v : ℝ, |v| = T →
      ‖∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤ 16 * KB * Lq * (z ^ 2 / Q) := by
    intro y hy hy2 v hv
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I))
      (C := KB * Lq * (4 * z ^ 2) / T ^ 2) (a := σ₁) (b := 2) (fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        have hM := hbox' ((x : ℂ) + (v : ℂ) * I) (by simp; exact hx.1.le)
          (by simp; rw [hv]; exact hTQ)
        refine (tc_horiz_pt χ _ y T x v hy hT0 hv hx.2 hM).trans ?_
        have hyy : y ^ 2 ≤ 4 * z ^ 2 := by nlinarith
        have hM0 : 0 ≤ KB * Real.log Q := le_trans (norm_nonneg _) hM
        gcongr)
    refine h.trans ?_
    have hlen : |2 - σ₁| ≤ 2 := by rw [abs_of_pos (by linarith)]; linarith
    have hKL : 0 ≤ KB * Lq := by positivity
    calc KB * Lq * (4 * z ^ 2) / T ^ 2 * |2 - σ₁| ≤ KB * Lq * (4 * z ^ 2) / T ^ 2 * 2 := by gcongr
      _ = 32 * (KB * Lq) * (z ^ 2 / Q) / Q := by rw [hTdef]; field_simp; ring
      _ ≤ 32 * (KB * Lq) * (z ^ 2 / Q) / 2 := by gcongr
      _ = 16 * KB * Lq * (z ^ 2 / Q) := by ring

  have hV := tc_left_int χ hχ z η σ₁ T (KB * Lq) hz0 hη.le hη1 hσc hσd hT0.le
    (fun u hu => hzf _ (by simp) (by simp; linarith) (by simpa using hu))
    (fun u hu => hbox' _ (by simp) (by simpa using hu.trans hTQ))
  rw [← hy1def] at hV
  have hlog : Real.log (1 + 800 * T) ≤ 10 * Lq := by rw [hTdef, hLq]; exact tc_log_bound Q hQ
  have hLq0 : 0 ≤ Lq := by linarith
  set A : ℝ := z ^ 2 / Q with hAdef
  set Bv : ℝ := η * z ^ σ₁ with hBvdef
  have hA0 : 0 ≤ A := div_nonneg (sq_nonneg z) (by linarith)
  have hB0 : 0 ≤ Bv := mul_nonneg hη.le (Real.rpow_nonneg hz0.le _)
  have hV' : ‖(∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ y1 ((σ₁ : ℂ) + (u : ℂ) * I))
      - ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ z ((σ₁ : ℂ) + (u : ℂ) * I)‖ ≤ 160 * KB * Lq ^ 2 * Bv := by
    refine hV.trans ?_
    have hn : 0 ≤ KB * Lq * (4 * η * z ^ σ₁) :=
      mul_nonneg (mul_nonneg hKB0 hLq0) (mul_nonneg (by linarith) (Real.rpow_nonneg hz0.le _))
    calc KB * Lq * (4 * η * z ^ σ₁) * (4 * Real.log (1 + 800 * T))
        ≤ KB * Lq * (4 * η * z ^ σ₁) * (4 * (10 * Lq)) := by
          apply mul_le_mul_of_nonneg_left _ hn; linarith
      _ = 160 * KB * Lq ^ 2 * Bv := by rw [hBvdef]; ring
  have hE1 := hE y1 hy1 hy12
  have hE0 := hE z hz (by linarith)
  have hHa1 := hH y1 hy1 hy12 (-T) (by rw [abs_neg, abs_of_pos hT0])
  have hHb1 := hH y1 hy1 hy12 T (abs_of_pos hT0)
  have hHa0 := hH z hz (by linarith) (-T) (by rw [abs_neg, abs_of_pos hT0])
  have hHb0 := hH z hz (by linarith) T (abs_of_pos hT0)
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, hn] at hcomb
  set X := ‖Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1‖ with hXdef
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hW : 0 ≤ 64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv := by
    have := mul_nonneg (mul_nonneg hKB0 hLq0) hA0
    have := mul_nonneg (mul_nonneg hKB0 (sq_nonneg Lq)) hB0
    linarith
  have hWW := le_mul_of_one_le_left hW hpi
  have h2X : 2 * Real.pi * X ≤
      2 * Real.pi * (16 * (1 + C₀) * A + (64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv)) := by
    linarith
  have hXR : X ≤ 16 * (1 + C₀) * A + (64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv) :=
    le_of_mul_le_mul_left h2X (by positivity)
  have p1 : 0 ≤ KB * Lq * A := mul_nonneg (mul_nonneg hKB0 hLq0) hA0
  have p2 : 0 ≤ (1 + C₀) * Lq ^ 2 * Bv := mul_nonneg (mul_nonneg (by linarith) (sq_nonneg Lq)) hB0
  have p3 : 0 ≤ (1 + C₀) * A * (2 * Lq - 1) := mul_nonneg (mul_nonneg (by linarith) hA0) (by linarith)
  have hgoal : (160 * KB + 32 * (1 + C₀)) * Lq * (Lq * η * z ^ σ₁ + A) =
      160 * KB * Lq ^ 2 * Bv + 160 * KB * Lq * A + 32 * (1 + C₀) * Lq ^ 2 * Bv
        + 32 * (1 + C₀) * Lq * A := by rw [hBvdef]; ring
  rw [hgoal]
  linarith

end Formalism.HermitianLattices.Ext.BoxTail
end
end

