import Formalism.PolynomialDimension.Bundle0002

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.FrameMultinomialBoundHolds
section
noncomputable section

open scoped BigOperators
open Finset Real

namespace Formalism.CountingSumsFrames

theorem gram_weylDim_cons (n : ℕ) (A : ℤ) (μ : Fin n → ℤ) :
    weylDim (n + 1) (Fin.cons A μ : Fin (n + 1) → ℤ) =
      (∏ j : Fin n, ((((A - μ j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) * weylDim n μ := by
  unfold weylDim
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, lt_self_iff_false, if_false, one_mul, Fin.succ_pos, if_true,
      Fin.val_succ, Fin.val_zero]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    push_cast
    ring
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_succ, Fin.cons_zero, Fin.not_lt_zero, if_false, one_mul, Fin.succ_lt_succ_iff,
      Fin.val_succ]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    split_ifs
    · push_cast
      congr 1 <;> ring
    · rfl

theorem gram_choose_prod (a' : ℕ) : ∀ n : ℕ,
    (((a' + n).choose n : ℕ) : ℝ) = ∏ j : Fin n, ((a' : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    have h := Nat.add_one_mul_choose_eq (a' + n) n
    have h' : ((a' + n : ℝ) + 1) * (((a' + n).choose n : ℕ) : ℝ) =
        (((a' + n + 1).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast h
    rw [show a' + (n + 1) = a' + n + 1 by ring]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [mul_div_assoc', eq_div_iff hn.ne']
    linarith

theorem gram_prod_le (m : ℕ) (f g : Fin m → ℝ) (t : ℝ) (hf : ∀ j, 0 ≤ f j)
    (hfg : ∀ j, f j ≤ (1 + t) * g j) :
    ∏ j, f j ≤ (1 + t) ^ m * ∏ j, g j := by
  calc ∏ j, f j ≤ ∏ j, ((1 + t) * g j) := Finset.prod_le_prod (fun j _ => hf j) (fun j _ => hfg j)
    _ = (1 + t) ^ m * ∏ j, g j := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem gram_key (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : (n : ℝ) * x ≤ y) :
    (1 - y) * (1 + x) ^ n ≤ 1 := by
  have hp : 0 ≤ (1 + x) ^ n := by positivity
  by_cases h : 1 - y ≤ 0
  · nlinarith
  · rw [not_le] at h
    have e1 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
    have e2 : (1 + x) ^ n ≤ Real.exp (n * x) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n
    calc (1 - y) * (1 + x) ^ n ≤ Real.exp (-y) * Real.exp (n * x) :=
          mul_le_mul e1 e2 hp (Real.exp_pos _).le
      _ = Real.exp (n * x - y) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero

theorem gram_weylDim_pos (m : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) : 0 < weylDim m μ := by
  unfold weylDim
  apply Finset.prod_pos; intro i _
  apply Finset.prod_pos; intro j _
  split_ifs with h
  · have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast (show (i : ℕ) < (j : ℕ) from h)
    have h2 : μ j ≤ μ i := hμ h.le
    have h3 : ((μ j : ℤ) : ℚ) ≤ ((μ i : ℤ) : ℚ) := by exact_mod_cast h2
    push_cast
    apply div_pos <;> linarith
  · exact one_pos

theorem one_sub_mul_mul_le (y P W C x : ℝ) (n : ℕ) (hW : 0 ≤ W) (hP0 : 0 ≤ P) (hC : 0 ≤ C)
    (hPle : P ≤ (1 + x) ^ n * C) (hkey : (1 - y) * (1 + x) ^ n ≤ 1) : (1 - y) * (P * W) ≤ C * W := by
  have hPW : 0 ≤ P * W := mul_nonneg hP0 hW
  have hCW : 0 ≤ C * W := mul_nonneg hC hW
  by_cases h : 1 - y ≤ 0
  · nlinarith
  · rw [not_le] at h
    calc (1 - y) * (P * W) ≤ (1 - y) * (((1 + x) ^ n * C) * W) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPle hW) h.le
      _ = ((1 - y) * (1 + x) ^ n) * (C * W) := by ring
      _ ≤ 1 * (C * W) := mul_le_mul_of_nonneg_right hkey hCW
      _ = C * W := one_mul _

end Formalism.CountingSumsFrames
end
end

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.HarmonicLevelCountRec
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

lemma dimPol_mono (k' : ℕ) {a b : ℕ} (h : a ≤ b) : dimPol k' a ≤ dimPol k' b :=
  Nat.choose_le_choose k' (by omega)

lemma dimPol_mul_deg (k' b : ℕ) : dimPol k' b * (b + 1 + k') = dimPol k' (b + 1) * (b + 1) := by
  unfold dimPol
  have h := Nat.choose_mul_succ_eq (b + k') k'
  rw [show b + k' + 1 - k' = b + 1 by omega] at h
  rw [show b + 1 + k' = b + k' + 1 by omega]
  exact h

lemma dimPol_succ_vars (k' b : ℕ) : dimPol (k' + 1) b * (k' + 1) = (b + k' + 1) * dimPol k' b := by
  unfold dimPol
  rw [show b + (k' + 1) = b + k' + 1 by omega]
  exact (Nat.add_one_mul_choose_eq (b + k') k').symm

lemma dimPol_mul_deg_real (k' b : ℕ) :
    (dimPol k' b : ℝ) * ((b : ℝ) + 1 + k') = (dimPol k' (b + 1) : ℝ) * ((b : ℝ) + 1) := by
  exact_mod_cast dimPol_mul_deg k' b

theorem harmonic_level_count_rec (k' : ℕ) : ∀ A B : ℕ,
    ∑ j ∈ range (min A B + 1), dimHar k' (A - j) (B - j) = dimPol k' A * dimPol k' B
  | 0, B => by simp [dimHar]
  | A + 1, 0 => by simp [dimHar]
  | A + 1, B + 1 => by
    rw [show min (A + 1) (B + 1) + 1 = (min A B + 1) + 1 by omega, Finset.sum_range_succ']
    have e : ∀ j ∈ range (min A B + 1),
        dimHar k' (A + 1 - (j + 1)) (B + 1 - (j + 1)) = dimHar k' (A - j) (B - j) := by
      intro j _
      rw [show A + 1 - (j + 1) = A - j by omega, show B + 1 - (j + 1) = B - j by omega]
    rw [Finset.sum_congr rfl e, harmonic_level_count_rec k' A B]
    have hle : dimPol k' A * dimPol k' B ≤ dimPol k' (A + 1) * dimPol k' (B + 1) :=
      Nat.mul_le_mul (dimPol_mono k' (by omega)) (dimPol_mono k' (by omega))
    simp only [dimHar, Nat.sub_zero, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, or_self, if_false]
    exact Nat.add_sub_cancel' hle

theorem harmonic_level_count : LevelCount :=
  fun k' A B => harmonic_level_count_rec k' A B

lemma sum_Icc_dimHar (k' A B J : ℕ) (hJ : J ≤ min A B) :
    ∑ j ∈ Icc J (min A B), dimHar k' (A - j) (B - j) = dimPol k' (A - J) * dimPol k' (B - J) := by
  have e : Icc J (min A B) = Ico J (J + (min (A - J) (B - J) + 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega
  rw [e, Finset.sum_Ico_eq_sum_range,
    show J + (min (A - J) (B - J) + 1) - J = min (A - J) (B - J) + 1 by omega,
    ← harmonic_level_count_rec k' (A - J) (B - J)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show A - (J + i) = A - J - i by omega, show B - (J + i) = B - J - i by omega]

lemma dimPol_ratio (B J : ℕ) (hJ : J ≤ B) : ∀ k' : ℕ,
    (dimPol k' (B - J) : ℝ) ≤ (1 - (J : ℝ) / ((B : ℝ) + k' + 1)) ^ k' * dimPol k' B
  | 0 => by simp [dimPol]
  | k' + 1 => by
    have ih := dimPol_ratio B J hJ k'
    have h1 : (dimPol (k' + 1) (B - J) : ℝ) * ((k' : ℝ) + 1)
        = ((B : ℝ) - J + k' + 1) * dimPol k' (B - J) := by
      have := congrArg (Nat.cast : ℕ → ℝ) (dimPol_succ_vars k' (B - J))
      push_cast [Nat.cast_sub hJ] at this
      linarith
    have h2 : (dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1) = ((B : ℝ) + k' + 1) * dimPol k' B := by
      have := congrArg (Nat.cast : ℕ → ℝ) (dimPol_succ_vars k' B)
      push_cast at this
      linarith
    have hJB : (J : ℝ) ≤ B := by exact_mod_cast hJ
    have hB0 : (0 : ℝ) < (B : ℝ) + k' + 1 := by positivity
    have hB1 : (0 : ℝ) < (B : ℝ) + ((k' + 1 : ℕ) : ℝ) + 1 := by positivity
    set x := (J : ℝ) / ((B : ℝ) + k' + 1) with hx
    set y := (J : ℝ) / ((B : ℝ) + ((k' + 1 : ℕ) : ℝ) + 1) with hy
    have hx1 : x ≤ 1 := by rw [hx, div_le_one hB0]; linarith
    have hyx : y ≤ x := by
      rw [hx, hy]
      apply div_le_div_of_nonneg_left (by positivity) hB0
      push_cast; linarith
    have hxe : (1 - x) * ((B : ℝ) + k' + 1) = (B : ℝ) - J + k' + 1 := by
      rw [hx]; field_simp; ring
    have hP0 : (0 : ℝ) ≤ dimPol k' B := by positivity
    have hk : (0 : ℝ) < (k' : ℝ) + 1 := by positivity
    rw [← mul_le_mul_iff_of_pos_right hk, h1]
    calc ((B : ℝ) - J + k' + 1) * dimPol k' (B - J)
        ≤ ((B : ℝ) - J + k' + 1) * ((1 - x) ^ k' * dimPol k' B) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - x) ^ (k' + 1) * ((dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1)) := by
          rw [h2, ← hxe]; ring
      _ ≤ (1 - y) ^ (k' + 1) * ((dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = (1 - y) ^ (k' + 1) * (dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1) := by ring

lemma tail_bound (k' A B J : ℕ) (hJ : J ≤ min A B) :
    ((dimPol k' (A - J) * dimPol k' (B - J) : ℕ) : ℝ) ≤
      (1 - (J : ℝ) / (B + k' + 1)) ^ k' * ((dimPol k' A * dimPol k' B : ℕ) : ℝ) := by
  have hJB' : J ≤ B := le_trans hJ (min_le_right A B)
  have hJB : (J:ℝ) ≤ B := by exact_mod_cast hJB'
  have hx0 : 0 ≤ 1 - (J:ℝ) / ((B:ℝ) + k' + 1) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have h1 : (dimPol k' (A - J) : ℝ) ≤ dimPol k' A := by
    exact_mod_cast dimPol_mono k' (Nat.sub_le A J)
  have h2 := dimPol_ratio B J hJB' k'
  rw [Nat.cast_mul, Nat.cast_mul]
  calc (dimPol k' (A - J) : ℝ) * dimPol k' (B - J)
      ≤ dimPol k' A * ((1 - (J:ℝ) / ((B:ℝ) + k' + 1)) ^ k' * dimPol k' B) :=
        mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem highLevelTail : LevelTail :=
  fun k' A B J hJ => ⟨sum_Icc_dimHar k' A B J hJ, tail_bound k' A B J hJ⟩

theorem level_tail_exp_bound : LevelTailExp := by
  intro k' A B J La b' hk hb hLa hJ hB
  by_cases hJm : J ≤ min A B
  · rw [sum_Icc_dimHar k' A B J hJm]
    refine le_trans (tail_bound k' A B J hJm) ?_
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    have hD : (0:ℝ) < (B:ℝ) + k' + 1 := by positivity
    have hJB : (J:ℝ) ≤ B := by exact_mod_cast le_trans hJm (min_le_right A B)
    have ht1 : 0 ≤ 1 - (J:ℝ) / ((B:ℝ) + k' + 1) := by
      rw [sub_nonneg, div_le_one hD]; linarith
    have hexp : 1 - (J:ℝ) / ((B:ℝ) + k' + 1) ≤ Real.exp (-((J:ℝ) / ((B:ℝ) + k' + 1))) := by
      linarith [Real.add_one_le_exp (-((J:ℝ) / ((B:ℝ) + k' + 1)))]
    have hpow := pow_le_pow_left₀ ht1 hexp k'
    rw [← Real.exp_nat_mul] at hpow
    refine le_trans hpow (Real.exp_le_exp.mpr ?_)
    have hk' : (2:ℝ) ≤ k' := by exact_mod_cast hk
    have hk1 : (k':ℝ) + 1 ≠ 0 := by positivity
    have hb0 : b' ≠ 0 := hb.ne'
    have htb : La * b' / (k' + 1) / (2 * b') ≤ (J:ℝ) / ((B:ℝ) + k' + 1) := by
      calc La * b' / (k' + 1) / (2 * b') ≤ (J:ℝ) / (2 * b') :=
            div_le_div_of_nonneg_right hJ (by positivity)
        _ ≤ (J:ℝ) / ((B:ℝ) + k' + 1) := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hD hB
    have hs : La * b' / (k' + 1) / (2 * b') = La / (2 * ((k':ℝ) + 1)) := by
      field_simp <;> ring
    rw [hs] at htb
    have e3 : (k':ℝ) * (La / (2 * ((k':ℝ) + 1))) - La / 3 = La * ((k':ℝ) - 2) / (6 * ((k':ℝ) + 1)) := by
      field_simp <;> ring
    have n3 : 0 ≤ La * ((k':ℝ) - 2) / (6 * ((k':ℝ) + 1)) := by
      apply div_nonneg (mul_nonneg hLa (by linarith)) (by positivity)
    have m3 := mul_le_mul_of_nonneg_left htb (by linarith : (0:ℝ) ≤ k')
    nlinarith [m3, e3, n3]
  · push_neg at hJm
    rw [Finset.Icc_eq_empty_of_lt hJm, Finset.sum_empty, Nat.cast_zero]
    positivity

theorem harmonic_lower_bound : HarLower := by
  intro k' al be
  by_cases h : al = 0 ∨ be = 0
  · have hd : dimHar k' al be = dimPol k' al * dimPol k' be := by
      unfold dimHar; rw [if_pos h, Nat.sub_zero]
    rw [hd]
    have hP : (0:ℝ) ≤ ((dimPol k' al * dimPol k' be : ℕ) : ℝ) := Nat.cast_nonneg _
    rcases Nat.eq_zero_or_pos (be + k') with h0 | h0
    · have h0' : ((be:ℝ) + k') = 0 := by exact_mod_cast h0
      rw [h0', div_zero]; exact hP
    · have hpos : (0:ℝ) < (be:ℝ) + k' := by exact_mod_cast h0
      rw [mul_div_assoc]
      calc _ ≤ ((dimPol k' al * dimPol k' be : ℕ) : ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left _ hP
            rw [div_le_one hpos]; linarith [(Nat.cast_nonneg be : (0:ℝ) ≤ be)]
        _ = _ := mul_one _
  · push_neg at h
    obtain ⟨ha, hb⟩ := h
    have hle1 : dimPol k' (al - 1) ≤ dimPol k' al := dimPol_mono k' (Nat.sub_le _ _)
    have hrec := dimPol_mul_deg k' (be - 1)
    rw [show be - 1 + 1 = be by omega] at hrec
    have hd : dimHar k' al be = dimPol k' al * dimPol k' be - dimPol k' (al - 1) * dimPol k' (be - 1) := by
      unfold dimHar; rw [if_neg (by omega)]
    have hle2 : dimPol k' (al - 1) * dimPol k' (be - 1) ≤ dimPol k' al * dimPol k' be :=
      Nat.mul_le_mul hle1 (dimPol_mono k' (Nat.sub_le _ _))
    rw [hd, Nat.cast_sub hle2]
    push_cast
    have hbe : (0:ℝ) < be := by exact_mod_cast Nat.pos_of_ne_zero hb
    have hpos : (0:ℝ) < (be:ℝ) + k' := by positivity
    have hrec' : (dimPol k' (be - 1) : ℝ) * ((be:ℝ) + k') = dimPol k' be * be := by exact_mod_cast hrec
    have hle1' : (dimPol k' (al - 1) : ℝ) ≤ dimPol k' al := by exact_mod_cast hle1
    set Pa := (dimPol k' al : ℝ)
    set Pb := (dimPol k' be : ℝ)
    set Pa1 := (dimPol k' (al - 1) : ℝ)
    set Pb1 := (dimPol k' (be - 1) : ℝ)
    have h3 : Pa1 * (Pb * be) ≤ Pa * (Pb * be) := mul_le_mul_of_nonneg_right hle1' (by positivity)
    have h4 : Pa1 * (Pb1 * ((be:ℝ) + k')) = Pa1 * (Pb * be) := by rw [hrec']
    rw [div_le_iff₀ hpos]
    have e : (Pa * Pb - Pa1 * Pb1) * ((be:ℝ) + k') =
        Pa * Pb * k' + (Pa * (Pb * be) - Pa1 * (Pb1 * ((be:ℝ) + k'))) := by ring
    rw [e, h4]
    linarith

end Formalism.CountingSumsFrames
end
end

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.HockeyStickIdentity
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

theorem hockey_stick_identity : HockeyStick := by
  intro m B
  induction B with
  | zero => simp [dimPol]
  | succ B ih =>
    rw [Finset.sum_range_succ']
    have h1 : ∀ j ∈ range (B + 1), dimPol m (B + 1 - (j + 1)) = dimPol m (B - j) := by
      intro j _
      congr 1
      omega
    rw [Finset.sum_congr rfl h1, ih]
    simp only [dimPol, Nat.sub_zero]
    have : B + 1 + (m + 1) = (B + m + 1) + 1 := by ring
    rw [this, Nat.choose_succ_succ]
    have h2 : B + 1 + m = B + m + 1 := by ring
    have h3 : B + (m + 1) = B + m + 1 := by ring
    rw [h2, h3, add_comm]

def digitSum {m P : ℕ} (τ : Fin m → Fin P) : ℕ := ∑ i, (τ i : ℕ)

theorem digit_class_count : DigitClassCount := by
  intro m P g hP
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  let f : (Fin m → Fin (p + 1)) → Fin (p + 1) := fun τ =>
    ⟨(g + p * digitSum τ) % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩
  have hsum : ∀ ρ : Fin (m + 1) → Fin (p + 1),
      (∑ i, (ρ i : ℕ)) = (ρ 0 : ℕ) + digitSum (Fin.tail ρ) := by
    intro ρ
    rw [Fin.sum_univ_succ]
    rfl
  have hcard : (univ : Finset (Fin m → Fin (p + 1))).card = (p + 1) ^ m := by
    simp
  rw [← hcard]
  apply Finset.card_nbij' (fun ρ => Fin.tail ρ) (fun τ => Fin.cons (f τ) τ)
  · intro ρ _
    simp
  · intro τ _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [hsum]
    simp only [Fin.cons_zero, Fin.tail_cons, f]
    rw [Nat.mod_add_mod]
    have : g + p * digitSum τ + digitSum τ = g + (p + 1) * digitSum τ := by ring
    rw [this, Nat.add_mul_mod_self_left]
  · intro ρ hρ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hρ
    rw [hsum] at hρ
    have h0 : f (Fin.tail ρ) = ρ 0 := by
      apply Fin.ext
      simp only [f]
      have hlt : (ρ 0 : ℕ) < p + 1 := (ρ 0).isLt
      have hmod : (ρ 0 : ℕ) + digitSum (Fin.tail ρ) ≡ g [MOD p + 1] := hρ
      have h2 := Nat.ModEq.add_right (p * digitSum (Fin.tail ρ)) hmod
      have h3 : (ρ 0 : ℕ) + digitSum (Fin.tail ρ) + p * digitSum (Fin.tail ρ)
          = (ρ 0 : ℕ) + (p + 1) * digitSum (Fin.tail ρ) := by ring
      rw [h3] at h2
      have h4 : (ρ 0 : ℕ) ≡ g + p * digitSum (Fin.tail ρ) [MOD p + 1] := by
        have h5 : (ρ 0 : ℕ) + (p + 1) * digitSum (Fin.tail ρ) ≡ (ρ 0 : ℕ) [MOD p + 1] := by
          unfold Nat.ModEq
          rw [Nat.add_mul_mod_self_left]
        exact h5.symm.trans h2
      unfold Nat.ModEq at h4
      rw [Nat.mod_eq_of_lt hlt] at h4
      exact h4.symm
    simp only
    rw [h0, Fin.cons_self_tail]
  · intro τ _
    simp

theorem digit_step (P g e : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hkey : ∀ j : ℕ, (1 - t) * ((g : ℝ) + j + 1) ≤ (P : ℝ) * ((e : ℝ) + j + 1)) :
    ∀ j : ℕ, (1 - (j : ℝ) * t) * ((g + j).choose j : ℝ) ≤ (P : ℝ) ^ j * ((e + j).choose j : ℝ) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hg : ((g + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((g : ℝ) + j + 1) * ((g + j).choose j : ℝ) := by
      have := Nat.add_one_mul_choose_eq (g + j) j
      have h' : g + (j + 1) = g + j + 1 := by ring
      rw [h']
      have hc : (((g + j + 1) * (g + j).choose j : ℕ) : ℝ)
          = (((g + j + 1).choose (j + 1) * (j + 1) : ℕ) : ℝ) := by
        rw [this]
      push_cast at hc
      linarith
    have he : ((e + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((e : ℝ) + j + 1) * ((e + j).choose j : ℝ) := by
      have := Nat.add_one_mul_choose_eq (e + j) j
      have h' : e + (j + 1) = e + j + 1 := by ring
      rw [h']
      have hc : (((e + j + 1) * (e + j).choose j : ℕ) : ℝ)
          = (((e + j + 1).choose (j + 1) * (j + 1) : ℕ) : ℝ) := by
        rw [this]
      push_cast at hc
      linarith
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hCg : (0 : ℝ) ≤ ((g + j).choose j : ℝ) := by positivity
    have hCe : (0 : ℝ) ≤ ((e + j).choose j : ℝ) := by positivity
    have hRHS : (0 : ℝ) ≤ (P : ℝ) ^ (j + 1) * ((e + (j + 1)).choose (j + 1) : ℝ) := by positivity
    push_cast
    by_cases hneg : 1 - ((j : ℝ) + 1) * t ≤ 0
    · have : (1 - ((j : ℝ) + 1) * t) * ((g + (j + 1)).choose (j + 1) : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith
    push Not at hneg
    have hA : 0 ≤ 1 - (j : ℝ) * t := by nlinarith
    have hB : 0 ≤ 1 - t := by nlinarith
    have hG : (0 : ℝ) ≤ (g : ℝ) + j + 1 := by positivity

    rw [← mul_le_mul_iff_of_pos_right hj1]
    have hL : (1 - ((j : ℝ) + 1) * t) * ((g + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = (1 - ((j : ℝ) + 1) * t) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ)) := by
      rw [mul_assoc, hg]
    have hR : (P : ℝ) ^ (j + 1) * ((e + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((P : ℝ) ^ j * ((e + j).choose j : ℝ)) * ((P : ℝ) * ((e : ℝ) + j + 1)) := by
      rw [mul_assoc, he, pow_succ]; ring
    rw [hL, hR]
    have h1 : (1 - ((j : ℝ) + 1) * t) ≤ (1 - (j : ℝ) * t) * (1 - t) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) (mul_nonneg ht ht)]
    calc (1 - ((j : ℝ) + 1) * t) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ))
        ≤ ((1 - (j : ℝ) * t) * (1 - t)) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((1 - (j : ℝ) * t) * ((g + j).choose j : ℝ)) * ((1 - t) * ((g : ℝ) + j + 1)) := by ring
      _ ≤ ((P : ℝ) ^ j * ((e + j).choose j : ℝ)) * ((P : ℝ) * ((e : ℝ) + j + 1)) :=
          mul_le_mul ih (hkey j) (by positivity) (by positivity)

theorem digit_class_size : DigitClassSize := by
  intro m P g e hP hg he
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by positivity
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg
  set t : ℝ := ((m : ℝ) + 1) * P / g with ht_def
  have ht : 0 ≤ t := by positivity
  have hgle : (g : ℝ) ≤ P * ((e : ℝ) + (m + 1)) := by
    have : (g : ℝ) / P ≤ (e : ℝ) + (m + 1) := by linarith
    rw [div_le_iff₀ hPpos] at this
    linarith
  have htg : t * g = ((m : ℝ) + 1) * P := by
    rw [ht_def]; field_simp
  have hkey : ∀ j : ℕ, (1 - t) * ((g : ℝ) + j + 1) ≤ (P : ℝ) * ((e : ℝ) + j + 1) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have htj : 0 ≤ t * ((j : ℝ) + 1) := by positivity
    nlinarith
  have main := digit_step P g e t ht hkey m
  have hdim : ∀ d, (dimPol m d : ℝ) = ((d + m).choose m : ℝ) := fun d => rfl
  rw [hdim, hdim]
  have hfac : 1 - ((m : ℝ) + 1) ^ 2 * P / g ≤ 1 - (m : ℝ) * t := by
    have : ((m : ℝ) + 1) ^ 2 * P / g = ((m : ℝ) + 1) * t := by
      rw [ht_def]; ring
    rw [this]
    nlinarith
  calc (1 - ((m : ℝ) + 1) ^ 2 * P / g) * ((g + m).choose m : ℝ)
      ≤ (1 - (m : ℝ) * t) * ((g + m).choose m : ℝ) :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ ≤ (P : ℝ) ^ m * ((e + m).choose m : ℝ) := main

end Formalism.CountingSumsFrames
end
end

