import Formalism.BranchSandwichDivisors.StatementR

-- bundled from Formalism.BranchSandwichDivisors.BranchIsometryProofs.MemBranchRangeOfDefectEq
section
open Finset

namespace Formalism.BranchingDeterminantCap

theorem memBranchRangeOfDefectEq : ConstituentRange := by
  unfold ConstituentRange
  intro n lam sg mu h1 h2 h3 i
  unfold Interlace at h1 h2
  have hmu := h2 i
  have hle : mu i - lam i.succ ≤ d0 lam mu := by
    unfold d0
    exact Finset.single_le_sum (f := fun j => mu j - lam j.succ)
      (fun j _ => sub_nonneg.mpr (h2 j).2) (Finset.mem_univ i)
  unfold rset
  rw [Finset.mem_Icc]
  refine ⟨hmu.2, le_min hmu.1 ?_⟩
  linarith

end Formalism.BranchingDeterminantCap
end

-- bundled from Formalism.BranchSandwichDivisors.BranchIsometryProofs.StepDiii
section
open Finset

namespace Formalism.BranchingDeterminantCap

theorem heightSumBound : BranchSandwichDiii := by
  intro Pl _ TT _ hP logT ev aT bT nτ lam1 D0 D1 logc logxi a La L m f k N S η b' CT Cev
    h0 hc hxi hn hTT hnT hD0 hD1 hb hT0 hT1 hCT hL hLa hl0 hl1 hm1 hmN hk hS hη hb' hcard hev hCev
  have hN1 : 0 ≤ N - 1 := by linarith
  have hN : 0 ≤ N := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hmη : 0 ≤ m * η := mul_nonneg hm0 hη
  have hηm : η ≤ m * η := by nlinarith
  have hTA : logT ≤ CT * N * La := by
    have h1 : CT * m * L ≤ CT * m * La := mul_le_mul_of_nonneg_left hL (mul_nonneg hCT hm0)
    have h2 : CT * m * La ≤ CT * N * La :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmN hCT) hLa
    linarith
  have hNT : N / 2 * logT ≤ N / 2 * (CT * N * La) := mul_le_mul_of_nonneg_left hTA (by linarith)
  have hxi' : ∀ τ, logxi τ ≤ N ^ 2 * La := by
    intro τ
    have q1 : N * (N - 1) / 2 ≤ N * N / 2 := by nlinarith
    have q2 : N * (N - 1) / 2 * Real.log (2 * a) ≤ N * N / 2 * (2 * La) :=
      mul_le_mul q1 hl1 hl0 (by nlinarith)
    nlinarith [hxi τ]
  have gen : ∀ τ, ∀ B : ℝ, 0 ≤ B → D0 τ ≤ S + m * η + B →
      D0 τ * logT ≤ (S + m * η + B) * (CT * N * La) ∧
        logc τ ≤ N * (4 * S + 4 * (m * η) + 3 * B) * (2 * La) := by
    intro τ B hB hDB
    have hX : 0 ≤ S + m * η + B := by linarith
    refine ⟨(mul_le_mul_of_nonneg_right hDB hT0).trans (mul_le_mul_of_nonneg_left hTA hX), ?_⟩
    have hD1' : D1 τ ≤ 3 * (S + m * η + B) + S + η := by linarith [hD1 τ]
    have hQ : 0 ≤ 3 * (S + m * η + B) + S + η := by linarith
    have q1 : (N - 1) * D1 τ * Real.log (2 * a) ≤
        (N - 1) * (3 * (S + m * η + B) + S + η) * Real.log (2 * a) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD1' hN1) hl0
    have q2 : (N - 1) * (3 * (S + m * η + B) + S + η) * Real.log (2 * a) ≤
        N * (3 * (S + m * η + B) + S + η) * (2 * La) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hQ) hl1 hl0 (mul_nonneg hN hQ)
    have q3 : N * (3 * (S + m * η + B) + S + η) * (2 * La) ≤
        N * (4 * S + 4 * (m * η) + 3 * B) * (2 * La) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hN) (by linarith)
    linarith [hc τ]
  have key : ∀ τ, -(nτ τ * logT) + (2 * logc τ + logxi τ) ≤
      (if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) +
        ((CT + 16) * ((m * η + S) * N) + (CT / 2 + 1) * N ^ 2) * La := by
    intro τ
    have hD := hD0 τ
    by_cases hτ : τ ∈ TT
    · rw [if_pos hτ] at hD ⊢
      obtain ⟨e1, e2⟩ := gen τ b' hb' (by linarith [hb τ hτ])
      have e4 : (N - k) / 2 * logT ≤ N / 2 * logT := mul_le_mul_of_nonneg_right (by linarith) hT0
      rw [hn τ, hTT τ hτ]
      linarith [hxi' τ]
    · rw [if_neg hτ] at hD ⊢
      obtain ⟨e1, e2⟩ := gen τ 0 le_rfl (by linarith)
      have e4 : -lam1 τ * logT ≤ N / 2 * logT :=
        mul_le_mul_of_nonneg_right (by linarith [hnT τ hτ]) hT0
      rw [hn τ]
      linarith [hxi' τ]
  have hsum : -(∑ τ, nτ τ * logT) + ∑ τ, (2 * logc τ + logxi τ) =
      ∑ τ, (-(nτ τ * logT) + (2 * logc τ + logxi τ)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hsk := Finset.sum_le_sum (fun τ (_ : τ ∈ Finset.univ) => key τ)
  have hsplit : ∑ τ, ((if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) +
        ((CT + 16) * ((m * η + S) * N) + (CT / 2 + 1) * N ^ 2) * La) =
      ∑ τ, (if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) +
        (Fintype.card Pl : ℝ) * (((CT + 16) * ((m * η + S) * N) + (CT / 2 + 1) * N ^ 2) * La) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfilt : Finset.univ.filter (fun τ => τ ∈ TT) = TT := by
    ext x
    simp
  have hite : ∑ τ, (if τ ∈ TT then -(aT τ * logT) + (CT + 12) * b' * N * La else 0) =
      -(∑ t ∈ TT, aT t * logT) + (TT.card : ℝ) * ((CT + 12) * b' * N * La) := by
    rw [← Finset.sum_filter, hfilt, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      nsmul_eq_mul]
  have hf0 : 0 ≤ f := le_trans (Nat.cast_nonneg _) hcard
  have hc2 : 0 ≤ ((CT + 16) * ((m * η + S) * N) + (CT / 2 + 1) * N ^ 2) * La := by
    have : 0 ≤ (CT + 16) * ((m * η + S) * N) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hN)
    have : 0 ≤ (CT / 2 + 1) * N ^ 2 := mul_nonneg (by linarith) (sq_nonneg N)
    exact mul_nonneg (by linarith) hLa
  have hcc := mul_le_mul_of_nonneg_right hcard hc2
  have hTT0 : (0 : ℝ) ≤ TT.card := Nat.cast_nonneg _
  have d1 : 0 ≤ (TT.card : ℝ) * b' * N * La * (4 + Cev) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hTT0 hb') hN) hLa) (by linarith)
  have d2 : 0 ≤ f * (m * η + S) * N * La * Cev :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hf0 (by linarith)) hN) hLa) hCev
  have d3 : 0 ≤ f * N ^ 2 * La * (15 + CT / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg hf0 (sq_nonneg N)) hLa) (by linarith)
  linarith

end Formalism.BranchingDeterminantCap
end

-- bundled from Formalism.BranchSandwichDivisors.BranchIsometryProofs.TransferMean
section
open Finset

namespace Formalism.BranchingDeterminantCap

theorem degreeTransferBound : TransferDeg := by
  unfold TransferDeg
  intro S _ rk nS dgA dgB la degP h1 h2 h3 hla hR
  have hR0 : 0 ≤ ∑ s, nS s * rk s := Finset.sum_nonneg fun s _ => hR s
  have hBA : |∑ s, dgB s - ∑ s, nS s * dgA s| ≤ 13 / 2 * la * ∑ s, nS s * rk s := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => h1 s)
  have hlR : 0 ≤ la * ∑ s, nS s * rk s := mul_nonneg hla hR0
  rw [abs_le] at hBA ⊢
  obtain ⟨hBA1, hBA2⟩ := hBA
  constructor <;> linarith

theorem meanTransferBound : TransferMean := by
  unfold TransferMean
  intro S _ rk nS dg nbar de la ka HH0 muP0 muPs muR0 muRs hnbar hde0 hde13 hla hka hrk hR hn
    hR0 hRs hdg hPs hP0
  rw [abs_le] at hR0 hRs
  obtain ⟨hR0a, hR0b⟩ := hR0
  obtain ⟨hRsa, hRsb⟩ := hRs
  have hD : ∑ s, dg s ≤ (∑ s, rk s) * (HH0 + ka * la) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun s _ => hdg s
  have hWlo : (1 - de) * nbar * ∑ s, rk s ≤ ∑ s, nS s * rk s := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hn s).1 (hrk s)
  have hmuP0 : muP0 ≤ HH0 + ka * la + 2 * la := by
    have h : muP0 * ∑ s, rk s ≤ (HH0 + ka * la + 2 * la) * ∑ s, rk s := by linarith
    exact le_of_mul_le_mul_right h hR
  refine ⟨by linarith, ?_⟩
  have hW : 0 < ∑ s, nS s * rk s := by
    have : 0 < (1 - de) * nbar * ∑ s, rk s := mul_pos (mul_pos (by linarith) hnbar) hR
    linarith
  have key : ∑ s, ((HH0 + ka * la) * (nS s * rk s) - (1 + de) * nbar * ((HH0 + ka * la) * rk s)
      + (1 + de) * nbar * dg s) ≤ ∑ s, nS s * dg s := by
    refine Finset.sum_le_sum fun s _ => ?_
    nlinarith [mul_nonneg (sub_nonneg.2 (hdg s)) (sub_nonneg.2 (hn s).2)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at key
  have hnn : 0 ≤ (1 + de) * nbar := mul_nonneg (by linarith) hnbar.le
  have h3 : (1 + de) * nbar * (muP0 * ∑ s, rk s) ≤
      (1 + de) * nbar * ((∑ s, dg s) + 2 * la * ∑ s, rk s) :=
    mul_le_mul_of_nonneg_left hP0 hnn
  have hY : 0 ≤ (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0) :=
    mul_nonneg (by linarith) (by linarith)
  have h1 : (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0) * ((1 - de) * nbar * ∑ s, rk s) ≤
      (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0) * ∑ s, nS s * rk s :=
    mul_le_mul_of_nonneg_left hWlo hY
  have h2 : 0 ≤ (HH0 + ka * la + 2 * la - muP0) * nbar * (∑ s, rk s) * (de * (1 - 3 * de)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hnbar.le) hR.le)
      (mul_nonneg hde0 (by linarith))
  have hmain : (-muPs) * ∑ s, nS s * rk s ≤
      (17 / 2 * la - (HH0 + ka * la) + (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0)) *
        ∑ s, nS s * rk s := by
    linarith
  have hmuPs := le_of_mul_le_mul_right hmain hW
  have hXY : 3 * de * (HH0 + ka * la + 2 * la - muP0) ≤
      3 * de * (-muR0 + HH0 + (2 * ka + 2) * la) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

theorem meanShiftAssembly : PassageAssembly := by
  unfold PassageAssembly
  intro S _ rk nS dg nbar lam0 HH0 muP0 muPs mu0 muC f r g Q C0 hnbar hlam0 hrk hR hf hr hg hn
    h0 hC hdg hPs hP0 hZQ hQ hfrQ hC0
  have hde0 : 0 ≤ 8 * f * r / g :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hf) hr) hg.le
  have hdeQ : 8 * f * r / g * (3 * Q) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hg]
    linarith
  have hMT := meanTransferBound
  unfold TransferMean at hMT
  set de := 8 * f * r / g with hde
  have hde13 : de ≤ 1 / 3 := by nlinarith [mul_nonneg hde0 (sub_nonneg.2 hQ)]
  obtain ⟨_, hB⟩ := hMT S rk nS dg nbar de lam0 1 HH0 muP0 muPs (-mu0) (-muC) hnbar hde0 hde13
    hlam0 zero_le_one hrk hR hn (by rw [one_mul]; exact h0) (by rw [one_mul]; exact hC)
    (fun s => by rw [one_mul]; exact hdg s) hPs hP0
  have hZ : 3 * de * (mu0 + HH0 + 4 * lam0) ≤ 3 * de * Q :=
    mul_le_mul_of_nonneg_left hZQ (by linarith)
  have hC' : 0 ≤ (C0 - 25 / 2) * lam0 := mul_nonneg (by linarith) hlam0
  constructor <;> linarith

end Formalism.BranchingDeterminantCap
end

