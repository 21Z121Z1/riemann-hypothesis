import Mathlib
import Formalism.FrobeniusContraction.Bundle0002
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.Bundle0001
import Formalism.EisensteinCokernelLengths.RationalTailBound
import Formalism.EisensteinCokernelLengths.Bundle0001
import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt

-- bundled from Formalism.EisensteinCokernelLengths.FactorialValuationBounds.FactorialValuationBoundsProofFact
section
namespace Formalism.ZetaNonvanishing.ARCV

open Polynomial

theorem range_sdiff_range (H : ℕ) : Finset.range (2 * H) \ Finset.range H = Finset.Ico H (2 * H) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
  omega

end Formalism.ZetaNonvanishing.ARCV
end

-- bundled from Formalism.EisensteinCokernelLengths.FactorialValuationBounds.GaussRam
section
open scoped ENNReal

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

private theorem le_addVal_of_mem_span_pow {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} {c : O}
    (hc : c ∈ Ideal.span {ϖ ^ e}) : (e : ℕ∞) ≤ IsDiscreteValuationRing.addVal O c := by
  rw [Ideal.mem_span_singleton] at hc
  have h := (IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).2 hc
  rwa [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    nsmul_one] at h

private theorem addVal_eq_of_mem_span_pow_not_mem_succ {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} {c : O}
    (h1 : c ∈ Ideal.span {ϖ ^ e}) (h2 : c ∉ Ideal.span {ϖ ^ (e + 1)}) :
    IsDiscreteValuationRing.addVal O c = e := by
  refine le_antisymm ?_ (le_addVal_of_mem_span_pow hϖ h1)
  by_contra h
  rw [not_le] at h
  apply h2
  rw [Ideal.mem_span_singleton]
  apply (IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).1
  rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    nsmul_one, Nat.cast_succ]
  exact Order.add_one_le_of_lt h

theorem gaussValEisenstein : GaussEisRam := by
  intro O _ _ _ ϖ hϖ e he x hx E N hN hE
  obtain ⟨hmon, hdeg, hcoef, h0⟩ := hE
  have hc0 : IsDiscreteValuationRing.addVal O (E.coeff 0) = e :=
    addVal_eq_of_mem_span_pow_not_mem_succ hϖ (hcoef 0 (by omega)) h0
  have hcN : E.coeff N = 1 := by
    have := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at this
  unfold Formalism.NOK.gaussV
  simp only [Polynomial.coeff_coe]
  apply le_antisymm
  · have h1 := iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) +
      ENNReal.ofReal (x * n)) 0
    have h2 := iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) +
      ENNReal.ofReal (x * n)) N
    simp only [hc0, hcN, AddValuation.map_one, ENat.toENNReal_zero, ENat.toENNReal_coe,
      Nat.cast_zero, mul_zero, ENNReal.ofReal_zero, add_zero, zero_add] at h1 h2
    rcases le_total (e : ℝ) (x * N) with h | h
    · rw [min_eq_left h, ENNReal.ofReal_natCast]
      exact h1
    · rw [min_eq_right h]
      exact h2
  · apply le_iInf
    intro n
    rcases lt_trichotomy n N with h | h | h
    · have hv := le_addVal_of_mem_span_pow hϖ (hcoef n h)
      calc ENNReal.ofReal (min (e : ℝ) (x * N)) ≤ ENNReal.ofReal (e : ℝ) :=
            ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = ((e : ℕ∞) : ℝ≥0∞) := by rw [ENNReal.ofReal_natCast, ENat.toENNReal_coe]
        _ ≤ ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) :=
            ENat.toENNReal_le.2 hv
        _ ≤ _ := le_self_add
    · subst h
      rw [hcN, AddValuation.map_one, ENat.toENNReal_zero, zero_add]
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact h)]
      simp

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
end

-- bundled from Formalism.EisensteinCokernelLengths.FactorialValuationBounds.LagrangeIdealSgProof
section
namespace Formalism.ZetaNonvanishing.LIFTV

theorem lagrangeIdealSg_proof : LagrangeIdealSg := by
  intro ℓ _ R _ _ sg S₁ S₂ c hd hc
  exact Formalism.LIFT.lift_LagrangeIdeal R (ℓ : R) ℤ S₁ S₂ c (fun a b => sg + padicValInt ℓ (a - b)) hd hc

theorem windowDiff_proof : WindowDiff := by
  unfold WindowDiff
  intro ℓ hℓ a₀ y D S a hS hD
  have hp : ℓ.Prime := hℓ.out
  have hl1 : 1 < ℓ := hp.one_lt
  have hlR : (1 : ℝ) < ℓ := by exact_mod_cast hl1
  set K := Nat.log ℓ D with hK

  have hv : ∀ b ∈ S.erase a, padicValInt ℓ (a - b) =
      ((Finset.Icc 1 K).filter (fun k => (ℓ : ℤ) ^ k ∣ a - b)).card := by
    intro b hb
    have hne : a - b ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm
    have hle : padicValInt ℓ (a - b) ≤ K := by
      have h1 : (ℓ : ℤ) ^ padicValInt ℓ (a - b) ≤ |a - b| :=
        Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr (padicValInt_dvd (a - b)))
      have h3 : ℓ ^ padicValInt ℓ (a - b) ≤ D := by
        have h4 := le_trans h1 (hD b (Finset.mem_of_mem_erase hb))
        exact_mod_cast h4
      exact Nat.le_log_of_pow_le hl1 h3
    have hset : (Finset.Icc 1 K).filter (fun k => (ℓ : ℤ) ^ k ∣ a - b) =
        Finset.Icc 1 (padicValInt ℓ (a - b)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, padicValInt_dvd_iff, hne, false_or]
      omega
    rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  have hsum : ∑ b ∈ S.erase a, padicValInt ℓ (a - b) =
      ∑ k ∈ Finset.Icc 1 K, ((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card := by
    rw [Finset.sum_congr rfl hv]
    simp only [Finset.card_filter]
    exact Finset.sum_comm

  have hk : ∀ k ∈ Finset.Icc 1 K, ((((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card : ℕ) : ℝ)
      ≤ ((y : ℝ) + 1) / (ℓ : ℝ) ^ k + 1 := by
    intro k _
    have hM : (0 : ℤ) < (ℓ : ℤ) ^ k := by positivity
    have hsub : (S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b) ⊆
        (Finset.Ico a₀ (a₀ + y + 1)).filter (fun x => x ≡ a [ZMOD (ℓ : ℤ) ^ k]) := by
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      have hbS := hS (Finset.mem_of_mem_erase hb.1)
      rw [Finset.mem_Icc] at hbS
      exact ⟨Finset.mem_Ico.mpr ⟨hbS.1, by omega⟩, Int.modEq_iff_dvd.mpr hb.2⟩
    have hcard := Int.Ico_filter_modEq_card a₀ (a₀ + y + 1) hM a
    have hle := Finset.card_le_card hsub
    have hMq : (0 : ℚ) < (ℓ : ℚ) ^ k := by positivity
    have hq : ((((Finset.Ico a₀ (a₀ + y + 1)).filter (fun x => x ≡ a [ZMOD (ℓ : ℤ) ^ k])).card : ℤ) : ℚ)
        ≤ ((y : ℚ) + 1) / (ℓ : ℚ) ^ k + 1 := by
      rw [hcard]
      push_cast
      apply max_le
      · have e1 := Int.ceil_lt_add_one (((a₀ : ℚ) + y + 1 - a) / (ℓ : ℚ) ^ k)
        have e2 := Int.le_ceil (((a₀ : ℚ) - a) / (ℓ : ℚ) ^ k)
        have e3 : ((a₀ : ℚ) + y + 1 - a) / (ℓ : ℚ) ^ k - ((a₀ : ℚ) - a) / (ℓ : ℚ) ^ k
            = ((y : ℚ) + 1) / (ℓ : ℚ) ^ k := by
          rw [← sub_div]
          ring
        linarith
      · positivity
    have hq2 : ((((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card : ℕ) : ℚ)
        ≤ ((y : ℚ) + 1) / (ℓ : ℚ) ^ k + 1 := by
      have h5 : ((((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card : ℕ) : ℚ)
          ≤ ((((Finset.Ico a₀ (a₀ + y + 1)).filter (fun x => x ≡ a [ZMOD (ℓ : ℤ) ^ k])).card : ℤ) : ℚ) := by
        exact_mod_cast hle
      linarith
    have hq3 := (Rat.cast_le (K := ℝ)).mpr hq2
    push_cast at hq3
    exact hq3
  have hgeo : ∑ k ∈ Finset.Icc 1 K, ((ℓ : ℝ)⁻¹) ^ k ≤ 1 / ((ℓ : ℝ) - 1) := by
    have h0 : (0 : ℝ) ≤ (ℓ : ℝ)⁻¹ := by positivity
    have h1 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlR
    have h2 := geom_sum_Ico_le_of_lt_one (m := 1) (n := K + 1) h0 h1
    have hI : Finset.Ico 1 (K + 1) = Finset.Icc 1 K := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hI] at h2
    have hl0 : (ℓ : ℝ) ≠ 0 := by positivity
    have hl1' : (ℓ : ℝ) - 1 ≠ 0 := by linarith
    have e : (ℓ : ℝ)⁻¹ ^ 1 / (1 - (ℓ : ℝ)⁻¹) = 1 / ((ℓ : ℝ) - 1) := by
      field_simp
    linarith
  have hsumk : ∑ k ∈ Finset.Icc 1 K, (((y : ℝ) + 1) / (ℓ : ℝ) ^ k + 1)
      = ((y : ℝ) + 1) * ∑ k ∈ Finset.Icc 1 K, ((ℓ : ℝ)⁻¹) ^ k + K := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [div_eq_mul_inv, inv_pow]
  have hlog : (K : ℝ) ≤ Real.logb ℓ D := Real.natLog_le_logb D ℓ
  have hy : (0 : ℝ) ≤ (y : ℝ) + 1 := by positivity
  rw [hsum]
  push_cast
  calc _ ≤ ∑ k ∈ Finset.Icc 1 K, (((y : ℝ) + 1) / (ℓ : ℝ) ^ k + 1) := Finset.sum_le_sum hk
    _ = ((y : ℝ) + 1) * ∑ k ∈ Finset.Icc 1 K, ((ℓ : ℝ)⁻¹) ^ k + K := hsumk
    _ ≤ ((y : ℝ) + 1) * (1 / ((ℓ : ℝ) - 1)) + Real.logb ℓ D := by gcongr
    _ = ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by ring

end Formalism.ZetaNonvanishing.LIFTV
end

-- bundled from Formalism.EisensteinCokernelLengths.FactorialValuationBounds.RationalTailBoundCubic
section
noncomputable section

namespace Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

theorem exponentChainBound : ExponentChainBound := by
  unfold ExponentChainBound
  intro ℓ b b' S E lam σ₂ h'' c' hℓ hb hS hE hσ hlam hc
  have h1 : 0 < ℓ - 1 := by linarith
  have h0 : 0 < ℓ := by linarith
  have h1' : ℓ - 1 ≠ 0 := h1.ne'
  have h0' : ℓ ≠ 0 := h0.ne'
  have key : b / (ℓ - 1) - b / ℓ = b / (ℓ * (ℓ - 1)) := by
    field_simp; ring
  have hS1 : (S + 1) / (ℓ - 1) ≤ S + 1 := div_le_self (by linarith) (by linarith)
  have hsplit : ((b + S) + 1) / (ℓ - 1) = b / (ℓ - 1) + (S + 1) / (ℓ - 1) := by ring
  have hnn : 0 ≤ b / (ℓ * (ℓ - 1)) := div_nonneg hb (mul_pos h0 h1).le
  apply max_le
  · linarith
  · linarith

lemma numC_cubic (ℓ : ℝ) (hℓ : 11 ≤ ℓ) :
    8 * (2 * ℓ - 1) * ℓ ^ 2 + 8 * ℓ ^ 2 * (ℓ - 1) + ℓ * (ℓ - 1) ^ 2 ≤ 3111 / 100 * (ℓ - 1) ^ 3 := by
  have ht : 0 ≤ ℓ - 11 := by linarith
  nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]

theorem rationalTailBoundCubic : NumC := by
  unfold NumC
  intro ℓ hℓ
  have h1 : 0 < ℓ - 1 := by linarith
  have h0 : 0 < ℓ := by linarith
  have h1' : ℓ - 1 ≠ 0 := h1.ne'
  have h0' : ℓ ≠ 0 := h0.ne'
  have key := numC_cubic ℓ hℓ
  have e : 8 * (2 * ℓ - 1) / (ℓ - 1) ^ 3 + 8 / (ℓ - 1) ^ 2 + 1 / (ℓ * (ℓ - 1)) =
      (8 * (2 * ℓ - 1) * ℓ ^ 2 + 8 * ℓ ^ 2 * (ℓ - 1) + ℓ * (ℓ - 1) ^ 2) / (ℓ ^ 2 * (ℓ - 1) ^ 3) := by
    field_simp
  have c : (31.11 : ℝ) = 3111 / 100 := by norm_num
  rw [e, div_le_div_iff₀ (mul_pos (pow_pos h0 2) (pow_pos h1 3)) (pow_pos h0 2), c]
  nlinarith [mul_le_mul_of_nonneg_right key (sq_nonneg ℓ)]

end Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
end
end

