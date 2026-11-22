import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0006
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ValuationOneEqZero

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.FrMemLetters
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Ord

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

theorem llPos_lt (j : ℤ) (l l' : ℕ) (hll : l < l') (hl' : l' < (Fr.LLset j).card) : llPos Fr j l < llPos Fr j l' := by
  unfold llPos
  have hs := (Finset.sortedLT_sort (Fr.LLset j)).strictMono_get
  have hlen : ((Fr.LLset j).sort (· ≤ ·)).length = (Fr.LLset j).card := Finset.length_sort _
  have e : ∀ k (hk : k < (Fr.LLset j).card), ((Fr.LLset j).sort (· ≤ ·)).getD k 0 =
      ((Fr.LLset j).sort (· ≤ ·))[k]'(by rw [hlen]; exact hk) := by
    intro k hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hlen, hk]
  rw [e l (by omega), e l' hl']
  exact hs (a := ⟨l, by rw [hlen]; omega⟩) (b := ⟨l', by rw [hlen]; exact hl'⟩) hll

private theorem fr_le_fr_of_le_of_valid (hV : Fr.Valid L₁ N₁) (j : ℤ) :
    ∀ i i', i ≤ i' → i' < r → Fr.fr j i ≤ Fr.fr j i' := by
  intro i i' hii' hi'
  induction i', hii' using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (ih (by omega)).trans (hV.2.2.1 j k (by omega)).le

private theorem llPos_mem_LLset' (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) : llPos Fr j l ∈ Fr.LLset j := by
  unfold llPos
  have hlen : ((Fr.LLset j).sort (· ≤ ·)).length = (Fr.LLset j).card := Finset.length_sort _
  have e : ((Fr.LLset j).sort (· ≤ ·)).getD l 0 =
      ((Fr.LLset j).sort (· ≤ ·))[l]'(by rw [hlen]; exact hl) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hlen, hl]
  rw [e, ← Finset.mem_sort (· ≤ ·)]
  exact List.getElem_mem _

theorem posU_lt (hV : Fr.Valid L₁ N₁) (j : ℤ) (a b : ℕ) (hab : a < b) (hb : b < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j a < posU Fr (Fr.LLset j).card j b := by
  have hm := fr_le_fr_of_le_of_valid hV j
  unfold posU
  split_ifs with ha hb hb
  · exact llPos_lt j a b hab hb
  · have h1 := llPos_mem_LLset' j a ha
    simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at h1
    exact lt_of_lt_of_le h1.1.2 (hm 0 (b - (Fr.LLset j).card) (Nat.zero_le _) (by omega))
  · omega
  · exact (hV.2.2.1 j (a - (Fr.LLset j).card) (by omega)).trans_le (hm _ _ (by omega) (by omega))

theorem posU_lt_iff (hV : Fr.Valid L₁ N₁) (j : ℤ) (a b : ℕ) (ha : a < (Fr.LLset j).card + r)
    (hb : b < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j a < posU Fr (Fr.LLset j).card j b ↔ a < b := by
  refine ⟨fun h => ?_, fun h => posU_lt hV j a b h hb⟩
  by_contra hn
  push_neg at hn
  rcases hn.lt_or_eq with h2 | h2
  · exact lt_asymm h (posU_lt hV j b a h2 ha)
  · subst h2
    exact lt_irrefl _ h

theorem posU_le_iff (hV : Fr.Valid L₁ N₁) (j : ℤ) (a b : ℕ) (ha : a < (Fr.LLset j).card + r)
    (hb : b < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j a ≤ posU Fr (Fr.LLset j).card j b ↔ a ≤ b := by
  rw [← not_lt, posU_lt_iff hV j b a hb ha, not_lt]

theorem posU_ll (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) : posU Fr (Fr.LLset j).card j l = llPos Fr j l := by
  unfold posU
  rw [if_pos hl]

theorem posU_fr (j : ℤ) (i : ℕ) : posU Fr (Fr.LLset j).card j ((Fr.LLset j).card + i) = Fr.fr j i := by
  unfold posU
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem w_lt_posU (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (i u : ℕ) (hi : i < r) (hu : u < (Fr.LLset j).card + r) :
    Fr.fr (j - 1) i < posU Fr (Fr.LLset j).card j u := by
  have hfi : Fr.fr (j - 1) i ≤ Fr.fr (j - 1) (r - 1) := fr_le_fr_of_le_of_valid hV (j - 1) i (r - 1) (by omega) (by omega)
  have hgap : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
    have h1 := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at h1
  unfold posU
  split_ifs with hu'
  · have h1 := llPos_mem_LLset' j u hu'
    simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at h1
    exact lt_of_le_of_lt hfi h1.1.1
  · exact lt_of_le_of_lt hfi (lt_of_lt_of_le hgap (fr_le_fr_of_le_of_valid hV j 0 _ (Nat.zero_le _) (by omega)))

theorem fr_mem_letters (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (i : ℕ) (hi : i < r) : Fr.fr j i ∈ Fr.letters j := by
  have hm0 := fr_le_fr_of_le_of_valid hV (j - 1)
  have hm := fr_le_fr_of_le_of_valid hV j
  have hgap : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
    have h1 := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at h1
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, hm i (r - 1) (by omega) (by omega)⟩, (hV.2.2.2.2.1 j i hi).1⟩
  exact (hm0 0 (r - 1) (Nat.zero_le _) (by omega)).trans (hgap.le.trans (hm 0 i (Nat.zero_le _) hi))

theorem w_mem_letters (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (i : ℕ) (hi : i < r) :
    Fr.fr (j - 1) i ∈ Fr.letters j := by
  have hm0 := fr_le_fr_of_le_of_valid hV (j - 1)
  have hm := fr_le_fr_of_le_of_valid hV j
  have hgap : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
    have h1 := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at h1
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨hm0 0 i (Nat.zero_le _) hi, ?_⟩, (hV.2.2.2.2.1 (j - 1) i hi).1⟩
  exact (hm0 i (r - 1) (by omega) (by omega)).trans
    (hgap.le.trans (hm 0 (r - 1) (Nat.zero_le _) (by omega)))

end Ord

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Imports
section

end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SizeStepAlt
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem sizeStep' : ∃ CDn C₁ : ℝ, 0 < CDn ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ,
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (_hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ [NeZero F.J],
      SizeAt (K := K) p F (fun j : ZMod F.J => (F.LLset (segZ j)).card) (dT TT lam0)
        (CDn * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a)) ∧
      (∀ (j : ZMod F.J) (u : ℕ), u < (fun j : ZMod F.J => (F.LLset (segZ j)).card) j + r →
        3 / 8 * slU F p (flatDeg lam0) Y (r + K) (fun j : ZMod F.J => (F.LLset (segZ j)).card) j u <
          Bo p F (flatDeg lam0) (segZ j) (posU F ((fun j : ZMod F.J => (F.LLset (segZ j)).card) j) (segZ j) u) / 2) ∧
      1 ≤ cPrime n' r TT.card c0 cpp cStar ∧ 1 ≤ F.J := by
  refine ⟨9, 4, by norm_num, by norm_num, ?_⟩
  intro C hC CLa p W Qq O Kf
  intro _ _ _ _ _ _ _ _ _ _
  intro ι σ j w n' m r
  intro _ _
  intro TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K
  intro _ _
  intro hk F nb B hD _
  have hD' := hD
  unfold DataII at hD'
  obtain ⟨-, hH, hF, -⟩ := hD'
  have hka : ((m + 1 : ℕ) : ℝ) ≤ a := k_le_a (by linarith) hH
  have hH' := hH
  unfold Hyps at hH'
  obtain ⟨hp13, hr2, hOrb, hN, hW, hY, -, hgap, -, -, hcs, hlast⟩ := hH'
  have hF' := hF
  unfold FramesOK at hF'
  obtain ⟨hF1, hV, -, -, -⟩ := hF'
  have hr : 1 ≤ r := by omega
  have hN1 : 1 ≤ orbitWindowCount r de h x := by
    unfold orbitWindowCount
    omega
  have hm : 2 ≤ m := by omega
  have hT : 1 ≤ TT.card := by
    by_contra hc
    have h0 : TT.card = 0 := by omega
    rw [h0, mul_zero] at hN
    have : 1 ≤ orbitWindowCount r de h x ^ 2 := Nat.one_le_pow _ _ hN1
    omega
  have hOrb' := hOrb
  unfold tableLineDegreeFive.OrbitHyp at hOrb'
  obtain ⟨-, -, hLU, -⟩ := hOrb'
  have hU : 1 ≤ goodU de := by omega
  have hG : goodG' r de h x ≠ 0 := by
    unfold goodG' goodEll
    exact Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by omega) (by omega))
  have hA1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 m)
  have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hr1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have hT1 : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hT
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hpl : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hQ1 : (1 : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 5 := one_le_pow₀ (one_le_pow₀ hp1)
  have hpQ : (p : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 5 :=
    le_trans (le_self_pow₀ hp1 hG) (le_self_pow₀ (one_le_pow₀ hp1) (by norm_num))
  have hc1 : (1 : ℝ) ≤ (cStar : ℝ) := by exact_mod_cast (by omega : 1 ≤ cStar)
  have hS : (1 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ)) := by
    have : (0 : ℝ) ≤ (r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ) := by positivity
    linarith
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hC1 : (1 : ℝ) ≤ C := by linarith
  have hA3 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hA1
  have hCT : C * (TT.card : ℝ) ≤ a := by
    have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * ((p : ℝ) ^ goodG' r de h x) ^ 5 *
        ((cStar : ℝ) + ((r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ))) * Y :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA3 hr1) hQ1) hS) hY1
    have h0 : (0 : ℝ) ≤ C * (TT.card : ℝ) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 h0
    refine le_trans ?_ hlast
    calc C * (TT.card : ℝ) = C * (TT.card : ℝ) * 1 := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  have hQa : ((p : ℝ) ^ goodG' r de h x) ^ 5 ≤ a := by
    have h1 : (1 : ℝ) ≤ C * ((m + 1 : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * (TT.card : ℝ) *
        ((cStar : ℝ) + ((r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ))) * Y :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hC1 hA3) hr1) hT1) hS) hY1
    have h0 : (0 : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 5 := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 h0
    refine le_trans ?_ hlast
    calc ((p : ℝ) ^ goodG' r de h x) ^ 5 = ((p : ℝ) ^ goodG' r de h x) ^ 5 * 1 := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  have hpa : (p : ℝ) ≤ a := le_trans hpQ hQa
  have h7 : (7 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 7 ≤ m + 1)
  have hlog : 1 ≤ Real.logb p a := by
    rw [← Real.logb_self_eq_one hpl]
    exact Real.logb_le_logb_of_le hpl (by linarith) hpa
  have hnb : NB p m r TT.card a := by
    refine ⟨by linarith, hpa, ?_, ?_, hlog, ?_⟩
    · have : 4 * (TT.card : ℝ) ≤ C * (TT.card : ℝ) := mul_le_mul_of_nonneg_right hC (by positivity)
      linarith
    · have : (r : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : r ≤ m + 1)
      linarith
    · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hT1 (one_le_pow₀ hA1)) hlog
  have hW' := hW
  unfold tableLineDegreeFive.WeightHyp at hW'
  obtain ⟨hBW, -, hab⟩ := hW'
  have hv : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp
  have hfd : ∀ s ∈ TT, a ≤ (flatDeg lam0 s : ℝ) ∧ (flatDeg lam0 s : ℝ) ≤ 2 * a := by
    intro s hs
    obtain ⟨h0, -, hmid⟩ := (hBW s).1 hs
    have hl := hmid 1 (by omega) (by omega)
    have hl' : |((lam0 s 1 : ℤ) : ℝ)| ≤ (cpp : ℝ) := by exact_mod_cast hl
    obtain ⟨hl1, hl2⟩ := abs_le.mp hl'
    obtain ⟨haT1, haT2, -, -⟩ := hab s hs
    have hv0R : (0 : ℝ) ≤ ((aT s : ℤ) : ℝ) - ((lam0 s 1 : ℤ) : ℝ) := by linarith
    have hv0 : 0 ≤ aT s - lam0 s 1 := by exact_mod_cast hv0R
    have e : ((flatDeg lam0 s : ℕ) : ℝ) = ((aT s : ℤ) : ℝ) - ((lam0 s 1 : ℤ) : ℝ) := by
      unfold flatDeg
      rw [h0, ← Int.cast_natCast, Int.toNat_of_nonneg hv0, Int.cast_sub]
    rw [e]
    constructor <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sizeAt_of (K := K) hk hF hr hnb hka hfd (fun j : ZMod F.J => (F.LLset (segZ j)).card) rfl (fun _ => rfl)
  · intro j u hu
    exact sl_lt_Bo hV hr p (by omega) (flatDeg lam0) a (by linarith)
      (fun s hs => (hfd s (by rw [hF1] at hs; exact hs)).1) Y (r + K) (by linarith) (by omega)
      (fun j : ZMod F.J => (F.LLset (segZ j)).card) (fun _ => rfl) j u hu
  · unfold cPrime
    omega
  · have hV' := hV
    unfold Frames.Valid at hV'
    exact hV'.1

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SumMulSumProd
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem ceil_le_of_geZ {x : WithTop ℤ} {t : ℝ} (h : geZ x t) : ((⌈t⌉ : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe k => exact WithTop.coe_le_coe.2 (Int.ceil_le.2 (h k rfl))

section Tr

variable {O : Type} [CommRing O] {J : ℕ} {n : ℕ}

theorem back_rename (j : ZMod J) (X : MvPolynomial ((ZMod J × ℤ) × Fin n) O)
    (hX : X ∈ supported O {v : (ZMod J × ℤ) × Fin n | v.1.1 = j}) :
    rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) (rename (fun v : (ZMod J × ℤ) × Fin n => (v.1.2, v.2)) X) = X := by
  rw [MvPolynomial.supported_eq_range_rename] at hX
  obtain ⟨Y, hY⟩ := hX
  rw [← hY]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.rename_rename]
  refine congrArg (fun f => (rename (R := O) f) Y) ?_
  funext v
  obtain ⟨⟨⟨a, b⟩, c⟩, hv⟩ := v
  simp only [Set.mem_setOf_eq] at hv
  subst hv
  rfl

private theorem twistSub_rename_eq {R : Type} [CommRing R] {ι κ : Type} {n : ℕ} (LL : Letters ι) (LK : Letters κ)
    (S : Set ι) (T : Set κ) (g : κ → ι) (hvec : ∀ y, LL.vec (g y) = LK.vec y) (hS : ∀ y, g y ∈ S ↔ y ∈ T)
    (k : Fin n) (X' : MvPolynomial (κ × Fin n) R) :
    twistSub LL S k (rename (R := R) (fun v : κ × Fin n => (g v.1, v.2)) X') =
      rename (R := GLLaurent R n) (fun v : κ × Fin n => (g v.1, v.2)) (twistSub LK T k X') := by
  have h : (twistSub LL S k).comp (rename (R := R) (fun v : κ × Fin n => (g v.1, v.2))).toRingHom =
      (rename (R := GLLaurent R n) (fun v : κ × Fin n => (g v.1, v.2))).toRingHom.comp (twistSub LK T k) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [twistSub]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, twistSub,
        eval₂Hom_X', hS, hvec]
      split_ifs <;> simp [map_sum]
  exact congrArg (fun φ => φ X') h

private theorem sDegs_rename_eq_of_injective {R : Type} [CommRing R] {ι κ : Type} {n : ℕ} (LL : Letters ι) (LK : Letters κ)
    (S : Set ι) (T : Set κ) (g : κ → ι) (hg : Function.Injective g) (hvec : ∀ y, LL.vec (g y) = LK.vec y)
    (hS : ∀ y, g y ∈ S ↔ y ∈ T) (k : Fin n) (X' : MvPolynomial (κ × Fin n) R) :
    sDegs LL S k (rename (fun v : κ × Fin n => (g v.1, v.2)) X') = sDegs LK T k X' := by
  have hinj : Function.Injective (fun v : κ × Fin n => (g v.1, v.2)) := fun a b h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hg h.1) h.2
  unfold sDegs
  rw [twistSub_rename_eq LL LK S T g hvec hS k X', MvPolynomial.support_rename_of_injective hinj,
    Finset.image_biUnion]
  simp only [MvPolynomial.coeff_rename_mapDomain _ hinj]

theorem seg_val [NeZero n] (j : ZMod J) (X' : MvPolynomial (ℤ × Fin n) O) (P : ℤ → Prop) :
    valS (LSeg J) {i | i.1 = j ∧ P i.2} (rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) X') = valS LZ {y | P y} X' ∧
    lam1S (LSeg J) {i | i.1 = j ∧ P i.2} (rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) X') = lam1S LZ {y | P y} X' := by
  have h1 : ∀ k, sDegs (LSeg J) {i | i.1 = j ∧ P i.2} k (rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) X') =
      sDegs LZ {y | P y} k X' := fun k =>
    sDegs_rename_eq_of_injective (LSeg J) LZ _ _ (fun y : ℤ => (j, y)) (fun a b h => (Prod.mk.inj h).2) (fun y => rfl)
      (fun y => by simp) k X'
  exact ⟨by simp only [valS, h1], by simp only [lam1S, h1]⟩

end Tr

section XGs

variable {O : Type} [CommRing O] [IsDomain O] {ι G : Type} (π : ι → G) {n : ℕ} [NeZero n] (LL : Letters ι)
  (Cv Cl : G → Set (Set ι × ℤ)) (F : MvPolynomial (ι × Fin n) O)

theorem XG_supported (j : G) (x : MvPolynomial (ι × Fin n) O) (hx : x ∈ XG π LL Cv Cl F j) :
    x ∈ supported O {v : ι × Fin n | π v.1 = j} := by
  rw [MvPolynomial.mem_supported]
  intro v hv
  obtain ⟨d, hd, hvd⟩ := (MvPolynomial.mem_vars v).mp (Finset.mem_coe.mp hv)
  obtain ⟨mo', -, rfl⟩ := Finset.mem_image.mp (hx.1 d hd)
  rw [Finsupp.mem_support_iff] at hvd
  show π v.1 = j
  by_contra hne
  exact hvd (by simp [partOf, Finsupp.filter_apply, hne])

theorem XG_part (j : G) (x : MvPolynomial (ι × Fin n) O) (hx : x ∈ XG π LL Cv Cl F j) (mo : ι × Fin n →₀ ℕ)
    (hmo : mo ∈ x.support) : ∃ mo' ∈ F.support, partOf π j mo' = mo :=
  Finset.mem_image.1 (hx.1 mo hmo)

theorem partOf_apply_pos (j : G) (mo : ι × Fin n →₀ ℕ) (v : ι × Fin n) (hv : π v.1 = j) : partOf π j mo v = mo v := by
  unfold partOf
  exact Finsupp.filter_apply_pos _ _ hv

end XGs

theorem support_homComp {R : Type} [CommRing R] {ι : Type} {n : ℕ} (δ : ι → ℕ) (F : MvPolynomial (ι × Fin n) R)
    (mo : ι × Fin n →₀ ℕ) (h : mo ∈ (homComp δ F).support) : mo ∈ F.support ∧ ∀ i, multideg mo i = δ i := by
  have hc := MvPolynomial.mem_support_iff.mp h
  simp only [homComp, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter] at hc
  split_ifs at hc with hm
  · exact hm
  · exact absurd rfl hc

section Ph

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] (K : ℕ) {J : ℕ}

theorem PhiPl_seg (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) :
    PhiPl Fr p O K J (rename (fun v : ℤ × Fin r => ((j, v.1), v.2)) A) = phSeg O K p Fr (segZ j) (plEmb O r K A) := by
  simp only [PhiPl, phSeg, plEmb, MvPolynomial.aeval_rename, Function.comp_def]

theorem PhiNo_seg (j : ZMod J) (B : MvPolynomial (ℤ × Fin K) O) :
    PhiNo Fr p O K J (rename (fun v : ℤ × Fin K => ((j, v.1), v.2)) B) = phSeg O K p Fr (segZ j) (nmEmb O r K B) := by
  simp only [PhiNo, phSeg, nmEmb, MvPolynomial.aeval_rename, Function.comp_def]

end Ph

theorem segZ_cast {J : ℕ} [NeZero J] (t : ℕ) (ht : t < J) : segZ (((t : ℤ) : ZMod J)) = (t : ℤ) := by
  simp only [segZ, Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ht]

theorem cast_segZ {J : ℕ} [NeZero J] (j : ZMod J) : ((segZ j : ℤ) : ZMod J) = j := by
  simp only [segZ, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem prod_range_zmod {M : Type} [CommMonoid M] {J : ℕ} [NeZero J] (g : ℤ → M) :
    ∏ t ∈ Finset.range J, g (t : ℤ) = ∏ j : ZMod J, g (segZ j) := by
  symm
  refine Finset.prod_nbij' (fun j => j.val) (fun t => (t : ZMod J)) ?_ ?_ ?_ ?_ ?_
  · intro j _
    simp [ZMod.val_lt]
  · intro t _
    simp
  · intro j _
    simp [ZMod.natCast_zmod_val]
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_range] at ht
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt ht]
  · intro j _
    rfl

theorem sum_mul_sum_prod {M : Type} [CommRing M] {G : Type} [Fintype G] {N1 N2 : ℕ} (a : Fin N1 → G → M)
    (b : Fin N2 → G → M) :
    (∑ i, ∏ j, a i j) * (∑ i, ∏ j, b i j) =
      ∑ q : Fin (N1 * N2), ∏ j, (a (finProdFinEquiv.symm q).1 j * b (finProdFinEquiv.symm q).2 j) := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv finProdFinEquiv _ _ (fun p => ?_)
  simp [Finset.prod_mul_distrib]

section SegDec

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {J : ℕ} [NeZero J] {n : ℕ} [NeZero n]

theorem seg_dec (hA : ATL) (hS : ValSlice) (F : MvPolynomial ((ZMod J × ℤ) × Fin n) O)
    (Cv Cl : ZMod J → Set ((ℤ → Prop) × ℤ))
    (hv : ∀ j, ∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤ valS (LSeg J) {i | i.1 = j ∧ q.1 i.2} F)
    (hl : ∀ j, ∀ q ∈ Cl j, lam1S (LSeg J) {i | i.1 = j ∧ q.1 i.2} F ≤ ((q.2 : ℤ) : WithBot ℤ)) :
    ∃ (N : ℕ) (A' : Fin N → ZMod J → MvPolynomial (ℤ × Fin n) O),
      (∀ i j, (∀ mo ∈ (A' i j).support, ∃ mo' ∈ F.support, ∀ x c, mo (x, c) = mo' ((j, x), c)) ∧
        (∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤ valS LZ {y | q.1 y} (A' i j)) ∧
        (∀ q ∈ Cl j, lam1S LZ {y | q.1 y} (A' i j) ≤ ((q.2 : ℤ) : WithBot ℤ))) ∧
      F = ∑ i, ∏ j, rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) (A' i j) := by
  classical
  let Cv' : ZMod J → Set (Set (ZMod J × ℤ) × ℤ) := fun j =>
    (fun q : (ℤ → Prop) × ℤ => ({i : ZMod J × ℤ | i.1 = j ∧ q.1 i.2}, q.2)) '' Cv j
  let Cl' : ZMod J → Set (Set (ZMod J × ℤ) × ℤ) := fun j =>
    (fun q : (ℤ → Prop) × ℤ => ({i : ZMod J × ℤ | i.1 = j ∧ q.1 i.2}, q.2)) '' Cl j
  obtain ⟨N, A, hA', hF⟩ := decGen (O := O) (Prod.fst : ZMod J × ℤ → ZMod J) (LSeg J) Cv' Cl' F hA hS
    (by
      rintro j q ⟨q0, -, rfl⟩ i hi
      exact hi.1)
    (by
      rintro j q ⟨q0, -, rfl⟩ i hi
      exact hi.1)
    (by
      rintro j q ⟨q0, hq0, rfl⟩
      exact hv j q0 hq0)
    (by
      rintro j q ⟨q0, hq0, rfl⟩
      exact hl j q0 hq0)
  have hback : ∀ i j, rename (fun v : ℤ × Fin n => ((j, v.1), v.2))
      (rename (fun v : (ZMod J × ℤ) × Fin n => (v.1.2, v.2)) (A i j)) = A i j := fun i j =>
    back_rename j (A i j) (XG_supported Prod.fst (LSeg J) Cv' Cl' F j (A i j) (hA' i j))
  refine ⟨N, fun i j => rename (fun v : (ZMod J × ℤ) × Fin n => (v.1.2, v.2)) (A i j), fun i j => ?_, ?_⟩
  · have hmem : A i j ∈ XG Prod.fst (LSeg J) Cv' Cl' F j := hA' i j
    refine ⟨?_, ?_, ?_⟩
    · intro mo hmo
      have hinj : Function.Injective (fun v : ℤ × Fin n => ((j, v.1), v.2)) := fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.2 h.2
      have h2 : Finsupp.mapDomain (fun v : ℤ × Fin n => ((j, v.1), v.2)) mo ∈ (A i j).support := by
        rw [← hback i j, MvPolynomial.support_rename_of_injective hinj]
        exact Finset.mem_image_of_mem _ hmo
      obtain ⟨mo', hmo', he⟩ := XG_part Prod.fst (LSeg J) Cv' Cl' F j (A i j) hmem _ h2
      refine ⟨mo', hmo', fun x c => ?_⟩
      have h4 : partOf Prod.fst j mo' ((j, x), c) =
          Finsupp.mapDomain (fun v : ℤ × Fin n => ((j, v.1), v.2)) mo ((j, x), c) := by
        rw [he]
      rw [partOf_apply_pos Prod.fst j mo' ((j, x), c) rfl,
        Finsupp.mapDomain_apply hinj mo (x, c)] at h4
      exact h4.symm
    · intro q hq
      have h3 := hmem.2.1 _ ⟨q, hq, rfl⟩
      dsimp only at h3
      rw [← hback i j, (seg_val j _ q.1).1] at h3
      exact h3
    · intro q hq
      have h3 := hmem.2.2 _ ⟨q, hq, rfl⟩
      dsimp only at h3
      rw [← hback i j, (seg_val j _ q.1).2] at h3
      exact h3
  · conv_lhs => rw [hF]
    refine Finset.sum_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    exact (hback i j).symm

end SegDec

end Formalism.MainNotions.Proposition5Numerics
end
end

