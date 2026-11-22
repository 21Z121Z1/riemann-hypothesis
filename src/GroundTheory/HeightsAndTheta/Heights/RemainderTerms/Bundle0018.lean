import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombDetDescFactorial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Comb Equiv

theorem CombDetDescFactorial.proof : CombDetDescFactorial.Statement := by
  intro m l
  rw [vandermondeOf_eq_det]

  set v : Fin m → ℚ := fun i => (l i : ℚ)
  have hA : (Matrix.of fun i j : Fin m => ((l i).descFactorial (stair m j) : ℚ)) =
      (Matrix.of fun i j : Fin m => (descPochhammer ℚ (j : ℕ)).eval (v i)).submatrix
        id Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, v,
      descPochhammer_eval_eq_descFactorial, stair]
    rw [Fin.val_rev]
    congr 2
    omega
  have hB : (Matrix.of fun i j : Fin m => v i ^ (m - 1 - (j : ℕ))) =
      (Matrix.vandermonde v).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, Fin.val_rev,
      Matrix.vandermonde_apply]
    congr 1
    omega
  rw [hA, hB, Matrix.det_permute', Matrix.det_permute',
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
      (fun j => descPochhammer ℚ (j : ℕ))
      (fun j => descPochhammer_natDegree ℚ _)
      (fun j => monic_descPochhammer ℚ _)]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombExtendWord
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

noncomputable section

open scoped Classical

namespace CombExtendWord

theorem snoc_mem {m n : ℕ} (lam : Fin m → ℕ) (hlam : Antitone lam) (k : Fin m) (hk : 1 ≤ lam k)
    (v : Fin n → Fin m) (hv : v ∈ latticeWords n (Function.update lam k (lam k - 1))) :
    (Fin.snoc v k : Fin (n + 1) → Fin m) ∈ latticeWords (n + 1) lam := by
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hv ⊢
  obtain ⟨hlat, hcont⟩ := hv
  refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
  · rcases Nat.lt_or_ge t (n + 1) with htn | htn
    · rw [pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]
      exact hlat t (by omega) i j hij
    · have ht' : t = n + 1 := by omega
      subst ht'
      rw [pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam k i hk,
        update_pred_sub lam k j hk]
      exact hlam hij
  · rw [pcnt_snoc_last, hcont, update_pred_sub lam k i hk]

theorem exists_word {m : ℕ} (h1 : CombPcntAppend.Statement) (μ : Fin m → ℕ) (hμ : Antitone μ) :
    ∀ (q : ℕ) (lam : Fin m → ℕ), Antitone lam → (∀ i, μ i ≤ lam i) →
      ∑ i, lam i = ∑ i, μ i + q →
        ∃ s : Fin q → Fin m, ∀ n, ∀ w ∈ latticeWords n μ,
          Fin.append w s ∈ latticeWords (n + q) lam := by
  intro q
  induction q with
  | zero =>
    intro lam _ hle hsum
    have heq : ∀ i, μ i = lam i := by
      have := (Finset.sum_eq_sum_iff_of_le (s := univ) (fun i _ => hle i)).mp (by simpa using hsum.symm)
      exact fun i => this i (mem_univ i)
    refine ⟨Fin.elim0, fun n w hw => ?_⟩
    simp only [latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
    have hp : ∀ t i, pcnt (Fin.append w (Fin.elim0 : Fin 0 → Fin m)) t i = pcnt w t i := by
      intro t i
      rw [h1]
      have : pcnt (Fin.elim0 : Fin 0 → Fin m) (t - n) i = 0 := by unfold pcnt; simp
      omega
    refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
    · rw [hp, hp]; exact hw.1 t ht i j hij
    · rw [hp, Nat.add_zero, hw.2 i, heq i]
  | succ q ih =>
    intro lam hlam hle hsum
    have hne : (univ.filter (fun i => μ i < lam i)).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      have : ∑ i, lam i ≤ ∑ i, μ i :=
        Finset.sum_le_sum fun i _ => not_lt.mp (hemp (mem_univ i))
      omega
    obtain ⟨k, hk, hkmax⟩ : ∃ k, μ k < lam k ∧ ∀ j, μ j < lam j → j ≤ k :=
      ⟨_, (mem_filter.mp (max'_mem _ hne)).2,
        fun j hj => le_max' _ j (mem_filter.mpr ⟨mem_univ j, hj⟩)⟩
    have hgt : ∀ j, k < j → lam j = μ j := by
      intro j hj
      by_contra hne'
      exact absurd (hkmax j (lt_of_le_of_ne (hle j) (Ne.symm hne'))) (not_le.mpr hj)
    have hanti : Antitone (Function.update lam k (lam k - 1)) := by
      intro i j hij
      by_cases hik : i = k <;> by_cases hjk : j = k
      · rw [hik, hjk]
      · rw [hik, Function.update_self, Function.update_of_ne hjk]
        have hkj : k < j := lt_of_le_of_ne (hik ▸ hij) (Ne.symm hjk)
        rw [hgt j hkj]
        have := hμ (hik ▸ hij)
        omega
      · rw [hjk, Function.update_self, Function.update_of_ne hik]
        have := hlam (hjk ▸ hij)
        omega
      · rw [Function.update_of_ne hik, Function.update_of_ne hjk]
        exact hlam hij
    have hle' : ∀ i, μ i ≤ Function.update lam k (lam k - 1) i := by
      intro i
      by_cases hik : i = k
      · rw [hik, Function.update_self]; omega
      · rw [Function.update_of_ne hik]; exact hle i
    have hsum' : ∑ i, Function.update lam k (lam k - 1) i = ∑ i, μ i + q := by
      have h2 : ∀ i, Function.update lam k (lam k - 1) i + (if k = i then 1 else 0) = lam i :=
        fun i => update_pred_sub lam k i (by omega)
      have : ∑ i, lam i = ∑ i, Function.update lam k (lam k - 1) i + 1 := by
        rw [← Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_add_distrib, Finset.sum_ite_eq]
        simp
      omega
    obtain ⟨s', hs'⟩ := ih _ hanti hle' hsum'
    refine ⟨Fin.snoc s' k, fun n w hw => ?_⟩
    rw [Fin.append_snoc]
    exact snoc_mem lam hlam k (by omega) _ (hs' n w hw)

theorem proof (h1 : CombPcntAppend.Statement) : CombExtendWord.Statement := by
  intro m n q μ lam hμ hlam hle hsum
  obtain ⟨s, hs⟩ := exists_word h1 μ hμ q lam hlam hle hsum
  exact ⟨s, hs n⟩

end CombExtendWord

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombHookBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombHookBranch.unconditional : CombHookBranch.Statement := by
  intro r s l hs hls hr a
  have ha := a.isLt
  by_cases hpos : 1 ≤ hookShape r (s + 1) l a
  · rw [if_pos hpos]
    by_cases ha0 : (a : ℕ) = 0
    · rw [if_neg (show ¬ ((a : ℕ) = l ∧ 1 ≤ l) by omega), add_zero]
      by_cases hl : l < s
      ·
        rw [if_pos ⟨ha0, hl⟩]
        have heq : Function.update (hookShape r (s + 1) l) a (hookShape r (s + 1) l a - 1)
            = hookShape r s l := by
          funext i
          simp only [Function.update_apply, hookShape, Fin.ext_iff]
          split_ifs <;> omega
        rw [heq]
      ·
        rw [if_neg (show ¬ ((a : ℕ) = 0 ∧ l < s) by omega),
          latticeWords_eq_empty_of_not_antitone, Finset.card_empty]
        intro hanti
        have key := hanti (show a ≤ (⟨1, by omega⟩ : Fin r) from
          Fin.le_iff_val_le_val.mpr (by show (a : ℕ) ≤ 1; omega))
        simp only [Function.update_apply, hookShape, Fin.ext_iff] at key
        split_ifs at key <;> omega
    · have hal : (a : ℕ) ≤ l := by
        simp only [hookShape] at hpos
        split_ifs at hpos <;> omega
      rw [if_neg (show ¬ ((a : ℕ) = 0 ∧ l < s) by omega), zero_add]
      by_cases hal' : (a : ℕ) = l
      ·
        rw [if_pos ⟨hal', by omega⟩]
        have heq : Function.update (hookShape r (s + 1) l) a (hookShape r (s + 1) l a - 1)
            = hookShape r s (l - 1) := by
          funext i
          simp only [Function.update_apply, hookShape, Fin.ext_iff]
          split_ifs <;> omega
        rw [heq]
      ·
        rw [if_neg (show ¬ ((a : ℕ) = l ∧ 1 ≤ l) by omega),
          latticeWords_eq_empty_of_not_antitone, Finset.card_empty]
        intro hanti
        have key := hanti (show a ≤ (⟨(a : ℕ) + 1, by omega⟩ : Fin r) from
          Fin.le_iff_val_le_val.mpr (by show (a : ℕ) ≤ (a : ℕ) + 1; omega))
        simp only [Function.update_apply, hookShape, Fin.ext_iff] at key
        split_ifs at key <;> omega
  ·
    rw [if_neg hpos]
    have hla : l < (a : ℕ) := by
      simp only [hookShape] at hpos
      split_ifs at hpos <;> omega
    rw [if_neg (show ¬ ((a : ℕ) = 0 ∧ l < s) by omega),
      if_neg (show ¬ ((a : ℕ) = l ∧ 1 ≤ l) by omega)]

theorem CombHookBranch.proof (_h1 : CombHookShapeFacts.Statement) : CombHookBranch.Statement :=
  CombHookBranch.unconditional

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombHookCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem card_latticeWords_zero_of_eq_zero {r : ℕ} (lam : Fin r → ℕ) (hlam : ∀ i, lam i = 0) :
    (latticeWords 0 lam).card = 1 := by
  have h : latticeWords 0 lam = univ := by
    ext w
    simp only [latticeWords, mem_filter, mem_univ, true_and, iff_true]
    exact ⟨fun t _ i j _ => by simp [pcnt], fun i => by rw [hlam i]; simp [pcnt]⟩
  rw [h, card_univ]
  simp

theorem CombHookCount.proof (h1 : CombHookShapeFacts.Statement) (h2 : CombHookBranch.Statement) :
    CombHookCount.Statement := by
  intro r s
  induction s with
  | zero => intro l hl; omega
  | succ s ih =>
    intro l hl hsr
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · have hl0 : l = 0 := by omega
      subst hl0
      have hr : 0 < r := by omega
      rw [card_latticeWords_succ 0 _ (h1 r 1 0 (by omega) hsr).1,
        Finset.sum_eq_single (⟨0, hr⟩ : Fin r) ?_ (fun h => absurd (mem_univ _) h)]
      · rw [if_pos (by simp [hookShape]), card_latticeWords_zero_of_eq_zero _ (fun i => ?_)]
        · simp
        · by_cases hi : i = ⟨0, hr⟩
          · subst hi; simp [hookShape]
          · rw [Function.update_of_ne hi]
            have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
            simp [hookShape, this]
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
        rw [if_neg]
        simp [hookShape, this]
    · rw [card_latticeWords_succ s _ (h1 r (s + 1) l hl hsr).1,
        Finset.sum_congr rfl (fun a _ => h2 r s l hs (by omega) hsr a), Finset.sum_add_distrib,
        Finset.sum_eq_single (⟨0, by omega⟩ : Fin r)
          (fun b _ hb => if_neg (fun h => hb (Fin.ext h.1))) (fun h => absurd (mem_univ _) h),
        Finset.sum_eq_single (⟨l, by omega⟩ : Fin r)
          (fun b _ hb => if_neg (fun h => hb (Fin.ext h.1))) (fun h => absurd (mem_univ _) h)]
      simp only [true_and, Nat.add_sub_cancel]
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      rcases Nat.eq_zero_or_pos l with rfl | hl1
      · rw [if_pos hs, if_neg (by omega), ih 0 hs (by omega)]
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
        rw [if_pos (show 1 ≤ k + 1 by omega), Nat.add_sub_cancel, ih k (by omega) (by omega),
          Nat.add_sub_cancel, Nat.choose_succ_succ]
        rcases Nat.lt_or_ge (k + 1) (t + 1) with hk | hk
        · rw [if_pos hk, ih (k + 1) hk (by omega), Nat.add_sub_cancel]
          ring
        · rw [if_neg (by omega), Nat.choose_eq_zero_of_lt (show t < k + 1 by omega)]
          ring

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombHookShapeFacts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem CombHookShapeFacts.sum_lt_indicator (l : ℕ) :
    ∀ m : ℕ, (∑ i ∈ range m, if i < l then 1 else 0) = min m l := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

theorem CombHookShapeFacts.proof : CombHookShapeFacts.Statement := by
  intro r s l hls hsr
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    simp only [hookShape]
    split_ifs <;> omega
  · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have h := Fin.sum_univ_eq_sum_range
      (fun k : ℕ => if k = 0 then s - l else if k ≤ l then 1 else 0) (m + 1)
    simp only [hookShape]
    rw [h, sum_range_succ']
    have h2 : (∑ i ∈ range m, (if i + 1 = 0 then s - l else if i + 1 ≤ l then 1 else 0)) =
        ∑ i ∈ range m, (if i < l then 1 else 0) := by
      refine sum_congr rfl fun i _ => ?_
      rw [if_neg (Nat.succ_ne_zero i)]
      split_ifs <;> omega
    rw [h2, CombHookShapeFacts.sum_lt_indicator l m]
    simp only [if_true]
    omega

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombPcntAppend
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

open scoped Classical

open Comb

theorem CombPcntAppend.proof : CombPcntAppend.Statement := by
  intro m n q w s t i
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.append_left, Fin.val_castAdd]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.append_right, Fin.val_natAdd]
    have h : (n + (k : ℕ) < t) ↔ ((k : ℕ) < t - n) := by omega
    simp only [h]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Equiv

theorem CombSortLe.proof : CombSortLe.Statement := by
  intro m u l σ hl hul hu k
  obtain ⟨j, hjk, hkj⟩ : ∃ j : Fin m, j ≤ k ∧ k ≤ σ j := by
    by_contra h
    push Not at h
    have hcard : (Iic k).card ≤ (Iio k).card := by
      refine card_le_card_of_injOn σ ?_ σ.injective.injOn
      intro j hj
      simp only [coe_Iic, coe_Iio, Set.mem_Iic, Set.mem_Iio] at hj ⊢
      exact h j hj
    rw [Fin.card_Iic, Fin.card_Iio] at hcard
    omega
  calc u (σ k) ≤ u (σ j) := hu hjk
    _ ≤ l (σ j) := hul _
    _ ≤ l k := hl hkj

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Equiv

namespace Comb

theorem add_index_le_of_strictAnti {m : ℕ} {f : Fin m → ℕ} (hf : StrictAnti f) (a b : Fin m)
    (hab : a ≤ b) : f b + (b : ℕ) ≤ f a + (a : ℕ) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have h1 := ih (by omega)
    have h2 : f ⟨n + 1, hb⟩ < f ⟨n, by omega⟩ := hf (by simp [Fin.lt_def])
    simp only at h1 ⊢
    omega

theorem CombSortShift.proof (h1 : CombSortLe.Statement) : CombSortShift.Statement := by
  intro m lam hlam q i hq hinj
  set u := Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) with hu
  obtain ⟨σ, hσ⟩ := exists_perm_strictAnti hinj
  have hge : ∀ k : Fin m, stair m k ≤ u (σ k) := by
    intro k
    have hk := add_index_le_of_strictAnti hσ k ⟨m - 1, by have := k.isLt; omega⟩ (by rw [Fin.le_def]; exact Nat.le_sub_one_of_lt k.isLt)
    simp only [Function.comp_apply] at hk
    simp only [stair]
    omega
  refine ⟨σ, fun k => u (σ k) - stair m k, ?_, ?_, ?_⟩
  · intro a b hab
    have h := add_index_le_of_strictAnti hσ a b hab
    have ha := hge a
    have hb := hge b
    simp only [Function.comp_apply, stair] at h ha hb ⊢
    omega
  · intro k
    have hl : Antitone (fun j => lam j + stair m j) := by
      intro a b hab
      have := hlam hab
      simp only [stair]
      have : (a : ℕ) ≤ b := hab
      omega
    have hul : ∀ j, u j ≤ lam j + stair m j := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [hu]
      · simp [hu, Function.update_of_ne hj]
    have := h1 m u (fun j => lam j + stair m j) σ hl hul hσ.antitone k
    show u (σ k) - stair m k ≤ lam k
    omega
  · intro k
    have := hge k
    show u (σ k) = u (σ k) - stair m k + stair m k
    omega

end Comb

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortShiftDistinct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Equiv

theorem CombSortShiftDistinct.proof : CombSortShiftDistinct.Statement := by
  intro m l hl q hq i j hij hqi hqj σ τ heq
  have hr := congrArg Set.range heq
  rw [σ.surjective.range_comp, τ.surjective.range_comp] at hr
  have hmem : l i ∈ Set.range (Function.update l j (l j - q)) :=
    ⟨i, by rw [Function.update_of_ne hij]⟩
  rw [← hr] at hmem
  obtain ⟨k, hk⟩ := hmem
  by_cases hki : k = i
  · subst hki
    rw [Function.update_self] at hk
    omega
  · rw [Function.update_of_ne hki] at hk
    exact hki (hl hk)

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauOfWord
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauOfWord.proof (h1 : CombCellOfWordMem.Statement)
    (h2 : CombCellOfWordInj.Statement) (h3 : CombCellOfWordMono.Statement) :
    CombTableauOfWord.Statement := by
  intro m lam _hlam w hw
  have hL : IsLattice w := by
    simp only [latticeWords, mem_filter] at hw
    exact hw.2.1
  let f : Fin (youngCells lam).card → youngCells lam := fun t => ⟨cellOfWord w t, h1 m lam w hw t⟩
  have hinj : Function.Injective f := by
    intro s t hst
    exact h2 m _ w (congrArg Subtype.val hst)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp⟩
  let T : youngCells lam ≃ Fin (youngCells lam).card := (Equiv.ofBijective f hbij).symm
  have hT : ∀ p : youngCells lam, cellOfWord w (T p) = p.1 := by
    intro p
    have : f (T p) = p := (Equiv.ofBijective f hbij).apply_symm_apply p
    exact congrArg Subtype.val this
  refine ⟨T, ?_, ?_⟩
  · intro p q hpq1 hpq2
    apply h3 m _ w hL
    · rw [hT p, hT q]; exact hpq1
    · rw [hT p, hT q]; exact hpq2
  · funext t
    show (T.symm t).1.1 = w t
    rfl

end GroundTheory.Heights₂.Heights.RestTerms
end

