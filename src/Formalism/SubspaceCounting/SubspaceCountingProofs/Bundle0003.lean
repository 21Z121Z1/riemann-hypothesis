import Formalism.SubspaceCounting.Bundle0002

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.TailSums
section
namespace Formalism.G0

namespace TailSumsP

theorem tailK_zero {K : ℕ} (α : Fin K → ℕ) : tailK α 0 = ∑ l, α l := by
  simp [tailK]

theorem tailK_zero_fun {K : ℕ} (u : ℕ) : tailK (0 : Fin K → ℕ) u = 0 := by
  simp [tailK]

theorem tailK_shrink {K : ℕ} {α α' : Fin K → ℕ} (h : ShrinkStep α α') (u : ℕ) :
    tailK α' u ≤ tailK α u := by
  unfold tailK
  apply Finset.sum_le_sum
  intro l _
  split_ifs
  · exact h l
  · exact le_rfl

theorem tailK_vec_succ {K : ℕ} {α α' : Fin K → ℕ} {B : ℕ} (h : VecStep α α' B) (u : ℕ) :
    tailK α' (u + 1) ≤ tailK α u := by
  obtain ⟨-, h2, -⟩ := h
  cases K with
  | zero => simp [tailK]
  | succ k =>
    unfold tailK
    rw [Fin.sum_univ_succ,
      Fin.sum_univ_castSucc (f := fun l : Fin (k + 1) => if u ≤ l.val then α l else 0)]
    simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Nat.add_le_add_iff_right,
      Nat.le_zero, Nat.add_one_ne_zero, if_false, zero_add]
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply Finset.sum_le_sum
    intro i _
    by_cases hu : u ≤ i.val
    · rw [if_pos (by omega), if_pos hu]
      have hh : i.castSucc.val + 1 < k + 1 := by simp
      have e : (⟨i.castSucc.val + 1, hh⟩ : Fin (k + 1)) = i.succ := Fin.ext (by simp)
      have := h2 i.castSucc hh
      rw [e] at this
      exact this
    · rw [if_neg (by omega), if_neg hu]

theorem tailK_vec_zero {K : ℕ} {α α' : Fin K → ℕ} {B : ℕ} (h : VecStep α α' B) :
    tailK α' 0 ≤ tailK α 0 + B := by
  rw [tailK_zero, tailK_zero]; exact h.2.2

theorem latestDegrees_succ_some (steps : List (Option ℕ)) (i : ℕ) (hi : i < steps.length)
    {B : ℕ} (h : steps[i] = some B) :
    latestDegrees steps (i + 1) = B :: latestDegrees steps i := by
  unfold latestDegrees
  rw [List.take_add_one, List.getElem?_eq_getElem hi, h]
  simp

theorem latestDegrees_succ_none (steps : List (Option ℕ)) (i : ℕ) (hi : i < steps.length)
    (h : steps[i] = none) :
    latestDegrees steps (i + 1) = latestDegrees steps i := by
  unfold latestDegrees
  rw [List.take_add_one, List.getElem?_eq_getElem hi, h]
  simp

def cnt (steps : List (Option ℕ)) (i j : ℕ) : ℕ :=
  (((steps.drop i).take (j - i)).filterMap id).length

theorem cnt_self (steps : List (Option ℕ)) (i : ℕ) : cnt steps i i = 0 := by
  simp [cnt]

theorem cnt_succ_some (steps : List (Option ℕ)) (i j : ℕ) (hij : i ≤ j) (hj : j < steps.length)
    {B : ℕ} (h : steps[j] = some B) : cnt steps i (j + 1) = cnt steps i j + 1 := by
  unfold cnt
  rw [show j + 1 - i = (j - i) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show i + (j - i) = j by omega, List.getElem?_eq_getElem hj, h]
  simp

theorem cnt_succ_none (steps : List (Option ℕ)) (i j : ℕ) (hij : i ≤ j) (hj : j < steps.length)
    (h : steps[j] = none) : cnt steps i (j + 1) = cnt steps i j := by
  unfold cnt
  rw [show j + 1 - i = (j - i) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show i + (j - i) = j by omega, List.getElem?_eq_getElem hj, h]
  simp

theorem clause1 {K : ℕ} (steps : List (Option ℕ)) (what₂ : ℕ → Fin K → ℕ)
    (hp : IsPath steps what₂) :
    ∀ i ≤ steps.length, ∀ u, tailK (what₂ i) u ≤ ((latestDegrees steps i).drop u).sum := by
  intro i
  induction i with
  | zero => intro _ u; rw [hp.1, tailK_zero_fun]; exact Nat.zero_le _
  | succ i ih =>
    intro hi u
    have hi' : i < steps.length := by omega
    have hstep := hp.2 i hi'
    cases hs : steps[i] with
    | none =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_none steps i hi' hs]
      exact le_trans (tailK_shrink hstep u) (ih (by omega) u)
    | some B =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_some steps i hi' hs]
      cases u with
      | zero =>
        simp only [List.drop_zero, List.sum_cons]
        have h1 := ih (by omega) 0
        simp only [List.drop_zero] at h1
        have h2 := tailK_vec_zero hstep
        omega
      | succ u =>
        simp only [List.drop_succ_cons]
        exact le_trans (tailK_vec_succ hstep u) (ih (by omega) u)

theorem clause2 {K : ℕ} (steps : List (Option ℕ)) (what₂ : ℕ → Fin K → ℕ)
    (hp : IsPath steps what₂) (i u X : ℕ)
    (hX : tailK (what₂ i) u + X ≤ ((latestDegrees steps i).drop u).sum) :
    ∀ j, i ≤ j → j ≤ steps.length →
      tailK (what₂ j) (u + cnt steps i j) + X ≤
        ((latestDegrees steps j).drop (u + cnt steps i j)).sum := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; rw [cnt_self, Nat.add_zero]; exact hX
  | succ j hij ih =>
    intro hj
    have hj' : j < steps.length := by omega
    have hstep := hp.2 j hj'
    cases hs : steps[j] with
    | none =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_none steps j hj' hs, cnt_succ_none steps i j hij hj' hs]
      have := tailK_shrink hstep (u + cnt steps i j)
      have := ih (by omega)
      omega
    | some B =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_some steps j hj' hs, cnt_succ_some steps i j hij hj' hs,
        ← Nat.add_assoc, List.drop_succ_cons]
      have := tailK_vec_succ hstep (u + cnt steps i j)
      have := ih (by omega)
      omega

end TailSumsP

theorem tail_sums : TailSums := by
  intro K steps what₂ hp
  refine ⟨TailSumsP.clause1 steps what₂ hp, ?_⟩
  intro i j u X hij hj hX
  exact TailSumsP.clause2 steps what₂ hp i u X hX j hij hj

end Formalism.G0
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.TopsChoiceCount
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.G0

namespace TopsCount

def a (m : ℕ) (δ : ℝ) (j : ℕ) : ℝ := (m.choose j : ℝ) * δ ^ j * (1 - δ) ^ (m - j)

def A (m : ℕ) (δ : ℝ) (K : ℕ) : ℝ := ∑ j ∈ range K, a m δ j

lemma a_nonneg {m : ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j : ℕ) : 0 ≤ a m δ j := by
  unfold a
  have : 0 ≤ 1 - δ := by linarith
  positivity

lemma A_succ (m : ℕ) (δ : ℝ) (K : ℕ) : A m δ (K + 1) = A m δ K + a m δ K := by
  unfold A; rw [sum_range_succ]

lemma pascal_term (m k : ℕ) (δ : ℝ) :
    ((m + 1).choose (k + 1) : ℝ) * δ ^ (k + 1) * (1 - δ) ^ (m + 1 - (k + 1)) =
      (1 - δ) * a m δ (k + 1) + δ * a m δ k := by
  unfold a
  rw [Nat.choose_succ_succ', Nat.cast_add]
  have e1 : m + 1 - (k + 1) = m - k := by omega
  rw [e1]
  rcases Nat.lt_or_ge k m with hk | hk
  · have e2 : m - k = (m - (k + 1)) + 1 := by omega
    rw [e2]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : m < k + 1)]
    push_cast; ring

lemma binLower_eq (m : ℕ) (δ : ℝ) (N : ℕ) :
    binLower (m + 1) δ N = (1 - δ) * A m δ N + δ * A m δ (N - 1) := by
  induction N with
  | zero => simp [binLower, A]
  | succ N ih =>
    have hs : binLower (m + 1) δ (N + 1) =
        binLower (m + 1) δ N + ((m + 1).choose N : ℝ) * δ ^ N * (1 - δ) ^ (m + 1 - N) := by
      unfold binLower; rw [sum_range_succ]
    rw [hs, ih]
    cases N with
    | zero =>
      simp [A, a]
      ring
    | succ k =>
      rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega,
        A_succ m δ (k + 1), A_succ m δ k, pascal_term]
      ring

lemma sum_ite_lt (m : ℕ) (δ : ℝ) (K : ℕ) :
    ∑ j ∈ range (m + 1), (if j < K then a m δ j else 0) = A m δ K := by
  rw [← sum_filter]
  unfold A
  apply sum_subset
  · intro j hj
    simp only [mem_filter] at hj
    exact mem_range.2 hj.2
  · intro j hjK hj
    simp only [mem_filter, mem_range, not_and] at hj
    have : m < j := by
      by_contra h
      exact hj (by omega) (mem_range.1 hjK)
    unfold a
    rw [Nat.choose_eq_zero_of_lt this]
    simp

lemma condProb_card (m : ℕ) (δ : ℝ) (N : ℕ) :
    condProb (m + 1) δ (fun T => T.card < N) = A m δ (N - 1) := by
  classical
  unfold condProb
  have h0 : (0 : ℕ) ∉ (range (m + 1)).erase 0 := notMem_erase 0 _
  have hr : range (m + 1) = insert 0 ((range (m + 1)).erase 0) :=
    (insert_erase (by simp)).symm
  rw [hr, sum_powerset_insert h0]
  beta_reduce
  rw [Finset.sum_eq_zero, zero_add]
  swap
  · intro t ht
    rw [if_neg]
    rintro ⟨h, _⟩
    exact h0 (mem_powerset.1 ht h)
  rw [Finset.sum_congr rfl (g := fun t : Finset ℕ =>
    (fun j : ℕ => if j < N - 1 then δ ^ j * (1 - δ) ^ (m - j) else 0) t.card)]
  swap
  · intro t ht
    have ht0 : (0 : ℕ) ∉ t := fun h => h0 (mem_powerset.1 ht h)
    rw [card_insert_of_notMem ht0]
    beta_reduce
    by_cases hN : t.card + 1 < N
    · rw [if_pos ⟨mem_insert_self 0 t, hN⟩, if_pos (by omega),
        show t.card + 1 - 1 = t.card by omega, show m + 1 - (t.card + 1) = m - t.card by omega]
    · rw [if_neg (fun h => hN h.2), if_neg (by omega)]
  rw [sum_powerset_apply_card (fun j : ℕ => if j < N - 1 then δ ^ j * (1 - δ) ^ (m - j) else 0)]
  have hcard : ((range (m + 1)).erase 0).card = m := by
    rw [card_erase_of_mem (by simp), card_range]; rfl
  rw [hcard, ← sum_ite_lt]
  apply sum_congr rfl
  intro j _
  rw [nsmul_eq_mul]
  by_cases hj : j < N - 1
  · rw [if_pos hj, if_pos hj]; unfold a; ring
  · rw [if_neg hj, if_neg hj, mul_zero]

end TopsCount

open TopsCount in
theorem tops_choice_count : SmallCardCondProbBound := by
  intro n δ N hn h0 h1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [condProb_card, binLower_eq]
  have hA : A m δ (N - 1) ≤ A m δ N := by
    unfold A
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (Nat.sub_le _ _))
      (fun j _ _ => a_nonneg h0 h1 j)
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hA)]

end Formalism.G0
end
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.TopsChoicePartC
section
noncomputable section

namespace Formalism.G0

namespace TopsConditionalProbabilityBounds

open Finset

theorem weight_nonneg (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (T : Finset ℕ) :
    0 ≤ δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) :=
  mul_nonneg (pow_nonneg hδ0 _) (pow_nonneg (by linarith) _)

theorem condProb_mono (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (A B : Finset ℕ → Prop)
    (h : ∀ T, 0 ∈ T → A T → B T) : condProb n δ A ≤ condProb n δ B := by
  classical
  unfold condProb
  apply sum_le_sum
  intro T _
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h T h1.1 h1.2⟩ h2
  · exact weight_nonneg n δ hδ0 hδ1 T
  · exact le_rfl

theorem condProb_disjoint (n : ℕ) (δ : ℝ) (S : Finset ℕ) (hS : S ⊆ range n) (h0 : 0 ∉ S)
    (hn : 1 ≤ n) :
    condProb n δ (fun T => Disjoint S T) = (1 - δ) ^ S.card := by
  classical
  set U := (range n \ S).erase 0 with hU
  have h0U : 0 ∈ range n \ S := by simp [h0]; omega
  have hUcard : U.card = n - S.card - 1 := by
    rw [hU, card_erase_of_mem h0U, card_sdiff_of_subset hS, card_range]
  have hs1 : S.card + 1 ≤ n := by
    have hsub : S ⊆ (range n).erase 0 := fun x hx => mem_erase.2 ⟨fun h => h0 (h ▸ hx), hS hx⟩
    have := card_le_card hsub
    rw [card_erase_of_mem (by simp; omega), card_range] at this
    omega
  have key : ∑ T' ∈ U.powerset, δ ^ T'.card * (1 - δ) ^ (U.card - T'.card) = 1 := by
    rw [sum_pow_mul_eq_add_pow]; simp
  have step1 : condProb n δ (fun T => Disjoint S T) =
      ∑ T ∈ (range n).powerset.filter (fun T => 0 ∈ T ∧ Disjoint S T),
        δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) := by
    unfold condProb
    rw [sum_filter]
    refine sum_congr rfl (fun T _ => ?_)
    split_ifs <;> rfl
  have step2 : ∑ T ∈ (range n).powerset.filter (fun T => 0 ∈ T ∧ Disjoint S T),
        δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) =
      ∑ T' ∈ U.powerset, δ ^ T'.card * ((1 - δ) ^ S.card * (1 - δ) ^ (U.card - T'.card)) := by
    refine sum_nbij' (fun T => T.erase 0) (fun T' => insert 0 T') ?_ ?_ ?_ ?_ ?_
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT ⊢
      obtain ⟨hTn, _, hST⟩ := hT
      intro x hx
      rw [mem_erase] at hx
      rw [hU, mem_erase, mem_sdiff]
      exact ⟨hx.1, hTn hx.2, fun hxS => disjoint_left.1 hST hxS hx.2⟩
    · intro T' hT'
      simp only [mem_filter, mem_powerset] at hT' ⊢
      refine ⟨?_, mem_insert_self _ _, ?_⟩
      · intro x hx
        rw [mem_insert] at hx
        rcases hx with rfl | hx
        · simp; omega
        · exact (mem_sdiff.1 (mem_of_mem_erase (hT' hx))).1
      · rw [disjoint_insert_right]
        refine ⟨h0, ?_⟩
        rw [disjoint_left]
        intro x hxS hxT
        exact (mem_sdiff.1 (mem_of_mem_erase (hT' hxT))).2 hxS
    · intro T hT
      simp only [mem_powerset, mem_filter] at hT
      exact insert_erase hT.2.1
    · intro T' hT'
      simp only [mem_powerset] at hT'
      apply erase_insert
      intro h
      have := hT' h
      rw [hU] at this
      exact (notMem_erase 0 _) this
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT
      obtain ⟨hTn, h0T, hST⟩ := hT
      have hsub : T.erase 0 ⊆ U := by
        intro x hx
        rw [mem_erase] at hx
        rw [hU, mem_erase, mem_sdiff]
        exact ⟨hx.1, hTn hx.2, fun hxS => disjoint_left.1 hST hxS hx.2⟩
      have hc := card_le_card hsub
      rw [card_erase_of_mem h0T] at hc ⊢
      have hT1 : 1 ≤ T.card := card_pos.2 ⟨0, h0T⟩
      rw [← pow_add]
      congr 2
      omega
  rw [step1, step2]
  simp_rw [mul_left_comm _ ((1 - δ) ^ S.card)]
  rw [← mul_sum, key, mul_one]

theorem bad_bound (n : ℕ) (δ : ℝ) (G : ℕ) (hn : 2 ≤ n) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (i : ℕ) (hi : i < n) :
    condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T) ≤ (1 - δ) ^ G := by
  rcases lt_or_ge (i + G) n with hlt | hge
  · calc condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T)
        ≤ condProb n δ (fun T => Disjoint (Icc (i + 1) (i + G)) T) := by
          apply condProb_mono n δ hδ0 hδ1
          rintro T _ ⟨_, hT⟩
          rw [disjoint_left]
          intro x hx hxT
          rw [mem_Icc] at hx
          have := hT (x - i) (by omega) (by omega)
          rw [show i + (x - i) = x by omega, Nat.mod_eq_of_lt (by omega)] at this
          exact this hxT
      _ = (1 - δ) ^ (Icc (i + 1) (i + G)).card := by
          apply condProb_disjoint n δ _ _ _ (by omega)
          · intro x hx
            rw [mem_Icc] at hx
            rw [mem_range]
            omega
          · rw [mem_Icc]
            omega
      _ = (1 - δ) ^ G := by
          rw [Nat.card_Icc]
          congr 1
          omega
  · calc condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T)
        ≤ condProb n δ (fun _ => False) := by
          apply condProb_mono n δ hδ0 hδ1
          rintro T h0T ⟨_, hT⟩
          have := hT (n - i) (by omega) (by omega)
          rw [show i + (n - i) = n by omega, Nat.mod_self] at this
          exact this h0T
      _ = 0 := by
          unfold condProb
          simp
      _ ≤ (1 - δ) ^ G := pow_nonneg (by linarith) _

end TopsConditionalProbabilityBounds

open Finset TopsConditionalProbabilityBounds in
theorem tops_choice_part_c : TopsChoiceThirdBound := by
  intro n δ G hn hδ0 hδ1
  classical
  have hunion : condProb n δ (fun T => ¬ CondC n T G) ≤
      ∑ i ∈ range n, condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T) := by
    unfold condProb
    rw [sum_comm]
    apply sum_le_sum
    intro T hT
    rw [mem_powerset] at hT
    split_ifs with h
    · obtain ⟨h0T, hC⟩ := h
      unfold CondC at hC
      push Not at hC
      obtain ⟨i, hiT, hi⟩ := hC
      have hir : i ∈ range n := hT hiT
      refine le_trans (le_of_eq ?_) (single_le_sum ?_ hir)
      · exact (if_pos ⟨h0T, hiT, hi⟩).symm
      · intro j _
        split_ifs
        · exact weight_nonneg n δ hδ0 hδ1 T
        · exact le_rfl
    · apply sum_nonneg
      intro j _
      split_ifs
      · exact weight_nonneg n δ hδ0 hδ1 T
      · exact le_rfl
  calc _ ≤ _ := hunion
    _ ≤ ∑ _i ∈ range n, (1 - δ) ^ G :=
        sum_le_sum (fun i hi => bad_bound n δ G hn hδ0 hδ1 i (mem_range.1 hi))
    _ = n * (1 - δ) ^ G := by rw [sum_const, card_range, nsmul_eq_mul]

end Formalism.G0
end
end

