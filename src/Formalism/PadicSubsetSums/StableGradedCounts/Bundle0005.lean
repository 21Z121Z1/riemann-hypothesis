import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0001

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRLemmaP
section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem two_numDerangements_le (n : ℕ) (hn : 1 ≤ n) : 2 * numDerangements n ≤ n.factorial := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _ => simp [numDerangements_one]
    | 2, _ => simp [numDerangements_add_two, numDerangements_zero, numDerangements_one, Nat.factorial]
    | k + 3, _ =>
      have h1 := ih (k + 1) (by omega) (by omega)
      have h2 := ih (k + 2) (by omega) (by omega)
      show 2 * numDerangements (k + 1 + 2) ≤ (k + 1 + 2).factorial
      rw [numDerangements_add_two, Nat.factorial_succ (k + 1 + 1)]
      rw [show k + 1 + 1 = k + 2 from rfl, Nat.factorial_succ (k + 1)] at *
      nlinarith [h1, h2]

theorem card_fixed_ge (β : Type) [Fintype β] [DecidableEq β] (hβ : 1 ≤ Fintype.card β) :
    (Fintype.card β).factorial ≤
      2 * ((univ : Finset (Equiv.Perm β)).filter (fun s => ∃ x, s x = x)).card := by
  have hd := card_derangements_eq_numDerangements β
  have h2 := two_numDerangements_le _ hβ
  have hsplit : ((univ : Finset (Equiv.Perm β)).filter (fun s => ∃ x, s x = x)).card +
      ((univ : Finset (Equiv.Perm β)).filter (fun s => ¬ ∃ x, s x = x)).card =
      (Fintype.card β).factorial := by
    rw [← Fintype.card_perm, ← Finset.card_univ]
    first
    | exact Finset.card_filter_add_card_filter_not _
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | exact Finset.card_filter_add_card_filter_neg _
  have hneg : ((univ : Finset (Equiv.Perm β)).filter (fun s => ¬ ∃ x, s x = x)).card =
      Fintype.card (derangements β) := by
    rw [Fintype.card_subtype]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
    exact Iff.rfl
  omega

section

variable {N : ℕ}

theorem stab_iff (A : Finset (Fin N)) (σ : Equiv.Perm (Fin N)) (h : ∀ x ∈ A, σ x ∈ A) (x : Fin N) :
    σ x ∈ A ↔ x ∈ A := by
  constructor
  · intro hx
    by_contra hxA
    have hsub : A.image σ ⊆ A := fun y hy => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact h z hz
    have hcard : (A.image σ).card = A.card := Finset.card_image_of_injective A σ.injective
    have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
    rw [← heq] at hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    exact hxA (σ.injective hzx ▸ hz)
  · exact h x

theorem card_stab_le (A : Finset (Fin N)) :
    ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card ≤
      A.card.factorial * (N - A.card).factorial := by
  have key : Fintype.card {σ : Equiv.Perm (Fin N) // ∀ x ∈ A, σ x ∈ A} ≤
      Fintype.card (Equiv.Perm {x // x ∈ A} × Equiv.Perm {x // x ∉ A}) := by
    refine Fintype.card_le_of_injective
      (fun σ => (σ.1.subtypePerm (fun x => stab_iff A σ.1 σ.2 x),
        σ.1.subtypePerm (fun x => not_congr (stab_iff A σ.1 σ.2 x)))) ?_
    rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ he
    simp only [Prod.mk.injEq] at he
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ A
    · have := congrArg (fun e => (e ⟨x, hx⟩ : Fin N)) he.1
      exact congrArg Fin.val (by simpa using this)
    · have := congrArg (fun e => (e ⟨x, hx⟩ : Fin N)) he.2
      exact congrArg Fin.val (by simpa using this)
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_coe,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe] at key
  calc _ = Fintype.card {σ : Equiv.Perm (Fin N) // ∀ x ∈ A, σ x ∈ A} := (Fintype.card_subtype _).symm
    _ ≤ _ := key

theorem card_good_ge (A : Finset (Fin N)) (h1 : 1 ≤ A.card) (h2 : 1 ≤ N - A.card) :
    A.card.factorial * (N - A.card).factorial ≤
      4 * ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧
        (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
  set P : Finset (Equiv.Perm {x // x ∈ A}) := univ.filter (fun s => ∃ x, s x = x) with hP
  set Q : Finset (Equiv.Perm {x // x ∉ A}) := univ.filter (fun s => ∃ x, s x = x) with hQ
  have hP1 : A.card.factorial ≤ 2 * P.card := by
    have := card_fixed_ge {x // x ∈ A} (by rw [Fintype.card_coe]; exact h1)
    rwa [Fintype.card_coe] at this
  have hc : Fintype.card {x // x ∉ A} = N - A.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have hQ1 : (N - A.card).factorial ≤ 2 * Q.card := by
    have := card_fixed_ge {x // x ∉ A} (by rw [hc]; exact h2)
    rwa [hc] at this
  have hinj : (P ×ˢ Q).card ≤ ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧
      (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    refine Finset.card_le_card_of_injOn (fun q => Equiv.Perm.subtypeCongr q.1 q.2) ?_ ?_
    · rintro ⟨α, β⟩ hq
      simp only [Finset.mem_coe, Finset.mem_product, hP, hQ, Finset.mem_filter, Finset.mem_univ,
        true_and] at hq
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun z hz => ?_, ⟨x.1, x.2, ?_⟩, ⟨y.1, y.2, ?_⟩⟩
      · simp [Equiv.Perm.subtypeCongr.left_apply, hz]
      · simp [Equiv.Perm.subtypeCongr.left_apply, x.2, hx]
      · simp [Equiv.Perm.subtypeCongr.right_apply, y.2, hy]
    · rintro ⟨α, β⟩ _ ⟨α', β'⟩ _ he
      simp only at he
      have hA : α = α' := by
        ext ⟨z, hz⟩
        have := congrArg (fun e : Equiv.Perm (Fin N) => e z) he
        have h' : α ⟨z, hz⟩ = α' ⟨z, hz⟩ := by
          simpa [Equiv.Perm.subtypeCongr.left_apply, hz] using this
        rw [h']
      have hB : β = β' := by
        ext ⟨z, hz⟩
        have := congrArg (fun e : Equiv.Perm (Fin N) => e z) he
        have h' : (β ⟨z, hz⟩ : Fin N) = β' ⟨z, hz⟩ := by
          simpa [Equiv.Perm.subtypeCongr.right_apply, hz] using this
        rw [h']
      rw [hA, hB]
  rw [Finset.card_product] at hinj
  calc A.card.factorial * (N - A.card).factorial ≤ (2 * P.card) * (2 * Q.card) :=
        Nat.mul_le_mul hP1 hQ1
    _ = 4 * (P.card * Q.card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 hinj

end

theorem prodMaxInvLeSq : LemmaP := by
  intro N a ha haN
  have key : ∀ σ : Equiv.Perm (Fin N),
      2 * (if (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A) then 1 else 0) + (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card ≤ 2 * (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
    intro σ
    have hsub : ((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y) ⊆ ((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A) := by
      intro A hA
      simp only [Finset.mem_filter] at hA ⊢
      exact ⟨hA.1, hA.2.1⟩
    have hle := Finset.card_le_card hsub
    split_ifs with hX
    · obtain ⟨A0, hA0c, hA0⟩ := hX
      have h1 : 1 ≤ (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
        apply Finset.card_pos.mpr
        exact ⟨A0, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA0c⟩, hA0⟩⟩
      by_cases hg : (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card = 0
      · omega
      · obtain ⟨A, hA⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hg)
        simp only [Finset.mem_filter, Finset.mem_powersetCard] at hA
        obtain ⟨⟨-, hAc⟩, hinv, ⟨x, hxA, hx⟩, ⟨y, hyA, hy⟩⟩ := hA
        have hyE : y ∉ A.erase x := fun h => hyA (Finset.mem_of_mem_erase h)
        have h2 : 1 < (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
          rw [Finset.one_lt_card]
          refine ⟨A, ?_, insert y (A.erase x), ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAc⟩, hinv⟩
          · simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
            refine ⟨?_, ?_⟩
            · rw [Finset.card_insert_of_notMem hyE, Finset.card_erase_of_mem hxA]
              have : 1 ≤ A.card := Finset.card_pos.mpr ⟨x, hxA⟩
              omega
            · intro z hz
              rcases Finset.mem_insert.mp hz with rfl | hz
              · rw [hy]
                exact Finset.mem_insert_self _ _
              · have hzA := Finset.mem_of_mem_erase hz
                have hzx := Finset.ne_of_mem_erase hz
                apply Finset.mem_insert_of_mem
                refine Finset.mem_erase.mpr ⟨?_, hinv z hzA⟩
                intro h
                apply hzx
                apply σ.injective
                rw [h, hx]
          · intro h
            apply hyA
            rw [h]
            exact Finset.mem_insert_self _ _
        omega
    · omega
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ (univ : Finset (Equiv.Perm (Fin N)))) => key σ)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hX : ∑ σ : Equiv.Perm (Fin N), (if (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A) then 1 else 0) =
      ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A))).card :=
    (Finset.card_filter _ _).symm
  have hs1 : ∑ σ : Equiv.Perm (Fin N), (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card =
      ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hs2 : ∑ σ : Equiv.Perm (Fin N), (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card =
      ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hfac : ∑ _A ∈ ((univ : Finset (Fin N)).powersetCard a), a.factorial * (N - a).factorial = N.factorial := by
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      ← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial haN.le
  have hinv : ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card ≤ N.factorial := by
    rw [← hfac]
    apply Finset.sum_le_sum
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    have := card_stab_le A
    rwa [hA.2] at this
  have hgood : N.factorial ≤ 4 * ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    rw [← hfac, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    have := card_good_ge A (by omega) (by omega)
    rwa [hA.2] at this
  rw [hX, hs1, hs2] at hsum
  omega

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.LagrangeBound
section
namespace Formalism.IrreducibleCountingLemmas.WindowSums

private theorem sum_le_of_unique {ι : Type} (s : Finset ι) (g : ι → ℕ) (r : ℕ)
    (hle : ∀ i ∈ s, g i ≤ r) (huniq : ∀ i ∈ s, ∀ j ∈ s, g i ≠ 0 → g j ≠ 0 → i = j) :
    ∑ i ∈ s, g i ≤ r := by
  classical
  by_cases h : ∃ i ∈ s, g i ≠ 0
  · obtain ⟨i, hi, hgi⟩ := h
    rw [← Finset.add_sum_erase s g hi]
    have h0 : ∑ j ∈ s.erase i, g j = 0 := Finset.sum_eq_zero fun j hj => by
      by_contra hne
      exact (Finset.ne_of_mem_erase hj) (huniq j (Finset.mem_of_mem_erase hj) i hi hne hgi)
    rw [h0, add_zero]
    exact hle i hi
  · push Not at h
    rw [Finset.sum_eq_zero h]
    exact Nat.zero_le _

theorem sumPadicValDifferencesLe : LagrangeBoundT := by
  intro l a A' r' Cc hl ha hA hlt hdiv c hc n hn
  have hfact : Fact l.Prime := ⟨hl⟩
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hnotL : ¬ (l : ℤ) ∣ (l : ℤ) ^ a - 1 := by
    intro h
    have h1 : (l : ℤ) ∣ (l : ℤ) ^ a := dvd_pow_self _ (by omega)
    have h2 : (l : ℤ) ∣ 1 := by
      have h3 := dvd_sub h1 h
      rwa [sub_sub_cancel] at h3
    exact hlZ.not_isUnit (isUnit_of_dvd_one h2)
  have hsep : ∀ x m1 m2 : ℤ, |m1 - m2| < l → (l : ℤ) ∣ x + m1 * ((l : ℤ) ^ a - 1) →
      (l : ℤ) ∣ x + m2 * ((l : ℤ) ^ a - 1) → m1 = m2 := by
    intro x m1 m2 hm h1 h2
    have h3 : (l : ℤ) ∣ (m1 - m2) * ((l : ℤ) ^ a - 1) := by
      have e : (m1 - m2) * ((l : ℤ) ^ a - 1) =
          (x + m1 * ((l : ℤ) ^ a - 1)) - (x + m2 * ((l : ℤ) ^ a - 1)) := by ring
      rw [e]
      exact dvd_sub h1 h2
    rcases hlZ.dvd_or_dvd h3 with h | h
    · have := Int.eq_zero_of_abs_lt_dvd h hm
      linarith
    · exact absurd h hnotL
  have hdv : ∀ z : ℤ, padicValInt l z ≠ 0 → (l : ℤ) ∣ z := by
    intro z hz
    have h := (padicValInt_dvd_iff (p := l) 1 z).mpr (Or.inr (Nat.one_le_iff_ne_zero.mpr hz))
    simpa using h
  have hneg : ∀ z : ℤ, padicValInt l (-z) = padicValInt l z := fun z => by simp [padicValInt]
  have hpow : ∀ k : ℕ, ((l ^ k - 1 : ℕ) : ℤ) = (l : ℤ) ^ k - 1 := fun k => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hl.pos)]
    push_cast
    ring
  have hper : ∀ c' ∈ Cc, (∑ n' ∈ Finset.range (2 * A'),
      if c' = c ∧ n' = n then 0
      else padicValInt l (((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)))) ≤
      if c' = c then 0 else r' := by
    intro c' hc'
    by_cases hcc : c' = c
    · subst hcc
      rw [if_pos rfl]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro n' hn'
      rw [Finset.mem_range] at hn'
      split_ifs with h
      · rfl
      · by_contra hne
        have h1 := hdv _ hne
        have hz : ((c' : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
            0 + ((n : ℤ) - n') * ((l : ℤ) ^ a - 1) := by ring
        rw [hz] at h1
        have h2 := hsep 0 ((n : ℤ) - n') 0 (by rw [sub_zero, abs_lt]; constructor <;> omega) h1 (by simp)
        exact h ⟨rfl, by omega⟩
    · rw [if_neg hcc]
      obtain ⟨ρ, hρ1, hρr, hρd⟩ := hdiv c hc c' hc' (Ne.symm hcc)
      apply sum_le_of_unique
      · intro n' hn'
        rw [Finset.mem_range] at hn'
        rw [if_neg (fun h => hcc h.1)]
        refine le_trans ?_ hρr
        rcases lt_or_gt_of_ne hcc with hlt' | hgt
        · have hdN : (l ^ a - 1) ∣ (c - c') * (l ^ ρ - 1) := by
            rw [← Int.natCast_dvd_natCast, Nat.cast_mul, hpow, hpow, Nat.cast_sub hlt'.le]
            exact hρd
          have hD := padicValIntShiftLe l a (c - c') ρ ((n : ℤ) - n') hl ha (by omega)
            (lt_of_le_of_lt (Nat.sub_le _ _) (hlt c hc)) hρ1 hdN
            (by rw [abs_lt]; constructor <;> omega)
          have hz : ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
              ((c - c' : ℕ) : ℤ) + ((n : ℤ) - n') * ((l : ℤ) ^ a - 1) := by
            rw [Nat.cast_sub hlt'.le]
            ring
          rw [hz]
          exact hD
        · have hdN : (l ^ a - 1) ∣ (c' - c) * (l ^ ρ - 1) := by
            rw [← Int.natCast_dvd_natCast, Nat.cast_mul, hpow, hpow, Nat.cast_sub hgt.le]
            have e : ((c' : ℤ) - c) * ((l : ℤ) ^ ρ - 1) = -(((c : ℤ) - c') * ((l : ℤ) ^ ρ - 1)) := by ring
            rw [e]
            exact dvd_neg.mpr hρd
          have hD := padicValIntShiftLe l a (c' - c) ρ ((n' : ℤ) - n) hl ha (by omega)
            (lt_of_le_of_lt (Nat.sub_le _ _) (hlt c' hc')) hρ1 hdN
            (by rw [abs_lt]; constructor <;> omega)
          have hz : ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
              -(((c' - c : ℕ) : ℤ) + ((n' : ℤ) - n) * ((l : ℤ) ^ a - 1)) := by
            rw [Nat.cast_sub hgt.le]
            ring
          rw [hz, hneg]
          exact hD
      · intro i hi j hj hgi hgj
        rw [Finset.mem_range] at hi hj
        rw [if_neg (fun h => hcc h.1)] at hgi hgj
        have h1 := hdv _ hgi
        have h2 := hdv _ hgj
        have ez : ∀ k : ℕ, ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + k * ((l : ℤ) ^ a - 1)) =
            ((c : ℤ) - c') + ((n : ℤ) - k) * ((l : ℤ) ^ a - 1) := fun k => by ring
        rw [ez] at h1 h2
        have := hsep _ _ _ (by rw [abs_lt]; constructor <;> omega) h1 h2
        omega
  calc (∑ c' ∈ Cc, ∑ n' ∈ Finset.range (2 * A'),
        if c' = c ∧ n' = n then 0
        else padicValInt l (((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1))))
      ≤ ∑ c' ∈ Cc, (if c' = c then 0 else r') := Finset.sum_le_sum hper
    _ = (Cc.card - 1) * r' := by
      rw [← Finset.add_sum_erase Cc _ hc, if_pos rfl, zero_add,
        Finset.sum_congr rfl (fun x hx => if_neg (Finset.ne_of_mem_erase hx)), Finset.sum_const,
        smul_eq_mul, Finset.card_erase_of_mem hc]

end Formalism.IrreducibleCountingLemmas.WindowSums
end

