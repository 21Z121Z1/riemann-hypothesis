import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombStripSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

theorem CombStripSum.proof (h1 : CombCfAtStair.Statement) (h2 : CombSortShift.Statement)
    (h3 : CombSortShiftDistinct.Statement) (h4 : CombExtendWord.Statement) :
    CombStripSum.Statement := by
  classical
  intro m n q lam hlam hq
  set l : Fin m → ℕ := fun j => lam j + stair m j with hl
  have hAlt : IsAlt (alternantPsum m (List.replicate n 1)) := isAlt_vandermonde_mul_prod _
  have hl_inj : Function.Injective l := by
    intro a b hab
    simp only [hl, stair] at hab
    have ha := a.isLt
    have hb := b.isLt
    rcases lt_trichotomy a b with h | h | h
    · have h' := hlam h.le
      have : (a : ℕ) < b := h
      omega
    · exact h
    · have h' := hlam h.le
      have : (b : ℕ) < a := h
      omega

  have key : ∀ i : Fin m, q ≤ l i → Function.Injective (Function.update l i (l i - q)) →
      ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m,
        (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧
        |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| =
          ((latticeWords n μ).card : ℚ) ∧
        ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam := by
    intro i hqi hinj
    obtain ⟨σ, μ, hμ, hμle, hσ0⟩ := h2 m lam hlam q i hqi hinj
    have hσ : ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k := hσ0
    have hsum : ∑ k, lam k = ∑ k, μ k + q := by
      have e1 : ∑ k, (μ k + stair m k) = ∑ k, Function.update l i (l i - q) k := by
        rw [← Equiv.sum_comp σ (Function.update l i (l i - q))]
        exact Finset.sum_congr rfl fun k _ => (hσ k).symm
      have e4 : ∑ k, l k = ∑ k, lam k + ∑ k, stair m k := Finset.sum_add_distrib
      have e3 : ∀ k, l k = Function.update l i (l i - q) k + if k = i then q else 0 := by
        intro k
        by_cases hk : k = i
        · subst hk; simp only [Function.update_self, if_true]; omega
        · simp [hk]
      have e2 : ∑ k, l k = ∑ k, Function.update l i (l i - q) k + q := by
        rw [Finset.sum_congr rfl (fun k _ => e3 k), Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      rw [Finset.sum_add_distrib] at e1
      omega
    obtain ⟨s, hs⟩ := h4 m n q μ lam hμ hlam hμle hsum
    refine ⟨μ, s, ⟨σ, hσ⟩, ?_, hs⟩
    have hu : Function.update l i (l i - q) = (fun k => μ k + stair m k) ∘ σ.symm := by
      funext k
      rw [Function.comp_apply, ← hσ (σ.symm k), Equiv.apply_symm_apply]
    rw [hu, cf_perm hAlt, abs_mul, h1 m n μ hμ]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
  have key' : ∀ i : Fin m, ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m,
      (q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) →
        (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧
        |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| =
          ((latticeWords n μ).card : ℚ) ∧
        ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam := by
    intro i
    by_cases h : q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))
    · obtain ⟨μ, s, hs⟩ := key i h.1 h.2
      exact ⟨μ, s, fun _ => hs⟩
    · exact ⟨fun _ => 0, fun _ => i, fun h' => absurd h' h⟩
  choose μ s hμs using key'
  set S := univ.filter
    (fun i : Fin m => q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) with hS
  change ∑ i : Fin m, (if q ≤ l i then
      |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) ≤ _
  have hsum_eq : ∑ i : Fin m, (if q ≤ l i then
      |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) =
      ∑ i ∈ S, ((latticeWords n (μ i)).card : ℚ) := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hqi : q ≤ l i
    · by_cases hinj : Function.Injective (Function.update l i (l i - q))
      · rw [if_pos hqi, if_pos ⟨hqi, hinj⟩, (hμs i ⟨hqi, hinj⟩).2.1]
      · rw [if_pos hqi, if_neg (fun h => hinj h.2)]
        simp only [Function.Injective, not_forall] at hinj
        obtain ⟨a, b, hab, hne⟩ := hinj
        rw [cf_eq_zero_of_eq hAlt hne hab, abs_zero]
    · rw [if_neg hqi, if_neg (fun h => hqi h.1)]
  rw [hsum_eq]
  have hcard : ∑ i ∈ S, (latticeWords n (μ i)).card ≤ (latticeWords (n + q) lam).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn (fun x => Fin.append x.2 (s x.1)) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_sigma] at hx
      exact (hμs x.1 (Finset.mem_filter.mp hx.1).2).2.2 x.2 hx.2
    · rintro ⟨i, w⟩ hx ⟨j, w'⟩ hy hxy
      rw [Finset.mem_coe, Finset.mem_sigma] at hx hy
      simp only at hxy hx hy
      have hw : w = w' := by
        funext k
        have := congrFun hxy (Fin.castAdd q k)
        simpa only [Fin.append_left] using this
      subst hw
      have hμij : μ i = μ j := by
        funext k
        have a1 := (Finset.mem_filter.mp hx.2).2.2 k
        have a2 := (Finset.mem_filter.mp hy.2).2.2 k
        rw [← a1, ← a2]
      have hSi := (Finset.mem_filter.mp hx.1).2
      have hSj := (Finset.mem_filter.mp hy.1).2
      have hij : i = j := by
        by_contra hij
        obtain ⟨σ, hσ⟩ := (hμs i hSi).1
        obtain ⟨τ, hτ⟩ := (hμs j hSj).1
        refine h3 m l hl_inj q hq i j hij hSi.1 hSj.1 σ τ ?_
        funext k
        rw [Function.comp_apply, Function.comp_apply, hσ k, hτ k, hμij]
      subst hij
      rfl
  exact_mod_cast hcard

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowCount.proof : CombTableauRowCount.Statement := by
  intro m lam T t i
  unfold pcnt rowWord
  apply Finset.card_bij' (fun s _ => T.symm s) (fun p _ => T p)
  · intro s hs
    simp only [mem_filter, mem_univ, true_and, Equiv.apply_symm_apply] at hs ⊢
    exact ⟨hs.2, hs.1⟩
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, Equiv.symm_apply_apply] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · intro s _
    simp
  · intro p _
    simp

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowLattice.proof : CombTableauRowLattice.Statement := by
  classical
  intro m lam hlam T hT t i j hij
  have hmem : ∀ p : youngCells lam, p.1.1 = j → (i, p.1.2) ∈ youngCells lam := by
    intro p hp
    have hp' := p.2
    simp only [youngCells, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_range] at hp' ⊢
    have h1 : p.1.2 < lam i := by
      rw [hp] at hp'
      exact lt_of_lt_of_le hp'.2 (hlam hij)
    refine ⟨lt_of_lt_of_le h1 ?_, h1⟩
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (lam k)) (Finset.mem_univ i)
  let f : youngCells lam → youngCells lam := fun p =>
    if h : p.1.1 = j then ⟨(i, p.1.2), hmem p h⟩ else p
  have hf : ∀ p : youngCells lam, ∀ h : p.1.1 = j, f p = ⟨(i, p.1.2), hmem p h⟩ := by
    intro p h
    simp only [f, dif_pos h]
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [hf p hp.1]
    refine ⟨rfl, lt_of_le_of_lt ?_ hp.2⟩
    have := hT ⟨(i, p.1.2), hmem p hp.1⟩ p (by simpa [hp.1] using hij) le_rfl
    exact_mod_cast this
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
    rw [hf p hp.1, hf q hq.1] at hpq
    have h2 : p.1.2 = q.1.2 := by
      have := congrArg (fun x : youngCells lam => x.1.2) hpq
      simpa using this
    apply Subtype.ext
    exact Prod.ext (hp.1.trans hq.1.symm) h2

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowPrefix
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowPrefix.proof : CombTableauRowPrefix.Statement := by
  intro m lam T hT t
  set c := T.symm t with hc
  have hTc : T c = t := by simp [hc]
  have key : ∀ p : youngCells lam, p.1.1 = c.1.1 →
      ((T p : ℕ) < (t : ℕ) ↔ p.1.2 < c.1.2) := by
    intro p hp
    constructor
    · intro hlt
      by_contra hle'
      have hle := not_lt.mp hle'
      have h := hT c p hp.symm.le hle
      rw [hTc] at h
      exact absurd hlt (not_lt.mpr (Fin.le_def.mp h))
    · intro hlt
      have hle : T p ≤ T c := hT p c hp.le hlt.le
      have hne : p ≠ c := by
        intro h
        rw [h] at hlt
        exact lt_irrefl _ hlt
      have hne' : T p ≠ T c := fun h => hne (T.injective h)
      rw [hTc] at hle hne'
      exact Fin.lt_def.mp (lt_of_le_of_ne hle hne')
  have hcmem : c.1 ∈ youngCells lam := c.2
  simp only [youngCells, mem_filter, mem_product, mem_univ, true_and, mem_range] at hcmem
  rw [show (univ.filter fun p : youngCells lam => p.1.1 = c.1.1 ∧ (T p : ℕ) < (t : ℕ)) =
      univ.filter fun p : youngCells lam => p.1.1 = c.1.1 ∧ p.1.2 < c.1.2 from
    filter_congr fun p _ => and_congr_right (key p)]
  refine Eq.trans ?_ (card_range c.1.2)
  refine card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    exact mem_range.mpr hp.2
  · intro p hp q hq hpq
    simp only [mem_filter, mem_univ, true_and] at hp hq
    exact Subtype.ext (Prod.ext (hp.1.trans hq.1.symm) hpq)
  · intro k hk
    rw [mem_range] at hk
    refine ⟨⟨(c.1.1, k), ?_⟩, ?_, rfl⟩
    · simp only [youngCells, mem_filter, mem_product, mem_univ, true_and, mem_range]
      exact ⟨by omega, by omega⟩
    · simp [hk]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombVandermondeSucc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem CombVandermondeSucc.proof : CombVandermondeSucc.Statement := by
  intro n v
  unfold vandermondeOf
  have hI : ∀ {k : ℕ} (i : Fin k), Ioi i = univ.filter (fun j => i < j) := by
    intro k i; ext j; simp
  simp only [hI, Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_lt_succ_iff]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombWordOfTableau
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

theorem CombWordOfTableau.proof (h1 : CombTableauRowCount.Statement)
    (h2 : CombTableauRowPrefix.Statement) (h3 : CombTableauRowLattice.Statement)
    (h4 : CombYoungRowCard.Statement) : CombWordOfTableau.Statement := by
  intro m lam hlam T hT
  refine ⟨?_, fun t => ?_⟩
  · simp only [latticeWords, mem_filter, mem_univ, true_and]
    refine ⟨fun t _ i j hij => ?_, fun i => ?_⟩
    · rw [h1 m lam T t j, h1 m lam T t i]
      exact h3 m lam hlam T hT t i j hij
    · rw [h1 m lam T _ i, ← h4 m lam i]
      congr 1
      exact Finset.filter_congr fun p _ => by simp [(T p).isLt]
  · unfold cellOfWord
    refine Prod.ext rfl ?_
    show pcnt (rowWord T) (t : ℕ) ((T.symm t).1.1) = (T.symm t).1.2
    rw [h1 m lam T t _]
    exact h2 m lam T hT t

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombYoungRowCard
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem CombYoungRowCard.proof : CombYoungRowCard.Statement := by
  intro m lam i
  rw [← Finset.card_range (lam i)]
  refine Finset.card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p hp
    have hp' : p.1.1 = i := (mem_filter.1 hp).2
    have hc : p.1.2 < lam p.1.1 := (mem_filter.1 p.2).2
    rw [hp'] at hc
    exact mem_range.2 hc
  · intro p hp q hq h
    have hp' : p.1.1 = i := (mem_filter.1 hp).2
    have hq' : q.1.1 = i := (mem_filter.1 hq).2
    exact Subtype.ext (Prod.ext (hp'.trans hq'.symm) h)
  · intro c hc
    have hc' : c < lam i := mem_range.1 hc
    have hmem : ((i, c) : Fin m × ℕ) ∈ youngCells lam := by
      unfold youngCells
      refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_range.2 ?_⟩, hc'⟩
      exact lt_of_lt_of_le hc'
        (Finset.single_le_sum (fun j _ => Nat.zero_le (lam j)) (mem_univ i))
    exact ⟨⟨(i, c), hmem⟩, mem_filter.2 ⟨mem_univ _, rfl⟩, rfl⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFrobeniusDimensionFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Comb

theorem FrobeniusDimensionFormula.proof (h1 : CombTableEqWords.Statement)
    (h2 : CombCfAtStair.Statement) (h3 : CombCfVandermondePsumOne.Statement) :
    FrobeniusDimensionFormula.Statement := by
  intro m lam hlam
  have hsum : ∑ i, (lam i + stair m i) = ∑ i, stair m i + ∑ i, lam i := by
    rw [Finset.sum_add_distrib, add_comm]
  have e := h3 m (∑ i, lam i) (fun i => lam i + stair m i) hsum
  rw [h2 m (∑ i, lam i) lam hlam] at e
  rw [h1 m lam hlam, e]
  simp only [stair]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookDimensionSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem HookDimensionSum.proof (h1 : CombTableEqWords.Statement)
    (h2 : CombHookShapeFacts.Statement) (h3 : CombHookCount.Statement) :
    HookDimensionSum.Statement := by
  intro k hk
  have hterm : ∀ l ∈ Finset.range k,
      numStandardTable (hookShape k k l) = (k - 1).choose l := by
    intro l hl
    have hl' : l < k := Finset.mem_range.mp hl
    obtain ⟨hanti, hsum⟩ := h2 k k l hl' le_rfl
    rw [h1 k (hookShape k k l) hanti, hsum]
    exact h3 k k l hl' le_rfl
  rw [Finset.sum_congr rfl hterm]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  simpa using Nat.sum_range_choose n

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaC
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem numStandardTable_eq_frobDim (h1 : FrobeniusDimensionFormula.Statement) {m : ℕ}
    (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (numStandardTable lam : ℚ) = GroundTheory.Heights₂.Heights.frobDim lam := by
  rw [h1 m lam hlam, GroundTheory.Heights₂.Heights.frobDim]
  congr 2
  unfold vandermondeOf
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]

theorem LemmaC.proof (h1 : FrobeniusDimensionFormula.Statement) : LemmaC.Statement := by
  intro r a nu hnu
  have hsum : Antitone (fun i => a + nu i) := fun i j hij => Nat.add_le_add_left (hnu hij) a
  have hrect : Antitone (rectangle r a) := fun _ _ _ => le_rfl
  have hb := GroundTheory.Heights₂.Heights.FrobeniusRectangleBound.intersectionNumber_baseChange r a nu hnu
  rw [← numStandardTable_eq_frobDim h1 _ hsum, ← numStandardTable_eq_frobDim h1 nu hnu,
    show (fun _ : Fin r => a) = rectangle r a from rfl,
    ← numStandardTable_eq_frobDim h1 _ hrect] at hb
  exact_mod_cast hb

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PTotalIdentity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem prod_fin_add_one_eq_factorial (n : ℕ) :
    ∏ j : Fin n, ((j : ℚ) + 1) = (n.factorial : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Nat.factorial_succ]
    push_cast
    ring

theorem prod_fin_add_two_eq_factorial (n : ℕ) :
    ∏ j : Fin n, ((j : ℚ) + 2) = ((n + 1).factorial : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Nat.factorial_succ (n + 1)]
    push_cast
    ring

theorem TotalIdentity.proof (h1 : FrobeniusDimensionFormula.Statement)
    (h2 : CombVandermondeSucc.Statement) : TotalIdentity.Statement := by
  intro r a hr _
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  set lam : Fin (n + 1) → ℕ := fun i => a + if (i : ℕ) = 0 then 1 else 0 with hlam
  have hanti : Antitone lam := by
    intro i j hij
    have : (i : ℕ) ≤ j := hij
    simp only [lam]
    split_ifs <;> omega
  have hrect : Antitone (rectangle (n + 1) a) := fun _ _ _ => le_rfl
  have e1 := h1 (n + 1) lam hanti
  have e2 := h1 (n + 1) (rectangle (n + 1) a) hrect
  rw [h2] at e1 e2
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, lam, rectangle, Fin.val_zero, Fin.val_succ,
    Nat.add_one_ne_zero, if_true, if_false, add_zero, Nat.add_sub_cancel, Nat.sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at e1 e2
  set V := vandermondeOf fun j : Fin n => ((a + (n - ((j : ℕ) + 1)) : ℕ) : ℚ) with hV
  set D := ∏ x : Fin n, (((a + (n - ((x : ℕ) + 1))).factorial : ℕ) : ℚ) with hD
  have hP1 : ∏ j : Fin n, (((a + n : ℕ) : ℚ) - ((a + (n - ((j : ℕ) + 1)) : ℕ) : ℚ)) =
      (n.factorial : ℚ) := by
    rw [← prod_fin_add_one_eq_factorial]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h' : (j : ℕ) + 1 ≤ n := j.isLt
    push_cast [Nat.cast_sub h']
    ring
  have hP2 : ∏ j : Fin n, (((a + 1 + n : ℕ) : ℚ) - ((a + (n - ((j : ℕ) + 1)) : ℕ) : ℚ)) =
      ((n + 1).factorial : ℚ) := by
    rw [← prod_fin_add_two_eq_factorial]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h' : (j : ℕ) + 1 ≤ n := j.isLt
    push_cast [Nat.cast_sub h']
    ring
  rw [hP2, show a + 1 + n * a = (n + 1) * a + 1 by ring, show a + 1 + n = a + n + 1 by ring,
    Nat.factorial_succ ((n + 1) * a), Nat.factorial_succ (a + n)] at e1
  rw [hP1] at e2
  rw [Nat.factorial_succ n] at e1
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => by positivity
  have hf0 : ((a + n).factorial : ℚ) ≠ 0 := by positivity
  apply Nat.cast_injective (R := ℚ)
  push_cast
  rw [e1, e2]
  push_cast
  field_simp
  ring

end GroundTheory.Heights₂.Heights.RestTerms
end

