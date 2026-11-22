import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountUp
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0002
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ChainDim

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KLettersDegEven
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

theorem strip_cons {r : ℕ} {nu mu : Fin r → ℤ} {g e : ℕ} (h : Strip nu mu g) {f f' : ℤ} (h1 : f ≤ f')
    (h2 : ∀ c : Fin r, c.val = 0 → nu c ≤ f) (he : f' - f + g = e) :
    Strip (Fin.cons f' nu : Fin (r + 1) → ℤ) (Fin.cons f mu) e := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun c => ?_) i
    · simpa using h1
    · simpa using h.1 c
  · intro i j
    refine Fin.cases ?_ (fun j' => ?_) j
    · intro hij; simp at hij
    · refine Fin.cases ?_ (fun c => ?_) i
      · intro hij
        simp only [Fin.cons_succ, Fin.cons_zero]
        exact h2 j' (by simpa using hij.symm)
      · intro hij
        simp only [Fin.cons_succ]
        exact h.2.1 c j' (by simpa using hij)
  · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have := h.2.2
    linarith

def fstOf {s : ℕ} (A : Fin s → ℕ) (cp : ℕ → ℤ) (LLv : ChainLetters (2 * s + 1)) (n : ℕ) : ℤ :=
  if n % 2 = 1 then cp ((n - 1) / 2) else
    if h : (n - 2) / 2 < s then cp ((n - 2) / 2) + A ⟨(n - 2) / 2, h⟩ - LLv.deg ⟨2 * ((n - 2) / 2), by omega⟩ else 0

theorem fstOf_odd {s : ℕ} (A : Fin s → ℕ) (cp : ℕ → ℤ) (LLv : ChainLetters (2 * s + 1)) (i : ℕ) :
    fstOf A cp LLv (2 * i + 1) = cp i := by
  unfold fstOf
  rw [if_pos (by omega)]
  congr 1
  omega

theorem fstOf_even {s : ℕ} (A : Fin s → ℕ) (cp : ℕ → ℤ) (LLv : ChainLetters (2 * s + 1)) (i : Fin s) :
    fstOf A cp LLv (2 * i.val + 2) = cp i + A i - LLv.deg ⟨2 * i.val, by omega⟩ := by
  have hi := i.isLt
  unfold fstOf
  rw [if_neg (by omega)]
  have hk : (2 * i.val + 2 - 2) / 2 = i.val := by omega
  rw [dif_pos (by omega)]
  simp only [hk]

def muOf {s r : ℕ} (fst : ℕ → ℤ) (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ) : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ :=
  fun l => if l.val = 0 then 0 else Fin.cons (fst l.val) (ka ⟨l.val - 1, by omega⟩)

theorem muOf_succ {s r : ℕ} (fst : ℕ → ℤ) (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ) (n : ℕ) (h : n + 1 < 2 * s + 1 + 1) :
    muOf fst ka ⟨n + 1, h⟩ = Fin.cons (fst (n + 1)) (ka ⟨n, by omega⟩) := by
  simp [muOf]

structure LevFacts {s r : ℕ} (A0 : ℤ) (A C : Fin s → ℕ) (cp : ℕ → ℤ) (LLv : ChainLetters (2 * s + 1))
    (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ) : Prop where
  c0 : cp 0 = A0
  A0nn : 0 ≤ A0
  vecv : ∀ a, LLv.vec a = decide (a.val % 2 = 0)
  hw : ∀ i : Fin s, (LLv.deg ⟨2 * i.val, by omega⟩ : ℤ) ≤ A i
  hc : ∀ i : Fin s, cp (i.val + 1) ≤ cp i.val + A i - LLv.deg ⟨2 * i.val, by omega⟩
  he : ∀ i : Fin s, cp i.val + A i - LLv.deg ⟨2 * i.val, by omega⟩ - cp (i.val + 1) +
    LLv.deg ⟨2 * i.val + 1, by omega⟩ = C i
  hb : ∀ (i : Fin s) (c : Fin r), c.val = 0 → ka ⟨2 * i.val + 1, by omega⟩ c ≤ cp i.val
  hd : ∀ (i : Fin s) (c : Fin r), c.val = 0 → ka ⟨2 * i.val + 1, by omega⟩ c ≤ cp (i.val + 1)
  hf : ∀ c : Fin r, c.val = 0 → ka (Fin.last _) c ≤ cp s

theorem kLetters_deg_odd {s : ℕ} (A0 : ℕ) (A C : Fin s → ℕ) (i : Fin s) :
    (kLetters A0 A C).deg ⟨2 * i.val + 1, by omega⟩ = A i := by
  have hi := i.isLt
  have h0 : ¬ (2 * i.val + 1 = 0) := by omega
  have h1 : (2 * i.val + 1 - 1) / 2 < s := by omega
  have h2 : (2 * i.val + 1) % 2 = 1 := by omega
  simp only [kLetters, Fin.val_mk]
  rw [if_neg h0, dif_pos h1, if_pos h2]
  congr 1
  ext
  simp only
  omega

theorem kLetters_deg_even {s : ℕ} (A0 : ℕ) (A C : Fin s → ℕ) (i : Fin s) :
    (kLetters A0 A C).deg ⟨2 * i.val + 2, by omega⟩ = C i := by
  have hi := i.isLt
  have h0 : ¬ (2 * i.val + 2 = 0) := by omega
  have h1 : (2 * i.val + 2 - 1) / 2 < s := by omega
  have h2 : ¬ ((2 * i.val + 2) % 2 = 1) := by omega
  simp only [kLetters, Fin.val_mk]
  rw [if_neg h0, dif_pos h1, if_neg h2]
  congr 1
  ext
  simp only
  omega

theorem chain_of_facts {s r : ℕ} {A0 : ℤ} {A C : Fin s → ℕ} {cp : ℕ → ℤ} {LLv : ChainLetters (2 * s + 1)}
    {ka : Fin (2 * s + 1 + 1) → Fin r → ℤ} (hF : LevFacts A0 A C cp LLv ka) (hch : IsChain LLv ka) :
    IsChain (kLetters A0.toNat A C) (muOf (fstOf A cp LLv) ka) ∧
      Inter (muOf (fstOf A cp LLv) ka (Fin.last _)) (ka (Fin.last _)) := by
  constructor
  · refine ⟨by unfold muOf; simp, ?_⟩
    rintro ⟨a, ha⟩
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    ·
      have hv : (kLetters A0.toNat A C).vec ⟨0, ha⟩ = true := by simp [kLetters]
      rw [if_pos hv]
      have e0 : muOf (fstOf A cp LLv) ka (Fin.castSucc ⟨0, ha⟩) = 0 := by unfold muOf; simp
      have e1 : muOf (fstOf A cp LLv) ka (Fin.succ ⟨0, ha⟩) = Fin.cons A0 0 := by
        unfold muOf
        simp only [Fin.succ_mk, Nat.zero_add]
        rw [if_neg (by omega)]
        have := fstOf_odd A cp LLv 0
        simp only [Nat.mul_zero, Nat.zero_add] at this
        rw [this, hF.c0]
        congr 1
        exact hch.1
      have hdeg : (kLetters A0.toNat A C).deg ⟨0, ha⟩ = A0.toNat := by simp [kLetters]
      rw [e0, e1, hdeg]
      refine ⟨?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun c => ?_) i
        · simpa using hF.A0nn
        · simp
      · intro i j
        refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij; simp at hij
        · intro _; simp
      · rw [Fin.sum_univ_succ]
        simp [Int.toNat_of_nonneg hF.A0nn]
    · rcases Nat.even_or_odd' a with ⟨i, rfl | rfl⟩
      ·
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have hi : i' < s := by omega
        have hv : (kLetters A0.toNat A C).vec ⟨2 * (i' + 1), ha⟩ = false := by
          simp [kLetters]
        rw [if_neg (by rw [hv]; simp)]
        have hst := hch.2 ⟨2 * i' + 1, by omega⟩
        rw [if_neg (by rw [hF.vecv]; simp)] at hst
        have e0 : muOf (fstOf A cp LLv) ka (Fin.castSucc ⟨2 * (i' + 1), ha⟩) =
            Fin.cons (cp i' + A ⟨i', hi⟩ - LLv.deg ⟨2 * i', by omega⟩) (ka (Fin.castSucc ⟨2 * i' + 1, by omega⟩)) := by
          have h := muOf_succ (fstOf A cp LLv) ka (2 * i' + 1) (by omega)
          rw [show fstOf A cp LLv (2 * i' + 1 + 1) = _ from fstOf_even A cp LLv ⟨i', hi⟩] at h
          exact h
        have e1 : muOf (fstOf A cp LLv) ka (Fin.succ ⟨2 * (i' + 1), ha⟩) =
            Fin.cons (cp (i' + 1)) (ka (Fin.succ ⟨2 * i' + 1, by omega⟩)) := by
          have h := muOf_succ (fstOf A cp LLv) ka (2 * (i' + 1)) (by omega)
          rw [fstOf_odd A cp LLv (i' + 1)] at h
          exact h
        have hdeg : (kLetters A0.toNat A C).deg ⟨2 * (i' + 1), ha⟩ = C ⟨i', hi⟩ :=
          kLetters_deg_even A0.toNat A C ⟨i', hi⟩
        rw [e0, e1, hdeg]
        exact strip_cons hst (hF.hc ⟨i', hi⟩) (fun c hc => hF.hd ⟨i', hi⟩ c hc) (hF.he ⟨i', hi⟩)
      ·
        have hi : i < s := by omega
        have hv : (kLetters A0.toNat A C).vec ⟨2 * i + 1, ha⟩ = true := by
          simp [kLetters]
        rw [if_pos hv]
        have hst := hch.2 ⟨2 * i, by omega⟩
        rw [if_pos (by rw [hF.vecv]; simp)] at hst
        have e0 : muOf (fstOf A cp LLv) ka (Fin.castSucc ⟨2 * i + 1, ha⟩) =
            Fin.cons (cp i) (ka (Fin.castSucc ⟨2 * i, by omega⟩)) := by
          have h := muOf_succ (fstOf A cp LLv) ka (2 * i) (by omega)
          rw [fstOf_odd A cp LLv i] at h
          exact h
        have e1 : muOf (fstOf A cp LLv) ka (Fin.succ ⟨2 * i + 1, ha⟩) =
            Fin.cons (cp i + A ⟨i, hi⟩ - LLv.deg ⟨2 * i, by omega⟩) (ka (Fin.succ ⟨2 * i, by omega⟩)) := by
          have h := muOf_succ (fstOf A cp LLv) ka (2 * i + 1) (by omega)
          rw [show fstOf A cp LLv (2 * i + 1 + 1) = _ from fstOf_even A cp LLv ⟨i, hi⟩] at h
          exact h
        have hdeg : (kLetters A0.toNat A C).deg ⟨2 * i + 1, ha⟩ = A ⟨i, hi⟩ :=
          kLetters_deg_odd A0.toNat A C ⟨i, hi⟩
        rw [e0, e1, hdeg]
        refine strip_cons hst (by have := hF.hw ⟨i, hi⟩; linarith) (fun c hc => hF.hb ⟨i, hi⟩ c hc) (by ring)
  ·
    have hst := hch.2 (Fin.last (2 * s))
    rw [if_pos (by rw [hF.vecv]; simp)] at hst
    have e1 : muOf (fstOf A cp LLv) ka (Fin.last (2 * s + 1)) =
        Fin.cons (cp s) (ka (Fin.castSucc (Fin.last (2 * s)))) := by
      have h := muOf_succ (fstOf A cp LLv) ka (2 * s) (by omega)
      rw [fstOf_odd A cp LLv s] at h
      exact h
    rw [Fin.succ_last] at hst
    rw [e1]
    intro i
    constructor
    · simp only [Fin.cons_succ]
      exact hst.1 i
    · rcases Nat.eq_zero_or_pos i.val with h0 | hp
      · have : i.castSucc = 0 := Fin.ext (by simp [h0])
        rw [this, Fin.cons_zero]
        exact hF.hf i h0
      · have : i.castSucc = Fin.succ ⟨i.val - 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [this, Fin.cons_succ]
        exact hst.2.1 ⟨i.val - 1, by omega⟩ i (by simp; omega)

def LevFactsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ z, SrcOK C0 CE1 CE2 X j m rz ry z →
        LevFacts ((X.seg C0 CE1 CE2 j).A0 X.p)
          (fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i)
          (fun i => coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i)
          (fun l => cap X.p (X.seg C0 CE1 CE2 j) z.1 l)
          ((BD C0 CE1 CE2 X j m z.1).lettersAt z.2.1.1 z.2.1.2) z.2.2

def SrcInjAt : Prop :=
  ∀ (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (m : ℝ)
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) (z z' : FinalTheorems (segS X.TT j) X.m (X.seg C0 CE1 CE2 j).t),
    SrcOK C0 CE1 CE2 X j m rz ry z → SrcOK C0 CE1 CE2 X j m rz ry z' → z.2.2 = z'.2.2 → z.2.1.2 = z'.2.1.2 → z = z'

theorem muOf_inj {s r : ℕ} {fst fst' : ℕ → ℤ} {ka ka' : Fin (2 * s + 1 + 1) → Fin r → ℤ}
    (h : muOf fst ka = muOf fst' ka') (hl : ka (Fin.last _) = ka' (Fin.last _)) : ka = ka' := by
  funext l
  by_cases hlt : l.val + 1 < 2 * s + 1 + 1
  · have e := congrFun h ⟨l.val + 1, hlt⟩
    rw [muOf_succ, muOf_succ] at e
    funext c
    have e2 := congrFun e c.succ
    simpa only [Fin.cons_succ] using e2
  · have hl' : l = Fin.last _ := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [hl']
    exact hl

theorem matchUp_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hF : LevFactsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hI : SrcInjAt) : MatchUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hH hc j m hm rz ry hd
  refine ⟨fun z => (muOf (fstOf (fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i)
      (fun l => cap X.p (X.seg C0 CE1 CE2 j) z.1 l) ((BD C0 CE1 CE2 X j m z.1).lettersAt z.2.1.1 z.2.1.2)) z.2.2,
      z.2.2 (Fin.last _), z.2.1.2), ?_, ?_⟩
  · intro z hz z' hz' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun t => t.2.1) h
    have h3 := congrArg (fun t => t.2.2) h
    exact hI C0 CE1 CE2 X j m rz ry z z' hz hz' (muOf_inj h1 h2) h3
  · intro z hz
    have h := chain_of_facts (hF X hD hH hc j m hm rz ry hd z hz) hz.2.2.1
    exact ⟨h.1, h.2, rfl, rfl⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegLow
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Finset

theorem finsum_classes {β γ : Type*} [DecidableEq γ] (K : β → Prop) (hfin : {b | K b}.Finite) (f : β → ℕ)
    (key : β → γ) (DC : Finset γ) (F : γ → β → ℕ) (G : β → ℕ)
    (hF1 : ∀ d b, K b → key b = d → F d b = f b) (hF0 : ∀ d b, ¬ (K b ∧ key b = d) → F d b = 0)
    (hG1 : ∀ b, K b → G b = f b) (hG0 : ∀ b, ¬ K b → G b = 0) :
    ∑ d ∈ DC, ∑ᶠ b, F d b ≤ ∑ᶠ b, G b := by
  classical
  have hFs : ∀ d, ∑ᶠ b, F d b = ∑ b ∈ hfin.toFinset, F d b := fun d => by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    rw [Function.mem_support] at hb
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hK
    exact hb (hF0 d b (fun h => hK h.1))
  have hGs : ∑ᶠ b, G b = ∑ b ∈ hfin.toFinset, G b := by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    rw [Function.mem_support] at hb
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hK
    exact hb (hG0 b hK)
  rw [hGs, Finset.sum_congr rfl (fun d _ => hFs d), Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  have hK : K b := (Set.Finite.mem_toFinset hfin).mp hb
  rw [hG1 b hK]

  have hcl : ∀ d ∈ DC, F d b = if d = key b then f b else 0 := fun d _ => by
    by_cases hd : d = key b
    · rw [if_pos hd, hF1 d b hK hd.symm]
    · rw [if_neg hd, hF0 d b (fun h => hd h.2.symm)]
  rw [Finset.sum_congr rfl hcl, Finset.sum_ite_eq']
  split_ifs <;> omega

def dset (m P g : ℕ) : Finset (Fin (m + 1) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (m + 1) => Finset.range P).filter fun ρ => ∑ c, ρ c ≤ g ∧ P ∣ g - ∑ c, ρ c

theorem card_tuple (m n : ℕ) : (Finset.Nat.antidiagonalTuple (m + 1) n).card = sd m n := by
  have h := card_tuples (m + 1) n (Nat.succ_pos m)
  have e : {P : Fin (m + 1) → ℕ // ∑ i, P i = n} ≃ (Finset.Nat.antidiagonalTuple (m + 1) n) :=
    Equiv.subtypeEquivRight fun P => Finset.Nat.mem_antidiagonalTuple.symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe] at h
  rw [h]
  unfold sdXi sd
  congr 1

theorem digit_sum (m P g : ℕ) (hP : 0 < P) : ∑ ρ ∈ dset m P g, sd m ((g - ∑ c, ρ c) / P) = sd m g := by
  classical
  simp only [← card_tuple]

  have hdec : ∀ e : Fin (m + 1) → ℕ, ∑ c, e c = ∑ c, e c % P + P * ∑ c, e c / P := fun e => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ => (Nat.mod_add_div (e c) P).symm)
  have hmap : ∀ e ∈ Finset.Nat.antidiagonalTuple (m + 1) g, (fun c => e c % P) ∈ dset m P g := by
    intro e he
    rw [Finset.Nat.mem_antidiagonalTuple] at he
    have h := hdec e
    rw [he] at h
    simp only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun c => Nat.mod_lt _ hP, le_of_le_of_eq (Nat.le_add_right _ _) h.symm, ?_⟩
    exact ⟨∑ c, e c / P, by rw [h, Nat.add_sub_cancel_left]⟩
  symm
  rw [Finset.card_eq_sum_card_fiberwise (s := Finset.Nat.antidiagonalTuple (m + 1) g) hmap]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hρ
  obtain ⟨hρP, hρle, hρdvd⟩ := hρ
  apply Finset.card_nbij' (fun e c => e c / P) (fun q c => ρ c + P * q c)
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at he
    obtain ⟨hsum, hmod⟩ := he
    rw [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple]
    have h := hdec e
    rw [hsum] at h
    have hr : ∑ c, e c % P = ∑ c, ρ c := by rw [← hmod]
    show ∑ c, e c / P = (g - ∑ c, ρ c) / P
    rw [h, hr, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hP]
  · intro q hq
    rw [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
    constructor
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq, Nat.mul_div_cancel' hρdvd]
      omega
    · funext c
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hρP c)]
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    funext c
    have h : e c % P = ρ c := congrFun he.2 c
    show ρ c + P * (e c / P) = e c
    rw [← h, Nat.mod_add_div]
  · intro q _
    funext c
    show (ρ c + P * q c) / P = q c
    rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt (hρP c), zero_add]

theorem symDim_nat (m g : ℕ) : symDim (m + 1) (g : ℤ) = sd m g := by
  unfold symDim sd
  have h1 : ¬ ((g : ℤ) < 0) := by omega
  rw [if_neg h1]
  first
    | rw [Int.toNat_natCast]
    | rw [Int.toNat_coe_nat]
    | simp only [Int.toNat_ofNat]
  congr 1 <;> omega

private theorem sum_prod_sd_digits_eq_prod_sd (m s : ℕ) (P bTop aTop : Fin s → ℕ) (hP : ∀ i, 0 < P i) :
    ∑ d ∈ (Fintype.piFinset fun i => dset m (P i) (bTop i)) ×ˢ (Fintype.piFinset fun i => dset m (P i) (aTop i)),
      ∏ i, sd m ((bTop i - ∑ c, d.1 i c) / P i) * sd m ((aTop i - ∑ c, d.2 i c) / P i) =
    ∏ i, sd m (bTop i) * sd m (aTop i) := by
  rw [Finset.sum_product]
  simp only [Finset.prod_mul_distrib]
  rw [← Finset.sum_mul_sum]
  congr 1
  · exact (Finset.prod_univ_sum (fun i => dset m (P i) (bTop i))
      (fun i ρ => sd m ((bTop i - ∑ c, ρ c) / P i))).symm.trans
      (Finset.prod_congr rfl fun i _ => digit_sum m (P i) (bTop i) (hP i))
  · exact (Finset.prod_univ_sum (fun i => dset m (P i) (aTop i))
      (fun i ρ => sd m ((aTop i - ∑ c, ρ c) / P i))).symm.trans
      (Finset.prod_congr rfl fun i _ => digit_sum m (P i) (aTop i) (hP i))

theorem segLow_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (h : LowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    SegLowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  unfold SegLowAt
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC j m hm hmc
  classical
  have hp : 0 < X.p := by
    obtain ⟨⟨hY, hkY, -⟩, -⟩ := hH
    have hk : (1 : ℝ) ≤ X.k := by
      unfold Loc.k
      have := (Nat.cast_nonneg X.m : (0 : ℝ) ≤ X.m)
      linarith
    have h3 : 1 ≤ X.k ^ 2 * X.Y ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk) (one_le_pow₀ hY)
    exact Nat.cast_pos.mp (show (0 : ℝ) < X.p by linarith)
  have hP : ∀ i, 0 < (X.seg C0 CE1 CE2 j).P X.p i := fun i => by
    unfold SegData.P
    exact pow_pos hp _
  have hdig : ∀ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock d.1 d.2) := by
    intro d hd
    rw [Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset] at hd
    obtain ⟨h1, h2⟩ := hd
    simp only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at h1 h2
    exact ⟨fun i c => ⟨(h1 i).1 c, (h2 i).1 c⟩, fun i => (h1 i).2, fun i => (h2 i).2⟩
  have hmm : ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ, mmB C0 CE1 CE2 X j rz ry =
      symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) *
        (∏ i, sd X.m (((X.seg C0 CE1 CE2 j).bTop i - ∑ c, rz i c) / (X.seg C0 CE1 CE2 j).P X.p i) *
          sd X.m (((segATop X.TT X.aT j) i - ∑ c, ry i c) / (X.seg C0 CE1 CE2 j).P X.p i)) * sd X.m (X.seg C0 CE1 CE2 j).bPlus := by
    intro rz ry
    simp only [mmB, dimMM, coarseA, coarseC, digitBlock, symDim_nat]
  have hsum : ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), mmB C0 CE1 CE2 X j d.1 d.2 =
      symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) *
        (∏ i, sd X.m (X.bT (segPos X.TT j i)) * sd X.m (X.aT (segPos X.TT j i))) *
          sd X.m (X.bT (segNext X.TT j)) := by
    rw [Finset.sum_congr rfl (fun d _ => hmm d.1 d.2), ← Finset.sum_mul, ← Finset.mul_sum,
      sum_prod_sd_digits_eq_prod_sd X.m (segS X.TT j) (fun i => (X.seg C0 CE1 CE2 j).P X.p i) (X.seg C0 CE1 CE2 j).bTop (segATop X.TT X.aT j) hP]
    rfl
  have hcls : ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), rankOnDigits O C0 CE1 CE2 X j m d.1 d.2 ≤
      segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m := by
    have hfin := kf_kept_finite X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j)
    exact finsum_classes (fun b => Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) hfin
      (fun b => blockRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b)
      (fun b : SegBlock (segS X.TT j) X.m => (b.rz, b.ry)) ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i)))
      (fun d b => if Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b ∧ b.rz = d.1 ∧ b.ry = d.2 then
        blockRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b else 0)
      (fun b => if Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b then
        blockRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b else 0)
      (fun d b hK hk => by subst hk; exact if_pos ⟨hK, rfl, rfl⟩)
      (fun d b hn => if_neg fun ⟨hK, h1, h2⟩ => hn ⟨hK, Prod.ext h1 h2⟩)
      (fun b hK => if_pos hK) (fun b hK => if_neg hK)
  rw [← hsum, Nat.cast_sum, Finset.mul_sum]
  calc ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), lowFac C0 CE1 CE2 X j ⌈m⌉₊ * (mmB C0 CE1 CE2 X j d.1 d.2 : ℝ)
      ≤ ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), (rankOnDigits O C0 CE1 CE2 X j m d.1 d.2 : ℝ) :=
        Finset.sum_le_sum fun d hd => h X W Qq O Kf ι σ jO w hS hH hC j m hm hmc d.1 d.2 (hdig d hd)
    _ = ((∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), rankOnDigits O C0 CE1 CE2 X j m d.1 d.2 : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m : ℝ) := Nat.cast_le.mpr hcls

theorem restSegLow_of (h : RestLow) : RestSegLow := by
  unfold RestSegLow
  unfold RestLow at h
  exact TransportedAlt.mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc hh => segLow_of hh) h

end Formalism.MainNotions.ColumnSystems.Pf
end
end

