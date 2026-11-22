import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeCoeffAdjacentSwapOfLeviReduction
section
noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.Swap

def ex (n m : ℕ) (a : Fin m → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < m then a ⟨i.val, h⟩
  else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then -(a ⟨n - 1 - i.val, h'.2⟩) else 0

theorem tMat_eq {L : Type} [Field L] (ϖ : L) (n m : ℕ) (a : Fin m → ℤ) :
    tMat ϖ n m a = Matrix.diagonal fun i => ϖ ^ ex n m a i := by
  unfold tMat ex
  congr 1
  funext i
  split_ifs <;> simp

theorem ex_low {n m : ℕ} (a : Fin m → ℤ) (c : Fin n) (k : Fin m) (h : c.val = k.val) : ex n m a c = a k := by
  unfold ex
  rw [dif_pos (h ▸ k.2)]
  exact congrArg a (Fin.ext h)

theorem ex_high {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (c : Fin n) (k : Fin m) (h : c.val + k.val + 1 = n) :
    ex n m a c = -a k := by
  have := k.2
  unfold ex
  rw [dif_neg (by omega), dif_pos (by omega)]
  exact congrArg (fun x => -a x) (Fin.ext (by simp only; omega))

theorem ex_mid {n m : ℕ} (a : Fin m → ℤ) (c : Fin n) (h : m ≤ c.val) (h' : c.val + m < n) :
    ex n m a c = 0 := by
  unfold ex
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem ex_rev {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (c : Fin n) : ex n m a c.rev = -ex n m a c := by
  have h1 := c.2
  have h2 := Fin.val_rev c
  by_cases h : c.val < m
  · rw [ex_low a c ⟨c.val, h⟩ rfl, ex_high hm a c.rev ⟨c.val, h⟩ (by simp only; omega)]
  · by_cases h' : c.val + m < n
    · rw [ex_mid a c (by omega) h', ex_mid a c.rev (by omega) (by omega), neg_zero]
    · rw [ex_high hm a c ⟨c.rev.val, by omega⟩ (by simp only; omega), ex_low a c.rev ⟨c.rev.val, by omega⟩ rfl,
        neg_neg]

def emb (n i : ℕ) (h : 2 * i + 4 ≤ n) : Fin 4 → Fin n :=
  ![⟨i, by omega⟩, ⟨i + 1, by omega⟩, ⟨n - 2 - i, by omega⟩, ⟨n - 1 - i, by omega⟩]

def blk (n i : ℕ) (a : Fin n) : ℕ :=
  if a.val = i + 1 then i else if a.val = n - 1 - i then n - 2 - i else a.val

theorem blk_eq_iff {n i : ℕ} (h : 2 * i + 4 ≤ n) (a b : Fin n) :
    blk n i a = blk n i b ↔ a.val = b.val ∨ (a.val = i ∧ b.val = i + 1) ∨ (a.val = i + 1 ∧ b.val = i) ∨
      (a.val + i + 2 = n ∧ b.val + i + 1 = n) ∨ (a.val + i + 1 = n ∧ b.val + i + 2 = n) := by
  unfold blk
  split_ifs <;> omega

theorem mem_range_emb {n i : ℕ} (h : 2 * i + 4 ≤ n) (a : Fin n) :
    a ∈ Set.range (emb n i h) ↔ a.val = i ∨ a.val = i + 1 ∨ a.val = n - 2 - i ∨ a.val = n - 1 - i := by
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp [emb]
  · rintro (h1 | h1 | h1 | h1)
    exacts [⟨0, Fin.ext h1.symm⟩, ⟨1, Fin.ext h1.symm⟩, ⟨2, Fin.ext h1.symm⟩, ⟨3, Fin.ext h1.symm⟩]

theorem isBlockDatum_emb {n i : ℕ} (h : 2 * i + 4 ≤ n) : IsBlockDatum (emb n i h) (blk n i) ![0, 0, 1, 1] := by
  have v0 : (emb n i h 0).val = i := rfl
  have v1 : (emb n i h 1).val = i + 1 := rfl
  have v2 : (emb n i h 2).val = n - 2 - i := rfl
  have v3 : (emb n i h 3).val = n - 1 - i := rfl
  have b0 : blk n i (emb n i h 0) = i := by unfold blk; rw [v0]; split_ifs <;> omega
  have b1 : blk n i (emb n i h 1) = i := by unfold blk; rw [v1]; split_ifs <;> omega
  have b2 : blk n i (emb n i h 2) = n - 2 - i := by unfold blk; rw [v2]; split_ifs <;> omega
  have b3 : blk n i (emb n i h 3) = n - 2 - i := by unfold blk; rw [v3]; split_ifs <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro k
    fin_cases k
    · show i < i + 1
      omega
    · show i + 1 < n - 2 - i
      omega
    · show n - 2 - i < n - 1 - i
      omega
  · intro k
    apply Fin.ext
    rw [Fin.val_rev]
    fin_cases k
    · show n - 1 - i = n - (i + 1)
      omega
    · show n - 2 - i = n - (i + 1 + 1)
      omega
    · show i + 1 = n - (n - 2 - i + 1)
      omega
    · show i = n - (n - 1 - i + 1)
      omega
  · intro a b hab
    have : a.val ≤ b.val := hab
    unfold blk
    split_ifs <;> omega
  · intro a b
    have := a.2
    have := b.2
    rw [blk_eq_iff h, blk_eq_iff h, Fin.val_rev, Fin.val_rev]
    clear v0 v1 v2 v3 b0 b1 b2 b3
    rintro (h1 | h1 | h1 | h1 | h1) <;> omega
  · intro a b
    rw [mem_range_emb, mem_range_emb, Fin.ext_iff, blk_eq_iff h]
    rintro (h1 | h1 | h1 | h1 | h1)
    · exact Or.inl h1
    all_goals exact Or.inr ⟨by omega, by omega⟩
  · have hne : i ≠ n - 2 - i := by omega
    simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
    simp [b0, b1, b2, b3, hne, hne.symm, show (Fin.succ 2 : Fin 4) = 3 from rfl]

theorem coeffSwap (H : LeviStep) (HI : IndexFour) (HC : CartanFour) : CoeffSwap := by
  intro L _ _ _ ϖ σ q n m hU hm hn h hh a i j hij t t' ht ht'
  have hj := j.2
  have h4 : 2 * i.val + 4 ≤ n := by omega
  have hq : q ≠ 0 := by
    have := hU.2.2.2.2.2.1
    omega
  have key : ∀ (c : Fin m → ℤ) (k : Fin 4),
      ex n m c (emb n i h4 k) = (![c i, c j, -c j, -c i] : Fin 4 → ℤ) k := by
    intro c k
    fin_cases k
    · exact ex_low c _ i rfl
    · exact ex_low c _ j hij.symm
    · exact ex_high hm c _ j (by show n - 2 - i.val + j.val + 1 = n; omega)
    · exact ex_high hm c _ i (by show n - 1 - i.val + i.val + 1 = n; omega)
  have key' : ∀ k : Fin 4, ex n m (a ∘ Equiv.swap i j) (emb n i h4 k) =
      (![a j, a i, -a i, -a j] : Fin 4 → ℤ) k := by
    intro k
    rw [key]
    simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have main := H L ϖ σ q n 4 (emb n i h4) (blk n i) ![0, 0, 1, 1] ![1, 0, 0, -1] (ex n m a)
    (ex n m (a ∘ Equiv.swap i j)) (q ^ 2) (a j - a i) t t' h hU (isBlockDatum_emb h4)
    (by decide) (by decide) (ex_rev hm _) (ex_rev hm _) ?_ ?_ (ht.trans (tMat_eq _ _ _ _))
    (ht'.trans (tMat_eq _ _ _ _)) (pow_ne_zero _ hq) (HI L ϖ σ q hU) ?_ hh
  · rw [main, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    congr 2
    push_cast
    ring
  · intro c hc
    rw [mem_range_emb] at hc
    have := c.2
    unfold ex
    split_ifs with h1 h2
    · rw [Function.comp, Equiv.swap_apply_of_ne_of_ne] <;> rw [Ne, Fin.ext_iff] <;> simp only <;> omega
    · rw [Function.comp, Equiv.swap_apply_of_ne_of_ne] <;> rw [Ne, Fin.ext_iff] <;> simp only <;> omega
    · rfl
  · intro k l
    rw [key', key']
    fin_cases k <;> fin_cases l <;> simp <;> ring
  · intro s s' hs hs'
    simp only [key a] at hs
    simp only [key'] at hs'
    exact HC L ϖ σ q hU (a i) (a j) s s' hs hs'

end GlobalTheory.SatakeWeyl.Swap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeCoeffLastSignChangeOfLeviReduction
section
noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.Neg

def ext {m : ℕ} (a : Fin m → ℤ) (x : ℕ) : ℤ := if h : x < m then a ⟨x, h⟩ else 0

def expo (n m : ℕ) (A : ℕ → ℤ) (x : Fin n) : ℤ :=
  if x.val < m then A x else if n - m ≤ x.val then -A (n - 1 - x.val) else 0

theorem tMat_eq {L : Type} [Field L] (ϖ : L) {n m : ℕ} (a : Fin m → ℤ) :
    tMat ϖ n m a = Matrix.diagonal fun x => ϖ ^ expo n m (ext a) x := by
  unfold tMat
  congr 1
  funext x
  have hx := x.2
  unfold expo ext
  by_cases h1 : x.val < m
  · simp [h1]
  · by_cases h2 : n - m ≤ x.val
    · have h3 : n - 1 - x.val < m := by omega
      simp [h1, h2, h3]
    · simp [h1, h2]

theorem ext_update {m : ℕ} (a : Fin m → ℤ) (i : Fin m) (c : ℤ) (x : ℕ) :
    ext (Function.update a i c) x = if x = i.val then c else ext a x := by
  unfold ext
  by_cases h : x = i.val
  · subst h
    simp
  · by_cases h1 : x < m
    · have : (⟨x, h1⟩ : Fin m) ≠ i := fun e => h (congrArg Fin.val e)
      simp [h, h1, Function.update_of_ne this]
    · simp [h, h1]

theorem expo_rev {n m : ℕ} (h : 2 * m ≤ n) (A : ℕ → ℤ) (x : Fin n) :
    expo n m A x.rev = -expo n m A x := by
  have hx := x.2
  have hr : (x.rev : ℕ) = n - 1 - x := by rw [Fin.val_rev]; omega
  unfold expo
  rw [hr]
  have e : n - 1 - (n - 1 - x.val) = x.val := by omega
  rw [e]
  split_ifs <;> first | omega | simp

def mid {n : ℕ} (k r : ℕ) (h : n = 2 * k + r) (j : Fin r) : Fin n := ⟨k + j.val, by have := j.2; omega⟩

theorem mem_range_mid {n k r : ℕ} (h : n = 2 * k + r) (x : Fin n) :
    x ∈ Set.range (mid k r h) ↔ k ≤ x.val ∧ x.val < k + r := by
  constructor
  · rintro ⟨j, rfl⟩
    have := j.2
    simp only [mid]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x.val - k, by omega⟩, Fin.ext (by simp only [mid]; omega)⟩

theorem blockDatum {n k r : ℕ} (h : n = 2 * k + r) (γ : Fin r → ℕ) (hγ : ∀ j, γ j = 0) :
    IsBlockDatum (mid k r h) (fun x => if k ≤ x.val ∧ x.val < k + r then k else x.val) γ := by
  refine ⟨fun i j hij => ?_, fun i => ?_, fun x y hxy => ?_, fun x y hxy => ?_, fun x y hxy => ?_, fun i j => ?_⟩
  · have : i.val < j.val := hij
    show k + i.val < k + j.val
    omega
  · have := i.2
    apply Fin.ext
    simp only [mid, Fin.val_rev]
    omega
  · have : x.val ≤ y.val := hxy
    simp only
    split_ifs <;> omega
  · have := x.2
    have := y.2
    simp only [Fin.val_rev] at hxy ⊢
    split_ifs at hxy ⊢ <;> omega
  · rw [mem_range_mid, mem_range_mid, Fin.ext_iff]
    simp only at hxy
    split_ifs at hxy <;> omega
  · have := i.2
    have := j.2
    simp only [mid, hγ]
    split_ifs <;> first | omega | simp

theorem step (H : LeviStep) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q n m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1)
    {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) (a : Fin m → ℤ) (i : Fin m) (hi : i.val + 1 = m)
    {t t' : GU σ n} (ht : mat t = tMat ϖ n m a) (ht' : mat t' = tMat ϖ n m (Function.update a i (-a i)))
    (r : ℕ) (hn : n = 2 * i.val + r) (γ : Fin r → ℕ) (hγ : ∀ j, γ j = 0) (b : Fin r → ℤ)
    (hb : ∀ j, b j = if j.val = 0 then 1 else if j.val + 1 = r then -1 else 0) (Q : ℕ) (hQ : Q ≠ 0)
    (hI : ∀ s₀ : GU σ r, mat s₀ = Matrix.diagonal (fun i => ϖ ^ b i) →
      ((KU σ r ⊓ rootU σ γ).map (MulAut.conj s₀).toMonoidHom).relIndex (KU σ r ⊓ rootU σ γ) = Q) :
    cellSum (KU σ n) (radU σ Fin.val) h t = (Q : ℂ) ^ (a i) * cellSum (KU σ n) (radU σ Fin.val) h t' := by
  have h0 : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact absurd this WithZero.zero_ne_coe
  have key : ∀ (c : Fin m → ℤ) (j : Fin r), expo n m (ext c) (mid i.val r hn j) = c i * b j := by
    intro c j
    have hj := j.2
    have hci : ext c i.val = c i := by simp [ext]
    rw [hb]
    unfold expo
    simp only [mid]
    by_cases h1 : j.val = 0
    · simp [h1, hci]
    · by_cases h2 : j.val + 1 = r
      · have e : n - 1 - (i.val + j.val) = i.val := by omega
        have f1 : ¬ i.val + j.val < m := by omega
        have f2 : n - m ≤ i.val + j.val := by omega
        simp [f1, f2, e, hci, h1, h2]
      · have f1 : ¬ i.val + j.val < m := by omega
        have f2 : ¬ n - m ≤ i.val + j.val := by omega
        rw [if_neg h1, if_neg h2, mul_zero]
        simp only [f1, f2, if_false]
  rw [tMat_eq] at ht ht'
  have := H L ϖ σ q n r (mid i.val r hn) _ γ b _ _ Q (-a i) t t' h hU (blockDatum hn γ hγ) ?_ ?_
    (expo_rev hm _) (expo_rev hm _) ?_ ?_ ht ht' hQ hI ?_ hh
  · rwa [neg_neg] at this
  · intro j
    have := j.2
    rw [hb, hb, Fin.val_rev]
    split_ifs <;> omega
  · intro j l hjl _
    have := l.2
    have : j.val < l.val := hjl
    rw [hb, hb]
    split_ifs <;> omega
  · intro x hx
    have := x.2
    rw [mem_range_mid] at hx
    unfold expo
    rw [ext_update, ext_update]
    split_ifs <;> first | rfl | omega
  · intro j l _
    rw [key, key, Function.update_self]
    ring
  · intro s s' hs hs' g _
    have e : s' = s⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      apply mat_injective
      rw [mat_mul, hs, hs', Matrix.diagonal_mul_diagonal, mat_one, ← Matrix.diagonal_one]
      congr 1
      funext j
      rw [key, key, Function.update_self, ← zpow_add₀ h0]
      simp
    obtain ⟨k₁, hk₁, k₂, hk₂, e'⟩ := inv_mem_dc hU (s * g)
    refine ⟨k₁, hk₁, k₂, ⟨hk₂, fun x y hxy => absurd ((hγ x).trans (hγ y).symm) hxy⟩, ?_⟩
    rw [← e', e, mul_inv_rev]

end GlobalTheory.SatakeWeyl.Neg

theorem GlobalTheory.SatakeWeyl.coeffNeg_of_leviStep : LeviStep → IndexTwo → IndexThree → CoeffNeg := by
  intro H H2 H3 L _ _ _ ϖ σ q n m hU hm hm' h hh a i hi t t' ht ht'
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  rcases (by omega : n = 2 * i.val + 2 ∨ n = 2 * i.val + 3) with hn | hn
  · rw [Neg.step H hU hm hm' hh a i hi ht ht' 2 hn ![0, 0] (by decide) ![1, -1] (by decide) (q ^ 2)
      (pow_ne_zero _ hq) (H2 L ϖ σ q hU)]
    congr 1
    rw [Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    congr 1
    rw [hn]
    push_cast
    ring
  · rw [Neg.step H hU hm hm' hh a i hi ht ht' 3 hn ![0, 0, 0] (by decide) ![1, 0, -1] (by decide) (q ^ 4)
      (pow_ne_zero _ hq) (H3 L ϖ σ q hU)]
    congr 1
    rw [Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    congr 1
    rw [hn]
    push_cast
    ring

end
end

