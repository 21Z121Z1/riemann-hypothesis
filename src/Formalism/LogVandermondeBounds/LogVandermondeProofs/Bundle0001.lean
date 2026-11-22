import Formalism.LogVandermondeBounds.Bundle0001

-- bundled from Formalism.LogVandermondeBounds.LogVandermondeProofs.BlockDimensionIdentities
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

lemma two_mul_card_lt_pairs (n : ℕ) :
    2 * ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card = n * (n - 1) := by
  have h : ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card = ∑ j ∈ range n, j := by
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.card_filter]
    have e : (range n).filter (fun i => i < j) = range j := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; omega
    simp [e]
  rw [h, mul_comm, Finset.sum_range_id_mul_two]

private lemma card_ordered_pairs_in_shifted_interval (a n N : ℕ) (h : a + n ≤ N) :
    ((range N ×ˢ range N).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ a ≤ p.1 ∧ p.2 < a + n)).card =
      ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
  refine Finset.card_nbij' (fun p => (p.1 - a, p.2 - a)) (fun p => (p.1 + a, p.2 + a)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range] at hp
    ext <;> simp <;> omega
  · intro p hp
    ext <;> simp

theorem blockDimensionIdentities : BlockDimensionIdentities := by
  intro k m rS r hm hme hrS hr blockOf dimN
  have hm2 : m = 2 * rS + 2 := by obtain ⟨t, ht⟩ := hme; omega
  have hsame : ∀ i j, i < j → j < r → (blockOf i = blockOf j ↔ rS ≤ i ∧ j < rS + (k + 1)) := by
    intro i j hij hj
    simp only [blockOf]
    split_ifs <;> omega
  have hA := two_mul_card_lt_pairs r
  have hB := card_ordered_pairs_in_shifted_interval rS (k + 1) r (by omega)
  have hC := two_mul_card_lt_pairs (k + 1)
  simp only [Nat.add_sub_cancel] at hC
  have hsplit : (((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2)).filter
      (fun p : ℕ × ℕ => blockOf p.1 = blockOf p.2)).card +
      (((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2)).filter
      (fun p : ℕ × ℕ => ¬ blockOf p.1 = blockOf p.2)).card =
      ((range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
    first
      | exact Finset.filter_card_add_filter_neg_card_eq_card _
      | exact Finset.card_filter_add_card_filter_not _
      | exact Finset.card_filter_add_card_filter_neg _
      | (rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _),
          Finset.filter_union_filter_neg_eq])
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have e1 : (range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ blockOf p.1 = blockOf p.2) =
      (range r ×ˢ range r).filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ rS ≤ p.1 ∧ p.2 < rS + (k + 1)) := by
    apply Finset.filter_congr
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hsame _ _ h1 hp.2).1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hsame _ _ h1 hp.2).2 h2⟩
  have e2 : dimN = ((range r ×ˢ range r).filter
      (fun p : ℕ × ℕ => p.1 < p.2 ∧ ¬ blockOf p.1 = blockOf p.2)).card := rfl
  rw [e1, hB, ← e2] at hsplit
  have hdim : 2 * dimN + (k + 1) * k = r * (r - 1) := by omega
  have hdZ : 2 * (dimN : ℤ) = (r : ℤ) * ((r : ℤ) - 1) - ((k : ℤ) + 1) * k := by
    have := congrArg (Nat.cast : ℕ → ℤ) hdim
    push_cast [Nat.cast_sub (show 1 ≤ r by omega)] at this
    linarith
  have hrZ : (r : ℤ) = k + 1 + 2 * rS := by exact_mod_cast hr
  have hmZ : (m : ℤ) = 2 * rS + 2 := by exact_mod_cast hm2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hrZ, hmZ]; ring
  · linear_combination hdZ - hrZ
  · linear_combination -hdZ + hrZ
  · ring
  · rw [hrZ, hmZ]; ring

theorem prodFactorialShift : ProdFactorialShift := by
  intro k r hkr
  induction r, hkr using Nat.le_induction with
  | base => simp
  | succ r hkr ih =>
    rw [Finset.prod_Ico_succ_top (by omega : k + 1 ≤ r + 1), Finset.prod_range_succ, ← ih]
    simp only [Nat.add_sub_cancel]
    ring

lemma castAdd_lt_castAdd_iff' {a m : ℕ} (i j : Fin a) :
    Fin.castAdd m i < Fin.castAdd m j ↔ i < j := by
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd]

lemma castAdd_lt_natAdd' {a m : ℕ} (i : Fin a) (j : Fin m) :
    Fin.castAdd m i < Fin.natAdd a j := by
  have := i.2
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd]
  omega

lemma not_natAdd_lt_castAdd' {a m : ℕ} (i : Fin m) (j : Fin a) :
    ¬ Fin.natAdd a i < Fin.castAdd m j := by
  have := j.2
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd]
  omega

lemma natAdd_lt_natAdd_iff' {a m : ℕ} (i j : Fin m) :
    Fin.natAdd a i < Fin.natAdd a j ↔ i < j := by
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_natAdd]
  omega

theorem vandermondeAppendNeg : VandermondeAppendNeg := by
  intro R _ a m v b
  simp only [Finset.prod_filter]
  rw [Fin.prod_univ_add]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, castAdd_lt_castAdd_iff',
    castAdd_lt_natAdd', not_natAdd_lt_castAdd', natAdd_lt_natAdd_iff', if_true, if_false,
    Finset.prod_const_one, mul_one, one_mul, sub_neg_eq_add, neg_sub_neg, neg_add_eq_sub, Finset.prod_mul_distrib]
  ring

theorem eulerProductBounds : EulerProductBounds := by
  intro q hq n
  set x := q⁻¹ with hx
  have hx0 : 0 < x := inv_pos.mpr (by linarith)
  have hxq : x * q = 1 := inv_mul_cancel₀ (by linarith)
  have hx3 : x ≤ 1 / 3 := by nlinarith
  have hx1 : x ≤ 1 := by linarith
  have key : ∀ n : ℕ, 1 - 2 * x + x ^ (n + 1) ≤ (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) := by
    intro n
    induction n with
    | zero => simp; linarith
    | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc]
      set y := x ^ (n + 1) with hy
      have hy0 : 0 ≤ y := pow_nonneg hx0.le _
      have hyx : y ≤ x := pow_le_of_le_one hx0.le hx1 (by omega)
      have hc : 0 ≤ 1 - y := by have : y ≤ 1 := pow_le_one₀ hx0.le hx1; linarith
      have h1 := mul_le_mul_of_nonneg_right ih hc
      have h2 : y * y ≤ y * x := mul_le_mul_of_nonneg_left hyx hy0
      have e : x ^ (n + 1 + 1) = y * x := by rw [hy, pow_succ]
      rw [e]
      nlinarith
  have hfac : ∀ i ∈ range n, 0 ≤ 1 - x ^ (i + 1) ∧ 1 - x ^ (i + 1) ≤ 1 := by
    intro i _
    exact ⟨by have : x ^ (i + 1) ≤ 1 := pow_le_one₀ hx0.le hx1; linarith,
      by have : 0 ≤ x ^ (i + 1) := pow_nonneg hx0.le _; linarith⟩
  refine ⟨?_, Finset.prod_le_one (fun i hi => (hfac i hi).1) (fun i hi => (hfac i hi).2)⟩
  by_contra hlt
  push_neg at hlt
  have h1 : (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) < (1 - x) * (1 / 2) :=
    mul_lt_mul_of_pos_left hlt (by linarith)
  have := key n
  have := pow_pos hx0 (n + 1)
  linarith

end Formalism.LogVandermondeBounds.StandardLattice
end

-- bundled from Formalism.LogVandermondeBounds.LogVandermondeProofs.InertPrimeCountBound
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

section Inert

variable {L : Type} [Field L] [Fintype L] [DecidableEq L] {q : ℕ}

lemma q_two_le (hq : Fintype.card L = q ^ 2) : 2 ≤ q := by
  have h := Fintype.one_lt_card (α := L)
  rw [hq] at h
  by_contra h'
  push Not at h'
  interval_cases q <;> simp at h

lemma frob_sub (hq : Fintype.card L = q ^ 2) (a b : L) : (a - b) ^ q = a ^ q - b ^ q := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card L (ringChar L)
  have hd : q ∣ ringChar L ^ (n : ℕ) := by
    rw [← hn, hq]; exact Dvd.intro _ (pow_two q).symm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hd
  subst hk
  have : Fact (ringChar L).Prime := ⟨hp⟩
  exact sub_pow_char_pow a b k

lemma pow_q_sq (hq : Fintype.card L = q ^ 2) (x : L) : x ^ (q ^ 2) = x := by
  rw [← hq]; exact FiniteField.pow_card x

lemma norm_fixed (hq : Fintype.card L = q ^ 2) (x : L) : (x ^ (q + 1)) ^ q = x ^ (q + 1) := by
  rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, pow_q_sq hq, ← pow_succ']

lemma root_bound (d : ℕ) (hd : 0 < d) (c : L) : (univ.filter (fun x : L => x ^ d = c)).card ≤ d := by
  calc _ ≤ (Polynomial.nthRoots d c).toFinset.card := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        simp [Multiset.mem_toFinset, Polynomial.mem_nthRoots hd, hx]
    _ ≤ Multiset.card (Polynomial.nthRoots d c) := Multiset.toFinset_card_le _
    _ ≤ d := Polynomial.card_nthRoots d c

def Sfix (L : Type) [Field L] [Fintype L] [DecidableEq L] (q : ℕ) : Finset L :=
  univ.filter (fun c : L => c ≠ 0 ∧ c ^ q = c)

def fib (q : ℕ) (d : L) : Finset L := (univ.erase 0).filter (fun u : L => u ^ (q + 1) = d)

lemma norm_maps (hq : Fintype.card L = q ^ 2) :
    ((univ.erase (0 : L) : Finset L) : Set L).MapsTo (fun u => u ^ (q + 1)) (Sfix L q) := by
  intro u hu
  simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hu
  simp only [Sfix, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
  exact ⟨pow_ne_zero _ hu, norm_fixed hq u⟩

lemma pigeon (hq : Fintype.card L = q ^ 2) :
    (Sfix L q).card = q - 1 ∧ ∀ d ∈ Sfix L q, (fib q d).card = q + 1 := by
  have h2 := q_two_le hq
  have htot := card_eq_sum_card_fiberwise (norm_maps hq)
  rw [card_erase_of_mem (mem_univ _), card_univ, hq] at htot
  have hfib : ∀ d ∈ Sfix L q, (fib q d).card ≤ q + 1 := by
    intro d _
    calc (fib q d).card ≤ (univ.filter (fun x : L => x ^ (q + 1) = d)).card := by
          apply card_le_card
          intro x
          simp only [fib, mem_filter, mem_erase, mem_univ, and_true, true_and]
          exact fun h => h.2
      _ ≤ q + 1 := root_bound _ (by omega) d
  have hS : (Sfix L q).card ≤ q - 1 := by
    calc _ ≤ (univ.filter (fun x : L => x ^ (q - 1) = 1)).card := by
          apply card_le_card
          intro c hc
          simp only [Sfix, mem_filter, mem_univ, true_and] at hc ⊢
          obtain ⟨h0, h1⟩ := hc
          have : c ^ (q - 1) * c = 1 * c := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega), h1, one_mul]
          exact mul_right_cancel₀ h0 this
      _ ≤ q - 1 := root_bound _ (by omega) 1
  have hle : ∑ d ∈ Sfix L q, (fib q d).card ≤ ∑ d ∈ Sfix L q, (q + 1) := sum_le_sum hfib
  rw [sum_const, smul_eq_mul] at hle
  have htot' : q ^ 2 - 1 = ∑ d ∈ Sfix L q, (fib q d).card := htot
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have hsq : (r + 2) ^ 2 - 1 = (r + 1) * (r + 3) := by
    have : (r + 2) ^ 2 = (r + 1) * (r + 3) + 1 := by ring
    omega
  have hS' : (Sfix L (r + 2)).card = r + 1 := by
    have h3 : (r + 1) * (r + 3) ≤ (Sfix L (r + 2)).card * (r + 3) := by
      rw [← hsq, htot']; exact hle
    have h4 : (Sfix L (r + 2)).card ≤ r + 1 := by simpa using hS
    have h5 := Nat.le_of_mul_le_mul_right h3 (by omega)
    omega
  refine ⟨by simpa using hS', ?_⟩
  have heq : ∑ d ∈ Sfix L (r + 2), (fib (r + 2) d).card = ∑ d ∈ Sfix L (r + 2), (r + 2 + 1) := by
    rw [← htot', hsq, sum_const, smul_eq_mul, hS']
  exact (sum_eq_sum_iff_of_le hfib).1 heq

def Ncnt (q M : ℕ) (c : L) : ℕ := Fintype.card {x : Fin M → L // ∑ i, x i ^ (q + 1) = c}

def Az (q M : ℕ) : ℤ := (q : ℤ) ^ M * ((q : ℤ) ^ M - (-1) ^ M)

def Zz (q M : ℕ) : ℤ := (q : ℤ) ^ (2 * M) + (-1) ^ M * ((q : ℤ) ^ (M + 1) - (q : ℤ) ^ M)

end Inert

end Formalism.LogVandermondeBounds.StandardLattice
end

-- bundled from Formalism.LogVandermondeBounds.LogVandermondeProofs.InterlacingSeparation
section
namespace Formalism.LogVandermondeBounds.flipTwoThree

open Finset

lemma term_le_B0 {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i : Fin n) : nu i - lam i.succ ≤ B0 lam nu := by
  unfold B0
  exact Finset.single_le_sum (f := fun k => nu k - lam k.succ)
    (fun k _ => by have := (h.2 k).1; linarith) (Finset.mem_univ i)

lemma loss_bound_nonneg {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu) :
    0 ≤ B0 lam nu := by
  unfold B0
  exact Finset.sum_nonneg (fun k _ => by have := (h.2 k).1; linarith)

lemma len_nonneg {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i : Fin n) : 0 ≤ len lam i := by
  unfold len
  have := h.2 i
  linarith [this.1, this.2]

lemma mem_Iset_of {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu' : Fin n → ℤ} {b : ℤ}
    (h' : Interlace lam nu') (hb : B0 lam nu' = b) (i : Fin n) : nu' i ∈ Iset lam b i := by
  have hle := term_le_B0 h' i
  have hi := h'.2 i
  have h1 : nu' i - lam i.succ ≤ min (len lam i) b :=
    le_min (by unfold len; linarith [hi.2]) (by rw [← hb]; exact hle)
  simp only [Iset, Finset.mem_Icc]
  constructor
  · linarith [hi.1]
  · linarith

lemma Iset_disj {n : ℕ} {lam : Fin (n + 1) → ℤ} (ha : Antitone lam) (b : ℤ) (i j : Fin n)
    (hij : i ≠ j) :
    Disjoint ((Iset lam b i).image (fun y => y - (i : ℤ)))
      ((Iset lam b j).image (fun y => y - (j : ℤ))) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_image, Iset, Finset.mem_Icc] at hx hx'
  obtain ⟨y, ⟨hy1, hy2⟩, hy⟩ := hx
  obtain ⟨z, ⟨hz1, hz2⟩, hz⟩ := hx'
  have hmi : min (len lam i) b ≤ lam i.castSucc - lam i.succ := min_le_left _ _
  have hmj : min (len lam j) b ≤ lam j.castSucc - lam j.succ := min_le_left _ _
  rcases lt_or_gt_of_ne hij with h | h
  · have h2 : lam j.castSucc ≤ lam i.succ := ha (Fin.succ_le_castSucc_iff.mpr h)
    have h3 : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast h
    omega
  · have h2 : lam i.castSucc ≤ lam j.succ := ha (Fin.succ_le_castSucc_iff.mpr h)
    have h3 : ((j : ℕ) : ℤ) < ((i : ℕ) : ℤ) := by exact_mod_cast h
    omega

lemma sep_self_ne_zero {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu) :
    sep lam nu nu ≠ 0 := by
  unfold sep
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro y hy
  rw [Finset.mem_erase] at hy
  unfold ev
  rw [Finset.prod_ne_zero_iff]
  intro j _ h0
  by_cases hij : i = j
  · subst hij
    exact hy.1 (by linarith)
  · have hyj : y - (i : ℤ) = nu j - (j : ℤ) := by linarith
    have m1 : y - (i : ℤ) ∈ (Iset lam (B0 lam nu) i).image (fun y => y - (i : ℤ)) :=
      Finset.mem_image_of_mem _ hy.2
    have m2 : y - (i : ℤ) ∈ (Iset lam (B0 lam nu) j).image (fun y => y - (j : ℤ)) := by
      rw [hyj]
      exact Finset.mem_image_of_mem _ (mem_Iset_of h rfl j)
    exact Finset.disjoint_left.mp (Iset_disj h.1 _ i j hij) m1 m2

lemma card_erase_Iset {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i : Fin n) :
    ((Iset lam (B0 lam nu) i).erase (nu i)).card = (min (len lam i) (B0 lam nu)).toNat := by
  rw [Finset.card_erase_of_mem (mem_Iset_of h rfl i)]
  unfold Iset
  rw [Int.card_Icc]
  have h0 : 0 ≤ min (len lam i) (B0 lam nu) := le_min (len_nonneg h i) (loss_bound_nonneg h)
  omega

lemma factor_bound {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i j : Fin n) (y : ℤ) (hy : y ∈ Iset lam (B0 lam nu) i) :
    |nu j - (j : ℤ) - (y - (i : ℤ))| ≤ lam 0 - lam (Fin.last n) + n + 1 := by
  simp only [Iset, Finset.mem_Icc] at hy
  have hmi : min (len lam i) (B0 lam nu) ≤ lam i.castSucc - lam i.succ := min_le_left _ _
  have a1 : lam (Fin.last n) ≤ lam j.succ := h.1 (Fin.le_last _)
  have a2 : lam j.castSucc ≤ lam 0 := h.1 (Fin.zero_le _)
  have a3 : lam (Fin.last n) ≤ lam i.succ := h.1 (Fin.le_last _)
  have a4 : lam i.castSucc ≤ lam 0 := h.1 (Fin.zero_le _)
  have hj := h.2 j
  have il : ((i : ℕ) : ℤ) < n := by exact_mod_cast i.isLt
  have jl : ((j : ℕ) : ℤ) < n := by exact_mod_cast j.isLt
  rw [abs_le]
  constructor <;> omega

lemma sep_self_abs {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu) :
    |sep lam nu nu| ≤ (lam 0 - lam (Fin.last n) + n + 1) ^
      (n * ∑ i, (min (len lam i) (B0 lam nu)).toNat) := by
  set W : ℤ := lam 0 - lam (Fin.last n) + n + 1 with hW
  have inner : ∀ i : Fin n, |∏ y ∈ (Iset lam (B0 lam nu) i).erase (nu i), ev nu (y - (i : ℤ))|
      ≤ W ^ (n * (min (len lam i) (B0 lam nu)).toNat) := by
    intro i
    rw [Finset.abs_prod, ← card_erase_Iset h i, pow_mul, ← Finset.prod_const (W ^ n)]
    refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) ?_
    intro y hy
    have hyI := (Finset.mem_erase.mp hy).2
    unfold ev
    rw [Finset.abs_prod]
    calc ∏ j, |nu j - (j : ℤ) - (y - (i : ℤ))| ≤ ∏ _j : Fin n, W :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => factor_bound h i j y hyI)
      _ = W ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold sep
  rw [Finset.abs_prod, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => inner i)

lemma sep_other_zero {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu nu' : Fin n → ℤ}
    (h' : Interlace lam nu') (hb : B0 lam nu' = B0 lam nu) (hne : nu' ≠ nu) :
    sep lam nu nu' = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  unfold sep
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (i := nu' i) (Finset.mem_erase.mpr ⟨hi, mem_Iset_of h' hb i⟩)
  unfold ev
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  ring

theorem interlacing_separation : InterlacingSeparation := by
  intro n lam nu h
  exact ⟨fun nu' h' hb i => mem_Iset_of h' hb i,
    fun i j hij => Iset_disj h.1 _ i j hij,
    sep_self_ne_zero h,
    sep_self_abs h,
    fun nu' h' hb hne => sep_other_zero h' hb hne⟩

end Formalism.LogVandermondeBounds.flipTwoThree
end

-- bundled from Formalism.LogVandermondeBounds.LogVandermondeProofs.PrimePowerSubgroupTrivial
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Polynomial

theorem primeOrderFinrank : PrimeOrderFinrank := by
  intro K _ _ n g A hg hA hA1
  haveI := Fact.mk hg
  let f : (Fin n → K) →ₗ[ℚ] (Fin n → K) := (Matrix.toLin' A).restrictScalars ℚ
  have hpow : ∀ v : Fin n → K, (f ^ g) v = v := by
    intro v
    rw [Module.End.pow_apply]
    show (⇑(Matrix.toLin' A))^[g] v = v
    rw [← Module.End.pow_apply, ← Matrix.toLin'_pow, hA, Matrix.toLin'_one, LinearMap.id_apply]
  have hfg : f ^ g = 1 := LinearMap.ext hpow
  have hint : IsIntegral ℚ f := IsIntegral.of_finite ℚ f
  have hm0 : minpoly ℚ f ≠ 0 := minpoly.ne_zero hint
  have hdvd : minpoly ℚ f ∣ Polynomial.cyclotomic g ℚ * (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hfg]
  have hirr := Polynomial.cyclotomic.irreducible_rat hg.pos
  have hdeg : (Polynomial.cyclotomic g ℚ).natDegree = g - 1 := by
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hg]
  have hle : (minpoly ℚ f).natDegree ≤ Module.finrank ℚ K * n := by
    have h1 := Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f) (LinearMap.charpoly_monic f).ne_zero
    rw [LinearMap.charpoly_natDegree] at h1
    have h2 : Module.finrank ℚ (Fin n → K) = Module.finrank ℚ K * n := by
      rw [Module.finrank_pi_fintype]
      simp [mul_comm]
    omega
  by_cases hc : Polynomial.cyclotomic g ℚ ∣ minpoly ℚ f
  · have := Polynomial.natDegree_le_of_dvd hc hm0
    omega
  · exfalso
    apply hA1
    have hcop : IsCoprime (minpoly ℚ f) (Polynomial.cyclotomic g ℚ) :=
      ((hirr.coprime_iff_not_dvd).2 hc).symm
    have h1 : minpoly ℚ f ∣ Polynomial.X - 1 := by
      first
        | exact hcop.dvd_of_dvd_mul_left hdvd
        | exact hcop.dvd_of_dvd_mul_right hdvd
        | exact hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at hdvd)
        | exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hdvd)
    have h2 : Polynomial.aeval f (Polynomial.X - 1 : Polynomial ℚ) = 0 := by
      obtain ⟨q, hq⟩ := h1
      rw [hq, map_mul, minpoly.aeval, zero_mul]
    have hf1 : f = 1 := by
      simpa [sub_eq_zero] using h2
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun hf1 v
    simpa [f] using this

theorem primePowerSubgroupTrivial : PrimePowerSubgroupTrivial := by
  intro K _ _ n g Γ hg hfin hcard hlt
  obtain ⟨e, he⟩ := hcard
  rw [Subgroup.eq_bot_iff_forall]
  intro γ hγ
  by_contra hne
  set x : Γ := ⟨γ, hγ⟩ with hxdef
  have hx : x ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have hdvd : orderOf x ∣ g ^ e := by
    rw [← he]
    exact orderOf_dvd_natCard x
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hg).1 hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hx (orderOf_eq_one_iff.1 (by simpa using hm))
  set y := x ^ (g ^ (m - 1)) with hy
  have hyg : y ^ g = 1 := by
    rw [hy, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm0), ← hm,
      pow_orderOf_eq_one]
  have hy1 : y ≠ 1 := by
    intro h
    have h3 := orderOf_dvd_of_pow_eq_one (show x ^ (g ^ (m - 1)) = 1 from h)
    rw [hm] at h3
    have := (Nat.pow_dvd_pow_iff_le_right hg.one_lt).1 h3
    omega
  have key := primeOrderFinrank K n g ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) hg
    (by rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hyg]; rfl)
    (fun h => hy1 (Subtype.ext (Units.ext (by simpa using h))))
  omega

end Formalism.LogVandermondeBounds.StandardLattice
end

