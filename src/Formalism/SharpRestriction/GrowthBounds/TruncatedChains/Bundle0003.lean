import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.Bundle0001

-- bundled from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CnNOOfNormal
section
namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G

variable {n : ℕ}

def NO (n j : ℕ) (l : List (Fin n × Fin n)) : Prop :=
  l.Nodup ∧ (∀ ab ∈ l, j ≤ ab.1.val ∧ ab.1.val < ab.2.val) ∧
    (∀ a b : Fin n, j ≤ a.val → a.val < b.val → (a, b) ∈ l) ∧
    ∀ a b c : Fin n, j ≤ a.val → a.val < b.val → b.val < c.val →
      (l.idxOf (a, b) < l.idxOf (a, c) ∧ l.idxOf (a, c) < l.idxOf (b, c)) ∨
      (l.idxOf (b, c) < l.idxOf (a, c) ∧ l.idxOf (a, c) < l.idxOf (a, b))

theorem cn_NO_of_normal {ord : List (Fin n × Fin n)} (h : NormalOrder n ord) : NO n 0 ord := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold NO
  exact ⟨h1, fun ab hab => ⟨Nat.zero_le _, h2 ab hab⟩, fun a b _ hab => h3 a b hab,
    fun a b c _ hab hbc => h4 a b c hab hbc⟩

theorem cn_ne {x1 x2 y1 y2 : Fin n} (h : ¬ (x1.val = y1.val ∧ x2.val = y2.val)) : (x1, x2) ≠ (y1, y2) := by
  intro heq
  rw [Prod.mk.injEq] at heq
  exact h ⟨congrArg Fin.val heq.1, congrArg Fin.val heq.2⟩

theorem cn_posR_swap (l1 l2 : List (Fin n × Fin n)) (x1 x2 y1 y2 : Fin n) (hxy : (x1, x2) ≠ (y1, y2))
    (hx : (x1, x2) ∉ l1) (hy : (y1, y2) ∉ l1) (u1 u2 : Fin n) :
    (u1.val = x1.val ∧ u2.val = x2.val ∧ (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) = l1.length ∧
      (l1 ++ (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length + 1) ∨
    (u1.val = y1.val ∧ u2.val = y2.val ∧ (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) = l1.length + 1 ∧
      (l1 ++ (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length) ∨
    (¬ (u1.val = x1.val ∧ u2.val = x2.val) ∧ ¬ (u1.val = y1.val ∧ u2.val = y2.val) ∧
      (l1 ++ (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) ∧
      ((l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) < l1.length ∨
        l1.length + 2 ≤ (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2))) := by
  have hu : ∀ v1 v2 : Fin n, u1.val = v1.val ∧ u2.val = v2.val → (u1, u2) = (v1, v2) :=
    fun v1 v2 hh => Prod.ext (Fin.ext hh.1) (Fin.ext hh.2)
  rcases cn_pos_swap l1 l2 (x1, x2) (y1, y2) hxy hx hy (u1, u2) with
    ⟨e, h2, h3⟩ | ⟨e, h2, h3⟩ | ⟨e1, e2, h3, h4⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inr (Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩)
  · exact Or.inr (Or.inr ⟨fun hh => e1 (hu _ _ hh), fun hh => e2 (hu _ _ hh), h3, h4⟩)

theorem cn_posR_braid (l1 l2 : List (Fin n × Fin n)) (x1 x2 y1 y2 z1 z2 : Fin n) (hxy : (x1, x2) ≠ (y1, y2))
    (hxz : (x1, x2) ≠ (z1, z2)) (hyz : (y1, y2) ≠ (z1, z2))
    (hx : (x1, x2) ∉ l1) (hy : (y1, y2) ∉ l1) (hz : (z1, z2) ∉ l1) (u1 u2 : Fin n) :
    (u1.val = x1.val ∧ u2.val = x2.val ∧
      (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) = l1.length ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length + 2) ∨
    (u1.val = y1.val ∧ u2.val = y2.val ∧
      (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) = l1.length + 1 ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length + 1) ∨
    (u1.val = z1.val ∧ u2.val = z2.val ∧
      (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) = l1.length + 2 ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length) ∨
    (¬ (u1.val = x1.val ∧ u2.val = x2.val) ∧ ¬ (u1.val = y1.val ∧ u2.val = y2.val) ∧
      ¬ (u1.val = z1.val ∧ u2.val = z2.val) ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) =
        (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) ∧
      ((l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) < l1.length ∨
        l1.length + 3 ≤ (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2))) := by
  have hu : ∀ v1 v2 : Fin n, u1.val = v1.val ∧ u2.val = v2.val → (u1, u2) = (v1, v2) :=
    fun v1 v2 hh => Prod.ext (Fin.ext hh.1) (Fin.ext hh.2)
  rcases cn_pos_braid l1 l2 (x1, x2) (y1, y2) (z1, z2) hxy hxz hyz hx hy hz (u1, u2) with
    ⟨e, h2, h3⟩ | ⟨e, h2, h3⟩ | ⟨e, h2, h3⟩ | ⟨e1, e2, e3, h3, h4⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inr (Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩)
  · rw [Prod.mk.injEq] at e
    exact Or.inr (Or.inr (Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨fun hh => e1 (hu _ _ hh), fun hh => e2 (hu _ _ hh),
      fun hh => e3 (hu _ _ hh), h3, h4⟩))

set_option maxHeartbeats 1600000 in
theorem cn_ar_swap {p P Q R P' Q' R' x y z a b c d : ℕ} (hxy : x < y) (hyz : y < z) (h1 : a ≠ c) (h2 : a ≠ d)
    (h3 : b ≠ c) (h4 : b ≠ d) (o : (P < Q ∧ Q < R) ∨ (R < Q ∧ Q < P))
    (p1 : (x = a ∧ y = b ∧ P = p ∧ P' = p + 1) ∨ (x = c ∧ y = d ∧ P = p + 1 ∧ P' = p) ∨
      (¬ (x = a ∧ y = b) ∧ ¬ (x = c ∧ y = d) ∧ P' = P ∧ (P < p ∨ p + 2 ≤ P)))
    (p2 : (x = a ∧ z = b ∧ Q = p ∧ Q' = p + 1) ∨ (x = c ∧ z = d ∧ Q = p + 1 ∧ Q' = p) ∨
      (¬ (x = a ∧ z = b) ∧ ¬ (x = c ∧ z = d) ∧ Q' = Q ∧ (Q < p ∨ p + 2 ≤ Q)))
    (p3 : (y = a ∧ z = b ∧ R = p ∧ R' = p + 1) ∨ (y = c ∧ z = d ∧ R = p + 1 ∧ R' = p) ∨
      (¬ (y = a ∧ z = b) ∧ ¬ (y = c ∧ z = d) ∧ R' = R ∧ (R < p ∨ p + 2 ≤ R))) :
    (P' < Q' ∧ Q' < R') ∨ (R' < Q' ∧ Q' < P') := by
  rcases p1 with h1' | h1' | h1' <;> rcases p2 with h2' | h2' | h2' <;>
    rcases p3 with h3' | h3' | h3' <;> rcases o with o | o <;> omega

set_option maxHeartbeats 3200000 in
theorem cn_ar_braid' {p P Q R P' Q' R' x y z a b c : ℕ} (hxy : x < y) (hyz : y < z) (hab : a < b) (hbc : b < c)
    (o : (P < Q ∧ Q < R) ∨ (R < Q ∧ Q < P))
    (p1 : (x = b ∧ y = c ∧ P = p ∧ P' = p + 2) ∨ (x = a ∧ y = c ∧ P = p + 1 ∧ P' = p + 1) ∨
      (x = a ∧ y = b ∧ P = p + 2 ∧ P' = p) ∨
      (¬ (x = b ∧ y = c) ∧ ¬ (x = a ∧ y = c) ∧ ¬ (x = a ∧ y = b) ∧ P' = P ∧ (P < p ∨ p + 3 ≤ P)))
    (p2 : (x = b ∧ z = c ∧ Q = p ∧ Q' = p + 2) ∨ (x = a ∧ z = c ∧ Q = p + 1 ∧ Q' = p + 1) ∨
      (x = a ∧ z = b ∧ Q = p + 2 ∧ Q' = p) ∨
      (¬ (x = b ∧ z = c) ∧ ¬ (x = a ∧ z = c) ∧ ¬ (x = a ∧ z = b) ∧ Q' = Q ∧ (Q < p ∨ p + 3 ≤ Q)))
    (p3 : (y = b ∧ z = c ∧ R = p ∧ R' = p + 2) ∨ (y = a ∧ z = c ∧ R = p + 1 ∧ R' = p + 1) ∨
      (y = a ∧ z = b ∧ R = p + 2 ∧ R' = p) ∨
      (¬ (y = b ∧ z = c) ∧ ¬ (y = a ∧ z = c) ∧ ¬ (y = a ∧ z = b) ∧ R' = R ∧ (R < p ∨ p + 3 ≤ R))) :
    (P' < Q' ∧ Q' < R') ∨ (R' < Q' ∧ Q' < P') := by
  rcases p1 with h1' | h1' | h1' | h1' <;> rcases p2 with h2' | h2' | h2' | h2' <;>
    rcases p3 with h3' | h3' | h3' | h3' <;> rcases o with o | o <;> omega

theorem cn_NO_swap {j : ℕ} (l1 l2 : List (Fin n × Fin n)) (a b c d : Fin n) (h1 : a ≠ c) (h2 : a ≠ d)
    (h3 : b ≠ c) (h4 : b ≠ d) (h : NO n j (l1 ++ (a, b) :: (c, d) :: l2)) :
    NO n j (l1 ++ (c, d) :: (a, b) :: l2) := by
  unfold NO at h ⊢
  obtain ⟨hnd, hb, hc, ht⟩ := h
  have hperm : (l1 ++ (c, d) :: (a, b) :: l2).Perm (l1 ++ (a, b) :: (c, d) :: l2) :=
    (List.Perm.swap (a, b) (c, d) l2).append_left l1
  have hne : (a, b) ≠ (c, d) := fun e => h1 (congrArg Prod.fst e)
  have hx : (a, b) ∉ l1 := cn_notMem hnd (by simp)
  have hy : (c, d) ∉ l1 := cn_notMem hnd (by simp)
  have v1 : a.val ≠ c.val := fun e => h1 (Fin.ext e)
  have v2 : a.val ≠ d.val := fun e => h2 (Fin.ext e)
  have v3 : b.val ≠ c.val := fun e => h3 (Fin.ext e)
  have v4 : b.val ≠ d.val := fun e => h4 (Fin.ext e)
  refine ⟨hperm.nodup_iff.2 hnd, fun ab hab => hb ab (hperm.mem_iff.1 hab),
    fun x y hj hxy => hperm.mem_iff.2 (hc x y hj hxy), ?_⟩
  intro x y z hj hxy hyz
  exact cn_ar_swap hxy hyz v1 v2 v3 v4 (ht x y z hj hxy hyz)
    (cn_posR_swap l1 l2 a b c d hne hx hy x y) (cn_posR_swap l1 l2 a b c d hne hx hy x z)
    (cn_posR_swap l1 l2 a b c d hne hx hy y z)

theorem cn_NO_braid' {j : ℕ} (l1 l2 : List (Fin n × Fin n)) (a b c : Fin n) (hab : a < b) (hbc : b < c)
    (h : NO n j (l1 ++ (b, c) :: (a, c) :: (a, b) :: l2)) :
    NO n j (l1 ++ (a, b) :: (a, c) :: (b, c) :: l2) := by
  unfold NO at h ⊢
  obtain ⟨hnd, hb, hc, ht⟩ := h
  have hperm : (l1 ++ (a, b) :: (a, c) :: (b, c) :: l2).Perm (l1 ++ (b, c) :: (a, c) :: (a, b) :: l2) :=
    ((((List.Perm.swap (a, c) (a, b) ((b, c) :: l2)).trans
      ((List.Perm.swap (b, c) (a, b) l2).cons (a, c))).trans
      (List.Perm.swap (b, c) (a, c) ((a, b) :: l2)))).append_left l1
  have hab' : a.val < b.val := hab
  have hbc' : b.val < c.val := hbc
  have hxy : ((b, c) : Fin n × Fin n) ≠ (a, c) := fun e => by
    have := congrArg (fun p : Fin n × Fin n => p.1.val) e; simp at this; omega
  have hxz : ((b, c) : Fin n × Fin n) ≠ (a, b) := fun e => by
    have := congrArg (fun p : Fin n × Fin n => p.1.val) e; simp at this; omega
  have hyz : ((a, c) : Fin n × Fin n) ≠ (a, b) := fun e => by
    have := congrArg (fun p : Fin n × Fin n => p.2.val) e; simp at this; omega
  have hx : (b, c) ∉ l1 := cn_notMem hnd (by simp)
  have hy : (a, c) ∉ l1 := cn_notMem hnd (by simp)
  have hz : (a, b) ∉ l1 := cn_notMem hnd (by simp)
  refine ⟨hperm.nodup_iff.2 hnd, fun ab hab => hb ab (hperm.mem_iff.1 hab),
    fun x y hj hxy => hperm.mem_iff.2 (hc x y hj hxy), ?_⟩
  intro x y z hj hxy' hyz'
  exact cn_ar_braid' hxy' hyz' hab' hbc' (ht x y z hj hxy' hyz')
    (cn_posR_braid l1 l2 b c a c a b hxy hxz hyz hx hy hz x y)
    (cn_posR_braid l1 l2 b c a c a b hxy hxz hyz hx hy hz x z)
    (cn_posR_braid l1 l2 b c a c a b hxy hxz hyz hx hy hz y z)

theorem cn_NO_rev {j : ℕ} {l : List (Fin n × Fin n)} (h : NO n j l) : NO n j l.reverse := by
  unfold NO at h ⊢
  obtain ⟨hnd, hb, hc, ht⟩ := h
  refine ⟨List.nodup_reverse.2 hnd, fun ab hab => hb ab (List.mem_reverse.1 hab),
    fun x y hj hxy => List.mem_reverse.2 (hc x y hj hxy), ?_⟩
  intro x y z hj hxy hyz
  have e1 := cn_idx_rev hnd (hc x y hj hxy)
  have e2 := cn_idx_rev hnd (hc x z hj (hxy.trans hyz))
  have e3 := cn_idx_rev hnd (hc y z (hj.trans hxy.le) hyz)
  have o := ht x y z hj hxy hyz
  omega

end Formalism.MainNotions.G.ExtremalProjector
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.ProjectorCoeffSuccIndex
section
noncomputable section

open Finset
open scoped Nat

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

def dn (c : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (c + k + 1) * dn c k

theorem dn_eq (c k : ℕ) : dn c k = (c + k).choose k * k ! := by
  induction k with
  | zero => simp [dn]
  | succ k ih =>
    have h := Nat.add_one_mul_choose_eq (c + k) k
    rw [dn, ih, Nat.factorial_succ, show c + (k + 1) = c + k + 1 by omega, ← mul_assoc, h]
    ring

theorem dn_shift (c k : ℕ) : (c + 1) * dn (c + 1) k = dn c (k + 1) := by
  induction k with
  | zero => simp [dn]
  | succ k ih =>
    simp only [dn] at ih ⊢
    rw [← ih]
    ring

theorem dn_pos (c k : ℕ) : 0 < dn c k := by
  rw [dn_eq]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.factorial_pos k)

section Coef

variable (K : Type*) [Field K] [CharZero K]

def al (c k : ℕ) : K := (-1) ^ k / ((dn c k : K) * (k ! : K))

theorem projector_coeff_succ_index (c j : ℕ) : al K c (j + 1) * ((j : K) + 1) = - al K (c + 1) j / ((c : K) + 1) := by
  have h1 : (dn (c + 1) j : K) ≠ 0 := by exact_mod_cast (dn_pos _ _).ne'
  have h2 : (j ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have h3 : (c : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero c
  have h4 : (j : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero j
  unfold al
  rw [← dn_shift c j, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem projector_coeff_succ_level (c j : ℕ) : al K c j = al K (c + 1) j * ((c : K) + j + 1) / ((c : K) + 1) := by
  have key : ((c : K) + j + 1) * (dn c j : K) = ((c : K) + 1) * (dn (c + 1) j : K) := by
    have := dn_shift c j
    simp only [dn] at this
    exact_mod_cast this.symm
  have hc : (c : K) + j + 1 ≠ 0 := by
    have := Nat.cast_add_one_ne_zero (R := K) (c + j)
    push_cast at this
    exact this
  have hd : (dn c j : K) = ((c : K) + 1) * (dn (c + 1) j : K) / ((c : K) + j + 1) := by
    rw [eq_div_iff hc, mul_comm, key]
  have h1 : (dn (c + 1) j : K) ≠ 0 := by exact_mod_cast (dn_pos _ _).ne'
  have h2 : (j ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have h3 : (c : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero c
  unfold al
  rw [hd]
  field_simp

end Coef

section Ring

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

def P (f e : Module.End K V) (c T : ℕ) : Module.End K V :=
  ∑ k ∈ Finset.range (T + 1), al K c k • (f ^ k * e ^ k)

theorem pf_eq_P {n : ℕ} (E : GLOps n K V) (a b : Fin n) (c T : ℕ) : pf E a b c T = P (E b a) (E a b) c T := by
  unfold pf P
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold divPowE
  rw [smul_mul_smul_comm, smul_smul]
  congr 1
  have h1 : (((c + k).choose k : ℕ) : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have h2 : (k ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  unfold al
  rw [dn_eq]
  push_cast
  field_simp

theorem tele (t : ℕ → V) (s T : ℕ) (γ : K) (hT : t T = 0) :
    ∑ k ∈ Finset.range (T + 1), al K s k • (t k + ((k : K) * (γ + k)) • t (k - 1)) =
      (((s : K) - γ) / ((s : K) + 1)) • ∑ k ∈ Finset.range (T + 1), al K (s + 1) k • t k := by
  have hA : ∑ k ∈ Finset.range (T + 1), al K s k • t k = ∑ k ∈ Finset.range T, al K s k • t k := by
    rw [Finset.sum_range_succ, hT, smul_zero, add_zero]
  have hR : ∑ k ∈ Finset.range (T + 1), al K (s + 1) k • t k =
      ∑ k ∈ Finset.range T, al K (s + 1) k • t k := by
    rw [Finset.sum_range_succ, hT, smul_zero, add_zero]
  have hB : ∑ k ∈ Finset.range (T + 1), al K s k • (((k : K) * (γ + k)) • t (k - 1)) =
      ∑ j ∈ Finset.range T, (al K s (j + 1) * (((j : K) + 1) * (γ + j + 1))) • t j := by
    rw [Finset.sum_range_succ']
    have h0 : al K s 0 • ((((0 : ℕ) : K) * (γ + ((0 : ℕ) : K))) • t (0 - 1)) = 0 := by simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_smul, Nat.add_sub_cancel]
    congr 1
    push_cast
    ring
  simp only [smul_add, Finset.sum_add_distrib]
  rw [hA, hB, hR, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_smul, ← add_smul]
  congr 1
  have h1 := projector_coeff_succ_index K s j
  have h2 := projector_coeff_succ_level K s j
  have hs : (s : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero s
  have h3 : al K s (j + 1) * (((j : K) + 1) * (γ + j + 1)) =
      al K s (j + 1) * ((j : K) + 1) * (γ + j + 1) := by ring
  rw [h2, h3, h1]
  field_simp
  ring

section Rank1

variable {e f h : Module.End K V}

theorem hE_pow (hhe : h * e = e * h + (2 : K) • e) {x : V} {c : K} (hx : h x = c • x) (k : ℕ) :
    h ((e ^ k) x) = (c + 2 * k) • (e ^ k) x := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have key : h (e ((e ^ k) x)) = e (h ((e ^ k) x)) + (2 : K) • e ((e ^ k) x) := by
      have := LinearMap.congr_fun hhe ((e ^ k) x)
      rw [Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
      exact this
    rw [pow_succ', Module.End.mul_apply, key, ih, map_smul, ← add_smul]
    congr 1
    push_cast
    ring

theorem hF_pow (hhf : h * f = f * h - (2 : K) • f) {x : V} {c : K} (hx : h x = c • x) (k : ℕ) :
    h ((f ^ k) x) = (c - 2 * k) • (f ^ k) x := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have key : h (f ((f ^ k) x)) = f (h ((f ^ k) x)) - (2 : K) • f ((f ^ k) x) := by
      have := LinearMap.congr_fun hhf ((f ^ k) x)
      rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
      exact this
    rw [pow_succ', Module.End.mul_apply, key, ih, map_smul, ← sub_smul]
    congr 1
    push_cast
    ring

theorem lemA (hef : e * f = f * e + h) (hhf : h * f = f * h - (2 : K) • f) {v : V} {c : K} (hv : h v = c • v)
    (k : ℕ) : e ((f ^ (k + 1)) v) = (f ^ (k + 1)) (e v) + (((k : K) + 1) * (c - k)) • (f ^ k) v := by
  have hef' : ∀ y, e (f y) = f (e y) + h y := fun y => by
    have := LinearMap.congr_fun hef y
    rw [Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply] at this
    exact this
  have hp : ∀ (n : ℕ) (y : V), (f ^ (n + 1)) y = f ((f ^ n) y) := fun n y => by
    rw [pow_succ', Module.End.mul_apply]
  induction k with
  | zero => simp [hef', hv]
  | succ k ih =>
    have hfk := hF_pow hhf hv (k + 1)
    rw [hp (k + 1) v, hef', ih, hfk, map_add, map_smul, ← hp (k + 1) (e v), ← hp k v,
      add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

theorem lemB (hef : e * f = f * e + h) (hhe : h * e = e * h + (2 : K) • e) {v : V} {c : K} (hv : h v = c • v)
    (k : ℕ) : (e ^ (k + 1)) (f v) = f ((e ^ (k + 1)) v) + (((k : K) + 1) * (c + k)) • (e ^ k) v := by
  have hef' : ∀ y, e (f y) = f (e y) + h y := fun y => by
    have := LinearMap.congr_fun hef y
    rw [Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply] at this
    exact this
  have hp : ∀ (n : ℕ) (y : V), (e ^ (n + 1)) y = e ((e ^ n) y) := fun n y => by
    rw [pow_succ', Module.End.mul_apply]
  induction k with
  | zero => simp [hef', hv]
  | succ k ih =>
    have hek := hE_pow hhe hv (k + 1)
    rw [hp (k + 1) (f v), ih, map_add, map_smul, hef', hek, ← hp (k + 1) v, ← hp k v,
      add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

theorem P_apply (f e : Module.End K V) (c T : ℕ) (y : V) :
    P f e c T y = ∑ k ∈ Finset.range (T + 1), al K c k • (f ^ k) ((e ^ k) y) := by
  simp only [P, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]

theorem R1 (hef : e * f = f * e + h) (hhe : h * e = e * h + (2 : K) • e) (hhf : h * f = f * h - (2 : K) • f)
    {x : V} {c : K} (hx : h x = c • x) (s T : ℕ) (he : e ^ T = 0) :
    e (P f e s T x) = (((s : K) - c - 1) / ((s : K) + 1)) • P f e (s + 1) T (e x) := by
  have hk : ∀ k : ℕ, e ((f ^ k) ((e ^ k) x)) =
      (f ^ k) ((e ^ k) (e x)) + ((k : K) * ((c + 1) + k)) • (f ^ (k - 1)) ((e ^ (k - 1)) (e x)) := by
    intro k
    rcases k with _ | j
    · simp
    · have h1 := lemA hef hhf (hE_pow hhe hx (j + 1)) j
      have h2 : e ((e ^ (j + 1)) x) = (e ^ (j + 1)) (e x) := by
        rw [← Module.End.mul_apply, ← pow_succ', pow_succ, Module.End.mul_apply]
      have h3 : (e ^ (j + 1)) x = (e ^ j) (e x) := by rw [pow_succ, Module.End.mul_apply]
      rw [h1, h2, Nat.add_sub_cancel, ← h3]
      congr 2
      push_cast
      ring
  have ht := tele (fun j => (f ^ j) ((e ^ j) (e x))) s T (c + 1) (by simp [he])
  rw [P_apply, P_apply, map_sum, show (s : K) - c - 1 = (s : K) - (c + 1) by ring, ← ht]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hk]

theorem sl2_projector_apply_f_eq_smul_f_projector_succ (hef : e * f = f * e + h) (hhe : h * e = e * h + (2 : K) • e)
    {z : V} {c : K} (hz : h z = c • z) (s T : ℕ) (he : e ^ T = 0) :
    P f e s T (f z) = (((s : K) + 1 - c) / ((s : K) + 1)) • f (P f e (s + 1) T z) := by
  have hpf : ∀ (n : ℕ) (y : V), (f ^ (n + 1)) y = (f ^ n) (f y) := fun n y => by
    rw [pow_succ, Module.End.mul_apply]
  have hpf' : ∀ (n : ℕ) (y : V), (f ^ (n + 1)) y = f ((f ^ n) y) := fun n y => by
    rw [pow_succ', Module.End.mul_apply]
  have key : ∀ k : ℕ, (f ^ k) ((e ^ k) (f z)) = (f ^ (k + 1)) ((e ^ k) z) +
      ((k : K) * ((c - 1) + k)) • (f ^ (k - 1 + 1)) ((e ^ (k - 1)) z) := by
    intro k
    cases k with
    | zero => simp
    | succ j =>
      rw [lemB hef hhe hz j, map_add, map_smul, ← hpf (j + 1), Nat.add_sub_cancel]
      congr 2
      push_cast
      ring
  have ht := tele (fun k => (f ^ (k + 1)) ((e ^ k) z)) s T (c - 1)
    (by show (f ^ (T + 1)) ((e ^ T) z) = 0; rw [he]; simp)
  beta_reduce at ht
  rw [P_apply, P_apply, map_sum]
  simp only [key, map_smul, ← hpf']
  rw [ht]
  congr 1
  ring

end Rank1

end Ring

end Formalism.MainNotions.G.ExtremalProjector
end
end

