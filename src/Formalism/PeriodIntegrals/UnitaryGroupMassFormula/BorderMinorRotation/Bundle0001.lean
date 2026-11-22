import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.Development

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.SkipOneEqSuccAbove
section
open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmBorderFull

open PI

theorem val_succAbove {t : ℕ} (p : Fin (t + 1)) (i : Fin t) :
    ((p.succAbove i : Fin (t + 1)) : ℕ) = if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  by_cases h : (i : ℕ) < (p : ℕ)
  · rw [if_pos h]
    first
    | exact congrArg Fin.val (Fin.succAbove_of_castSucc_lt p i h)
    | (rw [Fin.succAbove_of_castSucc_lt p i (by simpa [Fin.lt_iff_val_lt_val] using h)]; simp)
  · rw [if_neg h]
    first
    | exact congrArg Fin.val (Fin.succAbove_of_le_castSucc p i (Nat.not_lt.mp h))
    | (rw [Fin.succAbove_of_le_castSucc p i (by simp [Fin.le_iff_val_le_val]; omega)]; simp)

theorem skip_one_eq_succAbove {t : ℕ} (p : Fin (t + 1)) (i : Fin t) : skip1 p i = p.succAbove i := by
  apply Fin.ext
  rw [val_succAbove]
  unfold skip1
  split_ifs with h1 h2 <;> first | rfl | (exact absurd h1 h2) | (exact absurd h2 h1) | omega

theorem comp_skip1 {α : Type*} {t : ℕ} (f : Fin (t + 1) → α) (p : Fin (t + 1)) :
    f ∘ skip1 p = f ∘ p.succAbove := by
  funext i
  exact congrArg f (skip_one_eq_succAbove p i)

theorem bS_castSucc {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : bS v es ∘ Fin.castSucc = v := by
  funext i
  first | simp [bS] | (simp only [Function.comp_apply, bS, Fin.snoc_castSucc])

theorem bS_last {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : bS v es (Fin.last m) = es := by
  first | simp [bS] | (simp only [bS, Fin.snoc_last])

theorem rot_cons {n k : ℕ} (e : Fin n) (W : Fin k → Fin n) :
    bE e W = Fin.snoc (α := fun _ => Fin n) W e ∘ (finRotate (k + 1)).symm := by
  first
  | (rw [Fin.snoc_eq_cons_rotate]; funext i; simp [bE])
  | (funext i; obtain ⟨j, rfl⟩ := (finRotate (k + 1)).surjective i; simp only [Function.comp_apply, Equiv.symm_apply_apply, bE]; induction j using Fin.lastCases <;> simp [finRotate_last, finRotate_succ_apply])

theorem rowE (hLR : ExpLastRow) {A : Type} [Ring A] [Algebra ℂ A] {n k : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (e : Fin n) (W : Fin k → Fin n) (v : Fin (k + 1) → Fin n) (he : ∀ x, v x ≠ e) (u : ℂ) :
    qminor E (bE e W) v u =
      ∑ x : Fin (k + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) * (qminor E W (v ∘ x.succAbove) (u - 1) * E e (v x)) := by
  have hperm : ∀ (a : Fin (k + 1) → Fin n) (τ : Equiv.Perm (Fin (k + 1))),
      qminor E (a ∘ τ) v u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a v u := by
    intro a τ
    unfold qminor
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
    have hτ : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign τ : ℤ) : A) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.Perm.sign_mul,
      Units.val_mul, Int.cast_mul]
    rw [← mul_assoc, ← mul_assoc, hτ, one_mul]
  have hs : ∀ x : Fin (k + 1), ((Equiv.Perm.sign (finRotate (k + 1)).symm : ℤ) : A) *
      (((-1 : ℤ) ^ (k + (x : ℕ)) : ℤ) : A) = (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) := by
    intro x
    rw [Equiv.Perm.sign_symm, sign_finRotate, ← Int.cast_mul, Units.val_pow_eq_pow_val, Units.val_neg,
      Units.val_one, ← pow_add]
    congr 1
    have hx : ∀ a : ℕ, a = 2 * k + (x : ℕ) → (-1 : ℤ) ^ a = (-1) ^ (x : ℕ) := by
      rintro a rfl
      rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    exact hx _ (by omega)
  rw [rot_cons e W, hperm, hLR A n k E hE (Fin.snoc (α := fun _ => Fin n) W e) v u, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h1 : (Fin.snoc (α := fun _ => Fin n) W e ∘ Fin.castSucc) = W := by
    funext i
    simp
  have h2 : Tm E u e (v x) = E e (v x) := by
    unfold Tm
    rw [if_neg (fun h => he x h.symm), zero_add]
  rw [← mul_assoc, hs x, h1, Fin.snoc_last, h2]

theorem rw_zero {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1)) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) 0 = e := by
  first
  | simp [bE]
  | (show bE e (bS v es) ((w.castSucc.succ).succAbove 0) = e; rw [Fin.succ_succAbove_zero]; simp only [bE, Fin.cons_zero])

theorem rw_last {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1)) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) (Fin.last (k + 1)) = es := by
  show bE e (bS v es) ((w.castSucc.succ).succAbove (Fin.last (k + 1))) = es
  have hw := w.isLt
  have h1 : (w.castSucc.succ).succAbove (Fin.last (k + 1)) = (Fin.last (k + 1)).succ :=
    Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; split_ifs <;> omega)
  rw [h1]
  simp only [bE, bS, Fin.cons_succ, Fin.snoc_last]

theorem rows_succ {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1))
    (h : k + 1 = k + 1 - 1 + 1) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ Fin.succ =
      Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast h := by
  funext j
  simp only [Function.comp_apply]
  have hw := w.isLt
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have h1 : (w.castSucc.succ).succAbove (Fin.last k).succ = (Fin.last (k + 1)).succ :=
      Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; split_ifs <;> omega)
    rw [h1]
    simp only [bE, bS, Fin.cons_succ, Fin.snoc_last, Fin.cast_last]
  · have hj := j.isLt
    have h2 : (w.castSucc.succ).succAbove (Fin.castSucc j).succ = (Fin.castSucc (w.succAbove j)).succ :=
      Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc]; split_ifs <;> omega)
    have h3 : Fin.cast h (Fin.castSucc j) = Fin.castSucc (Fin.cast (by omega) j : Fin (k + 1 - 1)) :=
      Fin.ext (by simp only [Fin.coe_cast, Fin.coe_castSucc])
    rw [h2, h3]
    simp only [bE, bS, Fin.cons_succ, Fin.snoc_castSucc, Function.comp_apply]
    rw [skip_one_eq_succAbove]
    rfl

theorem rows_last {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1)) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ (Fin.last (k + 1)).succAbove = bE e (v ∘ w.succAbove) := by
  funext j
  have hw := w.isLt
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Function.comp_apply]
    have h0 : (Fin.last (k + 1)).succAbove 0 = 0 := Fin.ext (by rw [val_succAbove]; simp)
    rw [h0, Fin.succ_succAbove_zero]
    simp only [bE, Fin.cons_zero]
  · simp only [Function.comp_apply]
    have hj := j.isLt
    have h1 : (w.castSucc.succ).succAbove ((Fin.last (k + 1)).succAbove j.succ) = (Fin.castSucc (w.succAbove j)).succ :=
      Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; split_ifs <;> omega)
    rw [h1]
    simp only [bE, bS, Fin.cons_succ, Fin.snoc_castSucc, Function.comp_apply]

theorem cmul {A : Type*} [Ring A] (s : ℤ) (x y : A) : x * ((s : A) * y) = (s : A) * (x * y) := by
  rw [← mul_assoc, ← mul_assoc, Int.cast_comm]

theorem bfMid_of (hLC : ExpLastCol) (hLR : ExpLastRow) (hX : BFCross) : BFMid := by
  intro A _ _ n m E e es v hE hB u w
  cases m with
  | zero => exact w.elim0
  | succ k =>
  have hv : ∀ x, v x ≠ e := hB.2.2.1
  have hves : ∀ x, v x ≠ es := hB.2.2.2
  have hL : bE e (bS v es) w.castSucc.succ = v w := by simp [bE, bS]
  have hT : Tm E u (v w) e = E (v w) e := by simp [Tm, hv w]
  rw [hL, show bE e (bS v es) 0 = e from rfl, hT, show bE e (bS v es) ∘ Fin.succ = bS v es from rfl]
  rw [hLC A n (k + 1) E _ (bS v es) (u - 1), Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [bS_castSucc, bS_last]
  rw [hX A n k E e es v hE hB u w]
  simp only [Fin.succAbove_zero, Fin.succ_last, rw_zero, rw_last, rows_last]
  rw [rows_succ e es v w (by omega), rowE hLR E hE e (v ∘ w.succAbove) v hv (u - 1)]
  simp only [comp_skip1]
  have hTe : Tm E (u - 1 - ((k + 1 : ℕ) : ℂ)) e es = E e es := by simp [Tm, hB.2.1]
  have hu2 : u - 1 - 1 = u - 2 := by ring
  have hu3 : u - 1 - ((k + 1 : ℕ) : ℂ) = u - ((k + 1 : ℕ) : ℂ) - 1 := by ring
  rw [hTe, hu2, hu3]
  have hcomm : ∀ x, E e (v x) * Tm E (u - ((k + 1 : ℕ) : ℂ) - 1) es es =
      Tm E (u - ((k + 1 : ℕ) : ℂ) - 1) es es * E e (v x) := fun x =>
    (tm_comm_E E hE _ es e (v x) hB.2.1.symm (hves x)).symm
  have he2 : ((-1 : ℤ) ^ (k + 1 + (k + 1))) = 1 := Even.neg_one_pow ⟨k + 1, rfl⟩
  have p0 : ∀ Q : A, (((-1 : ℤ) ^ ((w : ℕ) + 1) : ℤ) : A) * (E (v w) e * ((((-1 : ℤ) ^ (k + 1) : ℤ) : A) * (Q * E e es)))
      = (((-1 : ℤ) ^ ((w : ℕ) + 1 + (k + 1)) : ℤ) : A) * (E (v w) e * (Q * E e es)) := by
    intro Q; rw [cmul, ← mul_assoc, ← Int.cast_mul, ← pow_add]
  have pm : ∀ S : A, (((-1 : ℤ) ^ ((w : ℕ) + 1) : ℤ) : A) * (E (v w) e * ((((-1 : ℤ) ^ (w : ℕ) : ℤ) : A) * S))
      = -(E (v w) e * S) := by
    intro S
    rw [cmul, ← mul_assoc, ← Int.cast_mul, ← pow_add, Odd.neg_one_pow ⟨w, by ring⟩, Int.cast_neg, Int.cast_one,
      neg_one_mul]
  have pl : ∀ f : Fin (k + 1) → A,
      (((-1 : ℤ) ^ ((w : ℕ) + 1) : ℤ) : A) * (E (v w) e * ∑ x : Fin (k + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) * f x)
      = -∑ x : Fin (k + 1), (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) * (E (v w) e * f x) := by
    intro f
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [cmul, ← mul_assoc, ← Int.cast_mul, ← pow_add,
      show ((-1 : ℤ) ^ ((w : ℕ) + 1 + (x : ℕ))) = -(-1) ^ ((w : ℕ) + (x : ℕ)) by ring, Int.cast_neg, neg_mul]
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last, add_zero, Nat.succ_eq_add_one, he2,
    Int.cast_one, one_mul, Finset.sum_mul, mul_assoc, hcomm, mul_add]
  simp only [p0, pm, pl]
  simp only [Finset.mul_sum, mul_ite, mul_zero, cmul]
  abel

end PI.UnitaryGroupMassFormula.QmBorderFull
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.SkipTwoSuccAboveComp
section
open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmBorderFull.Four

open PI

theorem val_sA {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  by_cases h : k.val < p.val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    rfl
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using not_lt.mp h)]
    rfl

theorem cons_comp_finRotate {n t : ℕ} (e : Fin n) (f : Fin t → Fin n) :
    bE e f ∘ (finRotate (t + 1) : Fin (t + 1) → Fin (t + 1)) = bS f e := by
  unfold bE bS
  rw [Fin.snoc_eq_cons_rotate]
  rfl

theorem neg_one_pow_mul_self (t : ℕ) : ((-1 : ℤ) ^ t) * ((-1 : ℤ) ^ t) = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem qminor_comp_perm_eq_sign_mul {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (τ : Equiv.Perm (Fin t)) (u : ℂ) :
    qminor E (a ∘ τ) b u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a b u := by
  unfold qminor
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [Function.comp_apply, Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Equiv.Perm.sign_mul]
  rw [← mul_assoc]
  congr 1
  rw [Units.val_mul, Int.cast_mul, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
    Units.val_one, Int.cast_one, one_mul]

theorem qminor_bE_eq {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (e : Fin n)
    (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bE e f) b u = (((-1 : ℤ) ^ t : ℤ) : A) * qminor E (bS f e) b u := by
  have h := qminor_comp_perm_eq_sign_mul E (bE e f) b (finRotate (t + 1)) u
  rw [cons_comp_finRotate, sign_finRotate, Nat.add_sub_cancel] at h
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h
  rw [h, ← mul_assoc, ← Int.cast_mul, neg_one_pow_mul_self, Int.cast_one, one_mul]

theorem qminor_bS_eq {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (e : Fin n)
    (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bS f e) b u = (((-1 : ℤ) ^ t : ℤ) : A) * qminor E (bE e f) b u := by
  have h := qminor_comp_perm_eq_sign_mul E (bE e f) b (finRotate (t + 1)) u
  rw [cons_comp_finRotate, sign_finRotate, Nat.add_sub_cancel] at h
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h
  exact h

theorem Tm_of_ne {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) {a b : Fin n}
    (h : a ≠ b) : Tm E u a b = E a b := by
  unfold Tm
  simp [h]

theorem zmul {A : Type} [Ring A] (z : ℤ) (y : A) : (z : A) * y = z • y := by
  rw [zsmul_eq_mul]

theorem rowPart (hR : ExpLastRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (hG : GlRel E) (e : Fin n) (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (he : ∀ x, b x ≠ e) (u : ℂ) :
    qminor E (bE e f) b u = ∑ x : Fin (t + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) *
      (qminor E f (b ∘ x.succAbove) (u - 1) * E e (b x)) := by
  rw [qminor_bE_eq, hR A n t E hG (bS f e) b u, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : bS f e ∘ Fin.castSucc = f := by
    funext i
    simp [bS]
  have h2 : bS f e (Fin.last t) = e := by simp [bS]
  have hs : (-1 : ℤ) ^ t * (-1 : ℤ) ^ (t + (x : ℕ)) = (-1 : ℤ) ^ (x : ℕ) := by
    rw [pow_add, ← mul_assoc, neg_one_pow_mul_self, one_mul]
  rw [h1, h2, Tm_of_ne E u (Ne.symm (he x)), ← mul_assoc, ← Int.cast_mul, hs]

theorem colPart (hF : ExpFirstRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (hG : GlRel E) (e : Fin n) (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (he : ∀ x, b x ≠ e) (u : ℂ) :
    qminor E (bS f e) b u = ∑ x : Fin (t + 1), (((-1 : ℤ) ^ (t + (x : ℕ)) : ℤ) : A) *
      (E e (b x) * qminor E f (b ∘ x.succAbove) u) := by
  rw [qminor_bS_eq, hF A n t E hG (bE e f) b u, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : bE e f ∘ Fin.succ = f := by
    funext i
    simp [bE]
  have h2 : bE e f 0 = e := by simp [bE]
  rw [h1, h2, Tm_of_ne E _ (Ne.symm (he x)), ← mul_assoc, ← Int.cast_mul, ← pow_add]

theorem inner (hR : ExpLastRow) (hF : ExpFirstRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (hG : GlRel E) (e es : Fin n) (W : Fin t → Fin n) (b : Fin (t + 2) → Fin n)
    (he : ∀ x, b x ≠ e) (hes : ∀ x, b x ≠ es) (z : ℂ) :
    qminor E (bE e (bS W es)) b z = ∑ x : Fin (t + 2), ∑ y : Fin (t + 1),
      (((-1 : ℤ) ^ ((x : ℕ) + t + (y : ℕ)) : ℤ) : A) *
        (E es (b (x.succAbove y)) * qminor E W ((b ∘ x.succAbove) ∘ y.succAbove) (z - 1) * E e (b x)) := by
  rw [rowPart hR E hG e (bS W es) b he z]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [colPart hF E hG es W (b ∘ x.succAbove) (fun y => hes _) (z - 1), Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Function.comp_apply, ← mul_assoc, ← Int.cast_mul, ← pow_add, add_assoc]

theorem skip_two_succAbove_comp_alt {k : ℕ} (w : Fin (k + 2)) (j : Fin (k + 1)) (i : Fin k) :
    skip2 (min w (w.succAbove j)) (max w (w.succAbove j)) i = w.succAbove (j.succAbove i) := by
  apply Fin.ext
  have hv := val_sA w j
  rw [val_sA w (j.succAbove i), val_sA j i]
  unfold skip2
  rcases lt_or_ge (j : ℕ) (w : ℕ) with h | h
  · have hlt : w.succAbove j < w := by rw [Fin.lt_def, hv, if_pos h]; exact h
    rw [min_eq_right hlt.le, max_eq_left hlt.le]
    rw [if_pos h] at hv
    split_ifs <;> (simp_all; try omega)
  · have hle : w ≤ w.succAbove j := by rw [Fin.le_def, hv, if_neg (by omega)]; omega
    rw [min_eq_left hle, max_eq_right hle]
    rw [if_neg (by omega)] at hv
    split_ifs <;> (simp_all; try omega)

theorem sign_pair_succAbove_right {k : ℕ} (w : Fin (k + 1)) (j : Fin k) :
    sg2 w (w.succAbove j) = (-1 : ℤ) ^ ((w : ℕ) + (j : ℕ)) := by
  unfold sg2
  rcases lt_or_ge (j : ℕ) (w : ℕ) with h | h
  · have hv : (w.succAbove j).val = j := by rw [val_sA, if_pos h]
    rw [if_pos (by rw [hv]; exact h), hv]
  · have hv : (w.succAbove j).val = j + 1 := by rw [val_sA, if_neg (by omega)]
    rw [if_neg (by rw [hv]; omega), hv, show (w : ℕ) + (j + 1) + 1 = (w + j) + 2 by ring, pow_add]
    norm_num

theorem sign_two_succAbove_left {k : ℕ} (x : Fin (k + 1)) (y : Fin k) :
    sg2 (x.succAbove y) x = -(-1 : ℤ) ^ ((x : ℕ) + (y : ℕ)) := by
  unfold sg2
  rcases lt_or_ge (y : ℕ) (x : ℕ) with h | h
  · have hv : (x.succAbove y).val = y := by rw [val_sA, if_pos h]
    rw [if_neg (by rw [hv]; omega), hv, pow_succ, add_comm (y : ℕ)]
    ring
  · have hv : (x.succAbove y).val = y + 1 := by rw [val_sA, if_neg (by omega)]
    rw [if_pos (by rw [hv]; omega), hv, show (y : ℕ) + 1 + x = (x + y) + 1 by ring, pow_succ]
    ring

theorem sum_sA_ite {M : Type*} [AddCommMonoid M] {k : ℕ} (w : Fin (k + 1)) (g : Fin (k + 1) → M) :
    ∑ w' : Fin (k + 1), (if w ≠ w' then g w' else 0) = ∑ j : Fin k, g (w.succAbove j) := by
  rw [Fin.sum_univ_succAbove _ w, if_neg (not_not.mpr rfl), zero_add]
  exact Finset.sum_congr rfl fun j _ => if_pos (Fin.succAbove_ne w j).symm

theorem triple {M : Type*} [AddCommMonoid M] {k : ℕ} (w : Fin (k + 1))
    (H : Fin (k + 1) → Fin (k + 1) → Fin (k + 1) → M) :
    ∑ w' : Fin (k + 1), ∑ x : Fin (k + 1), ∑ x' : Fin (k + 1), (if w ≠ w' ∧ x ≠ x' then H w' x x' else 0)
      = ∑ j : Fin k, ∑ x' : Fin (k + 1), ∑ y : Fin k, H (w.succAbove j) (x'.succAbove y) x' := by
  have h1 : ∀ w' : Fin (k + 1), (∑ x : Fin (k + 1), ∑ x' : Fin (k + 1),
      (if w ≠ w' ∧ x ≠ x' then H w' x x' else 0)) =
      if w ≠ w' then ∑ x : Fin (k + 1), ∑ x' : Fin (k + 1), (if x ≠ x' then H w' x x' else 0) else 0 := by
    intro w'
    by_cases hw : w ≠ w'
    · simp [hw]
    · simp [hw]
  rw [Finset.sum_congr rfl fun w' _ => h1 w', sum_sA_ite]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  have h2 : ∀ x : Fin (k + 1), (if x ≠ x' then H (w.succAbove j) x x' else 0) =
      if x' ≠ x then H (w.succAbove j) x x' else 0 := by
    intro x
    by_cases h : x = x'
    · subst h
      rfl
    · rw [if_pos h, if_pos (Ne.symm h)]
  rw [Finset.sum_congr rfl fun x _ => h2 x]
  exact sum_sA_ite x' (fun x => H (w.succAbove j) x x')

theorem mid_comp {n t : ℕ} (e es : Fin n) (F : Fin (t + 1) → Fin n) (p : Fin (t + 1)) :
    bE e (bS F es) ∘ (p.castSucc.succ).succAbove = bE e (bS (F ∘ p.succAbove) es) := by
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp [bE]
  · simp only [Function.comp_apply, bE, Fin.succ_succAbove_succ, Fin.cons_succ]
    refine Fin.lastCases ?_ (fun i'' => ?_) i'
    · rw [Fin.succAbove_ne_last_last (Fin.castSucc_lt_last p).ne]
      simp [bS]
    · rw [Fin.castSucc_succAbove_castSucc]
      simp [bS]

theorem mid_val {n t : ℕ} (e es : Fin n) (F : Fin t → Fin n) (j : Fin t) :
    bE e (bS F es) j.castSucc.succ = F j := by
  simp [bE, bS]

theorem scal (k w j x y : ℕ) :
    (-1 : ℤ) ^ (k + 1 + 1 + (j + 1)) * (-1 : ℤ) ^ (x + k + y) =
      (-1 : ℤ) ^ w * ((-1 : ℤ) ^ (w + j) * -(-1 : ℤ) ^ (x + y)) := by
  have hk := neg_one_pow_mul_self k
  have hw := neg_one_pow_mul_self w
  linear_combination (-(-1 : ℤ) ^ (j + x + y)) * hk + ((-1 : ℤ) ^ (j + x + y)) * hw

private theorem intCast_mul_mul_mul_eq_of_mul_eq {A : Type} [Ring A] (c₁ c₂ c₀ a : ℤ) (X S : A) (h : c₁ * c₂ = c₀ * a) :
    (c₁ : A) * (((c₂ : A) * X) * S) = (c₀ : A) * ((a : A) * (X * S)) := by
  rw [mul_assoc (c₂ : A), ← mul_assoc, ← mul_assoc (c₀ : A), ← Int.cast_mul, ← Int.cast_mul, h]

theorem bfCross_of (hRow : PI.QmRowExp) (_hSkip : PI.QmSkip) : BFCross := by
  intro A _ _ n k E e es v hG hB u w
  obtain ⟨hF, hR⟩ := hRow
  obtain ⟨_, _, hve, hves⟩ := hB
  cases k with
  | zero =>
    rw [Fin.sum_univ_zero]
    symm
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun w' _ => Finset.sum_eq_zero fun x _ =>
      Finset.sum_eq_zero fun x' _ => if_neg fun h => h.1 (Fin.ext ?_))
    have := w.isLt
    have := w'.isLt
    omega
  | succ k =>
    have ht := triple w (M := A) (fun w' x x' => ((sg2 w w' * sg2 x x' : ℤ) : A) *
      (E es (v x) * qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
        E e (v x') * E (v w') es))
    beta_reduce at ht
    rw [ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mid_comp, mid_comp, mid_val, Tm_of_ne E _ (a := (v ∘ w.succAbove) j) (hves (w.succAbove j)),
      inner hR hF E hG e es _ v hve hves (u - 1), Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hq1 : v ∘ skip2 (min w (w.succAbove j)) (max w (w.succAbove j)) = (v ∘ w.succAbove) ∘ j.succAbove := by
      funext i
      simp only [Function.comp_apply, skip_two_succAbove_comp_alt]
    have hq2 : v ∘ skip2 (min (x.succAbove y) x) (max (x.succAbove y) x) =
        (v ∘ x.succAbove) ∘ y.succAbove := by
      rw [min_comm, max_comm]
      funext i
      simp only [Function.comp_apply, skip_two_succAbove_comp_alt]
    have hu : u - 1 - 1 = u - 2 := by ring
    have hj : (j.castSucc.succ : ℕ) = (j : ℕ) + 1 := by simp
    rw [hq1, hq2, ← hu, sign_pair_succAbove_right, sign_two_succAbove_left, hj]
    exact intCast_mul_mul_mul_eq_of_mul_eq _ _ _ _ _ _ (scal k w j x y)

end PI.UnitaryGroupMassFormula.QmBorderFull.Four
end
end

