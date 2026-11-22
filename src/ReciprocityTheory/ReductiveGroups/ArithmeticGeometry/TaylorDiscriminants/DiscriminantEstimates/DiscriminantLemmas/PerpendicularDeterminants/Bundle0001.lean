import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0001

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.PerpendicularDeterminants.DetMemSubalgebra
section
namespace PI.UnitaryGroupMassFormula.FormPartialDerivatives

open ReciprocityTheory.ChartRestriction.G.TB MvPolynomial

variable {R : Type} [CommRing R] {p q n : ℕ}

def ySide (e : Fin p → Fin n → R) (b : Fin q) :
    Subalgebra R (MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R) where
  carrier := {B | (∀ j, pderiv (Sum.inl j) B = 0) ∧
    (∀ j j', pderiv (Sum.inl j') (pderiv (Sum.inr j) B) = 0) ∧
    (∀ b', ∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) B = 0)}
  mul_mem' := by
    rintro A B ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩
    refine ⟨fun j => ?_, fun j j' => ?_, fun b' => ?_⟩
    · simp [hA1, hB1]
    · simp [hA1, hB1, hA2, hB2]
    · have : ∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) (A * B)
          = (∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) A) * B
            + A * ∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) B := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [pderiv_mul]; ring
      rw [this, hA3, hB3]; ring
  add_mem' := by
    rintro A B ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩
    refine ⟨fun j => ?_, fun j j' => ?_, fun b' => ?_⟩
    · simp [hA1, hB1]
    · simp [hA2, hB2]
    · simp only [map_add, mul_add, Finset.sum_add_distrib, hA3, hB3, add_zero]
  algebraMap_mem' := by
    intro r
    refine ⟨fun j => ?_, fun j j' => ?_, fun b' => ?_⟩ <;> simp [MvPolynomial.algebraMap_eq]

def xSide (e : Fin p → Fin n → R) (a : Fin p) (b : Fin q) :
    Subalgebra R (MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R) where
  carrier := {A | (∀ j, pderiv (Sum.inr j) A = 0) ∧
    ∀ B ∈ ySide e b, ∑ k, pderiv (Sum.inl (a, k)) A * pderiv (Sum.inr (b, k)) B = 0}
  mul_mem' := by
    rintro A A' ⟨hA1, hA2⟩ ⟨hA'1, hA'2⟩
    refine ⟨fun j => ?_, fun B hB => ?_⟩
    · simp [hA1, hA'1]
    · have : ∑ k, pderiv (Sum.inl (a, k)) (A * A') * pderiv (Sum.inr (b, k)) B
          = A' * (∑ k, pderiv (Sum.inl (a, k)) A * pderiv (Sum.inr (b, k)) B)
            + A * ∑ k, pderiv (Sum.inl (a, k)) A' * pderiv (Sum.inr (b, k)) B := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [pderiv_mul]; ring
      rw [this, hA2 B hB, hA'2 B hB]; ring
  add_mem' := by
    rintro A A' ⟨hA1, hA2⟩ ⟨hA'1, hA'2⟩
    refine ⟨fun j => ?_, fun B hB => ?_⟩
    · simp [hA1, hA'1]
    · simp only [map_add, add_mul, Finset.sum_add_distrib, hA2 B hB, hA'2 B hB, add_zero]
  algebraMap_mem' := by
    intro r
    refine ⟨fun j => ?_, fun B _ => ?_⟩ <;> simp [MvPolynomial.algebraMap_eq]

end PI.UnitaryGroupMassFormula.FormPartialDerivatives
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.PerpendicularDeterminants.PerpVecOfPerp
section
namespace PI.UnitaryGroupMassFormula.FormPartialDerivatives

open ReciprocityTheory.ChartRestriction.G.TB

theorem perpVec_perp (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (c : Fin p) :
    h (perpVec h e e' g) (e c) = 0 := by
  have hentry : ∀ a', hMat h e e' a' c = h (e' a') (e c) := fun _ => rfl
  have key : ∀ a, ∑ a', (hMat h e e').adjugate a a' * h (e' a') (e c) =
      if a = c then (hMat h e e').det else 0 := by
    intro a
    have hk := congrFun (congrFun (Matrix.adjugate_mul (hMat h e e')) a) c
    rw [Matrix.mul_apply] at hk
    simp only [hentry] at hk
    rw [hk, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  simp only [perpVec, map_sub, map_smul, map_sum, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul]
  have hsum : ∑ a, ∑ a', (hMat h e e').adjugate a a' * h g (e a) * h (e' a') (e c) =
      (hMat h e e').det * h g (e c) := by
    calc ∑ a, ∑ a', (hMat h e e').adjugate a a' * h g (e a) * h (e' a') (e c)
        = ∑ a, h g (e a) * ∑ a', (hMat h e e').adjugate a a' * h (e' a') (e c) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a' _ => ?_
          ring
      _ = (hMat h e e').det * h g (e c) := by
          simp only [key, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
  rw [hsum]
  ring

theorem perpVec_int (R : Type) [CommRing R] (O : Subring R) (V : Type) [AddCommGroup V] [Module R V]
    (p : ℕ) (h : V →ₗ[R] (V → R)) (L : Submodule O V)
    (hL : ∀ u ∈ L, ∀ v ∈ L, h u v ∈ O) (e e' : Fin p → V) (g : V)
    (he : ∀ a, e a ∈ L) (he' : ∀ a, e' a ∈ L) (hg : g ∈ L) : perpVec h e e' g ∈ L := by
  let MO : Matrix (Fin p) (Fin p) O := Matrix.of fun a' a => ⟨h (e' a') (e a), hL _ (he' a') _ (he a)⟩
  have hMap : hMat h e e' = O.subtype.mapMatrix MO := by
    ext a' a
    rfl
  have hdet : (hMat h e e').det ∈ O := by
    rw [hMap, ← RingHom.map_det]
    exact (MO.det).2
  have hadj : ∀ a a', (hMat h e e').adjugate a a' ∈ O := by
    intro a a'
    rw [hMap, ← RingHom.map_adjugate]
    exact (MO.adjugate a a').2
  have hs : ∀ r ∈ O, ∀ v ∈ L, r • v ∈ L := by
    intro r hr v hv
    exact L.smul_mem (⟨r, hr⟩ : O) hv
  unfold perpVec
  refine L.sub_mem (hs _ hdet _ hg) (L.sum_mem fun a _ => L.sum_mem fun a' _ => ?_)
  exact hs _ (O.mul_mem (hadj a a') (hL _ hg _ (he a))) _ (he' a')

theorem perpVec_of_perp (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (hg : ∀ a, h g (e a) = 0) :
    perpVec h e e' g = (hMat h e e').det • g := by
  simp [perpVec, hg]

end PI.UnitaryGroupMassFormula.FormPartialDerivatives
end

