import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.Ii
import Formalism.PeriodIntegrals.Bundle0005

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.ContractPowSuccMem
section
noncomputable section

universe u v

namespace PI.KoszulExact

section General

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

theorem contract_pow_eq_zero (N : Submodule R M) (f : Module.Dual R M) (hf : ∀ m ∈ N, f m = 0) :
    ∀ (j : ℕ) (x : ExteriorAlgebra R M), x ∈ (N.map (ExteriorAlgebra.ι R)) ^ j →
      CliffordAlgebra.contractLeft f x = 0 := by
  intro j
  induction j with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.mem_one] at hx
    obtain ⟨y, rfl⟩ := hx
    exact CliffordAlgebra.contractLeft_algebraMap _ f y
  | succ j ih =>
    intro x hx
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨m, hm, rfl⟩ := ha
      rw [CliffordAlgebra.contractLeft_ι_mul, hf m hm, ih b hb, zero_smul, mul_zero, sub_zero]
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]

end General

section Koszul

variable {R : Type u} [CommRing R] {D : ℕ}

theorem Li_eq_map (R : Type u) [CommRing R] (D : ℕ) (i : ℕ) :
    Li R D i = (Submodule.span R ((fun k : Fin D => (Pi.single k (1 : R) : Fin D → R)) ''
      {k : Fin D | (k : ℕ) < i})).map (ExteriorAlgebra.ι R) := by
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem form_single (s : Fin D → R) (k : Fin D) : form s (Pi.single k 1) = s k := by
  simp [form, Pi.single_apply]

end Koszul

end PI.KoszulExact
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.KoszulImageInIdeal
section
universe u

namespace PI.KEX

open PI.KoszulExact

def P {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R) (i : ℕ) : Prop :=
  ∀ (j : ℕ) (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D i ^ (j + 1) →
    dK s x = 0 → ∃ y ∈ Li R D i ^ (j + 2), dK s y = x

def F1 : Prop :=
  ∀ (R : Type u) [CommRing R] (D j : ℕ), ⋀[R]^j (Fin D → R) = Li R D D ^ j

def KoszulLowersPower : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (i j : ℕ)
    (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D i ^ (j + 1) → dK s x ∈ Li R D i ^ j

def KoszulImageInIdeal : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (i : ℕ)
    (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D i ^ 1 →
      ∃ r ∈ Ii s i, dK s x = algebraMap R _ r

def secondLeviFamily : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (i : ℕ) (r : R), r ∈ Ii s i →
      ∃ y ∈ Li R D i ^ 1, dK s y = algebraMap R _ r

def F3 : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (i : Fin D) (j : ℕ)
    (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D ((i : ℕ) + 1) ^ (j + 1) →
      ∃ a ∈ Li R D i ^ (j + 1), ∃ b ∈ Li R D i ^ j, x = a + eb R i * b

def F4 : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (i : Fin D) (m n : ℕ)
    (u v : ExteriorAlgebra R (Fin D → R)), u ∈ Li R D i ^ m → v ∈ Li R D i ^ n →
      u + eb R i * v = 0 → v = 0

def W : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
    ∀ (i : Fin D) (r : R), s i * r ∈ Ii s i → r ∈ Ii s i

def Step : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
    ∀ i : Fin D, P s i → P s ((i : ℕ) + 1)

def Sec : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (r : R),
    (∃ y ∈ ⋀[R]^1 (Fin D → R), dK s y = algebraMap R _ r) ↔ r ∈ Ideal.span (Set.range s)

end PI.KEX
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.OfListTakeOfFn
section
noncomputable section

universe u

namespace PI.KoszulExact

open RingTheory.Sequence

theorem ofList_take_ofFn {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R) (i : ℕ) :
    Ideal.ofList ((List.ofFn s).take i) = Ii s i := by
  unfold Ideal.ofList Ii
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image]
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [List.length_take, List.length_ofFn] at hj
    exact ⟨⟨j, by omega⟩, by simp only; omega, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    have := j.isLt
    exact ⟨j, by simp only [List.length_take, List.length_ofFn]; omega, by simp⟩

theorem weak {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R)
    (hs : IsWeaklyRegular R (List.ofFn s)) (i : Fin D) (r : R) (hr : s i * r ∈ Ii s i) :
    r ∈ Ii s i := by
  have key := hs.regular_mod_prev i (by simp)
  have hsm : (Ideal.ofList ((List.ofFn s).take i) • ⊤ : Submodule R R) = Ii s i := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ofList_take_ofFn]
  have e : (List.ofFn s)[(i : ℕ)]'(by simp) = s i := by simp
  rw [e] at key
  have h1 : s i • (Submodule.Quotient.mk r :
      R ⧸ (Ideal.ofList ((List.ofFn s).take i) • ⊤ : Submodule R R)) = s i • 0 := by
    rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsm, smul_eq_mul]
    exact hr
  have h2 := key h1
  rwa [Submodule.Quotient.mk_eq_zero, hsm] at h2

end PI.KoszulExact
end
end

