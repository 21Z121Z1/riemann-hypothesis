import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ExistsDenLattice

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AntiLevWittJ
section
noncomputable section

namespace PI.IwaMeasEx.PD

open Matrix NumberField Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
open scoped TensorProduct

section Witt

variable {J n₀ : ℕ} (c : Composition J)

theorem antiLev_wittJ {R : Type} [CommRing R] [StarRing R] (J0 : Matrix (Fin n₀) (Fin n₀) R) :
    AntiLev (levW (n₀ := n₀) c) c.length (wittJ (J := J) J0) := by
  intro q r h
  have hs : ∀ s : Fin J, (c.index s : ℕ) < c.length := fun s => (c.index s).isLt
  rcases q with q | q | q <;> rcases r with r | r | r <;>
    simp [wittJ, levW, Matrix.one_apply] at h ⊢
  all_goals first
    | (obtain ⟨rfl, -⟩ := h; have := hs q; omega)
    | omega

end Witt

section Frame

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J)

abbrev eW : WIdx J (nz I J) ≃ Fin I.n := widx I Fr.hJ

abbrev Bm : Matrix (Fin I.n) (Fin I.n) I.E := (Fr.B : Matrix (Fin I.n) (Fin I.n) I.E)

abbrev Bi : Matrix (Fin I.n) (Fin I.n) I.E := ((Fr.B⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)

theorem Bm_Bi : Bm Fr * Bi Fr = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem Bi_Bm : Bi Fr * Bm Fr = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

def wcE (h : Matrix (Fin I.n) (Fin I.n) I.E) : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) I.E :=
  (Bi Fr * h * Bm Fr).submatrix (eW Fr) (eW Fr)

def unwc (A : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) I.E) : Matrix (Fin I.n) (Fin I.n) I.E :=
  Bm Fr * A.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr

theorem unwc_mul (A B : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) I.E) :
    unwc Fr A * unwc Fr B = unwc Fr (A * B) := by
  unfold unwc
  rw [← submatrix_mul_equiv A B (eW Fr).symm (eW Fr).symm (eW Fr).symm]
  calc Bm Fr * A.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr * (Bm Fr * B.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr)
      = Bm Fr * A.submatrix (eW Fr).symm (eW Fr).symm * (Bi Fr * Bm Fr) * B.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Bi_Bm, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem unwc_one : unwc Fr 1 = 1 := by
  unfold unwc
  rw [submatrix_one_equiv, Matrix.mul_one, Bm_Bi]

theorem cT_eq (M : Matrix (Fin I.n) (Fin I.n) I.E) : Formalism.UG.cT (starRingEnd I.E) M = Mᴴ := by
  ext i j; rfl

abbrev Gm : Matrix (Fin I.n) (Fin I.n) I.E := (Bm Fr)ᴴ * I.J * Bm Fr

theorem Gm_sub : (Gm Fr).submatrix (eW Fr) (eW Fr) = wittJ (J := J) Fr.J0 := by
  ext r s
  have := Fr.gram r s
  rw [cT_eq] at this
  exact this

end Frame

section Flag

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

end Flag

end PI.IwaMeasEx.PD

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.NatSmulMulEq
section
noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

abbrev sg : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

abbrev Jf : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def Bx (N : ℕ) : Set (Af I.F) := (fun u => algebraMap I.F (Af I.F) ((N : I.F)⁻¹) * u) '' Ohat I.F

theorem isCompact_Bx (N : ℕ) : IsCompact (Bx I N) :=
  isCompact_Ohat.image (continuous_const.mul continuous_id)

theorem mem_Bx {N : ℕ} (hN : 0 < N) {a : Af I.F} (ha : N • a ∈ Ohat I.F) : a ∈ Bx I N := by
  refine ⟨N • a, ha, ?_⟩
  have hN0 : (N : I.F) ≠ 0 := by exact_mod_cast hN.ne'
  simp only
  rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, inv_mul_cancel₀ hN0,
    map_one, one_mul]

def Cset (N : ℕ) : Set (Co I × Co I) :=
  {p | (∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N) ∧
    matOf I p.1 * matOf I p.2 = 1 ∧ matOf I p.2 * matOf I p.1 = 1 ∧
    Formalism.UG.cT (sg I) (matOf I p.1) * Jf I * matOf I p.1 = Jf I ∧
    (∀ l ∈ I.L, matOf I p.1 *ᵥ inclV (F := I.F) l ∈ I.Lf) ∧
    (∀ l ∈ I.L, matOf I p.2 *ᵥ inclV (F := I.F) l ∈ I.Lf)}

def psi (N : ℕ) (p : Cset I N) : I.Gf :=
  ⟨⟨matOf I p.1.1, matOf I p.1.2, p.2.2.1, p.2.2.2.1⟩, p.2.2.2.2.1⟩

end Cpt

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

end Cpt

end PI.IwaMeasEx.Wau

end
end

