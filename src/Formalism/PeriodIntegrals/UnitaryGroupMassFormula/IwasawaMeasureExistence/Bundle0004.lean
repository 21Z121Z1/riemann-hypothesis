import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdelesExt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.Bundle0003

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ContinuousProjFInv
section
noncomputable section

namespace PI.IwaMeasEx.AfT

open NumberField Matrix Topology Filter
open scoped TensorProduct
open Formalism.MainNotions.S Formalism.L2.S.S7.WittLeviSubgroups

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

end Alg

section Top

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T1Space R] {n : ℕ}

variable {X : Type} [TopologicalSpace X] (m : X → GL (Fin n) R)
  (hm : Continuous fun x => (m x : Matrix (Fin n) (Fin n) R))
  (hmi : Continuous fun x => (((m x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R))
include hm hmi

variable {ι : Type} [Fintype ι] (b : ι → (Fin n → R)) (lev : ι → ℕ) (e : ι ≃ Fin n)
  (P Q : Matrix (Fin n) (Fin n) R) (hQP : Q * P = 1) (hPQ : P * Q = 1) (hb : ∀ r i, b r i = P i (e r))
include hQP hPQ hb

end Top

variable (I : AutInst)

variable {I} {J : ℕ} (Fr : WittFrame I J)

def frF : Matrix (Fin I.n) (Fin I.n) (AEf I) :=
  (Fr.B : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))

def frFi : Matrix (Fin I.n) (Fin I.n) (AEf I) :=
  ((Fr.B⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))

theorem frFi_mul : frFi Fr * frF Fr = 1 := by
  rw [frFi, frF, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem frF_mul : frF Fr * frFi Fr = 1 := by
  rw [frFi, frF, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

def frVi (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  ((Fr.B⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v

theorem frVi_mul (v : InfinitePlace I.F) : frVi Fr v * Fr.frV v = 1 := by
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  rw [frVi, WittFrame.frV, Matrix.mul_assoc, ← Matrix.mul_assoc (I.P v), Matrix.mul_nonsing_inv _ hP,
    Matrix.one_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem frV_mul (v : InfinitePlace I.F) : Fr.frV v * frVi Fr v = 1 := by
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  rw [frVi, WittFrame.frV, Matrix.mul_assoc, ← Matrix.mul_assoc ((Fr.B : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)),
    ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.nonsing_inv_mul _ hP]

variable (c : Composition J)

def parA : Subgroup I.GA :=
  (parGL Fr.colF (levW c)).comap (projF I) ⊓ ⨅ v, (parGL (Fr.colV v) (levW c)).comap (projV I v)

end PI.IwaMeasEx.AfT
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicDecomposition
section
noncomputable section

namespace PI.IwaMeasEx.PD

open Matrix NumberField Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
open scoped TensorProduct

section Maps

variable {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {ι : Type} [Fintype ι] [DecidableEq ι]
  (lev : ι → ℕ) {T : Matrix ι ι R}

end Maps

section Pt

variable {I : AutInst}

theorem sigR_inclE (x : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) x) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star x) := by
  show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F))) (x ⊗ₜ[I.F] (1 : Af I.F)) = star x ⊗ₜ[I.F] (1 : Af I.F)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem cT_map (M : Matrix (Fin I.n) (Fin I.n) I.E) :
    Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (M.map (Formalism.UG.inclE (F := I.F) (Af I.F))) =
      Mᴴ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  ext i j
  simp only [Formalism.UG.cT, transpose_apply, map_apply, conjTranspose_apply]
  exact sigR_inclE (M j i)

def ptF (h : GL (Fin I.n) I.E) (hh : (h : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * h = I.J) : I.Gf :=
  ⟨Units.map (RingHom.mapMatrix (Formalism.UG.inclE (F := I.F) (Af I.F))).toMonoidHom h, by
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) ((h : Matrix (Fin I.n) (Fin I.n) I.E).map
        (Formalism.UG.inclE (F := I.F) (Af I.F))) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        (h : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) =
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rw [cT_map, ← Matrix.map_mul, ← Matrix.map_mul, hh]⟩

theorem semiconj_phi (v : InfinitePlace I.F) : Function.Semiconj (I.φ v) star star := fun a => by
  rw [I.cm.cmUnram.2.1 (I.φ v) a]
  rfl

def ptV (h : GL (Fin I.n) I.E) (hh : (h : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * h = I.J)
    (v : InfinitePlace I.F) : Formalism.REAL.UJ (I.ε v) :=
  ⟨⟨(I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
    (I.P v)⁻¹ * ((h⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v, by
      calc (I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v *
            ((I.P v)⁻¹ * ((h⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
          = (I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * (I.P v * (I.P v)⁻¹) *
            ((h⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [rrg_P_mul_inv, Matrix.mul_one, Matrix.mul_assoc (I.P v)⁻¹, ← Matrix.map_mul, ← Units.val_mul,
              mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, rrg_P_inv_mul], by
      calc (I.P v)⁻¹ * ((h⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v *
            ((I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
          = (I.P v)⁻¹ * ((h⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * (I.P v * (I.P v)⁻¹) *
            (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [rrg_P_mul_inv, Matrix.mul_one, Matrix.mul_assoc (I.P v)⁻¹, ← Matrix.map_mul, ← Units.val_mul,
              inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, rrg_P_inv_mul]⟩, by
    show ((I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)ᴴ * Formalism.REAL.Jm (I.ε v) *
      ((I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) = Formalism.REAL.Jm (I.ε v)
    have hJm : Formalism.REAL.Jm (I.ε v) = (I.P v)ᴴ * I.J.map (I.φ v) * I.P v := (I.P_spec v).symm
    have hc : ((h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ =
        ((h : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ).map (I.φ v) := (conjTranspose_map _ (semiconj_phi v)).symm
    have e1 : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
      rw [← conjTranspose_mul, rrg_P_mul_inv, conjTranspose_one]
    calc ((I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)ᴴ * Formalism.REAL.Jm (I.ε v) *
          ((I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
        = (I.P v)ᴴ * ((h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * (((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) *
            I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
          rw [hJm]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (I.P v)ᴴ * (((h : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * h).map (I.φ v)) * I.P v := by
          rw [e1, rrg_P_mul_inv, hc]; simp only [Matrix.map_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (I.ε v) := by rw [hh, hJm]⟩

def ptOf (h : GL (Fin I.n) I.E) (hh : (h : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * h = I.J) : I.GA :=
  (fun v => ptV h hh v, ptF h hh)

end Pt

section Dec

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

def glOf (A Ai : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) I.E) (h1 : A * Ai = 1) (h2 : Ai * A = 1) :
    GL (Fin I.n) I.E :=
  ⟨unwc Fr A, unwc Fr Ai, by rw [unwc_mul, h1, unwc_one], by rw [unwc_mul, h2, unwc_one]⟩

end Dec

end PI.IwaMeasEx.PD

namespace PI.IwaMeasEx.Sk

open Formalism.L2.S.S7.DensDefs PI.IwaMeasEx.PD

end PI.IwaMeasEx.Sk

end
end

