import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle0005
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0021
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
import Formalism.PeriodIntegrals.Bundle0015

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomFinal
section
set_option linter.unusedVariables false

open MeasureTheory

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge

theorem quotRightInv' (hI : PI.QuotInv) (hU : PI.QuotSetU) : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv := by
  intro k r z μG μS νq hz hT hG hS hq κ hκ F hF hFS
  obtain ⟨h1, h2, h3, h4, h5⟩ := hU k r z hz hT
  exact hI (2 * r + k + 1) _ _ μG μS νq ⟨h1, h2, h3, hG, hS, h4 μG hG, h5 μS hS, hq⟩ F hF hFS κ hκ

theorem quotRightInv_closed : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv := quotRightInv' quotient_invariant quotient_measure_unitary_group

theorem momNorm'_closed (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  momNorm'_of D large₂ C' Cl Cg cb Cu cT CT C0 Cn hBS hM1 hSm quotRightInv_closed Formalism.MainNotions.S.Pv.QuotUniq.quotLeftNorm

theorem momNorm'_closed_at (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : LowKOneAt D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  momNorm'_of_at D large₂ C' Cl Cg cb Cu cT CT C0 Cn hBS hM1 hSm quotRightInv_closed Formalism.MainNotions.S.Pv.QuotUniq.quotLeftNorm

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ)

def BesselSchurF' : Prop :=
  ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => BesselSchur' (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn

theorem momF'_of_schur (hBS : BesselSchurF' Fm Cg cb Cu cT CT C0) (hM1 : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomF' Fm Cg cb Cu cT CT C0 :=
  fun Cn => Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i h => momNorm'_closed _ _ _ _ _ _ _ _ _ _ _ h hM1 hSm) (hBS Cn)

theorem momF'_of_schur_at (hBS : BesselSchurF' Fm Cg cb Cu cT CT C0)
    (hM1 : ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => LowKOneAt (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomF' Fm Cg cb Cu cT CT C0 :=
  fun Cn => Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i h => momNorm'_closed_at _ _ _ _ _ _ _ _ _ _ _ h.1 h.2 hSm)
    ((hBS Cn).and (hM1 Cn))

end Fam

end Formalism.MainNotions.S.Pv.Mom
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.ProdLeProdSubOneLe
section
set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds

section Perm

variable {d : ℕ} (c : Composition d)

def bsig (i : Fin d) : Fin d :=
  ⟨c.sizeUpTo (c.index i) + c.sizeUpTo ((c.index i : ℕ) + 1) - 1 - i, by
    have a1 := c.sizeUpTo_index_le i
    have a2 := c.lt_sizeUpTo_index_succ i
    simp only [Fin.val_succ] at a2
    have a3 : c.sizeUpTo ((c.index i : ℕ) + 1) ≤ d := c.sizeUpTo_le _
    omega⟩

theorem bsig_val (i : Fin d) :
    ((bsig c i : Fin d) : ℕ) = c.sizeUpTo (c.index i) + c.sizeUpTo ((c.index i : ℕ) + 1) - 1 - i := rfl

theorem bsig_index (i : Fin d) : c.index (bsig c i) = c.index i := by
  have a1 := c.sizeUpTo_index_le i
  have a2 := c.lt_sizeUpTo_index_succ i
  simp only [Fin.val_succ] at a2
  apply index_unique c (bsig c i) (c.index i)
  · rw [bsig_val]; omega
  · rw [bsig_val]; omega

theorem bsig_bsig (i : Fin d) : bsig c (bsig c i) = i := by
  have a1 := c.sizeUpTo_index_le i
  have a2 := c.lt_sizeUpTo_index_succ i
  simp only [Fin.val_succ] at a2
  apply Fin.ext
  rw [bsig_val, bsig_index, bsig_val]
  omega

def bperm : Equiv.Perm (Fin d) := Function.Involutive.toPerm (bsig c) (bsig_bsig c)

end Perm

section Minor

variable {E : Type} [Field E] {d : ℕ}

end Minor

theorem max_mul_le {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) : max 1 (x * z) ≤ max 1 x * max 1 z := by
  have h1 : (1 : ℝ) ≤ max 1 x := le_max_left _ _
  have h2 : (1 : ℝ) ≤ max 1 z := le_max_left _ _
  apply max_le
  · nlinarith
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) hz (by linarith)

def pre (y : ℕ → ℝ) (a : ℕ) : ℝ := ∏ i ∈ range (a + 1), y i

section Ends

variable {E : Type} [Field E] {d : ℕ}

def bEnd (p : Point E d) (a : Fin (toComp p).length) : E :=
  leadMinorE (ptMat p) ((toComp p).sizeUpTo ((a : ℕ) + 1))

def yN (τ : E →+* ℂ) (p : Point E d) (i : ℕ) : ℝ :=
  if h : i < (toComp p).length then ‖τ (toT p ⟨i, h⟩)‖ ^ (toComp p).blocksFun ⟨i, h⟩ else 1

end Ends

end Formalism.MainNotions.S.Pv.HH

end
end

