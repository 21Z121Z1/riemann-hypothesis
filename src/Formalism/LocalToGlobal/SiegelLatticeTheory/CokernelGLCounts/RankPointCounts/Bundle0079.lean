import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0076
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0077
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfD
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0038
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0037
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0062
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0042
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueConvA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataColumns
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0055
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0078

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerRight
section
noncomputable section

open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Corner

variable {K : Type*} [CommRing K] (cj : K →+* K) {r : ℕ}

def cornerM (g : K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then g else 0

theorem corner_left (L : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hcj : cj 1 = 1) (g : K) : L * cornerM (r := r) g * cjT cj L = cornerM g := by
  ext i j
  simp only [Matrix.mul_apply, cornerM, Matrix.of_apply, cjT, Matrix.transpose_apply, Matrix.map_apply]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, if_pos rfl]
    rw [hL i, hL j]
    by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;> simp [hi, hj, hcj]
  · intro b _ hb; simp [hb]
  · simp

theorem corner_right (P : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0)
    (hcj : cj 1 = 1) (g : K) : cjT cj P * cornerM (r := r) g * P = cornerM g := by
  ext i j
  simp only [Matrix.mul_apply, cornerM, Matrix.of_apply, cjT, Matrix.transpose_apply, Matrix.map_apply]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hP i]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hP j]
  by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;> simp [hi, hj, hcj]

end Corner

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

theorem gDiag_corner (p : PlF D) (T : D.host.E) :
    gDiag δ M p T = cornerM (frFac δ p (Fin.last D.R.rS) * (M p).L.cj (frFac δ p (Fin.last D.R.rS)) *
      (D.s.atP p).ιE (-T)) := by
  ext a b
  simp only [gDiag, cornerM, Matrix.of_apply]
  by_cases h : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
  · rw [if_pos h, if_pos h, h.1, h.2]
  · rw [if_neg h, if_neg h, map_zero, mul_zero]

theorem gaCong_L (hA : ∀ q, Agree δ M q) (p : PlF D) (hs : (M p).split = none) (T T' : D.host.E) (Z Z' : MatZ D)
    (L P : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)
    (hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0)
    (hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0)
    (hLO : ∀ i j, L i j ∈ (M p).L.O) (hPO : ∀ i j, P i j ∈ (M p).L.O)
    (hLu : ∃ y ∈ (M p).L.O, L.det * y = 1) (hPu : ∃ y ∈ (M p).L.O, P.det * y = 1)
    (hX : ZhatLoc M δ p Z' = L * ZhatLoc M δ p Z * P) :
    ∃ A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
      GaPlus M δ p T T' Z' = (A.map (M p).L.cj).transpose * GaPlus M δ p T T' Z * A := by
  set cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep := ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) with hcj
  have hinv : ∀ x, cj (cj x) = x := fun x => (M p).L.cj_cj x
  refine ⟨Matrix.fromBlocks (cjT cj L) 0 0 P, ?_, ?_, ?_⟩
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O (M p).L _ (hLO j i)
    · exact (M p).L.O.zero_mem
    · exact (M p).L.O.zero_mem
    · exact hPO i j
  · obtain ⟨y, hy, hLy⟩ := hLu
    obtain ⟨z, hz, hPz⟩ := hPu
    refine ⟨cj y * z, (M p).L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O (M p).L _ hy) hz, ?_⟩
    rw [Matrix.det_fromBlocks_zero₂₁]
    have hd : (cjT cj L).det = cj L.det := by
      unfold cjT; rw [Matrix.det_transpose]; exact (RingHom.map_det cj L).symm
    rw [hd]
    calc cj L.det * P.det * (cj y * z) = cj (L.det * y) * (P.det * z) := by rw [map_mul]; ring
      _ = 1 := by rw [hLy, hPz, map_one, one_mul]
  · have e1 : GaPlus M δ p T T' Z' = GaLoc M δ p T T' Z' := by unfold GaPlus; rw [hs]
    have e2 : GaPlus M δ p T T' Z = GaLoc M δ p T T' Z := by unfold GaPlus; rw [hs]
    rw [e1, e2, gaLoc_blocks δ M hA, gaLoc_blocks δ M hA]
    show _ = cjT cj _ * _ * _
    refine (block_cong cj hinv _ _ _ _ _ _ _ _ ?_ ?_ ?_).symm
    · rw [cjT_cjT cj hinv, gDiag_corner]
      exact corner_left cj L hL (map_one cj) _
    · rw [cjT_cjT cj hinv, hX]
    · rw [gDiag_corner]
      exact corner_right cj P hP (map_one cj) _

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIC
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BetaI

theorem xi_inv_last (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (i : Fin D.R.rS) :
    (admXi D Λ F F')⁻¹ (Fin.last D.R.rS) i.castSucc = 0 := by
  obtain ⟨h1, h2⟩ := admissibility_witness_unitriangular Λ F F'
  have hbt : (admXi D Λ F F').BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : (admXi D Λ F F').det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [h2]
  haveI : Invertible (admXi D Λ F F') := Matrix.invertibleOfIsUnitDet _ (by rw [hdet]; exact isUnit_one)
  exact Matrix.blockTriangular_inv_of_blockTriangular hbt (Fin.castSucc_lt_last i)

theorem frameAct_mem {T' : D.host.E} (G : LFlag (VS D) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (i : Fin D.R.rS)
    (h : ξ (Fin.last D.R.rS) i.castSucc = 0) : frameAct (frame G) ξ i.castSucc ∈ Xsp G := by
  show ∑ a, ((ξ a i.castSucc : 𝓞 D.host.E) : D.host.E) • frame G a ∈ Xsp G
  rw [Fin.sum_univ_castSucc, h]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_) (by simp)
  rw [frame_csG]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem tf' (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (b : Fin (D.R.rS + 1)) :
    (tLoc Zd p γ).f' b = (TermLoc.sgnP' D p b * frFac Zd.δ p b) •
      baseChange₂ D p (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹ b) := rfl

theorem bcP_perp_f' (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {m : (VS D).V}
    (hm : m ∈ orth (VS D) (Xsp (repF γ))) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f') := by
  show ∀ w ∈ (locH Zd p).X (tLoc Zd p γ).f', (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [tf', LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _
        (frameAct_mem _ _ i (xi_inv_last γ.lam (lf D F0) (repF γ) i)), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

end BetaI

variable (u u' F0 what₂)

def PinB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ (p : PlF D) (m : (VS D).V) (hm : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
        (hm₂ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂))),
        m ∈ orth (VS D) (Xsp (repF γ)) →
        φ' p ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩) =
          (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩

variable {u u' F0 what₂}

theorem lsetB_of (hP : PinB Zd u u' F0 what₂) : LsetB Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO p m hm hmo
  have hloc := hB.2.2.2.1.2 p
  have hL' := hloc.2.2.2.1
  have hmp := bcP_perp_f' Zd p γ hmo
  have hXmap := BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have hmo₂ : β₀ m ∈ orth (VS D) (Xsp (liftF F'₂)) := by
    rw [← hXmap, Formalism.L2.SG.Pf.orth_map_sat β₀ hiso]
    exact Submodule.mem_map_of_mem hmo
  have hmp₂ := baseChangeAt_perp' Zd p F'₂ hmo₂
  have hin : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hmp⟩ ∈
      (locH Zd p).Lset (tLoc Zd p γ).abelian₂ (tLoc Zd p γ).f' := ⟨⟨_, hmp⟩, baseChange_mem_localLattice Zd hm p, rfl⟩
  obtain ⟨x, hxΛ, hxe⟩ := hL'.subset ⟨_, hin, rfl⟩
  rw [hP γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO p m hmp hmp₂ hmo] at hxe
  refine ⟨(x : Vp D p), hxΛ, ?_⟩
  have := (Submodule.Quotient.eq _).1 hxe.symm
  simpa using this

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExistB
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}

theorem LprExistB_equiv {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ) :
    Equivalence (Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ) :=
  Formalism.L2.SG.Corank.scalarEquiv_of_G scalar_equiv_general u u' F0 Λ hΛ

theorem LprExistB_repFree : Formalism.L2.SG.Corank.ScalarRepFree D u u' :=
  scalar_rep_free D u u'

theorem scal_move {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ)
    (x1 x2 y1 y2 : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0})
    (h1 : TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') x1.1 = TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') y1.1)
    (h2 : TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') x2.1 = TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') y2.1)
    (a : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ x1 x2) : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ y1 y2 := by
  have hEq := LprExistB_equiv (u := u) (u' := u') hΛ
  have hRF := LprExistB_repFree (D := D) (u := u) (u' := u') F0 Λ hΛ
  have r2 := (Formalism.L2.SG.Pf.double_coset_equivalence Λ (lf D F0) (PD D Λ (lf D F0) u') x2.1 y2.1).1 h2
  have a2 : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ x1 y2 := hRF x1 x2 y2 r2 a
  have r1 := (Formalism.L2.SG.Pf.double_coset_equivalence Λ (lf D F0) (PD D Λ (lf D F0) u') x1.1 y1.1).1 h1
  have a3 : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ y2 y1 := hRF y2 x1 y1 r1 (hEq.symm a2)
  exact hEq.symm a3

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
section
namespace Formalism.L2.SG.Pf

theorem formRelC_holds : Formalism.L2.SG.Pf.FormRel.FormRelC :=
  formRelC_of (fun D X Y u u' => Formalism.L2.SG.Pf.RowForm.RealDecompL.realDecompC_of X Y u u'
    (Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')) Formalism.L2.SG.Pf.RelChar.relCharC_holds

theorem formNGC_holds : Formalism.L2.SG.NGVanish.FormNGC := formNGC_of_rel formRelC_holds

theorem formGC_holds : Formalism.L2.SG.Pf.MainEqVanish.FormGC := formGC_of_rel formRelC_holds

end Formalism.L2.SG.Pf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrFacInvMul
section
noncomputable section

open scoped Classical Matrix

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Key

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem cj_iota (x : D.host.E) :
    (Z.M p).L.cj ((D.s.atP p).ιE x) = (D.s.atP p).ιE (star x) := by
  rw [Z.hcj p, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, ← (D.s.atP p).cj_ιE]

theorem frFac_inv_mul (a : Fin (D.R.rS + 1)) : Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a = 1 :=
  Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)

theorem frFac_mul_inv (a : Fin (D.R.rS + 1)) : frFac Z.δ p a * Ring.inverse (frFac Z.δ p a) = 1 :=
  Ring.mul_inverse_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)

theorem key_rel (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hrel : Nᴴ * Z₂ = Z₁ * M) :
    ((locU Z p N).map (Z.M p).L.cj)ᵀ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * locU Z p M := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, locU_apply,
    Formalism.L2.SG.CntLocal.ZhatLoc, Matrix.of_apply]
  have hL : ∀ c, (Z.M p).L.cj (Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (N c a) * frFac Z.δ p a) *
      (frFac Z.δ p b * (Z.M p).L.cj (frFac Z.δ p c) * (D.s.atP p).ιE (Z₂ c b)) =
      (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (star (N c a) * Z₂ c b) := by
    intro c
    rw [map_mul, map_mul, cj_iota Z p, map_mul (D.s.atP p).ιE]
    have h1 : (Z.M p).L.cj (Ring.inverse (frFac Z.δ p c)) * (Z.M p).L.cj (frFac Z.δ p c) = 1 := by
      rw [← map_mul, frFac_inv_mul, map_one]
    calc _ = ((Z.M p).L.cj (Ring.inverse (frFac Z.δ p c)) * (Z.M p).L.cj (frFac Z.δ p c)) *
          ((Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b *
            ((D.s.atP p).ιE (star (N c a)) * (D.s.atP p).ιE (Z₂ c b))) := by ring
      _ = _ := by rw [h1, one_mul]
  have hR : ∀ c, frFac Z.δ p c * (Z.M p).L.cj (frFac Z.δ p a) * (D.s.atP p).ιE (Z₁ a c) *
      (Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (M c b) * frFac Z.δ p b) =
      (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (Z₁ a c * M c b) := by
    intro c
    rw [map_mul (D.s.atP p).ιE]
    calc _ = (frFac Z.δ p c * Ring.inverse (frFac Z.δ p c)) *
          ((Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p b *
            ((D.s.atP p).ιE (Z₁ a c) * (D.s.atP p).ιE (M c b))) := by ring
      _ = _ := by rw [frFac_mul_inv, one_mul]
  rw [Finset.sum_congr rfl (fun c _ => hL c), Finset.sum_congr rfl (fun c _ => hR c), ← Finset.mul_sum,
    ← Finset.mul_sum, ← map_sum, ← map_sum]
  congr 2
  have := congrFun (congrFun hrel a) b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at this
  exact this

end Key

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobalCountOfSplitMode
section
namespace Formalism.L2.SG.LsDatumA

def ModSide0G : Prop := Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n true)

def ModSideUG : Prop := Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n true)

theorem modSide0_mode (h0G : ModSide0G) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n M.split.isSome) := by
  intro F _ _ _ E _ _ _ _ M hM r n
  cases h : M.split.isSome
  · exact modSide0L F E M hM r n
  · exact h0G F E M hM r n

theorem modSideU_mode (hUG : ModSideUG) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n M.split.isSome) := by
  intro F _ _ _ E _ _ _ _ M hM r n
  cases h : M.split.isSome
  · exact modSideUL F E M hM r n
  · exact hUG F E M hM r n

theorem globalCount_of_split_mode (D : Formalism.BasicNotions.D7) (h0G : ModSide0G) (hUG : ModSideUG) : Formalism.MainNotions.ThinScalesBound.T2 D :=
  globalCount_of_module D (fun F _ _ _ E _ _ _ _ M hM => modSide0_mode h0G F E M hM _ _)
    (fun F _ _ _ E _ _ _ _ M hM => modSideU_mode hUG F E M hM _ _)

end Formalism.L2.SG.LsDatumA
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXColumns
section
namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.L2.SG.TypedSets

theorem inColumnsAt_holds :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn),
      InColumnsAt X hb hK FdN FdN' u u' X0 L A :=
  massDataColumns_of' Formalism.L2.SG.Closed.AdBridgeIso_holds Formalism.L2.SG.Closed.AdBridgeGF_holds
    Formalism.L2.SG.Closed.AdBridgeK_holds
    (fun X u hK => Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu X u hK
      (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) (Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK))
    (fun X u hK => Formalism.L2.SG.Closed.ClassFin_holds X u hK)
    (fun I hb => ⟨Formalism.L2.SG.Pf.Meas.eFin I hb, fun _ => rfl⟩)
    (fun X => Formalism.L2.SG.Pf.level_subgroup_compact_open X)
    Formalism.L2.SG.Closed.AutKCompact_holds
    Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion
    (fun X u => Formalism.L2.SG.Pf.hinf_compact X u)

end Formalism.L2.SG.Pf.MassDataX
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRecPos
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

theorem massH_pos {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    0 < massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) := by
  classical
  have hC := Formalism.L2.SG.Pf.MassDataX.classFinite_holds X u
  have hS := MassDataMassesW.stabFinite_of Formalism.L2.SG.Pf.MassDataX.hinfCompact_holds
    Formalism.L2.SG.Pf.MassDataX.kCompactOpen_holds X u
  show 0 < massCl (MassDataMassesW.GamH X u) (MassDataMassesW.KH X u)
  unfold massCl
  haveI := hC
  letI : Fintype (DoubleCoset.Quotient (G := ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (MassDataMassesW.GamH X u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (MassDataMassesW.KH X u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))) :=
    Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  apply Finset.sum_pos
  · intro c _
    haveI := hS (Quotient.out c)
    apply inv_pos.mpr
    exact_mod_cast Nat.card_pos
  · exact Finset.univ_nonempty_iff.mpr ⟨Quot.mk _ 1⟩

theorem finrank_Vpi_pos {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : 0 < Module.finrank ℂ (X.Vpi u) := by
  classical
  have hx : ∀ v, ∃ y : X.Vloc u v, y ≠ 0 := fun v => by
    haveI := (X.piLoc_type u v).1
    exact exists_ne 0
  choose x hx using hx
  have hne : X.tensU u x ≠ 0 := by
    intro h0
    have h := X.tensU_inner u x x
    rw [h0, inner_zero_left] at h
    exact (Finset.prod_ne_zero_iff.mpr fun v _ => inner_self_ne_zero.mpr (hx v)) h.symm
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UUEEqAsp
section
noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UUE_eq_Asp {D : D7} {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : Submodule.IsLattice D.host.E Λ) (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (hL : IsLift Λ F) (hL' : IsLift Λ F') : UUE Λ F F' = Asp F.fl F'.fl := by
  refine le_antisymm ?_ ?_
  · have hX' : F'.fl.X ≤ Asp F.fl F'.fl := by rw [← Asp_symm]; exact X_le_Asp F'.fl F.fl
    have hz' : F'.fl.z ∈ Asp F.fl F'.fl := by rw [← Asp_symm]; exact z_mem_Asp F'.fl F.fl
    have key : UU Λ F F' ≤ (Asp F.fl F'.fl).restrictScalars (𝓞 D.host.E) := by
      unfold UU
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro y hy
        exact X_le_Asp F.fl F'.fl (Submodule.mem_inf.1 hy).2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hL.2]
        exact z_mem_Asp F.fl F'.fl
      · intro y hy
        exact hX' (Submodule.mem_inf.1 hy).2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hL'.2]
        exact hz'
    unfold UUE spanE
    rw [Submodule.span_le]
    intro x hx
    exact key hx
  · rw [Asp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL' i

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

