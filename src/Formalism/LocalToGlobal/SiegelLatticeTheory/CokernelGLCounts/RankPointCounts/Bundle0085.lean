import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LastCoordMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0045
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0083

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BwdTermOfGx
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} {Zd : LocDat D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
  {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}

theorem bwdTerm'_of_gx (hGX : GenXiRev Zd u' F0) : BwdTerm' Zd u u' F0 what₂ :=
  bwdTerm'_of' (btOK_holds Zd) hGX

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarPinOm
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

variable (u u' F0 what₂)

theorem pinOm_cancel {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {a k d₁ d₂ : R} {A B C : W}
    (ha : IsUnit a) (hk : IsUnit k) (hd : IsUnit d₂) (h1 : (a * d₂ * k) • A = (a * d₁ * k) • B)
    (h2 : d₂ • C = d₁ • B) : A = C := by
  have key : (a * d₂ * k) • A = (a * d₂ * k) • C := by
    rw [h1]
    calc (a * d₁ * k) • B = (a * k) • (d₁ • B) := by rw [smul_smul]; congr 1; ring
      _ = (a * k) • (d₂ • C) := by rw [h2]
      _ = (a * d₂ * k) • C := by rw [smul_smul]; congr 1; ring
  obtain ⟨v, hv⟩ := (ha.mul hd).mul hk
  have := congrArg (fun w => ((v⁻¹ : Rˣ) : R) • w) key
  simp only [← hv, smul_smul, Units.inv_mul, one_smul] at this
  exact this

set_option maxHeartbeats 4000000 in

theorem pinOm_holds : PinOm Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hβ hfr hW hO p hm hm₂
  obtain ⟨hC, hCtx, hS, -, -, hTH, hPD, hGv⟩ := hB
  obtain ⟨hZd, -, -⟩ := starMinors_holds u u' F0 what₂ γ Z hCtx
  have hT2 := hS.2.1 p
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  obtain ⟨K, hK⟩ : ∃ K : (D.s.atP p).Ep, K = (Zd.M p).L.cj (∏ j ∈ Finset.univ.erase (Fin.last D.R.rS), sF' Zd p j) *
      ∏ j, sF Zd p j := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : (D.s.atP p).Ep, P = (∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sF Zd p (Fin.castLE le_rfl i))) *
      (∏ i : Fin (D.R.rS + 1), sF' Zd p (Fin.castLE le_rfl i)) := ⟨_, rfl⟩
  have ho1 : (locH Zd p).om (tLoc Zd p γ).f (tLoc Zd p γ).f' = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame (repF γ))) := by
    have e := om_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹)
      (sF Zd p) (sF' Zd p)
    rw [Gom_frameAct (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hK] at e
    exact e
  have ho2 : (locH Zd p).om (tLoc Zd p γ).f (locF' Zd p F'₂) = K • baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) := by
    have e := om_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p)
    rw [← hK] at e
    exact e
  have hd1 : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) =
      P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1)) := by
    have e := dl_loc Zd p (frame (lf D F0)) (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹)
      (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl
    rw [GDl_frameAct_top (frame (lf D F0)) (frame (repF γ)) _ hξ1 hξ2, ← hP] at e
    exact e
  have hd2 : (locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1) =
      P * (D.s.atP p).ιE (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)) := by
    have e := dl_loc Zd p (frame (lf D F0)) (frame F'₂) (sF Zd p) (sF' Zd p) (D.R.rS + 1) le_rfl
    rw [← hP] at e
    exact e
  have hid := hT2.2.2.2.1
  have hs := hid.2.2.2.2.1
  dsimp only at hs
  rw [ho1, ho2, hd1, hd2] at hs
  have hω₂ : baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) :=
    baseChangeAt_perp' Zd p F'₂ (Gom_orth (lf D F0) F'₂)
  have h1 := hs (K • ⟨_, hm⟩) (K • ⟨_, hω₂⟩) rfl rfl
  have e1 := ((locH Zd p).mkW (tLoc Zd p γ).f').map_smul K ⟨_, hm⟩
  have e2 := ((locH Zd p).mkW (locF' Zd p F'₂)).map_smul K ⟨_, hω₂⟩
  have e3 := ((φ' p).toLinearMap).map_smul K ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hm⟩)
  rw [e1, e2, e3, smul_smul, smul_smul] at h1
  have hD2 : GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1) ≠ 0 := by
    rw [GDl_top']
    have e : GZ (frame (lf D F0)) (frame F'₂) = Z := hS.1
    rw [e]; exact hZd
  have hOp : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) •
        baseChange₂ D p (β₀ (Gom (frame (lf D F0)) (frame (repF γ)))) -
      (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) •
        baseChange₂ D p (Gom (frame (lf D F0)) (frame F'₂)) ∈ (locH Zd p).X (locF' Zd p F'₂) := by
    have := bcP_X' Zd p (liftF F'₂) hO
    rw [map_sub, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂] at this
    exact this
  have hcls : (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1))) •
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hm₂⟩ =
      (D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1))) •
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hω₂⟩ := by
    rw [← LinearMap.map_smul, ← LinearMap.map_smul]
    apply (Submodule.Quotient.eq _).2
    exact hOp
  rw [map_mul, map_mul, cj_iota (Zd.hcj p), cj_iota (Zd.hcj p)] at h1
  have hPu : IsUnit P := by
    rw [hP]
    exact (IsUnit.prod_univ_iff.2 fun i => (isUnit_sF Zd p _).map _).mul
      (IsUnit.prod_univ_iff.2 fun i => isUnit_sF' Zd p _)
  have hKu : IsUnit K := by
    rw [hK]
    exact ((IsUnit.prod_iff.2 fun j _ => isUnit_sF' Zd p j).map _).mul
      (IsUnit.prod_univ_iff.2 fun j => isUnit_sF Zd p j)
  have hDu : IsUnit ((D.s.atP p).ιE (star (GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)))) :=
    (isUnit_iff_ne_zero.2 (star_ne_zero.2 hD2)).map _
  exact pinOm_cancel (hPu.map _) hKu hDu h1 hcls

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GaCongG
section
noncomputable section

open Matrix ValuativeRel
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

set_option maxHeartbeats 1600000

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

theorem e_alg (p : PlF D) (g : Loc.SplitG (M p).L) (x : (D.s.atP p).Fp) :
    g.e (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep x) = (x, x) := by
  rw [AlgEquiv.commutes]; rfl

theorem gaCong_G (hA : ∀ q, Agree δ M q) (p : PlF D) (g : Loc.SplitG (M p).L) (hs : (M p).split = some g)
    (T T' : D.host.E) (Tf Tf' : (D.s.atP p).Fp) (Z Z' : MatZ D)
    (L P : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)
    (hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0)
    (hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0)
    (hLR : ∀ i j, L i j ∈ (M p).R) (hPR : ∀ i j, P i j ∈ (M p).R)
    (hLu : ∃ y ∈ (M p).R, L.det * y = 1) (hPu : ∃ y ∈ (M p).R, P.det * y = 1)
    (hX : Loc.HermSp.ZZplusOf (M p) (ZhatLoc M δ p Z') Tf Tf' =
      L * Loc.HermSp.ZZplusOf (M p) (ZhatLoc M δ p Z) Tf Tf' * P) :
    ∃ A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
      GaPlus M δ p T T' Z' = (A.map (M p).L.cj).transpose * GaPlus M δ p T T' Z * A := by
  set cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep := ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) with hcj
  have hinv : ∀ x, cj (cj x) = x := fun x => (M p).L.cj_cj x
  set Mm := mmG (M p) g L P with hMm
  set U := uuG (M p) g L P with hU
  set qi : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) with hqi
  set A0 : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    Matrix.fromBlocks 1 (-qi • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) 0
      (qi • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) with hA0
  set B : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    Matrix.fromBlocks Mm (qi • (U - Mm)) 0 U with hB
  set At : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    Matrix.fromBlocks Mm 0 0 U with hAt
  have hplus : ∀ Y : MatZ D, GaPlus M δ p T T' Y = cjT cj A0 * GaLoc M δ p T T' Y * A0 := by
    intro Y; unfold GaPlus; rw [hs]; rfl
  have hloc : GaLoc M δ p T T' Z' = cjT cj At * GaLoc M δ p T T' Z * At := by
    rw [gaLoc_blocks δ M hA, gaLoc_blocks δ M hA]
    refine (block_cong cj hinv _ _ _ _ _ _ _ _ ?_ ?_ ?_).symm
    · rw [gDiag_corner]; exact condM_G (M p) g hL hP _
    · exact condX_G (M p) g hs hL hP Tf Tf' hX
    · rw [gDiag_corner]; exact condU_G (M p) g hL hP _
  have hcomm : A0 * B = At * A0 := by
    rw [hA0, hB, hAt, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_zero] <;> module
  refine ⟨B, ?_, ?_, ?_⟩
  ·
    have hcomp : ∀ x ∈ (M p).R, (g.e x).1 ∈ 𝒪[(D.s.atP p).Fp] ∧ (g.e x).2 ∈ 𝒪[(D.s.atP p).Fp] ∧
        ∃ c : 𝒪[(D.s.atP p).Fp], (g.e x).1 - (g.e x).2 = (g.q : (D.s.atP p).Fp) * c :=
      fun x hx => Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.comp_of_mem_R hs hx
    have hq := q_ne (M p) g
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · refine Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ ?_ ?_
      · simp [hB, hMm, mmG, (hcomp _ (hPR i j)).2.1]
      · simp [hB, hMm, mmG, (hcomp _ (hLR j i)).1]
    · obtain ⟨-, -, c, hc⟩ := hcomp _ (hPR i j)
      obtain ⟨-, -, c', hc'⟩ := hcomp _ (hLR j i)
      refine Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ ?_ ?_
      · have : (g.e (B (Sum.inl i) (Sum.inr j))).1 = c := by
          simp only [hB, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul,
            map_sub, hqi, e_alg, hU, hMm, uuG, mmG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Prod.fst_mul,
            Prod.fst_sub]
          rw [hc]; field_simp
        rw [this]; exact c.2
      · have : (g.e (B (Sum.inl i) (Sum.inr j))).2 = -c' := by
          simp only [hB, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul,
            map_sub, hqi, e_alg, hU, hMm, uuG, mmG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Prod.snd_mul,
            Prod.snd_sub]
          rw [show (g.e (L j i)).2 - (g.e (L j i)).1 = -((g.e (L j i)).1 - (g.e (L j i)).2) by ring, hc']
          field_simp
        rw [this]; exact (-c').2
    · simp [hB]
    · refine Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ ?_ ?_
      · simp [hB, hU, uuG, (hcomp _ (hPR i j)).1]
      · simp [hB, hU, uuG, (hcomp _ (hLR j i)).2.1]
  ·
    obtain ⟨yL, hyL, hLy⟩ := hLu
    obtain ⟨yP, hyP, hPy⟩ := hPu
    have cL := Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.comp_of_mem_R hs hyL
    have cP := Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.comp_of_mem_R hs hyP
    refine ⟨g.e.symm ((g.e yP).2 * (g.e yP).1, (g.e yL).1 * (g.e yL).2),
      Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.mem_O_of_comp g _ (by simpa using mul_mem cP.2.1 cP.1)
        (by simpa using mul_mem cL.1 cL.2.1), ?_⟩
    rw [hB, Matrix.det_fromBlocks_zero₂₁]
    apply g.e.injective
    have d1 : (g.e Mm.det).1 = (g.e P.det).2 := by
      have := RingHom.map_det (π1 (M p) g) Mm
      rw [π1_apply] at this
      rw [this, RingHom.mapMatrix_apply, middleMatrix_map_firstComponent, ← RingHom.mapMatrix_apply, ← RingHom.map_det, π2_apply]
    have d2 : (g.e Mm.det).2 = (g.e L.det).1 := by
      have := RingHom.map_det (π2 (M p) g) Mm
      rw [π2_apply] at this
      rw [this, RingHom.mapMatrix_apply, middleMatrix_map_secondComponent, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, π1_apply]
    have d3 : (g.e U.det).1 = (g.e P.det).1 := by
      have := RingHom.map_det (π1 (M p) g) U
      rw [π1_apply] at this
      rw [this, RingHom.mapMatrix_apply, unipotentMatrix_map_firstComponent, ← RingHom.mapMatrix_apply, ← RingHom.map_det, π1_apply]
    have d4 : (g.e U.det).2 = (g.e L.det).2 := by
      have := RingHom.map_det (π2 (M p) g) U
      rw [π2_apply] at this
      rw [this, RingHom.mapMatrix_apply, unipotentMatrix_map_secondComponent, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, π2_apply]
    have eL := congrArg g.e hLy
    have eP := congrArg g.e hPy
    rw [map_mul, map_one] at eL eP
    refine Prod.ext ?_ ?_
    · simp only [map_mul, Prod.fst_mul, AlgEquiv.apply_symm_apply, map_one, Prod.fst_one, d1, d3]
      have e1 := congrArg Prod.fst eP
      have e2 := congrArg Prod.snd eP
      simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_one, Prod.snd_one] at e1 e2
      linear_combination (g.e P.det).1 * (g.e yP).1 * e2 + e1
    · simp only [map_mul, Prod.snd_mul, AlgEquiv.apply_symm_apply, map_one, Prod.snd_one, d2, d4]
      have e1 := congrArg Prod.fst eL
      have e2 := congrArg Prod.snd eL
      simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_one, Prod.snd_one] at e1 e2
      linear_combination (g.e L.det).2 * (g.e yL).2 * e1 + e2
  ·
    show GaPlus M δ p T T' Z' = cjT cj B * GaPlus M δ p T T' Z * B
    rw [hplus, hplus, hloc]
    calc cjT cj A0 * (cjT cj At * GaLoc M δ p T T' Z * At) * A0
        = cjT cj (At * A0) * GaLoc M δ p T T' Z * (At * A0) := by
          rw [cjT_mul]; simp only [Matrix.mul_assoc]
      _ = cjT cj (A0 * B) * GaLoc M δ p T T' Z * (A0 * B) := by rw [hcomm]
      _ = cjT cj B * (cjT cj A0 * GaLoc M δ p T T' Z * A0) * B := by
          rw [cjT_mul]; simp only [Matrix.mul_assoc]

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntMTranspose
section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

def IntM (X : Formalism.L2.SG.LsDatumB.MatP D p) : Prop := ∀ i j, X i j ∈ (Z.M p).L.O

def Cq (X : Formalism.L2.SG.LsDatumB.MatP D p) : Prop :=
  ∀ i j, ∃ o ∈ (Z.M p).L.O, X i j = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o

theorem intM_mul {A B : Formalism.L2.SG.LsDatumB.MatP D p} (hA : IntM Z p A) (hB : IntM Z p B) : IntM Z p (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem cq_mul_left {A X : Formalism.L2.SG.LsDatumB.MatP D p} (hA : IntM Z p A) (hX : Cq Z p g X) : Cq Z p g (A * X) := fun i j => by
  choose o ho he using hX
  refine ⟨∑ k, A i k * o k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (ho k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he k j]
  ring

theorem cq_mul_right {X B : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) (hB : IntM Z p B) : Cq Z p g (X * B) := fun i j => by
  choose o ho he using hX
  refine ⟨∑ k, o i k * B k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ho i k) (hB k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he i k]
  ring

theorem cq_neg {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) : Cq Z p g (-X) := fun i j => by
  obtain ⟨o, ho, he⟩ := hX i j
  exact ⟨-o, Subring.neg_mem _ ho, by rw [Matrix.neg_apply, he, mul_neg]⟩

theorem cq_transpose {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) : Cq Z p g Xᵀ := fun i j => hX j i

theorem cq_map_cj {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) : Cq Z p g (X.map (Z.M p).L.cj) := fun i j => by
  obtain ⟨o, ho, he⟩ := hX i j
  refine ⟨(Z.M p).L.cj o, PI.LocCntLat.GC.cj_mem_O _ ho, ?_⟩
  rw [Matrix.map_apply, he, map_mul, AlgEquiv.commutes]

theorem intM_map_cj {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : IntM Z p X) : IntM Z p (X.map (Z.M p).L.cj) := fun i j =>
  PI.LocCntLat.GC.cj_mem_O _ (hX i j)

theorem intM_transpose {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : IntM Z p X) : IntM Z p Xᵀ := fun i j => hX j i

theorem map_cj_mul (A B : Formalism.L2.SG.LsDatumB.MatP D p) : (A * B).map (Z.M p).L.cj = A.map (Z.M p).L.cj * B.map (Z.M p).L.cj := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

theorem map_cj_cj (A : Formalism.L2.SG.LsDatumB.MatP D p) : (A.map (Z.M p).L.cj).map (Z.M p).L.cj = A := by
  ext i j
  simp [(Z.M p).L.cj_cj]

theorem map_cj_one : (1 : Formalism.L2.SG.LsDatumB.MatP D p).map (Z.M p).L.cj = 1 := by
  ext i j
  simp [Matrix.one_apply, apply_ite]

theorem map_cj_inv (A : Formalism.L2.SG.LsDatumB.MatP D p) (hA : IsUnit A.det) : (A⁻¹).map (Z.M p).L.cj = (A.map (Z.M p).L.cj)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← map_cj_mul, Matrix.nonsing_inv_mul A hA, map_cj_one]

end Cong

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaG3OfInputs
section
noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option linter.dupNamespace false
set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem Hp_eq_Hsp (t : TauC Y u u') (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ)
    (hL : IsLift Λ (lf D (X.Fu u))) (hL' : IsLift Λ t.frame) :
    Hp Λ (lf D (X.Fu u)) t.frame = Hsp (X.Fu u) t.frame.fl := by
  unfold Hp Hsp
  rw [UUE_eq_Asp Λ hΛ _ _ hL hL']

theorem lemmaG3_of_inputs (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0)
    (h2 : Gt t2 ≠ 0) (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) (hG1 : t1.G = t0.G) (hG2 : t2.G = t0.G)
    (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u')))
    (he : t2.lin = σ * t1.lin * s') (ha : coefA Y u u' t0 t1 = coefA Y u u' t0 t2)
    (ha' : coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2) :
    σ (omp (X.Fu u) t1.frame.fl) - omp (X.Fu u) t1.frame.fl ∈ (X.Fu u).X ∧
    (t1.lin * s'⁻¹ * t1.lin⁻¹) (omp t1.frame.fl (X.Fu u)) - omp t1.frame.fl (X.Fu u) ∈ t1.frame.fl.X ∧
    ∀ w ∈ Hsp (X.Fu u) t1.frame.fl, ∃ w0 ∈ Hsp (X.Fu u) t1.frame.fl,
      σ w - w0 ∈ (X.Fu u).X ∧ (t1.lin * s'⁻¹ * t1.lin⁻¹) w - w0 ∈ t1.frame.fl.X := by
  obtain ⟨⟨l1, -⟩, ⟨l1', -⟩⟩ := line_occ Y t0 t1 h0 h1 hR1 hG1 hT hT'
  obtain ⟨⟨l2, -⟩, ⟨l2', -⟩⟩ := line_occ Y t0 t2 h0 h2 hR2 hG2 hT hT'
  have hy : yT Y u u' t2 - yT Y u u' t1 ∈ (X.Fu u).X := by
    have := Submodule.sub_mem _ l2 l1
    rw [← ha] at this
    convert this using 1
    abel
  have hy' : yT' Y u u' t2 - yT' Y u u' t1 ∈ (X.Fu u').X := by
    have := Submodule.sub_mem _ l2' l1'
    rw [← ha'] at this
    convert this using 1
    abel
  obtain ⟨o1, o2, o3, o4⟩ := omp_terms Y t1 t2 σ s' hσ hs' he
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hs'i := SRat_inv (lf D (X.Fu u')) hs'
  have hσm := hσ
  obtain ⟨hσi, hσf, hσz⟩ := hσm
  obtain ⟨hsi', hsf', hsz'⟩ := hs'i
  have hsymm : ∀ v, t2.lin.symm (σ v) = s'.symm (t1.lin.symm v) := by
    intro v
    apply t2.lin.injective
    rw [LinearEquiv.apply_symm_apply, he]
    show σ v = σ (t1.lin (s' (s'.symm (t1.lin.symm v))))
    simp
  refine ⟨?_, ?_, ?_⟩
  · have e : yT Y u u' t2 - yT Y u u' t1 =
        ((Tu D u : ℕ) : D.host.E) • (σ (omp (X.Fu u) t1.frame.fl) - omp (X.Fu u) t1.frame.fl) := by
      simp only [yT, yv, o1, o2, smul_sub]
      abel
    rw [e] at hy
    exact (Submodule.smul_mem_iff _ hTE).1 hy
  · set ω := omp t1.frame.fl (X.Fu u) with hω
    have e : yT' Y u u' t2 - yT' Y u u' t1 =
        ((Tu D u' : ℕ) : D.host.E) • (s'.symm (t1.lin.symm ω) - t1.lin.symm ω) := by
      simp only [yT', yv, o3, o4, frame_z_eq_lin_zu, map_add, map_smul, LinearEquiv.symm_apply_apply, hsymm, smul_sub]
      abel
    rw [e] at hy'
    have hv := (Submodule.smul_mem_iff _ hTE').1 hy'
    refine (mem_frameX Y t1 _).2 ?_
    convert hv using 1
    rw [map_sub]
    show t1.lin.symm (t1.lin (s'.symm (t1.lin.symm ω))) - t1.lin.symm ω = _
    rw [LinearEquiv.symm_apply_apply]
  · obtain ⟨hl1, hl2, hTh⟩ := th21 Y t0 t1 t2 h0 h1 h2 hR1 hR2
    have hlat : Submodule.IsLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.1
    have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
    have hL1 : IsLift t0.lam t1.frame := by rw [← hl1]; exact t1.rep.2.2.2.2.1
    have hL2 : IsLift t0.lam t2.frame := by rw [← hl2]; exact t2.rep.2.2.2.2.1
    have hH1 := Hp_eq_Hsp Y t1 t0.lam hlat hLF hL1
    have hH2 := Hp_eq_Hsp Y t2 t0.lam hlat hLF hL2

    have hX1A : t1.frame.fl.X ≤ Asp (X.Fu u) t1.frame.fl := by
      rw [← Asp_symm]; exact X_le_Asp _ _
    have hz1A : t1.frame.fl.z ∈ Asp (X.Fu u) t1.frame.fl := by
      rw [← Asp_symm]; exact z_mem_Asp _ _
    have hAsp : Asp (X.Fu u) t2.frame.fl ≤ (Asp (X.Fu u) t1.frame.fl).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [Asp, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases i with
      | inl a =>
        refine ⟨σ.symm ((X.Fu u).fvec a), ?_, by simp⟩
        induction a using Fin.lastCases with
        | last =>
          have e : σ.symm ((X.Fu u).fvec (Fin.last _)) =
              (X.Fu u).z + (σ.symm (X.Fu u).z - (X.Fu u).z) := by
            simp [FlagG.fvec, Fin.snoc_last]
          rw [e]
          exact Submodule.add_mem _ (z_mem_Asp _ _) (X_le_Asp _ _ (SRat_inv (lf D (X.Fu u)) hσ).2.2)
        | cast a =>
          simp only [FlagG.fvec, Fin.snoc_castSucc]
          refine X_le_Asp _ _ (X_pres (lf D (X.Fu u)) (SRat_inv (lf D (X.Fu u)) hσ).2.1 _ ?_)
          exact Submodule.subset_span ⟨a, rfl⟩
      | inr b =>
        refine ⟨t1.lin (s' ((X.Fu u').fvec b)), ?_, ?_⟩
        · induction b using Fin.lastCases with
          | last =>
            have e : t1.lin (s' ((X.Fu u').fvec (Fin.last _))) =
                t1.frame.fl.z + t1.lin (s' (X.Fu u').z - (X.Fu u').z) := by
              rw [frame_z_eq_lin_zu, map_sub]; simp [FlagG.fvec, Fin.snoc_last]
            rw [e]
            refine Submodule.add_mem _ hz1A (hX1A ((mem_frameX Y t1 _).2 ?_))
            rw [LinearEquiv.symm_apply_apply]
            exact hs'.2.2
          | cast b =>
            refine hX1A ((mem_frameX Y t1 _).2 ?_)
            rw [LinearEquiv.symm_apply_apply]
            simp only [FlagG.fvec, Fin.snoc_castSucc]
            exact X_pres (lf D (X.Fu u')) hs'.2.1 _ (Submodule.subset_span ⟨b, rfl⟩)
        · show σ (t1.lin (s' ((X.Fu u').fvec b))) = t2.frame.fl.fvec b
          rw [frame_fvec, he]
          rfl
    intro w hw
    have hσw : σ w ∈ Hp t0.lam (lf D (X.Fu u)) t2.frame := by
      rw [hH2]
      refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun y hy => ?_
      obtain ⟨a, ha, rfl⟩ := hAsp hy
      rw [LinearEquiv.coe_coe, hσi]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).1 hw a ha
    rw [← hTh] at hσw
    obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hσw
    obtain ⟨-, hp2, hp12, hpβ⟩ := (CorankRelation.mem_ThPairs t0.lam _ t2.frame t1.frame _ p).1 hp
    simp only [LinearMap.fst_apply] at hp1
    refine ⟨p.2, by rw [← hH1]; exact hp2, ?_, ?_⟩
    · rw [← hp1]; exact hp12
    · have e : (t1.lin * t2.lin⁻¹) p.1 = (t1.lin * s'⁻¹ * t1.lin⁻¹) w := by
        rw [hp1]
        show t1.lin (t2.lin.symm (σ w)) = t1.lin (s'.symm (t1.lin.symm w))
        rw [hsymm]
      rw [← e]
      exact hpβ

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

