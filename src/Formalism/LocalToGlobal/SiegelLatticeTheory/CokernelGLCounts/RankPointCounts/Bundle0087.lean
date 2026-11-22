import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0085
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0086
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0045
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0047

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BwdTermHolds
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))

theorem bwdTerm'_holds : BwdTerm' Zd u u' F0 what₂ := bwdTerm'_of_gx (genXiRev_holds Zd)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountBase
section
noncomputable section

namespace Formalism.L2.SG.Pf.CountBase

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.AtPt
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem zhatOM_sg (X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    ZhatOM X * Sg D.host.E D.R.rS = X := by
  ext a b
  simp only [ZhatOM, Sg, Matrix.mul_diagonal]
  rw [mul_comm, ← mul_assoc, ← mul_pow]
  simp

theorem modMat_ord (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D) (hM : (M p).split = none)
    (w : Point D.host.E (D.R.rS + 1)) :
    Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) *
        (ptMat w).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) =
      modMat δ T T' p w := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hR : (D.s.atP p).split = none := by
    have h := (hA p).2.2.2.2.2
    rw [hM] at h
    cases h' : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [h'] at h; exact h.elim
  ext a b
  rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
  by_cases hb : b = sgF w a
  · rw [if_pos hb, if_pos hb, modMat_blk Zd]
    simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul]
    subst hb
    ring
  · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]

theorem baseConj_L (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (hM : (M p).split = none) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) :
    Formalism.L2.SG.Pf.ProdE.Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p +
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w = a.mat := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hY := Formalism.L2.SG.Pf.PCount.zzp_sgn_ord Zd u u' p hM (ZhatOM (ptMat w))
  rw [zhatOM_sg] at hY
  have hmat := Formalism.L2.SG.Pf.LocOrbSumPf.modShift_holds δ (D.mem u).A.T (D.mem u').A.T p w a ha
  rw [hmat]
  unfold Formalism.L2.SG.Pf.ProdE.Y0
  congr 1
  rw [show Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p =
    Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p from rfl, hY]
  exact modMat_ord hA _ _ p hM w

end Formalism.L2.SG.Pf.CountBase
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CrossOfComp
section
noncomputable section

open Matrix ValuativeRel
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount
  Formalism.L2.SG.LsDatumB

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem cross_of_comp {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L) {r : ℕ} {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (h1 : Cross (A.map (π1 M g)) (A'.map (π1 M g))) (h2 : Cross (A.map (π2 M g)) (A'.map (π2 M g))) : Cross A A' := by
  unfold Cross at h1 h2 ⊢
  have d : ∀ (f : E →+* F) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (B.map f).det = f B.det :=
    fun f B => (RingHom.map_det f B).symm
  rw [ld_map, ld_map, d, d, ← map_mul, ← map_mul] at h1 h2
  apply g.e.injective
  exact Prod.ext h1 h2

theorem gaPlusTh_of (hLO : LiftOrb) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) : GaPlusTh M δ u u' := by
  intro hA hT hPH w w' Z Z' hk hZ hZ' p hne heq
  set c := cornerSh δ (D.mem u).A.T (D.mem u').A.T p w with hc
  have hc' : cornerSh δ (D.mem u).A.T (D.mem u').A.T p w' = c := (cornerSh_of_kind δ _ _ p hk).symm
  set Y := CntLocal.ZZP (M := M) δ u u' p Z + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY
  set Y' := CntLocal.ZZP (M := M) δ u u' p Z' + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY'
  have hcm : ∀ cc : (D.s.atP p).Ep, (Matrix.of fun a b : Fin (D.R.rS + 1) =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cc else 0) = cc • Ec (K := (D.s.atP p).Ep) D.R.rS := by
    intro cc; ext a b; simp only [Ec, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
  have eY : FCount.thZ M δ u u' w Z p = clsOf (M p) Y := by
    unfold FCount.thZ thL; rw [hcm]
  have eY' : FCount.thZ M δ u u' w' Z' p = clsOf (M p) Y' := by
    unfold FCount.thZ thL; rw [hcm, hc']
  rw [eY] at hne heq
  rw [eY'] at heq

  have hXc : Cross (ZhatLoc M δ p Z) (ZhatLoc M δ p Z') := cross_zhatLoc δ M p (cross_global hk hZ hZ')
  have hZc : Cross (CntLocal.ZZP (M := M) δ u u' p Z) (CntLocal.ZZP (M := M) δ u u' p Z') := by
    unfold CntLocal.ZZP
    rcases hs : (M p).split with _ | g
    · unfold Loc.HermSp.ZZplusOf; rw [hs]; exact hXc
    · refine cross_of_comp (M p) g ?_ ?_
      · rw [zzPlus_map_firstComponent (M p) g hs, zzPlus_map_firstComponent (M p) g hs]
        exact cross_shift (cross_map _ hXc) _ _
      · rw [zzPlus_map_secondComponent (M p) g hs, zzPlus_map_secondComponent (M p) g hs]
        exact cross_shift (cross_transpose (cross_map _ hXc)) _ _
  unfold clsOf at hne heq
  by_cases h1 : (∀ a b, Y a b ∈ (M p).R) ∧ IsUnit Y.det
  swap
  · exact absurd (dif_neg h1) hne
  rw [dif_pos h1] at heq
  by_cases h2 : (∀ a b, Y' a b ∈ (M p).R) ∧ IsUnit Y'.det
  swap
  · rw [dif_neg h2] at heq; exact absurd heq (by simp)
  rw [dif_pos h2] at heq
  set ZZ : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y a b, h1.1 a b⟩, h1.2⟩ with hZZ
  set ZZ' : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y' a b, h2.1 a b⟩, h2.2⟩ with hZZ'
  have hmap : ZZ.Z.map (M p).R.subtype = Y := rfl
  have hmap' : ZZ'.Z.map (M p).R.subtype = Y' := rfl
  have hiso : Nonempty ((M p).Iso ZZ ZZ') := Quotient.exact (Option.some.inj heq)
  have hκ : (ZZ.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) =
      (ZZ'.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) := by
    rw [hmap, hmap']
    exact kappa_eq hZc c h1.2 h2.2
  obtain ⟨l, ρ, hlu, hρu, hle, hρl, hrel⟩ := hLO (M p) (hA p).1 D.R.rS ZZ ZZ' hiso hκ
  set L := l.map (M p).R.subtype with hLdef
  set P := ρ.map (M p).R.subtype with hPdef
  have hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0 := by
    intro i; simp only [hLdef, Matrix.map_apply, hle i]; split_ifs <;> simp
  have hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0 := by
    intro j; simp only [hPdef, Matrix.map_apply, hρl j]; split_ifs <;> simp
  have hYrel : Y' = L * Y * P := by
    rw [← hmap, ← hmap', hrel, Matrix.map_mul, Matrix.map_mul]
  have hZrel : CntLocal.ZZP (M := M) δ u u' p Z' = L * CntLocal.ZZP (M := M) δ u u' p Z * P := by
    have e := hYrel
    rw [hY, hY', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Ec_eq_cornerM,
      corner_sandwich L P hL hP 1] at e
    exact add_right_cancel e
  have hLR : ∀ i j, L i j ∈ (M p).R := fun i j => (l i j).2
  have hPR : ∀ i j, P i j ∈ (M p).R := fun i j => (ρ i j).2
  have hLu : ∃ y ∈ (M p).R, L.det * y = 1 := by
    obtain ⟨v, hv⟩ := hlu
    refine ⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩
    have : L.det = ((l.det : (M p).R) : (D.s.atP p).Ep) := (RingHom.map_det (M p).R.subtype l).symm
    rw [this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  have hPu : ∃ y ∈ (M p).R, P.det * y = 1 := by
    obtain ⟨v, hv⟩ := hρu
    refine ⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩
    have : P.det = ((ρ.det : (M p).R) : (D.s.atP p).Ep) := (RingHom.map_det (M p).R.subtype ρ).symm
    rw [this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rcases hs : (M p).split with _ | g
  · have hRO : (M p).R = (M p).L.O := by unfold Loc.Model.R; rw [hs]
    have hX : ZhatLoc M δ p Z' = L * ZhatLoc M δ p Z * P := by
      have e := hZrel
      unfold CntLocal.ZZP Loc.HermSp.ZZplusOf at e
      rw [hs] at e
      exact e
    obtain ⟨yL, hyL, hLy⟩ := hLu
    obtain ⟨yP, hyP, hPy⟩ := hPu
    exact gaCong_L δ M hA p hs _ _ Z Z' L P hL hP (fun i j => hRO ▸ hLR i j) (fun i j => hRO ▸ hPR i j)
      ⟨yL, hRO ▸ hyL, hLy⟩ ⟨yP, hRO ▸ hyP, hPy⟩ hX
  · exact gaCong_G δ M hA p g hs _ _ _ _ Z Z' L P hL hP hLR hPR hLu hPu hZrel

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIE
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

theorem sub_add_eq {R W : Type*} [Ring R] [AddCommGroup W] [Module R W] {P : Submodule R W} {a b c : W}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (e : c = a + b) : (⟨c, hc⟩ : P) = ⟨a, ha⟩ + ⟨b, hb⟩ := by
  subst e; rfl

theorem sub_smul_eq {R W : Type*} [Ring R] [AddCommGroup W] [Module R W] {P : Submodule R W} {a c : W} (k : R)
    (ha : a ∈ P) (hc : c ∈ P) (e : c = k • a) : (⟨c, hc⟩ : P) = k • ⟨a, ha⟩ := by
  subst e; rfl

section Place

variable (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
  (ψ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
  (β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V)

theorem sendsB_add {m₁ m₂ : (VS D).V}
    (h₁ : baseChange₂ D p m₁ ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
    (h₂ : baseChange₂ D p m₂ ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
    (k₁ : baseChange₂ D p (β₀ m₁) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))
    (k₂ : baseChange₂ D p (β₀ m₂) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))
    (s₁ : SendsB Zd p γ F'₂ ψ β₀ m₁) (s₂ : SendsB Zd p γ F'₂ ψ β₀ m₂) : SendsB Zd p γ F'₂ ψ β₀ (m₁ + m₂) := by
  intro hm hm₂
  have e1 : (⟨baseChange₂ D p (m₁ + m₂), hm⟩ : ↥((locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))) =
      ⟨baseChange₂ D p m₁, h₁⟩ + ⟨baseChange₂ D p m₂, h₂⟩ :=
    sub_add_eq h₁ h₂ hm ((baseChange₂ D p).map_add m₁ m₂)
  have e2 : (⟨baseChange₂ D p (β₀ (m₁ + m₂)), hm₂⟩ : ↥((locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))) =
      ⟨baseChange₂ D p (β₀ m₁), k₁⟩ + ⟨baseChange₂ D p (β₀ m₂), k₂⟩ :=
    sub_add_eq k₁ k₂ hm₂ (by rw [LinearEquiv.map_add, (baseChange₂ D p).map_add])
  have f1 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p (m₁ + m₂), hm⟩ =
      (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m₁, h₁⟩ + (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m₂, h₂⟩ :=
    (congrArg _ e1).trans (LinearMap.map_add _ _ _)
  have f2 : (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ (m₁ + m₂)), hm₂⟩ =
      (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m₁), k₁⟩ +
        (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m₂), k₂⟩ :=
    (congrArg _ e2).trans (LinearMap.map_add _ _ _)
  exact ((congrArg ψ f1).trans (LinearEquiv.map_add ψ _ _)).trans
    ((congrArg₂ (· + ·) (s₁ h₁ k₁) (s₂ h₂ k₂)).trans f2.symm)

theorem sendsB_smul (c : D.host.E) {m : (VS D).V}
    (h₁ : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
    (k₁ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))
    (s : SendsB Zd p γ F'₂ ψ β₀ m) : SendsB Zd p γ F'₂ ψ β₀ (c • m) := by
  intro hm hm₂
  have e1 : (⟨baseChange₂ D p (c • m), hm⟩ : ↥((locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))) =
      (D.s.atP p).ιE c • ⟨baseChange₂ D p m, h₁⟩ :=
    sub_smul_eq _ h₁ hm (Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂ p c m)
  have e2 : (⟨baseChange₂ D p (β₀ (c • m)), hm₂⟩ : ↥((locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)))) =
      (D.s.atP p).ιE c • ⟨baseChange₂ D p (β₀ m), k₁⟩ :=
    sub_smul_eq _ k₁ hm₂ (by rw [LinearEquiv.map_smul]; exact Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂ p c (β₀ m))
  have f1 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p (c • m), hm⟩ =
      (D.s.atP p).ιE c • (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, h₁⟩ :=
    (congrArg _ e1).trans (LinearMap.map_smul _ _ _)
  have f2 : (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ (c • m)), hm₂⟩ =
      (D.s.atP p).ιE c • (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), k₁⟩ :=
    (congrArg _ e2).trans (LinearMap.map_smul _ _ _)
  exact ((congrArg ψ f1).trans (LinearEquiv.map_smul ψ _ _)).trans
    ((congrArg ((D.s.atP p).ιE c • ·) (s h₁ k₁)).trans f2.symm)

theorem sendsB_X {m : (VS D).V} (hX1 : baseChange₂ D p m ∈ (locH Zd p).X (tLoc Zd p γ).f')
    (hX2 : baseChange₂ D p (β₀ m) ∈ (locH Zd p).X (locF' Zd p F'₂)) : SendsB Zd p γ F'₂ ψ β₀ m := by
  intro hm hm₂
  have e1 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hX1
  have e2 : (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hX2
  rw [e1, e2]
  exact LinearEquiv.map_zero ψ

theorem bcP_X_f' {x : (VS D).V} (hx : x ∈ Xsp (repF γ)) : baseChange₂ D p x ∈ (locH Zd p).X (tLoc Zd p γ).f' := by
  obtain ⟨h1, -⟩ := admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)
  set ξ := admXi D γ.lam (lf D F0) (repF γ) with hξdef
  have hξ : ξ⁻¹ * ξ = 1 := OmL.admissibility_witness_inv_mul γ.lam (lf D F0) (repF γ)
  have key : ∀ b, ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • frameAct (frame (repF γ)) ξ⁻¹ a = frame (repF γ) b := by
    intro b
    simp only [frameAct, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h1' : ∀ c, ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) * ((ξ⁻¹ c a : 𝓞 D.host.E) : D.host.E) =
        (((ξ⁻¹ * ξ) c b : 𝓞 D.host.E) : D.host.E) := by
      intro c
      rw [Matrix.mul_apply]
      push_cast
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    simp only [← Finset.sum_smul, h1', hξ, Matrix.one_apply]
    simp
  change x ∈ Submodule.span D.host.E (Set.range (repF γ).fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [← frame_csG, ← key, map_sum, Fin.sum_univ_castSucc]
    have hl : ξ (Fin.last D.R.rS) j.castSucc = 0 := h1 _ _ (Fin.castSucc_lt_last j)
    rw [hl]
    simp only [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
    refine add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) (by simp)
    have e : baseChange₂ D p (frameAct (frame (repF γ)) ξ⁻¹ i.castSucc) =
        (((isUnit_sF' Zd p i.castSucc).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) • (tLoc Zd p γ).f' i.castSucc := by
      rw [tf', smul_smul]
      have : ((((isUnit_sF' Zd p i.castSucc).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) *
          (TermLoc.sgnP' D p i.castSucc * frFac Zd.δ p i.castSucc) = 1 := (isUnit_sF' Zd p i.castSucc).val_inv_mul
      rw [this, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

end Place

section Place2

variable (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
  (ψ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
  (β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V)

theorem z_orthG {T' : D.host.E} (G : LFlag (VS D) D.R.rS T') : G.fl.z ∈ orth (VS D) (Xsp G) :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) G.fl.z x]
    have h := NMoveP.hT_f_X G.fl (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]

theorem X_le_orthG {T' : D.host.E} (G : LFlag (VS D) D.R.rS T') : Xsp G ≤ orth (VS D) (Xsp G) :=
  BwdNA.X_le_orth (VS D) (Xsp G) fun _ hx _ hy => NMoveP.hT_X_X G.fl hx hy

theorem starLast_sub_mem :
    frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹ (Fin.last D.R.rS) - (repF γ).fl.z ∈
      Xsp (repF γ) := by
  obtain ⟨-, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  show ∑ a, (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a (Fin.last D.R.rS) : 𝓞 D.host.E) : D.host.E) • frame (repF γ) a -
    (repF γ).fl.z ∈ Xsp (repF γ)
  rw [Fin.sum_univ_castSucc, hξ2, frame_lastG, (by simp : ((1 : 𝓞 D.host.E) : D.host.E) = 1), one_smul,
    add_sub_cancel_right]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  rw [frame_csG]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem sends_beta_z
    (hS : (locH Zd p).SendsTo ψ.toLinearMap 1 1 ((tLoc Zd p γ).f' (Fin.last D.R.rS)) (locF' Zd p F'₂ (Fin.last D.R.rS)))
    (hzβ : β₀ (repF γ).fl.z = F'₂.fl.z) : SendsB Zd p γ F'₂ ψ β₀ (repF γ).fl.z := by
  intro hm hm₂
  obtain ⟨g, hg⟩ : ∃ g, g = frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹ (Fin.last D.R.rS) :=
    ⟨_, rfl⟩
  have hd : g - (repF γ).fl.z ∈ Xsp (repF γ) := hg ▸ starLast_sub_mem γ
  have hlast : (tLoc Zd p γ).f' (Fin.last D.R.rS) = baseChange₂ D p g := by
    rw [tf', hg]
    have h1 : TermLoc.sgnP' D p (Fin.last D.R.rS) * frFac Zd.δ p (Fin.last D.R.rS) = 1 := sF'_last Zd p
    rw [h1, one_smul]
  have hgo : g ∈ orth (VS D) (Xsp (repF γ)) := by
    have e : g = (repF γ).fl.z + (g - (repF γ).fl.z) := by abel
    rw [e]
    exact add_mem (z_orthG (repF γ)) (X_le_orthG (repF γ) hd)
  have hmem : (tLoc Zd p γ).f' (Fin.last D.R.rS) ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f') :=
    hlast ▸ bcP_perp_f' Zd p γ hgo
  have h2 : baseChange₂ D p (β₀ (repF γ).fl.z) = locF' Zd p F'₂ (Fin.last D.R.rS) := by
    rw [hzβ, locF'_last]
  have h3 : (1 : (D.s.atP p).Ep) • ψ.toLinearMap ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hmem⟩) =
      (1 : (D.s.atP p).Ep) • (locH Zd p).mkW (locF' Zd p F'₂) ⟨_, hm₂⟩ :=
    hS ⟨(tLoc Zd p γ).f' (Fin.last D.R.rS), hmem⟩ ⟨baseChange₂ D p (β₀ (repF γ).fl.z), hm₂⟩ rfl h2
  have h3' := ((one_smul _ _).symm.trans h3).trans (one_smul _ _)
  have hX : baseChange₂ D p (repF γ).fl.z - (tLoc Zd p γ).f' (Fin.last D.R.rS) ∈ (locH Zd p).X (tLoc Zd p γ).f' := by
    rw [hlast, ← (baseChange₂ D p).map_sub]
    have : (repF γ).fl.z - g = -(g - (repF γ).fl.z) := by abel
    rw [this]
    exact bcP_X_f' Zd p γ ((Xsp (repF γ)).neg_mem hd)
  have h4 : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p (repF γ).fl.z, hm⟩ =
      (locH Zd p).mkW (tLoc Zd p γ).f' ⟨_, hmem⟩ := (Submodule.Quotient.eq _).2 hX
  exact (congrArg ψ h4).trans h3'

end Place2

end BetaI

theorem pinB_of (hSp : SpanOm D) (hOm : PinOm Zd u u' F0 what₂) (hW0 : PartialIsometryExtension Zd u u' F0 what₂) :
    PinB Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO p m hm hm₂ hmo
  have hB0 := hB
  obtain ⟨-, hZ, hSt, -, -, -, -, hG⟩ := hB
  obtain ⟨-, hZ₁d, -⟩ := starMinors_holds u u' F0 what₂ γ Z hZ
  have hl1 := star_frame_lead_minor γ (D.R.rS + 1)
  rw [FsLA.leadMinorE_full, FsLA.leadMinorE_full] at hl1
  have hdet1 : (Zhat F0 (repF γ).fl).det ≠ 0 := fun h0 => hZ₁d (hl1.trans h0)
  have hzβ : β₀ (repF γ).fl.z = F'₂.fl.z := by
    have := hfr (Fin.last _)
    rwa [BwdBetaCut.fvec_last', BwdBetaCut.fvec_last'] at this
  have hXmap := BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have horth : ∀ y ∈ orth (VS D) (Xsp (repF γ)), β₀ y ∈ orth (VS D) (Xsp (liftF F'₂)) := by
    intro y hy
    rw [← hXmap, Formalism.L2.SG.Pf.orth_map_sat β₀ hiso]
    exact Submodule.mem_map_of_mem hy
  have hmapX : ∀ x ∈ Xsp (repF γ), β₀ x ∈ Xsp (liftF F'₂) := fun x hx => by
    rw [← hXmap]; exact Submodule.mem_map_of_mem hx
  have k1 : ∀ y, y ∈ orth (VS D) (Xsp (repF γ)) →
      baseChange₂ D p y ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f') := fun y hy => bcP_perp_f' Zd p γ hy
  have k2 : ∀ y, y ∈ orth (VS D) (Xsp (repF γ)) →
      baseChange₂ D p (β₀ y) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂)) :=
    fun y hy => baseChangeAt_perp' Zd p F'₂ (horth y hy)
  have hsp := hSp F0 (repF γ).fl hdet1 hG m hmo
  refine Exists.elim hsp fun x' h1 => ?_
  refine Exists.elim h1.2 fun w h2 => ?_
  refine Exists.elim h2.2 fun a h3 => ?_
  refine Exists.elim h3 fun b hmeq => ?_
  have hx' : x' ∈ (repF γ).fl.X := h1.1
  have hw : w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus) := h2.1
  subst hmeq
  have ox : x' ∈ orth (VS D) (Xsp (repF γ)) := X_le_orthG (repF γ) hx'
  have hXle : (repF γ).fl.X ≤ F0.Xplus ⊔ (repF γ).fl.Xplus :=
    (show (repF γ).fl.X ≤ (repF γ).fl.Xplus from le_sup_left).trans le_sup_right
  have ow : w ∈ orth (VS D) (Xsp (repF γ)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx =>
    (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw x (hXle hx)
  have oz : (repF γ).fl.z ∈ orth (VS D) (Xsp (repF γ)) := z_orthG (repF γ)
  have oo : Gom F0.fvec (repF γ).fl.fvec ∈ orth (VS D) (Xsp (repF γ)) := BwdBetaCut.Gom_orth (lf D F0) (repF γ)
  have sx : SendsB Zd p γ F'₂ (φ' p) β₀ x' :=
    sendsB_X Zd p γ F'₂ (φ' p) β₀ (bcP_X_f' Zd p γ hx') (bcP_X' Zd p F'₂ (hmapX x' hx'))
  have sw : SendsB Zd p γ F'₂ (φ' p) β₀ w := hW0 γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p w hw
  have sz : SendsB Zd p γ F'₂ (φ' p) β₀ (repF γ).fl.z :=
    sends_beta_z Zd p γ F'₂ (φ' p) β₀ (hSt.2.1 p).2.2.2.2.2 hzβ
  have so : SendsB Zd p γ F'₂ (φ' p) β₀ (Gom F0.fvec (repF γ).fl.fvec) := hOm γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p
  have oxw := add_mem ox ow
  have oaz := Submodule.smul_mem _ a oz
  have obo := Submodule.smul_mem _ b oo
  have s1 := sendsB_add Zd p γ F'₂ (φ' p) β₀ (k1 _ ox) (k1 _ ow) (k2 _ ox) (k2 _ ow) sx sw
  have s2 := sendsB_add Zd p γ F'₂ (φ' p) β₀ (k1 _ oxw) (k1 _ oaz) (k2 _ oxw) (k2 _ oaz) s1
    (sendsB_smul Zd p γ F'₂ (φ' p) β₀ a (k1 _ oz) (k2 _ oz) sz)
  have s3 := sendsB_add Zd p γ F'₂ (φ' p) β₀ (k1 _ (add_mem oxw oaz)) (k1 _ obo) (k2 _ (add_mem oxw oaz))
    (k2 _ obo) s2 (sendsB_smul Zd p γ F'₂ (φ' p) β₀ b (k1 _ oo) (k2 _ oo) so)
  exact s3 hm hm₂

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LmatMemR
section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem det_upper {X : Formalism.L2.SG.LsDatumB.MatP D p} (h1 : ∀ a b, b < a → X a b = 0) (h2 : ∀ a, X a a = 1) :
    X.det = 1 := by
  have hb : X.BlockTriangular id := fun i j hij => h1 i j hij
  rw [Matrix.det_of_upperTriangular hb]
  simp [h2]

theorem det_lower {X : Formalism.L2.SG.LsDatumB.MatP D p} (h1 : ∀ a b, a < b → X a b = 0) (h2 : ∀ a, X a a = 1) :
    X.det = 1 := by
  have hb : X.BlockTriangular OrderDual.toDual := fun i j hij => h1 i j hij
  rw [Matrix.det_of_lowerTriangular X hb]
  simp [h2]

theorem lmat_mem_R (hs : (Z.M p).split = some g) {x y : (D.s.atP p).Ep} (hx : x ∈ (Z.M p).L.O)
    (hy : y ∈ (Z.M p).L.O)
    (hc : ∃ o ∈ (Z.M p).L.O, x - (Z.M p).L.cj y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o) :
    g.e.symm ((g.e x).1, (g.e y).2) ∈ (Z.M p).R := by
  obtain ⟨o, ho, he⟩ := hc
  refine mem_R_of Z p g hs (by rw [AlgEquiv.apply_symm_apply]; exact (comp_mem Z p g hx).1)
    (by rw [AlgEquiv.apply_symm_apply]; exact (comp_mem Z p g hy).2) ⟨(g.e o).1, (comp_mem Z p g ho).1, ?_⟩
  rw [AlgEquiv.apply_symm_apply]
  have h := congrArg (fun t => (g.e t).1) he
  simp only [map_sub, map_mul, AlgEquiv.commutes, g.e_cj, Prod.fst_sub, Prod.swap_prod_mk, Prod.fst_mul,
    Prod.fst_swap, Prod.algebraMap_apply] at h
  rw [h]
  rfl

end ModeG

end Formalism.L2.SG.Pf.FibQ
end
end

