import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountLoc
section
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZOrb

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

section Typed

variable (p : PlF D) (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
  (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Zd.M p).L) (hM : (Zd.M p).split = some g)
  (hge : g.e = sg.e) (hgq : g.q = sg.q)
include hR hM hge hgq

theorem zz1' (u u' : D.what₂.Word) (Z : PairVal.MatR D) :
    (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p).map (p1 sg.e) =
      (sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
        (Z * Sg D.host.E D.R.rS).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) -
        (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
  have hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hf1 : ∀ a, p1 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl
  have hf2 : ∀ a, p2 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl
  have hm1 : ∀ k : ℕ, p1 sg.e ((-1 : (D.s.atP p).Ep) ^ k) = (-1) ^ k := fun k => by simp
  ext a b
  simp only [Matrix.map_apply, CntLocal.ZZP, Loc.HermSp.ZZplusOf, hM, CntLocal.ZhatLoc, LsDatumB.sgnP,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, hge, hgq, map_mul, map_sub, fst_proj_symm,
    apply_ite (p1 sg.e), map_zero, Prod.fst_mul, ← adeleInfiniteComponent_apply, ← adele_ext_components, hcj1, hf1, hf2, hm1, Zd.hcj p,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Ecorner, Sg, RingHom.comp_apply, map_pow, map_neg, map_one]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Fin.val_last, Nat.sub_self, pow_zero]
    ring
  · ring

theorem zz2' (u u' : D.what₂.Word) (Z : PairVal.MatR D) :
    (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p).map (p2 sg.e) =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) *
        ((Z.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
        ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
  have hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hf1 : ∀ a, p1 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl
  have hf2 : ∀ a, p2 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl
  have hm2 : ∀ k : ℕ, p2 sg.e ((-1 : (D.s.atP p).Ep) ^ k) = (-1) ^ k := fun k => by simp
  ext a b
  simp only [Matrix.map_apply, CntLocal.ZZP, Loc.HermSp.ZZplusOf, hM, CntLocal.ZhatLoc, LsDatumB.sgnP,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, hge, hgq, map_mul, map_sub, snd_proj_symm,
    apply_ite (p2 sg.e), map_zero, Prod.snd_mul, ← adeleInfiniteComponent_apply, ← adele_ext_components, hcj2, hf1, hf2, hm2, Zd.hcj p,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Ecorner, Sg, RingHom.comp_apply, map_pow, map_neg, map_one,
    Matrix.transpose_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Fin.val_last, Nat.sub_self, pow_zero]
    ring
  · ring

theorem mm1' (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    (modMat Zd.δ Tn T'n p w).map (p1 sg.e) =
      (sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) * (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) *
        Matrix.diagonal (cf Zd p)) -
        (if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then -(Tn : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp) else 0) •
          Ecorner D.R.rS := by
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  have hq : q ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hqi : Ring.inverse (qE p) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹ := by
    simp only [qE, hR]
    have := Ring.inverse_unit ((Units.mk0 q hq).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)
    simpa only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv,
      Units.val_inv_eq_inv_val] using this
  have htw1 : ∀ s x, p1 sg.e (twist p s x) = p1 sg.e x := fun s x => by
    simp only [twist, hR]; rw [fst_proj_symm]; rfl
  have hta1 : ∀ T T' : ℕ, p1 sg.e (tau0 p T T') = -(T : (D.s.atP p).Fp) * q⁻¹ := fun T T' => by
    simp only [tau0, hR, map_mul, fst_proj_symm, hqi, fst_proj_algebraMap]
  ext a b
  simp only [Matrix.map_apply, modMat_apply', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, ptMat_apply', Ecorner, Matrix.of_apply]
  by_cases hb : b = sgF w a
  · subst hb
    simp only [if_true, modMat_blk, map_sub, map_mul, fst_proj_algebraMap, htw1, hqi, apply_ite (p1 sg.e), hta1, map_zero,
      hφ1, RingHom.comp_apply]
    by_cases ha : a = Fin.last D.R.rS
    · subst ha; split_ifs <;> first | ring1 | (exfalso; rename_i h1 h2; exact h2 h1.2) | (exfalso; rename_i h1 h2; exact h1 h2.2)
    · simp only [ha, false_and, if_false]; ring
  · rw [if_neg hb, if_neg hb, map_zero, map_zero, mul_zero, zero_mul, mul_zero]
    by_cases ha : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
    · obtain ⟨rfl, rfl⟩ := ha
      have : ¬ sgF w (Fin.last D.R.rS) = Fin.last D.R.rS := fun h => hb h.symm
      simp [this]
    · simp [ha]

theorem mm2' (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    (modMat Zd.δ Tn T'n p w).map (p2 sg.e) =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
        (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
        (if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then (T'n : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp) else 0) •
          Ecorner D.R.rS := by
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  have hq : q ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hqi : Ring.inverse (qE p) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹ := by
    simp only [qE, hR]
    have := Ring.inverse_unit ((Units.mk0 q hq).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)
    simpa only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv,
      Units.val_inv_eq_inv_val] using this
  have htw2 : ∀ s x, p2 sg.e (twist p s x) = (-1) ^ s * p2 sg.e x := fun s x => by
    simp only [twist, hR]; rw [snd_proj_symm]; rfl
  have hta2 : ∀ T T' : ℕ, p2 sg.e (tau0 p T T') = (T' : (D.s.atP p).Fp) * q⁻¹ := fun T T' => by
    simp only [tau0, hR, map_mul, snd_proj_symm, hqi, snd_proj_algebraMap]
  ext a b
  simp only [Matrix.map_apply, modMat_apply', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, ptMat_apply', Ecorner, Matrix.of_apply, Sg]
  by_cases hb : b = sgF w a
  · subst hb
    have hsr := sign_rel (R := (D.s.atP p).Fp) _ _ _ (nu_parity w a)
    simp only [if_true, modMat_blk, map_sub, map_mul, snd_proj_algebraMap, htw2, hqi, apply_ite (p2 sg.e), hta2, map_zero,
      hφ2, RingHom.comp_apply, hsr]
    by_cases ha : a = Fin.last D.R.rS
    · subst ha; split_ifs <;> first | ring1 | (exfalso; rename_i h1 h2; exact h2 h1.2) | (exfalso; rename_i h1 h2; exact h1 h2.2)
    · simp only [ha, false_and, if_false]; ring
  · rw [if_neg hb, if_neg hb, map_zero, map_zero, mul_zero, zero_mul, mul_zero, zero_mul]
    by_cases ha : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
    · obtain ⟨rfl, rfl⟩ := ha
      have : ¬ sgF w (Fin.last D.R.rS) = Fin.last D.R.rS := fun h => hb h.symm
      simp [this]
    · simp [ha]

theorem zzpSgn_orb_typed (u u' : D.what₂.Word) {w : Point D.host.E (D.R.rS + 1)} {Z L B : PairVal.MatR D}
    (hL : IsLo L) (hB : IsUp B) (hf' : Z * Sg D.host.E D.R.rS = L * ptMat w * B) :
    ∃ uL uU : MatP D p, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p = uL * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * uU := by
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hA' : Z = L * ptMat w * B * Sg D.host.E D.R.rS := by
    rw [← hf', Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  have hs0 : ∀ a : Fin (D.R.rS + 1), (-1 : (D.s.atP p).Fp) ^ (D.R.rS - a.val) ≠ 0 :=
    fun a => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  obtain ⟨L1, U1, hL1, hU1, h1⟩ := generic_comp (sgF w) (sgF_sgF _)
    (isLo_map ((p1 sg.e).comp (D.s.atP p).ιE) hL) (isUp_map ((p1 sg.e).comp (D.s.atP p).ιE) hB)
    (W := (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE))
    (fun a b hb => by simp only [Matrix.map_apply, ptMat_apply', if_neg hb, map_zero])
    (fun a => by
      simp only [Matrix.map_apply, ptMat_apply', if_true]
      exact (map_ne_zero _).2 (pTau_ne' _ a))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (sg.q : (D.s.atP p).Fp)⁻¹ (inv_ne_zero hq)
    (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  obtain ⟨L2, U2, hL2, hU2, h2⟩ := generic_comp (sgF w) (sgF_sgF _)
    (isLo_conj (isLo_transpose (isUp_map ((p2 sg.e).comp (D.s.atP p).ιE) hB)) _ _ (fun a => sgn_sq' D.R.rS a) :
      IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    (isUp_conj (isUp_transpose (isLo_map ((p2 sg.e).comp (D.s.atP p).ιE) hL)) _ _ (fun a => sgn_sq' D.R.rS a) :
      IsUp (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    (L := Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS)
    (B := Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS)
    (W := Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) *
      Sg (D.s.atP p).Fp D.R.rS)
    (fun a b hb => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_neg hb, map_zero,
        mul_zero, zero_mul])
    (fun a => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true]
      exact mul_ne_zero (mul_ne_zero (hs0 _) ((map_ne_zero _).2 (pTau_ne' _ a))) (hs0 _))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (-(sg.q : (D.s.atP p).Fp)⁻¹) (neg_ne_zero.2 (inv_ne_zero hq))
    ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  have e2 : (Z.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS =
      (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        (Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) *
          Sg (D.s.atP p).Fp D.R.rS) *
        (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) := by
    rw [hA', Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
    exact fact2 _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _) (by rw [← Matrix.transpose_map, ptMat_transpose])
  refine goal_of (isLo_glue sg.e hL1 hL2) (isUp_glue sg.e hU1 hU2) (mat_eq sg.e ?_ ?_)
  · rw [zz1' Zd p sg hR g hM hge hgq, hf']
    conv_lhs => rw [Matrix.map_mul, Matrix.map_mul]
    rw [h1]
    conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst]
    rw [mm1' Zd p sg hR g hM hge hgq]
  · rw [zz2' Zd p sg hR g hM hge hgq, e2, h2]
    conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd]
    rw [mm2' Zd p sg hR g hM hge hgq]

end Typed

theorem zzpSgn_orb (u u' : D.what₂.Word) {w : Point D.host.E (D.R.rS + 1)} {Z : PairVal.MatR D} (hZ : AtMat w Z)
    (p : PlF D) :
    ∃ uL uU : MatP D p, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p = uL * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * uU := by
  obtain ⟨L, U, hL, hU, e⟩ := hZ
  have hL' := isLo_of_uni hL
  have hU' := isUp_of_uni hU
  have hf' : Z * Sg D.host.E D.R.rS = L * ptMat w * U := by rw [← zhatOM_eq]; exact e
  have hAg := (Zd.agree p).2.2.2.2.2
  rcases hM : (Zd.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>
    simp only [hM, hR] at hAg
  · set ι := (D.s.atP p).ιE
    set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)
    set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)
    have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
    have hfr' : ∀ a, fr a * fri a = 1 := fun a => by simp only [fr, fri, ← map_mul, cf_cfi, map_one]
    have hmod : Matrix.diagonal fr * (ptMat w).map ι * Matrix.diagonal fr =
        modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w := by
      ext a b
      rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
      by_cases hb : b = sgF w a
      · rw [if_pos hb, if_pos hb, modMat_blk Zd]
        simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul, fr]
        subst hb
        ring
      · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]
    rw [zzp_sgn_ord Zd u u' p hM Z, hf', Matrix.map_mul, Matrix.map_mul, regroup fr fri hfr, hmod]
    exact goal_of (isLo_conj (isLo_map ι hL') fr fri hfr') (isUp_conj (isUp_map ι hU') fri fr hfr) rfl
  · exact zzpSgn_orb_typed Zd p sg hR g hM hAg.1 hAg.2 u u' hL' hU' hf'

end ZOrb

end Formalism.L2.SG.Pf.PCount
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfSteps
section
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lead

variable {K : Type*} [CommRing K]

def leadM {m : ℕ} (X : Matrix (Fin m) (Fin m) K) (l : ℕ) : K :=
  if hl : l ≤ m then (X.submatrix (Fin.castLE hl) (Fin.castLE hl)).det else 0

theorem sum_castLE {A : Type*} [AddCommMonoid A] {l m : ℕ} (hl : l ≤ m) (g : Fin m → A)
    (hg : ∀ a : Fin m, l ≤ a.val → g a = 0) : ∑ a, g a = ∑ a : Fin l, g (Fin.castLE hl a) := by
  have e : ∑ a : Fin l, g (Fin.castLE hl a) = ∑ a ∈ Finset.univ.map (Fin.castLEEmb hl), g a := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hg
  by_contra h
  exact ha (Finset.mem_map.2 ⟨⟨a.val, Nat.lt_of_not_le h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem leadM_mul {m : ℕ} {L X U : Matrix (Fin m) (Fin m) K} (hL : IsLo L) (hU : IsUp U) (l : ℕ) :
    leadM (L * X * U) l = leadM X l := by
  unfold leadM
  split_ifs with hl
  · have e : (L * X * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        L.submatrix (Fin.castLE hl) (Fin.castLE hl) * X.submatrix (Fin.castLE hl) (Fin.castLE hl) *
          U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      refine (sum_castLE hl _ ?_).trans (Finset.sum_congr rfl fun b _ => ?_)
      · intro b hb
        have hj := j.isLt
        rw [hU.2 _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]
      · congr 1
        refine sum_castLE hl _ fun a ha => ?_
        have hi := i.isLt
        rw [hL.2 _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]
    rw [e, Matrix.det_mul, Matrix.det_mul]
    have h1 : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 :=
      det_lo' ⟨fun a => hL.1 _, fun a b hab => hL.2 _ _ hab⟩
    have h2 : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 :=
      det_up' ⟨fun a => hU.1 _, fun a b hab => hU.2 _ _ hab⟩
    rw [h1, h2, one_mul, mul_one]
  · rfl

end Lead

section Mats

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)

def mkMat {m : ℕ} (P : Matrix (Fin m) (Fin m) E) (hP : ∀ a b, P a b ∈ M.R) (hu : IsUnit P.det) : M.Mat m :=
  ⟨Matrix.of fun a b => ⟨P a b, hP a b⟩, by
    have : (Matrix.of fun a b => (⟨P a b, hP a b⟩ : M.R)).map M.R.subtype = P := rfl
    rw [this]; exact hu⟩

theorem clsOf_mk {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hP : ∀ a b, P a b ∈ M.R)
    (hu : IsUnit P.det) : clsOf M P = some (Quotient.mk (M.isoSetoid m) (mkMat M P hP hu)) := by
  unfold clsOf
  rw [dif_pos ⟨hP, hu⟩]
  rfl

theorem clsOf_map {m : ℕ} (Z : M.Mat (m + 1)) :
    clsOf M (Z.Z.map M.R.subtype) = some (Quotient.mk (M.isoSetoid m) Z) := by
  exact clsOf_mk M (Z.Z.map M.R.subtype) (fun a b => (Z.Z a b).2) Z.unit

theorem nIso_mk_out {m : ℕ} (Z₁ Z₂ : M.Mat (m + 1)) :
    M.nIso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₁)) (Quotient.out (Quotient.mk (M.isoSetoid m) Z₂)) =
      M.nIso Z₁ Z₂ := by
  have h1 : Nonempty (M.Iso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₁)) Z₁) :=
    Quotient.mk_out (s := M.isoSetoid m) Z₁
  have h2 : Nonempty (M.Iso (Quotient.out (Quotient.mk (M.isoSetoid m) Z₂)) Z₂) :=
    Quotient.mk_out (s := M.isoSetoid m) Z₂
  exact nIso_congr M h1.some h2.some

def headMat {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hP : ∀ a b, P a b ∈ M.R)
    (hu : IsUnit (leadM P m)) : M.Mat m :=
  ⟨Matrix.of fun a b => ⟨P a.castSucc b.castSucc, hP _ _⟩, by
    have e1 : (Matrix.of fun a b => (⟨P a.castSucc b.castSucc, hP _ _⟩ : M.R)).map M.R.subtype =
        P.submatrix (Fin.castLE (Nat.le_succ m)) (Fin.castLE (Nat.le_succ m)) := by
      ext a b; rfl
    have e2 : leadM P m = (P.submatrix (Fin.castLE (Nat.le_succ m)) (Fin.castLE (Nat.le_succ m))).det := by
      unfold leadM; exact dif_pos _
    rw [e1, ← e2]; exact hu⟩

end Mats

section Cut

def BridgeBA : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (m : ℕ) (n s : E) (P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) E),
    IsLo L₁ → IsUp U₁ → IsLo L₂ → IsUp U₂ → P₁ = L₁ * X₁ * U₁ → P₂ = L₂ * X₂ * U₂ →
    (∀ a : Fin m, X₁ a.castSucc (Fin.last m) = 0 ∧ X₁ (Fin.last m) a.castSucc = 0 ∧
      X₂ a.castSucc (Fin.last m) = 0 ∧ X₂ (Fin.last m) a.castSucc = 0) →
    X₁ (Fin.last m) (Fin.last m) = s → X₂ (Fin.last m) (Fin.last m) = s → IsUnit (s + n) → n ∈ M.R →
    ∀ (Y₁ Y₂ : M.Mat m) (be₁ be₂ al₁ al₂ : Fin m → M.R),
      (∀ a b : Fin m, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧ (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin m, (be₁ a : E) = P₁ a.castSucc (Fin.last m) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last m) ∧
        (al₁ a : E) = P₁ (Fin.last m) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last m) a.castSucc) →
      (∀ a b, P₁ a b ∈ M.R) → (∀ a b, P₂ a b ∈ M.R) →
      ∃ Z₁ Z₂ : M.Mat (m + 1), Z₁.Z.map M.R.subtype = P₁ + n • Ecorner m ∧
        Z₂.Z.map M.R.subtype = P₂ + n • Ecorner m ∧ M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂ = M.nIso Z₁ Z₂

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def LeadZZ : Prop :=
  ∀ (p : PlF D) (Zh : MatP D p) (T T' : (D.s.atP p).Fp),
    (leadM Zh D.R.rS = 0 ↔ leadM (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T') D.R.rS = 0) ∧
    (IsUnit (leadM Zh D.R.rS) ↔ IsUnit (leadM (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T') D.R.rS)) ∧
    (leadM Zh D.R.rS = 0 → IsUnit (leadM Zh (D.R.rS + 1)) →
      IsUnit (Loc.HermSp.ZZplusOf (Zd.M p) Zh T T').det)

def ModKind : Prop :=
  ∀ (p : PlF D) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)),
    (Dmin w D.R.rS = 0 → leadM (modMat Zd.δ T T' p w) D.R.rS = 0) ∧
    (Dmin w D.R.rS ≠ 0 → IsUnit (leadM (modMat Zd.δ T T' p w) D.R.rS) ∧
      (∀ a : Fin D.R.rS, modMat Zd.δ T T' p w a.castSucc (Fin.last D.R.rS) = 0 ∧
        modMat Zd.δ T T' p w (Fin.last D.R.rS) a.castSucc = 0) ∧
      modMat Zd.δ T T' p w (Fin.last D.R.rS) (Fin.last D.R.rS) =
        blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w) ∧
      IsUnit (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w) +
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep)))

theorem add_cornE_zero (p : PlF D) (X : MatP D p) : X + cornE p 0 = X := by
  ext a b; simp [cornE]

theorem loUp_of_hyp {p : PlF D} {uL uU : MatP D p} (h1 : ∀ a, uL a a = 1 ∧ uU a a = 1)
    (h2 : ∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) : IsLo uL ∧ IsUp uU :=
  ⟨⟨fun a => (h1 a).1, fun a b hab => (h2 a b hab).1⟩, ⟨fun a => (h1 a).2, fun a b hab => (h2 a b hab).2⟩⟩

set_option maxHeartbeats 1000000 in

theorem partnerIsomorphismCount_of_bounds (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd) (hL : LeadZZ Zd) (hK : ModKind Zd) (hB : BridgeBA) :
    PartnerIsomorphismCount Zd := by
  intro p T T' w w' t₁ f₂' φ φ' hk hT hT' hyp h1 h2 hint2
  have hkd : (Dmin w D.R.rS = 0 ↔ Dmin w' D.R.rS = 0) := by
    have hk' := hk
    unfold kind at hk'
    constructor
    · intro h; by_contra h'; rw [if_pos h, if_neg h'] at hk'; exact absurd hk' (by simp)
    · intro h; by_contra h'; rw [if_neg h', if_pos h] at hk'; exact absurd hk' (by simp)
  obtain ⟨uL, uU, hd, ho, hP1⟩ := h1
  obtain ⟨uL', uU', hd', ho', hP2⟩ := h2
  obtain ⟨hLo, hUp⟩ := loUp_of_hyp hd ho
  obtain ⟨hLo', hUp'⟩ := loUp_of_hyp hd' ho'
  have hT2p := hT2 _ _ (Zd.M p) (Zd.agree p).1 (Vp D p) (locH Zd p) (finrank_Vp p) t₁ hyp.1 t₁.f f₂' φ φ'
    hyp.2.1 hyp.2.2.1 hyp.2.2.2.1 hyp.2.2.2.2.1 hyp.2.2.2.2.2
  dsimp only at hT2p
  have hint1 : ∀ a b, (locH Zd p).ZZplus t₁ a b ∈ (Zd.M p).R := hI p t₁ hyp.1
  have hLZ1 := hL p ((locH Zd p).Zhat t₁.f t₁.f') t₁.T t₁.T'
  have hLZ2 := hL p ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T'
  have hlead1 : leadM ((locH Zd p).ZZplus t₁) D.R.rS = leadM (modMat Zd.δ T T' p w) D.R.rS := by
    rw [hP1]; exact leadM_mul hLo hUp _
  have hlead2 : leadM (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') D.R.rS =
      leadM (modMat Zd.δ T T' p w') D.R.rS := by
    rw [hP2]; exact leadM_mul hLo' hUp' _
  by_cases hD : Dmin w D.R.rS = 0
  · have hD' := hkd.1 hD
    have hsh : cornerSh Zd.δ T T' p w = 0 := by unfold cornerSh; rw [if_pos hD]
    have hsh' : cornerSh Zd.δ T T' p w' = 0 := by unfold cornerSh; rw [if_pos hD']
    have e1 : (locH Zd p).ZZplus t₁ + cornE p (cornerSh Zd.δ T T' p w) = (locH Zd p).ZZplus t₁ := by
      rw [hsh]; exact add_cornE_zero _ _
    have e2 : Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' + cornE p (cornerSh Zd.δ T T' p w') =
        Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' := by
      rw [hsh']; exact add_cornE_zero _ _
    rw [e1, e2]
    have hl1 : leadM ((locH Zd p).ZZplus t₁) D.R.rS = 0 := hlead1.trans ((hK p T T' w).1 hD)
    have hl2 : leadM (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') D.R.rS = 0 :=
      hlead2.trans ((hK p T T' w').1 hD')
    have hDl : (locH Zd p).Dl t₁.f t₁.f' D.R.rS = 0 := hLZ1.1.2 hl1
    have hu1 : IsUnit ((locH Zd p).ZZplus t₁).det := hLZ1.2.2 (hLZ1.1.2 hl1) hyp.1.1.2.2.2.1
    by_cases hu2 : IsUnit (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T').det
    · rw [clsOf_mk (Zd.M p) _ hint1 hu1, clsOf_mk (Zd.M p) _ hint2 hu2]
      show _ = (Zd.M p).nIso _ _
      rw [nIso_mk_out]
      exact hT2p.1 hDl _ _ rfl rfl
    · have hc2 : clsOf (Zd.M p) (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') = none := by
        unfold clsOf; rw [dif_neg (fun h => hu2 h.2)]
      rw [hc2]
      have h0 : ∀ o : Option ((Zd.M p).Cls D.R.rS), nIsoO Zd.M p o none = 0 := fun o => by cases o <;> rfl
      rw [h0, Nat.card_eq_zero]
      left
      constructor
      rintro ⟨Λ₂, hg, -⟩
      exact hu2 (hLZ2.2.2 (hLZ2.1.2 hl2) hg.1.2.2.2.1)
  · have hD' : Dmin w' D.R.rS ≠ 0 := fun h => hD (hkd.2 h)
    have hz : zetaOf w = zetaOf w' := by
      unfold kind at hk; rw [if_neg hD, if_neg hD'] at hk; exact Option.some_inj.1 hk
    obtain ⟨hu1, hcol1, hc1, hs1⟩ := (hK p T T' w).2 hD
    obtain ⟨hu2, hcol2, hc2, -⟩ := (hK p T T' w').2 hD'
    rw [← hz] at hc2
    have hsh : cornerSh Zd.δ T T' p w =
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) := by
      unfold cornerSh; rw [if_neg hD]
    have hsh' : cornerSh Zd.δ T T' p w' =
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) := by
      unfold cornerSh; rw [if_neg hD', ← hz]
    rw [hsh, hsh', cornE_eq]
    have hl1 : IsUnit (leadM ((locH Zd p).ZZplus t₁) D.R.rS) := hlead1 ▸ hu1
    have hl2 : IsUnit (leadM (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T') D.R.rS) :=
      hlead2 ▸ hu2
    have hDl : IsUnit ((locH Zd p).Dl t₁.f t₁.f' D.R.rS) := hLZ1.2.1.2 hl1
    have hcard := hT2p.2 hDl (headMat (Zd.M p) _ hint1 hl1) (headMat (Zd.M p) _ hint2 hl2)
      (fun a => ⟨(locH Zd p).ZZplus t₁ a.castSucc (Fin.last _), hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' a.castSucc (Fin.last _),
        hint2 _ _⟩)
      (fun a => ⟨(locH Zd p).ZZplus t₁ (Fin.last _) a.castSucc, hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' (Fin.last _) a.castSucc,
        hint2 _ _⟩)
      (fun a b => ⟨rfl, rfl⟩) (fun a => ⟨rfl, rfl, rfl, rfl⟩)
    obtain ⟨Z₁, Z₂, e₁, e₂, hb⟩ := hB (Zd.M p) D.R.rS _ _ _ _ _ _ _ _ _ _ hLo hUp hLo' hUp' hP1 hP2
      (fun a => ⟨(hcol1 a).1, (hcol1 a).2, (hcol2 a).1, (hcol2 a).2⟩) hc1 hc2 hs1
      (natCast_mem _ _) (headMat (Zd.M p) _ hint1 hl1) (headMat (Zd.M p) _ hint2 hl2)
      (fun a => ⟨(locH Zd p).ZZplus t₁ a.castSucc (Fin.last _), hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' a.castSucc (Fin.last _),
        hint2 _ _⟩)
      (fun a => ⟨(locH Zd p).ZZplus t₁ (Fin.last _) a.castSucc, hint1 _ _⟩)
      (fun a => ⟨Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' (Fin.last _) a.castSucc,
        hint2 _ _⟩)
      (fun a b => ⟨rfl, rfl⟩) (fun a => ⟨rfl, rfl, rfl, rfl⟩) hint1 hint2
    refine (show Nat.card (locSet Zd p t₁ f₂' φ φ') = _ from hcard).trans ?_
    have c1 : clsOf (Zd.M p) ((locH Zd p).ZZplus t₁ +
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) • Ecorner D.R.rS) =
        some (Quotient.mk ((Zd.M p).isoSetoid D.R.rS) Z₁) := by
      have h := clsOf_map (Zd.M p) Z₁; rw [e₁] at h; exact h
    have c2 : clsOf (Zd.M p) (Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat t₁.f f₂') t₁.T t₁.T' +
        ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (zetaOf w)) : ℕ) : (D.s.atP p).Ep) • Ecorner D.R.rS) =
        some (Quotient.mk ((Zd.M p).isoSetoid D.R.rS) Z₂) := by
      have h := clsOf_map (Zd.M p) Z₂; rw [e₂] at h; exact h
    exact hb.trans ((nIso_mk_out _ Z₁ Z₂).symm.trans (congrArg₂ (nIsoO Zd.M p) c1 c2).symm)

end Cut

end Formalism.L2.SG.Pf.PCount
end
end

