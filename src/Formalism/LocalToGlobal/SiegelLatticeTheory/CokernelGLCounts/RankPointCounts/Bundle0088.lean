import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0060
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0086
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0083
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0018
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0085

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIotaA
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem gS_typed (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) :
    ∃ w ∈ (D.s.atP p).O, ∃ w' ∈ (D.s.atP p).O,
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w ∧
        w * w' = 1 := by
  obtain ⟨sg, hsg, hq, -⟩ := typed_data Zd p g hs
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, (D.s.atP p).ιE (uP p : D.host.E),
    Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p, ?_, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ _
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg]
    simp only [Nat.cast_mul, map_mul, map_natCast]
  · rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [mul_inv_cancel₀ h0, map_one]

theorem localLattice_mono {A B : Submodule (𝓞 D.host.E) (VS D).V} (h : A ≤ B) : lattice₂ D Zd.M p A ≤ lattice₂ D Zd.M p B :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_O_M {a : (D.s.atP p).Ep} (ha : a ∈ (D.s.atP p).O) : a ∈ (Zd.M p).L.O := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.hO Zd p]; exact ha

theorem smul_gS_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    rw [← Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    have h1 : ((gS D : ℕ) : D.host.E) • y = ((gS D : ℕ) : 𝓞 D.host.E) • y := by
      rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) y, map_natCast]
    rw [SetLike.mem_coe, h1]
    refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (o • v) = o • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) := by
      show _ • ((o : (D.s.atP p).Ep) • v) = (o : (D.s.atP p).Ep) • _
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ hv

theorem untyped_mem (hs : (Zd.M p).split = none) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  have e := Formalism.L2.SG.Pf.StabIntSh.gS_mul_uP Zd.δ Zd.M Zd.agree p hs
  have hv' : v = (D.s.atP p).ιE (uP p : D.host.E) • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) := by
    rw [smul_smul, mul_comm, e, one_smul]
  rw [hv']
  exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p) (smul_gS_mem Zd p F F' hv)

theorem typed_q_mem (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') {v : Vp D p}
    (hv : v ∈ lattice₂ D Zd.M p Λ) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  obtain ⟨w, -, w', hw', he, hww⟩ := gS_typed Zd p g hs
  have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v =
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (w' • v) := by
    rw [he, smul_smul, mul_assoc, hww, mul_one]
  rw [e]
  exact smul_gS_mem Zd p F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p hw' hv)

theorem l1 {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T' : D.host.E} (G : LFlag (VS D) D.R.rS T')
    (f : Fin (D.R.rS + 1) → Vp D p) (s : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hs : ∀ a, s a ∈ (D.s.atP p).O)
    (hf : ∀ i : Fin D.R.rS, f i.castSucc = (s i.castSucc * frFac Zd.δ p i.castSucc) • baseChange₂ D p (G.fl.e i))
    (hprim : (locH Zd p).Prim (lattice₂ D Zd.M p Λ) f) (hXS : XLam Λ G = XS D G.fl) {v : Vp D p}
    (hv : v ∈ lattice₂ D Zd.M p Λ) (hvX : v ∈ (locH Zd p).X f) : v ∈ lattice₂ D Zd.M p (XLam Λ G) := by
  have hvE : v ∈ Submodule.span (D.s.atP p).Ep (Set.range f) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _) hvX
  have hvO := hprim.2.2 v hv hvE
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Zd.M p).L.O).1 hvO
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun (D.s.atP p).Ep).1 hvX
  have key : (c (Fin.last D.R.rS) : (D.s.atP p).Ep) = 0 := by
    have h0 : ∑ a, ((c a : (D.s.atP p).Ep) - Fin.snoc (α := fun _ => (D.s.atP p).Ep) e 0 a) • f a = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc (f := fun a => Fin.snoc (α := fun _ => (D.s.atP p).Ep) e 0 a • f a)]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero]
      rw [he, ← hc, sub_eq_zero]
      rfl
    have := Fintype.linearIndependent_iff.1 hprim.2.1 _ h0 (Fin.last D.R.rS)
    simpa using this
  rw [← hc, Fin.sum_univ_castSucc]
  refine add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) ?_
  · rw [hf, hXS, Formalism.L2.SG.Pf.BBTie.bt_latP_XS Zd p (Formalism.L2.SG.Pf.locDiffC_holds D Zd) G.fl, mul_smul]
    have hm : frFac Zd.δ p i.castSucc • baseChange₂ D p (G.fl.e i) ∈ Submodule.span (Zd.M p).L.O
        (Set.range fun a : Fin D.R.rS => frFac Zd.δ p a.castSucc • baseChange₂ D p (G.fl.e a)) := Submodule.subset_span ⟨i, rfl⟩
    exact Submodule.smul_mem _ (⟨s i.castSucc, mem_O_M Zd p (hs _)⟩ : (Zd.M p).L.O) hm
  · have : c (Fin.last D.R.rS) • f (Fin.last D.R.rS) = 0 := by
      rw [Subring.smul_def, key, zero_smul]
    rw [this]; exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameActMemXplus
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem frameAct_mem_Xplus {T' : D.host.E} (G : LFlag (VS D) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (b : Fin (D.R.rS + 1)) :
    frameAct (frame G) ξ b ∈ G.fl.Xplus := by
  rw [SpanOmPf.Xplus_eq]
  show ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • frame G a ∈ _
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem form_zero (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {w : (VS D).V}
    (hw : w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus)) {v : (VS D).V}
    (hv : v ∈ F0.Xplus ⊔ (repF γ).fl.Xplus) (c : (D.s.atP p).Ep) :
    LocFacts₂ Zd.M p (baseChange₂ D p w) (c • baseChange₂ D p v) = 0 := by
  rw [LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, map_zero,
    mul_zero]

theorem baseChange_mem_W0 (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {w : (VS D).V}
    (hw : w ∈ orth (VS D) (F0.Xplus ⊔ (repF γ).fl.Xplus)) :
    baseChange₂ D p w ∈ (locH Zd p).W0 (tLoc Zd p γ).f (tLoc Zd p γ).f' := by
  show ∀ x ∈ (locH Zd p).Xp (tLoc Zd p γ).f ⊔ (locH Zd p).Xp (tLoc Zd p γ).f', (locH Zd p).h (baseChange₂ D p w) x = 0
  intro x hx
  rw [h_eq]
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  clear hx
  rw [LocFacts.localForm_add_right]
  have hA : LocFacts₂ Zd.M p (baseChange₂ D p w) a = 0 := by
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [tf]
      refine form_zero Zd p γ hw (Submodule.mem_sup_left ?_) _
      rw [SpanOmPf.Xplus_eq]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact LocFacts.localForm_zero_right Zd p _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
    | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]
  clear ha
  have hB : LocFacts₂ Zd.M p (baseChange₂ D p w) b = 0 := by
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [tf']
      exact form_zero Zd p γ hw (Submodule.mem_sup_right (frameAct_mem_Xplus _ _ i)) _
    | zero => exact LocFacts.localForm_zero_right Zd p _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
    | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]
  rw [hA, hB, add_zero]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioMap
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

abbrev GG (p : PlF D) : Type := GLp p × (GLp p)ᵐᵒᵖ

def KP (p : PlF D) : Subgroup (GG p) where
  carrier := {x | Formalism.MainNotions.S.TieN.IntLow (M p) ((x.1 : GLp p) : MP p) ∧
    Formalism.MainNotions.S.TieN.IntUp (M p) ((x.2.unop : GLp p) : MP p)}
  one_mem' := ⟨ZsVolGrp.intLow_one _, ZsVolGrp.intUp_one _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (((x.1 * y.1 : GLp p)) : MP p)
      rw [Units.val_mul]; exact ZsVolGrp.intLow_mul _ hx1 hy1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) (((x.2 * y.2).unop : GLp p) : MP p)
      rw [MulOpposite.unop_mul, Units.val_mul]; exact ZsVolGrp.intUp_mul _ hy2 hx2
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (((x.1)⁻¹ : GLp p) : MP p)
      rw [Matrix.coe_units_inv]; exact (ZsVolGrp.intLow_inv _ hx1).1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) ((((x.2)⁻¹).unop : GLp p) : MP p)
      rw [MulOpposite.unop_inv, Matrix.coe_units_inv]; exact (ZsVolGrp.intUp_inv _ hx2).1

def StabX (p : PlF D) (X : MP p) : Subgroup (GG p) where
  carrier := {x | ((x.1 : GLp p) : MP p) * X * ((x.2.unop : GLp p) : MP p) = X}
  one_mem' := by simp
  mul_mem' := by
    rintro x y hx hy
    show ((x.1 * y.1 : GLp p) : MP p) * X * (((x.2 * y.2).unop : GLp p) : MP p) = X
    rw [MulOpposite.unop_mul, Units.val_mul, Units.val_mul]
    calc (x.1 : MP p) * (y.1 : MP p) * X * (((y.2.unop : GLp p) : MP p) * ((x.2.unop : GLp p) : MP p))
        = (x.1 : MP p) * ((y.1 : MP p) * X * ((y.2.unop : GLp p) : MP p)) * ((x.2.unop : GLp p) : MP p) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [show (y.1 : MP p) * X * ((y.2.unop : GLp p) : MP p) = X from hy]; exact hx
  inv_mem' := by
    rintro x hx
    have hx' : ((x.1 : GLp p) : MP p) * X * ((x.2.unop : GLp p) : MP p) = X := hx
    show (((x.1)⁻¹ : GLp p) : MP p) * X * ((((x.2)⁻¹).unop : GLp p) : MP p) = X
    rw [MulOpposite.unop_inv]
    have h1 : (((x.1)⁻¹ : GLp p) : MP p) * (x.1 : MP p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : ((x.2.unop : GLp p) : MP p) * (((x.2.unop)⁻¹ : GLp p) : MP p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    conv_lhs => rw [← hx']
    calc (((x.1)⁻¹ : GLp p) : MP p) * ((x.1 : MP p) * X * ((x.2.unop : GLp p) : MP p)) *
          (((x.2.unop)⁻¹ : GLp p) : MP p)
        = ((((x.1)⁻¹ : GLp p) : MP p) * (x.1 : MP p)) * X *
            (((x.2.unop : GLp p) : MP p) * (((x.2.unop)⁻¹ : GLp p) : MP p)) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

variable {p : PlF D}

def g0 (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) : GG p :=
  (⟨lOf δ M p L U, lOf δ M p L⁻¹ U⁻¹,
      (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp (lp_inv M δ hA L U hL hU), lp_inv M δ hA L U hL hU⟩,
    MulOpposite.op ⟨ρOf δ M p L U, ρOf δ M p L⁻¹ U⁻¹, up_inv M δ hA L U hL hU,
      (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp (up_inv M δ hA L U hL hU)⟩)

def XP (w : Point D.host.E (D.R.rS + 1)) (L U : Formalism.L2.SG.PairVal.MatR D) : MP p :=
  lOf δ M p L U * Y0 M δ u u' w p * ρOf δ M p L U

def Ag (w : Point D.host.E (D.R.rS + 1)) : Subgroup (GG p) := (AP M δ u u' w p).map (StP M δ u u' w p).subtype

def Cg (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) : Subgroup (GG p) :=
  (CPL M δ u u' w hA L U hL hU).map (StP M δ u u' w p).subtype

theorem idxRatio_map {G : Type} [Group G] (S : Subgroup G) (A C : Subgroup S) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio A C = Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A.map S.subtype) (C.map S.subtype) := by
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [Subgroup.relIndex_map_map_of_injective _ _ S.subtype_injective,
    Subgroup.relIndex_map_map_of_injective _ _ S.subtype_injective]

def CShapeAt (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) : Prop :=
  Cg M δ u u' w hA L U hL hU = cj (g0 M δ hA L U hL hU) (KP M p ⊓ StabX p (XP M δ u u' w L U))

def CountAt (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) (v : ℝ) : Prop :=
  ∃ (N : Subgroup (GG p)) (π : GG p → GG p) (hR : Retr (StP M δ u u' w p) N π)
    (hHN : KP M p ⊓ StabX p (XP M δ u u' w L U) ≤ N),
    g0 M δ hA L U hL hU ∈ N ∧ img hR _ hHN ≤ Ag M δ u u' w ∧ (img hR _ hHN).relIndex (Ag M δ u u' w) ≠ 0 ∧
      v = ((img hR _ hHN).relIndex (Ag M δ u u' w) : ℝ)

def OverAt (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  ∀ s ∈ StP M δ u u' w p, ∃ B' : Subgroup (GG p), Ag M δ u u' w ≤ B' ∧ s ∈ B' ∧ (Ag M δ u u' w).relIndex B' ≠ 0

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def StepsC : Prop :=
  ∀ (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D),
    CShapeAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1 ∧
    CountAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
      (Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)) ∧
    OverAt M δ u u' (p := p) w

end Formalism.L2.SG.Pf.ProdEP2Cut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaG3OfCoefficients
section
noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem lemmaG3_of_coefficients (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0)
    (h2 : Gt t2 ≠ 0) (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) (hG1 : t1.G = t0.G) (hG2 : t2.G = t0.G)
    (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u')))
    (he : t2.lin = σ * t1.lin * s') (ha : coefA Y u u' t0 t1 = coefA Y u u' t0 t2)
    (ha' : coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2) :
    nmlOf Y u u' t1 = nmlOf Y u u' t2 := by
  obtain ⟨iω, iς, i3⟩ := lemmaG3_of_inputs Y hT hT' t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 σ s' hσ hs' he ha ha'
  have hγ1 : t1.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t1.rep.2.2.1
  have hGF1 : Gflag (X.Fu u) t1.frame.fl ≠ 0 := G_ne_of_Gt Y h1
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hσ' := SRat_inv (lf D (X.Fu u)) hσ
  have hs'' := SRat_inv (lf D (X.Fu u')) hs'
  set ς := t1.lin * s'⁻¹ * t1.lin⁻¹ with hς
  have hςx : ∀ x, ς x = t1.lin (s'.symm (t1.lin.symm x)) := fun x => rfl
  have hςf : ∀ x ∈ t1.frame.fl.X, ς x - x ∈ t1.frame.fl.X := by
    intro x hx
    refine (mem_frameX Y t1 _).2 ?_
    have hx0 := (mem_frameX Y t1 x).1 hx
    rw [map_sub, hςx, LinearEquiv.symm_apply_apply]
    exact Submodule.sub_mem _ (X_pres (lf D (X.Fu u')) hs''.2.1 _ hx0) hx0
  have hςz : ς t1.frame.fl.z - t1.frame.fl.z ∈ t1.frame.fl.X := by
    refine (mem_frameX Y t1 _).2 ?_
    rw [map_sub, hςx, LinearEquiv.symm_apply_apply, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply]
    exact hs''.2.2
  obtain ⟨τ, hτi, hτA, P1, P2⟩ := tau_exists (X.Fu u) t1.frame.fl hGF1 hTE (star_natCast _) hTE' (star_natCast _)
    σ ς hσ.1 (fun x hx => Submodule.sub_mem _ (X_pres (lf D (X.Fu u)) hσ.2.1 x hx) hx)
    (fun x hx => X_pres (lf D (X.Fu u)) hσ'.2.1 x hx) hσ.2.2 hςf hςz iω iς i3
  have hτX : ∀ x ∈ (X.Fu u).X, τ x = x := fun x hx => hτA x (X_le_Asp _ _ hx)
  have hτX1 : ∀ x ∈ t1.frame.fl.X, τ x = x := fun x hx => hτA x (by rw [← Asp_symm]; exact X_le_Asp _ _ hx)
  have hτs : ∀ x ∈ (X.Fu u).X, τ.symm x = x := fun x hx => by
    conv_lhs => rw [← hτX x hx]
    simp
  set n := σ * τ⁻¹ with hn
  set n' := t1.lin⁻¹ * τ * t1.lin * s' with hn'
  have hnN : n ∈ NRat (lf D (X.Fu u)) := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem hσ.1 ((Formalism.HermitianLatticesTheory.isom _).inv_mem hτi), fun j x hx => ?_, fun y hy => ?_⟩
    · have hxX : x ∈ (X.Fu u).X := Xflag_le_X (lf D (X.Fu u)) (j + 1) hx
      show σ (τ.symm x) - x ∈ _
      rw [hτs x hxX]
      exact hσ.2.1 j x hx
    · have hτi' : τ.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom _).inv_mem hτi
      have hz : τ.symm y ∈ orth (VS D) (Xsp (lf D (X.Fu u))) :=
        perp_pres (lf D (X.Fu u)) hτi' (fun x hx => by rw [LinearEquiv.symm_symm, hτX x hx]; exact hx) y hy
      have := P1 _ hz
      rw [LinearEquiv.apply_symm_apply] at this
      show σ (τ.symm y) - y ∈ _
      rw [← neg_sub]
      exact Submodule.neg_mem _ this
  have hn'N : n' ∈ NRat (lf D (X.Fu u')) := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem
      ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ1) hτi) hγ1) hs'.1, fun j x hx => ?_, fun y hy => ?_⟩
    · have hxX : x ∈ (X.Fu u').X := Xflag_le_X (lf D (X.Fu u')) (j + 1) hx
      have hsx : s' x ∈ (X.Fu u').X := X_pres (lf D (X.Fu u')) hs'.2.1 x hxX
      have h1x : t1.lin (s' x) ∈ t1.frame.fl.X := (mem_frameX Y t1 _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hsx)
      show t1.lin.symm (τ (t1.lin (s' x))) - x ∈ _
      rw [hτX1 _ h1x, LinearEquiv.symm_apply_apply]
      exact hs'.2.1 j x hx
    · have hsy : s' y ∈ orth (VS D) (Xsp (lf D (X.Fu u'))) :=
        perp_pres (lf D (X.Fu u')) hs'.1 (fun x hx => X_pres (lf D (X.Fu u')) hs''.2.1 x hx) y hy
      have hv : t1.lin (s' y) ∈ Lat.orth (VS D) t1.frame.fl.X := by
        refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun x hx => ?_
        rw [show x = t1.lin (t1.lin.symm x) by simp, hγ1]
        exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).1 hsy _ ((mem_frameX Y t1 x).1 hx)
      have h := P2 _ hv
      rw [hςx, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h
      have h' := (mem_frameX Y t1 _).1 h
      rw [map_sub, LinearEquiv.symm_apply_apply] at h'
      exact h'
  have heq : t2.lin = n * t1.lin * n' := by
    rw [he, hn, hn']
    group
  ext δ
  constructor
  · rintro ⟨m, hm, m', hm', rfl⟩
    refine ⟨m * n⁻¹, NRat_mul _ hm (NRat_inv _ hnN), n'⁻¹ * m', NRat_mul _ (NRat_inv _ hn'N) hm', ?_⟩
    rw [heq]
    group
  · rintro ⟨m, hm, m', hm', rfl⟩
    refine ⟨m * n, NRat_mul _ hm hnN, n' * m', NRat_mul _ hn'N hm', ?_⟩
    rw [heq]
    group

theorem normalsLemmaG3_holds : UnitaryNormalVectorCount := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hc t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 hσs ha ha' => ?_⟩
  obtain ⟨σ, hσ, s', hs', he⟩ := hσs
  have hT : 3 ≤ Tu D u ∧ 3 ≤ Tu D u' := by
    clear * - hc
    unfold Ctx at hc
    obtain ⟨-, -, -, h3, h3', -⟩ := hc.2.1
    exact ⟨h3, h3'⟩
  exact lemmaG3_of_coefficients Y hT.1 hT.2 t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 σ s' hσ hs' he ha ha'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SpanOmHolds
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open SpanOmPf in

theorem spanOm_holds (D : Formalism.BasicNotions.D7) : SpanOm D := by
  intro T T' F F' hdet hG m hm
  set ω := Gom F.fvec F'.fvec with hω
  set Dd := GDl F.fvec F'.fvec (D.R.rS + 1) with hDd
  set Dr := GDl F.fvec F'.fvec D.R.rS with hDr
  have hD : Dd ≠ 0 := by rw [hDd, GDl_top', SpanOmPf.GZ_eq]; exact hdet
  have hG' : Dd * star Dd - T * T' * (Dr * star Dr) ≠ 0 := by
    rw [hDd, hDr, SpanOmPf.GDl_eq, SpanOmPf.GDl_eq]; exact hG
  set W0 := orth (VS D) (F.Xplus ⊔ F'.Xplus) with hW0
  set U := F'.X ⊔ W0 ⊔ Submodule.span D.host.E {F'.z, ω} with hU
  have key : ∀ u ∈ orth (VS D) U, u ∈ F'.X := by
    intro u hu
    rw [PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth] at hu
    have h1 : ∀ y ∈ F'.X, (VS D).hT y u = 0 := fun y hy =>
      hu y (Submodule.mem_sup_left (Submodule.mem_sup_left hy))
    have h2 : ∀ w ∈ W0, (VS D).hT w u = 0 := fun w hw =>
      hu w (Submodule.mem_sup_left (Submodule.mem_sup_right hw))
    have h3 : (VS D).hT F'.z u = 0 :=
      hu _ (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _)))
    have h4 : (VS D).hT ω u = 0 :=
      hu _ (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
    have hP : u ∈ F.Xplus ⊔ F'.Xplus :=
      BwdNA.mem_of_orth_orth (VS D) _ (fun w hw => by rw [SpanOmPf.hsw', h2 w hw, star_zero])
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hP
    obtain ⟨y', hy', s, hs, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hs
    have hxX : ∀ y0 ∈ F'.X, (VS D).hT y0 x = 0 := by
      intro y0 hy0
      have := h1 y0 hy0
      rw [map_add, map_add, SpanOmPf.iso_X F' hy0 hy', map_smul, SpanOmPf.isotropicSpan_orthogonal_anisotropicVector F' hy0, smul_zero, add_zero, add_zero] at this
      exact this
    obtain ⟨c, rfl⟩ := SpanOmPf.om_uniq F F' hD (by rw [← SpanOmPf.Xplus_eq]; exact hx) hxX
    have hzo : (VS D).hT F'.z ω = star Dd := by rw [SpanOmPf.hsw', SpanOmPf.omega_hermitian_z]
    have e3 : c * star Dd + β * -T' = 0 := by
      have := h3
      rw [map_add, map_add, map_smul, map_smul, hzo, SpanOmPf.z_orth_X F' hy', F'.z_norm, smul_eq_mul, smul_eq_mul,
        zero_add] at this
      exact this
    have e4 : c * (-T * (Dr * star Dr)) + β * Dd = 0 := by
      have := h4
      rw [map_add, map_add, map_smul, map_smul, SpanOmPf.om_om, SpanOmPf.om_X' F F' hy', SpanOmPf.omega_hermitian_z, smul_eq_mul, smul_eq_mul,
        zero_add] at this
      exact this
    have hc : c = 0 := by
      have hcG : c * (Dd * star Dd - T * T' * (Dr * star Dr)) = 0 := by
        linear_combination Dd * e3 + T' * e4
      exact (mul_eq_zero.1 hcG).resolve_right hG'
    have hβ : β = 0 := by
      rw [hc] at e4
      have : β * Dd = 0 := by linear_combination e4
      exact (mul_eq_zero.1 this).resolve_right hD
    rw [hc, hβ, zero_smul, zero_smul, add_zero, zero_add]
    exact hy'
  have hmU : m ∈ U := BwdNA.mem_of_orth_orth (VS D) U (fun u hu => by
    rw [SpanOmPf.hsw', (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm u (key u hu), star_zero])
  obtain ⟨y, hy, s, hs, rfl⟩ := Submodule.mem_sup.1 hmU
  obtain ⟨x', hx', w, hw, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hs
  exact ⟨x', hx', w, hw, a, b, by abel⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

