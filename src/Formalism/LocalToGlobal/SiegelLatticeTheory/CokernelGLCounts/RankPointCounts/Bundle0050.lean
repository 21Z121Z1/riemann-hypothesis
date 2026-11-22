import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0048
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0012
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0028
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.P2MemZ2OfMemZ2
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0047
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0029
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0016

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PhaseLiftCell
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting

noncomputable section

namespace Formalism.L2.SG.Pf.PhaseLiftCell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem realLink' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (v : InfinitePlace X.B.I.F) :
    Formalism.L2.SG.RealObj.ZhatO (Formalism.L2.SG.RealObj.ZX X u u' 1 s.pt.1 v) =
      (ZhatOM (ZhatL (lf D (X.Fu u)) s.frame)).map (fun x => X.B.I.φ v (X.ιE.symm x)) := by
  obtain ⟨M, _, hM1, _, hM3⟩ := s.rep.2.1
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hfam : ∀ (w : D.what₂.Word) (a : Fin (D.R.rS + 1)),
      Formalism.L2.SG.RealObj.fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) a =
        rv X.B.I v (X.crd ((X.Fu w).fvec a)) := by
    intro w a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp [Formalism.L2.SG.RealObj.fam, FlagG.fvec, X.flagZVector w, HidaSetting.zR]
    · simp [Formalism.L2.SG.RealObj.fam, FlagG.fvec, X.Fu_e w, HidaSetting.eR]
  ext a b
  simp only [Formalism.L2.SG.RealObj.ZhatO, ZhatOM, Formalism.L2.SG.RealObj.ZX, Formalism.L2.SG.RealObj.Zhat,
    Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc, Matrix.map_apply, Complex.ofReal_one, one_pow, inv_one,
    one_smul]
  rw [hfam u a, hfam u' b]
  have h1 : Formalism.MainNotions.S.uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
      X.B.I.P v := hM1 v
  rw [h1, Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3, Formalism.L2.SG.PoincareInHH.Cut.hJ_crd]
  have h2 : ZhatL (lf D (X.Fu u)) s.frame a b = (VS D).hT ((X.Fu u).fvec a) (s.lin ((X.Fu u').fvec b)) := by
    rw [← Formalism.L2.SG.Pf.Act.frame_mapLF hiso (X.Fu u') b]
    rfl
  rw [h2, map_mul, map_mul]
  simp only [map_pow, map_neg, map_one]
  rw [X.φ_eq, RingEquiv.apply_symm_apply]
  rfl

theorem liftCell_of_atSome {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (h1 : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ) : Formalism.L2.SG.Pf.FinitePhase.LiftCellC X Y u u' κ := by
  intro R ρ s hrel
  obtain ⟨w0, hw0⟩ := h1 R ρ s hrel
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) :=
    Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hcell := ((Formalism.L2.SG.TermDef.atPt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _) (Formalism.L2.SG.Pf.cell_function_holds _ _ _)
    ⟨s.1.frame, s.1.rep.2.2.2.2⟩ _).1 hat).2
  obtain ⟨L, U, hL, hU, hLU⟩ := hcell
  refine ⟨L, U, hL, hU, hLU, fun v => ?_⟩
  rw [realLink' X u u' s.1 v]
  exact congrArg (fun Z => Z.map (fun x => X.B.I.φ v (X.ιE.symm x))) hLU

theorem phaseAgreement_of_lift {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (h1 : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ) (hF : Formalism.L2.SG.Pf.FinitePhase.FinPhaseC X Y u u' κ) :
    Formalism.L2.SG.Pf.RowForm.PhaseTieC X Y u u' κ :=
  Formalism.L2.SG.Pf.FinitePhase.phaseTieC_of X Y u u' κ (liftCell_of_atSome X Y u u' κ h1) hF

end Formalism.L2.SG.Pf.PhaseLiftCell
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RhoTieCHolds
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Final

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem weight_eq (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (h : Hfin X u) :
    ((Nat.card ↥(gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom) : ℕ) : ℝ)⁻¹ =
      wRow D (X.Fu u) (cls X u what₂ h) := by
  obtain ⟨-, δ, hδ, hδe⟩ := cls_spec hR hL h
  have e1 : Nat.card ↥(gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom) =
      Nat.card ↥(autLz D (X.Fu u) (cls X u what₂ h)) := by
    rw [show gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom = stabR X u h from rfl, card_stab, card_AH,
      ← hδe, card_autLz_gmap (X.Fu u) hδ]
  rw [e1]
  rfl

theorem massH_rows (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (hI : LatInj X u) (hS : LatSurj X u) :
    Formalism.L2.SG.TypedSets.massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (Formalism.L2.SG.TypedSets.frameOf X u) =
      Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) what₂ := by
  rw [massH_eq]
  exact massCl_eq_sum (gamR X u) (kR X u) what₂ (cls X u what₂) (wRow D (X.Fu u))
    (fun h => (cls_spec hR hL h).1) (cls_rel hR hL hI) (cls_surj hR hL hS) (weight_eq X u what₂ hR hL)

end Final

end Formalism.L2.SG.RhoPf

namespace Formalism.L2.SG.MassDataConc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Full MeasureTheory

theorem RhoTieC_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (i0 i0' : NumberField.InfinitePlace X.B.I.F → Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hL : Formalism.L2.SG.Pf.LatRowLat X u) (hI : Formalism.L2.SG.Pf.LatInj X u) (hS : Formalism.L2.SG.Pf.LatSurj X u) :
    RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq :=
  Formalism.L2.SG.RhoPf.massH_rows X u (Y.what₂ u) (Y.rowsOK u) hL hI hS

end Formalism.L2.SG.MassDataConc
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabApprox
section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem locTarget (Zd : LocDat D) (u u' : D.what₂.Word) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    {Z₁ L₁ U₁ A₀ B₀ : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀) {l ρ : MatP D p}
    (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
      l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) :
    LocTarget Zd p w L₁ U₁ A₀ B₀ := by
  rcases hM : (Zd.M p).split with _ | g
  · exact target_L Zd u u' p hM w hL₁ hU₁ hZ hA₀ hB₀ hl hρ h
  · exact target_G Zd u u' p hM w hL₁ hU₁ hZ hA₀ hB₀ hl hρ h

theorem cf_int (Zd : LocDat D) (p : PlF D) (hδ1 : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hδ2 : (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) (hu1 : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O)
    (hu2 : (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) :
    (∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) ∈ (D.s.atP p).O) ∧
      ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) ∈ (D.s.atP p).O := by
  have e1 : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((uP p : ℚ) : D.host.F)) := by
    rw [← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]
  have e2 : (D.s.atP p).ιE (((uP p : ℚ) : D.host.E)⁻¹) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((D.s.atP p).ιF ((uP p : ℚ) : D.host.F))⁻¹) := by
    rw [← map_inv₀ (D.s.atP p).ιF, ← (D.s.atP p).compat, map_inv₀ (algebraMap D.host.F D.host.E),
      map_ratCast (algebraMap D.host.F D.host.E)]
  have hy : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p) ∈ (D.s.atP p).O := by
    unfold yP
    rw [map_mul, ← e1]
    exact (D.s.atP p).O.mul_mem (LocModel.LM.algebraMap_mem_O p hδ1) hu1
  have hyi : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p)⁻¹ ∈ (D.s.atP p).O := by
    unfold yP
    rw [mul_inv, map_mul, ← e2]
    exact (D.s.atP p).O.mul_mem (LocModel.LM.algebraMap_mem_O p hδ2) hu2
  exact ⟨fun a => by unfold cf; rw [map_pow]; exact pow_mem hyi _,
    fun a => by unfold cfi; rw [map_pow]; exact pow_mem hy _⟩

theorem stabApprox (Zd : LocDat D) (u u' : D.what₂.Word) : Formalism.L2.SG.Pf.TupGlob.StabApprox Zd u u' := by
  intro w Z₁ A₀ B₀ hAt hA₀ hB₀ hloc
  obtain ⟨L₁, U₁, hL₁u, hU₁u, e₁⟩ := hAt
  have hL₁ : IsLo L₁ := isLo_of_uni hL₁u
  have hU₁ : IsUp U₁ := isUp_of_uni hU₁u
  rw [zhatOM_eq] at e₁
  choose l ρ hl hρ hlr using hloc
  choose T c hc0 hT using fun p => locTarget Zd u u' p w hL₁ hU₁ e₁ hA₀ hB₀ (hl p) (hρ p) (hlr p)
  have hE : ∀ᶠ p in Filter.cofinite, ∀ (k : Fin 8) (i j : Fin (D.R.rS + 1)),
      (D.s.atP p).ιE ((![A₀, B₀, L₁, L₁⁻¹, U₁, U₁⁻¹, Matrix.of fun i _ => pv w.1 i,
        Matrix.of fun i _ => (pv w.1 i)⁻¹] : Fin 8 → PairVal.MatR D) k i j) ∈ (D.s.atP p).O :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      LocModel.LM.iotaIntegral_almost_all D _
  have hG := (LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅).and hE
  have hfin := Filter.eventually_cofinite.1 hG
  choose t ht1 ht2 using fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
    sa_lat D.s.atP hfin.toFinset (fun p => T p ij.1 ij.2) c (fun p _ => hc0 p)
  let X' : PairVal.MatR D := Matrix.of fun i j => if Free (fσ w) i j then t (i, j) else (1 : PairVal.MatR D) i j
  have hX'1 : ∀ i j, ¬ Free (fσ w) i j → X' i j = (1 : PairVal.MatR D) i j := fun i j h => by
    simp only [X', Matrix.of_apply, if_neg h]
  have hX'2 : ∀ i j, Free (fσ w) i j → X' i j = t (i, j) := fun i j h => by
    simp only [X', Matrix.of_apply, if_pos h]
  have hX' : IsLo X' :=
    ⟨fun a => by rw [hX'1 a a (fun h => lt_irrefl a h.1), Matrix.one_apply_eq],
      fun a b hab => by rw [hX'1 a b (fun h => absurd h.1 (not_lt.2 hab.le)), Matrix.one_apply_ne hab.ne]⟩
  have hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0 := fun i j hij => by
    have hf : ¬ Free (fσ w) i j := fun h => absurd h.2 (not_lt.2 hij.le)
    have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
    rw [hX'1 i j hf, Matrix.one_apply_ne hne]
  obtain ⟨hgX, hgY, hst⟩ := glob_stab w hL₁ hU₁ e₁ hX' hpat
  refine ⟨gX L₁ X', gY w U₁ X', hgX, hgY, hst, fun p => ?_⟩
  by_cases hp : p ∈ hfin.toFinset
  · exact hT p X' hX' hpat fun i j hf => by rw [hX'2 i j hf]; exact ht1 (i, j) p hp
  · have hgp : _ ∧ _ := not_not.1 ((Set.Finite.mem_toFinset hfin).not.1 hp)
    obtain ⟨⟨hM, ⟨hδ1, hδ2⟩, ⟨hu1, hu2⟩, -⟩, hEp⟩ := hgp
    obtain ⟨hcf, hcfi⟩ := cf_int Zd p hδ1 hδ2 hu1 hu2
    have hXi : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O := by
      intro i j
      by_cases hf : Free (fσ w) i j
      · rw [hX'2 i j hf]; exact ht2 (i, j) p hp
      · rw [hX'1 i j hf, Matrix.one_apply]
        split_ifs
        · rw [map_one]; exact Subring.one_mem _
        · rw [map_zero]; exact Subring.zero_mem _
    exact good_at Zd p hM w hL₁ hU₁ hA₀ hB₀ hX' hpat hcf hcfi
      (fun i j => hEp 0 i j) (fun i j => hEp 1 i j) (fun i j => hEp 2 i j) (fun i j => hEp 3 i j)
      (fun i j => hEp 4 i j) (fun i j => hEp 5 i j) (fun a => hEp 6 a a) (fun a => hEp 7 a a) hXi

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.XLeSpanRight
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section T2CR

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def ClaimRL (M : Model F E) (r n : ℕ) : Prop := M.split = none → ClaimR M r n

def ClaimRG (M : Model F E) (r n : ℕ) : Prop := M.split.isSome = true → ClaimR M r n

theorem claimR_of_modes (M : Model F E) (r n : ℕ) (hL : ClaimRL M r n) (hG : ClaimRG M r n) :
    ClaimR M r n := by
  rcases hs : M.split with _ | g
  · exact hL hs
  · exact hG (by rw [hs]; rfl)

theorem X_le_span_left {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.X f ≤ Submodule.span E (Set.range (Sum.elim f f')) :=
  Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inl j.castSucc, rfl⟩)

theorem X_le_span_right {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.X f' ≤ Submodule.span E (Set.range (Sum.elim f f')) :=
  Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inr j.castSucc, rfl⟩)

theorem surj_MMsharp (M : Model F E) (hM : M.OK) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {r : ℕ} (t : Term V M r) (hgen : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) :
    ∀ m : ↥(MMsharp H t), ∃ w : ↥(H.W0 t.f t.f'), (m : V) + w ∈ t.abelian₂ := by
  intro m
  have hU' : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f')))
      (H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f')))) := by
    rw [← hermSp_W0_eq_perp_span_range_MMfam]
    exact hU
  have hmU : (m : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := spanMM_le_U H t m.2.1
  obtain ⟨x, hx, hpx⟩ := ((local_hermitian_glue F E M hM V H t.abelian₂ hgen.1.1 _ hU').1 (m : V) hmU).2
    (fun y hy hyU => m.2.2 y (hgen.2.2.2 y hy (span_frames_le_MM H t hyU)))
  have hx' : x ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) ⊔
      H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f'))) := by
    rw [hU'.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx'
  have hpa : ((Submodule.linearProjOfIsCompl _ _ hU' x :
      ↥(Submodule.span E (Set.range (Sum.elim t.f t.f')))) : V) = a := by
    rw [← hab, map_add]
    have e1 := Submodule.projectionOnto_apply_left hU' ⟨a, ha⟩
    have e2 := Submodule.projectionOnto_apply_right hU' ⟨b, hb⟩
    simp only [Submodule.linearProjOfIsCompl] at *
    rw [e1, e2, add_zero]
  have hma : (m : V) = a := by rw [← hpx, hpa]
  have hbW : b ∈ H.W0 t.f t.f' := by rw [hermSp_W0_eq_perp_span_range_MMfam]; exact hb
  refine ⟨⟨b, hbW⟩, ?_⟩
  show (m : V) + b ∈ t.abelian₂
  rw [hma, hab]
  exact hx

theorem claimRL_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimRL M r n := by
  intro hs V _ _ H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  have hT₁ := hyp.1.1
  have hT₂ := hg.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT₁.2.1.2.1, hT₁.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT₁.2.2.1.2.1, hT₁.2.2.1.2.2.1⟩
  have hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)) := hT₂.2.2.2.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT₁.2.2.2.1
  obtain ⟨ψ, -, hψc⟩ := corrIso_holds M r n V H hn t₁ f₂ f₂' φ φ' hyp hD₂
  have hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f') :=
    isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ (isUnit_Gdet H _ _ _ _ hT₁.2.2.2.2.1)
  have hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim f₂ f₂'))) (H.W0 f₂ f₂') :=
    isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hyp.2.1 hyp.2.2.1 hD₂ (isUnit_Gdet H _ _ _ _ hT₂.2.2.2.2.1)
  have hMM₁ : MMo H t₁ ≤ t₁.abelian₂ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyp.1.2.1 i)
  have hMM₂ : MMo H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) ≤ Λ₂ :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hg.2.1 i)
  have hth' : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂ :=
    fun w => hth w (ψ w) ((hψc _ _).2 ⟨w.2, rfl⟩)
  have hθ' : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂ := by
    intro m₁ m₂
    rw [hθ m₁ m₂]
    constructor
    · rintro ⟨n₁, n₂, hc, h1, h2⟩
      obtain ⟨hn₁, hψn⟩ := (hψc _ _).1 hc
      exact ⟨⟨n₁, hn₁⟩, h1, by rw [hψn]; exact h2⟩
    · rintro ⟨w, h1, h2⟩
      exact ⟨w, ψ w, (hψc _ _).2 ⟨w.2, rfl⟩, h1, h2⟩
  have hsurj₁ := surj_MMsharp M hM H t₁ hyp.1 hU₁

  have hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW f₂ ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp H (ψ w).2⟩ := by
    intro w
    obtain ⟨_, _, c₁, _⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
    exact c₁
  have hC1' : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW f₂' ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp' H (ψ w).2⟩ := by
    intro w
    obtain ⟨_, _, _, c₂⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
    exact c₂
  have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
  have hZ₁' : IsUnit (H.Zhat t₁.f' t₁.f).det := det_Zhat_swap_unit H _ _ hZ₁
  have hzφ : φ (H.mkW t₁.f ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩) =
      H.mkW f₂ ⟨f₂ (Fin.last r), z_mem_perpX H hyp.2.1⟩ := by
    have e := hyp.2.2.2.2.1 ⟨_, z_mem_perpX H hF₁⟩ ⟨_, z_mem_perpX H hyp.2.1⟩ rfl rfl
    simpa using e
  have hzφ' : φ' (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perpX H hF₁'⟩) =
      H.mkW f₂' ⟨f₂' (Fin.last r), z_mem_perpX H hyp.2.2.1⟩ := by
    have e := hyp.2.2.2.2.2 ⟨_, z_mem_perpX H hF₁'⟩ ⟨_, z_mem_perpX H hyp.2.2.1⟩ rfl rfl
    simpa using e
  obtain ⟨u, hu⟩ := hD₂
  have hoφ : φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
      ((↑u⁻¹ : E) * H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ := by
    have e : H.Dl f₂ f₂' (r + 1) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
        H.Dl t₁.f t₁.f' (r + 1) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.1 _ _ rfl rfl
    rw [← hu] at e
    calc φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)
        = (↑u⁻¹ : E) • ((u : E) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  obtain ⟨u', hu'⟩ : IsUnit (M.L.cj (H.Dl f₂ f₂' (r + 1))) := by rw [← hu]; exact (Units.isUnit u).map _
  have hoφ' : φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
      ((↑u'⁻¹ : E) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ := by
    have e : M.L.cj (H.Dl f₂ f₂' (r + 1)) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
        M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.2.1 _ _ (om'_swap H _ _) (om'_swap H _ _)
    rw [← hu'] at e
    calc φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)
        = (↑u'⁻¹ : E) • ((u' : E) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  have hC2 := cond_second_of_iso H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T hF₁ hyp.2.1 hZ₁ φ _ hzφ hoφ
  have hC2'' := cond_second_of_iso H t₁.f' t₁.f f₂' f₂ t₁.T' t₁.T' hF₁' hyp.2.2.1 hZ₁' φ' _ hzφ' hoφ'
  have hC2' : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f'),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')), ∃ hu' : u' ∈ H.perp (H.X f₂'),
        φ' (H.mkW t₁.f' ⟨u, hu⟩) = H.mkW f₂' ⟨u', hu'⟩ := by
    intro v hv hvp
    rw [← U_swap] at hv
    obtain ⟨v', hv', hv'p, e⟩ := hC2'' v hv hvp
    rw [U_swap] at hv'
    exact ⟨v', hv', hv'p, e⟩
  have hL := claimR_side H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ hU₂ hU₁ hT₁.1 hT₂.1 hMM₁ hMM₂ hth' θ hθ' hsurj₁
    t₁.f f₂ (X_le_span_left H f₂ f₂') (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp H h) (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp H h) φ hC1 hC2
  have hL' := claimR_side H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ hU₂ hU₁ hT₁.1 hT₂.1 hMM₁ hMM₂ hth' θ hθ' hsurj₁
    t₁.f' f₂' (X_le_span_right H f₂ f₂') (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp' H h) (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp' H h) φ' hC1' hC2'
  constructor
  · intro hR
    refine ⟨fun _ => ⟨hL.1 hR.1, hL'.1 hR.2.2.1⟩, fun g hg => ?_⟩
    rw [hs] at hg
    exact absurd hg (by simp)
  · rintro ⟨h1, -⟩
    obtain ⟨a, b⟩ := h1 hs
    refine ⟨hL.2 a, hyp.2.2.2.2.1, hL'.2 b, hyp.2.2.2.2.2, fun g hg => ?_⟩
    rw [hs] at hg
    exact absurd hg (by simp)

end T2CR

end Formalism.L2.SG.LsDatumA
end
end

