import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhaseL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0035
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ScalKindPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUnramB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0038
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCountTh
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0047
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0049
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiProdE
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0037
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLocInB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0055
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GflagSwap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCutAt
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutAt_of_leaves {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hA : ∀ p, Agree δ M p) (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hP : PrimeHyp D u (Tu D u')) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hM : Formalism.L2.SG.Pf.NormRepMove D u u')
    (hPG : PhaseLocG M δ u u' F0 what₂) (hVP : VolIdxProd M δ u u' F0 what₂)
    (hE : PCount.ExistP ⟨δ, M, hA⟩ u u' F0 what₂) (hS : PCount.SumFrP ⟨δ, M, hA⟩ u u' F0 what₂)
    (hG : PCount.FrGlobP ⟨δ, M, hA⟩ u u' F0 what₂) (hI : PCount.IntGenP ⟨δ, M, hA⟩)
    (hτ : PCount.TauOneReduction ⟨δ, M, hA⟩ u u' F0 what₂) (hT : PCount.PartnerIsomorphismCount ⟨δ, M, hA⟩)
    (hFS : FCount.FibSum M δ u u' F0 what₂) (hDT : FCount.DensTh M δ L u u') :
    CutAt M δ L u u' F0 what₂ := by
  have hNR := normRepElig_of hN
  have hU := Formalism.L2.SG.Pf.locUnram_holds hA u u'
  have hR := Formalism.L2.SG.Pf.thRestricted_holds_of hA hrows hN PCount.eligRel_holds
  have hTS := Formalism.L2.SG.Pf.thSome_holds hA hc hrows hNR
  refine ⟨LocOrbSumPf.localOrbitSum_holds M δ u u' hA, Formalism.L2.SG.Pf.scalKind_of hrows,
    coefficient_product_of_local hA hc hrows hN hM (phaseLoc_of hA hPG) (psi_product_e D) hVP,
    Formalism.L2.SG.Pf.partnerCount_holds hA hc hrows hP hU hR hE hS hG hI hτ hT,
    FCount.fiberCount_of_rest hA hc hP hU hR hrows hN PCount.eligRel_holds (hE ⟨hc, hrows, hP⟩) hTS hFS
      nu_not_class_holds hDT (FCount.eligible_totally_positive u u' F0 what₂),
    hNR, hTS, ⟨LocModel.thTriv M, hU, hR⟩⟩

def CutLeaves (D : Formalism.BasicNotions.D7) : Prop :=
  (VS D).SigOK →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
      PairVal.NormRepExists D u u' F0 what₂ ∧ Formalism.L2.SG.Pf.NormRepMove D u u' ∧ PhaseLocG M δ u u' F0 what₂ ∧
      VolIdxProd M δ u u' F0 what₂ ∧ PCount.ExistP ⟨δ, M, hA⟩ u u' F0 what₂ ∧ PCount.SumFrP ⟨δ, M, hA⟩ u u' F0 what₂ ∧
      PCount.FrGlobP ⟨δ, M, hA⟩ u u' F0 what₂ ∧ PCount.IntGenP ⟨δ, M, hA⟩ ∧ PCount.TauOneReduction ⟨δ, M, hA⟩ u u' F0 what₂ ∧
      PCount.PartnerIsomorphismCount ⟨δ, M, hA⟩ ∧ FCount.FibSum M δ u u' F0 what₂ ∧ FCount.DensTh M δ L u u'

theorem rowsDatumP_of_leaves {D : Formalism.BasicNotions.D7} (h : CutLeaves D) : RowsDatumP D :=
  rowsDatumP_of fun hsig δ M hA L u u' hc hP F0 what₂ hrows =>
    have hl := h hsig δ M hA L u u' hc hP F0 what₂ hrows
    cutAt_of_leaves hA hc hP hrows hl.1 hl.2.1 hl.2.2.1 hl.2.2.2.1 hl.2.2.2.2.1 hl.2.2.2.2.2.1 hl.2.2.2.2.2.2.1
      hl.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2.2.2.2.2

theorem rowsInputP_of_leaves {D : Formalism.BasicNotions.D7} (hN : Formalism.L2.SG.SupportG.NormProd D) (h : CutLeaves D) :
    RowsInputP D :=
  rowsInputP_of_normProd hN (rowsDatumP_of_leaves h)

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaRep
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem repG_holds : RepG u u' F0 what₂ := by
  intro hC γ Z hZ
  obtain ⟨w, hγ, -⟩ := hZ
  have hN := normRepExists_ctx hC
  obtain ⟨⟨hgen, hG⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat (eligRel_holds γ w ⟨⟨hgen, hG⟩, hat⟩) hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hrep : repF γ = hex.choose.2.1 := by unfold repF; rw [hn]
  obtain ⟨⟨hPD, hmk⟩, -⟩ := hex.choose_spec
  refine ⟨⟨hex.choose.2.1, hPD⟩, hrep.symm, hmk, ?_⟩
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hrow
  have hrel := (hEq ⟨hex.choose.2.1, hPD⟩ (Quot.out γ.cls)).1 (hmk.trans (Quot.out_eq γ.cls).symm)
  have e := Formalism.L2.SG.Pf.g_value_function _ _ _ _ _ hrel
  exact fun h0 => hG (e.symm.trans h0)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaT
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace BwdBetaCut

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T T' : E}

theorem map_inf_equiv (A B : Submodule E S.V) :
    (A ⊓ B).map (β : S.V →ₗ[E] S.V) = A.map (β : S.V →ₗ[E] S.V) ⊓ B.map (β : S.V →ₗ[E] S.V) := by
  ext v
  simp only [Submodule.mem_inf, Submodule.mem_map_equiv]

theorem Xplus_mapL (F : LFlag S r T) : Xplus (mapL β hβ F) = (Xplus F).map (β : S.V →ₗ[E] S.V) := by
  simp only [Xplus, FlagG.Xplus]
  rw [Submodule.map_sup, ← Formalism.L2.SG.Pf.X_mapFlag β hβ, Submodule.map_span, Set.image_singleton]
  rfl

include hβ in
theorem Hp_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Hp (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = (Hp Λ F F').map (β : S.V →ₗ[E] S.V) := by
  rw [Hp, Hp, Formalism.L2.SG.Pf.UUE_mapL β hβ, Formalism.L2.SG.Pf.orth_map_sat β hβ]

include hβ in
theorem Ylift_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Ylift (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = (Ylift Λ F F').map (β : S.V →ₗ[E] S.V) := by
  rw [Ylift, Ylift, Formalism.L2.SG.Pf.UUE_mapL β hβ, Xplus_mapL β hβ, Formalism.L2.SG.Pf.orth_map_sat β hβ, map_inf_equiv]

include hβ in
theorem Ylift'_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Ylift' (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = (Ylift' Λ F F').map (β : S.V →ₗ[E] S.V) := by
  rw [Ylift', Ylift', Formalism.L2.SG.Pf.UUE_mapL β hβ, Xplus_mapL β hβ, Formalism.L2.SG.Pf.orth_map_sat β hβ,
    map_inf_equiv]

theorem sgRel_mapL (F : LFlag S r T) (F' : LFlag S r T') (y y' : S.V) (al al' : E) :
    SgRel (mapL β hβ F) (mapL β hβ F') (β y) (β y') al al' ↔ SgRel F F' y y' al al' := by
  simp only [SgRel, Formalism.L2.SG.Pf.Xsp_mapL β hβ, Formalism.L2.SG.Pf.zt_mapL]
  constructor
  · rintro ⟨x, hx, x', hx', h⟩
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨x0', hx0', rfl⟩ := Submodule.mem_map.1 hx'
    refine ⟨x0, hx0, x0', hx0', β.injective ?_⟩
    simp only [map_sub, map_add, map_smul, LinearEquiv.coe_coe] at h ⊢
    exact h
  · rintro ⟨x, hx, x', hx', h⟩
    refine ⟨β x, Submodule.mem_map_of_mem hx, β x', Submodule.mem_map_of_mem hx', ?_⟩
    rw [← map_sub, h]
    simp only [map_add, map_smul]

end Gen

end BwdBetaCut

open BwdCut BwdBetaCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdBetaCut

def IotaC₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (VS D) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ x' ∈ Lrep Λ F', ∀ l ∈ Lrep Λ F, ∀ l₂ ∈ Lrep Λ₂ F, l - l₂ ∈ Xsp F →
    (l - x' ∈ NgX Λ (gS D) F F' ↔ l₂ - β₂ x' ∈ NgX Λ₂ (gS D) F F₂)

def W0₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (VS D) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ w ∈ Hp Λ F F', ∃ w₂ ∈ Hp Λ₂ F F₂, w - w₂ ∈ Xsp F ∧ β₂ w - w₂ ∈ Xsp F₂

def Scalar₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (VS D) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ y1 ∈ Ylift Λ F F', ∀ y2 ∈ Ylift Λ₂ F F₂, ∀ y1' ∈ Ylift' Λ F F', ∀ y2'' ∈ Ylift' Λ₂ F F₂,
    y1 - y2 ∈ Xsp F → y2'' - β₂ y1' ∈ Xsp F₂ →
      ∀ al al' : D.host.E, SgRel F F' y1 y1' al al' ↔ SgRel F F₂ y2 y2'' al al'

def IsPair₂ (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {T' : D.host.E}
    (F' F₂ : LFlag (VS D) D.R.rS T') (β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  β₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap β₂ Λ = Λ₂ ∧
    (∀ j, (Xflag F' j).map (β₂ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag F₂ j) ∧ β₂ F'.fl.z = F₂.fl.z ∧
    IotaC₂ Λ Λ₂ F F' F₂ β₂ ∧ W0₂ Λ Λ₂ F F' F₂ β₂ ∧ Scalar₂ Λ Λ₂ F F' F₂ β₂

end BwdBetaCut

variable (u u' F0 what₂)

def BetaCore₂ : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', (∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) →
        TermHyp (F0 := F0) Λ₂ F'₂ → PD D γ.lam (lf D F0) u' (repF γ) → Gval (lf D F0) (repF γ) ≠ 0 →
        ∃ β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V, IsPair₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₂

variable {u u' F0 what₂}

namespace BwdBetaCut

theorem unipotent_preserves_x {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) :
    (Xsp (lf D F0)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp (lf D F0) := by
  have h := Formalism.L2.SG.Pf.Xsp_mapL n (isom_of_N0F hn) (lf D F0)
  rw [mapL_lf hn] at h
  exact h.symm

theorem unipotent_preserves_orth {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) :
    (orth (VS D) (Xsp (lf D F0))).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = orth (VS D) (Xsp (lf D F0)) := by
  rw [← Formalism.L2.SG.Pf.orth_map_sat n (isom_of_N0F hn), unipotent_preserves_x hn]

theorem unipotent_inv_sub_mem {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) {v : (VS D).V}
    (hv : v ∈ orth (VS D) (Xsp (lf D F0))) : v - n.symm v ∈ Xsp (lf D F0) := by
  have h1 : n.symm v ∈ orth (VS D) (Xsp (lf D F0)) := by
    rw [← unipotent_preserves_orth hn] at hv
    rw [Submodule.mem_map_equiv] at hv
    exact hv
  have h2 := hn.2.2.1 _ h1
  rwa [LinearEquiv.apply_symm_apply] at h2

theorem Hp_le_orthX (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ) {T' : D.host.E}
    (F' : LFlag (VS D) D.R.rS T') (hL : IsLift Λ (lf D F0)) (hL' : IsLift Λ F') :
    Hp Λ (lf D F0) F' ≤ orth (VS D) (Xsp (lf D F0)) := by
  intro w hw
  rw [Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)]
  have hw' := hw
  rw [Hp, Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)] at hw'
  intro e he
  refine hw' e ?_
  refine (Submodule.span_le.2 ?_) he
  rintro _ ⟨a, rfl⟩
  have := PI.PairCorankPos.W.frame_mem_UUE Λ hΛ (lf D F0) F' hL hL' (Sum.inl a.castSucc)
  simpa [FlagG.fvec] using this

end BwdBetaCut

namespace BwdBetaCut

theorem map_mul_eq (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Submodule D.host.E (VS D).V) :
    U.map ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
      (U.map (b : (VS D).V →ₗ[D.host.E] (VS D).V)).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  rw [← Submodule.map_comp]; rfl

theorem orth_Xplus_le {T : D.host.E} (F : LFlag (VS D) D.R.rS T) :
    orth (VS D) (Xplus F) ≤ orth (VS D) (Xsp F) := by
  intro v hv
  rw [Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)] at hv ⊢
  exact fun x hx => hv x (le_sup_left (a := Xsp F) hx)

end BwdBetaCut

theorem betaCore_of₂ (h : BetaCore₂ Zd u u' F0 what₂) : BetaCore Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg hT hPD hG
  obtain ⟨β₂, hiso, hgm, hfl, hz, hI, hW, hSc⟩ := h hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ ⟨n, hn, himg⟩ hT hPD hG
  have hni := isom_of_N0F hn
  have hF : mapL n hni (lf D F0) = lf D F0 := mapL_lf hn
  have hΛ : Formalism.HermitianLatticesTheory.gmap n Λ₂ = γ.lam := gmap_eq_of_image himg
  have hfix := (hC.2.1.1 γ.lam γ.mem).2.1
  have hL₂ : IsLift Λ₂ (lf D F0) := by
    have := Formalism.L2.SG.Pf.IsLift_mapL n hni Λ₂ (lf D F0)
    rw [hF, hΛ] at this
    exact this.1 hfix.2.2.1
  have hX'' : Xsp (mapL n hni (liftF F'₂)) = (Xsp (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) :=
    Formalism.L2.SG.Pf.Xsp_mapL n hni _
  refine ⟨n * β₂, ⟨⟨Subgroup.mul_mem _ hni hiso, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Formalism.L2.SG.Pf.gmap_mul_sat, hgm, hΛ]
  · intro j
    rw [Formalism.L2.SG.Pf.Xflag_mapL n hni, ← hfl j, BwdBetaCut.map_mul_eq]
  · show n (β₂ (repF γ).fl.z) = n (liftF F'₂).fl.z
    rw [hz]
  · intro x' hx' l hl
    have hN : NgX γ.lam (gS D) (lf D F0) (mapL n hni (liftF F'₂)) =
        Formalism.HermitianLatticesTheory.gmap n (NgX Λ₂ (gS D) (lf D F0) (liftF F'₂)) := by
      rw [← Formalism.L2.SG.Pf.NgX_mapL n hni, hF, hΛ]
    have hLr : Lrep γ.lam (lf D F0) = Formalism.HermitianLatticesTheory.gmap n (Lrep Λ₂ (lf D F0)) := by
      rw [← Formalism.L2.SG.Pf.Lrep_mapL n hni, hF, hΛ]
    have hl₂ : n.symm l ∈ Lrep Λ₂ (lf D F0) := by
      rw [hLr, Formalism.L2.SG.Saturated.mem_gmap_iff] at hl; exact hl
    have hlo : l ∈ orth (VS D) (Xsp (lf D F0)) := (Submodule.mem_inf.1 hl).2
    rw [hI x' hx' l hl (n.symm l) hl₂ (BwdBetaCut.unipotent_inv_sub_mem hn hlo), hN, Formalism.L2.SG.Saturated.mem_gmap_iff]
    simp only [map_sub]
    rw [show n.symm ((n * β₂) x') = β₂ x' from n.symm_apply_apply (β₂ x')]
  · intro w hw
    obtain ⟨w₂, hw₂, h1, h2⟩ := hW w hw
    refine Submodule.mem_map.2 ⟨(w, n w₂), ?_, rfl⟩
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_ThPairs]
    have hHp : Hp γ.lam (lf D F0) (mapL n hni (liftF F'₂)) =
        (Hp Λ₂ (lf D F0) (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← BwdBetaCut.Hp_mapL n hni, hF, hΛ]
    have hw₂o := BwdBetaCut.Hp_le_orthX Λ₂ hΛ₂.1 (liftF F'₂) hL₂ hT.1.1 hw₂
    refine ⟨hw, ?_, ?_, ?_⟩
    · rw [hHp]; exact Submodule.mem_map_of_mem hw₂
    · have h3 := hn.2.2.1 w₂ hw₂o
      have : w - n w₂ = (w - w₂) - (n w₂ - w₂) := by abel
      show w - n w₂ ∈ Xsp (lf D F0)
      rw [this]; exact sub_mem h1 h3
    · show n (β₂ w) - n w₂ ∈ Xsp (mapL n hni (liftF F'₂))
      rw [← map_sub, hX'']
      exact Submodule.mem_map_of_mem h2
  · intro y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hd1 hd2 al al'
    have hY : Ylift γ.lam (lf D F0) (mapL n hni (liftF F'₂)) =
        (Ylift Λ₂ (lf D F0) (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← BwdBetaCut.Ylift_mapL n hni, hF, hΛ]
    have hY' : Ylift' γ.lam (lf D F0) (mapL n hni (liftF F'₂)) =
        (Ylift' Λ₂ (lf D F0) (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← BwdBetaCut.Ylift'_mapL n hni, hF, hΛ]
    have hy2o : y2 ∈ orth (VS D) (Xsp (lf D F0)) :=
      BwdBetaCut.orth_Xplus_le (lf D F0) (Submodule.mem_inf.1 hy2).2
    rw [hY, Submodule.mem_map_equiv] at hy2
    rw [hY', Submodule.mem_map_equiv] at hy2''
    have e1 : y1 - n.symm y2 ∈ Xsp (lf D F0) := by
      have : y1 - n.symm y2 = (y1 - y2) + (y2 - n.symm y2) := by abel
      rw [this]; exact add_mem hd1 (BwdBetaCut.unipotent_inv_sub_mem hn hy2o)
    have e2 : n.symm y2'' - β₂ y1' ∈ Xsp (liftF F'₂) := by
      have hd2' : y2'' - (n * β₂) y1' ∈ (Xsp (liftF F'₂)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
        rw [← hX'']; exact hd2
      rw [Submodule.mem_map_equiv] at hd2'
      have : n.symm (y2'' - (n * β₂) y1') = n.symm y2'' - β₂ y1' := by
        rw [map_sub]; congr 1; exact n.symm_apply_apply (β₂ y1')
      rwa [this] at hd2'
    rw [hSc y1 hy1 _ hy2 y1' hy1' _ hy2'' e1 e2 al al']
    have hs := BwdBetaCut.sgRel_mapL n hni (lf D F0) (liftF F'₂) (n.symm y2) (n.symm y2'') al al'
    rw [hF, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hs
    exact hs.symm

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfC
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.S.Loc.HermSp.LprU

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def LprExist : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ F', IsPartner γ Z F' → ∀ p : PlF D,
      ∃ ψ₀ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'),
        (locH Zd p).Ident (tLoc Zd p γ) ⟨⊥, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩
          (LinearEquiv.refl _ _) ψ₀ ∧
        (locH Zd p).SendsTo ψ₀.toLinearMap 1 1 ((tLoc Zd p γ).f' (Fin.last _)) (locF' Zd p F' (Fin.last _)) ∧
        ψ₀ '' (locH Zd p).Lset (tLoc Zd p γ).abelian₂ (tLoc Zd p γ).f' =
          (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (locF' Zd p F') ∧
        ∀ g, (Zd.M p).split = some g →
          Prod.map ψ₀ (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
            (locH Zd p).iotaGraph g (tLoc Zd p γ) =
            (locH Zd p).iotaGraph g
              ⟨lattice₂ D Zd.M p γ.lam, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

def LprNondeg : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ F', IsPartner γ Z F' → ∀ p : PlF D,
      GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (tLoc Zd p γ).f') ∧
      GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (locF' Zd p F')) ∧
      IsUnit ((locH Zd p).Zhat (tLoc Zd p γ).f (tLoc Zd p γ).f').det ∧
      IsUnit ((locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p F')).det ∧
      Iso' (locH Zd p) (tLoc Zd p γ).f' ∧ Iso' (locH Zd p) (locF' Zd p F')

variable {u u' F0 what₂}

set_option maxHeartbeats 800000 in

theorem lprPart_of (hE : LprExist Zd u u' F0 what₂) (hN : LprNondeg Zd u u' F0 what₂) : LprPart Zd u u' F0 what₂ := by
  intro hrows γ Z hC F' hP p ψ hI hz
  obtain ⟨ψ₀, hI₀, hz₀, hL, hι⟩ := hE hrows γ Z hC F' hP p
  obtain ⟨n1, n2, d1, d2, k1, k2⟩ := hN hrows γ Z hC F' hP p
  have h : ψ = ψ₀ := psi_unique (H := locH Zd p) (tLoc Zd p γ)
    ⟨⊥, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩ (LinearEquiv.refl _ _) ψ ψ₀
    n1 n2 d1 d2 k1 k2 hI hI₀ hz hz₀
  rw [h]
  exact ⟨hL, hι⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorEqPointMinor
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leadingMinor_eq_pointMinor {D : D7} {n : ℕ} (w : Point D.host.E n) (l : ℕ) (hl : l ≤ n) :
    Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (ptMat w) l = Formalism.MainNotions.S.LocalSplitGroups.Dmin w l := by
  unfold Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor Formalism.MainNotions.S.LocalSplitGroups.Dmin
  rw [dif_pos hl]
  let e : Fin l ≃ {i : Fin n // (i : ℕ) < l} :=
    { toFun := fun j => ⟨Fin.castLE hl j, by simp⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun j => by ext; simp
      right_inv := fun i => by ext; simp }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem conjF_star' {D : D7} (x : D.host.E) : D.conjF x = star x :=
  (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host) x).symm

theorem GPt_junk (D : D7) (u u' : D.what₂.Word) :
    GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts (Formalism.L2.SG.PairVal.junkPoint D u u')) = 0 := by
  have h := (Formalism.MainNotions.S.Inh.zero_of_gram_point_exists D u u').choose_spec
  unfold Formalism.MainNotions.S.LocalSplitGroups.Gpt at h
  unfold Formalism.L2.SG.PairVal.junkPoint GPt
  rw [LeadingMinorIntegrality.dlast_eq, LeadingMinorIntegrality.dr_eq, leadingMinor_eq_pointMinor _ _ le_rfl, leadingMinor_eq_pointMinor _ _ (Nat.le_succ _),
    ← conjF_star', ← conjF_star']
  convert h using 3
  all_goals first
    | rfl
    | (push_cast; rfl)
    | norm_cast

theorem GPt_ne_of_NGPt {D : D7} (TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) (h : 1 ≤ NGPt D.host.rdE TT γ) :
    GPt TT γ ≠ 0 := by
  unfold NGPt at h
  intro h0
  rw [h0] at h
  simp [Fintype.card_ne_zero] at h
  linarith

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem gval_occ (t : TauC Y u u')
    (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    Gval (lf D (X.Fu u)) t.frame = GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t) := by
  have hne := GPt_ne_of_NGPt _ _ hG
  by_cases h : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant
  · obtain ⟨F', ⟨hP, hmk⟩, -, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm h
    have h1 := LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) F' _ hcell
    rw [show ptPN t = toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) from rfl, h1, ← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]
    have hΛ := (Y.rowsOK u).1 t.lam t.mem
    show Formalism.L2.SG.TermDef.Gt _ _ _ t.toTerm.cls = _
    rw [← hmk]
    exact Formalism.L2.SG.TermDef.Gt_mk ((Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).1) _
  · exfalso
    apply hne
    show GPt _ (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) = 0
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dif_neg h]
    exact GPt_junk D u u'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

