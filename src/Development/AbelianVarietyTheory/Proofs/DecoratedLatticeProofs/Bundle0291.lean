import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.Bundle0002
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0104
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0345
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealStabilizerProductMeasureIsHaarOnSet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MuSHaar

open scoped Pointwise

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Sinf Formalism.L2.SG.PoincareInHH.PoincareSetting

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

theorem muN_conj (h : X.B.I.Ginf) (hh : h ∈ Hinf X u) :
    (X.muN u).map (fun x => h * x * h⁻¹) = X.muN u := by
  have hNc : IsClosed (X.NinfU u) := isClosed_ninfU X u
  have hHc : IsCompact ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := hinf_compact X u
  obtain ⟨-, hfin, hpos⟩ := haarOnSet_isHaar_inst X.B.I (NinfSub X.eR (X.zR u)) (isClosed_ninfU X u)
    (X.muN u) (X.muN_haar u)
  have hgN : QPK.IsGrp (X.NinfU u) :=
    ⟨(NinfSub X.eR (X.zR u)).one_mem, fun a ha b hb => (NinfSub X.eR (X.zR u)).mul_mem ha hb,
      fun a ha => (NinfSub X.eR (X.zR u)).inv_mem ha⟩
  have hgH : QPK.IsGrp ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) :=
    ⟨(Hinf X u).one_mem, fun a ha b hb => (Hinf X u).mul_mem ha hb, fun a ha => (Hinf X u).inv_mem ha⟩
  exact QPK.conjugation_invariant_measure X.B.I.Ginf (X.NinfU u) _ hNc hHc hgN hgH
    (fun h hh m hm => conj_ninf X u hh hm) (X.muN u) (X.muN_haar u) ⟨fun K hK => hfin K hK⟩
    (fun U hU hne => (hpos U hU hne).ne') h hh

theorem muS_compact {K : Set X.B.I.Ginf} (hK : IsCompact K) :
    ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) K < ⊤ := by
  haveI := (X.muN_haar u).1
  haveI := (X.muH_haar u).1
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  set L : Set X.B.I.Ginf := (K * ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)⁻¹) ∩ X.NinfU u with hL
  have hLc : IsCompact L := (hK.mul (hinf_compact X u).inv).inter_right (isClosed_ninfU X u)
  rw [Measure.map_apply hmul hK.isClosed.measurableSet]
  calc ((X.muN u).prod (X.muH u)) ((fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) ⁻¹' K)
      ≤ ((X.muN u).prod (X.muH u)) (L ×ˢ Set.univ) := by
        refine measure_mono_ae ?_
        filter_upwards [ae_NH X u] with p hp hpK
        refine ⟨⟨?_, hp.1⟩, Set.mem_univ _⟩
        have e : p.1 = (p.1 * p.2) * p.2⁻¹ := by group
        rw [e]
        exact Set.mul_mem_mul hpK (Set.inv_mem_inv.2 hp.2)
    _ = X.muN u L * X.muH u Set.univ := Measure.prod_prod _ _
    _ < ⊤ := ENNReal.mul_lt_top (muN_compact X u hLc) (hFinite_holds X u)

theorem muS_isHaarOnSet : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  intro D X u
  obtain ⟨hNσ, hN0, -, hNinv⟩ := X.muN_haar u
  obtain ⟨hHσ, hH0, -, hHinv⟩ := X.muH_haar u
  haveI := hNσ
  haveI := hHσ
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI : IsFiniteMeasureOnCompacts (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) :=
      ⟨fun K hK => muS_compact X u hK⟩
    infer_instance
  · intro h0
    have h1 := congrArg (fun μ : Measure X.B.I.Ginf => μ Set.univ) h0
    simp only [Measure.map_apply hmul MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero,
      Pi.zero_apply] at h1
    rw [← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero, Measure.measure_univ_eq_zero,
      Measure.measure_univ_eq_zero] at h1
    exact h1.elim hN0 hH0
  · exact ae_iff.1 (Formalism.L2.SG.WuDecayPf.muSOn X u)
  · intro s hs
    obtain ⟨h0, hh0, n0, hn0, rfl⟩ := levi X u hs
    have hf : (X.muN u).map (fun x => h0 * (n0 * x) * h0⁻¹) = X.muN u := by
      have e : (fun x => h0 * (n0 * x) * h0⁻¹) = (fun x => h0 * x * h0⁻¹) ∘ (fun x => n0 * x) := rfl
      rw [e, ← Measure.map_map (by fun_prop) (by fun_prop), hNinv n0 hn0, muN_conj X u h0 hh0]
    have hg : (X.muH u).map (fun y => h0 * y) = X.muH u := hHinv h0 hh0
    have hfm : Measurable (fun x : X.B.I.Ginf => h0 * (n0 * x) * h0⁻¹) := by fun_prop
    have hgm : Measurable (fun y : X.B.I.Ginf => h0 * y) := by fun_prop
    calc (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)).map (fun x => h0 * n0 * x)
        = ((X.muN u).prod (X.muH u)).map ((fun x => h0 * n0 * x) ∘ (fun p => p.1 * p.2)) :=
          Measure.map_map (by fun_prop) hmul
      _ = ((X.muN u).prod (X.muH u)).map ((fun p => p.1 * p.2) ∘
            Prod.map (fun x => h0 * (n0 * x) * h0⁻¹) (fun y => h0 * y)) := by
          congr 1; funext p; simp only [Function.comp, Prod.map]; group
      _ = (((X.muN u).prod (X.muH u)).map
            (Prod.map (fun x => h0 * (n0 * x) * h0⁻¹) (fun y => h0 * y))).map (fun p => p.1 * p.2) :=
          (Measure.map_map hmul (hfm.prodMap hgm)).symm
      _ = (((X.muN u).map (fun x => h0 * (n0 * x) * h0⁻¹)).prod ((X.muH u).map (fun y => h0 * y))).map
            (fun p => p.1 * p.2) := by rw [Measure.map_prod_map _ _ hfm hgm]
      _ = ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) := by rw [hf, hg]

end GlobalTheory.MuSHaar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeEntriesMemSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EntrySB
open scoped Pointwise

theorem exists_nhds_add_eq {M E : Type*} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [Zero E]
    {F : M → E} (hl : IsLocallyConstant F) (hc : HasCompactSupport F) :
    ∃ V ∈ nhds (0 : M), ∀ x, ∀ v ∈ V, F (x + v) = F x := by
  letI : TopologicalSpace E := ⊥
  haveI : DiscreteTopology E := ⟨rfl⟩
  have hT : (F '' tsupport F).Finite := (hc.isCompact.image hl.continuous).finite_of_discrete
  have hsep : ∀ a : E, ∃ W ∈ nhds (0 : M), a ≠ 0 → F ⁻¹' {a} + W ⊆ F ⁻¹' {a} := by
    intro a
    by_cases ha : a = 0
    · exact ⟨Set.univ, Filter.univ_mem, fun h => (h ha).elim⟩
    · have hsub : F ⁻¹' {a} ⊆ tsupport F := fun y hy =>
        subset_tsupport F (by simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy; simp [Function.mem_support, hy, ha])
      have hK : IsCompact (F ⁻¹' {a}) := hc.isCompact.of_isClosed_subset (hl.isClopen_fiber a).isClosed hsub
      obtain ⟨W, hW, hW'⟩ := compact_open_separated_add_right hK (hl.isOpen_fiber a) le_rfl
      exact ⟨W, hW, fun _ => hW'⟩
  choose W hW hWs using hsep
  refine ⟨⋂ a ∈ F '' tsupport F, (W a ∩ -W a), (Filter.biInter_mem hT).2 fun a _ =>
    Filter.inter_mem (hW a) (neg_mem_nhds_zero M (hW a)), ?_⟩
  intro x v hv
  simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_neg] at hv
  by_cases hx : F x = 0
  · by_contra hne
    have hxv : x + v ∈ tsupport F := subset_tsupport F (by rw [Function.mem_support]; rwa [hx] at hne)
    have hb : F (x + v) ≠ 0 := fun h => hne (h.trans hx.symm)
    have := hWs (F (x + v)) hb (Set.add_mem_add (a := x + v) (b := -v) rfl (hv _ ⟨_, hxv, rfl⟩).2)
    simp only [add_neg_cancel_right, Set.mem_preimage, Set.mem_singleton_iff] at this
    exact hne this.symm
  · have hxs : x ∈ tsupport F := subset_tsupport F hx
    have := hWs (F x) hx (Set.add_mem_add (a := x) (b := v) rfl (hv _ ⟨_, hxs, rfl⟩).1)
    simpa using this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Aff
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem affPt_add (p : ℕ) (x₀ v : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p (x₀ + v) e = affPt p x₀ e + fromBlocks v 0 0 0 := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;> simp [affPt, basePt] <;> ring

theorem ch_add (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (x + y) = ch x + ch y := by
  simp [ch, Finset.sum_add_distrib]

theorem ch_fromBlocks (v : Matrix n n' k) :
    ch (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) = 0 := by
  simp [ch]

theorem corner_affPt (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    (Matrix.of fun i j => affPt p x₀ e (Sum.inl i) (Sum.inl j)) = x₀ := by
  ext i j
  simp [affPt, basePt, Free]

variable [MeasurableSpace k] [BorelSpace k]

theorem opE_mem_SB (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    {F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hF : F ∈ SB _) :
    GlobalTheory.RootEx.opE ψ ν p F ∈ SB (Matrix n n' k) := by
  obtain ⟨hl, hc⟩ := hF
  refine ⟨?_, ?_⟩
  · obtain ⟨V, hV, hVF⟩ := exists_nhds_add_eq hl hc
    have hι : Continuous fun v : Matrix n n' k =>
        (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
      continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const
    have hW : (fun v : Matrix n n' k =>
        (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) ⁻¹' V ∈ nhds (0 : Matrix n n' k) := by
      apply hι.continuousAt.preimage_mem_nhds
      simpa [fromBlocks_zero] using hV
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ => ?_
    rw [← map_add_left_nhds_zero x₀, Filter.eventually_map]
    filter_upwards [hW] with v hv
    simp only [GlobalTheory.RootEx.opE]
    congr 1
    funext e
    rw [affPt_add, hVF _ _ hv, ch_add, ch_fromBlocks, add_zero]
  · have hpr : Continuous fun M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
        (Matrix.of fun i j => M (Sum.inl i) (Sum.inl j) : Matrix n n' k) :=
      continuous_matrix fun i j => continuous_id.matrix_elem _ _
    refine HasCompactSupport.intro (hc.isCompact.image hpr) fun x₀ hx₀ => ?_
    have h0 : ∀ e, F (affPt p x₀ e) = 0 := fun e => image_eq_zero_of_notMem_tsupport fun hm =>
      hx₀ ⟨_, hm, corner_affPt p x₀ e⟩
    simp [GlobalTheory.RootEx.opE, h0]

end Aff

end GlobalTheory.EntrySB

open GlobalTheory.EntrySB in

theorem GlobalTheory.StepData.xi_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle), Continuous ψ →
  ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (J : Subgroup (GL (n ⊕ Fin c) k)) (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    xi ψ ν μ Φ.1 J b h' h ∈ SB (Matrix n n' k) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ψ _ ν _ μ Φ J b h' h
  have := Submodule.smul_mem (SB (Matrix n n' k)) ((((volNat ν b (Cgrp J h))⁻¹ : ℝ) : ℂ))
    (opE_mem_SB ψ ν 1 (GlobalTheory.SplitWeil.om_mem_SB μ h' h Φ.2))
  convert this using 1
  funext x
  simp [xi, flat]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowGen1POfSteps
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
open Formalism.L2.SG.Pf

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scT_sc_genSet {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) :
    (scT X).sc (scT X).genSet = X.one X.genSet := by
  ext p
  simp only [PB.Terms.one, PB.Terms.sc, PB.Terms.allPairs, Set.mem_setOf_eq]
  exact ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, trivial⟩⟩

theorem rowGen1P_of_steps (hCh : PN.NGChain) (hC : StepClass1) (hN : StepNormals1) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLoc1) (hTB : GlobalTheory.SnPos.StepThmBGP) : RowGen1P := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨CB, hCB, a₁, b₁, hTB2⟩ := hTB Cg cb Cw cT CT C0 hcb hcT (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, a₂, b₂, hS2⟩ := sizes_of_hypotheses Cg cb Cw cT CT C0
  obtain ⟨a₃, b₃, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨a₄, b₄, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨a₅, b₅, hH2⟩ := stepHeightG_of_normOne hO Cg cb Cw cT CT C0
  obtain ⟨a₆, b₆, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨a₇, b₇, hT2⟩ := hTi Cg cb Cw cT CT C0
  obtain ⟨a₈, b₈, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨a₉, b₉, hV2⟩ := hV Cg cb Cw cT CT C0
  obtain ⟨Cn, hCn, hK⟩ := rowGenJoint_of hCh meanAmplitudeGeneric_holds C1 C0n (C1 + C0n + 38) CB CSt Cgs CTs
    hCB hCSt hCg hCT le_rfl
  refine ⟨Cn, hCn, max a₀ (max a₁ (max a₂ (max a₃ (max a₄ (max a₅ (max a₆ (max a₇ (max a₈ a₉)))))))),
    max b₀ (max b₁ (max b₂ (max b₃ (max b₄ (max b₅ (max b₆ (max b₇ (max b₈ b₉)))))))),
    fun C' Cl e1 e2 D large₂ X Y u hTies hH0 hSt hT ha => ?_⟩
  simp only [max_le_iff] at e1 e2
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := e1
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := e2
  have hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u := ⟨hH0, hSt, hT⟩
  obtain ⟨hb, X0, ψ, hTie⟩ := hT2 C' Cl p7 q7 D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl p6 q6 D large₂ X Y u u hc hb X0 ψ hTie
  have hBk' : MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) (Irat * kapU D) (Ire * kapU D) :=
    massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨ν, hν⟩ := hE2 C' Cl p8 q8 D large₂ X Y u u hc
  obtain ⟨s, hs1, hs0, hsb, hLe⟩ :=
    hL2 C' Cl p0 q0 D large₂ X Y u hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  have hSum := hTB2 C' Cl p1 q1 D large₂ X Y u hTies hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  generalize bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq = B at hBk' hLe
  have hSz := hS2 C' Cl p2 q2 D large₂ X Y u u hc
  have hrd : 0 < D.host.rdE := by
    obtain ⟨-, -, hrd, -⟩ := hSz
    have hv : 2 * D.host.v = D.host.rdE := by simp only [Formalism.BasicNotions.Host.v]; ring
    rwa [hv] at hrd
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk'
  set ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA * 2 *
      HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ PN.eN D.R.rS *
      nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u : ℕ)) γ with hng
  obtain ⟨hPt, -, -, hAmp⟩ := GlobalTheory.Core.One.genericTerms_points_agree_groupSums_corankOne D X Y u (sc s ν) ν ng
  have hVan : ∀ t ∈ (Y.tO u u).genSet, J2of Y u u (sc s ν) (ptPN t) = 0 → (Y.tO u u).vec t = 0 := by
    intro t ht h0
    obtain ⟨g, hg⟩ := J2of_sc Y u u s ν (ptPN t)
    rw [hg] at h0
    have hp : (0 : ℝ) < (s g : ℝ) ^ 2 := by have := hs0 g; positivity
    exact hV2 C' Cl p9 q9 D large₂ X Y u hc ν hν t ht ((mul_eq_zero.1 h0).resolve_left hp.ne')
  have hIn : GenInputs (scT (Y.tO u u)) (NOf1 Y u (sc s ν) ν ng) D.R.f C1 C0n (C1 + C0n + 38) CB large₂.sc.b
      (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
      (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f))
      (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) 2 (Ire * kapU D) := by
    refine ⟨hC D X Y u hT _ _ _, hAmp hVan, hN2 C' Cl p3 q3 D large₂ X Y u hc _ _ _, ?_,
      localInputG_of_le _ _ _ _ _ hLe (fun γ => rfl), ?_, ?_, ?_, ?_⟩
    · exact fun γ hγ => hP2 C' Cl p4 q4 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun γ hγ => measureInputG_sc Y u s ν _ hsb ng γ ((hPt γ).1 hγ)
    · exact fun γ _ => ⟨nPt_nonneg _ hrd _ _ γ, le_rfl⟩
    · exact fun γ hγ => hH2 C' Cl p5 q5 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun S hS => hSum (sc s ν) ng S (fun γ hγ => (hPt γ).1 (hS γ hγ))
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u) _ _ _ _ (scT (Y.tO u u)) D.R.rS D.R.k (Set (TauC Y u u)) (NuC D)
    (NOf1 Y u (sc s ν) ν ng) _ B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
    (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) 2 (Irat * kapU D) (Ire * kapU D)
  rw [hcard] at key
  have r := key ha hG hNI hFI (ngSizes_of hSz hb0 le_rfl zero_le_two le_rfl) hIn
  rw [hdd] at r
  unfold PB.Terms.RowMain at r
  rw [scT_sc_genSet] at r
  exact r

end GlobalTheory.Core.One
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RtrMemOfNorm
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MiTop.CenIsom

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

theorem rtr_mem_of_norm (hK : X.LevelSubgroupCharacter) {δ : Hfin X u}
    (hn : ∀ κ : Ku X u hK, ∃ κ' : Ku X u hK, (κ : Hfin X u) * δ = δ * κ' ∧
      ((psiK X u hK κ' : ℂˣ) : ℂ) = ((psiK X u hK κ : ℂˣ) : ℂ))
    {T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)} (hT : T ∈ Cu X u hK) : rtr X δ T ∈ Cu X u hK := by
  obtain ⟨h1, h2⟩ := hT
  refine ⟨fun ξ => ⟨fun γ y => ?_, fun y κ => ?_⟩, fun g ξ y => ?_⟩
  · show T ξ ((_, _) * y * (1, δ)) = T ξ (y * (1, δ))
    rw [mul_assoc]
    exact (h1 ξ).1 γ _
  · obtain ⟨κ', hκ', hψ⟩ := hn κ
    have hc : ((1 : Hinf X u), (κ : Hfin X u)) * (1, δ) = (1, δ) * (1, (κ' : Hfin X u)) :=
      Prod.ext rfl hκ'
    have e : y * (1, (κ : Hfin X u)) * (1, δ) = y * (1, δ) * (1, (κ' : Hfin X u)) := by
      rw [mul_assoc, mul_assoc, hc]
    refine (congrArg (T ξ) e).trans (((h1 ξ).2 _ κ').trans ?_)
    rw [hψ]
    rfl
  · have hc : ((g : Hinf X u), (1 : Hfin X u)) * (1, δ) = (1, δ) * (g, 1) :=
      Prod.ext ((mul_one g).trans (one_mul g).symm) ((one_mul δ).trans (mul_one δ).symm)
    have e : y * (g, 1) * (1, δ) = y * (1, δ) * (g, 1) := by
      rw [mul_assoc, mul_assoc, hc]
    exact (h2 g ξ (y * (1, δ))).trans (congrArg (T ξ) e.symm)

theorem rtr_comm {δ δ' : Hfin X u} (h : δ * δ' = δ' * δ) (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) :
    rtr X δ' (rtr X δ T) = rtr X δ (rtr X δ' T) := by
  ext ξ y
  have hc : ((1 : Hinf X u), δ') * (1, δ) = (1, δ) * (1, δ') := Prod.ext rfl h.symm
  have e : y * (1, δ') * (1, δ) = y * (1, δ) * (1, δ') := by rw [mul_assoc, mul_assoc, hc]
  exact congrArg (T ξ) e

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem exists_rtr_dia {F : Formalism.L2.Forms.Forms0 D u} (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter) (hL : LevelMatch X Tr hK)
    (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    ∃ δ : Hfin X u, ∀ T ∈ Cu X u hK, rtr X δ T ∈ Cu X u hK ∧
      dictA X Tr (rtr X δ T) = (D.mem u).A.rhoT v a (dictA X Tr T) := by
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  have hσ := GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X Tr.ιA hA
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.frame_action_mulEquiv D X u Tr.wt Tr.ιA hW hA hσ
  obtain ⟨-, hΓ, hsT⟩ := GlobalTheory.transport_rational_points D X u Tr.wt Tr.ιA hW hA Φ hΦ
  obtain ⟨hψ, -, hφ, -, -⟩ := cols_sharp_dictionary D X u hK
  obtain ⟨k, hk, hkT⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσe⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.splitAtT_of_tied F.atT v
  obtain ⟨y, hy⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.is_diamond_of_local_diamond F.cls0.lev (F.atT.eV v).1 (F.atT.eV v).2 k
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_diamond_of_split_idempotent F.cls0.lev _ _ (D.mem u).A.T_prime k hkT e he hee hσe)
  have hlev := fun h => hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)
  obtain ⟨δ, hδ⟩ : ∃ δ : Hfin X u, Φ δ = Tr.h0 * y * Tr.h0⁻¹ := Φ.surjective _
  refine ⟨δ, fun T hT => ⟨rtr_mem_of_norm hK (fun κ => ?_) hT, ?_⟩⟩
  · have hκ := (hlev κ).1.1 κ.2
    have hm := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.diamond_conj_mem_level F.cls0.lev _ _ hy ⟨_, hκ⟩
    have hχ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.level_character_conj_diamond F.cls0.lev _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.level_places_not_bad F.atT v) hy ⟨_, hκ⟩
    have e1 : Tr.h0⁻¹ * Φ (δ⁻¹ * κ * δ) * Tr.h0 = y⁻¹ * (Tr.h0⁻¹ * Φ κ * Tr.h0) * y := by
      rw [map_mul, map_mul, map_inv, hδ]
      group
    have e2 := congrArg Subtype.val e1
    have hm' : (Tr.h0⁻¹ * Φ (δ⁻¹ * κ * δ) * Tr.h0).1 ∈ F.cls0.lev.U := by
      rw [e2]
      exact hm
    have hin := (hlev (δ⁻¹ * κ * δ)).1.2 hm'
    refine ⟨⟨δ⁻¹ * κ * δ, hin⟩, by simp only [← mul_assoc, mul_inv_cancel, one_mul], ?_⟩
    rw [(hlev _).2 hin hm', (hlev κ).2 κ.2 hκ, ← hχ]
    exact congrArg (fun x => ((F.cls0.lev.chi x : ℂˣ) : ℂ)) (Subtype.ext e2)
  · have key := GlobalTheory.adForms_of_equivariant D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hinf X u) (Hfin X u)
      (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 D.what₂.Tau (Formalism.L2.Forms.embT D)
      ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ
      (fun h => (hlev h).1) (fun h hk hy => (hlev h).2 hk hy) hΓ
      (fun γ g hγ ξ y y' hy => Tr.J_eqv _ (iotaI X u γ).2 ξ y y' (by rw [hsT γ g hγ]; exact hy))
      (fun ξ => by rw [← Formalism.L2.Forms.lamT_zero]; exact Tr.J_val ξ)
      (shP X u T) (hφ ⟨T, hT⟩)
    have hc : ∀ c, Φ (Tr.hc c) = F.cls0.y c * Tr.h0⁻¹ := fun c => (hΦ (Tr.hc c) _).1 (Tr.hc_rep c)
    have e1 : dictA X Tr T = fun c s =>
        (fun x => Tr.J (shP X u T (Φ.symm (x * Tr.h0⁻¹)))) (F.cls0.y c) (F.val0.eY s) := by
      funext c s
      show Tr.J (shP X u T (Tr.hc c)) (F.val0.eY s) = Tr.J (shP X u T (Φ.symm (F.cls0.y c * Tr.h0⁻¹))) (F.val0.eY s)
      rw [← hc, MulEquiv.symm_apply_apply]
    rw [e1, Formalism.L2.Forms.rhoT_eq F.val0 v a k hk y hy _ key.1]
    funext c s
    have e2 : Tr.hc c * δ = Φ.symm (F.cls0.y c * y * Tr.h0⁻¹) := by
      apply Φ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hc, hδ]
      group
    show Tr.J (shP X u (rtr X δ T) (Tr.hc c)) (F.val0.eY s) =
      Tr.J (shP X u T (Φ.symm (F.cls0.y c * y * Tr.h0⁻¹))) (F.val0.eY s)
    rw [Formalism.L2.SG.Pf.ColDictPf.rieszVector_rightTranslate, e2]

theorem ram_rtr {F : Formalism.L2.Forms.Forms0 D u} (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter) (hL : LevelMatch X Tr hK)
    (hI : ColDictInto X Tr hK) (hB : ColDictBij X Tr hK) (δ : Hfin X u) (hδ : ∀ k : Hfin X u, δ * k = k * δ)
    (T S : Cu X u hK) (hS : S.1 = rtr X δ T.1) (hT : colDictL X Tr hK T ∈ (D.mem u).A.Mram) :
    colDictL X Tr hK S ∈ (D.mem u).A.Mram := by
  refine ⟨hI S, (Submodule.mem_iInf _).2 fun v => ?_⟩
  have h0 : (D.mem u).A.Nm v (dictA X Tr T.1) = 0 := (Submodule.mem_iInf _).1 hT.2 v
  choose d hd using exists_rtr_dia Tr hK hL v
  have hsum : ∀ P ∈ Cu X u hK, (D.mem u).A.Nm v (dictA X Tr P) = dictA X Tr (∑ a, rtr X (d a) P) := by
    intro P hP
    rw [map_sum, Formalism.BasicNotions.ColumnsAtT.Nm, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (hd a P hP).2.symm
  have hmem : ∑ a, rtr X (d a) T.1 ∈ Cu X u hK := Submodule.sum_mem _ fun a _ => (hd a T.1 T.2).1
  have hz : (⟨_, hmem⟩ : Cu X u hK) = 0 :=
    hB.1 (((hsum T.1 T.2).symm.trans h0).trans (map_zero (colDictL X Tr hK)).symm)
  have hz' : ∑ a, rtr X (d a) T.1 = 0 := congrArg Subtype.val hz
  have e : ∑ a, rtr X (d a) S.1 = rtr X δ (∑ a, rtr X (d a) T.1) := by
    rw [map_sum, hS]
    exact Finset.sum_congr rfl fun a _ => rtr_comm (hδ (d a)) T.1
  show (D.mem u).A.Nm v (dictA X Tr S.1) = 0
  rw [hsum S.1 S.2, e, hz', map_zero, map_zero]

theorem sum_inner_rieszVector_rightTranslate (hK : X.LevelSubgroupCharacter) {ι : Type} [Fintype ι] (s : ι → Hfin X u)
    (hs : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : Ku X u hK), h = iotaF X u γ * s i * (κ : Hfin X u))
    (δ : Hfin X u) (hδ : ∀ k : Hfin X u, δ * k = k * δ) (T T' : Cu X u hK) :
    ∑ i, ⟪shP X u (rtr X δ T'.1) (s i), shP X u (rtr X δ T.1) (s i)⟫_ℂ =
      ∑ i, ⟪shP X u T'.1 (s i), shP X u T.1 (s i)⟫_ℂ := by
  simp only [Formalism.L2.SG.Pf.ColDictPf.rieszVector_rightTranslate]
  refine Formalism.L2.SG.Pf.ColDictPf.sum_reps X u (fun i => s i * δ) s (Ku X u hK) (fun h => ?_) hs
    (fun h => ⟪shP X u T'.1 h, shP X u T.1 h⟫_ℂ)
    (fun γ h κ => Formalism.L2.SG.Pf.ColDictPf.inner_shP_rat X u hK T T' γ h κ)
  have e : ∀ (i : ι) (γ : Gam X u) (κ : Ku X u hK), h * δ⁻¹ = iotaF X u γ * s i * (κ : Hfin X u) ↔
      h = iotaF X u γ * (s i * δ) * (κ : Hfin X u) := by
    intro i γ κ
    rw [mul_inv_eq_iff_eq_mul, mul_assoc _ (κ : Hfin X u) δ, ← hδ κ]
    simp only [mul_assoc]
  simpa only [e] using hs (h * δ⁻¹)

open Formalism.MainNotions Formalism.L2 Formalism.L2.DIV

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : Formalism.L2.RecT ex}

set_option maxHeartbeats 1000000 in

theorem ipC_eq_sum (S : Formalism.L2.SG.SpectralTiesReal.STiesR R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (T T' : Cu S.X u S.Y.hK) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ := by
  have h1 : ∀ P : Cu S.X u S.Y.hK, colDictL S.X (S.tr u) S.Y.hK P = (D.s_Cu u (((S.hI hF).eCu u).symm P)).1 := by
    intro P
    have h := S.colPin hF u (((S.hI hF).eCu u).symm P)
    have h' : @Eq (Cu S.X u S.Y.hK) ((S.hI hF).eCu u (((S.hI hF).eCu u).symm P)) P :=
      ((S.hI hF).eCu u).apply_symm_apply P
    exact congrArg Subtype.val ((congrArg (colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u)) h').symm.trans h)
  have h2 := ((S.hI hF).eCu u).symm.inner_map_map T T'
  have h3 : @inner ℂ (Formalism.L2.SG.PackageTie2.ColT (hF.shInj u)) _ T T' =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ :=
    (Formalism.L2.SG.PackageTie2.inner_colT (hF.shInj u) T T').trans (PiLp.inner_apply _ _)
  have h4 := (congrArg₂ ((D.fm u).ipC 0) (h1 T) (h1 T')).trans (D.s_Cu_isom u _ _).symm
  exact h4.trans (h2.trans h3)

theorem isom_rtr (S : Formalism.L2.SG.SpectralTiesReal.STiesR R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (δ : Hfin S.X u) (hδ : ∀ k : Hfin S.X u, δ * k = k * δ) (T T' P P' : Cu S.X u S.Y.hK)
    (hP : P.1 = rtr S.X δ T.1) (hP' : P'.1 = rtr S.X δ T'.1) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK P) (colDictL S.X (S.tr u) S.Y.hK P') =
      (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') := by
  refine (ipC_eq_sum S hF u P P').trans (Eq.trans ?_ (ipC_eq_sum S hF u T T').symm)
  rw [hP, hP']
  exact sum_inner_rieszVector_rightTranslate S.Y.hK _ (S.Y.colReps u) δ hδ T T'

end GlobalTheory.MiTop.CenIsom

end
end

