import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0490
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0461
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0514
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0511
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticesGoodPositionAllPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0517
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementProperty
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZeroMem

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem h0_eq (D : D7) : 0 + 2 * D.R.rS + 2 = D.R.m := by
  obtain ⟨q, hq⟩ := D.R.m_even
  have := D.R.two_le_m
  unfold Ranks.rS
  omega

set_option maxHeartbeats 1000000 in

theorem conj_mem_K_two (W : RealPack ex) (hPk : PkHyp W) {u : D.what₂.Word} (f : FamCh W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) {v : VCom f.c} (G : (GlobalTheory.BaseChain.com W).Pg → GLoc v)
    (hBot : GlobalTheory.LevZero.Bot (c := f.c) (GlobalTheory.BaseChain.com W) (GlobalTheory.LevZero.stZero W) (f.g.b 0) G)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hBl : B.lev = f.c.B 0 D.R.rS h0) (hAd : B.Adapted (W.S.tr u).wt) (hTr : LevTrace f B)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧
      finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0))) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (hone : ∀ k ∈ levS (D.sp.Y 0) ((pk W).βY 0) (GlobalTheory.LevZero.datZero W),
      (∀ PP ∈ (GlobalTheory.BaseChain.com W).Pg, redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0) PP (finE (D.sp.Y 0) k) = 1) →
      (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2) :
    ∀ k ∈ levS (D.sp.Y 0) ((pk W).βY 0) (GlobalTheory.LevZero.datZero W), (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2 := by
  have hemb : ∀ b, embA B.d B.o b = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o b : GA D (D.sp.Y 0)) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (D.sp.Y 0)) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (f.c.bes 0 D.R.rS h0).d : Subgroup (GA D (D.sp.Y 0))) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  refine GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents (GlobalTheory.BaseChain.com W) (GlobalTheory.LevZero.stZero W) (f.g.b 0) G h0 hBot
    (fun k : GA D (D.sp.Y 0) => (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2) ?_ ?_ ?_ hone
  · intro (k : GA D (D.sp.Y 0)) _ (k' : GA D (D.sp.Y 0)) _ q q'
    show (iotaX W.S.X W.Q.instEq (s * (k * k') * s⁻¹)).2 ∈ W.S.X.K2
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    rw [e, map_mul, Prod.snd_mul]
    exact W.S.Y.hK.2.1 _ q _ q'
  · intro PP (n : GA D (D.sp.Y 0)) q hn _ _ hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      rw [hs]; group
    have hk' : t⁻¹ * n * t ∈ levS (D.sp.Y 0) ((pk W).βY 0) (GlobalTheory.LevZero.datZero W) := by rw [ht]; exact hk
    have hKs := ((hSt (s * (t⁻¹ * n * t) * s⁻¹)).1 ⟨GlobalTheory.MemMatch.conj_mem_GfC W.S.X W.Q.instEq s _ hk'.1, by
      rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.conj_mem_St_iff]; exact parLev_St hk'.2.1⟩).2
    have hN := ((B.tieN _).1 (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn')).2
    have goal : (iotaX W.S.X W.Q.instEq (s * (t⁻¹ * n * t) * s⁻¹)).2 ∈ W.S.X.K2 := by
      rw [e] at hKs ⊢
      generalize embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹ = n' at hN hKs ⊢
      rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply] at hKs ⊢
      generalize iotaX W.S.X W.Q.instEq n' = y at hN hKs ⊢
      change (W.S.X.xu u)⁻¹ * y.2 * W.S.X.xu u ∈ _ at hKs ⊢
      refine Formalism.L2.SG.Pf.unipotent_conj_mem_level hN ?_
      have := Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (W.S.X.xu_K u) hKs)
        (Formalism.L2.SG.Pf.unitaryCongruence.K_inv _ (W.S.X.xu_K u))
      rwa [show W.S.X.xu u * ((W.S.X.xu u)⁻¹ * y.2 * W.S.X.xu u) * (W.S.X.xu u)⁻¹ = y.2 by group] at this
    subst ht
    exact goal
  · intro b hb hk
    rw [← hemb b] at hk
    have h1 := (GlobalTheory.T.level_trace_adapted_translate W hPk u f B hTr hAd a₀ hH0 b hb).1.1 hk
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    rw [← e] at h1
    rw [← hemb b]
    subst ht
    exact h1.2

set_option maxHeartbeats 2000000 in

theorem mem_K_two_iff (W : RealPack ex) (hPk : PkHyp W) {u : D.what₂.Word} (f : FamCh W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) {v : VCom f.c} (G : (GlobalTheory.BaseChain.com W).Pg → GLoc v)
    (hBot : GlobalTheory.LevZero.Bot (c := f.c) (GlobalTheory.BaseChain.com W) (GlobalTheory.LevZero.stZero W) (f.g.b 0) G)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hBl : B.lev = f.c.B 0 D.R.rS h0) (hAd : B.Adapted (W.S.tr u).wt) (hTr : LevTrace f B)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧
      finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0))) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ GfC (D.sp.Y 0))
    (hκS : finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0))) :
    (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.K2 ↔
      rTup (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0)) (GlobalTheory.LevZero.datZero W) (finE (D.sp.Y 0) κ) ∈
        (GlobalTheory.LevZero.datZero W).P.H := by
  obtain ⟨hr, ξ, hL⟩ := hBot.mem.lev
  obtain ⟨N, hN, -⟩ := hBot.mem.base
  have hrk : (D.sp.Y 0).rank = D.R.rankY 0 := hBot.mem.rank
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by rw [hrk]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hr' : D.R.r ≤ (D.sp.Y 0).rank := hr
  have hLb : GlobalTheory.LevZero.datZero W = (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' (GlobalTheory.BaseChain.com W).Pg ∅
      (GlobalTheory.BaseChain.com W).P (GlobalTheory.BaseChain.com W).chi ξ Frm.B) := hL
  have hlift : Lev.LiftsExist (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0) (GlobalTheory.LevZero.datZero W) :=
    GlobalTheory.ChainOnto.FlagAct.liftsExist_stage hBot.com hBot.mem
  obtain ⟨m, hm⟩ := GlobalTheory.MemMatch.exists_read W.S.X W.Q.instEq (GlobalTheory.BaseChain.com W).Pg hBot.typ hBot.com.split
    (fun PP => ⟨_, (hBot.loc PP).idem⟩) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0) ((pk W).ΛY 0) N hN s hSt
  have hin := conj_mem_K_two W hPk f B G hBot h0 hBl hAd hTr a₀ hH0 a hac t s ht hs hSt (fun k hk h1 =>
    (hm k hk.1 (parLev_St hk.2.1)).2 fun PP => by rw [h1 PP.1 PP.2, mul_one, mul_inv_cancel]; exact one_mem _)
  have hpat : ∀ g : ∀ PP : (GlobalTheory.BaseChain.com W).Pg, GL (Fin D.R.r) (kP PP.1),
      g ∈ (GlobalTheory.BaseChain.com W).P.H ↔ ∀ PP, GlobalTheory.SymRes.IsPat D.R.rS D.R.k (g PP) :=
    fun g => (hBot.grp g).trans (forall_congr' fun PP => GlobalTheory.LevZero.exists_red_iff_isPat (G PP) PP.1 (hBot.loc PP).idem (g PP))
  rw [hLb] at hlift hin ⊢
  have hlev : ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St (F := D.host.F) (E := D.host.E) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0) →
      (fun PP : (GlobalTheory.BaseChain.com W).Pg => upperLeftBlock hr' (redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0) PP.1 (finE (D.sp.Y 0) k))) ∈ (GlobalTheory.BaseChain.com W).P.H →
      k ∈ levS (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0) (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' (GlobalTheory.BaseChain.com W).Pg ∅
        (GlobalTheory.BaseChain.com W).P (GlobalTheory.BaseChain.com W).chi ξ Frm.B) := by
    intro k hk hS hP
    refine ⟨hk, ?_⟩
    show finE (D.sp.Y 0) k ∈ lev _ _ _ _
    rw [mem_lev, mem_parLev]
    exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hS, fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _,
      fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, hP⟩
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  have hk₀ : k₀ ∈ GfC (D.sp.Y 0) := by
    have := GlobalTheory.MemMatch.conj_mem_GfC W.S.X W.Q.instEq s⁻¹ _ hκ
    rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
  have hfe : finE (D.sp.Y 0) (s * k₀ * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k₀ * (finE (D.sp.Y 0) s)⁻¹ := by rw [map_mul, map_mul, map_inv]
  rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS
  rw [hfe, GlobalTheory.FrameConj.rTup_conj]
  refine ⟨fun hK => ?_, fun hP => hin k₀ (hlev k₀ hk₀ hκS hP)⟩
  refine (hpat _).2 fun PP => (GlobalTheory.MemMatch.isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 ?_
  haveI : Finite (kP PP.1) := Ideal.finiteQuotientOfFreeOfNeBot PP.1.asIdeal PP.1.ne_bot
  have hrr : (D.sp.Y 0).rank = D.R.k + (2 * D.R.rS + 1) := by
    have := le_antisymm hn hr'
    have h0' := h0
    unfold Ranks.r at this
    omega
  refine GlobalTheory.SymResCount.conj_pat_onto (kP PP.1) _ D.R.rS D.R.k hrr (m PP) (fun g hg => ?_) _ ((hm k₀ hk₀ hκS).1 hK PP)
  let g0 : ∀ Q : (GlobalTheory.BaseChain.com W).Pg, GL (Fin D.R.r) (kP Q.1) := Function.update (fun _ => 1) PP (upperLeftBlock hr' g)
  have hg0 : g0 ∈ (GlobalTheory.BaseChain.com W).P.H := (hpat _).2 fun Q => by
    by_cases hQ : Q = PP
    · subst hQ
      simp only [g0, Function.update_self]
      exact (GlobalTheory.MemMatch.isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 hg
    · simp only [g0, Function.update_of_ne hQ]
      exact GlobalTheory.SymRes.isPat_one _ _
  obtain ⟨k, hk, hkp, hkr⟩ := hlift g0
  have hkr' : (fun PP : (GlobalTheory.BaseChain.com W).Pg => upperLeftBlock hr' (redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0) PP.1 (finE (D.sp.Y 0) k))) = g0 := hkr
  have h1 := (hm k hk (parLev_St hkp)).1 (hin k (hlev k hk (parLev_St hkp) (hkr' ▸ hg0))) PP
  have h2 : redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0) PP.1 (finE (D.sp.Y 0) k) = g :=
    GlobalTheory.MemMatch.reductionBlock_injective_of_eq hr' hn _ _ ((congrFun hkr' PP).trans (Function.update_self _ _ _))
  rwa [h2] at h1

set_option maxHeartbeats 2000000 in

theorem mem_rowJ_iff_rTup : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → GlobalTheory.LevZero.StabAt f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (GlobalTheory.LevZero.frAt f B a₀ a) → (κ ∈ rowJ W.S.X W.Q.instEq ↔ Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (GlobalTheory.LevZero.frAt f B a₀ a) (GlobalTheory.LevZero.datZero W) (finE (D.sp.Y 0) κ) ∈ (GlobalTheory.LevZero.datZero W).P.H) := by
  intro D L hT Gi Gl Kc Yd cX ex W hPk u f B hPl a₀ hH0 a _ hac hStab κ hκ hκS
  obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, hc, hv, hvt, hsh, hpin, hread, hbt⟩ := hPl
  have hBot := GlobalTheory.T.bessel_local_type_data W hPk u f B k ι v o n G pl ⟨hc, hv, hvt, hsh, hpin, hread, hbt⟩
  have h0 := h0_eq D
  have hκ1 : (iotaX W.S.X W.Q.instEq κ).1 = 1 := (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq κ).2 hκ
  show (iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.K2 ↔ _
  exact (and_iff_right hκ1).trans (mem_K_two_iff W hPk f B _ hBot h0 (hbt.lev h0) hbt.adapted hbt.trace a₀ hH0 a hac _ _ rfl rfl
    hStab κ hκ hκS)

end GlobalTheory.LevZeroMem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateCompactMemLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevConj

variable {D : D7}

theorem mem_idAt_of_eq {P : Pl D → Prop} {v : Pl D} (hv : P v) {a : AE D} (ha : a ∈ idAt D (· = v)) : a ∈ idAt D P := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hw => w.2 (by rw [hw]; exact hv)⟩⟩

theorem latV_supp_iff (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) {P : Pl D → Prop} {v : Pl D}
    (hv : P v) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S L P ↔ y ∈ latV S L (· = v) := by
  have hT := ((GlobalTheory.FinPl.localComponents D P).2 S).2.2.2 L y hL
  have hV := ((GlobalTheory.FinPl.localComponents D (· = v)).2 S).2.2.2 L y hL
  rw [hT, hV]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hy, fun w hw e he => h w (by rw [hw]; exact hv) e he⟩
  · rintro ⟨_, h⟩
    refine ⟨fun i => mem_idAt_of_eq hv (hy i), fun w _ e he => ?_⟩
    by_cases hwv : w = v
    · exact h w hwv e he
    · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.FinPl.localComponents D (· = w)).1
      have hzero : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = w) := by
          have h' := hy i
          simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'
          simp only [idOff, Submodule.mem_iInf]
          intro u
          exact h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩
        have h1 : ε * e = e := (hAt e).1 he.1
        have h2 : ε * y i = 0 := (hOff (y i)).1 hyi
        show e * y i = 0
        rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
      rw [hzero]
      exact (latV S L (· = w)).zero_mem

theorem moves_at_of_moves {S : HSp D} {L : Lat S} (hL : Submodule.IsLattice D.host.E L) {P : Pl D → Prop} {v : Pl D}
    (hv : P v) {g : GA D S} (h : Moves S g L L P) : Moves S g L L (· = v) := by
  intro y hy
  rw [← latV_supp_iff S L hL hv y hy, ← latV_supp_iff S L hL hv _ (GlobalTheory.FinPl.KOpen.supp_mulVec S _ g hy)]
  exact h y fun i => mem_idAt_of_eq hv (hy i)

end GlobalTheory.LevConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProofStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.AllComb D := by
  first | exact @GlobalTheory.FinPl.allComb | exact GlobalTheory.FinPl.allComb | (intros; apply GlobalTheory.FinPl.allComb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFramesFirstRelationMeanZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.DepFrames

theorem gramQ_mul {D : D7} (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (u : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    gramQ W (x * u) = uᴴ * gramQ W x * u := by
  simp only [gramQ, conjTranspose_mul, Matrix.mul_assoc]

theorem dep_frames_mean_zero : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∀ j : Fin ρ, ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x = gramQ W x₀ ∧ (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  intro D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ j
  classical
  have : Countable D.host.E := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE
  have : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  obtain ⟨hLC, hSC, -, -, -, hDisc, hCnt⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have h56 := GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D V V₀ ρ d
  haveI : LocallyCompactSpace (flagN d) := h56.1.locallyCompactSpace
  haveI : SecondCountableTopology (flagN d) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : vN.ν.IsHaarMeasure := vN.unit.1
  obtain ⟨hle, hNcl, hNnorm, K, hK, hcov⟩ := h56.2 (Nfix d j) (Or.inr (Or.inr ⟨j, rfl⟩))
  have hT := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hw hw' vS
  have hcont : ∀ x, Continuous fun n : flagN d => term ψ d W vS (om (n.1, 1) Ψ) x := fun x =>
    ((hT Ψ hΨ).2.2.2.1 x).comp (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hw hw' vS Ψ hΨ
  obtain ⟨K0, hK0, hcov0⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨Mb, hMb⟩ := hK0.exists_bound_of_continuousOn (f := fun n : flagN d => Th n.1) hTh.cont.continuousOn
  have hThb : ∀ n : flagN d, ‖Th n.1‖ ≤ Mb := by
    intro n
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov0 n
    have hγ' : (γ : GA D V) ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have : Th ((γ * k : flagN d) : GA D V) = Th k.1 := hTh.left γ.1 hγ' γ.2 k.1 k.2
    rw [this]
    exact hMb k hk
  have hbdS : ∀ (S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E)) (n : flagN d),
      ∑' x : S, ‖Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1‖ₑ ≤
        ((Mb.toNNReal * (C * (height V 1 * quotHeight W 1) ^ A).toNNReal : NNReal) : ENNReal) := by
    intro S n
    have h1 : ∑' x, ‖term ψ d W vS (om (n.1, 1) Ψ) x‖ₑ ≤ ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) := by
      have := hC 1 1 n.1 n.2
      rwa [mul_one] at this
    simp_rw [enorm_mul]
    rw [ENNReal.tsum_mul_left, ENNReal.coe_mul]
    refine mul_le_mul' ?_ ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans h1)
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hThb n)
  let Pj : Matrix (Fin W.rank) (Fin ρ) D.host.E → Prop := fun x => gramQ W x = gramQ W x₀ ∧
    (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
    ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0
  have huniq : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E,
      (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) →
      ∀ a a' : Fin ρ → D.host.E, a j = 1 → (∀ i, j < i → a i = 0) → x *ᵥ a = 0 →
        a' j = 1 → (∀ i, j < i → a' i = 0) → x *ᵥ a' = 0 → a = a' := by
    intro x hind a a' ha1 ha2 ha3 hb1 hb2 hb3
    refine sub_eq_zero.1 (hind (a - a') (fun i hi => ?_) (by rw [Matrix.mulVec_sub, ha3, hb3, sub_self]))
    rcases hi.lt_or_eq with h | h
    · simp [ha2 i h, hb2 i h]
    · subst h; simp [ha1, hb1]
  have hPu : ∀ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, u * u' = 1 → u' * u = 1 → (∀ i, u i i = 1) →
      (∀ i k, k < i → u i k = 0) → ∀ x, Pj x ↔ Pj (x * u) := by
    intro u u' huu' hu'u hdiag htri x
    have hG := GlobalTheory.T.gramMatrixOfColumns_unitriangular_conj_eq D W ρ x₀ hB u hdiag htri
    refine and_congr ⟨fun h => by rw [gramQ_mul, h, hG], fun h => ?_⟩ ((GlobalTheory.T.dependent_frame_first_column_relation D.host.E W.rank ρ x).2.2 j u hdiag htri)
    rw [gramQ_mul, ← hG] at h
    have h' := congrArg (fun M => u'ᴴ * M * u') h
    have e1 : ∀ M : Matrix (Fin ρ) (Fin ρ) D.host.E, u'ᴴ * (uᴴ * M * u) * u' = M := by
      intro M
      rw [show u'ᴴ * (uᴴ * M * u) * u' = (u * u')ᴴ * M * (u * u') by
        simp only [conjTranspose_mul, Matrix.mul_assoc]]
      rw [huu', conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rwa [e1, e1] at h'

  have key : ∀ γ : flagN d, γ.1 ∈ GQ V → ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ.1 →
      ∀ (n : flagN d) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E),
        Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) x = Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) (x * u) := by
    intro γ hγ u hu n x
    have hom : om ((γ * n).1, 1) Ψ = om (γ.1, 1) (om (n.1, 1) Ψ) := by
      rw [show (((γ * n : flagN d) : GA D V), (1 : GA D W)) = (γ.1, 1) * (n.1, 1) by
        rw [Prod.mk_mul_mk, one_mul]; rfl, map_mul]
      rfl
    rw [hom, (hT _ (hw.om_pres _ _ hΨ)).2.1 γ.1 hγ γ.2 x (x * u) (by rw [rat_mul, hu]),
      show ((γ * n : flagN d) : GA D V) = γ.1 * n.1 from rfl, hTh.left γ.1 hγ γ.2 n.1 n.2]
  have hfixv : ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (∀ i k, k ≤ j → u i k = if i = k then 1 else 0) →
      ∀ c : Fin ρ → D.host.E, (∀ i, j < i → c i = 0) → u *ᵥ c = c := by
    intro u hu c hc
    funext i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl (g := fun k => if i = k then c k else 0) fun k _ => ?_, Finset.sum_ite_eq]
    · simp
    · rcases le_or_gt k j with h | h
      · rw [hu i k h]; split_ifs <;> simp
      · rw [hc k h]; simp
  refine GlobalTheory.T.integral_tsum_normal_eigenfunctions_eq_zero (flagN d) vN.ν ((GQ V).subgroupOf (flagN d)) ((Nfix d j).subgroupOf (flagN d)) ?_ ?_ hNnorm
    (hNcl.preimage continuous_subtype_val) ?_ vN.𝓝 vN.unit.2.1 (by rw [vN.unit.2.2]; exact ENNReal.one_ne_top)
    {x // Pj x} (Fin ρ → D.host.E) (fun x => Classical.choose x.2.2.2)
    (fun x n => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) (fun x => (hTh.cont.mul (hcont x.1)).measurable)
    ⟨_, fun n => hbdS {x | Pj x} n⟩ ?_ ?_ ?_
  · exact Function.Injective.countable (f := fun x : ((GQ V).subgroupOf (flagN d)) =>
      (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : GQ V))
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun y : GQ V => y.1) h)))
  · exact DiscreteTopology.of_continuous_injective (f := fun x : ((GQ V).subgroupOf (flagN d)) =>
      (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : GQ V))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun y : GQ V => y.1) h)))
  · refine ⟨(fun m : Nfix d j => (⟨⟨m.1, hle m.2⟩, m.2⟩ : (Nfix d j).subgroupOf (flagN d))) '' K,
      hK.image ((continuous_subtype_val.subtype_mk _).subtype_mk _), fun m => ?_⟩
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov ⟨m.1.1, Subgroup.mem_subgroupOf.1 m.2⟩
    refine ⟨⟨⟨γ.1, hle γ.2⟩, γ.2⟩, ?_, ⟨⟨k.1, hle k.2⟩, k.2⟩, ⟨k, hk, rfl⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]; exact Subgroup.mem_subgroupOf.1 hγ
    · have e2 : m.1.1 = γ.1 * k.1 := congrArg Subtype.val e
      exact Subtype.ext (Subtype.ext e2)
  · intro γ hγ n
    have hγ' : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨u, u', hu, huu', hu'u, hdiag, htri, -⟩ := GlobalTheory.T.rational_flagUnipotent_isotropicBlock_unitriangular D V V₀ ρ d γ.1 hγ' γ.2
    let e : {x // Pj x} ≃ {x // Pj x} :=
      { toFun := fun x => ⟨x.1 * u, (hPu u u' huu' hu'u hdiag htri x.1).1 x.2⟩
        invFun := fun x => ⟨x.1 * u', (hPu u u' huu' hu'u hdiag htri (x.1 * u')).2
          (by rw [Matrix.mul_assoc, hu'u, Matrix.mul_one]; exact x.2)⟩
        left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, huu', Matrix.mul_one])
        right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hu'u, Matrix.mul_one]) }
    show ∑' i : {x // Pj x}, Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) i.1 =
      ∑' i : {x // Pj x}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1
    rw [← e.tsum_eq (fun i => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1)]
    exact tsum_congr fun i => key γ hγ' u hu n i.1
  · intro c γ hγ hγM n
    have hγ' : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨u, u', hu, huu', hu'u, hdiag, htri, hfix⟩ := GlobalTheory.T.rational_flagUnipotent_isotropicBlock_unitriangular D V V₀ ρ d γ.1 hγ' γ.2
    have hfu := hfixv u (hfix j (Subgroup.mem_subgroupOf.1 hγM))
    let e : {x // Pj x} ≃ {x // Pj x} :=
      { toFun := fun x => ⟨x.1 * u, (hPu u u' huu' hu'u hdiag htri x.1).1 x.2⟩
        invFun := fun x => ⟨x.1 * u', (hPu u u' huu' hu'u hdiag htri (x.1 * u')).2
          (by rw [Matrix.mul_assoc, hu'u, Matrix.mul_one]; exact x.2)⟩
        left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, huu', Matrix.mul_one])
        right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hu'u, Matrix.mul_one]) }
    have hκ : ∀ x : {x // Pj x}, Classical.choose (e x).2.2.2 = Classical.choose x.2.2.2 := by
      intro x
      have s1 := Classical.choose_spec (e x).2.2.2
      have s0 := Classical.choose_spec x.2.2.2
      exact huniq _ (e x).2.2.1 _ _ s1.1 s1.2.1 s1.2.2 s0.1 s0.2.1
        (by show (x.1 * u) *ᵥ _ = 0; rw [← Matrix.mulVec_mulVec, hfu _ s0.2.1, s0.2.2])
    let e' := e.subtypeEquiv (p := fun x => Classical.choose x.2.2.2 = c) (q := fun x => Classical.choose x.2.2.2 = c)
      (fun x => by rw [hκ x])
    show ∑' i : {i : {x // Pj x} // Classical.choose i.2.2.2 = c}, Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) i.1.1 =
      ∑' i : {i : {x // Pj x} // Classical.choose i.2.2.2 = c}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1.1
    rw [← e'.tsum_eq (fun i => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1.1)]
    exact tsum_congr fun i => key γ hγ' u hu n i.1.1
  · intro c
    by_cases hc : ∃ x : {x // Pj x}, Classical.choose x.2.2.2 = c
    · obtain ⟨x, hx⟩ := hc
      have s0 := Classical.choose_spec x.2.2.2
      rw [hx] at s0
      have hg : gramQ W x₀ *ᵥ c = 0 := by
        rw [← x.2.1, gramQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, s0.2.2, Matrix.mulVec_zero,
          Matrix.mulVec_zero]
      obtain ⟨v, u, a, hform, htr, huN, ha, hTu⟩ := hTh.dep j c s0.1 s0.2.1 hg
      refine ⟨⟨u, hle huN⟩, huN, a, ha, fun y hy m hm n => ?_⟩
      have sy := Classical.choose_spec y.2.2.2
      rw [hy] at sy
      have hm' : m.1 ∈ Nfix d j := Subgroup.mem_subgroupOf.1 hm
      show Th (m.1 * u * n.1) * term ψ d W vS (om (m.1 * u * n.1, 1) Ψ) y.1 =
        a * (Th (m.1 * n.1) * term ψ d W vS (om (m.1 * n.1, 1) Ψ) y.1)
      rw [hTu m.1 m.2 n.1 n.2, GlobalTheory.T.transvection_trivial_after_flagUnipotentFixing D hDesc ψ V V₀ W ρ d χV χW om hw vS Ψ hΨ j c s0.2.1 v u hform htr y.1 sy.2.2
        m.1 hm' n.1, mul_assoc]
    · push_neg at hc
      exact ⟨1, one_mem _, 0, zero_ne_one, fun x hx => absurd hx (hc x)⟩

end GlobalTheory.Unf.DepFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearEquivariantOrthogonalSummandLiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bilinear_equivariant_orthogonalSummandLift : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∃ lS : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → Vac ψ S T LS LT (· = p.v) f₀ → ∃ θ : GlobalTheory.FinPl.SrcGl.CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ), (∀ (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ) (f : WO S T → ℂ), Over ψ α₀ β LS LT f₀ Φ f → θ v Φ = liftA o om vA v f) ∧ ∀ (g : GL n' k) (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) → θ (GlobalTheory.FinPl.SrcGl.caRep α g v) (fun x => Φ (x * (GlobalTheory.FinPl.SrcGl.blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ := by
  first | exact @GlobalTheory.FinPl.SrcTheta.exists_theta | exact GlobalTheory.FinPl.SrcTheta.exists_theta | (intros; apply GlobalTheory.FinPl.SrcTheta.exists_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralGlueLocalHomothetiesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_glue_localHomotheties : ∀ (D : D7) (V A : HSp D) (e : GA D A →* GA D V) (g : GA D V) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → (∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v)) → (∀ v : GlobalTheory.FinPl.Pl D, ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves V c (g * e a) L M v) → ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ z ∈ Subgroup.center (GA D V), Moves V (z * (g * e a)) L M (fun _ => True) := by
  first | exact @GlobalTheory.Core.Mi.LatGlue.glue | exact GlobalTheory.Core.Mi.LatGlue.glue | (intros; apply GlobalTheory.Core.Mi.LatGlue.glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCombinationRebaseVacuumLatticesInjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_combination_rebase_vacuumLattices_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)), IsSelfDualC S M → IsSelfDualC S N → IsSelfDualC T M' → IsSelfDualC T N' → (∀ p ∈ Q, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p))) → (∀ p, p ∉ Q → GlobalTheory.FinPl.latV S M (· = p) = GlobalTheory.FinPl.latV S N (· = p) ∧ GlobalTheory.FinPl.latV T M' (· = p) = GlobalTheory.FinPl.latV T N' (· = p)) → ∃ o : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ Q) o ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) f → GlobalTheory.FinPl.Vac ψ S T N N' (fun _ => True) (comb ψ S T o f) ∧ (f ≠ 0 → comb ψ S T o f ≠ 0) := by
  first | exact @GlobalTheory.VacRebase.rebase_vac | exact GlobalTheory.VacRebase.rebase_vac | (intros; apply GlobalTheory.VacRebase.rebase_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticesGoodPositionAllPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattices_goodPosition_all_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → IsSelfDualC c.T v.NT → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : Lat c.Lz, IsSelfDualC _ LZ ∧ OrthAt (c.oT n h) (c.x n).L v.NT LZ x) → ∃ (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, Frame (o.p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j)) ∧ (∀ x, GoodAt { v with N := N } { o with M := M, β₀ := β₀ } x) ∧ (∀ x, x ∉ v.tP → SplitAt { v with N := N } { o with M := M, β₀ := β₀ } x) ∧ ∀ j ρ h i, GluedCore (c.B j ρ h) (M j ρ h) o.q (o.β j i) (β₀ j ρ h i) (o.Q j i) := by
  first | exact @GlobalTheory.GoodPos.exists_goodAt | exact GlobalTheory.GoodPos.exists_goodAt | (intros; apply GlobalTheory.GoodPos.exists_goodAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedThetaLiftCommutesSplitPlaceOperatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedThetaLift_commutes_splitPlace_operators : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), CoCpt S → ∀ (vS : Vol S) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → ∀ (α : Frame p S n') (β : Frame p T n) (P : Pair k n') (Q : Pair k n), ∃ c : ℂ, c ≠ 0 ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ f : WO S T → ℂ), Over ψ α β LS LT f₀ (phiOne P Q) f → ∀ φ₀, RamAt α P φ₀ → RamAt β Q (liftT om vS.μ vS.𝓕 φ₀ f) ∧ ∀ ε : 𝓀[k]ˣ, liftT om vS.μ vS.𝓕 (sOp α P q (resChar χ hχ q) ε φ₀) f = c • sOp β Q q (resChar χ hχ q) ε (liftT om vS.μ vS.𝓕 φ₀ f) := by
  first | exact @GlobalTheory.FinPl.lift_sOp_comm | exact GlobalTheory.FinPl.lift_sOp_comm | (intros; apply GlobalTheory.FinPl.lift_sOp_comm <;> assumption)
end

