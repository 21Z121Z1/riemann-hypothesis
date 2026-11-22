import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0613
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0075
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0103
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0112
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0126
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0159
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0829
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0828
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0127
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0191
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0149
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0096
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0092
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0105

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemTupleFreeLevelOfMemKStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_tuple_free_mem_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ κ, GlobalTheory.FinPl.InK _ (a.g.x j).L (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) κ → κ ∈ _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj := by
  first | exact @_root_.GlobalTheory.PenLev.mem_tuple_free_level_of_mem_K_alt | exact _root_.GlobalTheory.PenLev.mem_tuple_free_level_of_mem_K_alt | (intros; apply _root_.GlobalTheory.PenLev.mem_tuple_free_level_of_mem_K_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointCases
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.SerRefCore
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SerRefPt
section Core
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
end Core
end GlobalTheory.SerRefPt
namespace GlobalTheory.SerRefPt
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 3200000 in
theorem fw_eq_zero_or_exists_norm_algComb (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (hR : p.PointConditions')
    (hM : More p) (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m) (h0 : RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j)
    (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool) (h : RealPin p.R p.cG ρ) :
    (∀ y ∈ (p.R.FW j).WK, y = 0) ∨ ∃ ν, IsNorm p.R p.v₀ (ρ.B t j b) ν ∧ ∀ s g P, ρ.IsDatum t j b s g P →
      P ∈ ρ.lat t j b (smallInt (Fm.D x i)) g → AlgComb p.nexp p.v₀ j (ν • ρ.theta t j b g P) := by
  obtain ⟨c', w, hw, hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (_root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 hP Fm x hx i p hR hM t j h0)
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (fullHeckeRealDatMovedReadings p.R w).toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w hw h0.unif
  have hG : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsFam := { c.fam with }
  have hMo : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsModels := { c.models with }
  have hCh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsChain := { c.chain with }
  have hTh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (fullHeckeRealDatMovedReadings p.R w).toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((fullHeckeRealDatMovedReadings p.R w).phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (fullHeckeRealDatMovedReadings p.R w) (F2 p) B'.κ B'.v₀ B'.O t j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  have hpin' : RealPin (fullHeckeRealDatMovedReadings p.R w) p.cG ρ :=
    ⟨h.psi, h.inf, h.cartT, h.onbS, h.onbT, h.latS, h.latT, h.frS, h.frT, h.vac, h.Pg, h.grp, h.mu0, h.eta, h.delta, h.deltaPl,
      h.ap, h.am⟩
  have hsp : (Fm.D x i).host.cls (Fm.D x i).host.pde = PrimeClass.splitK ∧
      (Fm.D x i).host.cls (Fm.D x i).host.pde' = PrimeClass.splitK :=
    ⟨(Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.1, (Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.2⟩
  have H := core_cases (T := setCE p.T c') (Rl := fullHeckeRealDatMovedReadings p.R w) hA hRF hS (GlobalTheory.UnframeForms.movedYS p.nexp w) hρ b hpin' hRat hsp
  rw [hv] at H
  rcases H with H | ⟨ν, hN, H⟩
  · exact Or.inl H
  · exact Or.inr ⟨ν, hN, fun s g P hd hl => algComb_of_moved p.nexp w p.v₀ j (H s g P hd hl)⟩
theorem serRef_of_reciprocity_ray_class : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.SerRefAlt := by
  intro hP hA hRF hS
  have hL := _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt
  have hT := _root_.GlobalTheory.BigOn.Exp.twAdm_alt
  unfold _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace at hL
  unfold _root_.GlobalTheory.BigOn.Exp.TwAdmAlt at hT
  unfold _root_.GlobalTheory.BigOn.Exp.SerRefAlt
  refine (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hL hT).imp fun Fm x hx i p hp hM w _ j h => ?_
  intro ρ hρ ν hpin hN hR0
  refine ⟨ν, hN, hR0, fun s g P hd hl => ?_⟩
  rcases _root_.GlobalTheory.SerRefPt.fw_eq_zero_or_exists_norm_algComb hP hA hRF (GlobalTheory.SerStd.seriesRatS_of hS) Fm x hx i p hp hM _ j
    (_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hp hM _ h.2.2.2 h.1 j) ρ hρ _ hpin with H | ⟨ν₁, hN₁, H⟩
  · have h0 := theta_eq_zero p.nexp p.v₀ hρ _ j _ H hR0 hd
    have h1 : AlgComb p.nexp p.v₀ j (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) g P) := by
      rw [h0, smul_zero]
      exact AlgComb.zero
    exact h1
  · obtain ⟨ζ, hζ, e⟩ := exists_root_of_isNorm p.R p.v₀ _ hN₁ hN
    have h1 : AlgComb p.nexp p.v₀ j (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) g P) := by
      rw [e, mul_smul]
      exact (H s g P hd hl).smul hζ
    exact h1
end GlobalTheory.SerRefPt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PuNZMember
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MiTop
open GlobalTheory.Core.Rk
theorem puNZ_member_alt : GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.MiTop.PuNZ D) := by
  intro hRow hL p hTP
  have hR := fun Cg CT : ℝ => hRow Cg (1 / 4) 3 (1 / 2) CT (by norm_num) (by norm_num)
  choose Cf Af Bf hC hrow using hR
  have h1 := _root_.GlobalTheory.T.exists_constants_for_parameters_scale_bundle hL p (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
  have h2 := _root_.GlobalTheory.T.degHypL_all_linked_good_members hL p (fun C => Af (C.P.CYL + 1) C.CTu) (fun C => Bf (C.P.CYL + 1) C.CTu)
  have h3 : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
      (fun κ _ _ _ _ => Cf (κ.C.P.CYL + 1) κ.C.CTu + 1 ≤ κ.C.CGam) :=
    EvP.mono (fun _ _ _ h _ _ _ _ _ => h) (evP_cGam fun a b => Cf a b + 1)
  refine (((hTP.and h1).and h2).and h3).imp fun κ K β c b hk _ _ h => ?_
  obtain ⟨⟨⟨hT, -, -, -, -, -, -, -, ⟨t1, t2, -, t4, t5⟩, -, hmu, -⟩, hH⟩, hG⟩ := h
  have hD : TrueD β.D := _root_.GlobalTheory.Fam.trueD_of_truePack_alt _ hT
  have hCG : β.O.L.CGam = κ.C.CGam := by rw [← hk.1]; exact β.val.CGam_eq
  have hC1 := hC (κ.C.P.CYL + 1) κ.C.CTu
  refine puNZ_of_sDiag β.O.L hC1 (hCG ▸ hG) hD ⟨t1, t2, hH, t4, t5⟩ hmu fun u => ?_
  exact hrow _ _ _ _ (le_max_left _ _) (le_max_left _ _) β.D _ u (trueE_of_trueD hD)
    ⟨⟨β.O.L, rfl, by rw [hCG]; exact le_max_right _ _, by rw [hCG]; linarith⟩, hmu⟩ ⟨t1, t2, hH, t4, t5⟩
end GlobalTheory.MiTop
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideB
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def Mv.sideB_alt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {low Pq S hk eig θ} (x : SideB D cf A.row low Pq S hk eig θ) : SideB m.D (m.cf cf) (m.sideA_alt A).row low Pq S hk eig θ := @_root_.GlobalTheory.HeightCounting.SideB.mk (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (twF := @_root_.GlobalTheory.HeightCounting.TwFrameC.mk (_)
      (K0 := (by with_unfolding_all exact (x.twF.K0 :)))
      (eO0 := (by with_unfolding_all exact (x.twF.eO0 :)))
      (j0 := (by with_unfolding_all exact (x.twF.j0 :)))
      (Lw := (by with_unfolding_all exact (x.twF.Lw :)))
      (eO := (by with_unfolding_all exact (x.twF.eO :)))
      (eOk := (by with_unfolding_all exact (x.twF.eOk :)))
      (iCq := (by with_unfolding_all exact (x.twF.iCq :)))
      (S0x := (by with_unfolding_all exact (x.twF.S0x :))))
    (tw := @_root_.GlobalTheory.HeightCounting.TwistFrameLowIndexCompatibility.mk (_) (_) (_)
      (pl_emb := (by with_unfolding_all exact (x.tw.pl_emb :)))
      (ringSpec_baseIntegersEquiv_algebraMap := (by with_unfolding_all exact (x.tw.ringSpec_baseIntegersEquiv_algebraMap :)))
      (ringSpec_baseEmbedding_compatible := (by with_unfolding_all exact (x.tw.ringSpec_baseEmbedding_compatible :)))
      (eO_alg := (by with_unfolding_all exact (x.tw.eO_alg :)))
      (eOk_alg := (by with_unfolding_all exact (x.tw.eOk_alg :)))
      (mu_g := (by with_unfolding_all exact (x.tw.mu_g :)))
      (hk_split := (by with_unfolding_all exact (x.tw.hk_split :)))
      (ringSpec_excludedPlaces_eq := (by with_unfolding_all exact (x.tw.ringSpec_excludedPlaces_eq :)))
      (concreteTwistFrame_extraExcludedPlaces_conj := (by with_unfolding_all exact (x.tw.concreteTwistFrame_extraExcludedPlaces_conj :)))
      (B_range := (by with_unfolding_all exact (x.tw.B_range :)))
      (sig_inj := (by with_unfolding_all exact (x.tw.sig_inj :)))
      (qs_pos := (by with_unfolding_all exact (x.tw.qs_pos :)))
      (concreteTwistFrame_extraExcluded_over_smallPrimes := (by with_unfolding_all exact (x.tw.concreteTwistFrame_extraExcluded_over_smallPrimes :))))
    (cover := (by with_unfolding_all exact (x.cover :)))
    (chiD := @_root_.Formalism.L2.NC.NChiData.mk (_)
      (mu0 := (by with_unfolding_all exact (x.chiD.mu0 :)))
      (etaT := (by with_unfolding_all exact (x.chiD.etaT :)))
      (del := (by with_unfolding_all exact (x.chiD.del :)))
      (psi := (by with_unfolding_all exact (x.chiD.psi :)))
      (chiI := (by with_unfolding_all exact (x.chiD.chiI :)))
      (embO := (by with_unfolding_all exact (x.chiD.embO :))))
    (chi := @_root_.Formalism.L2.NC.NormalizedCharacterCompatibility.mk (_) (_)
      (psi := (by with_unfolding_all exact (x.chi.psi :)))
      (del_fix := (by with_unfolding_all exact (x.chi.del_fix :)))
      (delta := (by with_unfolding_all exact (x.chi.delta :)))
      (chi1 := (by with_unfolding_all exact (x.chi.chi1 :)))
      (ringSpec_sidedEmbedding_fixedField := (by with_unfolding_all exact (x.chi.ringSpec_sidedEmbedding_fixedField :)))
      (etaT_unr := (by with_unfolding_all exact (x.chi.etaT_unr :)))
      (etaT_inf := (by with_unfolding_all exact (x.chi.etaT_inf :)))
      (lamG := (by with_unfolding_all exact (x.chi.lamG :))))
    (eta_eq := (by with_unfolding_all exact (x.eta_eq :)))
    (ringSpec_normalisedCharacter_eq := (by with_unfolding_all exact (x.ringSpec_normalisedCharacter_eq :)))
    (del_eq := (by with_unfolding_all exact (x.del_eq :)))
    (iCq_embO := (by with_unfolding_all exact (x.iCq_embO :)))
    (embO_star := (by with_unfolding_all exact (x.embO_star :)))
    (deltaRead := (by with_unfolding_all exact (x.deltaRead :)))
    (exp := @_root_.Formalism.L2.NExpTied.mk (_)
      (U_eq := (by with_unfolding_all exact (x.exp.U_eq :)))
      (psiU_gen := (by with_unfolding_all exact (x.exp.psiU_gen :)))
      (psiU_side := (by with_unfolding_all exact (x.exp.psiU_side :)))
      (psiU_xi := (by with_unfolding_all exact (x.exp.psiU_xi :)))
      (delU_cont := (by with_unfolding_all exact (x.exp.delU_cont :)))
      (delU_ine := (by with_unfolding_all exact (x.exp.delU_ine :)))
      (thU_empty := (by with_unfolding_all exact (x.exp.thU_empty :)))
      (sgnT := (by with_unfolding_all exact (x.exp.sgnT :)))
      (sgnT_one := (by with_unfolding_all exact (x.exp.sgnT_one :)))
      (Wt := (by with_unfolding_all exact (x.exp.Wt :)))
      (acgWt := (by with_unfolding_all exact (x.exp.acgWt :)))
      (modWt := (by with_unfolding_all exact (x.exp.modWt :)))
      (fdWt := (by with_unfolding_all exact (x.exp.fdWt :)))
      (rhoW := (by with_unfolding_all exact (x.exp.rhoW :)))
      (rhoW_irr := (by with_unfolding_all exact (x.exp.rhoW_irr :)))
      (rhoW_alg := (by with_unfolding_all exact (x.exp.rhoW_alg :)))
      (tauG := (by with_unfolding_all exact (x.exp.tauG :)))
      (sgnG := (by with_unfolding_all exact (x.exp.sgnG :)))
      (sgnG_one := (by with_unfolding_all exact (x.exp.sgnG_one :)))
      (tau_galois_first_character := (by with_unfolding_all exact (x.exp.tau_galois_first_character :)))
      (mtV := @fun x1 => @fun x2 => @fun x3 => @fun x4 => @fun x5 => @fun x6 => @fun x7 => @fun x8 => @fun x9 => @_root_.Formalism.L2.NX.MtVReal.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
        (W := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).W : _)))
        (acg := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).acg : _)))
        (mod := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).mod : _)))
        (fd := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).fd : _)))
        (ρ := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).ρ : _)))
        (irr := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).irr : _)))
        (alg := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).alg : _)))
        (bc := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).bc : _)))
        (J := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J : _)))
        (χ := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).χ : _)))
        (J_open := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J_open : _)))
        (hyp := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).hyp : _)))
        (QP := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP : _)))
        (QP_sub := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_sub : _)))
        (QP_cover := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_cover : _)))
        (QP_nconj := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_nconj : _)))
        (DP := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP : _)))
        (DP_sub := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_sub : _)))
        (DP_cover := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_cover : _)))
        (DP_nconj := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_nconj : _)))
        (sp := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).sp : _)))
        (sp_w := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).sp_w : _)))
        (redG := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).redG : _)))
        (J_mem := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J_mem : _)))
        (chi_eq := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).chi_eq : _)))
        (real := (by with_unfolding_all exact ((@_root_.Formalism.L2.NExpTied.mtV (_) x.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).real : _))))
      (rhoW_hw := (by with_unfolding_all exact (x.exp.rhoW_hw :)))
      (rhoW_wt := (by with_unfolding_all exact (x.exp.rhoW_wt :))))
    (pq := (by with_unfolding_all exact (x.pq :)))
    (psiU := (by with_unfolding_all exact (x.psiU :)))
    (rho := (by with_unfolding_all exact (x.rho :)))
    (chiL := (by with_unfolding_all exact (x.chiL :)))
    (hs := (by with_unfolding_all exact (x.hs :)))
    (eF := (by with_unfolding_all exact (x.eF :)))
    (bsup := (by with_unfolding_all exact (x.bsup :)))
    (act := (by with_unfolding_all exact (x.act :)))
    (cHk := (by with_unfolding_all exact (x.cHk :)))
    (hkEq := (by with_unfolding_all exact (x.hkEq :)))
    (cHk_del := (by with_unfolding_all exact (x.cHk_del :)))
    (hk_emb := (by with_unfolding_all exact (x.hk_emb :)))
    (sigSpan := (by with_unfolding_all exact (x.sigSpan :)))
    (rowS := (by with_unfolding_all exact (x.rowS :)))
    (rowS_eig := (by with_unfolding_all exact (x.rowS_eig :)))
    (hEig_zero := (by with_unfolding_all exact (x.hEig_zero :)))
    (rhoS := (by with_unfolding_all exact (x.rhoS :)))
section
end
section
end
end GlobalTheory.LayerMove
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StFacts
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.SerCarry
open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr
theorem st_facts_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (g : Geo x) (hg : GlobalTheory.RealGeo.InGeo g) (a : BigHost (Dof x)) :
    HkAd (sideAt x g hg a) l.rat.In.Sb ((l.rat.In.hL)) ∧ KeepsMat (D := Dof x) fun i => (l.mt.ad.PV i).ψ :=
  ⟨(l.rat.rat.hecke), x.r.Y.hF, l.mt.ad.id⟩
end GlobalTheory.HeightCounting.SerCarry
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedDataSAssemble
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
open Formalism.L2 in
set_option maxHeartbeats 1000000 in
theorem tiedDataS_assemble_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} (ex : Extra D L hT Gi Gl K Y cX)
    (host : Formalism.L2.Host.HostTied D) (level : Formalism.L2.Host.LevelTied D) (cols : Formalism.L2.Forms.ColsTiedSym D) (full : Formalism.L2.Forms.ColsFullS cols)
    (extra : Formalism.L2.Forms.ColsExtraTiedS full ex) (provA : Formalism.BasicNotions.TH.ProvA) (theta : Formalism.L2.Theta.AllTied D ex.th provA) (twIn : Formalism.MainNotions.TwIn D)
    (n : _root_.Formalism.L2.NTiedAllAlt D ex.nch twIn) (frameN : ∀ x, n.gal.fr.jE x = host.fr.j x)
    (cf : Formalism.L2.Host.CharFrame D) (tp : Formalism.L2.Host.TupTied D cf ex.nch)
    (h : (⟨n.cf, n.tp⟩ : Σ c : Formalism.L2.Host.CharFrame D, Formalism.L2.Host.TupTied D c ex.nch) = ⟨cf, tp⟩)
    (thetaChr : Formalism.L2.Host.ThetaChrTied D cf ex.nch tp ex.th) (chrVal : Formalism.L2.Host.ValLL0 D cf) (chrDt : Formalism.L2.Host.DtTied D cf)
    (chrN : Formalism.L2.Host.NCharTied D cf ex.nch tp) (chrGal : Formalism.L2.Host.NGalChrTied D cf ex.nch tp)
    (chrPsi : Formalism.L2.Host.PsiChoiceCompatible D cf ex.nch tp) (sameChr : Formalism.L2.JoinChr.SameChr theta.T thetaChr)
    (what₂ : Formalism.L2.Rows.RowsCompatible D host cf tp) (inK : Y.Lev → ℕ → Prop) (geo : Formalism.L2.Geo.GeoTiedP Y inK)
    (tw0 : TwForms D) (he : ex.tw = tw0) (tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes tp cols tw0) (emt : Formalism.L2.Rows.EMtTied D cols tw)
    (g : Formalism.L2.G.GroupCompatibilityAll D hT ex.cmp) (herm_eq : g.herm = full.1.to0) (forms_eq : g.forms = fun u => (cols.forms u).to0)
    (P : ∀ (c : Formalism.L2.Host.CharFrame D) (t : Formalism.L2.Host.TupTied D c ex.nch) (C : Formalism.L2.Forms.ColsTiedSym D), Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes t C tw0 → Prop)
    (hP : P cf tp cols tw) :
    ∃ S : _root_.Formalism.L2.TiedDataSAlt ex, S.host = host ∧ S.cols = cols ∧ HEq S.full full ∧ S.g = g ∧
      (⟨S.provA, S.theta⟩ : Σ a, Formalism.L2.Theta.AllTied D ex.th a) = ⟨provA, theta⟩ ∧
      (⟨S.twIn, S.n⟩ : Σ I, _root_.Formalism.L2.NTiedAllAlt D ex.nch I) = ⟨twIn, n⟩ ∧ HEq S.thetaChr thetaChr ∧
      (∀ a, S.chrDt.eDt a = chrDt.eDt a) ∧
      (S.what₂.O.pieces.rcf = what₂.O.pieces.rcf ∧ S.what₂.O.pieces.MDel = what₂.O.pieces.MDel) ∧
      S.inK = inK ∧ HEq S.geo geo ∧ P _ _ _ (he ▸ S.tw) := by
  cases h
  subst he
  first
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, frameN := frameN, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩
set_option maxHeartbeats 2000000 in
theorem WPt.exists_pinned_spectral_data_compatible : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) → Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → ∃ S : _root_.Formalism.L2.TiedDataSAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q S := by
  intro hA hW hL p K q hlev hze
  obtain ⟨extra, g, hg, hherm, hforms⟩ := WPt.extraTied_col p.s K q
  obtain ⟨I, n, hE, hgood, hchr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_core_parameters_agree hL p K q
  obtain ⟨he, tw, hstd, emt⟩ := GlobalTheory.Mem.Top.Bl.WPt.colsTwTied p.s K q
  obtain ⟨dt, hdt⟩ := TC.dtTied_true q.w.I q.w.ok q.w.pins q.w.l q.Z
  have hO : ∃ O : Formalism.L2.Rows.OTied (q.w.D q.Z) q.core_data_of_point.a.host (TC.cf q.w.I q.w.l q.Z),
      O.pieces.rcf = GlobalTheory.Mem.HD.qb q.core_data_of_point.a.host.fr.ι q.w.δ.ray ∧ O.pieces.MDel = GlobalTheory.Mem.HD.qb q.core_data_of_point.a.host.fr.ι q.w.δ.M' := by
    generalize q.core_data_of_point.a.host = H
    rw [← ColW.cf_eq]
    exact GlobalTheory.Mem.CyclotomicFieldContainment.oTied_of_ksExact hA hW (q.w.st q.Z) q.f q.w.δ q.w.exact H
  obtain ⟨O, hO1, hO2⟩ := hO
  have hval : Formalism.L2.Host.ValLL0 (q.w.D q.Z) (TC.cf q.w.I q.w.l q.Z) := by
    rw [← ColW.cf_eq]
    exact q.w.val _ _ _ _ _ _
  have hfr : ∀ x, n.gal.fr.jE x = q.core_data_of_point.a.host.fr.j x := by
    rw [h1]
    exact q.core_data_of_point.a.frameN
  obtain ⟨S, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    _root_.GlobalTheory.Mem.Top.Bl.tiedDataS_assemble_alt q.O.ex q.core_data_of_point.a.host hlev q.x.col.C q.x.col.full extra q.x.th.provA q.x.th.all I n hfr
      (TC.cf q.w.I q.w.l q.Z) q.x.n.tp hchr q.x.th.chr hval dt q.core_data_of_point.a.chrN q.core_data_of_point.a.chrGal q.x.n.chrPsi q.x.th.same
      ⟨O, q.O.ex.kap_def, hze⟩ q.x.div.inK q.x.div.geo (q.w.tw q.Z) he tw emt g hherm hforms
      (fun _ _ _ t => TC.StdTw q.w.I q.w.l q.Z q.w.l0 t) hstd
  have key : ∀ Q : (Σ I, _root_.Formalism.L2.NTiedAllAlt (q.w.D q.Z) q.O.ex.nch I) → Prop, Q ⟨I, n⟩ → Q ⟨S.twIn, S.n⟩ :=
    fun Q hQ => s6 ▸ hQ
  refine ⟨S, s1, s2, s3, s4 ▸ hg, s5, key (fun z => z.1.E = _) hE, key (fun z => DQ.GoodAllAt _ _ z.1) hgood,
    key (fun z => (⟨z.2.cf, z.2.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = _) hchr,
    key (fun z => z.2.gal = _) h1, key (fun z => z.2.n = _) h2, key (fun z => z.2.exp = _) h3,
    key (fun z => z.2.chiD = _) h4, key (fun z => z.2.twF = _) h5, key (fun z => HEq z.2.types _) h6,
    key (fun z => HEq z.2.cover _) h7, key (fun z => z.2.plB = _) h8, s7, fun a => (s8 a).trans (hdt a), ?_, s10, s11, he, s12⟩
  rw [s9.1, s9.2, s1]
  exact ⟨hO1, hO2⟩
end GlobalTheory.Mem.Top.Bl
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupAllUsedAtPart
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.StageZeroRow
theorem tupAllUsed_at_part_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : Formalism.L2.DIV.TupAllUsed b.P := by
  intro t
  rcases b.pt.charW.tup.mu_used t with h | ⟨w, hw⟩
  · left
    subst h
    exact b.P.tied.div.tup.mu0
  · right
    refine ⟨D.plEq.symm w, ?_⟩
    have e1 := b.pt.tupAt (D.plEq.symm w)
    rw [Equiv.apply_symm_apply] at e1
    have e2 := b.pt.tupTie (D.what₂.muAt (D.plEq.symm w)) (Or.inr ⟨_, rfl⟩)
    rw [e1, hw] at e2
    exact e2
theorem p_div_at_piece_of_div3g {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) (h : GlobalTheory.Cp.DivRows3G b.P) : _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b :=
  Formalism.L2.DIV.DivRows3G.toRows (_root_.GlobalTheory.Fc.StageZeroRow.tupAllUsed_at_part_alt b)
    ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩
theorem row_rRows_stage0_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.DiscreteSeriesClassification → _root_.GlobalTheory.BigOn.SurjectiveOntoX → _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q Lk → _root_.GlobalTheory.Fc.R1.SlotDivisorCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowGoodnessCondition Q Lk → _root_.GlobalTheory.Fc.S0.GeometricWeakCompatibility' Q Lk → _root_.GlobalTheory.Fc.S0.CovolumeBoundThirdPlaceSeries Q Lk → _root_.GlobalTheory.Fc.S0.FunctionalCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowKappaCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowDefectCondition Q Lk → _root_.GlobalTheory.Fc.R1.SlotDefiniteRowsCondition _root_.GlobalTheory.Fc.DefiniteSideCondition Q Lk := by
  intro hDS hHC hCR hCW hDC hOnto hLam Q Lk hPA hDiv hGood hGeo hL3 hFun hMi hKap hDf
  refine _root_.GlobalTheory.Fc.row_rRows_of_parts_alt _root_.GlobalTheory.Fc.DefiniteSideCondition Q Lk ?_ hMi hKap hDf
  refine (((((hPA.and hDiv).and hGood).and hGeo).and hL3).and hFun).imp fun 𝒜 σ hsel H => ?_
  obtain ⟨⟨⟨⟨⟨hpa, hdv⟩, hgd⟩, hall⟩, hl3⟩, hfun⟩ := H
  choose τ hτ using fun {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) x hx i => hall Fm hc x hx i
  let τ' : _root_.GlobalTheory.Fc.CompatibleSelection σ := fun Fm hc x hx i => τ Fm hc x hx i
  have hduty : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm := fun _ Fm hc =>
    let ⟨_, _, h7, _⟩ := hsel Fm hc
    (DQ.familyClass_sevenDuties_and_stableLattices _ Fm h7).1
  have hiota : AtAll _root_.GlobalTheory.Fc.Ind.IotaPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => (hτ Fm hc x hx i).1
  have hppa : AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => hpa Fm hc x hx i
  have hpdiv : AtAll _root_.GlobalTheory.Fc.Ind.DivisorPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => _root_.GlobalTheory.Fc.StageZeroRow.p_div_at_piece_of_div3g _ (hdv Fm hc x hx i)
  have hcs : AtAll (fun D O c (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.CompatibilityConditions) 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') :=
    fun Fm hc x hx i => ⟨(hτ Fm hc x hx i).2.1, (hτ Fm hc x hx i).2.2.1⟩
  have hrows : Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := _root_.GlobalTheory.T.eventually_pDiv_ties_of_class_sum_pin hDS hHC hCR hCW 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hppa hpdiv hgd hcs
  have hmore : Ind.EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') :=
    evW_of_atAll' fun Fm hc x hx i => (hτ Fm hc x hx i).2.2.2
  refine ⟨τ', ?_, hl3, _root_.GlobalTheory.T.eventually_norm_bound_of_more_points hOnto 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hduty hrows hmore, _root_.GlobalTheory.T.eventually_L6_bound_of_lamLow hLam 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hduty hrows, hfun⟩
  exact _root_.GlobalTheory.T.eventually_small_of_seeEx_primitive 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') (fun Fm hc x hx i =>
      _root_.GlobalTheory.T.indefinite_scale_theta_nonvanishing_alt hDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_root_.GlobalTheory.Fc.summandSelection σ τ' Fm hc x hx i).B.Q (_root_.GlobalTheory.Fc.summandSelection σ τ' Fm hc x hx i).pins
        (hiota Fm hc x hx i)) hppa
end GlobalTheory.Fc.StageZeroRow
end
end

