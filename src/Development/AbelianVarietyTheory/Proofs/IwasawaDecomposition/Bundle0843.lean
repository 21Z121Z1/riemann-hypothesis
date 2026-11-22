import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0842
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0485
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0769
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0523
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0635
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberOfConstructionStepsSecondPass
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.MemberEx2

theorem step_start (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ B _ T => T = TwDat.untw B T.pl) (fun K B f T => ∃ w : ColW B f T, Start K B f T w) :=
  (Step.and (Step.of_all fun _ _ _ _ _ _ _ h => h)
      ((Step.of_all fun _ _ _ _ _ _ _ _ => trivial).trans (PinW.step_pinned h2b))).trans
    (Step.of_all fun _ _ _ _ _ _ _ H =>
      let ⟨w, hw⟩ := H.2
      ⟨w, hw, supp_of_untw w H.1, coh_of_untw H.1⟩)

theorem stepW_builtE {𝒮 : Slots} {p : WP} (hp : ∀ K B f T w, p K B f T w → Pinned K B f T w)
    (h4 : StepW (pinAnd (Has3 𝒮)) (Has4 𝒮)) (hc : StepW (pinAnd (Has4 𝒮)) (HasC (BuiltE 𝒮)))
    (h3 : StepW p (Has3 𝒮)) : StepW p (HasC (BuiltE 𝒮)) :=
  have q : StepW p Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => hp _ _ _ _ _ h
  (q.and ((q.and h3).trans h4)).trans hc

end GlobalTheory.Mem.Top.Bl.MemberEx2

namespace GlobalTheory.Mem.Top.Bl

theorem memberE_of_steps2 : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM →
    ∀ 𝒮 𝒮' : Slots, StepW Start (Has3 𝒮) → StepW (pinAnd (Has3 𝒮)) (Has4 𝒮) → AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
      ExportF KPx (IsBuiltE 𝒮) →
      Pass KPx (IsBuiltE 𝒮) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w) →
      StepW (pinAnd (Has3 𝒮')) (Has4 𝒮') → AmbEx 𝒮' → DivEx 𝒮' → ThEx 𝒮' →
      (∀ K B f T w Z c, BuiltE 𝒮' K B f T w Z c → GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) → MemberE 𝒮 := by
  intro hR hP hC h2b 𝒮 𝒮' h3 h4 hA hD hT hE hPass h4' hA' hD' hT' hL
  have hB : BaseCond KPx := KPxCond.baseCond_KPx hR hP hC h2b
  have h1 : FirstG KPx (IsBuiltE 𝒮) :=
    step_hasCore (MemberEx2.step_start h2b)
      (MemberEx2.stepW_builtE (fun _ _ _ _ _ h => h.1) h4 (GlobalTheory.T.exists_constructedCore_of_all_construction_stages h2b 𝒮 hA hD hT) h3)
  have hW : StepW (fun K B f T w => Start K B f T w ∧ Has3 𝒮' K B f T w)
      (HasC fun K B f T w Z c => GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) :=
    (MemberEx2.stepW_builtE (fun _ _ _ _ _ h => h.1.1) h4' (GlobalTheory.T.exists_constructedCore_of_all_construction_stages h2b 𝒮' hA' hD' hT')
      (StepW.of_all fun _ _ _ _ _ _ _ h => h.2)).trans
      (StepW.of_all fun _ _ _ _ _ _ _ H => let ⟨Z, c, hc⟩ := H; ⟨Z, c, hL _ _ _ _ _ _ _ hc⟩)
  have hS := step_hasCore (admitted := fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w)
    (Step.of_all fun _ _ _ _ _ _ _ h => h) hW
  have h2 : SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) :=
    GlobalTheory.Mem.Top.GroupRetwisting.pass_step KPx _ _ _ hB hPass (hS.trans (Step.of_all fun _ _ _ _ _ _ _ H =>
      let ⟨C, W, V, S, N, G, c, hc⟩ := H
      ⟨C, W, V, S, N, G, c, positionOf_ind (R := fun K X f T c => IsBuiltE 𝒮 K X f T c ∧ DQ.TwAllAt X.toD7 c.O.nch c.O.xd ∧
        IsGoodE 𝒮 K X f T c) (fun _ _ _ _ _ _ _ h => ⟨positionOf_intro h.1.1, h.2, positionOf_intro h.1⟩) hc⟩))
  exact ⟨hB, h1, hE, h2⟩

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieGramIsGoodMumford
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.LieBaseGood

theorem lieGram_isGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsGood Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ch, a, ha, g, rk, τ₀, B, hP, hHolo, hys, hy0, hpoly, hbd, A, hA, Q, hQ, hcard, hind, hform, horth⟩ :=
    GlobalTheory.T.exists_hodgeMetric_periodChart_at_boundaryPoint E H Dw l Xo c O β Y T F e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ρ, hρ, hρ2, c₀, N₀, hb⟩ := GlobalTheory.T.inv_hodgeMetricGram_mumfordGoodGrowth_boundaryChart X.dim a ha g rk τ₀ B hP
  let W : Set (ReciprocityTheory.L2DbarEstimates.V X.dim) :=
    (ch.target ∩ ch.symm ⁻¹' GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j)) ∩
      WithLp.ofLp ⁻¹' GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ
  have hWo : IsOpen W := (ch.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
    ((GlobalTheory.HodgeChartRow.isOpen_punctured ha ρ).preimage (PiLp.continuous_ofLp 2 _))
  let G₀ : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin g) (Fin g) ℂ :=
    fun u => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹
  let Q' : ∀ τ : E →+* ℂ, ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ := fun τ u => Q τ u.ofLp
  have hdo : Differentiable ℂ (WithLp.ofLp : ReciprocityTheory.L2DbarEstimates.V X.dim → Fin X.dim → ℂ) :=
    (EuclideanSpace.equiv (Fin X.dim) ℂ).differentiable
  have hQ' : ∀ τ i k, DifferentiableOn ℂ (fun u => Q' τ u i k) (Metric.ball 0 1) := by
    intro τ i k
    refine (hQ τ i k).comp hdo.differentiableOn fun u hu k' => ?_
    exact (PiLp.norm_apply_le u k').trans_lt (by simpa using hu)
  have hind' : LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q' p.1 0 p.2) := by
    simpa [Q'] using hind
  have hG₀ : ∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧
      GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c₀ N₀ G₀ v := by
    intro v hv
    obtain ⟨hpd, hcd, hgb⟩ := hb v hv.2
    refine ⟨?_, hcd, hgb⟩
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hpd.det_pos.ne')).ne_zero
  have horth' : ∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q' τ v * G₀ v * (Q' τ' v)ᴴ = 0 := by
    intro v hv τ τ' hne
    have := horth (ch.symm v) (ch.map_target hv.1.1) hv.1.2 τ τ' hne
    rwa [ch.right_inv hv.1.1] at this
  obtain ⟨r', hr', c', N', hfr⟩ := GlobalTheory.T.mumfordGoodGrowthBound_frameChange_orthogonalSummands X.dim g (Finset.univ.map (Fin.castLEEmb ha)) W G₀ c₀ N₀ (E →+* ℂ)
    Dw.mult Q' 1 hWo one_pos hQ' hcard hind' hG₀ horth'
  refine ⟨ch, Finset.univ.map (Fin.castLEEmb ha), hHolo, hys, ?_, ?_, A, hA, c', N', ?_⟩
  · intro b _
    rw [hy0]
    rfl
  · intro z hz
    rw [hbd z hz]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Fin.castLE ha i, by simp, hi⟩
    · rintro ⟨b, hb', hb0⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hb'
      exact ⟨i, hb0⟩
  · have h1 : ∀ᶠ z in nhds y, z ∈ ch.source ∧ ch z ∈ Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V X.dim) (min r' ρ) :=
      Filter.Eventually.and (ch.open_source.mem_nhds hys) ((ch.continuousAt hys).preimage_mem_nhds
        (by rw [hy0]; exact Metric.ball_mem_nhds _ (lt_min hr' hρ)))
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hzO τ
    obtain ⟨hzs, hzb⟩ := hz
    rw [mem_ball_zero_iff] at hzb
    have hzW : ch z ∈ W := by
      refine ⟨⟨ch.map_source hzs, Set.mem_preimage.2 (by rw [ch.left_inv hzs]; exact hzO)⟩, ?_, ?_⟩
      · exact fun k => (PiLp.norm_apply_le _ k).trans_lt (hzb.trans_le (min_le_right _ _))
      · intro i hi
        exact (hbd z hzs).2 ⟨i, hi⟩ hzO
    have hGB := hfr (ch z) hzW (hzb.trans_le (min_le_left _ _)) τ
    refine GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram X.dim _ _ c' N' _ _ (ch z) ?_ hGB
    filter_upwards [hWo.mem_nhds hzW] with u hu
    have := hform (ch.symm u) (ch.map_target hu.1.1) hu.1.2 τ
    rw [ch.right_inv hu.1.1] at this
    exact this.symm

end GlobalTheory.LieBaseGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsOfMultiplicityEqual
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.LiftsAt

open GlobalTheory.Mem.Top.GroupRetwisting

theorem serClause_of_typesTrue (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) {P W} (h : TypesTrue D.ntypes P W) : SerClause D := by
  intro k
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hζ : Formalism.L2.NT.IsGenSys (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen := by
    intro d hd
    refine ⟨(GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order d hd, fun d' hdd hd' => ?_⟩
    obtain ⟨e, rfl⟩ := hdd
    exact (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_norm d e hd (Nat.pos_of_mul_pos_left hd')
  obtain ⟨O, -, -, hO⟩ := GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel (ZMod (D.host.g k)) _
    (GlobalTheory.T.cuspParam_of_greenParametrisation hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) _ hζ)
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact ⟨_, O, fun f => (h.ser k f).trans (GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent hG _ _ _ _ _ (h.teich k) O hO D.R.r f hr)⟩

def Closes (X : Stages) : Prop :=
  ∀ (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (Tw : TwDat X.B) (Wt : Set X.B.places.Pl) (z : Dat X I hX Tw Wt),
    TiesB z.R z.F → TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O → GlobalTheory.CuspMult.MultEq z.R.toRealDat → z.R.toRealDat.LIntegral →
      HoldsL z.R z.F

theorem ev_closes (P : Hypotheses3) (hRSW : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm) (hHL : GlobalTheory.Published.HeckeLPartialContinuation) :
    Ev fun K => ∀ (X : Stages) (L : SizeData₂ X.toD7), L.sc = K.s → SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → Closes X := by
  refine ⟨1, one_pos, fun eps _ h0 _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ?_⟩⟩⟩⟩
  obtain ⟨x₀, h⟩ := GlobalTheory.LiftsOnly.holdsL_of_ties P hRSW hHL eps h0
  exact ⟨x₀, fun K _ _ _ hs hx X L e hS hP px I hX Tw Wt z =>
    h z.core z.R z.F z.geo.κ z.geo.v₀ z.geo.O L (by rw [e]; exact hs) (by rw [e]; exact hx) hS hP⟩

set_option maxHeartbeats 2000000 in

theorem ties_at (hG : GlobalTheory.Published.GreenCuspidal) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (hN : GrpTrue Z.N f)
    (ok : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.Ok3 1) (hEx : z.R.toRealDat.ExAt)
    (host : Formalism.IndefR.Links.HostHyp (w.st Z).toD7) (par : ∃ L : SizeData₂ (w.st Z).toD7, Nonempty (ParameterChoice' (w.st Z).toD7 L))
    (hn : 8 * (w.st Z).toD7.R.f * (w.st Z).toD7.R.r + 4 ≤ (w.st Z).toD7.R.nV)
    (hI : IoExt z.R.toRealDat) (hU : z.R.toRealDat.LUnif) (hW : CoverAt.WeberLev B f T) :
    TiesB z.R z.F ∧ TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O := by
  have ty : TypesTrue (w.st Z).toD7.ntypes z.R.C.P z.R.C.W := by
    have e : z.R.toLevCh.C = Fr.at (w.st Z) f := z.lev.C.trans (congrArg (Fr.at (w.st Z)) w.C_eq)
    have e' : z.R.C = Fr.at (w.st Z) f := e
    rw [e']
    exact hN
  have hch := z.pins.char
  refine ⟨⟨ok, hch, hEx, host, par, B.ccK_top, z.pins.keep.guard,
    GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hch.base.lev ty, serClause_of_typesTrue hG _ ty,
    GlobalTheory.Hk3.inertJunk_colIn3 _ _ _ hX _ _ _ _ _ _, z.pins.trSem, z.pins.keep.std, z.pins.phs, hn⟩,
    TiesG.of_dat z hU hI (fun i => ?_) (CoverAt.coverField_of_weberLev hW w Z hX Wt z)⟩
  exact GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation _ _ _ _ _ _ z.core z.R z.F z.geo.κ z.geo.v₀ z.geo.O (fun _ => 1) hn hch hEx ⟨z.geo.fw⟩ hI i
    (z.geo.pins i) (z.geo.phase i hU)

set_option maxHeartbeats 4000000 in

theorem holdsLU : Hypotheses3 → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → GlobalTheory.Published.HeckeLPartialContinuation → (StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → GlobalTheory.CuspMult.MultEq z.R.toRealDat) → LowerUnitaryCaseCondition := by
  intro P hRSW hHL hM
  have hE : Step KPx (fun _ _ _ _ => True) fun K B f T => (∀ X : Stages, X.B = B →
      (∀ L : SizeData₂ X.toD7, L.sc = K.s → SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → Closes X) ∧
      (X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → (∀ w j, X.toD7.what₂.Aj j w = 0) →
        ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ SizesAt L ∧ Nonempty (ParameterChoice' X.toD7 L) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) ∧
      Formalism.IndefR.Links.HostHyp X.toD7 ∧
      ∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧
        (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) :=
    Step.of_evG ((((evG_of_ev (ev_closes P hRSW hHL)).inter (evG_of_ev LedRec.ev_exists_sizeData)).inter
      (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).imp fun K _ _ _ _ H B f T hO _ _ _ X e => by
        subst e
        exact ⟨H.1.1 X, H.1.2 X hO, (H.2 X hO).1, (H.2 X hO).2.2.2.2.2.2.1⟩)
  refine ((((hE.and (Step.of_evLgG (evLgG_of_evLg GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField))).and
    (Step.of_evLgG (q := fun _ => CoverAt.WeberLev) (evG_all CoverAt.lg_weberLev))).and hM).and
    (Step.and (lUnif_atDat P.q3 P.q2 P.q1) (atDat_lIntegral P.q3 P.q2 P.q1))).trans
    (Step.of_all fun K B f T _ _ _ H w hw Z hX Wt z g1 g2 hEx g4 => ?_)
  obtain ⟨⟨⟨⟨h1, hOk⟩, hW⟩, hM⟩, hU, hI⟩ := H
  obtain ⟨b, hb, heta, hA⟩ := LedRec.exists_bare P.q12 (C := w.C) Z f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨hcl, hled, hhost, hV⟩ := h1 (w.st b) rfl
  obtain ⟨L, hL, hS, hP, hn⟩ := hled heta hA
  have s : SameGrp (C := w.C) Z b := LedRec.sameGrp g1 hb
  have hEx' := DatCopy.copy_exAt b s hEx
  have hU' := DatCopy.copy_lUnif b s (hU w hw Z hX Wt z g1 g2 hEx g4)
  have hT := ties_at P.q12 w b hX Wt (DatCopy.copy b s z) hb
    ((hOk w.px w.I hX w.ok w.C_eq w.xi_range).2 _ _ _ (DatCopy.copy b s z).good.irr) hEx' hhost ⟨L, hP⟩ hn
    (GlobalTheory.T.ioExt_of_weakCharacterisation_of_orthonormal_frames _ _ _ _ _ _ _ (DatCopy.copy b s z).R (DatCopy.copy b s z).F (DatCopy.copy b s z).pins.char hEx' hV) hU' hW
  exact LiftCopy.holdsL_of_copy b s (hcl L hL hS hP w.px w.I hX T Wt (DatCopy.copy b s z) hT.1 hT.2
    (DatCopy.copy_multEq b s (hM w hw Z hX Wt z g1 g2 hEx g4)) (DatCopy.copy_lIntegral b s (hI w hw Z hX Wt z g1 g2 hEx g4)))

end GlobalTheory.Mem.R3.LiftsAt

end
end

