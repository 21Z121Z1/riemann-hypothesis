import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Formalism.LocalToGlobal.IndefiniteReal.LinksComap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0531
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictToBase
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BaseRestrict

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev baseA (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) : FamIn D.what₂.LL G Pl0 Unit D.R.m := A.comap (fun _ : Unit => A.μ0) ()

def baseF (F : Face D A) : Face D (baseA A) where
  P0 := F.P0
  ψ0 := F.ψ0
  P1 := F.P1
  ψ1 := F.ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

section Any

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def baseR (R : RealDat D A Ks) : RealDat D (baseA A) Ks :=
  R.comap (fun _ : Unit => A.μ0) () (fun _ => ()) R.twPl R.FW R.kap (fun i _ => R.lam i A.μ0) R.err0

variable {R : RealDat D A Ks}

set_option maxHeartbeats 2000000 in
theorem core_base {F : Face D A} (h : GlobalTheory.Hk3.Core R F) : GlobalTheory.Hk3.Core (baseR R) (baseF F) := by
  obtain ⟨hlev, hgrp, hfam, hmod, hch, hth⟩ := h
  refine ⟨LevCh.comap_is hlev (f := fun _ : Unit => A.μ0) (fun _ _ _ => rfl) rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ q => hgrp.red_R A.μ0 q, fun i _ q => hgrp.red_L i A.μ0 q, hgrp.levels, hgrp.record, hgrp.chiW⟩
  · obtain ⟨g, c0R, c0L, ht⟩ := hfam.tie
    exact ⟨⟨g, c0R, c0L, ht.comap (fun _ : Unit => A.μ0) ()⟩, hfam.Sb, fun _ PP => hfam.roots A.μ0 PP, hfam.pl_onto,
      fun _ P => hfam.degR A.μ0 P, fun i _ P => hfam.degL i A.μ0 P, fun i _ P hP => hfam.muVal i A.μ0 P hP,
      fun P hP => hfam.etaVal P hP⟩
  · exact ⟨hmod.inf, hmod.vpos, hmod.cX, hmod.cV, hmod.prX, fun _ => hmod.HX A.μ0, fun i _ => hmod.HV i A.μ0, hmod.HE, hmod.HW,
      hmod.gE, hmod.gW, fun _ x => hmod.jX A.μ0 x, fun i _ x => hmod.jV i A.μ0 x, fun _ j h2 => hmod.νY A.μ0 j h2,
      fun _ => hmod.νY' A.μ0, hmod.ν0, fun _ => hmod.νX A.μ0, fun i _ => hmod.νV i A.μ0, hmod.νW, hmod.BV, hmod.order⟩
  · exact ⟨fun _ k hk => hch.ωY A.μ0 k hk, fun _ => hch.ωX A.μ0, fun _ k hk => hch.vY A.μ0 k hk, fun _ => hch.vX A.μ0,
      fun _ k hk P => hch.ptY A.μ0 k hk P, fun _ P => hch.ptX A.μ0 P, fun _ k hk => hch.ItY A.μ0 k hk, fun _ => hch.ItX A.μ0,
      fun _ => hch.ioY A.μ0, fun _ => hch.ioX A.μ0, fun _ => hch.Th A.μ0⟩
  · exact ⟨fun i _ => hth.ωP i A.μ0, fun i _ => hth.vP i A.μ0, fun i _ P => hth.pt_theta i A.μ0 P, fun i _ => hth.ioP i A.μ0,
      fun i _ => hth.thF_mem i A.μ0, fun i _ => hth.thF i A.μ0, fun i _ => hth.thG i A.μ0⟩

theorem ioExt_base (h : IoExt R) : IoExt (baseR R) := h

theorem qGuard_base (h : QGuard R) : QGuard (baseR R) := ⟨fun _ => h.1 A.μ0, fun _ => h.2 A.μ0⟩

theorem baseOf_base {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} (h : BaseOf R j B) : BaseOf (baseR R) j B :=
  ⟨h.ψ, h.θ, h.sT, h.BS, h.BT, h.ΛS, h.ΛT, h.βS, h.βT, h.vac, h.Pg, h.mu0, h.eta, h.lam, h.delta, h.p, h.q, h.c⟩

theorem twLev_base {χ : Formalism.L2.Host.HChar D.host.E} {xi : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)}
    {xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (h : TwConj.TwLev R χ xi Q xiR) : TwConj.TwLev (baseR R) χ xi Q xiR :=
  ⟨h.xi, h.xi_fin, h.xi_triv, h.xi_tame, h.Q_pl, h.Q_off,
    fun p hp => (h.Q_de p hp).imp fun _ h' => ⟨fun _ => h'.1 A.μ0, h'.2⟩,
    h.Q_ram, h.xiR, h.roots, h.muVal, h.half, h.guard⟩

end Any

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

set_option maxHeartbeats 2000000 in

def fwBase (t : FWTie T R κ v₀) : FWTie T (baseR R) κ v₀ where
  alg_eq := t.alg_eq
  e := t.e
  ks := t.ks
  kap := t.kap
  pt := t.pt
  nrm_eq := t.nrm_eq
  laws := t.laws
  chiR := t.chiR
  hv₀ := t.hv₀
  x0 := t.x0
  ev0 := t.ev0
  ev := t.ev

set_option maxHeartbeats 2000000 in

def omBase {i : Fin D.R.m} (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) :
    OMDat T.toCore (baseR R) i Unit (fun _ => (baseA A).μ0) where
  c' := O.c'
  hle := O.hle
  jL := O.jL
  hV := O.hV
  c0' := O.c0'
  lev := O.lev
  dδ := O.dδ
  Cl' := O.Cl'
  fCl := O.fCl
  bad := O.bad
  Lh := O.Lh
  La := O.La
  Nc := O.Nc
  gam := O.gam
  vol := O.vol
  ep := O.ep
  B := O.B
  epF := O.epF
  io := O.io
  hw := O.hw
  φ := O.φ
  w := O.w
  U₂ := O.U₂
  dict₂ := O.dict₂
  xi := O.xi
  thAd := O.thAd
  Plc := O.Plc

variable {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}

set_option maxHeartbeats 4000000 in
theorem omPins_base {i : Fin D.R.m} (h : OMPins T R κ v₀ O i) : OMPins T (baseR R) κ v₀ (fun i => omBase (O i)) i := by
  have hP := h.2
  have h1 := hP.lift
  have h2 := hP.tuple
  refine ⟨h.1, ⟨h1.field, h1.std, h1.v0, ?_, h1.lev⟩,
    fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    hP.act, hP.bad, hP.reps, hP.ep, hP.io, hP.w, hP.cov, hP.cxi, hP.model₂⟩
  obtain ⟨g, c, c', h3, h4⟩ := h1.c0
  exact ⟨g, c, c', h3.comap (fun _ : Unit => A.μ0) (), h4⟩

set_option maxHeartbeats 4000000 in
theorem oneMapOf_base {i : Fin D.R.m} (cc ph) :
    (omBase (O i)).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph ↔ (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem phaseTie_base {ph : Fin D.R.m → ℂ} {i : Fin D.R.m} (h : PhaseTie T R κ v₀ O ph i) :
    PhaseTie T (baseR R) κ v₀ (fun i => omBase (O i)) ph i :=
  fun ⟨cc, p, h'⟩ => (oneMapOf_base _ _).2 (h ⟨cc, p, (oneMapOf_base _ _).1 h'⟩)

set_option maxHeartbeats 4000000 in
theorem ext_base (j : Fin D.R.m) : TwConj.Ext T R κ v₀ O j (baseR R) v₀ (fun i => omBase (O i)) :=
  ⟨fun _ h => ⟨h.core, h.host, h.curve, h.split, h.chi⟩, fun _ _ _ _ h => h, fun c u hc hu => ⟨c, u, hc, hu, fun _ => rfl⟩⟩

set_option maxHeartbeats 2000000 in

theorem restrict_to_base : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∃ (A0 : FamIn D.what₂.LL G Pl0 Unit D.R.m) (R0 : RealDat D A0 T.Q.c.F) (F0 : Face D A0)
      (v0 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R0.MW i σ).Vec) (O0 : ∀ i, OMDat T.toCore R0 i Unit (fun _ => A0.μ0)),
      GlobalTheory.BigOn.Exp.TwConj.Laws T R0 F0 κ v0 O0 ph j B ∧ GlobalTheory.BigOn.Exp.TwConj.Ext T R κ v₀ O j R0 v0 O0 ∧ (∀ t, R0.xiH t = 1) ∧
      ∀ (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E)) (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
        GlobalTheory.BigOn.Exp.TwConj.TwLev R χ xi Q xiR → GlobalTheory.BigOn.Exp.TwConj.TwLev R0 χ xi Q xiR := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B h
  obtain ⟨h1, -, ⟨h3⟩, h4, h5, h6, h7, h8⟩ := h
  exact ⟨baseA A, baseR R, baseF F, v₀, fun i => omBase (O i),
    ⟨core_base h1, inferInstance, ⟨fwBase h3⟩, ioExt_base h4, qGuard_base h5, omPins_base h6, phaseTie_base h7, baseOf_base h8⟩,
    ext_base j, fun _ => h1.lev.xi_base, fun _ _ _ _ h => twLev_base h⟩

end GlobalTheory.BaseRestrict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceFiniteSetStatement
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_place_finite_set : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), PtAt.Rows p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite := by
  first | exact @GlobalTheory.FrameAutCof.cofinite_labels_at | exact GlobalTheory.FrameAutCof.cofinite_labels_at | (intros; apply GlobalTheory.FrameAutCof.cofinite_labels_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBoundFittedIdentity
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField

namespace GlobalTheory.BigTop.Fun.ThbTie

theorem sqRank_half {D : D7} (ij : Sq D) : sqRank D ij / 2 = GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
  unfold sqRank GlobalTheory.FunObj.SqNum.halfRank GlobalTheory.ChiGrid.rankV
  congr 1
  ring

theorem htLe_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] {g : Formalism.PairingDivisionLocalBalance.Pl K → ℤ} {z : K} {B : ℝ}
    (h : Formalism.PairingDivisionLocalBalance.HtLe g z B) : 0 ≤ B :=
  (finsum_nonneg fun w => mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (abs_nonneg _)).trans h.2

theorem htLe_one_zero {K : Type} [Field K] [NumberField K] [StarRing K] {B : ℝ} (hB : 0 ≤ B) :
    Formalism.PairingDivisionLocalBalance.HtLe (fun _ => (0 : ℤ)) (1 : K) B := by
  have e : (fun w : Formalism.PairingDivisionLocalBalance.Pl K => Formalism.DivisionValues.lw w * |((Formalism.DivisionValues.vw w (1 : K) + 0 : ℤ) : ℝ)|) = fun _ => 0 := by
    funext w
    simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  refine ⟨?_, ?_⟩
  · rw [e]
    simp
  · rw [e, finsum_zero]
    exact hB

end GlobalTheory.BigTop.Fun.ThbTie

open GlobalTheory.BigTop.Fun.ThbTie in

theorem GlobalTheory.BigTop.Fun.thb_tie (hS : SetAt)
    (hd : Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hT : ThbSt) : Thb @Comparison₂ := by
  have hQ := GlobalTheory.T.fitted_ties_bound_eventual _ hS hd hT
  refine Lf.mono hQ ?_
  intro D L hT' Gi Gl Kc Y cX ex Csz p CF d C CH _ htie
  refine ⟨htie, fun hq => ?_⟩
  obtain ⟨a, ha⟩ := htie.2
  have hsq := ha.sq
  have hin : ∀ (ij : Sq D) (s : ℤ), 1 ≤ s → s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 →
      Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) 1 (bTH D C p.Z.x p.Z.b) ∧
        ∀ c, d.zTd ij c s ≠ 0 ∧ Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) (d.zTd ij c s) (bTH D C p.Z.x p.Z.b) := by
    intro ij s h1 h2
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ s)
    have h1' : 1 ≤ n := by omega
    have h2' : n ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by omega
    exact hq ij.1 ij.2 n h1' h2' _ _ (hsq.inside ij n h1' h2').1
  have hB0 : ∀ ij : Sq D, 0 ≤ bTH D C p.Z.x p.Z.b := by
    intro ij
    have hr : 1 ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
      have := D.R.m_add_three_le_k
      unfold GlobalTheory.FunObj.SqNum.halfRank GlobalTheory.ChiGrid.rankV
      have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
      omega
    exact htLe_nonneg (hin ij 1 le_rfl (by exact_mod_cast hr)).1
  have hB : d.O.bTH C p.Z.x p.Z.b = bTH D C p.Z.x p.Z.b := rfl
  have hzT : ∀ ij s, d.O.zT ij s = 1 := hsq.base
  refine ⟨fun ij s h1 h2 => ?_, fun ij s => ?_, fun ij c s => ?_⟩
  · have h2' : s ≤ (GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 : ℤ) :=
      h2.trans_eq (congrArg (fun n : ℕ => (n : ℤ)) (sqRank_half (D := D) ij))
    exact ⟨by rw [hzT]; exact one_ne_zero, fun c => ((hin ij s h1 h2').2 c).1⟩
  · rw [hzT, hB]
    by_cases hs : 1 ≤ s ∧ s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2
    · exact (hin ij s hs.1 hs.2).1
    · have := (hsq.outside ij s hs).2.1
      change Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) 1 _
      rw [this]
      exact htLe_one_zero (hB0 ij)
  · rw [hB]
    by_cases hs : 1 ≤ s ∧ s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2
    · exact ((hin ij s hs.1 hs.2).2 c).2
    · obtain ⟨e1, e2, -⟩ := hsq.outside ij s hs
      change Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) (d.zTd ij c s) _
      rw [e1 c, e2]
      exact htLe_one_zero (hB0 ij)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumInvariantRationalUnitary
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.ThetaRatPair

theorem det_ne_zero_of_hasSig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul Aᵀ M e.symm id id Function.bijective_id]
    simp [Matrix.transpose_submatrix, Matrix.submatrix_map]
  intro h0
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self] at this
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at this
  exact pow_ne_zero s (by norm_num : (-1 : ℂ) ≠ 0) this.symm

theorem det_ne_zero_of_map {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem thetaSum_om_rat : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine det_ne_zero_of_map W.J (B.emb w).1 fun h0 => det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ

end GlobalTheory.ThetaRatPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtPlaceProduct
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.PureAway

theorem pure_away : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (f₂ : SInf F (Fin a' × Fin (a + a'))) (φ₂ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ᶠ w in Filter.cofinite, φ₂ w = G.M'.vac w) ∧ φ₂ v = φ v ∧
      om' (g, h) (pure f φ) = pure f₂ φ₂ := by
  classical
  intro P F E _ _ _ _ _ σ B a a' G X om om' hT v g h hg hh f φ hφ hφv
  obtain ⟨S, g₁, g₂, g₃, h₁, h₂, h₃, hvS, rfl, rfl, a1, a2, b1, b2, c1, c2, c3, c4, c5, c6⟩ :=
    GlobalTheory.T.theta_local_factor_finite_place F E σ B a a' G X om om' hT v g h hg hh φ hφv
  obtain ⟨c, hc⟩ := GlobalTheory.T.theta_trivial_at_infinity_set P F E σ B a a' G X om om' hT (insert v S) g₃ h₃ c1 c2
    (fun w hw => c3 w (Finset.mem_insert.mp hw)) (fun w hw => c4 w (Finset.mem_insert.mp hw))
    (fun w hw => c5 w (fun e => hw (e ▸ Finset.mem_insert_self _ _)) (fun e => hw (Finset.mem_insert_of_mem e))) f φ hφ
    (fun w hw => c6 w (fun e => hw (e ▸ Finset.mem_insert_self _ _)) (fun e => hw (Finset.mem_insert_of_mem e)))
  obtain ⟨φ₁, hφ₁, hφ₁e, he₁⟩ := GlobalTheory.T.theta_trivial_at_finite_set P F E σ B a a' G X om om' hT S g₂ h₂ b1 b2 f φ hφ hφv
  have hφ₁v : ∀ᶠ w in Filter.cofinite, φ₁ w = G.M'.vac w := by
    filter_upwards [hφv, S.finite_toSet.compl_mem_cofinite] with w hw hwS
    rw [hφ₁e w hwS, hw]
  obtain ⟨f₂, he₂⟩ := GlobalTheory.T.archimedean_theta_local_action P F E σ B a a' G X om om' hT g₁ h₁ a1 a2 f φ₁ hφ₁ hφ₁v
  refine ⟨c • f₂, φ₁, hφ₁, hφ₁v, hφ₁e v hvS, ?_⟩
  have hmul : ((g₁ * g₂ * g₃, h₁ * h₂ * h₃) : UA σ G.V'.J × UA σ G.W.J) = (g₁, h₁) * (g₂, h₂) * (g₃, h₃) := rfl
  rw [hmul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc, map_smul, he₁, map_smul, he₂]
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.PureAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiesBOfExplicit
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.BasicNotions.TH Formalism.L2.GlobalTheoryTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.PrimIn.AtData

set_option maxHeartbeats 1000000 in

theorem ev_params : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0) →
    ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ SizesAt L ∧ Nonempty (ParameterChoice' X.toD7 L) ∧
      8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  exact ⟨L, e1, M.sizes, ⟨M.params⟩, M.parT.nV_ge⟩

theorem stepW_ev {Q : Ctx → Prop} (h : Ev Q) : StepW Pinned fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)

end GlobalTheory.PrimIn.AtData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopNodeFormWeightAbsLeLinearStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topNodeFormWeight_abs_le_linear : ∃ K1 : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), sc.cGap = 1 → ∀ τ i, |(((wt G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ K1 * large₂.sc.b := by
  first | exact @GlobalTheory.InfSize.WtSize.wt_top_abs_le | exact GlobalTheory.InfSize.WtSize.wt_top_abs_le | (intros; apply GlobalTheory.InfSize.WtSize.wt_top_abs_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataAbelianStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_ratio_field_data_abelian : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    ∀ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) →
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ → T₀ ≠ 0 →
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) →
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) → (∃ ι : ℂ →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w),
        (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = GlobalTheory.ToricDenom.toBar D.ntw (ex.nch.twI w) (D.ntw.emb0 (ex.nch.twI w) x)) ∧
        ∀ b : Bool, ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (jk : FractionRing (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) (c : ℤ),
            D.ntw.sideL (ex.nch.twI w) lam = b ∧ IsCoprime c (D.ntw.l (ex.nch.twI w) : ℤ) ∧
            jk.comp (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)) = algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) ∧
            ∀ a : ℤ, jk (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) *
                GlobalTheory.ToricDenom.atSide D.ntw b ι T₀ =
              jk (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) * GlobalTheory.ToricDenom.atSide D.ntw b ι (T (ψc ^ (c * a)))) := by
  first | exact @GlobalTheory.ThmAUpper.read_twisted | exact GlobalTheory.ThmAUpper.read_twisted | (intros; apply GlobalTheory.ThmAUpper.read_twisted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunCuspFormReadingLinearIndependentStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_family_linearIndependent : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (n : ℕ) (b : Fin n → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), LinearIndependent (recB (h.laws v).p.toLawsCore).KO b → LinearIndependent ℂ (fun k => rdLin h ha (b k)) := by
  first | exact @GlobalTheory.ShareOn.Reading.rdLin_linearIndependent | exact GlobalTheory.ShareOn.Reading.rdLin_linearIndependent | (intros; apply GlobalTheory.ShareOn.Reading.rdLin_linearIndependent <;> assumption)
end

