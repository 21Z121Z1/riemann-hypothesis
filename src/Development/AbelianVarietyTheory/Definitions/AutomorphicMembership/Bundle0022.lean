import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}

structure Refill (a : Late B C) where

  S : SStage B C a.W

  G : GJStage B C

  L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V

  h : B.Word → ℝ

  HH : ℝ

  HH_ge : sFrame (fun u => { a.V.div.Nu u with L := L u }) h + a.V.div.RR.muMax ≤ HH

  etaF : ℝ

abbrev Refill.to {a : Late B C} (c : Refill a) : Late B C :=
  ⟨a.W, { a.V with
      div := { a.V.div with Nu := fun u => { a.V.div.Nu u with L := c.L u }, h := c.h, HH := c.HH, HH_ge := c.HH_ge, etaF := c.etaF } },
    c.S, a.N, c.G⟩

abbrev Refill.ofSG (a : Late B C) (S : SStage B C a.W) (G : GJStage B C) : Refill a :=
  ⟨S, G, fun u => (a.V.div.Nu u).L, a.V.div.h, a.V.div.HH, a.V.div.HH_ge, a.V.div.etaF⟩

theorem Refill.ofSG_to (a : Late B C) (S : SStage B C a.W) (G : GJStage B C) : (Refill.ofSG a S G).to = ⟨a.W, a.V, S, a.N, G⟩ := rfl

abbrev Refill.ofDiv (a : Late B C) (L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) : Refill a :=
  ⟨a.S, a.G, L, h, max 1 (sFrame (fun u => { a.V.div.Nu u with L := L u }) h + a.V.div.RR.muMax), le_max_right _ _, a.V.div.etaF⟩

def Refill.same {a : Late B C} (c : Refill a) : SameGrp a c.to := SameGrp.ofN a.N a.V c.to.V a.S c.S a.G c.G

def Refill.same' {a : Late B C} (c : Refill a) : SameGrp c.to a := SameGrp.ofN a.N c.to.V a.V c.S a.S c.G a.G

namespace Tr

variable {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def rowSide {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide a.D EE) :
    RowSide c.to.D EE where
  Amb := (X.Amb)
  instAmb := (X.instAmb)
  instAmbi := (X.instAmbi)
  instAmbf := (X.instAmbf)
  Mult := (X.Mult)
  instMult := (X.instMult)
  instMulti := (X.instMulti)
  instMultf := (X.instMultf)
  multZero := (X.multZero)
  multTop := (X.multTop)
  io := (X.io)
  Mtilde := (X.Mtilde)
  cen := (X.cen)
  eOp := (X.eOp)
  eOp_idem := (X.eOp_idem)
  eOp_sa := (X.eOp_sa)
  eOp_tie := (X.eOp_tie)
  RR := (X.RR)
  RR_frames := (X.RR_frames)
  jEE := (X.jEE)
  jEE_basis := (X.jEE_basis)
  jEE_norm := (X.jEE_norm)

def baseLevelRowSideTransport (X : BaseLevelRowSide a.D) : BaseLevelRowSide c.to.D := ⟨(@rowSide B C a c (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X))⟩

def colReal (K : ColReal a.D) : ColReal c.to.D := ⟨(K.xi)⟩

section Chain

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A} {tupT : a.D.what₂.Tup → T}
  {hm : 0 < a.D.R.m} {hTop : TopMultH R}

variable (F tupT hm hTop) in

def spEEc : type_of% (toChainReal R F tupT hm hTop).EEc := ((chainB c.to F tupT hm hTop).EEc)

variable (F tupT hm hTop) in

theorem spEEc_eq : (toChainReal R F tupT hm hTop).EEc = spEEc c F tupT hm hTop := (chain_EEc c.to F tupT hm hTop)

variable (F tupT hm hTop) in

def spCC : type_of% (toChainReal R F tupT hm hTop).CC := ((chainB c.to F tupT hm hTop).CC)

variable (F tupT hm hTop) in

theorem spCC_eq : (toChainReal R F tupT hm hTop).CC = spCC c F tupT hm hTop := (chain_CC c.to F tupT hm hTop)

variable (F tupT hm hTop) in

def spCCP : type_of% (toChainReal R F tupT hm hTop).CCP := ((chainB c.to F tupT hm hTop).CCP)

variable (F tupT hm hTop) in

theorem spCCP_eq : (toChainReal R F tupT hm hTop).CCP = spCCP c F tupT hm hTop := (chain_CCP c.to F tupT hm hTop)

variable (F tupT hm hTop) in

def spCCX : type_of% (toChainReal R F tupT hm hTop).CCX := ((chainB c.to F tupT hm hTop).CCX)

variable (F tupT hm hTop) in

theorem spCCX_eq : (toChainReal R F tupT hm hTop).CCX = spCCX c F tupT hm hTop := (chain_CCX c.to F tupT hm hTop)

variable (F tupT hm hTop) in

def spCCXP : type_of% (toChainReal R F tupT hm hTop).CCXP := ((chainB c.to F tupT hm hTop).CCXP)

variable (F tupT hm hTop) in

theorem spCCXP_eq : (toChainReal R F tupT hm hTop).CCXP = spCCXP c F tupT hm hTop := (chain_CCXP c.to F tupT hm hTop)

variable (F tupT hm hTop) in

def okB (l : Bool) (μ : a.D.what₂.Tup) : Prop := (chainB c.to F tupT hm hTop).IoOK l ((μ))

theorem okB_imp {l : Bool} {μ : a.D.what₂.Tup} (h : okB c F tupT hm hTop l μ) : (toChainReal R F tupT hm hTop).IoOK l μ :=
  chain_ioOK c.to F tupT hm hTop ((h))

theorem eq_via {N : Type} {r : ℂ} (f : N → ℂ) {u u' v : N} (h : r = f u) (e : v = u') (hu : u' = u) : r = f v := by
  rw [e, hu, h]

def ioCB (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) : (toChainReal R F tupT hm hTop).Amb k :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioC l ((by with_unfolding_all exact (μ :))) k
    ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v) :)))).1 :))

theorem ioCB_eq (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) :
    ioCB c l μ k v = ((toChainReal R F tupT hm hTop).ioC l μ k v).1 :=
  (by with_unfolding_all exact ((chain_ioC c.to (R := R) (tupT μ) k ((v.1))
    (((LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v).2)) ((v.2))) : _))

def ioXB' (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) : (toChainReal R F tupT hm hTop).Amb (a.D.R.m - 1) :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioX l ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v) :)))).1 :))

theorem ioXB'_eq (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) :
    ioXB' c l μ v = ((toChainReal R F tupT hm hTop).ioX l μ v).1 :=
  (by with_unfolding_all exact ((chain_ioX c.to (R := R) hm hTop (tupT μ) ((by with_unfolding_all exact (v.1 :))) ((by with_unfolding_all exact ((topMult_tr c.to hTop) :)))
    ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v).2 :))) ((by with_unfolding_all exact (v.2 :)))) :))

end Chain

end Tr

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoIff
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {f : T' → T} {μ : T'}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D (A.comap id (f μ)) C.Q.c.F}
  (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T') (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)))

set_option maxHeartbeats 1600000 in

def omDat {i : Fin D.R.m} (O : OMDat C.toCore R i Unit fun _ => (A.comap id (f μ)).μ0) :
    OMDat C.toCore (dat2 f μ R mu tw) i Unit fun _ => (A.comap f μ).μ0 := { O with }

set_option maxHeartbeats 1600000 in

def fwTie {κ v₀} (t : FWTie C R κ v₀) : FWTie C (dat2 f μ R mu tw) κ v₀ :=
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }

set_option maxHeartbeats 1600000 in

theorem omPins {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (O : ∀ i, OMDat C.toCore R i Unit fun _ => (A.comap id (f μ)).μ0) (i : Fin D.R.m) (h : OMPins C R κ v₀ O i) :
    OMPins C (dat2 f μ R mu tw) κ v₀ (fun i => omDat mu tw (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  obtain ⟨g, c, l, ht, hb⟩ := h1.c0
  refine ⟨⟨h1.field, h1.std, ?_, ⟨g, c, l, ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, fun t => ht.ok (f t), ht.gramR_eq,
    ht.mapR, ht.mapL, fun t => ht.coefR (f t), fun i t => ht.coefL i (f t)⟩, hb⟩, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

set_option maxHeartbeats 1600000 in

def geoHalf {ph : Fin D.R.m → ℂ} (g : GlobalTheory.RealGeo.GeoHalf C R ph) : GlobalTheory.RealGeo.GeoHalf C (dat2 f μ R mu tw) ph :=
  ⟨g.κ, g.v₀, fwTie mu tw g.fw, g.bar, fun i => omDat mu tw (g.O i), fun i => omPins mu tw g.O i (g.pins i), g.rhoGeo, g.equivAll,
    g.cTie, g.phase⟩

set_option maxHeartbeats 1600000 in

theorem inGeo {ph : Fin D.R.m → ℂ} {g : GlobalTheory.RealGeo.GeoHalf C R ph} (h : GlobalTheory.RealGeo.InGeo g) :
    GlobalTheory.RealGeo.InGeo (geoHalf mu tw g) :=
  ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩

set_option maxHeartbeats 1600000 in

theorem inGeo_iff {ph : Fin D.R.m → ℂ} {g : GlobalTheory.RealGeo.GeoHalf C R ph} :
    GlobalTheory.RealGeo.InGeo (geoHalf mu tw g) ↔ GlobalTheory.RealGeo.InGeo g :=
  ⟨fun h => ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩, inGeo mu tw⟩

end GlobalTheory.Mem.R3.Res

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictedCharacterDataValid
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (f : T' → T) (μ : T')

def dat3 (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : RealDat3 D (A3.comap f μ) Ks where
  toRealDat := dat2 (A := A3.A) f μ R.toRealDat mu tw
  plI := R.plI
  SF := R.SF
  phs := R.phs
  lam3 i t := R.lam3 i (f t)

def bare3 (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* D.what₂.LLˣ) : Face3 D A3 where
  P0 := P0
  ψ0 := ψ0
  P1 := P1
  ψ1 := ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable {f μ} {R : RealDat3 D (A3.comap id (f μ)) Ks} (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
  (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}

set_option maxHeartbeats 2000000 in

theorem isInert (h : R.IsInert) : (dat3 f μ R mu tw).IsInert := by
  exact ⟨⟨h.tie.plI_inj, fun t Q => h.tie.okI (f t) Q⟩, h.onto, fun t => h.hR (f t), fun i t => h.hL i (f t), h.SF⟩

set_option maxHeartbeats 2000000 in

theorem pThmB (h : R.PThmB) : (dat3 f μ R mu tw).PThmB := by
  intro t p x hx
  exact h (f t) p x hx

set_option maxHeartbeats 2000000 in

theorem isScal (h : R.IsScal (bare3 _ P0 ψ0 P1 ψ1)) (hB : R.PThmB) : (dat3 f μ R mu tw).IsScal (bare3 _ P0 ψ0 P1 ψ1) where
  lam0 i t := h.lam0 i (f t)
  kap κ hκ hne := by
    obtain ⟨t, p, hp, hl⟩ := hne
    exact Lift.IsKap.unique (pThmB mu tw hB) hκ t p hp hl
  off := h.off
  abs0 i t := h.abs0 i (f t)
  abs := h.abs
  tup i t := h.tup i (f t)

structure NewTup (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : Prop where

  sub : tw ⊆ R.twPl

  conj : ∀ w, Formalism.DivisionValues.conjPl w ∈ tw ↔ w ∈ tw

  on : ∀ w ∈ tw, f (mu w) = R.mu w

  off : ∀ w, w ∉ tw → mu w = μ

  used : ∀ t, t = μ ∨ ∃ w, mu w = t

variable {mu tw} in

theorem isTup (hf : Function.Injective f) (h : R.IsTup) (n : NewTup R mu tw) : (dat3 f μ R mu tw).IsTup where
  mu_off := n.off
  mu_used := n.used
  mu_ne w hw heq := by
    change mu w = μ at heq
    apply h.mu_ne w (n.sub hw)
    rw [← n.on w hw, heq]
    rfl
  mu_conj w := by
    change mu (Formalism.DivisionValues.conjPl w) = mu w
    by_cases hw : w ∈ tw
    · apply hf
      have hc : Formalism.DivisionValues.conjPl w ∈ tw := (n.conj w).2 hw
      rw [n.on _ hc, n.on w hw]
      exact h.mu_conj w
    · have hc : Formalism.DivisionValues.conjPl w ∉ tw := fun hc => hw ((n.conj w).1 hc)
      rw [n.off _ hc, n.off w hw]
  mu_on w hw := by
    obtain ⟨ψw, Qw, h1, h2⟩ := h.mu_on w (n.sub hw)
    refine ⟨ψw, Qw, h1, ?_⟩
    change R.xiH (f (mu w)) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψw
    rw [n.on w hw]
    exact h2

variable {mu tw} in
set_option maxHeartbeats 2000000 in

theorem restricted_character_data_valid (hf : Function.Injective f) (h : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (e : R.toRealDat.ExAt) (hB : R.PThmB)
    (n : NewTup R mu tw) : (dat3 f μ R mu tw).WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1) where
  base := baseW mu tw hf h.base e
  inert := isInert mu tw h.inert
  fullY t := h.fullY (f t)
  fullX t := h.fullX (f t)
  fullP i t := h.fullP i (f t)
  scal := isScal mu tw h.scal hB
  tup := isTup hf h.tup n
  phase := h.phase
  allPl := h.allPl

set_option maxHeartbeats 2000000 in

theorem keep {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Keep (A3 := A3.comap id (f μ)) R.toRealDat (bare3 _ P0 ψ0 P1 ψ1).lv2 cG) :
    Keep (A3 := A3.comap f μ) (dat3 f μ R mu tw).toRealDat (bare3 _ P0 ψ0 P1 ψ1).lv2 cG where
  std := h.std
  signs := h.signs
  frames := h.frames
  beta := h.beta
  prX := h.prX
  grp := h.grp
  psi := h.psi
  guard := ⟨fun t => h.guard.1 (f t), fun t => h.guard.2 (f t)⟩
  valKs := h.valKs
  frameKs := h.frameKs
  levKs := h.levKs

variable {mu tw} in
set_option maxHeartbeats 2000000 in

theorem pins (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (hB : R.PThmB) (n : NewTup R mu tw) : Pins (dat3 f μ R mu tw) (bare3 _ P0 ψ0 P1 ψ1) cG where
  char := restricted_character_data_valid hf h.char e hB n
  keep := keep mu tw h.keep
  phs := h.phs
  trSem := h.trSem

end GlobalTheory.Mem.R3.Res

end
end

