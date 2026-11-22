import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0017
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
import Formalism.LocalToGlobal.IndefiniteReal.EigSumLeComapSemi
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0015
import Formalism.LocalToGlobal.GlobalTheory.PassageAtBaseSymmetricLevels
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxCore
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

structure CxCore (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (X : CxData A.fam.amb) (s : ℕ)
    (C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop)
    (ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K)
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH)
    (C CH : ℝ)
    (hE : ∀ t, (A.fam.R t).Pl × ℕ → Module.End ℂ X.EE)
    (hW : ∀ j t, (A.fam.L j t).Pl × ℕ → Module.End ℂ (X.W j)) (gE : Representation ℂ G X.EE)
    (gW : ∀ j, Representation ℂ G (X.W j)) : Prop where

  kFormR : X.KFormR

  kFormL : X.KFormL

  jIsoR : X.JIsoR (cvOf A P0 ψ0 P1 ψ1)

  jIsoL : X.JIsoL (cvOf A P0 ψ0 P1 ψ1)

  npTie : NPTie X P0 P1

  ok : A.fam.Ok s

  sep : A.fam.TypesSep

  heckeR : HeckeRatAllR A

  heckeL : HeckeRatAllL A

  thetaR : HeckeThetaR A X hE

  thetaL : HeckeThetaL A X hW

  gUnit : Formalism.IndefR.CxPass.GUnit A X gE

  gEquiv : Formalism.IndefR.CxPass.GEquiv A X gE

  lev0 : Formalism.IndefR.CxPass.LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE false P0 ψ0

  lev1 : Formalism.IndefR.CxPass.LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE true P1 ψ1

  h2P : Formalism.IndefR.CxPass.PrincipalInjectiveCommonRange A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc)

  gUnitL : Formalism.IndefR.CxPass.GUnitL A X gW

  gEquivL : Formalism.IndefR.CxPass.GEquivL A X gW

  lower_level_lift_type : Formalism.IndefR.CxPass.LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0

  upper_level_lift_type : Formalism.IndefR.CxPass.LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW true P1 ψ1

  inBlock : X.zs.InBlock

  ratZ : X.RatZ

  eig0 : LiftsEig A X P0 ψ0 C0

  eig1 : LiftsEig A X P1 ψ1 C1

  typ0 : LiftsTyp A C0

  typ1 : LiftsTyp A C1

  pos : ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Pos

  h0 : X.H0

  w1 : ∀ w, X.W1 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH) w → w ∈ X.Tw

  h4pos : X.H4pos

  thmBop : ∀ b, X.ThmBop b

  partsE : ∀ b, X.PartsE b

  ratMu : ∀ b, X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  kForm : ∀ b, X.KForm b

  mLat : ∀ b, X.MLat b

  ewNorm : ∀ b, X.EWnorm b

  thmAop : ∀ b, X.ThmAop b

  partsW : ∀ b, X.PartsW b

  ratTh : ∀ b, X.RATth (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  galD : ∀ b, X.GalD (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  dimParts : ∀ b, X.DimParts b

  l3 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).L3 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  on : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).ON ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  l6 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true).L6 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  btVanish : X.BtVanish (fc := faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc)

  mi0 : X.MatrixIdentityOffBase (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ζ

  zetaOK : X.ZetaOK ζ

  l1e : (X.colOf (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e

  fun0 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).FUN ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

section Core

variable {A : FamIn K G Pl0 T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base} {X : CxData A.fam.amb} {s : ℕ}
  {C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop}
  {ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH}
  {C CH : ℝ}
  {hE : ∀ t, (A.fam.R t).Pl × ℕ → Module.End ℂ X.EE} {hW : ∀ j t, (A.fam.L j t).Pl × ℕ → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)}

theorem CxCore.stable (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW) : X.zs.Stable :=
  CxData.cutStable X hC.kFormR hC.kFormL
    (Formalism.IndefR.CxPass.kerStabR_of hC.kFormR hC.gEquiv (kerStabR_hecke hC.thetaR))
    (Formalism.IndefR.CxPass.kerStabL_of hC.kFormL hC.gEquivL (kerStabL_hecke hC.thetaL))
    (adjClosedR_of hC.ok hC.heckeR hC.kFormR hC.jIsoR) (adjClosedL_of hC.ok hC.heckeL hC.kFormL hC.jIsoL)

theorem CxCore.wf (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW) :
    ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).WF := fun b => match b with
  | false => A.side_WF hC.ok P0 ψ0 X.zs hC.stable hC.inBlock hC.sep
  | true => A.side_WF hC.ok P1 ψ1 X.zs hC.stable hC.inBlock hC.sep

theorem CxCore.h2 (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW) (b : Bool) :
    X.H2 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b :=
  (cutRows (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf A P0 ψ0 P1 ψ1) b (hC.wf b) hC.h4pos
    (isoR_of hC.ok hC.jIsoR hC.npTie b) (crdZ_of X b) (coordinates_in_good_part_of_definite X b)
    (Formalism.IndefR.CxPass.ratLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv b)
    (Formalism.IndefR.CxPass.dnLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv hC.h2P hC.lev0 hC.lev1 b)
    (Formalism.IndefR.CxPass.upLev_of hC.ok hC.kFormR hC.jIsoR hC.gUnit hC.gEquiv hC.lev0 hC.lev1 b)
    (hC.thmBop b) (hC.partsE b)).1

theorem prims_of_core (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW)
    (hPass : Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
      (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)) :
    CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X (cvOf A P0 ψ0 P1 ψ1) s C0 C1 ζ sEE C CH := by
  have kR : X.KerStabR := Formalism.IndefR.CxPass.kerStabR_of hC.kFormR hC.gEquiv (kerStabR_hecke hC.thetaR)
  have kL : X.KerStabL := Formalism.IndefR.CxPass.kerStabL_of hC.kFormL hC.gEquivL (kerStabL_hecke hC.thetaL)
  have aR : X.AdjClosedR := adjClosedR_of hC.ok hC.heckeR hC.kFormR hC.jIsoR
  have aL : X.AdjClosedL := adjClosedL_of hC.ok hC.heckeL hC.kFormL hC.jIsoL
  have hst : X.zs.Stable := CxData.cutStable X hC.kFormR hC.kFormL kR kL aR aL
  exact
    { kFormR := hC.kFormR, kFormL := hC.kFormL, kerStabR := kR, kerStabL := kL, adjClosedR := aR, adjClosedL := aL
      inBlock := hC.inBlock, ratZ := hC.ratZ, jIsoR := hC.jIsoR, jIsoL := hC.jIsoL, ok := hC.ok, sep := hC.sep
      heckeR := hC.heckeR A.fam.μ0, heckeL := fun j => hC.heckeL j A.fam.μ0
      eig0 := hC.eig0, eig1 := hC.eig1, typ0 := hC.typ0, typ1 := hC.typ1, pos := hC.pos, h0 := hC.h0, w1 := hC.w1
      h4pos := hC.h4pos, isoR := isoR_of hC.ok hC.jIsoR hC.npTie, crdZ := crdZ_of X, coordinates_in_good_part := coordinates_in_good_part_of_definite X
      ratLev := Formalism.IndefR.CxPass.ratLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv
      dnLev := Formalism.IndefR.CxPass.dnLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv hC.h2P hC.lev0 hC.lev1
      upLev := Formalism.IndefR.CxPass.upLev_of hC.ok hC.kFormR hC.jIsoR hC.gUnit hC.gEquiv hC.lev0 hC.lev1
      thmBop := hC.thmBop, partsE := hC.partsE
      ratMu := hC.ratMu, h3 := equivRows_of P0 ψ0 P1 ψ1 Dc Sp Zsc hC.kFormR hst hC.ok hC.thetaR
      kForm := hC.kForm, mLat := hC.mLat, ewNorm := hC.ewNorm, isoL := isoL_of hC.ok hC.jIsoL hC.npTie
      crdZL := crdZL_of X, lift_coordinates_in_good_part := lift_coordinates_in_good_part_of_definite X
      ratLevL := Formalism.IndefR.CxPass.ratLevL_of hC.ok hC.kFormL hC.jIsoL hC.ratZ hC.gUnitL hC.gEquivL
      dnLevL := Formalism.IndefR.CxPass.dnLevL_of hC.ok hC.kFormL hC.jIsoL hC.ratZ hC.gUnitL hC.gEquivL hC.lower_level_lift_type hC.upper_level_lift_type
      upLevL := Formalism.IndefR.CxPass.upLevL_of hC.ok hC.kFormL hC.jIsoL hC.gUnitL hC.gEquivL hC.lower_level_lift_type hC.upper_level_lift_type
      thmAop := hC.thmAop, partsW := hC.partsW, ratTh := hC.ratTh
      h3W := equivLifts_of P0 ψ0 P1 ψ1 Dc Sp Zsc hC.kFormL hst hC.ok hC.thetaL
      galD := hC.galD, dimParts := hC.dimParts, l3 := hC.l3, on := hC.on, l6 := hC.l6, btVanish := hC.btVanish
      mi0 := hC.mi0, zetaOK := hC.zetaOK, l1e := hC.l1e, passage := hPass, fun0 := hC.fun0 }

theorem links_of_core (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW)
    (hPass : Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
      (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)) :
    X.CxLinks (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE) C CH :=
  links_of_prims (prims_of_core hC hPass)

end Core

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.InBlock
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

structure In3 (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type)
    (m : ℕ) where
  A3 : FamIn3 K G Pl0 I0 Ty T m
  P0 : Subgroup G
  ψ0 : P0 →* Kˣ
  P1 : Subgroup G
  ψ1 : P1 →* Kˣ
  Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)
  Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)
  Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3
  X : CxData A3.fam3.amb3
  gE : Representation ℂ G X.EE

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

abbrev A : FamIn K G Pl0 T m := I.A3.A

abbrev cr : Crd I.A3.fam3.amb3 (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

abbrev cg : Crd I.A3.fam3.amb3 (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

def lvP : Bool → Subgroup G := fun b => cond b I.P1 I.P0

def lvψ : ∀ b, I.lvP b →* Kˣ
  | false => I.ψ0
  | true => I.ψ1

abbrev Sb (b : Bool) := I.X.data I.cr b

abbrev Sg := (prin I.X).data I.cg false

abbrev iCg := I.X.iC I.cg false I.A3.fam3.base3.μ0

def Jm (b : Bool) : Matrix (Fin I.Sg.D) (Fin (I.Sb b).D) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat I.iCg (I.X.iC I.cr b I.A3.fam3.base3.μ0))

def ρf (g : G) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat I.iCg ((I.gE g).comp I.iCg))

def Jt (b : Bool) (t : I.A3.fam3.base3.Tup) :
    Matrix (Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t)) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat (I.X.iC I.cg false t) (I.X.iC I.cr b t))

open Classical in

def epM (P : Subgroup G) (ψ : P →* Kˣ) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  haveI : Fintype P := Fintype.ofFinite P
  ((Nat.card P : K)⁻¹) • ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)

def eMat {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  (Formalism.IndefR.TransferLatticeStatement.charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, Formalism.IndefR.TransferLatticeStatement.charOf τ x⁻¹ • I.ρf x

abbrev LA {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) : LevelAmb K (I.Sb false).D (I.Sb true).D where
  Dg := I.Sg.D
  Xg := I.Sg.XE
  Rg := I.Sg.RR
  ep0 := I.epM I.P0 I.ψ0
  ep1 := I.epM I.P1 I.ψ1
  S := S
  fS := inferInstance
  es s := I.eMat (τ s)
  nS s := Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) ⟨I.P1, I.ψ1⟩
  nbar := nbar
  G := Fintype.card G
  h0 := Nat.card I.P0
  h1 := Nat.card I.P1
  ι0 := I.Jm false
  ι1 := I.Jm true

structure Hyp (s : ℕ) : Prop where
  ok : I.A3.fam3.Ok3 s
  sep : I.A3.fam3.TypesSep3
  stable : I.X.zs.Stable
  inBlock : I.X.zs.InBlock
  h4pos : I.X.H4pos
  pos0 : (I.A3.side3 I.P0 I.ψ0 I.X.zs).Pos
  pos1 : (I.A3.side3 I.P1 I.ψ1 I.X.zs).Pos
  h2 : ∀ b, I.X.H2 I.cr b
  ratMu : ∀ b, I.X.RATmu I.cr b
  h2g : PrincipalLevelBijectivity I.A3 I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)
  ratMug : I.X.RATmu I.cg false
  gunit : ∀ (g : G) (x y : I.X.EE), ⟪I.gE g x, I.gE g y⟫_ℂ = ⟪x, y⟫_ℂ
  gequiv : GEquiv3 I.A3 I.X I.gE
  np0 : I.X.nP false = (Nat.card I.P0 : ℝ)
  np1 : I.X.nP true = (Nat.card I.P1 : ℝ)

def PRho : Prop :=
  ∀ s, I.Hyp s → I.ρf 1 = 1 ∧ (∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) ∧
    ∀ g (x : Fin I.Sg.D → K), I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.ρf g *ᵥ x)) =
      I.gE g (I.iCg (cpt I.A3.fam3.base3.v0.embedding x))

def PJ : Prop :=
  ∀ s, I.Hyp s → ∀ b, (∀ x : Fin (I.Sb b).D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ x)) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x)) ∧ Function.Injective (I.Jm b).mulVec

def PJt : Prop :=
  ∀ s, I.Hyp s → ∀ b t,
    (∀ x, I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding (I.Jt b t *ᵥ x)) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x)) ∧
    (∀ x, I.cg.toR I.X.zs false t (I.Jt b t *ᵥ x) = I.cr.toR I.X.zs b t x) ∧
    ∀ x, I.Jm b *ᵥ (I.X.rowMat I.cr b t *ᵥ x) = I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ x)

def PRange : Prop :=
  ∀ s, I.Hyp s → ∀ b, LinearMap.range (I.Jm b).mulVecLin = LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin

def PMet : Prop :=
  ∀ s, I.Hyp s → ∀ b v (x y : Fin (I.Sb b).D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (I.Sb b).D)) (I.Sb b).XE v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt (Nat.card (I.lvP b))) I.Sg.XE) v
        (I.Jm b *ᵥ x) (I.Jm b *ᵥ y)

def PFrames : Prop := ∀ s, I.Hyp s → ∀ v, IsUnit (I.Sg.XE v).det

def PUni : Prop :=
  ∀ s, I.Hyp s → ∀ v (g : G) (x y : Fin I.Sg.D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v (I.ρf g *ᵥ x) (I.ρf g *ᵥ y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v x y

def PLat : Prop := ∀ s, I.Hyp s → Submodule.IsLattice K I.Sg.RR

def PGLat : Prop := ∀ s, I.Hyp s → ∀ (g : G), ∀ x ∈ I.Sg.RR, I.ρf g *ᵥ x ∈ I.Sg.RR

def PSand : Prop :=
  ∀ s, I.Hyp s → ∀ b,
    (∀ x ∈ (I.Sb b).RR, I.Jm b *ᵥ x ∈ I.Sg.RR) ∧
    ∀ y ∈ I.Sg.RR, y ∈ LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin →
      ∃ x ∈ (I.Sb b).RR, I.Jm b *ᵥ x = ((Nat.card (I.lvP b) : ℕ) : 𝓞 K) • y

def PGood {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) : Prop :=
  ∀ s, I.Hyp s → Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ I.A.fam.X → ∑ t, I.eMat (τ t) = 1

end In3

end Formalism.IndefR.CxPass
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.MajAtEqZeroOfMemQpOfNe
section
open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx.GroupActionMatrices

section Inst3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}

theorem okOp_opAll {B : BlockDat K G Pl0} {D : InertDat3 B I0 Ty} {s : ℕ} (h : B.Ok s) (hD : D.Ok3) (hH : B.OkH)
    (hH3 : D.InertRationalAdjoint) : OkOp B D.opAll where
  rat i a b := by
    rcases i with p | k
    · exact hH.rat p a b
    · exact hH3.rat k a b
  adj i := by
    rcases i with p | k
    · obtain ⟨p', hp'⟩ := hH.adj p
      exact ⟨Sum.inl p', hp'⟩
    · obtain ⟨k', hk'⟩ := hH3.adj k
      exact ⟨Sum.inr k', hk'⟩
  comm := hD.comm
  split := InertDat3.splitOver_opAll D h hD
  opG i g := by
    rcases i with p | k
    · exact h.opG p g
    · exact hD.opG k g

end Inst3

section Main3

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3)

theorem proviso_of_lift_eigenvalues {s : ℕ} (hOk : A3.fam3.Ok3 s) (hH : ∀ j, (A3.A.fam.L j A3.A.fam.μ0).OkH ∧ (A3.liftI j A3.A.fam.μ0).InertRationalAdjoint)
    (P : Subgroup G) (ψ : P →* Kˣ) {C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
    (hC : LiftsEig3 A3 X P ψ C) : (A3.side3 P ψ X.zs).Proviso := by
  intro j
  have hB := DefFam.blockHyp_lift A3.A.fam hOk.ok2 P ψ j A3.A.fam.μ0
  have hO : OkOp _ (A3.liftI j A3.A.fam.μ0).opAll :=
    okOp_opAll (hOk.ok2.lifts j A3.A.fam.μ0) (hOk.lifts j A3.A.fam.μ0) (hH j).1 (hH j).2
  have hr := eig_ratG hB hO (C j)
  rw [← hC j] at hr
  exact CyclotomicLifting.xq_rat hB hr

theorem types_of_lift_eigenvalues {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (hst : X.zs.Stable) (P : Subgroup G)
    (ψ : P →* Kˣ) {C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop} (hC : LiftsEig3 A3 X P ψ C)
    (hT : LiftsTyp3 A3 C) : (A3.side3 P ψ X.zs).Types := by
  intro j
  refine (A3.fam3.LI j A3.A.fam.μ0).inert_parts_span_top (ℓ := A3.A.fam.lvlA P ψ) (Z := X.Zl j A3.A.fam.μ0)
    hOk.ok2.conj (hOk.ok2.lifts j A3.A.fam.μ0) (hOk.lifts j A3.A.fam.μ0)
    hOk.ok2.irr ?_ (fun p : A3.fam3.base3.Ix => A3.fam3.tr3 j p.1) ?_ ?_
  · intro i
    exact Submodule.map_le_iff_le_comap.1 (hst.2 j A3.A.fam.μ0 (Sum.inl i))
  · intro p q hpq
    exact hsep p.1 p.2 q.1 q.2 (fun h => hpq (Subtype.ext h)) j
  · refine (hC j).le.trans ?_
    apply BlockDat.good_part_coordinates_mono
    refine Col.eigSum_mono fun x hx => ?_
    obtain ⟨p, hp, hx'⟩ := hT j x hx
    exact ⟨⟨p, hp⟩, hx'⟩

theorem majAt_eq_zero_of_mem_Qp_of_ne {s : ℕ} (hOk : A3.fam3.Ok3 s) (hH : (A3.A.fam.R A3.A.fam.μ0).OkH ∧ (A3.rowI A3.A.fam.μ0).InertRationalAdjoint)
    (hst : X.zs.Stable) (P : Subgroup G) (ψ : P →* Kˣ) (v : InfinitePlace K) (p q : A3.fam3.base3.Ix) (hpq : p ≠ q)
    (x : Fin ((A3.side3 P ψ X.zs).dQ A3.A.fam.μ0) → K) (hx : x ∈ (A3.side3 P ψ X.zs).Qp A3.A.fam.μ0 p)
    (y : Fin ((A3.side3 P ψ X.zs).dQ A3.A.fam.μ0) → K) (hy : y ∈ (A3.side3 P ψ X.zs).Qp A3.A.fam.μ0 q) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((A3.side3 P ψ X.zs).XQ A3.A.fam.μ0) v x y = 0 := by
  have hB : BlockHyp (A3.A.fam.R A3.A.fam.μ0) (A3.A.fam.lvl P ψ) A3.A.fam.v0 s :=
    ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ A3.A.fam.μ0⟩
  have hO : OkOp (A3.A.fam.R A3.A.fam.μ0) (A3.fam3.RI A3.A.fam.μ0).opAll :=
    okOp_opAll (hOk.ok2.what₂ A3.A.fam.μ0) (hOk.what₂ A3.A.fam.μ0) hH.1 hH.2
  refine part_orthg hB hO (fun i => Submodule.map_le_iff_le_comap.1 (hst.1 A3.A.fam.μ0 (Sum.inl i))) v
    (C := (A3.fam3.RI A3.A.fam.μ0).HasRes3 p.1) (C' := (A3.fam3.RI A3.A.fam.μ0).HasRes3 q.1) ?_ hx hy
  intro z hz
  exact (A3.fam3.RI A3.A.fam.μ0).excl3
    ((A3.fam3.RI A3.A.fam.μ0).diffAt_of_mem_ixFin3 q.2 p.2 (fun h => hpq (Subtype.ext h).symm)) z hz

end Main3

end Formalism.IndefR.Cx
end
end

