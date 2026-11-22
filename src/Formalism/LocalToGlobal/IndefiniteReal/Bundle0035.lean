import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
import Formalism.LocalToGlobal.IndefiniteReal.IsFDiagIffDiagonal
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealPins
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

open Classical in

structure RealPins {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : RealT Rc P Dcf Spf Zscf S Ks) : Prop where

  cfEq : Q.Rl.C = Rc.T.n.cf

  qGuard : Formalism.IndefR.FWT.QGuard Q.Rl.toRealDat

  hF : D.host.F = maximalRealSubfield D.host.E

  phsOne : ∀ i, Q.Rl.phs i = 1

  prXunit : Formalism.IndefR.Seed.PrIso Q.Rl.MX Q.Rl.cX Q.Rl.prX

  grpRecPin : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ Q.Rl.toRealDat.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : Q.Rl.toRealDat.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf P.A3.A.X).coeff g) = D.ntypes.e0.coeff ((Q.Rl.eG.trans Q.cG) g)) ∧
    (∀ kv, Q.Rl.toRealDat.C.P.Div kv.1 (plg kv).1) ∧
    ∀ g kv, Q.Rl.toRealDat.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((Q.Rl.eG.trans Q.cG) g kv)

  fdiag : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i)

  pgEq : Q.Rl.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE)

  tSfin : Q.tS ∈ Formalism.L2.Theta.GfC (Yc D 0)

  tSpin : (∃ t ∈ Formalism.L2.Theta.GfC (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq t) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel Q.tS⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq Q.tS

  eGtie : P.I.eG = Q.Rl.eG.trans Q.cG

  betaStd : (∀ i, Q.Rl.βV i = 1) ∧ Q.Rl.βX = 1

  bR_read : ∀ x i, Q.bR x i = D.eMu (Q.wdD x) (D.jN (Q.wdD x) (P.I.eNu (Q.wdD x)
    (Pi.single (Fin.cast (congrArg P.Dc.a (Q.wU_wdD x)).symm i) 1)))

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def SeeEx (Q : RealT Rc P Dcf Spf Zscf S Ks) : Prop :=
  (∃ t ∈ Formalism.L2.Theta.GfC (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq t) ∧
    ∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (Q.Rl.MY 0) Q.Rl.ν0 Q.Rl.fd0 (Q.Rl.toRealDat.EEat (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G Q.ιS Q.tS c'

end Formalism.IndefR
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealRec
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def twPOf (P : RowSideFamily ex) (tupT : D.what₂.Tup → P.T) (tupTie : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → P.I.tup (tupT μ) = μ)
    (μ : D.what₂.Tup) (i : Fin D.R.m) (x : D.what₂.MtL μ ((i : ℕ) + 1)) :
    P.A3.A.fam.amb.FL i (tupT μ) :=
  if h : Formalism.IndefR.RecTie.Used0 D μ then
    (P.A3.A.fam.L i (tupT μ)).S.basis.equivFun.symm
      (((P.A3.A.fam.L i (tupT μ)).S.lvlE (P.A3.A.fam.L i (tupT μ)).r (P.A3.A.fam.lvlA P.P0 P.ψ0).P
          (P.A3.A.fam.lvlA P.P0 P.ψ0).ψ).mulVec
        ((P.I.eMt i (tupT μ)).symm ((tupTie μ h).symm ▸ x)))
  else 0

theorem dW_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.dW = S1.dW := by
  subst h
  cases hS
  rfl

theorem dWL_eq (Q : RealT Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i) = (P.A3.indefDown P.S0).dW i := by
  refine (congrFun (dW_of_heq ?_ Q.s0) i).trans ?_
  · rw [Q.zs]
    rfl
  · rfl

def jDT (Q : RealT Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (y : Fin ((P.A3.indefDown P.S0).dW i) → D.what₂.LL) :
    Fin (Q.Rl.nW i) → D.what₂.LL :=
  Formalism.IndefR.NX.jDL Q.Rl Q.F.lv2 i (y ∘ Fin.cast (dWL_eq Q i))

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RealRec (Q : RealT Rc P Dcf Spf Zscf S Ks) : Type 1 where

  tupT : D.what₂.Tup → P.T

  hm : 0 < D.R.m

  hTop : Formalism.IndefR.RecTie.TopMultH Q.Rl.toRealDat

  hinj : ∀ i t, Function.Injective (Q.Rl.toRealDat.extV i t)

  Ish : Formalism.IndefR.RecTie.RowIds (Formalism.BasicNotions.RowSide.sharp D) (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) true

  I0 : Formalism.IndefR.RecTie.RowIds ex.p0.s (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) false

  IL : Formalism.IndefR.RecTie.LiftIds (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj)

  Kc : Formalism.IndefR.RecTie.ColReal D

  E : EigIdx D Y

  labPi : E.Pi → P.A3.A.fam.base.Ix

  PY : Formalism.IndefR.principalLevelFrame.RowPsi (Yc D 0) D.R.r

  PW : ∀ i, Formalism.IndefR.principalLevelFrame.RowPsi (Wc D i) D.R.r

  eFT : D.what₂.FT ≃ Formalism.IndefR.principalLevelFrame.FTR Q.Rl.θ PY (Q.Rl.MY 0)
    (fun b => levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b)))
    (fun b => Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b))) (fun _ => Q.Rl.e0)

  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

  ιW : ∀ i, ↥(Formalism.L2.Theta.GfC (Yc D 0)) →* ↥(Formalism.L2.Theta.GfC (Wc D i))

  Tp : Formalism.L2.Host.TupTied D Q.Rl.C ex.nch

  recR : Formalism.IndefR.RecTie.RecReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj ex.p0 Ish I0 IL Kc E labPi PY PW eFT piOf ιW ex.nch Tp

  tpEq : HEq Tp Rc.T.n.tp

  tupTie : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → P.I.tup (tupT μ) = μ

  tupT_tup : ∀ t, tupT (P.I.tup t) = t

  muEq : Q.Rl.mu = P.S0.μ

  mtRead : Formalism.IndefR.RecTie.MtRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (twPOf P tupT tupTie)

  mjRead : Formalism.IndefR.RecTie.MjRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (fun i => (P.A3.indefDown P.S0).dW i)
    (fun i y => P.I.jW i y) (jDT Q)

namespace RealRec

variable {Q : RealT Rc P Dcf Spf Zscf S Ks} (Qr : RealRec Q)

theorem tupT_inj_used {μ μ' : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (hμ' : Formalism.IndefR.RecTie.Used0 D μ')
    (h : Qr.tupT μ = Qr.tupT μ') : μ = μ' := by
  calc μ = P.I.tup (Qr.tupT μ) := (Qr.tupTie μ hμ).symm
    _ = P.I.tup (Qr.tupT μ') := by rw [h]
    _ = μ' := Qr.tupTie μ' hμ'

theorem tupleRead_baseTuple_eq_family : Qr.tupT D.what₂.mu0 = P.A3.A.μ0 := by
  have h : P.I.tup P.A3.A.μ0 = D.what₂.mu0 := by
    first
    | exact P.tied.div.tup.mu0
    | exact P.tied.div.1.tup.mu0
    | exact P.tied.div.tied.tup.mu0
  rw [← h]
  exact Qr.tupT_tup _

theorem tw_iff (Qr : RealRec Q) (w : D.what₂.places.Pl) : D.plEq w ∈ Q.Rl.twPl ↔ D.what₂.muAt w ≠ D.what₂.mu0 := by
  have h0 := Qr.tupleRead_baseTuple_eq_family
  constructor
  · intro hw he
    apply Q.charW.tup.mu_ne (D.plEq w) hw
    rw [← Qr.recR.tupAt w, he, h0]
  · intro hne
    by_contra hw
    apply hne
    apply Qr.tupT_inj_used (Or.inr ⟨w, rfl⟩) (Or.inl rfl)
    rw [Qr.recR.tupAt w, Q.charW.tup.mu_off (D.plEq w) hw, h0]

end RealRec

namespace RealRec

variable {Q : RealT Rc P Dcf Spf Zscf S Ks}

def ThetaFireAll (Qr : RealRec Q) : Prop :=
  Formalism.IndefR.RecTie.ThetaFireRow (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.hTop Qr.hinj) Qr.IL

def PartsRow (Qr : RealRec Q) : Prop :=
  Formalism.IndefR.RecTie.PartsRec Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.PY Qr.PW Qr.eFT Qr.E Qr.labPi Qr.piOf Qr.Ish.prt Qr.IL.prtW

end RealRec

end Formalism.IndefR
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealTP
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

namespace RealT

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : RealT Rc P Dcf Spf Zscf S Ks)

theorem rows_transport {Z Z' : DefSub P.A3.fam3.amb3} (h : Z = Z') (R0 : IndefRows (P.A3.side3 P.P0 P.ψ0 Z))
    (S : IndefData (P.A3.side3 P.P0 P.ψ0 Z')) (hS : HEq R0.toIndefData S) :
    ∃ R0' : IndefRows (P.A3.side3 P.P0 P.ψ0 Z'), R0'.toIndefData = S := by
  subst h
  exact ⟨R0, eq_of_heq hS⟩

theorem rowsHold0 {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (hP : PrimRows3 R.Rl R.F) :
    RowsHold0_3 P := by
  have hR := complex_data_conditions_base_level_of_primitive_links hOk hsep R.charW hP
  refine ⟨R.zs ▸ hR.stable, R.zs ▸ hR.inBlock, ?_, ⟨s, hOk⟩, hsep⟩
  exact rows_transport R.zs (primRows3 hOk hsep R.Rl R.F R.charW hP) P.S0 (by
    rw [primRows3_data]
    exact R.s0)

theorem level_transport {Z : DefSub P.A3.fam3.amb3} (hZ : Z = P.Zs) (S0 : IndefData (P.A3.side3 P.P0 P.ψ0 Z))
    (S1 : IndefData (P.A3.side3 P.Ps P.ψs Z)) (h0 : HEq S0 P.S0) (h1 : HEq S1 P.S1) (h : LevelLink S0 S1) :
    LevelLink P.S0 P.S1 := by
  subst hZ
  cases eq_of_heq h0
  cases eq_of_heq h1
  exact h

theorem cols_transport {Z : DefSub P.A3.fam3.amb3} (hZ : Z = P.Zs) {Dc' : DefCols (P.A3.side3 P.Ps P.ψs Z)} {Sp' : SPer Dc'}
    {N : IndefNum P.A3.fam3.base3} (Sc : IndefColsR (P.A3.side3 P.Ps P.ψs Z) Dc' Sp' N) (hDc : HEq Dc' P.Dc) (hSp : HEq Sp' P.Sp)
    (hS : HEq Sc.toIndefData P.S1) (hC : HEq Sc.col P.C) :
    ∃ (N : IndefNum P.A3.fam3.base3) (Sc : IndefColsR (P.A3.side3 P.Ps P.ψs P.Zs) P.Dc P.Sp N),
      Sc.toIndefData = P.S1 ∧ HEq Sc.col P.C := by
  subst hZ
  cases eq_of_heq hDc
  cases eq_of_heq hSp
  exact ⟨N, Sc, eq_of_heq hS, hC⟩

theorem rowsHold [IsTotallyComplex D.what₂.LL] {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (C CH : ℝ)
    (hP : CovolumeOntoIsometryConditions R.Rl R.F R.sEE (hkCan P.A3) C CH) (hI : PassIn3 R.Rl R.F C CH) (hbu : D.BuRational) :
    RowsHold3 P := by
  let Pk := primitivePackageFullHecke hOk hsep R.Rl R.F R.sEE (hkCan P.A3) C CH R.charW hP hI
  refine ⟨R.rowsHold0 hOk hsep hP.toPrimRows3, ?_, hbu, ?_⟩
  · exact level_transport R.zs _ _ R.s0 R.s1 Pk.core.extra.level
  · have hDc : HEq (Dcf (R.Rl.toCx3 R.F).zs) P.Dc := by
      have h : HEq (Dcf (R.Rl.toCx3 R.F).zs) (Dcf P.Zs) := congr_arg_heq Dcf R.zs
      exact h.trans (heq_of_eq R.dc)
    have hSp : HEq (Spf (R.Rl.toCx3 R.F).zs) P.Sp := by
      have h : HEq (Spf (R.Rl.toCx3 R.F).zs) (Spf P.Zs) := congr_arg_heq Spf R.zs
      exact h.trans R.sp
    exact cols_transport R.zs Pk.core.cols hDc hSp R.s1 R.col

end RealT

end Formalism.IndefR
end
end

