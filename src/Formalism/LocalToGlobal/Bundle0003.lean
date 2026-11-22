import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.LocalToGlobal.FiniteTOf
import Formalism.LocalToGlobal.BaseRankEqOfRealisation
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0036
import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.CarriedPlMap
import Formalism.LocalToGlobal.Divisibility.Bundle0004
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Formalism.LocalToGlobal.InpAtOf

-- bundled from Formalism.LocalToGlobal.TieTwRecOf
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace Formalism.L2.Top4

open Formalism.L2.Top3

section StageB

abbrev SelB (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) (selS : SelS 𝒜 sel) (selP : BaseLevelCompatibleSelection 𝒜 sel) (selDH : SelDH 𝒜 sel) (selC : ColumnCompatibleSelection 𝒜 sel selP) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    Formalism.IndefR.RealTB ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (ZscAt sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i)

variable {𝒜 : FamClass} {sel : Formalism.L2.TSel 𝒜} {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : SelDH 𝒜 sel} {selC : ColumnCompatibleSelection 𝒜 sel selP}

def selKOf (selB : SelB 𝒜 sel selS selP selDH selC) : SelK 𝒜 sel :=
  fun Fm hc x hx h i => { Ks := (selB Fm hc x hx h i).T.Q.c.F }

def selIOf (selB : SelB 𝒜 sel selS selP selDH selC) : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC (selKOf selB) :=
  fun Fm hc x hx h i => (selB Fm hc x hx h i).Q

def OneMapOf (selB : SelB 𝒜 sel selS selP selDH selC) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x)
    (i : Fm.Ix x) : Prop :=
  ∀ j, Formalism.IndefR.FWT.OneMapRowR (selB Fm hc x hx h i).T (selB Fm hc x hx h i).Q.Rl.toRealDat (selB Fm hc x hx h i).κ
    (selB Fm hc x hx h i).v₀ (selB Fm hc x hx h i).O (Formalism.IndefR.phEff (selB Fm hc x hx h i).Q.Rl) j

end StageB

section TwPl

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem tw_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.Tw = S1.Tw := by
  subst h; cases eq_of_heq hS; rfl

theorem twPl_eq (Q : RealT Rc P Dcf Spf Zscf S Ks) : Q.Rl.twPl = P.S0.Tw :=
  tw_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0

theorem tieTwRec_of {Q : RealT Rc P Dcf Spf Zscf S Ks} (Qr : RealRec Q)
    (hs : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → w ∈ L.supp) : TieTwRec L P.S0.Tw := by
  intro y hy
  rw [← twPl_eq Q] at hy
  have h := (Qr.tw_iff (D.plEq.symm y)).1 (by simpa using hy)
  exact ⟨hs _ h, h⟩

end TwPl

end Formalism.L2.Top4

end
end

-- bundled from Formalism.LocalToGlobal.Wire4F
section
noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S

namespace Formalism.L2.Top4Wire2

variable {𝒜 : FamClass} {sel : Formalism.L2.TSel 𝒜} {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : SelDH 𝒜 sel}
  {selC : ColumnCompatibleSelection 𝒜 sel selP} {selK : SelK 𝒜 sel}

theorem wire4F [∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x), IsTotallyComplex (Fm.D x i).what₂.LL]
    (selI : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC selK) (hPA : PrimAll sel selI)
    (OneMapRow : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop)
    (Cabs : ℝ) (hCabs : 1 ≤ Cabs)
    (hTw : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      TieTwRec (Fm.L x i) (selP Fm hc x hx h i).1.S0.Tw)
    (hD0 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      (Fm.D x i).what₂.D0 = ((selP Fm hc x hx h i).1.A3.A.fam.R (selP Fm hc x hx h i).1.A3.A.fam.μ0).dZ ((selP Fm hc x hx h i).1.A3.A.fam.lvl (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0)
        ((selP Fm hc x hx h i).1.Zs.Z (selP Fm hc x hx h i).1.A3.A.fam.μ0))
    (hPt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      RowsHoldDcPt3 (selP Fm hc x hx h i).1)
    (hR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I)
    :
    Wire4 sel selS selP selDH selC selK selI hPA (fun Fm hc x hx h i C CH => DefRowsF selI Fm hc x hx h i C CH)
      OneMapRow Cabs := by
  intro eps Fm hc CH hCsz hDG hRows hOne _hBu hN
  obtain ⟨Ce, x3, hCe⟩ := id hN
  obtain ⟨Cd, x4, hFDG⟩ := hDG
  obtain ⟨C, hC, x1, hr⟩ := hRows
  obtain ⟨x2, ho⟩ := hOne
  refine ⟨max 0 (max (50 * c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct + 10)
      (60 * ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct))),
    max (max x1 x2) (max (max x3 x4)
      (x0F eps Fm.Ct Fm.Cc CH (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)))),
    fun x hx0 hx h i => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
  have hx3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx0
  have hx4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx0
  have hx5 : x0F eps Fm.Ct Fm.Cc CH (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  obtain ⟨ra, hd⟩ := hr x hx h hx1 i
  obtain ⟨prows, hsep⟩ := hPA Fm (d3_a hc) x hx h i
  have hok1 := (selC Fm (d3_a hc) x hx h i).ok1
  have hP : CovolumeOntoIsometryConditions (selI Fm (d3_a hc) x hx h i).Rl (selI Fm (d3_a hc) x hx h i).F (selI Fm (d3_a hc) x hx h i).sEE (hkCan (selP Fm (d3_a hc) x hx h i).1.A3) C CH :=
    { toPrimRows3 := prows, w1 := ra.w1, covol := ra.covol, onto := ra.onto hN, lamLow := ra.lamLow (ho x hx h hx2 i),
      seeIso := ra.seeIso, miStar := ra.miStar, fun0 := ra.fun0 hN }
  have hZs : (pkOf (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs = (selP Fm (d3_a hc) x hx h i).1.Zs := (selI Fm (d3_a hc) x hx h i).zs
  have hS0 : HEq (pkOf (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.toIndefData (selP Fm (d3_a hc) x hx h i).1.S0 := (selI Fm (d3_a hc) x hx h i).s0
  have hS := Fm.sizes x hx i
  have hFD : FactDGam (Fm.D x i) (max Cd 0) := J.factDGam_mono (hFDG x hx4 i) (le_max_left _ _)
  have hDGp := Cons.gamma_size_of_sizeData (selP Fm (d3_a hc) x hx h i).2 (finiteT_of (selC Fm (d3_a hc) x hx h i))
    hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.1 (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 (Fm.L x i).Nc (cloudConstant_nonneg (Fm.L x i))
    (max Cd 0) (le_max_right _ _) hFD
  have eCc : (Fm.L x i).Cc = Fm.Cc := Fm.Cc_eq x i
  have eCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have eCY : (Fm.params x hx i).CYL = Fm.CYL := Fm.params_CYL x hx i
  have hxL : x0F (Fm.L x i).sc.eps (Fm.L x i).Ct (Fm.L x i).Cc CH
      (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz (Fm.L x i).Cc (Fm.params x hx i).CYL (Fm.L x i).Ct)) ≤ (Fm.L x i).sc.x := by
    rw [Fm.L_eps x i, eCt, eCc, eCY, Fm.L_x x i hx]
    exact hx5
  obtain ⟨lam0, Sw, C1, H, dg, hdg, hdvd, hA⟩ := arithClause_rec (Fm.L x i) (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 hS (selDH Fm (d3_a hc) x hx h i).2.1 (selDH Fm (d3_a hc) x hx h i).2.2 (Fm.params x hx i) (Fm.ex x hx i).fdef
    (Fm.ex x hx i).kap_def (selP Fm (d3_a hc) x hx h i).1.A3 (selP Fm (d3_a hc) x hx h i).1.tied.div.grp.card (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 (selP Fm (d3_a hc) x hx h i).1.Ps (selP Fm (d3_a hc) x hx h i).1.ψs (selC Fm (d3_a hc) x hx h i).c.face (selC Fm (d3_a hc) x hx h i).Sp _ C CH Fm.Csz Ce
    (2 + 9 * max Cd 0) (finiteT_of (selC Fm (d3_a hc) x hx h i)) hDGp hC hCsz hxL (pkOf (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass)
  have e0 : c0F Fm.Csz (Fm.L x i).Cc (Fm.params x hx i).CYL (Fm.L x i).Ct = c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct := by
    rw [eCc, eCY, eCt]
  exact ptK_of_real ((sel Fm (d3_a hc)).2 x hx h i) ((RkOf sel selS selP selDH selC selK selI hPA Fm hc).2 x hx h i) rfl
    (selP Fm (d3_a hc) x hx h i).2 ra.kap (hPt Fm (d3_a hc) x hx h i) (hR Fm (d3_a hc) x hx h i)
    (selS Fm (d3_a hc) x hx h i) (selI Fm (d3_a hc) x hx h i) hsep C CH hP ra.pass _ Cabs (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2
    (selDH Fm (d3_a hc) x hx h i).2.1 (selDH Fm (d3_a hc) x hx h i).2.2 lam0 _ _ Fm.Csz Sw C1 (Equiv.refl _) H
    (inpAt_of (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 lam0 _ _ Fm.Csz Sw C1 (Equiv.refl _) H Ce (hCe x hx3 i)
      (by rw [tw_heq hZs hS0]; exact hTw Fm (d3_a hc) x hx h i) (by rw [hZs]; exact hD0 Fm (d3_a hc) x hx h i)
      (lift_exponent_of_least (selP Fm (d3_a hc) x hx h i).1.A3.A hok1.ok2 (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 ((selP Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 (pkOf (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs)
        (pkOf (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.μ (pkOf (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.Tw _ (fun _ _ _ => rfl))
      ⟨dg, hdg, hdvd, hA⟩ (fun NuC I hT hI u => hd hok1 hsep hP ra.pass lam0 _ _ Sw C1 H NuC I hT hI u))
    (Fm.nprimeDef x hx i) (fun u => Fm.h_eq x hx i u)
    (fixedScale_tied (Fm.L x i) (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 (Fm.ex x hx i).kap_def (Fm.ex x hx i).fdef (selP Fm (d3_a hc) x hx h i).1.A3 (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 (Equiv.refl _)
      (Fm.L x i).Nc Fm.Csz (pkOf (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs C CH)
    (le_max_left _ _) (by rw [e0]; exact le_trans (le_max_left _ _) (le_max_right _ _))
    (by rw [e0]; exact le_trans (le_max_right _ _) (le_max_right _ _)) hCabs
    (Formalism.MainNotions.DIV.La_nonneg (Fm.L x i) (Fm.sizes x hx i).2.2.2.2.2.2.1)

end Formalism.L2.Top4Wire2

end
end

