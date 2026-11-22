import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
section
noncomputable section
namespace GlobalTheory.CoefDuty.OPinModel
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.Mem.Col2

def LabFixed (D : D7) : Prop :=
  GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩

theorem labFixed_withLoc {D : D7} (L : LocAll (lay0 D)) : LabFixed (withLoc L) ↔ LabFixed D := Iff.rfl

theorem labFixed_iff {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) : LabFixed D ↔ LabFixed a.nt.D := by
  have e : ∀ D', D' = withLoc a.nt.L → (LabFixed D' ↔ LabFixed a.nt.D) := by
    rintro _ rfl
    exact labFixed_withLoc _
  exact e D a.nt.eq

theorem labFixed_of_typesTrue {D : D7} {P : PiBar D.host} {W : Omg D.host} (h : TypesTrue D.ntypes P W) : LabFixed D :=
  fun k => ⟨(h.teich k).symm, h.ser k⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem lab_of_rows {hL : GlobalTheory.Published.LocalLanglandsGL} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
    (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch} (c : NCore hL t n) : LabFixed c.a.nt.D :=
  (labFixed_iff c.a).1 fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩

theorem isGenSys_gen (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) : Formalism.L2.NT.IsGenSys L.gen := by
  intro d hd
  refine ⟨L.gen_order d hd, ?_⟩
  rintro d' ⟨e, rfl⟩ h
  exact L.gen_norm d e hd (Nat.pos_of_mul_pos_left h)

theorem tame_of_pin {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    {a : NAt hL D cf nch tp} (h : OPin a) (k : Fin 2) (v : a.nt.D.nd.PlG k) :
    @Formalism.L2.NT.TameCoupled _ _ _ _ _ (a.nt.D.nd.plOm.1 (a.nt.D.naut.plGw k v)) _ ⟨a.nt.D.host.g_prime k⟩ (a.nt.A.grp.kv k v)
      (a.nt.D.ntypes.tg k v) (@GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩
        (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)) := by
  rw [← h.gen k]
  exact a.nt.A.grp.tg_tame k v

theorem opin_iff {hL : GlobalTheory.Published.LocalLanglandsGL} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
    (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch} (c : NCore hL t n) :
    OPin c.a ↔ (SumRepresentations.hypO (w.D Z) ∧ TakenAll (w.D Z)) ∧ (∀ i, ClassSum (c.a.all.gal.mt.loc i)) ∧
      ∀ k, c.a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨c.a.nt.D.host.g_prime k⟩
        (@GlobalTheory.Mem.TypePl.labDat (c.a.nt.D.host.g k) ⟨c.a.nt.D.host.g_prime k⟩) :=
  ⟨fun h => ⟨⟨h.large.1, h.large.2.2⟩, h.inner, h.gen⟩,
    fun h => ⟨⟨h.1.1, c.a.split, h.1.2⟩, h.2.1, lab_of_rows t c, h.2.2⟩⟩

example (hL : GlobalTheory.Published.LocalLanglandsGL) : NCondition := NX hL (OExt hL)
end GlobalTheory.CoefDuty.OPinModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyExtAnd
section
noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RealSide.Framed {D : D7} (X : RealSide D) : Prop :=
  ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV

theorem RealSide.space_eq {D : D7} (X : RealSide D) (j : Fin D.R.m) :
    X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j :=
  X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀

section At

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (nch : NChoice D) (xd : ThData D) (first : Prop) {G : Type}
  [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL]
  (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
  (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (S : RatDat D.ntw) (YS : NExpRealS R cG S)

def TwAt (_H : NExpRealH R cG S YS) (cf : CharFrame D) : Type 1 :=
  TwJoin hL D nch xd first R F cG geo S YS cf

variable {hL D nch xd first R F cG geo S YS}

theorem TwAt.Sb_eq {H : NExpRealH R cG S YS} {cf : CharFrame D} (a : TwAt hL D nch xd first R F cG geo S YS H cf) :
    a.X.R.Sb = R.Sb := TwJoin.Sb_eq a

end At

def TwAt.ofBundles {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {nch : NChoice D} {xd : ThData D} {first : Prop}
    (X : RealSide D) (Y : SerSide X (twEOf xd)) (g : GalSide D) (h1 : g.cf = X.R.C) (h2 : g.lam.C = X.R.C) (hF : FieldOk X)
    (cg : CGTrue hL D g.wd) (hb : first → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w))
    (H : NExpRealH X.R X.cG Y.S Y.YS) : TwAt hL D nch xd first X.R X.F X.cG X.geo Y.S Y.YS H X.R.C :=
  TwJoin.mk X rfl HEq.rfl HEq.rfl rfl rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl Y rfl HEq.rfl g h1 h2 rfl hF cg hb

def TwExt (hL : GlobalTheory.Published.LocalLanglandsGL) : NExt hL := fun _ B _ T w Z _ _ t nch _ xd c =>
  TwAt hL (w.st Z).toD7 nch xd (T = TwDat.untw B T.pl) t.r.z.R t.r.z.F t.r.z.cG t.r.z.geo _ c.row.nexp c.row.hecke (TC.cf w.I w.l Z)

def extAnd {hL : GlobalTheory.Published.LocalLanglandsGL} (E E' : NExt hL) : NExt hL := fun K B f T w Z Wt p0 t nch n xd c =>
  E K B f T w Z Wt p0 t nch n xd c × E' K B f T w Z Wt p0 t nch n xd c

section Rows

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)}

def extAndNone (E : NExt hL) (c : NCore hL t n) :
    extAnd E (NExt.none hL) K B f T w Z Wt p0 t nch n xd c ≃ E K B f T w Z Wt p0 t nch n xd c := Equiv.prodPUnit _

def NXAnd.fst {E E' : NExt hL} (y : NX hL (extAnd E E') K B f T w Z Wt p0 t nch n xd) : NX hL E K B f T w Z Wt p0 t nch n xd :=
  ⟨y.1, y.2.1⟩

def NXAnd.snd {E E' : NExt hL} (y : NX hL (extAnd E E') K B f T w Z Wt p0 t nch n xd) : NX hL E' K B f T w Z Wt p0 t nch n xd :=
  ⟨y.1, y.2.2⟩

example {c : NCore hL t n} (a : TwExt hL K B f T w Z Wt p0 t nch n xd c) : a.X.R.Sb = t.r.z.R.Sb := TwAt.Sb_eq a

example {c : NCore hL t n} (a : TwExt hL K B f T w Z Wt p0 t nch n xd c) : a.X.R.C = TC.cf w.I w.l Z := a.C_eq

end Rows

end GlobalTheory.TwInputs

end
end

