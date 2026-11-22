import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0618
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChtTrueYEta
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

namespace Cht

open FamPf

theorem exists_fam : FamSt := by
  intro D A N j S κ p ct Z C y K w hw
  have hE : ExtendSt := extendSt
  have hF : FlagBaseSt := FlagBase.flagBase
  have hM : FrameMoveSt := frameMove
  have hC : CocycleSt := Cocycle.cocycle
  have hT : TowerSt := Tower.tower
  have hN : N2 ct.Y := (S.sys.clauses p ct.W ct.hp ct.hW).1
  have h1 : 1 ≤ S.Dw.p + S.Dw.q := by
    rw [S.rank_eq]; exact one_le_two.trans S.two_le
  obtain ⟨P, hP1, hP⟩ := hT _ _ _ _ _ _ ct.Y ct.hp ct.hW h1 C Z.i y.P
  have hyg : y.gen ≫ Z.π = (P Z.i).x0 := by
    have e : (P Z.i).x0 = spMap (intO ↥C.S).subtype ≫ (P Z.i).yt := (P Z.i).ext.symm
    rw [e, hP1, ← y.z_π, PtAt.gen, Category.assoc]
  have hr : Set.range w ⊆ Z.opn := by
    refine range_of_base K.subtype _ ?_
    rw [hw]
    rintro _ ⟨s, rfl⟩
    refine ⟨(P Z.i).y s, ?_⟩
    exact (congrArg (fun f => f s) hyg).symm
  obtain ⟨u₁, hu₁⟩ := ((hF _ _ _ _ _ _ ct.Y _ Z ↥K w).1 hr)
  have hu : Z.FlagAt y.gen (u₁.bc K.subtype) := by
    rw [← hw]
    exact (hF _ _ _ _ _ _ ct.Y _ Z ↥K w).2 ↥C.S K.subtype _ hu₁
  obtain ⟨fam, hfam, hall⟩ := fam_core hE hM hC hN P hP Z y hP1.symm _ hu
  refine ⟨fam, hfam, ?_⟩
  have hi : ct.YY.i = idx0 ct := ct.isYY.1.trans (ct.B.lvl none)
  have hd : ct.YY.i.l.Dvd Z.i.l := hi ▸ Z.dvd
  have hc : ct.YY.i.c.F ≤ Z.i.c.F := hi ▸ Z.le
  obtain ⟨mu, ht⟩ := exists_isTrans hN ct.YY.i Z.i hd hc
  obtain ⟨hg, hf⟩ := hall ct.YY _ mu hd ht
  exact rat_core hE hF hM K Z ct.YY hc ht (P Z.i) (P ct.YY.i) (hP _ _ _ _ hd ht) w (by rw [hw]; exact hyg) u₁ hu₁ _ hg hf

end Cht

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem Cht.goodIff (ct : At S κ p) : Cht.GoodIff ct := Cht.goodIff_of Cht.GoodOfZero.abOfTriv Cht.trivOfAbSt ct

theorem Cht.genEx (ct : At S κ p) : Cht.GenEx ct :=
  Cht.genEx_of GlobalTheory.SpecialStalk.stalkSt Cht.CompletedClosure.fieldSt Cht.extendSt Cht.exists_fam ct

def chtTrue (ct : At S κ p) : ChtSt ct := Cht.chtOf ct (Cht.goodIff ct) (Cht.genEx ct)

theorem chtTrue_genK (ct : At S κ p) {Z : ct.Mdl} (η : ct.Gen Z) : Cht.IsGenK η ((chtTrue ct).genK η) :=
  (Cht.genEx ct Z η).choose_spec

theorem chtTrue_yEta (ct : At S κ p) {Z : ct.Mdl} (η : ct.Gen Z) :
    (chtTrue ct).yEta η = (chtTrue ct).ptK Z ((chtTrue ct).genK η) := rfl

theorem Cht.nonempty_dvp (ct : At S κ p) {Z : ct.Mdl} (η : ct.Gen Z) : ∃ y : Cht.DVP ct, Nonempty (Cht.Ext y) :=
  ⟨(chtTrue ct).genK η, Cht.nonempty_ext _⟩

example {ct : At S κ p} {y : Cht.DVP ct} (e : Cht.Ext y) (h : e.π = p) : Cht.vpi e = 1 := by
  have h1 : ((e.π : ↥e.L) : ↥y.C.S) = p := by rw [h]; simp
  have hp : (1 : ℝ) < p := by exact_mod_cast ct.hp.one_lt
  rw [Cht.vpi, h1, y.C.norm_p, Real.logb_inv, neg_neg, Real.logb_self_eq_one hp]

example {ct : At S κ p} {y : Cht.DVP ct} {e : Cht.Ext y} {Z : ct.Mdl} (χ : Cht.Chart Z y e) (F : ct.Sh Z)
    (f : ct.Sec F) : Cht.ordGe χ F f 0 :=
  fun _ _ _ _ _ _ _ n hn => absurd hn (not_lt.2 n.cast_nonneg)

example {ct : At S κ p} {y : Cht.DVP ct} {e : Cht.Ext y} {Z : ct.Mdl} (χ : Cht.Chart Z y e) (h : Cht.chAt χ)
    (h' : Cht.chAbExact χ) : 0 < Cht.dvRho y := by
  rw [Cht.dvRho_pos_iff (Cht.goodIff ct) Z, ← Cht.chAt_imgM χ h]
  intro hab
  refine (h' (closedPoint e.R)).1 hab ?_
  change PowerSeries.X ∈ maximalIdeal e.R
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simp

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PositionMv (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) (x : Wit 𝒮 K w Z O)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h →
    ∀ (col : ColumnDataSplitPrimes K w (Db.setDivZ Z N h)) (n : NchT w (Db.setDivZ Z N h) x.Wt O'.nch),
    ∃ t : RowsT K w (Db.setDivZ Z N h) x.Wt O'.p0, ObjT O' t ∧
      Nonempty (𝒮.Rx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t) ∧
      Nonempty (𝒮.Nx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t O'.nch n O'.xd) ∧
      Nonempty (𝒮.Sx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t col.toColT) ∧
      Nonempty (𝒮.Ox K B f T w (Db.setDivZ Z N h) x.Wt O' t)

def WitMv (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) (x : Wit 𝒮 K w Z O)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), EntC x.ker →
    ∃ x' : Wit 𝒮 K w (Db.setDivZ Z N h) (O.tr N h), EntC x'.ker

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

abbrev Dof (x : St P) : D7 := (w.st x.o.Z).toD7

abbrev cfOf (x : St P) : CharFrame (Dof x) := TC.cf w.I w.l x.o.Z

open Classical in

def QOf (P : Pre2 K w) (v : B.places.Pl) : Finset (HeightOneSpectrum (𝓞 B.host.E)) := if v ∈ P.Wt then T.Q v else ∅

structure LA (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 where
  a : StA hL (Dof x) (cfOf x) (repOf x.r.Y)
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (Dof x).host.E)) → PlE (Dof x).host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  sel : Set.range Pq = Set.range w.I.sel

structure LI (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LA hL x where
  mt : InMt x.r.Y (cfOf x) w.I.xi (QOf P)
  rat : InRat x.r.Y x.m.z.cG
  cusp : RowCusp (Dof x) a.A.row

structure SettingsLevel (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : SettingsFormsState a rat Pq

structure SeriesLevel (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : SeriesState x.m.z.geo a rat mt.ad.PV Pq

structure StrictHenselianAcyclic (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : ModuliPointsState x.m.z.geo a rat mt.ad.PV Pq

structure LC (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends StrictHenselianAcyclic hL x where
  c : StC mt b T.k T.psi

abbrev AllSt (p : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop) : Prop :=
  StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), p K B f T w P x

variable (hL)

def NEb : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NE hL K B f T w Z Wt p0 t nch n xd c × PLift (BkLaw (w.D Z))

def SA : Prop := AllSt fun _ _ _ _ _ P x => IsEmpty x.o.N.nd.Loc →
  ∃ x' : St P, Nonempty (LA hL x') ∧ GlobalTheory.TwistChoice.SameGalois (Dof x).nd (Dof x').nd

def SMt : Prop := AllSt fun _ _ _ _ w P x => Nonempty (InMt x.r.Y (cfOf x) w.I.xi (QOf P))

def SRat : Prop := AllSt fun _ _ _ _ _ _ x => LA hL x → Nonempty (InRat x.r.Y x.m.z.cG)

def SCusp : Prop := AllSt fun _ _ _ _ _ _ x => ∀ l : LA hL x, RowCusp (Dof x) l.a.A.row

def SettingsFormsExist : Prop := AllSt fun _ _ _ _ _ P x => LI hL x → ∃ x' : St P, Nonempty (SettingsLevel hL x')

def SeriesExist : Prop := AllSt fun _ _ _ _ _ P x => SettingsLevel hL x → ∃ x' : St P, Nonempty (SeriesLevel hL x')

def SB2 : Prop := AllSt fun _ _ _ _ _ P x => SeriesLevel hL x → ∃ x' : St P, Nonempty (StrictHenselianAcyclic hL x')

def SC : Prop := AllSt fun _ _ _ T _ _ x => ∀ l : StrictHenselianAcyclic hL x, Nonempty (StC l.mt l.b T.k T.psi)

def SEta : Prop := AllSt fun _ _ _ _ _ P x => ∀ l : LC hL x,
  GlobalTheory.CoefDuty.BuiltEx l.a.A l.mt.M l.c.ch l.c.tp.tup → GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
    GlobalTheory.CoefDuty.Large D' ∧ ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v

structure Kept {D D' : D7} (c : NChoice D) (c' : NChoice D') : Prop where
  gal : GlobalTheory.TwistChoice.SameGalois D.nd D'.nd
  set : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients D.ntw D'.ntw
  forms : GlobalTheory.TwistChoice.SameForms D.nexp D'.nexp
  br : HEq D.ntwbr D'.ntwbr
  twI : HEq c.twI c'.twI
  sd : HEq c.sd c'.sd
  Q : HEq c.Q c'.Q
  k : HEq c.k' c'.k'
  psi : HEq c.psi' c'.psi'

def SFin : Prop := AllSt fun K _ _ _ w P x => ∀ (l : LC hL x) (S : SExt) (Γ : GeoP),
  ∃ (Z : w.Lt) (v : Lv3 (prmR (NEb hL) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch

def NEg : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEb hL K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)

def SecondN : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (prmR (NEb hL) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR (NEg hL) S Γ).s K B f T w

end GlobalTheory.HeightCounting.Up

end
end

