import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0614
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0040
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsFiniteQCHomModOfExact
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackPtC
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0042
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FibLatPreSubSpanSubLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure PrN : Prop where
  what₂ : GlobalTheory.NRows.Hypotheses₂
  decay : GlobalTheory.Published.CuspRapidDecay
  hc : GlobalTheory.Published.HarishChandraFinite
  greenC : GlobalTheory.Published.GreenCuspidal
  green : GlobalTheory.GLq.Green
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  dz : GlobalTheory.Published.DepthZeroInertia
  ray : GlobalTheory.Published.RayClassFieldSt
  rayF : GlobalTheory.NT.RayField
  rayA : GlobalTheory.Published.RayCharacterArtin
  bc : GlobalTheory.Published.BaseChangeDefiniteUnitary
  ds : GlobalTheory.Published.DiscreteSpectrumGL
  gen : GlobalTheory.Published.GenericUnitaryDualGL
  std : GlobalTheory.Published.StandardCosocleGL
  cheb : GlobalTheory.TwSys.Cheb
  howe : GlobalTheory.Hk3.HoweUnram

structure SerN : Prop where
  rat : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat
  int : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt
  hkInt : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt
  hkTr : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform
  hkRead : GlobalTheory.HeckeSupSt.HeckeReadTie
  ratio : GlobalTheory.ToricRational.RatioConj

abbrev LayP (hL : GlobalTheory.Published.LocalLanglandsGL) : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch), NCore hL t n → Prop

def AtMem (hL : GlobalTheory.Published.LocalLanglandsGL) (p : LayP hL) : Prop :=
  EvLgG fun K B f T => KPx B f → ∀ w Z Wt p0 t nch n xd c, Nonempty (NE hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) →
    ColPin w → p K B f T w Z Wt p0 t nch n c

def CenUsed (D : D7) (M : MtFam D) : Prop :=
  ∀ (μ : D.what₂.Tup), Formalism.IndefR.RecTie.Used0 D μ → ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ L : G0g D.nd → GAf D.host.E D.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧ ∀ (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (x : D.what₂.Mt μ j),
      (M μ j h1 h2).real (D.ntypes.cenMt μ j z x) =
        GlobalTheory.PendOf.actSum D L (z : MonoidAlgebra ℂ (G0g D.nd)) ((M μ j h1 h2).real x)

theorem cenUsed_of_cenReal {D : D7} {M : MtFam D} (h : GlobalTheory.PendOf.CenReal D M) : CenUsed D M := fun μ _ => h μ

def SumUsed (D : D7) (M : MtFam D) : Prop :=
  ∀ (μ : D.what₂.Tup), Formalism.IndefR.RecTie.Used0 D μ → ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), GlobalTheory.CoefDuty.ClassSum (M μ j h1 h2)

def RootsLL (D : D7) : Prop := ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ D.what₂.restRowsFiniteGroupCard

structure PinAt {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) (P : GlobalTheory.NPin.Pin hL D) : Prop where
  cf_eq : P.cf = cf
  C_eq : P.C = nch
  tp_eq : HEq P.tp tp
  rep_eq : HEq P.rep a.nt.rep
  M_eq : P.M = a.all.gal.mt
  lab : GlobalTheory.PendOf.LabAll D P.T
  green : GlobalTheory.PendOf.GreenLab P.ty.grp
  chiT : ChiTOk D P.cf

def ParSt (hL : GlobalTheory.Published.LocalLanglandsGL) : Prop :=
  AllSt fun _ _ _ _ _ _ x => ∀ l : LA hL x, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (Dof x) l.a.A.row

def SXd (hL : GlobalTheory.Published.LocalLanglandsGL) : Prop :=
  AllSt fun _ _ _ _ _ _ x => SeriesLevel hL x → ∃ xd : ThData (Dof x), XdAll xd

def PtSt (hL : GlobalTheory.Published.LocalLanglandsGL) : Prop :=
  AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
    (SumRepresentations.hypO D' → SumRepresentations.Conclusion41 D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D' ∧ SumRepresentations.Conclusion42 D' ∧ SumRepresentations.ConclusionZ D') ∧ D'.nd.EigSpan ∧ Rows.IsotInternal D'.what₂

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHTLatOf
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.LocM

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def IsHTLatOf {ct : At S κ p} (hm : HTmSt ct (shfTrue ct) (htpTrue ct)) (B : ct.Mdl) (L : Lat B) : Prop :=
  (∃ n, 3 ≤ n ∧ hm.IsHTBlowup B (ct.Xn n)) ∧ ∀ y : ct.Pt B,
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing
    hm.omPat y = (GlobalTheory.HTSheaf.fibLat (ct.isGrpPullback_htToMdl y) L.N).toAddSubgroup

def stagesOf (ct : At S κ p) (hm : HTmSt ct (shfTrue ct) (htpTrue ct)) (jt : JetSt ct (uniTrue ct) (thgTrue ct)) : Stages ct where
  lw := SharedLaws.lawSt _ _ _ _ _ _ _ ct
  mo := motTrue ct
  sh := shfTrue ct
  fg := flgOf ct (IsHTLatOf hm)
  fr := frmTrue ct
  ch := chtTrue ct
  tr := torTrue ct
  fj := fjTrue ct
  un := uniTrue ct
  tb := thbTrue ct
  ky := keyTrue ct
  bd := bdyTrue ct
  tg := thgTrue ct
  jt := jt
  ev := evlTrue ct
  hq := htpTrue ct
  hm := hm
  cd := crdTrue ct
  cr := crhOf ct (IsHTLatOf hm) (classFam (IsHTLatOf hm))

abbrev HTmFam (D : D7) : Type 1 := ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p),
  HTmSt ct (shfTrue ct) (htpTrue ct)

abbrev JetFam (D : D7) : Type 1 := ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p),
  JetSt ct (uniTrue ct) (thgTrue ct)

def stOf (hm : HTmFam D) (jt : JetFam D)  (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) : StFam S κ :=
  ⟨fun {p} ct => stagesOf ct (hm A N j S κ p ct) (jt A N j S κ p ct), alpOf D, fun _ => rfl⟩

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistGrid
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

def GridPin (D : D7) {I : Type} (Lc : Formalism.IndefR.Links.LevCh D I) (CF b : ℝ) : Prop :=
  ∃ G : GlobalTheory.ChiGrid.GridData Lc ⟨1, CF, b⟩,
    GlobalTheory.BigTop.Fun.FieldHas G (embLL0 D) ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw (GlobalTheory.BigTop.Fun.lamOf G)

def GridSt {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) : Prop :=
  GridPin (Dof x) x.m.z.R.toRealDat.toLevCh K.C.P.CF K.s.b

variable (hL : GlobalTheory.Published.LocalLanglandsGL)

def NEc : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEb hL K B f T w Z Wt p0 t nch n xd c ×
  PLift (GridPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh K.C.P.CF K.s.b)

def NEcg : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEc hL K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)

def SettingsFormsExistGrid : Prop := AllSt fun _ _ _ _ _ P x => LI hL x → ∃ x' : St P, Nonempty (SettingsLevel hL x') ∧ GridSt x'

def SeriesExistGrid : Prop := AllSt fun _ _ _ _ _ P x => SettingsLevel hL x → ∃ x' : St P, Nonempty (SeriesLevel hL x') ∧ (GridSt x → GridSt x')

def ModuliPointsExistGrid : Prop := AllSt fun _ _ _ _ _ P x => SeriesLevel hL x → ∃ x' : St P, Nonempty (StrictHenselianAcyclic hL x') ∧ (GridSt x → GridSt x')

def SFing : Prop := AllSt fun K _ _ _ w P x => ∀ (l : LC hL x) (S : SExt) (Γ : GeoP), GridSt x →
  ∃ (Z : w.Lt) (v : Lv3 (prmR (NEc hL) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch

def SecondNg : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (prmR (NEc hL) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR (NEcg hL) S Γ).s K B f T w

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

def ListPin (D : D7) {I : Type} (Lc : Formalism.IndefR.Links.LevCh D I) (CF b : ℝ) : Prop :=
  ∃ G : GlobalTheory.ChiGrid.GridData Lc ⟨1, CF, b⟩,
    GlobalTheory.BigTop.Fun.FieldHas G (embLL0 D) ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw (GlobalTheory.BigTop.Fun.lamOf G)

def ListSt (cDep : ℝ) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) : Prop :=
  ListPin (Dof x) x.m.z.R.toRealDat.toLevCh cDep K.s.b

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ)

def NEl : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEb hL K B f T w Z Wt p0 t nch n xd c ×
  PLift (ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep K.s.b)

def NElg : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEl hL cDep K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)

def SettingsFormsExistList : Prop := AllSt fun _ _ _ _ _ P x => LI hL x → ∃ x' : St P, Nonempty (SettingsLevel hL x') ∧ ListSt cDep x'

def SeriesExistList : Prop := AllSt fun _ _ _ _ _ P x => SettingsLevel hL x → ∃ x' : St P, Nonempty (SeriesLevel hL x') ∧ (ListSt cDep x → ListSt cDep x')

def ModuliPointsExistList : Prop := AllSt fun _ _ _ _ _ P x => SeriesLevel hL x → ∃ x' : St P, Nonempty (StrictHenselianAcyclic hL x') ∧ (ListSt cDep x → ListSt cDep x')

def SFinl : Prop := AllSt fun K _ _ _ w P x => ∀ (l : LC hL x) (S : SExt) (Γ : GeoP), ListSt cDep x →
  ∃ (Z : w.Lt) (v : Lv3 (prmR (NEl hL cDep) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch

def SecondNl : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (prmR (NEl hL cDep) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR (NElg hL cDep) S Γ).s K B f T w

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThirdLevelOfGoodTwists
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem kept_refl {D : D7} (c : NChoice D) : Kept c c :=
  ⟨by constructor <;> rfl, by constructor <;> rfl, by constructor <;> rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem kept_withLoc {D : D7} (L : LocAll (lay0 D)) (c : NChoice D) : Kept c (chL L c) :=
  ⟨by constructor <;> rfl, by constructor <;> rfl, by constructor <;> rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

def levelThreeIndependentOfChoices {N : NExt hL} {S S' : SExt} {Γ Γ' : GeoP} {Z : w.Lt} (v : Lv3 (prmR N S Γ).s K w Z) : Lv3 (prmR N S' Γ').s K w Z :=
  { g := v.g, coh := v.coh, Wt := v.Wt, p0 := v.p0, what₂ := v.what₂, rx := v.rx, nch := v.nch, n := v.n, xd := v.xd, chiT := v.chiT,
    nx := v.nx }

theorem third_level_of_good_twists {S : SExt} {Γ : GeoP} (h : Has3 (prmR (NEg hL) S Γ).s K B f T w) : Has3 (prmR (NEb hL) S Γ).s K B f T w :=
  let ⟨Z, ⟨v⟩⟩ := h
  ⟨Z, ⟨⟨⟨v.g, v.coh, v.Wt, v.p0, v.what₂, v.rx⟩, v.nch, v.n, v.xd, v.chiT, ⟨v.nx.1, v.nx.2.1⟩⟩⟩⟩

theorem qOf_off (v : B.places.Pl) (h : v ∉ P.Wt) : QOf P v = ∅ := if_neg h

theorem qOf_on (v : B.places.Pl) (h : v ∈ P.Wt) : QOf P v = T.Q v := if_pos h

theorem qOf_eq (v : B.places.Pl) : QOf P v = T.Q v := by
  by_cases h : v ∈ P.Wt
  · exact qOf_on v h
  · rw [qOf_off v h]
    refine (Finset.eq_empty_of_forall_notMem fun u hu => ?_).symm
    have h1 := ((T.psi_is v).ram u).1 (by rw [P.supp v h]; exact fun _ _ => rfl)
    exact h1 hu

theorem mem_of_twisted (x : St P) (v : B.places.Pl) (h : TwistedAt (Dof x) v) : v ∈ P.Wt := by
  by_contra hv
  exact h (P.q.mu.off v hv)

theorem del_mul_ne_one {p : ℕ} (hp : p.Prime) (hS : p ∈ offSet B.toPre) {δ : HChar B.host.E} (hδ : IsDelta (H := B.host) p δ)
    (v : B.places.Pl) : δ * T.psi v ≠ 1 := by
  intro h
  obtain ⟨Q, hQ, hpQ⟩ : ∃ Q : Ideal (𝓞 B.host.E), Q.IsMaximal ∧ ((p : ℕ) : 𝓞 B.host.E) ∈ Q := by
    have hne : Ideal.span {((p : ℕ) : 𝓞 B.host.E)} ≠ ⊤ := by
      intro ht
      have := congrArg Ideal.absNorm ht
      rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at this
      have h2 : Algebra.norm ℤ ((p : ℕ) : 𝓞 B.host.E) = (p : ℤ) ^ Module.finrank ℤ (𝓞 B.host.E) := by
        rw [← map_natCast (algebraMap ℤ (𝓞 B.host.E)), Algebra.norm_algebraMap]
      rw [h2, Int.natAbs_pow, Int.natAbs_natCast] at this
      rcases Nat.pow_eq_one.1 this with h3 | h3
      · exact hp.one_lt.ne' h3
      · exact Module.finrank_pos.ne' h3
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    exact ⟨Q, hQ, hle (Ideal.subset_span rfl)⟩
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hpQ))
  let u : HeightOneSpectrum (𝓞 B.host.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hu : OverP B.host p u := hpQ
  have hψ : (T.psi v).UnrAt u := by
    by_contra hn
    obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 u hn
    have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 B.host.E) ∈ u.asIdeal := Ideal.absNorm_mem _
    by_cases e : Ideal.absNorm u.asIdeal = p
    · exact h2 (e ▸ hS)
    · obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 B.host.E) (p : 𝓞 B.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes h1 hp).2 e)
      exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ hpQ)))
  have h15 := (hδ.ine u hu 1).1 fun x hx => by
    have e := congrArg (fun χ : HChar B.host.E => χ.loc u x) h
    simp only [HChar.loc_mul, hψ x hx, mul_one] at e
    rw [pow_one, e]
    rfl
  omega

theorem twisted_iff (x : St P) (v : B.places.Pl) : TwistedAt (Dof x) v ↔ v ∈ P.Wt := by
  refine ⟨mem_of_twisted x v, fun hv h => ?_⟩
  have h1 : P.q.W₀.muTw v = w.C.mu0 := (P.q.mu.on v hv).symm.trans h
  have h2 := P.q.mu.tw v
  rw [h1] at h2
  have h3 : T.xiTw f v = 1 := h2.symm.trans w.ok.trueColumnChoices_heckeChar_reference_eq_one
  unfold TwDat.xiTw at h3
  split_ifs at h3
  · exact del_mul_ne_one B.host.pde'_prime (by simp [offSet]) f.isDel' v h3
  · exact del_mul_ne_one B.host.pde_prime (by simp [offSet]) f.isDel v h3

theorem eta_zero {x : St P} (l : LA hL x) (j : ℕ) (v : B.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ B.R.m) : x.o.η j v = 0 := by
  have h := x.o.N.etaJ_tie j v h1 h2
  have hE : IsEmpty x.o.N.nd.Loc := l.a.A.bare
  rw [Finset.eq_empty_of_isEmpty (x.o.N.nd.locs j v), Finset.sum_empty] at h
  exact h

theorem chain (h0 : StepW Start HasBare) (hA : SA hL) (hM : SMt) (hR : SRat hL) (hC : SCusp hL) (b0 : SettingsFormsExist hL) (b1 : SeriesExist hL)
    (b2 : SB2 hL) (hc : SC hL) (hF : SFin hL) (S : SExt) (Γ : GeoP) : StepW Start (Has3 (prmR (NEb hL) S Γ).s) := by
  refine (h0.and (StepW.and hA (StepW.and hM (StepW.and hR (StepW.and hC (StepW.and b0 (StepW.and b1 (StepW.and b2
    (StepW.and hc hF))))))))).trans (StepW.of_all ?_)
  rintro K B f T w - - ⟨⟨P, x, hx, -⟩, hA, hM, hR, hC, b0, b1, b2, hc, hF⟩
  obtain ⟨x1, ⟨a⟩, -⟩ := hA P x hx
  obtain ⟨m⟩ := hM P x1
  obtain ⟨r⟩ := hR P x1 a
  obtain ⟨x2, ⟨l0⟩⟩ := b0 P x1 { toLA := a, mt := m, rat := r, cusp := hC P x1 a }
  obtain ⟨x3, ⟨l1⟩⟩ := b1 P x2 l0
  obtain ⟨x4, ⟨l2⟩⟩ := b2 P x3 l1
  obtain ⟨c⟩ := hc P x4 l2
  obtain ⟨Z, v, -⟩ := hF P x4 { toStrictHenselianAcyclic := l2, c := c } S Γ
  exact ⟨Z, ⟨v⟩⟩

end GlobalTheory.HeightCounting.Up.Model

end
end

