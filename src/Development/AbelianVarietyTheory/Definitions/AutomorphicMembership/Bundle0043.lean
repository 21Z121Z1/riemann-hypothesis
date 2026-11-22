import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0042
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Formalism.LocalToGlobal.ClassRec

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

def coreS {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (J : Formalism.L2.Pj.Core D) :
    Formalism.L2.Pj.Core (setDiv D N h) where
  Q := ⟨J.Q.H, J.Q.l, J.Q.c, J.Q.Dw, J.Q.Xo, J.Q.eO⟩
  U := J.U
  V := J.V
  dict := J.dict
  mu := J.mu
  Kf := J.Kf
  pb := J.pb

inductive GeoCl (Γ : GeoP) : ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop
  | base {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} : Γ D J X → GeoCl Γ D J X
  | step {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
      {J : Formalism.L2.Pj.Core D} {X : DivX D} : GeoCl Γ D J X → GeoCl Γ (setDiv D N h) (coreS N h J) (divTr N h X)

def geoCl (Γ : GeoP) : GeoP := GeoCl Γ

theorem geoCl_of {Γ : GeoP} {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} (h : Γ D J X) : geoCl Γ D J X := GeoCl.base h

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotLamAreShift
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl.OXModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical in

def setLam {D : D7} (X : DivX D) (l : ℕ → D.what₂.FT → (D.what₂.LL →+* ℂ) → ℝ) : DivX D :=
  { X with
    logLam := fun j σ e => if e = D.what₂.embLL then Real.log (D.what₂.lamP D.what₂.mu0 j σ) else l j σ e
    logLam_base := fun _ _ => if_pos rfl }

theorem setLam_off {D : D7} (X : DivX D) (l) (j σ) {e} (h : e ≠ D.what₂.embLL) : (setLam X l).logLam j σ e = l j σ e := if_neg h

theorem isGeoOf_set {D : D7} {Q : GlobalTheory.ShFam.KitClass D} {J c} {X : DivX D} (h : GlobalTheory.ShFam.IsGeoOf Q J c X) (l)
    (t : GlobalTheory.ShFam.Pad.SurfSt) : GlobalTheory.ShFam.IsGeoOf Q J c (t.put (setLam X l)) := by
  obtain ⟨T, hT, Φ, X₀, iM, hiM, e1, rfl, h3, h4⟩ := h
  exact ⟨T, hT, Φ, t.put (setLam X₀ l), iM, hiM, e1, rfl, h3, h4⟩

theorem geoOf_set {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D} {D : D7} {J} {c : ℕ} (hc : 0 < c) {X : DivX D}
    (h : GlobalTheory.ShFam.IsGeoOf (Q D) J c X) (l) : geoOf Q D J (GlobalTheory.ShFam.Pad.surfSt.put (setLam X l)) :=
  ⟨⟨c, hc, isGeoOf_set h l _⟩, rfl⟩

theorem geoOf_surf {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D} {D : D7} {J} {X : DivX D} (h : geoOf Q D J X) :
    Nonempty X.Surf ∧ Nonempty X.SurfFp := by
  have e := h.2
  have e1 : X.Surf = GlobalTheory.ShFam.Pad.Surf := congrArg GlobalTheory.ShFam.Pad.SurfSt.Surf e
  have e2 : X.SurfFp = GlobalTheory.ShFam.Pad.SurfFp := congrArg GlobalTheory.ShFam.Pad.SurfSt.SurfFp e
  rw [e1, e2]
  exact ⟨inferInstance, inferInstance⟩

section Reading

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

open Classical in

def lamOf (_Z : R3.ReadL R F X0 Y) (lab : D.what₂.FT → A3.fam3.base3.Ix) (j : ℕ) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ) : ℝ :=
  if h : j - 1 < D.R.m then
    if D.what₂.isot j σ = ⊥ then 0 else Real.log ((R3.s0Of R F).lam ⟨j - 1, h⟩ A3.A.μ0 (lab σ) (InfinitePlace.mk e))
  else 0

theorem lamAre_set (Z : R3.ReadL R F X0 Y) (lab : D.what₂.FT → A3.fam3.base3.Ix)
    (hl : ∀ σ, (∃ c, OverIx Z σ c) → OverIx Z σ (lab σ)) (X : DivX D) (t : GlobalTheory.ShFam.Pad.SurfSt) :
    LamAre Z (t.put (setLam X (lamOf Z lab))) := by
  refine ⟨lab, hl, fun i σ e he => ?_⟩
  have h : (i : ℕ) + 1 - 1 < D.R.m := i.2
  have e1 : (t.put (setLam X (lamOf Z lab))).logLam ((i : ℕ) + 1) σ e = lamOf Z lab ((i : ℕ) + 1) σ e := setLam_off X _ _ _ he
  rw [e1, lamOf, dif_pos h]
  exact ⟨fun h0 => if_neg h0, fun h0 => if_pos h0⟩

theorem exists_lab (Z : R3.ReadL R F X0 Y) (hne : Nonempty D.what₂.FT → Nonempty A3.fam3.base3.Ix) :
    ∃ lab : D.what₂.FT → A3.fam3.base3.Ix, ∀ σ, (∃ c, OverIx Z σ c) → OverIx Z σ (lab σ) := by
  have : ∀ σ, ∃ c, (∃ c, OverIx Z σ c) → OverIx Z σ c := fun σ => by
    by_cases h : ∃ c, OverIx Z σ c
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨(hne ⟨σ⟩).some, fun h' => (h h').elim⟩
  exact ⟨fun σ => (this σ).choose, fun σ => (this σ).choose_spec⟩

theorem nonempty_ix {Z : R3.ReadL R F X0 Y} {X : DivX D} (h : LamAre Z X) : Nonempty D.what₂.FT → Nonempty A3.fam3.base3.Ix :=
  fun ⟨σ⟩ => ⟨h.choose σ⟩

def LamVia (Z : R3.ReadL R F X0 Y) (cOf : D.what₂.FT → A3.fam3.base3.Ix) : Prop :=
  ∀ (i : Fin D.R.m) (c : A3.fam3.base3.Ix), (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) =
    Submodule.span ℂ ((Z.jW i) '' ((R3.s0Of R F).Wp i c : Set (Fin ((R3.s0Of R F).dW i) → D.what₂.LL)))

theorem overIx_of_via {Z : R3.ReadL R F X0 Y} {cOf} (h : LamVia Z cOf) (σ) : OverIx Z σ (cOf σ) := fun i => by
  rw [← h i]
  exact le_iSup (fun τ : {τ : D.what₂.FT // cOf τ = cOf σ} => D.what₂.isot ((i : ℕ) + 1) τ.1) ⟨σ, rfl⟩

theorem eq_of_overIx {Z : R3.ReadL R F X0 Y} {cOf} (h : LamVia Z cOf) {i : Fin D.R.m}
    (hi : iSupIndep (D.what₂.isot ((i : ℕ) + 1))) {σ c} (h0 : D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥) (hc : OverIx Z σ c) : c = cOf σ := by
  by_contra hne
  have h1 := hc i
  rw [← h i] at h1
  refine h0 ((hi σ).eq_bot_of_le (h1.trans (iSup_le fun τ => ?_)))
  exact le_iSup₂_of_le (f := fun j (_ : j ≠ σ) => D.what₂.isot ((i : ℕ) + 1) j) τ.1 (fun e => hne (τ.2.symm.trans (congrArg cOf e))) le_rfl

theorem logLam_eq {Z : R3.ReadL R F X0 Y} {X : DivX D} (hX : LamAre Z X) {cOf} (h : LamVia Z cOf) {i : Fin D.R.m}
    (hi : iSupIndep (D.what₂.isot ((i : ℕ) + 1))) {σ} (h0 : D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥) {e} (he : e ≠ D.what₂.embLL) :
    X.logLam ((i : ℕ) + 1) σ e = Real.log ((R3.s0Of R F).lam i A3.A.μ0 (cOf σ) (InfinitePlace.mk e)) := by
  obtain ⟨lab, hl, hv⟩ := hX
  rw [(hv i σ e he).1 h0, eq_of_overIx h hi h0 (hl σ ⟨_, overIx_of_via h σ⟩)]

theorem logLam_all {Z : R3.ReadL R F X0 Y} {X : DivX D} (hX : LamAre Z X) (h : R3.Lam3 Z)
    (hi : ∀ i : Fin D.R.m, iSupIndep (D.what₂.isot ((i : ℕ) + 1))) (hv : InfinitePlace.mk D.what₂.embLL = A3.A.v0) :
    ∃ cOf : D.what₂.FT → A3.fam3.base3.Ix, ∀ (i : Fin D.R.m) σ, D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ → ∀ e,
      X.logLam ((i : ℕ) + 1) σ e = Real.log ((R3.s0Of R F).lam i A3.A.μ0 (cOf σ) (InfinitePlace.mk e)) := by
  obtain ⟨cOf, h1, h2, -⟩ := h
  refine ⟨cOf, fun i σ h0 e => ?_⟩
  by_cases he : e = D.what₂.embLL
  · subst he
    have := h2 i A3.A.μ0 σ (Or.inl Y.tup0) h0
    rw [Y.tup0] at this
    rw [X.logLam_base, this, hv]
    rfl
  · exact logLam_eq hX (fun i c => (h1 i c).2) (hi i) h0 he

theorem logLam_conj {Z : R3.ReadL R F X0 Y} {X : DivX D} (hX : LamAre Z X) (h : R3.Lam3 Z)
    (hi : ∀ i : Fin D.R.m, iSupIndep (D.what₂.isot ((i : ℕ) + 1))) (hv : InfinitePlace.mk D.what₂.embLL = A3.A.v0)
    (i : Fin D.R.m) (σ) (h0 : D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥) (e) :
    X.logLam ((i : ℕ) + 1) σ (ComplexEmbedding.conjugate e) = X.logLam ((i : ℕ) + 1) σ e := by
  obtain ⟨cOf, hc⟩ := logLam_all hX h hi hv
  rw [hc i σ h0, hc i σ h0, InfinitePlace.mk_conjugate_eq]

theorem not_lamAre_shift {Z : R3.ReadL R F X0 Y} {X : DivX D} (hX : LamAre Z X) {cOf} (h : LamVia Z cOf) (i : Fin D.R.m)
    (hi : iSupIndep (D.what₂.isot ((i : ℕ) + 1))) (σ : D.what₂.FT) {e} (he : e ≠ D.what₂.embLL) :
    ¬ LamAre Z (setLam X fun j σ e => X.logLam j σ e + 1) := fun hX' => by
  have e1 := setLam_off X (fun j σ e => X.logLam j σ e + 1) ((i : ℕ) + 1) σ he
  by_cases h0 : D.what₂.isot ((i : ℕ) + 1) σ = ⊥
  · have a := (hX.choose_spec.2 i σ e he).2 h0
    have b := (hX'.choose_spec.2 i σ e he).2 h0
    rw [e1, a] at b
    norm_num at b
  · have a := logLam_eq hX h hi h0 he
    have b := logLam_eq hX' h hi h0 he
    rw [e1, a] at b
    norm_num at b

theorem mk_emb (R : RealDat3 D A3 Ks) : InfinitePlace.mk D.what₂.embLL = A3.A.v0 := by
  have h := R.toRealDat.emb0
  rw [← InfinitePlace.mk_embedding A3.A.v0]
  cases hb : twAt D.what₂.embLL A3.A.v0
  · rw [hb] at h
    congr 1
    exact RingHom.ext fun a => (h a).symm
  · rw [hb] at h
    rw [← InfinitePlace.mk_conjugate_eq]
    congr 1
    exact RingHom.ext fun a => (h a).symm

theorem mjAre_set {Z : R3.ReadL R F X0 Y} {X : DivX D} (h : MjAre Z X) (l) (t : GlobalTheory.ShFam.Pad.SurfSt) :
    MjAre Z (t.put (setLam X l)) := by
  obtain ⟨J, hJ⟩ := h
  exact ⟨⟨J.eW⟩, ⟨hJ.1, hJ.2⟩⟩

end Reading

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}

theorem oAt_any (t : RowsT K w Z Wt p0) (h : R3.Lam3 t.r.Z) (X : DivX (w.D Z)) :
    ∃ l, Nonempty (OAt anyGeometry t ((GlobalTheory.ShFam.Pad.SurfSt.of X).put (setLam X l))) := by
  obtain ⟨cOf, h1, -⟩ := h
  exact ⟨_, ⟨trivial, lamAre_set t.r.Z cOf (fun σ _ => overIx_of_via (fun i c => (h1 i c).2) σ) X _⟩⟩

theorem oAt_geoOf (Q) (t : RowsT K w Z Wt p0) (h : R3.Lam3 t.r.Z) {c : ℕ} (hc : 0 < c) (X : DivX (w.st Z).toD7)
    (hX : GlobalTheory.ShFam.IsGeoOf (Q _) t.r.z.core.toCore c X) :
    ∃ l, Nonempty (OAt (geoOf Q) t (GlobalTheory.ShFam.Pad.surfSt.put (setLam X l))) := by
  obtain ⟨cOf, h1, -⟩ := h
  exact ⟨_, ⟨geoOf_set hc hX _, lamAre_set t.r.Z cOf (fun σ _ => overIx_of_via (fun i c => (h1 i c).2) σ) X _⟩⟩

end GlobalTheory.Mem.Top.Bl.OXModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev SExt : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (p0 : BaseLevelRowSide (w.D Z)) (r : RowsT K w Z Wt p0) (col : ColT w Z), SX K B f T w Z Wt p0 r col → Type 1

def SExt.none : SExt := fun _ _ _ _ _ _ _ _ _ _ _ => PUnit

def SXE (E : SExt) : SPosition := fun K B f T w Z Wt p0 r col => Σ a : SX K B f T w Z Wt p0 r col, E K B f T w Z Wt p0 r col a

structure Prm (hL : GlobalTheory.Published.LocalLanglandsGL) : Type 2 where
  R : RPosition
  N : NExt hL
  S : SExt
  Γ : GeoP

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

@[reducible] def Prm.s (p : Prm hL) : Slots := ⟨p.R, NX hL p.N, SXE p.S, OX p.Γ⟩

def WPt.core {p : Prm hL} {K : Ctx} (q : WPt p.s K) : NCore hL q.x.what₂ q.x.n := q.x.nx.1

structure SPin {p : Prm hL} {K : Ctx} (q : WPt p.s K) (S : Formalism.L2.LinkedFamilyData q.O.ex) : Prop where
  host : S.host = q.core.a.host
  cols : S.cols = q.x.col.C
  full : HEq S.full q.x.col.full
  g : HEq S.g q.x.col.g
  theta : (⟨S.provA, S.theta⟩ : Σ a, Formalism.L2.Theta.AllTied (q.w.D q.Z) q.O.ex.th a) = ⟨q.x.th.provA, q.x.th.all⟩
  twE : S.twIn.E = twEOf q.O.ex.xd
  twGood : DQ.GoodAllAt (q.w.D q.Z) q.O.ex.nch S.twIn
  chr : (⟨S.n.cf, S.n.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = ⟨TC.cf q.w.I q.w.l q.Z, q.x.n.tp⟩
  gal : S.n.gal = q.core.a.all.gal
  nn : S.n.n = q.core.a.all.n
  exp : S.n.exp = q.core.a.all.exp
  chiD : S.n.chiD = q.core.a.all.chiD
  twF : S.n.twF = q.core.a.all.twF
  types : HEq S.n.types q.core.a.all.types
  cover : HEq S.n.cover q.core.a.all.cover
  plB : S.n.plB = q.core.a.all.plB
  thetaChr : HEq S.thetaChr q.x.th.chr
  dt : ∀ a, S.chrDt.eDt a = (QuotientGroup.mk a : GlobalTheory.Mem.Col2.DtQ q.B.host q.w.I.SQ)
  pieces : S.what₂.O.pieces.rcf = GlobalTheory.Mem.HD.qb S.host.fr.ι q.w.δ.ray ∧ S.what₂.O.pieces.MDel = GlobalTheory.Mem.HD.qb S.host.fr.ι q.w.δ.M'
  inK : S.inK = q.x.div.inK
  geo : HEq S.geo q.x.div.geo
  tw : ∃ he : q.O.ex.tw = q.w.tw q.Z, TC.StdTw q.w.I q.w.l q.Z q.w.l0 (he ▸ S.tw)

structure KPin {𝒮 : Slots} {K : Ctx} (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex) : Prop where
  std : TC.StdKer q.w.I q.w.l q.Z t
  O : t.O = q.x.ker.O
  ent : HEq t.ent q.x.ker.E
  adapted : t.Adapted
  top : t.TopPinned

abbrev BdRec : GlobalTheory.Fc.BdT := fun _ O _ => Formalism.L2.RecT O.ex

structure RecPin {p : Prm hL} {K : Ctx} (q : WPt p.s K) (R : Formalism.L2.RecT q.O.ex) : Prop where
  s : SPin q R.T.toTiedDataS
  k : KPin q R.T.ker
  crd : ∀ u i hi, R.T.crd u i hi = 1

def ZeU (𝒮 : Slots) : Prop := ∀ (K : Ctx) (q : WPt 𝒮 K), Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

def EntC {w : ColW B f T} {Z : w.Lt} {t : ColT w Z} {Y : DivX (w.D Z)} {Gy : G.LatInst (w.D Z)}
    {ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy} (k : KerT t Y Gy ker) : Prop :=
  ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl k.O Bs Y (w.tw Z)),
    k.E = Formalism.L2.Ker.kerEntC Pl k.O Bs h

def BuiltE (𝒮 : Slots) : CP := fun K _ _ _ w Z c => ∃ b : Built 𝒮 K w Z c, EntC b.ker

def GoodE (𝒮 : Slots) : CP := fun K B f T w Z c => BuiltE 𝒮 K B f T w Z c ∧ GoodO (w.D Z) c.O.nch c.O.xd

def IsBuiltE (𝒮 : Slots) : V4.Slot := positionOf (BuiltE 𝒮)

def IsGoodE (𝒮 : Slots) : V4.Slot := positionOf (GoodE 𝒮)

theorem IsBuiltE.isBuilt {𝒮 : Slots} (K X f T c) (h : IsBuiltE 𝒮 K X f T c) : IsBuilt 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ ⟨b, _⟩ => ⟨b⟩) K X f T c h

theorem IsGoodE.isGood {𝒮 : Slots} (K X f T c) (h : IsGoodE 𝒮 K X f T c) : IsGood 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ ⟨⟨b, _⟩, g⟩ => ⟨⟨b⟩, g⟩) K X f T c h

theorem IsGoodE.isBuiltE {𝒮 : Slots} (K X f T c) (h : IsGoodE 𝒮 K X f T c) : IsBuiltE 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ h => h.1) K X f T c h

def MemberE (𝒮 : Slots) : Prop :=
  BaseCond KPx ∧ FirstG KPx (IsBuiltE 𝒮) ∧ ExportF KPx (IsBuiltE 𝒮) ∧ SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮)

def WitExE (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (β : GlobalTheory.Fc.BPt K), β.Is (IsGoodE 𝒮) → ∃ q : WPt 𝒮 K, q.Is β.D β.O ∧ EntC q.x.ker

structure RecPinE {p : Prm hL} {K : Ctx} (q : WPt p.s K) (R : Formalism.L2.RecT q.O.ex) : Prop extends RecPin q R where
  entC : EntC q.x.ker
  std : GlobalTheory.Svd.StdAt q.w.I q.w.l q.w.l0 q.Z q.O R.T.ker
  rd : GlobalTheory.Pdv.StdRd q.w.I q.w.l q.Z R.T.ker

def LinkR (p : Prm hL) : GlobalTheory.Fc.LkT BdRec := linkOf (𝒮 := p.s) (Bd := BdRec) fun _ q _ R => RecPinE (p := p) q R

def RecExE (p : Prm hL) : Prop := GlobalTheory.Fc.ExB (IsGoodE p.s) (LinkR p)

@[reducible] def prmR (N : NExt hL) (S : SExt) (Γ : GeoP) : Prm hL := ⟨RX, N, S, Γ⟩

end GlobalTheory.Mem.Top.Bl

end
end

