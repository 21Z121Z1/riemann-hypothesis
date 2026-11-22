import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0039
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.RowEx
open Formalism.L2.Host (HChar)
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.LiteralAutomorphy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NEa (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (A : AtP) : NExt hL := fun K B f T w Z Wt p0 t nch n xd c =>
  N K B f T w Z Wt p0 t nch n xd c × PLift (A K B f T)

@[reducible] def prmA (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (A : AtP) : Prm hL :=
  prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) A) SExt.none (geoCl anyGeometry)

abbrev GKey (P : Pre) : Type :=
  HeightOneSpectrum (𝓞 P.host.F) × HeightOneSpectrum (𝓞 P.host.E) × (Fin P.R.m → HChar P.host.E)

def gkeyOf {X : Stages} {T : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) : GKey X.B.toPre :=
  (G.pl.v0, G.pl.w G.pl.v0, fun a => G.ch.chiH (a.1 + 1))

def GKeyFin : Prop := ∀ (P : Pre) (c : ℝ), ∃ 𝒦 : Set (GKey P), 𝒦.Finite ∧
  ∀ (X : Stages) (T : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T) (sc : GlobalTheory.ChiGrid.Consts) (G : GridData L sc), X.B.toPre = P → sc.cGap = c →
    ∃ κ ∈ 𝒦, HEq (gkeyOf G) κ

def WeilEx : Prop := BigR fun R sc => ∀ G : GridData R.toLevCh sc, ∃ W : G.Weil, W.Over R ∧ Nonempty (GridChoice W Set.univ)

def NFSq : Prop := ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
  GlobalTheory.SqTop.Rec large₂ → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh D T) (μ₀ : T), L.Is μ₀ → ∀ G : GridData L ⟨1, CF, large₂.sc.b⟩,
    InNF fun _ σ => GlobalTheory.BigTop.Fun.SqIn G μ₀ σ

def TrSq : Prop := OnAgree fun {_ _ _ _ _ _ _} G G' _ _ _ _ μ₀ μ₀' _ => ∀ (M : IntermediateField ℚ ℂ) (σ : M →+* ℂ),
  GlobalTheory.BigTop.Fun.SqIn G μ₀ σ → GlobalTheory.BigTop.Fun.SqIn G' μ₀' σ

def Full {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {sc : GlobalTheory.ChiGrid.Consts}
    (G : GridData R.toLevCh sc) : Prop :=
  ∃ W M ρ ξ cv rm S rp n e c, (⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ : Choice R).Is ∧
    (⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ : Choice R).FieldOK ∧ GlobalTheory.BigTop.Fun.SqIn G A.μ0 D.what₂.embLL

def GridAt (s : Scale) (CF : ℝ) (X : Stages) (f : Fr X.B.toPre) (Ξ : Set (HChar X.B.host.E)) : Prop :=
  ∀ large₂ : SizeData₂ X.toD7, large₂.sc = s → GlobalTheory.SqTop.Rec large₂ → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type)
    (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL]
    (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F → R.C = Fr.at X f → TwistPlacesOffPrimeQZero R.toLevCh →
    (∀ t, ∃ ξ ∈ Ξ, HEq (R.toLevCh.xiH t) ξ) → ∀ G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩,
      ∃ G : GridData R.toLevCh ⟨1, CF, s.b⟩, gkeyOf G = gkeyOf G₀ ∧ Full R G

def ExGrid : Prop := ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ s : Scale, s.eps = ε → x₀ ≤ s.x →
  ∀ (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)), Ξ.Finite → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ (X : Stages) (f' : Fr X.B.toPre) (Ξ' : Set (HChar X.B.host.E)), X.B.toPre = P → HEq f' f → HEq Ξ' Ξ →
      (∀ z ∈ S, z ∈ Set.range X.toD7.what₂.embLL) → GridAt s CF X f' Ξ'

def GridA (CF : ℝ) : AtP := fun K B f T => ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
  (N : NStage B C W) (G : GJStage B C), GridAt K.s CF ⟨B, C, W, V, S, N, G⟩ f (T.set f)

end GlobalTheory.Mem.LiteralAutomorphy

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

variable {D : D7}

abbrev StFams (D : D7) : Type 1 := ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A), StFam S κ

section One

variable {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (F : StFam S κ) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D)

abbrev PolOf {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) : Type := PolDat s Φ (metsOf x Φ) (refMet x Φ)

abbrev padWith {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) (cts : Ats S κ) {jC : JC D} (hj : jC.Pinned) (hA : AdmEx S κ) :
    PadPkg D N j s.Comp jC ngTrue :=
  padTrue s Φ (metsOf x Φ) jC hj hA (locStOf F cts) (globStOf F cts)

structure IsKitWith (k : KitT s L jC) (d : s.Comp → D.what₂.Tau → ℝ) (x : ToroidalCompactificationData s) (P : PolOf x k.Φ) (cts : Ats S κ)
    (hj : jC.Pinned) (hA : AdmEx S κ) : Prop where
  ats : cts.Over jC
  bd : IsBdOf x L k.B
  fl : k.fl = flBetti s k.Φ L
  mb : k.Mb = mbarOf P
  pad : k.pad = padWith F x k.Φ cts hj hA
  deg : d = degFlat s k.Φ (metsOf x k.Φ)

variable {s jC} in

def kitWith (Φ : s.Flag) (key : KeySec s.Xo κ.c) (x : ToroidalCompactificationData s) (B : s.Bd L) (P : PolOf x Φ) (cts : Ats S κ)
    (hj : jC.Pinned) (hA : AdmEx S κ) : KitT s L jC where
  Φ := Φ
  dim_eq := (CmDim.cm_dim D A).2.2 N j S κ s Φ
  key := key
  B := B
  fl := flBetti s Φ L
  Mb := mbarOf P
  pad := padWith F x Φ cts hj hA
  levIn _ := Iff.rfl

variable {s L jC} in

theorem isKitWith_kitWith (Φ : s.Flag) (key : KeySec s.Xo κ.c) {x : ToroidalCompactificationData s} {B : s.Bd L} (hB : IsBdOf x L B)
    (P : PolOf x Φ) {cts : Ats S κ} (hc : cts.Over jC) (hj : jC.Pinned) (hA : AdmEx S κ) :
    IsKitWith F s L jC (kitWith F L Φ key x B P cts hj hA) (degFlat s Φ (metsOf x Φ)) x P cts hj hA :=
  ⟨hc, hB, rfl, rfl, rfl, rfl⟩

namespace IsKitWith

variable {F s L jC} {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} {x : ToroidalCompactificationData s} {P : PolOf x k.Φ} {cts : Ats S κ}
  {hj : jC.Pinned} {hA : AdmEx S κ} (h : IsKitWith F s L jC k d x P cts hj hA)
include h

theorem pad_eq : k.pad = padAt s (locStOf F cts) (globStOf F cts) (admissible_representation_factorisation S κ jC hj hA) (flatSt s k.Φ (metsOf x k.Φ))
    (arIn s k.Φ (metsOf x k.Φ)) := h.pad

theorem isBetti {c : s.Comp} {τ : D.what₂.Tau} (hb : ∃ b, IsBetti s k.Φ L c τ (flatSec s k.Φ c τ) b) :
    IsBetti s k.Φ L c τ (flatSec s k.Φ c τ) (k.fl c τ) := h.fl ▸ isBetti_flBetti hb

open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain in

theorem r_eq (c : s.Comp) {z} (hz : z ∈ DomI D.what₂.Tau j (N - j)) :
    (k.B c).r z = x.r κ.σ₀ (s.toCpt L c z) := h.bd.r_eq c hz

theorem bd_ne_invariant (hb : (genBd s.T.Z : Set (gen s.T.Z : Scheme.{0})).Nonempty) :
    k.B ≠ GlobalTheory.TrueCx.invariantB _ _ (GlobalTheory.TrueCx.first_index_eq_of_unfolded _ s.isUnf S.p_eq) _ := fun e =>
  have ⟨c⟩ := s.compNe
  h.bd.m_ne_zero c hb (by rw [e]; rfl)

end IsKitWith

end One

def IsKitOf (st : StFams D) : KitClass D := fun A N j S κ s L jC k d =>
  ∃ x P cts hj hA, IsKitWith (st A N j S κ) s L jC k d x P cts hj hA

namespace IsKitOf

variable {st : StFams D} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {L : CmList A} {jC : JC D}
  {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} (h : IsKitOf st A N j S κ s L jC k d)
include h

theorem fl_eq : k.fl = flBetti s k.Φ L := have ⟨_, _, _, _, _, h⟩ := h; h.fl

theorem bd_ne_invariant (hb : (genBd s.T.Z : Set (gen s.T.Z : Scheme.{0})).Nonempty) :
    k.B ≠ GlobalTheory.TrueCx.invariantB _ _ (GlobalTheory.TrueCx.first_index_eq_of_unfolded _ s.isUnf S.p_eq) _ :=
  have ⟨_, _, _, _, _, h⟩ := h; h.bd_ne_invariant hb

end IsKitOf

example {A : Amb D} {N j : ℕ} (S : Sig A N j) (L : CmList A) (τ : D.what₂.Tau) :
    expo S.Dw (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ)) =
      fun z => -GlobalTheory.AllWt.exOf S.Dw (GlobalTheory.FlatLine.flatWt S.Dw (L.ψ τ)) 0 (some z) := detEx_eq S L τ

example {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {F : StFam S κ} {s : FinalTheorems S κ} {L : CmList A} {jC : JC D}
    {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} {x : ToroidalCompactificationData s} {P : PolOf x k.Φ} {cts : Ats S κ}
    {hj : jC.Pinned} {hA : AdmEx S κ} (h : IsKitWith F s L jC k d x P cts hj hA) (τ : D.what₂.Tau) :
    ¬ IsKitWith F s L jC k (d + 1) x P cts hj hA := fun h' =>
  have ⟨c⟩ := s.compNe
  by simpa using congrFun₂ (h'.deg.trans h.deg.symm) c τ

example {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {F : StFam S κ} {s : FinalTheorems S κ} {L : CmList A} {jC : JC D}
    {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} {x : ToroidalCompactificationData s} {P : PolOf x k.Φ} {cts : Ats S κ}
    {hj : jC.Pinned} {hA : AdmEx S κ} (h : IsKitWith F s L jC k d x P cts hj hA) (hq : S.Dw.q = 0) :
    d = degFrame s k.Φ (metsOf x k.Φ) := by
  funext c τ
  simp [h.deg, degFlat, hq]

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
section
noncomputable section

section Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.L2 (NExpTied)
open Formalism.L2.Host (embLL0 CharFrame)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.SerMove

variable {D D' : D7}

structure BigHost (D : D7) : Prop where
  host : HostHyp D
  std : ∀ j, FWT.VStd D j
  size : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

structure Frames (X : RealSide D) (X' : RealSide D') : Prop where
  Pg : HEq X.R.Pg X'.R.Pg
  ψ : HEq X.R.ψ X'.R.ψ
  θ : HEq X.R.θ X'.R.θ
  ΛV : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.ΛV j) (X'.R.ΛV j')
  ΛW : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.ΛW j) (X'.R.ΛW j')
  βV : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.βV j) (X'.R.βV j')
  βW : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.βW j) (X'.R.βW j')
  BV : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.BV j) (X'.R.BV j')
  vacP : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.vacP j) (X'.R.vacP j')
  MW : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → SameModel (model X j) (model X' j')
  v₀ : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' →
    SameVec (X.geo.v₀ j (sg0 D X.A3.A)) (X'.geo.v₀ j' (sg0 D' X'.A3.A))

structure Chars (X : RealSide D) (X' : RealSide D') : Prop where
  eta : HEq X.R.eta X'.R.eta
  mu0 : ∀ (j : Fin D.R.m), HEq (X.R.mu0 ((j : ℕ) + 1)) (X'.R.mu0 ((j : ℕ) + 1))
  Cmu0 : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.C.mu0 j) (X'.R.C.mu0 j')
  delAt : ∀ l, HEq (X.R.C.delAt l) (X'.R.C.delAt l)

structure Grps (X : RealSide D) (X' : RealSide D') (ι : D.what₂.LL →+* D'.what₂.LL) (γ : X.Γ ≃* X'.Γ) : Prop where
  eG : ∀ g, HEq (X.R.eG g) (X'.R.eG (γ g))
  cG : HEq X.cG X'.cG
  P0 : ∀ g, g ∈ X.F.P0 ↔ γ g ∈ X'.F.P0
  ψ0 : ∀ (g : X.F.P0) (g' : X'.F.P0), γ g = g' → (X'.F.ψ0 g' : D'.what₂.LL) = ι (X.F.ψ0 g : D.what₂.LL)

def PlCl (X : RealSide D) (X' : RealSide D') : Prop :=
  ∀ i' t' P', P' ∈ X'.R.Q t' → P' ∈ D'.ntw.pD i' → ∃ t, ∃ P ∈ X.R.Q t, HEq P P'

def IoCl (X : RealSide D) (X' : RealSide D') (ι : D.what₂.LL →+* D'.what₂.LL) : Prop :=
  ∃ c0L c0L', IsCoef X c0L ∧ IsCoef X' c0L' ∧ ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' →
    ∀ (u : ∀ τ, lowT (model X j) τ) (u' : ∀ τ, lowT (model X' j') τ), SameVec (M := model X j) (M' := model X' j') (fun τ => u τ) (fun τ => u' τ) →
    ∀ (F : VV D.what₂.LL (FWT.lamV D j)) (F' : VV D'.what₂.LL (FWT.lamV D' j')),
      HEq (MvPolynomial.map ι (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank))
        (F' : Formalism.L2.DIV.Pol D'.what₂.LL D'.what₂.Tau (Vc D' j').rank) →
      HEq (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F)) (X'.R.ioP j' (PiTensorProduct.tprod ℂ u') (c0L' j' F'))

def FormsCl (X : RealSide D) (X' : RealSide D') (ι : D.what₂.LL →+* D'.what₂.LL) (eK : X.core.Q.c.F ≃+* X'.core.Q.c.F)
    (γ : X.Γ ≃* X'.Γ) : Prop :=
  ∃ forms : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → KsIso ι eK γ (X.R.FW j) (X'.R.FW j'),
  ∀ (j : Fin D.R.m) (j' : Fin D'.R.m) (h : (j : ℕ) = j') (x : (X.R.FW j).WK),
    SameMap (evidence X j x) (evidence X' j' ((forms j j' h).φ x))

theorem realMove_of_parts {X : RealSide D} {X' : RealSide D'} {ι : D.what₂.LL →+* D'.what₂.LL} {eK : X.core.Q.c.F ≃+* X'.core.Q.c.F}
    {γ : X.Γ ≃* X'.Γ} (a : Frames X X') (b : Chars X X') (c : Grps X X' ι γ) (q : PlCl X X') (o : IoCl X X' ι)
    (s : FormsCl X X' ι eK γ) : Nonempty (RealMove X X' ι) :=
  let ⟨forms, hr⟩ := s
  ⟨{ eK := eK, γ := γ, forms := forms, read := hr, Q := q, io := o, Pg := a.Pg, ψ := a.ψ, θ := a.θ, ΛV := a.ΛV, ΛW := a.ΛW, βV := a.βV, βW := a.βW, BV := a.BV, vacP := a.vacP, MW := a.MW, v₀ := a.v₀,
     eta := b.eta, mu0 := b.mu0, Cmu0 := b.Cmu0, delAt := b.delAt, eG := c.eG, cG := c.cG, P0 := c.P0, ψ0 := c.ψ0 }⟩

end GlobalTheory.HeightCounting.SerMove

end Abstract

section States

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.SerMove

variable {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
  {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}

abbrev Geo (x : St P) := GlobalTheory.RealGeo.GeoHalf x.m.z.core x.m.z.R.toRealDat fun _ => 1

abbrev datAt (x : St P) (g : Geo x) : Dat (w.st x.o.Z) w.I P.hX T P.Wt := { x.m.z with geo := g }

theorem finite_tup (P : Pre2 K w) : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
  have hs : ({τ | τ = (Formalism.L2.DIV.mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
      Set _).Finite :=
    (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
  exact hs.to_subtype

def sideAt (x : St P) (g : Geo x) (hg : GlobalTheory.RealGeo.InGeo g) (a : BigHost (Dof x)) : GlobalTheory.TwInputs.RealSide (Dof x) :=
  GlobalTheory.TwInputs.RealSide.ofPins g x.m.z.pins x.m.intersectionNumber_baseChange hg (finite_tup P) a.host a.std a.size

structure Link (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0)
    (g : Geo x) (g' : Geo x') : Prop where
  ov : K.Over B'.toPre
  kpx : KPx B' f'
  forced : Forced K B' T'
  start' : Start K B' f' T' w'
  enl : Enl B B'
  fr : HEq f' f
  start : Start K B f T w
  px : HEq w'.px w.px
  sel : HEq w'.I.sel w.I.sel
  J : HEq w'.I.J w.I.J
  δ : HEq w'.δ w.δ
  ext : Ext P.z P'.z
  cp : GlobalTheory.TwInputs.Move.CopyTw (Dof x) (Dof x') ι e
  gal : SameGal (Dof x) (Dof x')
  extN : ExtN (datAt x g) (datAt x' g')

end GlobalTheory.HeightCounting.SerMove

end States

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
section
noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

structure PrM : Prop where
  m1 : GlobalTheory.Published.HarishChandraAnalyticity
  m2 : GlobalTheory.Published.DiscreteSeriesClassification
  m3 : GlobalTheory.Published.CuspRapidDecay
  m4 : GlobalTheory.Published.HarishChandraFinite
  m5 : GlobalTheory.Published.CuspTraceClass
  m6 : GlobalTheory.Published.DixmierMalliavinFactorisation
  m7 : GlobalTheory.Published.FlathFactorisation
  m8 : GlobalTheory.Published.PseudoCoefficientUpq
  m9 : GlobalTheory.Published.HarishChandraCharacters
  m10 : GlobalTheory.Published.LanglandsClassification
  m11 : GlobalTheory.Published.LabesseWaldspurger
  m12 : GlobalTheory.Published.ZelevinskyPolynomialRing
  m13 : GlobalTheory.Published.GeometricLemma
  m14 : GlobalTheory.Published.GreenCuspidal

def Mult0 : Prop := Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
  (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), K.Over B.toPre → GrpTrue Z.N f →
    (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.Ok3 1 → z.R.toRealDat.ExAt → GlobalTheory.CuspMult.MultEq z.R.toRealDat

def MultL : Prop := StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo →
    GlobalTheory.CuspMult.MultEq z.R.toRealDat

def RowRatW : Prop := StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt →
    GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) →
    Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)

theorem hypH_of (c : GlobalTheory.Published.DiscreteSeriesCover) (h1 : GlobalTheory.PrimIn.Hypotheses3) (h2 : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm)
    (h3 : GlobalTheory.Published.HeckeLPartialContinuation) (m : MultL) (r : RowRatW) : HypH :=
  ⟨c, h1, h2, h3, m,
    (StepW.and ((StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans m) r).trans
      (StepW.of_all fun _ _ _ _ _ _ _ G Z hX Wt z a b k c d e g u v => ⟨G.1 Z hX Wt z a b c d, G.2 Z hX Wt z a b k c d e g u v⟩)⟩

end GlobalTheory.Mem.LiteralAutomorphy

end
end

