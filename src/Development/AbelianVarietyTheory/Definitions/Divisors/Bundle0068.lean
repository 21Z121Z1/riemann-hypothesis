import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ArchAtEmptyOfRhoZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.RefSum

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ} [Fact p.Prime]

def FacBetween (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
    (A : EReal) ≤ nuFac p y f k ∧ (y.IsAlg → nuFac p y f k ≤ (B : EReal))

def NuBetween (la : PointsOfFlagModel.abelian₂ p c) (cx : Lt1 Dw → ℕ) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
    (A : EReal) ≤ nuP p y cx ∧ (y.IsAlg → nuP p y cx ≤ (B : EReal))

variable (c p) in

def OscLe (cx : Lt1 Dw → ℕ) (b : ℝ) : Prop :=
  ∀ la : PointsOfFlagModel.abelian₂ p c, ∃ A : ℕ, NuBetween Xo la cx A (A + b)

variable (Dw) in

def nCol : ℕ := 8 * ((∑ f : Lt1 Dw, 2 * rk f) / 8 + Fintype.card (Lt1 Dw) + 1)

variable (Dw) in

def shift (u : Weight Dw) (n : ℕ) (τ : Psi H) : ℤ :=
  ((n / 2 : ℕ) : ℤ) + 1 - if h : 0 < Dw.p then u τ ⟨Dw.p - 1, by omega⟩ else 0

variable (Dw) in

def thA (u : Weight Dw) (n : ℕ) : (E →+* ℂ) × ℕ → ℕ :=
  fun x => ((wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ)).1 x).toNat

theorem eight_dvd_nCol : 8 ∣ nCol Dw := Dvd.intro _ rfl

theorem sum_le_nCol : ∑ f : Lt1 Dw, 2 * rk f ≤ nCol Dw := by
  unfold nCol; omega

theorem OscLe.mono {cx : Lt1 Dw → ℕ} {b b' : ℝ} (h : OscLe Xo c p cx b) (hb : b ≤ b') : OscLe Xo c p cx b' := fun la => by
  obtain ⟨A, hA⟩ := h la
  exact ⟨A, fun T io e ho y => ⟨(hA T io e ho y).1, fun ha => ((hA T io e ho y).2 ha).trans
    (EReal.coe_le_coe_iff.2 (by linarith))⟩⟩

def PrimeSum (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ) : Prop :=
  (∀ q ∈ S, q.Prime) ∧ (∀ q, 0 ≤ e q) ∧ (∀ q ∉ S, e q = 0) ∧ ∑ q ∈ S, e q * Real.log q ≤ s

example : PrimeSum ∅ 0 0 := ⟨by simp, fun _ => le_rfl, fun _ _ => rfl, by simp⟩

end Free

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

abbrev aOf (u1 : Weight (dat p i)) : (D.host.E →+* ℂ) × ℕ → ℕ := thA (dat p i) u1 (nCol (dat p i))

abbrev GOf (u1 : Weight (dat p i)) : WTZ D.host.E := wtZ (aOf p i u1) (nCol (dat p i))

def SumAt (PP C : ℝ) (u1 : Weight (dat p i)) : Prop :=
  ∃ (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ), PrimeSum S e s ∧ lenT p i PP * s ≤ C * unitE p ∧
    ∀ (q : ℕ) [Fact q.Prime], (∀ k, q ≠ D.host.g k) →
      OscLe (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c q (gap (dat p i) (aOf p i u1)) (e q)

def RefAt {l : Level p.T.Q.H} {Xo : Moduli (dat p i) l} {c : Coeff l} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
    (G : WTZ D.host.E) (PP C : ℝ) : Prop :=
  ∃ (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ), PrimeSum S e s ∧ lenT p i PP * s ≤ C * unitE p ∧
    ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) G q ≤ (e q : EReal)

end Point

def SumPt : Prop := Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → SumAt p i PP C u1

def RefCore : Prop := Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 →
  RefAt p i (p.T.U ((i : ℕ) + 1)) (GOf p i u1) PP C

def RefTheta : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (GOf p i u1) PP C

def RefW : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (wtOf (dat p i) u1 0) PP C

end GlobalTheory.RefSum

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

namespace GlobalTheory.ShareOn

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

def sub (M : TwoLevels E r U C) (H : Subgroup U) : TwoLevels E r H C :=
  { M with
    tr := fun u c => M.tr u c
    tr_herm := fun u => M.tr_herm u
    tr_Λ := fun u => M.tr_Λ u
    tr_L' := fun u => M.tr_L' u
    tr_conj := fun u => M.tr_conj u
    tr_mul := fun u v => M.tr_mul u v
    tr_faithful := fun u c h1 h2 => Subtype.ext (M.tr_faithful u c h1 h2) }

def IsPullRep (M : TwoLevels E r U C) (la : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp la)) : Prop :=
  ∃ a : U → C → ℂˣ, ∀ (h : U) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS la) (c : C) (x : M.dom),
    ((ρ h⁻¹ ⟨M.res F, Submodule.subset_span ⟨F, hF, rfl⟩⟩ : M.cusp la) : C → M.dom → ℂ) c x = (a h c : ℂ) * M.pull h F c x.1

def Ranks (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (s : ℕ) (ep c : ℝ) : Prop :=
  Module.Finite ℂ (M.cusp ka) ∧ Module.Finite ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 s)) ∧
    (1 - ep) * finrank ℂ (M.cusp ka) ≤ finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s)) ∧
    (finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 s)) : ℝ) ≤ c * finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s)) ∧
    Module.Finite ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s))

def ArchOne (X : Data E r) (L Fp : Wt X.Ψ r) (T : ℕ) : Prop :=
  ∃ Xa : ArchInM X, Xa.L = L ∧ Xa.Fp = Fp ∧ Xa.T = T ∧ GlobalTheory.Shares.Margins X Xa ∧ Nonempty (FlatM X Xa)

def ArchOn (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (T : ℕ) : Prop :=
  ∃ L Fp : Wt M.Ψ r, ka = Fp + T • L ∧ GapsGe M.p0 L 1 ∧ PairGe L (1.9 * T) ∧
    GapsGe M.p0 (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 0 ∧ PairGe (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 1 ∧
    ∀ c, ArchOne (M.comp c).toData (castWt (M.comp_Ψ c) L) (castWt (M.comp_Ψ c) Fp) T

def sOf (M : TwoLevels E r U C) : ℕ := 2 * r + 50 * r ^ 2 * M.dimX + 2

theorem ArchOne.upper {X : Data E r} {L Fp : Wt X.Ψ r} {T : ℕ} (h : ArchOne X L Fp T) :
    ∃ (Xa : ArchInM X) (Fl : FlatM X Xa), Xa.L = L ∧ Xa.Fp = Fp ∧ Xa.T = T ∧ GlobalTheory.Shares.Margins X Xa ∧
      ∀ (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Fp + T • L)) →
        (∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0) →
        m ≤ Fl.δ * (T + 2 * ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X + 6).choose (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) := by
  obtain ⟨Xa, rfl, rfl, rfl, hm, ⟨Fl⟩⟩ := h
  exact ⟨Xa, Fl, rfl, rfl, rfl, hm, fun m f hf hi => GlobalTheory.UpperModel.upper E r X Xa Fl m f (fun q => (hf q).1) hi⟩

theorem ArchOne.jetInjAt {X : Data E r} {L Fp : Wt X.Ψ r} {T : ℕ} (h : ArchOne X L Fp T) :
    ∃ Xa : ArchInM X, Xa.L = L ∧ Xa.Fp = Fp ∧ Xa.T = T ∧ GlobalTheory.Shares.Margins X Xa ∧ ∃ Fl : FlatM X Xa, JetInjAt X Xa Fl := by
  obtain ⟨Xa, h1, h2, h3, hm, ⟨Fl⟩⟩ := h
  exact ⟨Xa, h1, h2, h3, hm, Fl, GlobalTheory.UpTie.jetInj E r X Xa Fl⟩

theorem exists_archOne (h : Module.finrank ℚ E = 4) : ∃ (X : Data E 2) (L Fp : Wt X.Ψ 2) (T : ℕ), ArchOne X L Fp T := by
  obtain ⟨X, Xa, Fl, -, -, hm⟩ := GlobalTheory.Shares.Model.relIn_margins_lines (E := E) (RingHom.id ℂ) h
  exact ⟨X, Xa.L, Xa.Fp, Xa.T, Xa, rfl, rfl, rfl, hm, ⟨Fl⟩⟩

theorem even_sOf (M : TwoLevels E r U C) : Even (sOf M) := ⟨r + 25 * (r ^ 2 * M.dimX) + 1, by unfold sOf; ring⟩

theorem le_sOf (M : TwoLevels E r U C) : 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ sOf M := Nat.le_succ _

theorem sOf_sub (M : TwoLevels E r U C) (H : Subgroup U) : sOf (sub M H) = sOf M := rfl

theorem cusp_sub (M : TwoLevels E r U C) (H : Subgroup U) (la : Wt M.Ψ r) : (sub M H).cusp la = M.cusp la := rfl

theorem IsPullRep.restrict {M : TwoLevels E r U C} {la : Wt M.Ψ r} {ρ : Representation ℂ U (M.cusp la)} (h : IsPullRep M la ρ)
    (H : Subgroup U) : IsPullRep (sub M H) la (ρ.comp H.subtype) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨fun u c => a u c, fun u F hF c x => ha u F hF c x⟩

theorem ranks_zero (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (h : Module.Finite ℂ (M.cusp ka)) : Ranks M ka 0 0 1 := by
  have h0 : deMul M.Ψ r M.p0 0 = 0 := by
    funext τ i
    simp [deMul]
  unfold Ranks
  rw [h0, smul_zero, add_zero, sub_zero ka]
  exact ⟨h, h, by simp, by simp, h⟩

end Model

section Point

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

def HalfUnip (H : Subgroup p.P.Gp) : Prop :=
  ∃ k : Fin 2, ∀ g ∈ H, ∀ v : D.nd.PlG k,
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((p.R.eG.trans p.cG) g ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))

def ModelAt (T : ℕ) : Prop :=
  ∃ (C : Type) (_ : Finite C) (_ : MulAction p.P.Gp C) (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r)
    (ρ : Representation ℂ p.P.Gp (M.cusp ka)) (σ : D.what₂.LL →+* ℂ)
    (f : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[σ] M.cusp ka),
    IsPullRep M ka ρ ∧ (∀ g v, ρ g (f v) = f ((p.R.toRealDat.FW i).ρ g v)) ∧
    (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ ∧
    (∀ H, HalfUnip p H → LevelHyp (sub M H)) ∧ M.Ψ.card = D.R.f ∧
    ((M.p0 = 0 ∨ M.p0 = D.R.r) ∨ (0 < M.p0 ∧ M.p0 < D.R.r ∧ ArchOn M ka T))

def ShareW (y : ℝ) : Prop :=
  (1 - y) * (p.R.toRealDat.nW i : ℝ) ≤ (Nat.card p.P.P0 : ℝ) * finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i)

def BadW (del : ℝ) : Prop :=
  (finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i ⊓ LinearMap.ker (eGood p.R.toRealDat i) : Submodule D.what₂.LL _) : ℝ) ≤
    del * finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i)

end Point

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn

def ModelSt : Prop := AtRuns fun Fm x hx ι p _ _ => ∀ i, ModelAt p i (Fm.parT x hx ι).TO

def ShareWSt : Prop := AtRuns fun Fm x _ ι p _ _ => ∀ i,
  ShareW p i (1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3))

def BadWSt : Prop := AtRuns fun Fm x _ ι p _ _ => ∀ i,
  BadW p i (Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))))

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsComplSpace
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit GlobalTheory.SWLink
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWInt

section
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

def HasWeilModel (ψ : AddChar (AF F) ℂ) (χ : Chr F E) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (T : GL (Fin (n + n)) E)
    (K : Subgroup (UA σ J₂)) (JV : Matrix (Fin m) (Fin m) E) (P : Submodule ℂ (UA σ J₂ → ℂ) → Prop) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co ∧
  ∃ (_ : MeasurableSpace (κ → AF F)) (_ : BorelSpace (κ → AF F)) (μ : Measure (κ → AF F)), IsTamagawa F κ μ ∧
  ∃ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om ∧ P (secSpace om K)

def ComplMet (m t : ℕ) (b : Prop) : Prop :=
  IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧
  ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
  ∃ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin (m + t)) (Fin (m + t)) E)
    (J₂ : Matrix (Fin (m + t + (m + t))) (Fin (m + t + (m + t))) E),
    l ≠ 0 ∧ IsHermND σ (l • JV) ∧ (∀ x, form σ JV x x = 0 → x = 0) ∧
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) ∧ J₂ = dblGram finSumFinEquiv J ∧
  ∃ T : GL (Fin (m + t + (m + t))) E, IsWittBasis σ J l T ∧
  ∃ χ : Chr F E, IsHecke F E χ ∧ ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m ∧
  ∃ K : Subgroup (UA σ J₂), IsStdK σ T K ∧ IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K ∧
    (∃ w : UA σ J₂, IsWeylElt σ T w) ∧ (∃ νN : Measure (GlobalTheory.SWWeil.unipN σ J₂), IsNormN σ νN) ∧
    HasWeilModel σ ψ χ T K JV (fun R => b → R ≠ ⊥) ∧ HasWeilModel σ ψ χ T K (complGram l JV t) fun R => b → R ≠ ⊥

end

theorem exists_frame_hyp (D : D7) (t : ℕ) : ∃ b : Module.Basis (Fin (t + t)) D.host.E (GlobalTheory.OrthSumSp.hypSp D t).V,
    ∀ i j, (GlobalTheory.OrthSumSp.hypSp D t).hT (b i) (b j) = -blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0 i j := by
  let P : Matrix (Fin (t + t)) (Fin (t + t)) D.host.E := blk 1 (-((2 : D.host.E)⁻¹ • 1)) 1 ((2 : D.host.E)⁻¹ • 1)
  have hP : P * blk ((2 : D.host.E)⁻¹ • 1) ((2 : D.host.E)⁻¹ • 1) (-1) 1 = 1 := by
    rw [WittModel.blk_mul, ← WittModel.blk_one]
    congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg] <;>
      match_scalars <;> norm_num
  let f := (GlobalTheory.OrthSumSp.hypSp D t).frame
  let b := f.map (Matrix.toLinearEquiv f P (Matrix.isUnit_det_of_right_inverse hP))
  have hb : ∀ j, b j = ∑ i, P i j • f i := fun j => by
    simp only [b, Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have hG : ∀ i j, (GlobalTheory.OrthSumSp.hypSp D t).hT (f i) (f j) =
      dblGram finSumFinEquiv (1 : Matrix (Fin t) (Fin t) D.host.E) i j := fun i j => by
    have := gram_hdbl (GlobalTheory.OrthSumSp.posSp D t)
    rw [GlobalTheory.OrthSumSp.posSp_gram D t] at this
    exact congrFun (congrFun this i) j
  refine ⟨b, fun i j => ?_⟩
  have e : (GlobalTheory.OrthSumSp.hypSp D t).hT (b i) (b j) =
      (Pᴴ * dblGram finSumFinEquiv (1 : Matrix (Fin t) (Fin t) D.host.E) * P) i j := by
    simp only [hb, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hG, smul_eq_mul,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e1 : Pᴴ = blk 1 1 (-((2 : D.host.E)⁻¹ • 1)) ((2 : D.host.E)⁻¹ • 1) := by
    simp [P, blk, Matrix.fromBlocks_conjTranspose]
  have e2 : dblGram finSumFinEquiv (1 : Matrix (Fin t) (Fin t) D.host.E) = blk 1 0 0 (-1) := rfl
  have e3 : -blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0 = blk 0 (-1) (-1) 0 := by
    change (-Matrix.fromBlocks (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0).submatrix _ _ = _
    rw [Matrix.fromBlocks_neg, neg_zero, blk]
  rw [e, ← Matrix.neg_apply, e3, e1, e2, WittModel.blk_mul, WittModel.blk_mul]
  congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_zero, add_zero, zero_add] <;>
    match_scalars <;> norm_num

theorem exists_compl_space (D : D7) (V : HSp D) (t : ℕ) :
    ∃ b : Module.Basis (Fin (t + t)) D.host.E (GlobalTheory.OrthSumSp.hypSp D t).V,
      -(hsum V { GlobalTheory.OrthSumSp.hypSp D t with frame := b }).gram = complGram 1 (-V.gram) t := by
  obtain ⟨b, hb⟩ := exists_frame_hyp D t
  refine ⟨b, ?_⟩
  have e : HSpace.gram { GlobalTheory.OrthSumSp.hypSp D t with frame := b } = -blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0 :=
    Matrix.ext hb
  rw [gram_hsum, e, complGram, inv_one, one_smul]
  change (-Matrix.fromBlocks V.gram 0 0 (-blk (0 : Matrix (Fin t) (Fin t) D.host.E) 1 1 0)).submatrix _ _ = _
  rw [Matrix.fromBlocks_neg, neg_zero, neg_zero, neg_neg, blkMat]

set_option maxHeartbeats 4000000 in

theorem complMet_of (D : D7) (V : HSp D) (han : IsAniso V) (t : ℕ) : ComplMet D.sp.cm.sig V.rank t False := by
  let n := V.rank + t
  obtain ⟨-, ψ, χ, omh, -, -, -, -, hω, -, -, -⟩ :=
    GlobalTheory.SiegelFormula.Model.data_exist GlobalTheory.weilRepresentationUnitaryPair V V
  obtain ⟨θ, hθ⟩ := hω.std.2.1
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  obtain ⟨lam, hlam, hψ, -⟩ :=
    GlobalTheory.StdUnn.shift_char_realPar D ψ hω.std θ hθ D.host.xi0 ⟨hxi, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D⟩
  have hl : lam ≠ 0 := fun h => by
    rw [h, map_zero] at hlam
    exact div_ne_zero (neg_ne_zero.2 hxi) hxi hlam.symm
  have hCM := GlobalTheory.AdelicU.isCMExt_host D
  obtain ⟨δ, hδ0, hδ⟩ := skew_xi D
  let J : Matrix (Fin n) (Fin n) D.host.E := δ • 1
  have hJ : ∀ i j, D.sp.cm.sig (J j i) = -J i j := fun i j => by
    by_cases h : i = j
    · subst h; simp [J, hδ]
    · simp [J, h, Ne.symm h]
  have hJ' : ∀ i j, D.sp.cm.sig (((1 : D.host.E)⁻¹ • J) j i) = -((1 : D.host.E)⁻¹ • J) i j := by
    rw [inv_one, one_smul]; exact hJ
  have hJ0 : J.det ≠ 0 := by simp [J, hδ0]
  obtain ⟨T, K, hT, hK, -⟩ := GlobalTheory.T.exists_witt_basis_compact_stabiliser D.host.F D.host.E D.sp.cm.sig hCM n 1 J _ one_ne_zero hJ0 rfl
  have hG := gram_witt hJ hT
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.witt_change_basis_unitary_iso D n _ T hG
  obtain ⟨hP, ha⟩ := GlobalTheory.T.siegel_parabolic_chart_levi_block D n _ T κ hκ J hT
  have hK' := GlobalTheory.T.standard_compact_under_witt_chart D n _ T κ hκ K hK
  obtain ⟨H, hH⟩ := GlobalTheory.StdUnn.exists_height D n
  obtain ⟨hI, -⟩ := height hH hP ha hK'
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let ε := Module.finBasis D.host.F D.host.E
  have key : ∀ B : HSp D, ResEta D χ B.rank →
      HasWeilModel D.sp.cm.sig (GlobalTheory.StdUnn.shift ψ lam) χ T K (-B.gram) fun R => False → R ≠ ⊥ := fun B hB => by
    obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.MixModel.exists_isCovolOne D B.rank n
    obtain ⟨ω, hW⟩ := GlobalTheory.StdUnn.Inhab.weil_exists D n B ψ hω.std lam hl χ hω.hecT hB θ hθ μ 𝓕 hμ
    obtain ⟨ι, hι, -⟩ := GlobalTheory.T.unitary_group_conj_hermitian_automorphisms D B
    obtain ⟨co, had, hco⟩ := GlobalTheory.T.darboux_basis_adapted_coordinates D n B J _ T hT hG _ ε
    letI : MeasurableSpace (Fin B.rank × Fin n × Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := borel _
    haveI : BorelSpace (Fin B.rank × Fin n × Fin (Module.finrank D.host.F D.host.E) → AF D.host.F) := ⟨rfl⟩
    obtain ⟨μ', hμ', hint⟩ := GlobalTheory.T.tamagawa_measure_matrix_adeles D B.rank n _ ε μ 𝓕 hμ
    obtain ⟨om, hom⟩ := GlobalTheory.T.weil_representation_seesaw_schwartz D n B _ χ θ hθ μ 𝓕 hμ ω hW _ _ ε ι κ
    exact ⟨_, inferInstance, co, had, inferInstance, inferInstance, μ', hμ', om, formulas hθ hW hT hG hκ hι hco hint hom,
      False.elim⟩
  obtain ⟨b, hb⟩ := exists_compl_space D V t
  have hres : ResEta D χ (V.rank + (t + t)) := resEta_parity hω.resT (by omega)
  have h2 := key (hsum V { GlobalTheory.OrthSumSp.hypSp D t with frame := b }) hres
  rw [hb] at h2
  obtain ⟨w, -, hw⟩ := exists_isWeylElt (GlobalTheory.SiegelSet.sigma_sigma hCM) one_ne_zero hJ' rfl hT
  exact ⟨hCM, unramified_host D, _, hψ, 1, -V.gram, J, _, one_ne_zero, isHermND_neg_gram V, aniso_neg_gram han, hJ', rfl,
    T, hT, χ, hω.hecT, GlobalTheory.LFun.resEtaPow_of_resEta D.host.F D.host.E hCM.2.2.1 χ V.rank hω.resT, K, hK, hI, ⟨w, hw⟩,
    (existsUnique_isNormN hCM one_ne_zero hJ' hJ0 rfl).exists, key V hω.resT, h2⟩

theorem exists_complMet : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E), ∀ m t, ComplMet σ m t False := by
  obtain ⟨D⟩ := GlobalTheory.Mem.nonempty_record
  refine ⟨D.host.F, D.host.E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D.sp.cm.sig,
    fun m t => ?_⟩
  obtain ⟨-, V, -, rfl, h⟩ := GlobalTheory.AnisoStdModel.ranks D 0 m
  exact complMet_of D V h t

end GlobalTheory.SWInt

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

structure HostNum (D : D7) (L : SizeData₂ D) (PP A M : ℝ) : Prop where
  big : M ≤ L.sc.L ∧ 10 ≤ L.sc.L ∧ L.sc.L ≤ L.sc.x ∧ 1 ≤ Real.log (Real.log L.sc.x)
  f8 : 8 ≤ D.R.f
  deg : Module.finrank ℚ D.host.E = 2 * D.R.f
  logfr : Real.log ((D.R.f : ℝ) * D.R.r) ≤ L.sc.L ∧ Real.log (D.R.nV : ℝ) ≤ L.sc.L
  logg : ∀ k, Real.log (D.host.g k : ℝ) ≤ 9 * L.sc.L + 1
  disc : Real.log |(discr D.host.E : ℝ)| ≤ 4 * D.R.f * L.sc.L
  logd : Real.log (D.host.d : ℝ) ≤ L.sc.L
  split : 5 ≤ D.host.splitBound
  cop : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)
  ppLow : zBase L ^ 12 ≤ PP
  poly : 1 ≤ A ∧ PP ≤ L.sc.x ^ A ∧ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L ≤ L.sc.x ^ A
  room : (L.sc.x ^ A) ^ M ≤ L.sc.b
  low : Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n

def wtsAt (PP : ℝ) (h0 : ℤ) (S eta : ℝ) (u1 : Weight (dat p i)) :
    GlobalTheory.MeanTop.Wts (Psi p.T.Q.H) ((dat p i).p + (dat p i).q) :=
  { kc := D.R.k - 1, p := (dat p i).p, T := lenT p i PP, Dd := dimFlag (dat p i), c0 := cZero D ((i : ℕ) + 1), h0 := h0, S := S,
    eta := eta, b := 4 * L.sc.b, w := fun τ => (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ), u := uW p i, u1 := u1 }

theorem quo_iff (PP : ℝ) (h0 : ℤ) (S eta : ℝ) (u1 : Weight (dat p i)) : Quo p i PP u1 ↔ (wtsAt p i PP h0 S eta u1).IsDiv :=
  Iff.rfl

structure WtNum (PP : ℝ) : Prop where
  sig : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1 ∧ (dat p i).q = (D.R.sigW ((i : ℕ) + 1)).2 ∧ (dat p i).p + (dat p i).q = D.R.r
  card : Nat.card (Psi p.T.Q.H) = D.R.f
  dim : dimFlag (dat p i) = D.R.f * D.R.r.choose 2
  cols : (p.κ i).n = D.R.nV
  dom : Dom (wtA (p.κ i)) (p.κ i).n
  unit : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x)
  om : |(ofRecord D L p.Del p.h0).logOm| ≤ 3 * L.sc.L
  up : ∀ τ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| ≤ 4 * L.sc.b
  low : ∀ τ, L.sc.w'' D.R.n ≤ 2 * (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)
  what₂ : PP ^ 2 * D.R.r * D.R.m * D.R.k * (dimFlag (dat p i) : ℝ) ^ 3 ≤ L.sc.b ∧
    PP * lenT p i PP * (dimFlag (dat p i) : ℝ) ^ 2 * L.sc.L ≤ L.sc.b
  hyp : (i : ℕ) + 1 < D.R.m → ∃ (h0 : ℤ) (S eta : ℝ), 0 ≤ S ∧ 0 ≤ eta ∧ PP * (S + eta) ≤ 100 * L.sc.w'' D.R.n ∧
    4 * (lenT p i PP : ℤ) ^ 2 ≤ h0 ∧
    PP * lenT p i PP * D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * dimFlag (dat p i) ≤ h0 ∧
    ∀ u1, (wtsAt p i PP h0 S eta u1).Hyp

def HostN (M : ℝ) : Prop := Lifts fun Fm x _ ι _ _ PP A => HostNum (Fm.D x ι) (Fm.L x ι) PP A M

def WtN : Prop := Lifts fun _ _ _ _ p i PP _ => WtNum p i PP

end GlobalTheory.CovTop

end
end

