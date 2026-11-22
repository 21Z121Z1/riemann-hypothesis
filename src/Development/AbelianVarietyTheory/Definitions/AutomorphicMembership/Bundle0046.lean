import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyGridDataIff

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev RowP : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (hX : B.fields.Ok)
    (z : Dat (w.st Z) w.I hX T Wt) (p0 : BaseLevelRowSide (w.D Z)), Read z.R.toRealDat z.F.lv2 p0 → Prop

def OverRows (p : RowP) : Prop :=
  EvLgG fun K B f T => KPx B f → ∀ w : ColW B f T, ColPin w → ∀ Z Wt hX z p0 Y, Holds z.R z.F → z.R.toRealDat.ExAt →
    GlobalTheory.RealGeo.InGeo z.geo → GrpTrue Z.N f → GrpAt (w.st Z) w.I → p K B f T w Z Wt hX z p0 Y

def CenLoc (D : D7) (M : MtFam D) : Prop :=
  ∀ i : D.nd.Loc, ∃ L : G0g D.nd → GAf D.host.E D.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
      ∀ (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (x : D.what₂.Mt (D.nd.mu i) (D.nd.j i)),
        (M.loc i).real (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) z x) =
          GlobalTheory.PendOf.actSum D L (z : MonoidAlgebra ℂ (G0g D.nd)) ((M.loc i).real x)

theorem cenLoc_of_cenReal {D : D7} {M : MtFam D} (h : GlobalTheory.PendOf.CenReal D M) : CenLoc D M :=
  fun i => h (D.nd.mu i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2

def SumTw (D : D7) (M : MtFam D) : Prop :=
  ∀ w, TwistedAt D w → ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), GlobalTheory.CoefDuty.ClassSum (M (D.what₂.muTw w) j h1 h2)

structure ParIn (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (Rw : RowSide D) : Type 1 where
  T : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : LabTrue D T
  chr : CharSide D cf
  cg : CGTrue hL D T
  A : AUSide D
  au : AUTrue hL D T A
  row : RowTrue hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR

def ParIn.ofSt {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (a : StA hL D cf rep) : ParIn hL D cf rep a.A.row := ⟨a.A.wdT, a.A.lab, a.A.chr, a.cg, a.A.au, a.au, a.row⟩

open GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings in

structure LiftAt (D : D7) (Rw : RowSide D) (j : ℕ) (σ : D.what₂.FT) (π : D.nbc.AU j) (μ : D.naut.CG 1) : Prop where
  csd : D.naut.csd μ
  unr : ∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)
  sph : SphericalInertData.SphInert D.nd D.naut D.nbc j π
  loc : ∀ w, IsSplitPl D.host w → D.nbc.locAU j π w =
    D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w)
  eta : ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧ D.naut.infG D.naut.etaTinv (embTauBar D τ) = {(1 / 2 : ℂ)}
  inf : ∀ τ, D.nbc.infW j (D.nbc.wtAU j π) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = (hcSigma (D.hc τ)).map (· - 1 / 2) +
      isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) ∧
    D.nbc.infW j (D.nbc.wtAU j π) (embTauBar D τ) = (hcSigma (D.hc τ)).map (fun y => -y + 1 / 2) +
      isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (embTauBar D τ)

def LiftAll (D : D7) (Rw : RowSide D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∃ π μ, LiftAt D Rw j σ π μ

def RowLoc (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) : Prop :=
  ∀ w : PlE D.host, IsSplitPl D.host w → (∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) → D.naut.unr (Rw.locR σ w) ∧
    ∀ α ∈ D.naut.frobEig (Rw.locR σ w), ‖α‖ < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)

structure ParLaws (D : D7) : Prop where
  tie0 : SumRepresentations.tie0 D
  an : SumRepresentations.adm5 D
  temp : SumRepresentations.adm7 D
  lab : SumRepresentations.tieLab D
  one : GlobalTheory.RowCopy.HeckeSplitOne D
  cancel : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b
  gsp : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

theorem AtMem.imp {p q : LayP hL} (h : AtMem hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : AtMem hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)

theorem AtMem.and {p q : LayP hL} (h : AtMem hL p) (h' : AtMem hL q) :
    AtMem hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w Z Wt p0 t nch n xd c a b d =>
    ⟨H.1 kp w Z Wt p0 t nch n xd c a b d, H.2 kp w Z Wt p0 t nch n xd c a b d⟩

theorem rootsLL_pow {D : D7} (h : RootsLL D) : ∃ ζ : D.what₂.LL, ζ ^ D.what₂.restRowsFiniteGroupCard = 1 ∧ orderOf ζ = D.what₂.restRowsFiniteGroupCard ∧ 0 < orderOf ζ := by
  obtain ⟨ζ, hζ⟩ := h
  exact ⟨ζ, hζ.pow_eq_one, hζ.eq_orderOf.symm, hζ.eq_orderOf ▸ D.what₂.restRowsFiniteGroupCard_pos⟩

theorem sumUsed_ref {D : D7} {M : MtFam D} (h : SumUsed D M) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    GlobalTheory.CoefDuty.ClassSum (M D.what₂.mu0 j h1 h2) := h _ (Or.inl rfl) j h1 h2

theorem used_loc {D : D7} (i : D.nd.Loc) : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

theorem sumUsed_loc {D : D7} {M : MtFam D} (h : SumUsed D M) (i : D.nd.Loc) : GlobalTheory.CoefDuty.ClassSum (M.loc i) :=
  h _ (used_loc i) _ _ _

theorem exists_xdAll_iff (D : D7) : (∃ xd : ThData D, XdAll xd) ↔
    ∀ i j b, 1 ≤ j → j ≤ D.R.m → ∀ (a : D.nexp.Dat i j b) (u : D.nexp.U), D.nexp.actG i j b u (D.nexp.th i j b a) =
      ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • D.nexp.th i j b a := by
  constructor
  · rintro ⟨xd, h⟩ i j b h1 h2 a u
    exact xd.thetaBase_invariant_action i j b a (by rw [h i j b h1 h2]; trivial) u
  · intro h
    refine ⟨⟨fun i j b => {_a | 1 ≤ j ∧ j ≤ D.R.m}, fun i j b a ha u => h i j b ha.1 ha.2 a u⟩, fun i j b h1 h2 => ?_⟩
    exact Set.eq_univ_of_forall fun _ => ⟨h1, h2⟩

theorem isot_withLoc {D : D7} (L : LocAll (lay0 D)) : Rows.IsotInternal (withLoc L).what₂ ↔ Rows.IsotInternal D.what₂ := Iff.rfl

end GlobalTheory.HeightCounting.Up.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ParMem
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th

structure HypA : Prop where
  a1 : GlobalTheory.NT.RayField
  a2 : GlobalTheory.Published.PrincipalIdealSt
  a3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt
  a5 : GlobalTheory.Published.HarishChandraModules
  a6 : GlobalTheory.Published.CuspRapidDecay
  a7 : GlobalTheory.Published.CasselmanWallach
  a8 : GlobalTheory.Published.WeilRepresentationUnitaryPair
  a9 : GlobalTheory.Published.DiscreteSeriesExists
  a10 : GlobalTheory.Published.HarishChandraFinite
  a11 : GlobalTheory.Dec.DSInfChar
  a12 : GlobalTheory.Published.DiscreteSeriesUpqUnique
  a13 : Formalism.L2.SG.RowsDef.RowsFinDim
  a14 : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent
  a15 : PI.BesselMapUniq.BesselMapUniq
  a16 : Vol.DiscreteSeriesExist
  a17 : Vol.FormalDegreeFormula₂
  a18 : StandardLattice.SiegelMassRatioCM
  a19 : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ
  a20 : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)
  a21 : ∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam
  a22 : GlobalTheory.Published.GlobalArtinReciprocity
  a23 : GlobalTheory.Published.WeberRayFieldSt

end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw

structure HypE : Prop where
  e1 : GlobalTheory.TwSys.Cheb
  e2 : GlobalTheory.Published.PoitouTateTotallyComplex
  e3 : GlobalTheory.Published.CohDimTwo
  e4 : GlobalTheory.Published.TameLocal
  e5 : LocalFiniteness
  e6 : LocalTateDuality
  e7 : LocalEulerChar
  e8 : GlobalFiniteness
  e9 : GlobalEulerChar
  e10 : UnramifiedOrthogonality
  e11 : BlochKatoReduction.Gen.ArchimedeanSignatureMatching
  e12 : GreenbergWiles
  e13 : GlobalTheory.Published.RayCharacterArtin
  e14 : GlobalTheory.Published.ChebotarevDegreeOne
  e15 : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator
  e16 : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat
  e17 : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt
  e18 : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt
  e19 : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform
  e20 : GlobalTheory.HeckeSupSt.HeckeReadTie
  e21 : GlobalTheory.Published.AutomorphicFormsFiniteGL
  e22 : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal
  e23 : GlobalTheory.Published.DeRhamPotSemistable
  e24 : GlobalTheory.GalOfCusp.LocalGlobalAboveL
  e25 : ∀ D : D7, LocalSituation.Conclusion5 D

end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

structure HypN (hL : GlobalTheory.Published.LocalLanglandsGL) : Prop where
  pr : PrN
  ser : SerN
  arch : ArchCmp hL
  par : ParSt hL
  pt : PtSt hL
  parMem : AtMem hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw)

@[reducible] def prm0 (hL : GlobalTheory.Published.LocalLanglandsGL) : Prm hL := prmR (NEb hL) SExt.none (geoCl anyGeometry)

def MultQ {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) : Prop :=
  GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat

end

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistOfGrid
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up.GridModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.Links NumberField IsDedekindDomain GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem depth0_mono (D : D7) {C C' b : ℝ} (h : C ≤ C') (hb : 1 ≤ b) : depth0 D C b ≤ depth0 D C' b := by
  have hq : 0 < Real.log (q0 D) := Real.log_pos (by exact_mod_cast (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.one_lt)
  have one : ∀ {n : ℕ}, n ≠ 0 → (1 : ℝ) ≤ n := fun hn => by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have h1 : (1 : ℝ) ≤ nRk D := one (by unfold nRk; omega)
  have h2 : (1 : ℝ) ≤ D.host.g 0 := one (D.host.g_prime 0).ne_zero
  have h3 : (1 : ℝ) ≤ D.host.g 1 := one (D.host.g_prime 1).ne_zero
  have h4 : (1 : ℝ) ≤ D.host.pde := one D.host.pde_prime.ne_zero
  have h5 : (1 : ℝ) ≤ D.host.pde' := one D.host.pde'_prime.ne_zero
  have h6 : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero D.host.E)
    exact_mod_cast this
  have hl : 0 ≤ Real.log (b * nRk D * D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * |(discr D.host.E : ℝ)|) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hb h1) h2) h3) h4) h5) h6)
  unfold depth0 sizeP
  gcongr

theorem gridPin_anti {D : D7} {I : Type} {Lc : LevCh D I} {μ0 : I} (hL : Lc.Is μ0) {CF CF' b : ℝ} (h : CF ≤ CF') (hb : 1 ≤ b)
    (hp : GridPin D Lc CF' b) : GridPin D Lc CF b := by
  obtain ⟨G, hF, hT⟩ := hp
  obtain ⟨h1, h2⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 I Lc G.pl ⟨1, CF, b⟩
  obtain ⟨V⟩ := GlobalTheory.ChiGridModel.nonempty_vertices D I Lc _ _ (GlobalTheory.ChiGrid.colY_isV D I Lc μ0 hL 0 (Nat.zero_le _)).sd h1 h2
  refine ⟨⟨G.pl, G.ch, V⟩, ⟨hF.values, fun v hv => ?_⟩, hT⟩
  obtain ⟨z, hz⟩ := hF.roots v hv
  have hd : G.pl.depth ⟨1, CF, b⟩ v ≤ G.pl.depth ⟨1, CF', b⟩ v := by
    unfold Places.depth
    split_ifs
    · exact depth0_mono D h hb
    · exact le_rfl
  have hpos : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  exact ⟨_, hz.pow (pow_pos hpos _) (by rw [← pow_add, Nat.sub_add_cancel hd])⟩

theorem not_gridPin {D : D7} {I : Type} (Lc : LevCh D I) (CF b : ℝ) (h : q0 D = D.host.g 0) : ¬ GridPin D Lc CF b :=
  fun ⟨G, _⟩ => (GlobalTheory.ChiGridModel.isEmpty_gridData Lc _ h).false G

theorem fixed_not_diagonal (𝒞 : FamClass) : ∃ P : ℝ → ∀ {eps : ℝ}, FamP eps → ℝ → Prop,
    (∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed 𝒞 (P CF)) ∧ ∀ (eps : ℝ) (Fm : FamP eps) (CH : ℝ), ¬ P Fm.CF Fm CH :=
  ⟨fun CF _ Fm _ => CF < Fm.CF, ⟨0, fun CF _ => ⟨1, one_pos, fun _ _ _ =>
    ⟨⟨0, fun _ => 0, fun _ => CF + 1, fun _ => 0⟩, fun Fm CH _ h =>
      lt_of_lt_of_le (lt_add_one CF) (h.2.2.1 Fm.CF (by simp [FamP.cMid]))⟩⟩⟩, fun _ _ _ => lt_irrefl _⟩

section Guard

open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR GlobalTheory.BigTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem gridPin_of_fit (p : PtAt ex Csz) {CF : ℝ} {G : Grid p CF} (h : GridFit p G) : GridPin D p.R.toRealDat.toLevCh CF L.sc.b :=
  ⟨G, h.field, h.list⟩

theorem fit_of_gridPin (p : PtAt ex Csz) {μ0} (hL : p.R.toRealDat.toLevCh.Is μ0) {CF CF' : ℝ} (h : CF ≤ CF') (hb : 1 ≤ L.sc.b)
    (hp : GridPin D p.R.toRealDat.toLevCh CF' L.sc.b) {xd v0 rep} (ht : GlobalTheory.EX.TwistAt L ex.nch xd v0 rep)
    (h1 : ValLL0 D p.R.C) (h3 : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp) : ∃ G : Grid p CF, GridFit p G :=
  let ⟨G, a, b⟩ := gridPin_anti hL h hb hp
  ⟨G, GridFit.of_twistAt ht h1 a h3 b⟩

end Guard

theorem not_gridPin_of_empty {D : D7} {I : Type} (Lc : LevCh D I) (CF b : ℝ) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (h : IsEmpty (D.ntw.abelian₂ i)) : ¬ GridPin D Lc CF b := fun ⟨_, _, t⟩ => (t.nonempty hi).elim h.false

variable (hL : GlobalTheory.Published.LocalLanglandsGL)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem settingsFormsExist_of_grid : SettingsFormsExistGrid hL → SettingsFormsExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem seriesExist_of_grid : SeriesExistGrid hL → SeriesExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem moduliPointsExist_of_grid : ModuliPointsExistGrid hL → SB2 hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

end GlobalTheory.HeightCounting.Up.GridModel

end
end

