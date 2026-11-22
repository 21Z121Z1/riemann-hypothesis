import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0616
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0613
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.SharpRestriction.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0190
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialLFunctionOfPublished
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.LiftOntoOfPublished

theorem ontoC_of_classicalTheorems : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW := by
  intro hDSC hHCM hCusp hHowe hWSF hDbl hUnr hBZ hReg hHeckeL D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hHost hPar hcc hQ
    hGT hOkH hPG hLU hW hHT
  have hGiv : Given R.toRealDat F.lv2 :=
    GlobalTheory.GivenOfTop.given_of_top R F hOk hC hEx hHost hPar hcc hQ hGT
  have hFull : R.toRealDat.FullP := hC.fullP
  have hLI : LiftInj R.toRealDat :=
    (GlobalTheory.T.unramified_howe_lift_rows hCusp hDbl hReg hUnr hHeckeL hHowe _ _ _ _ _ _ R.toRealDat F.lv2 hGiv hFull).1
  have hSE : GlobalTheory.Published.SiegelEisensteinContinuation :=
    GlobalTheory.Published.siegelEisensteinContinuation_of_doublingMethod hDbl
  have hCore := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  have hA : AForm R.toRealDat R.SF :=
    GlobalTheory.T.thetaInnerProduct_eq_const_mul_LValue hDSC hHCM hCusp hWSF hSE hUnr hBZ R.toRealDat F.lv2 hGiv hcc R.SF hCore.2.1
  have hUp : UpInjW R.toRealDat :=
    GlobalTheory.Core.Rk.UpInjWProof.upInjW_of_aForm _ _ _ _ _ _ R.toRealDat F.lv2 hCore.1
      (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) hGiv.irr R.SF hCore.2.1 hA
  exact GlobalTheory.T.thetaLift_onto_of_injective_eigenspaces R F hOk hC hEx hLI hUp hOkH hPG hLU hW hHT

end GlobalTheory.LiftOntoOfPublished
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftFirstHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
namespace GlobalTheory.ThmAFinal

theorem pThmA_short
    (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHCF : GlobalTheory.Published.HarishChandraFinite)
    (hHCM : GlobalTheory.Published.HarishChandraModules) (hCW : GlobalTheory.Published.CasselmanWallach)
    (hCusp : GlobalTheory.Published.CuspRapidDecay) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hWS : GlobalTheory.Published.WeilSiegelFormulaUnitary) (hHk : ∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D')
    (hSE : GlobalTheory.Published.SiegelEisensteinContinuation) (hUD : GlobalTheory.Published.UnramifiedDoublingGL)
    (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) :
    ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PThmA := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hCh hEx hHost hLed hcc hQ hGT hInert
  obtain ⟨hCore, hSF, hE, hW⟩ := GlobalTheory.T.core_clauses_of_weak_characterisation R F hCh hEx
  have hGiven := GlobalTheory.T.scalarHypotheses_of_topRows R F hOk hCh hEx hHost hLed hcc hQ hGT
  have hFix := GlobalTheory.T.hyperspecial_fixes_vacua_good_inert_place R F hCh hEx
  have hA := GlobalTheory.T.thetaInnerProduct_eq_const_mul_LValue hDS hHCM hCusp hWS hSE hUD hBZ R.toRealDat F.lv2 hGiven hcc R.SF hSF
  have hU := (GlobalTheory.T.thetaLift_adjoint_scalarFormula_injective hDS hHCF hHCM hCW hCusp hHowe hWS hHk hSE hUD R.toRealDat F.lv2 hGiven hcc hCh.allPl hFix R.SF hSF).2
  have hC := GlobalTheory.T.finiteType_carriesOnePart hHowe hCusp R F hOk hCh hEx hInert hU
  exact GlobalTheory.T.thetaAdjoint_scalar_theorem_of_scalar_formula R F hOk hCh hEx hA hC

end GlobalTheory.ThmAFinal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftScalarIdentityMatchingAdjointInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalAll

theorem scal_matchUp_upInj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → R.Sb = R.Pg → (∀ t P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R t P) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF → Scal R SF ∧ MatchUp R SF ∧ UpInj R ∧ UpInjW R := by
  intro hDS hHCF hHCM hCW hCRD hHowe hWS hSWU hSEC hUD hBZ D G _ _ Pl0 T A Ks _ _ _ R F hG hcc hSb hfix SF hSF hTR
  have hA : AForm R SF := GlobalTheory.T.thetaInnerProduct_eq_const_mul_LValue hDS hHCM hCRD hWS hSEC hUD hBZ R F hG hcc SF hSF
  obtain ⟨hB, hUp⟩ := GlobalTheory.T.thetaLift_adjoint_scalarFormula_injective hDS hHCF hHCM hCW hCRD hHowe hWS hSWU hSEC hUD R F hG hcc hSb hfix SF hSF
  have hM : MatchUp R SF := GlobalTheory.MatchUpProof.matchUp_of_tr R F hG.core SF hTR
  have hS : Scal R SF := scal_of_aForm_bForm R SF hA hB hM
  exact ⟨hS, hM, hUp, (upInj_of_scal R F hG.core (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R) hG.irr SF hSF hS).2⟩

end GlobalTheory.ScalAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryStepRelationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_step_relation : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∃ U0 : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), U0 ≤ GfC _ ∧ IsCompact (U0 : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) ∧ ∀ t (J : QJ a t), J.Reads → ∀ α, J.A.U j (J.ι j α) ≤ U0 ∧ (J.A.U j (J.ι j α)).relIndex U0 = ∏ i, (GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)) (α i)))).relIndex (GlobalTheory.SplitWeil.KO (J.G i).k _) := by
  first | exact @GlobalTheory.PenBridge.pen_bridge | exact GlobalTheory.PenBridge.pen_bridge | (intros; apply GlobalTheory.PenBridge.pen_bridge <;> assumption)
end

