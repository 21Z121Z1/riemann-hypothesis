import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0831
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0851
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0808
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0823
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0816
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0835
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0832
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0758
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0828
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllReductionStatementsHold
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem reductionStatements_of_casselmanWallach : GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.DiscreteSeriesUpqUnique → HypH → PrN → SerN →
    ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ArchCmp hL → PtSt hL →
    SA hL ∧ SMt ∧ SRat hL ∧ SCusp hL ∧ SettingsFormsExist hL ∧ SeriesExist hL ∧ SB2 hL ∧ SC hL ∧ SFin hL ∧
      ∀ cDep : ℝ, SettingsFormsExistList hL cDep ∧ SeriesExistList hL cDep ∧ ModuliPointsExistList hL cDep ∧ SFinl hL cDep := by
  intro hCW hHM hW hD hU hH hP hS hL hA hPt
  have hMt : SMt := GlobalTheory.T.multiplicity_of_primitive hP
  have hRat : SRat hL := GlobalTheory.HeightCounting.RatSide.sRat_of_duties hU hP hS (GlobalTheory.HeightCounting.Up.IsotAtStates.isot_allSt hW hD hH hP) hL
  have hPar : ParSt hL := GlobalTheory.T.parameter_statement_all hP hMt hL
  have hEta : SEta hL := GlobalTheory.StEta.sEta hP hL hPt
  have hFin := GlobalTheory.T.finiteness_of_localLanglands hW hD hP hL hA hEta (GlobalTheory.HeightCounting.Up.sXd_all hL)
  have hG := GlobalTheory.HeightCounting.UpPin.steps_pin hL 0
  refine ⟨GlobalTheory.T.reduction_to_local_langlands_A hP hA.pht hL, hMt, hRat, GlobalTheory.SCuspRows.sCusp_of_parSt hP hL hPar hRat, hG.1 (GlobalTheory.T.settingsFormsExistList_of_localLanglands hP hS hL 0),
    hG.2.1 (GlobalTheory.T.second_bound_of_primitive hP hS hL 0), hG.2.2.1 (GlobalTheory.T.moduliPointsExistList_of_localLanglands hP hS hL 0), GlobalTheory.T.series_cover_of_primitive hH.cover hCW hHM hP hS hL, hFin.1, fun c => ?_⟩
  exact ⟨GlobalTheory.T.settingsFormsExistList_of_localLanglands hP hS hL c, GlobalTheory.T.second_bound_of_primitive hP hS hL c, GlobalTheory.T.moduliPointsExistList_of_localLanglands hP hS hL c, hFin.2 c⟩

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightSetSaturatedOfHypsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unlocalized_saturated_state_of_hypA_hypH : HypA → HypH → ExistsUnlocalizedSaturatedState := by
  first | exact @GlobalTheory.HeightCounting.Up.w1Sat_of_hyps | exact GlobalTheory.HeightCounting.Up.w1Sat_of_hyps | (intros; apply GlobalTheory.HeightCounting.Up.w1Sat_of_hyps <;> assumption)
end

