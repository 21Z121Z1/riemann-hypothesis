import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0848
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0844
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0825
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StatementCOfCasselmanWallach
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricZeroConditionAllStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_zero_condition_all : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → RL.At (prmR N S Γ) R1.DivisorConditionAtBundlePoints → RL.At (prmR N S Γ) RL.Row_tie → RL.At (prmR N S Γ) S0.GeometricWeakCompatibility := by
  first | exact @GlobalTheory.Fc.GeoZeroAt.row_geo0_at | exact GlobalTheory.Fc.GeoZeroAt.row_geo0_at | (intros; apply GlobalTheory.Fc.GeoZeroAt.row_geo0_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StartStateUntwistedEmptyLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
open GlobalTheory.Mem.R3.Tr
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.Mem.R3.Rw.Bare

set_option maxHeartbeats 4000000 in

theorem hasBare_sat : HypA → HypH → DatExt0 → StepW Start fun K B f T w => ∃ (P : Pre2 K w) (x : St P), (T = TwDat.untw B T.pl → ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt) ∧ IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0 := by
  intro hA hH hE
  have holdsW : WeightCaseCondition := GlobalTheory.T.weight_set_residue_characteristic hH.h1 hH.h2 hH.h3 hH.multW
  have holdsL : LowerUnitaryCaseCondition := GlobalTheory.T.holds_of_multiplicity_equal hH.h1 hH.h2 hH.h3 hH.multL
  have datS : DatExS := GlobalTheory.T.exists_fineAdelicDatum_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10
  have hW := GlobalTheory.T.untwisted_adelic_data_saturated_over_fixed_field hH.h1.q12 datS holdsL hE
  have hPr := GlobalTheory.T.constructionStartingChoices_of_fine_adelicData hA.a8 hA.a9 hA.a10 hA.a6 holdsW
  have pS : StepW Start Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h.1
  have iS : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have s1 : StepW Start fun K B f T w => Pinned K B f T w ∧ ∃ P : Pre2 K w, (T = TwDat.untw B T.pl →
      ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt) := by
    refine (iS.and ((pS.trans hW).and hPr)).trans (StepW.of_all fun K B f T w _ _ h => ?_)
    obtain ⟨⟨hPin, hSupp, -⟩, hU, hP⟩ := h
    by_cases hT : T = TwDat.untw B T.pl
    · obtain ⟨Z, hX, z, g, gr, ga, ka, hF, hsub, hpsi, hsat⟩ := hU hT
      obtain ⟨P, hZ, hWt, -⟩ := hP Z hX z g gr ga ka hF hsub hpsi
      refine ⟨hPin, P, fun _ => ?_⟩
      rw [hWt, hZ]
      exact hsat
    · rcases hSupp with h | hG
      · exact absurd h hT
      obtain ⟨Z, hX, z, g, gr, ga, ka, ex, ig, core, std, hsub, hpsi⟩ := hG
      obtain ⟨P, -, -, -⟩ := hP Z hX z g gr ga ka ⟨ex, ig, core, std⟩ hsub hpsi
      exact ⟨hPin, P, fun h => absurd h hT⟩
  have hQ : StepW (fun K B f T w => Pinned K B f T w ∧ ∃ P : Pre2 K w, (T = TwDat.untw B T.pl →
      ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt)) (pinAnd HasPk) :=
    StepW.of_all fun _ _ _ _ _ _ _ h => ⟨h.1, ⟨h.2.choose⟩⟩
  refine s1.trans ((StepW.of_all fun _ _ _ _ _ _ _ h => h).and (hQ.trans GlobalTheory.T.localizationFreeStage_trueGroup_columnChoiceStep) |>.trans
    (StepW.of_all fun K B f T w hO _ h => ?_))
  obtain ⟨⟨-, P, hsat⟩, hN⟩ := h
  obtain ⟨N, hEm, hG, hN⟩ := hN P
  obtain ⟨V, hV, -, -, hη, -, hB⟩ := exists_divStage_of_pk B w.C (Gc B w.px) P.q.p P.q.e P.q.W₀ P.q.n (fun _ _ => 0)
    (fun _ _ => le_rfl) (frames_unit P.q.t) (fun u => ((w.C.fm u).lat 0).L) (fun _ => 0) (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl) P.Z₀.G.cd hO
    (GlobalTheory.Mem.Df.cols_pos w.I w.ok w.pins w.l P.hX) (rows_le P.q.t)
  obtain ⟨x, hx⟩ := GlobalTheory.T.fittingLaterStages_row_is_constructionState hA.a8 hA.a9 hA.a10 hA.a6 K B f T w P ⟨_, _, V, S, N, P.Z₀.G⟩
    ⟨hV, hG, (hN V S P.Z₀.G).1, (hN V S P.Z₀.G).2⟩ rfl hη (fun hr => hB hr)
  refine ⟨P, x, hsat, ?_⟩
  exact Eq.mpr (congrArg (fun o : P.q.Over => IsEmpty o.N.nd.Loc ∧ ∀ j v, o.η j v = 0) hx) ⟨hEm, fun _ _ => rfl⟩

end GlobalTheory.Mem.R3.Rw.Bare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StatementCOfCasselmanWallachStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.statement_c_of_casselman_wallach : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SCk hL := by
  first | exact @GlobalTheory.LevCmp.choices_exist_for | exact GlobalTheory.LevCmp.choices_exist_for | (intros; apply GlobalTheory.LevCmp.choices_exist_for <;> assumption)
end

