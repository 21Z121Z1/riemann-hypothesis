import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0519
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BlochKatoDimensionRightExact
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.FontaineBoundsAllRecords

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Adm8AllRecords
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

namespace GlobalTheory.CompanionTheory.TateDualRow

theorem blochKato_dimFormula_all_finiteExt_coeffField : ∀ D : D7, LocalSituation.adm8 D := GlobalTheory.TateDualFil.main

end GlobalTheory.CompanionTheory.TateDualRow
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BlochKatoDimensionRightExactStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_dimension_rightExact : ∀ D : D7, LocalSituation.adm5 D → LocalSituation.adm6 D → LocalSituation.adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), LocalSituation.bkADim ((D.loc l).PD K) ∧ LocalSituation.bkARightExact ((D.loc l).PD K) := by
  first | exact @GlobalTheory.CompanionTheory.BKDim.bkADim_and_bkARightExact | exact GlobalTheory.CompanionTheory.BKDim.bkADim_and_bkARightExact | (intros; apply GlobalTheory.CompanionTheory.BKDim.bkADim_and_bkARightExact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.FontaineBoundsAllRecordsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSituation_adm7_of_D7 : ∀ D : D7, LocalSituation.adm7 D := by
  first | exact @GlobalTheory.CompanionTheory.Fontaine.adm7_all | exact GlobalTheory.CompanionTheory.Fontaine.adm7_all | (intros; apply GlobalTheory.CompanionTheory.Fontaine.adm7_all <;> assumption)
end

