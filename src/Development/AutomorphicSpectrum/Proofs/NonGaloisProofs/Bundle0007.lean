import Mathlib
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BlochKatoCokernelOfDualityEuler

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Adm8AllRecordsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSituation_adm8_forall : ∀ D : D7, LocalSituation.adm8 D := by
  first | exact @GlobalTheory.CompanionTheory.TateDualRow.blochKato_dimFormula_all_finiteExt_coeffField | exact GlobalTheory.CompanionTheory.TateDualRow.blochKato_dimFormula_all_finiteExt_coeffField | (intros; apply GlobalTheory.CompanionTheory.TateDualRow.blochKato_dimFormula_all_finiteExt_coeffField <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BlochKatoCokernelOfDualityEulerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_cokernel_of_duality_euler : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), bkACore ((D.loc l).PD K) → bkBCore ((D.loc l).PD K) → LocalSituation.bkC ((D.loc l).PD K) := by
  first | exact @GlobalTheory.CompanionTheory.BKTorsion.main | exact GlobalTheory.CompanionTheory.BKTorsion.main | (intros; apply GlobalTheory.CompanionTheory.BKTorsion.main <;> assumption)
end

