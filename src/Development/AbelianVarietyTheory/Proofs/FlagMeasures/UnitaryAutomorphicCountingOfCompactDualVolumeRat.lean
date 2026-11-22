import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.RowsFinC
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0152
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0174
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0344
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0414
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0394
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0347
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0402
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0198
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0370
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0466
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0459
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0454

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CountFinal

theorem countingTheorem_of_volumeStep :
    GlobalTheory.FlagMeas.VolumeStep → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  intro hV
  have hDec : GlobalTheory.DSId.DecGap := GlobalTheory.T.lowestKType_decayGap_of_compressionFormulaGap GlobalTheory.T.lowestKType_compressionFormula_of_strictLowestKType
  have hPt : GlobalTheory.Deep.PtBound := GlobalTheory.Deep.ptBound_of_decGap hDec
  have hAbs : GlobalTheory.FlagMeas.AbsoluteVolume := GlobalTheory.T.hermAbsoluteVolumeBound_of_volume_ratio_induction hV
  have hFM : GlobalTheory.FlagMeas.FlagMeasureBound := GlobalTheory.T.isotropicFlagProbabilityBound_of_volumeRatio hV
  have hFin := GlobalTheory.T.finiteDimensional_rowsSpace_discreteSeriesCount hDec hAbs
  have hNear := GlobalTheory.NearMod.nearModerate hFM GlobalTheory.T.flag_explicit_constant_le_exp_neg_half GlobalTheory.NearElement.near_unipotent hPt
  have hFar := GlobalTheory.T.farTermsModerateRegion_of_flagBound hFM (GlobalTheory.FarTerms.farBound_of_ptBound hPt)
  have hRare := GlobalTheory.FlagRareProof.flagRare_of_nonzeroFlagBound (GlobalTheory.T.nonzeroFlagProbabilityBound_of_volumeRatioInduction hV)
  have hDeep := GlobalTheory.T.deepRegion_kernelDiagonal_bound hAbs (GlobalTheory.T.deepPointKernelBound_of_pointwiseBound hPt hFin)
  exact GlobalTheory.T.discreteSeries_counting_of_finite_and_bounds hFin hFM hPt hNear hFar hRare hDeep

end GlobalTheory.CountFinal
