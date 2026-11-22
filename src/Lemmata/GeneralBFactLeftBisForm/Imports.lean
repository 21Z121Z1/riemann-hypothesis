import Mathlib
import Formalism.MahlerMeasure.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.ObjSeg
import Formalism.SharpRestriction.GrowthBounds.Bundle0001
import Formalism.MahlerMeasure.Bundle0008
import Formalism.MahlerMeasure.Bundle0009
import Formalism.MahlerMeasure.MahlerMeasureProofs.Bundle0004
import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalRingCardinality.DataCoeff
import Formalism.LocalRingCardinality.DataArith
import Formalism.LocalRingCardinality.DataKernels
import Formalism.LocalRingCardinality.DataRows
import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.LocalRingCardinality.DataCD
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt
import Formalism.MahlerMeasure.MahlerMeasureProofs.Bundle0003
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInv
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Bundle0001
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Discharge
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjection
import Formalism.PolynomialDimension.ChainOrderLetters
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.StatementB
import Formalism.SharpRestriction.GrowthBounds.RootWeights.SumFinsuppAntidiagEqSumPiFinset
import Formalism.FrobeniusOrbits.Bundle0001
import Formalism.FrobeniusOrbits.Bundle0002
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.CoboundaryTransfers.Statement
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementC
import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementF
import Formalism.ThetaLogCoordinates.FockResolutionOnto.MulEarlyModP
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.OmegaInjectiveHolds
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.FinalLL
import Formalism.GrowthSums.LemmaATwoFactList
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.Statement
import Formalism.FormalDegreeBessel.StatementG
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementA
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RaisingKeepsEarlyLetters
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeKeepsSpaceHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.Bundle0002
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementG
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.LatticeTheoremOfDischarge
import Formalism.ThetaLogCoordinates.PartnerDischarge.StatementPW
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PairStep
import Formalism.FrobeniusOrbits.Statement
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0001
import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam
import Formalism.TameInertiaTowers.FinalGroup
import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
import Formalism.TameInertiaTowers.CentralOrderTwo.Bundle0002
import Formalism.FormalDegreeBessel.Bundle0001
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0002
import Formalism.RealPlaceAnalysis.StatementU
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.RealPlaceAnalysis.Bundle0002
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0005
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
import Formalism.SharpRestriction.GrowthBounds.RootWeights.TwistSubEqMatrixSubst
import Formalism.RealPlaceAnalysis.Bundle0001

namespace Bl.general_b_fact_left_bis_form

theorem goal1 :
  ∀ {O : Type} [inst : CommRing.{0} O] [inst_1 : IsDomain.{0} O] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} O V] [inst_4 : Module.{0, 0} (Formalism.MainNotions.G.KK.{0} O) V]
  [IsScalarTower.{0, 0, 0} O (Formalism.MainNotions.G.KK.{0} O) V] (M : Submodule.{0, 0} O V) (y : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} (Formalism.MainNotions.G.KK.{0} O) (SetLike.coe.{0, 0} M)) y →
    Exists.{1} fun (s : O) ↦ And (Ne.{1} s 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} s y))  := by
  intro O _ _ V _ _ _ _ M y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : (s * t) • (x + z) = t • (s • x) + s • (t • z) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [e]
    exact M.add_mem (M.smul_mem t hsx) (M.smul_mem s htz)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors O) a
    refine ⟨(d : O) * s, mul_ne_zero (nonZeroDivisors.ne_zero d.2) hs, ?_⟩
    have e : ((d : O) * s) • (a • x) = n • (s • x) := by
      rw [mul_comm, mul_smul, ← algebraMap_smul (Formalism.MainNotions.G.KK O) (d : O) (a • x), smul_smul,
        mul_comm (algebraMap O (Formalism.MainNotions.G.KK O) (d : O)) a]
      simp only at hnd
      rw [hnd, algebraMap_smul]
      exact smul_comm s n x
    rw [e]
    exact M.smul_mem n hsx

end Bl.general_b_fact_left_bis_form
