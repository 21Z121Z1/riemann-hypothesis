-- shake: keep-all (pre-minimization imports restored: this file fails to elaborate under the minimized set)
import BuildAid.Leniency.Open
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Formalism.TameInertiaTowers.FinalGroup
import Formalism.HarderNarasimhan.StatementFrame
import Formalism.LatticeLocalGlobal.LatticeLocalGlobalOfGlobal
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaTallZero
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.SubspaceCounting.TopsChoiceSecondBound
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInducingCoeMatrix
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.IsRightTranslationIsometric
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Formalism.SharpRestriction.DFam
import Formalism.LocalRingCardinality.DataKerI
import Formalism.Statement
import Formalism.ZetaNonvanishingGeneralWeights
import Formalism.ProductFormula.StatementOCCM
import Formalism.SizeWindowBrackets.PowerBoundGivesRiemannHypothesis
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.OrbitSum
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Ipindep
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ChainScalar
import Formalism.HermitianLattices.HermitianLatticesProofs.ThetaBasic
import Formalism.LatticeTheta.ThetaShiftInversion
import Formalism.HermitianLattices.HermitianLatticesProofs.ExampleZ
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkowskiIILowerOf
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NPWDivision
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NPUnit
import Formalism.HermitianLattices.HermitianLatticesProofs.DualOrthSum
import Formalism.HermitianLattices.HermitianLatticesProofs.MajDual
import Formalism.HermitianLattices.HermitianLatticesProofs.OpBound
import Formalism.HermitianLattices.HermitianLatticesProofs.MajBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.NeighbourConstruct
import Formalism.HermitianLattices.ThetaLEuclid
import Formalism.HermitianLattices.DiscrFinite
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodUnramUnique
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.EigenSwap
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.FFPlancherel
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.DetSwap
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrderOfSignGroupDvdTwo
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import Formalism.CMTypeGalois.CMTypeFrobenius.TypesA
import Formalism.CMTypeGalois.CMTypeFrobenius.TypesB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
import Formalism.LocalRingCardinality.HostCls
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Example
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwist
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckebasic
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActionLevelMemHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AutomorphicFormsDecompositionHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Nabladual
import Formalism.SatakeDualWeyl.NablaRepApply
import Formalism.SatakeDualWeyl.DualWeylRepApply
import Formalism.ThickAverageLoss.ThickAverageProofs.Balance
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.RankGapBounds.RankGapProofs.WeightedMeanData
import Formalism.SizeWindowBrackets.ChainSlopeWindows.CorollaryModelSideCondition
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe
import Formalism.LocalToGlobal.GlobalTheory.GL5.VolumeAndDsigCompatOfCompatibleData
import Formalism.LogVandermondeBounds.LogVandermondeProofs.TaylorLogMetric
import Formalism.LogVandermondeBounds.LogVandermondeProofs.InertPrimeCountBound
import Formalism.LogVandermondeBounds.LogVandermondeProofs.RamifiedLatticeOperatorIdentity
import Formalism.LogVandermondeBounds.LogVandermondeProofs.MulSingleMulApplySelf
import Formalism.LogVandermondeBounds.LogVandermondeProofs.FourierIsometryOnNormKernel
import Formalism.GL3MeanSquares.GenusMassVolumeResults
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.FormalGroupWitt.ShiftSOneLetter
import Formalism.GL3MeanSquares.HookFormulaTorsion.ConditionIffDualEqFunctional
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourierCommutesHeckeScalar
import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral
import Formalism.GL3MeanSquares.GlobalBoundRefinementResults
import Formalism.GL3MeanSquares.FinalB
import Formalism.FockGram.FockGramProofs.FockSesq
import Formalism.FockGram.FockGramProofs.FockPerm
import Formalism.FockGram.FockGramProofs.DetSymPow
import Formalism.FockGram.FockGramProofs.HermitianTensorMulHermitian
import Formalism.FockGram.StatementSymPos
import Formalism.LocalToGlobal.GlobalTheory.GL5.TheoremThreeAllUnitary
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCompactOpenUnitsSubgroupContinuousSqrt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNsmulIntegersMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.QuotientMetricDivisors.ProdFormula
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

theorem adicCompletionIntegers_norm_eq_one_of_mul_eq_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletionIntegers F) (h : x * y = 1) : ‖(x : Fv F v)‖ = 1 := by
  have hx : ‖(x : Fv F v)‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).mpr x.2
  have hy : ‖(y : Fv F v)‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).mpr y.2
  have hxy : ‖(x : Fv F v)‖ * ‖(y : Fv F v)‖ = 1 := by
    rw [← norm_mul]
    have : ((x : Fv F v) * (y : Fv F v)) = 1 := by
      have := congrArg (fun z : v.adicCompletionIntegers F => (z : Fv F v)) h
      simpa using this
    rw [this, norm_one]
  have h0 := norm_nonneg (x : Fv F v)
  have h0' := norm_nonneg (y : Fv F v)
  nlinarith

end GlobalTheory
