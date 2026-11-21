-- shake: keep-all (pre-minimization imports restored: this file fails to elaborate under the minimized set)
import BuildAid.Leniency.Open
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.Imports
import Formalism.TameInertiaTowers.FinalGroup
import Formalism.HarderNarasimhan.StatementFrame
import Formalism.LatticeLocalGlobal.LatticeLocalGlobalOfGlobal
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaTallZero
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.SubspaceCounting.TopsChoiceSecondBound
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
import Formalism.SharpRestriction.DFam
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInducingCoeMatrix
import Formalism.RealPlaceAnalysis.IsRightTranslationIsometric
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
import Formalism.LocalRingCardinality.DataKerI
import Formalism.Statement
import Formalism.ZetaNonvanishingGeneralWeights
import Formalism.ProductFormula.StatementOCCM
import Formalism.SizeWindowBrackets.PowerBoundGivesRiemannHypothesis
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.BigCellConjI
import Formalism.YangianSpanCharacter.ModHypYangian
import Formalism.YangianSpanCharacter.YangianRTTProofs.MinusFrameIdentity
import Formalism.FormalDegreeBessel.FormalDegreeRatio.AdjointFunctionalHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop
import Formalism.HermitianLattices.HermitianLatticesProofs.ThetaBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.ExampleZ
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkowskiIILowerOf
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NPWDivision
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NPUnit
import Formalism.HermitianLattices.HermitianLatticesProofs.MajDual
import Formalism.HermitianLattices.HermitianLatticesProofs.OpBound
import Formalism.HermitianLattices.HermitianLatticesProofs.MajBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.NeighbourConstruct
import Formalism.HermitianLattices.ThetaLEuclid
import Formalism.HermitianLattices.DiscrFinite
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodUnramUnique
import Formalism.LatticeRigidity.HeightMin
import Formalism.HarderNarasimhan.StatementCor
import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
import Formalism.LogSumExpBounds.StatementE
import Formalism.LogSumExpBounds.CharacterSumPhase.KappaModulusHolds
import Formalism.LogSumExpBounds.CharacterSumPhase.DescEquivLiftEquiv
import Formalism.LogSumExpBounds.CharacterSumPhase.ZLiftAsm
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearCoefficients
import Formalism.NormUnitaryBounds.DetPolynomialWeights.LtSuccOfMemWeightCompositions
import Formalism.NormUnitaryBounds.DetPolynomialWeights.NormUnitary
import Formalism.NormUnitaryBounds.DetPolynomialWeights.NormMul
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Example
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VandermondeRatioHarmonic
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.OrbitSum
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Ipindep
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ChainScalar
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
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.FormalGroupWitt.ShiftSOneLetter
import Formalism.GL3MeanSquares.HookFormulaTorsion.ConditionIffDualEqFunctional
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourierCommutesHeckeScalar
import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral
import Formalism.GL3MeanSquares.GlobalBoundRefinementResults
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
import Formalism.LatticeRigidity.HeightMinimum.BlockEquationHolds
import Formalism.LatticeRigidity.HeightMinimum.ChebyshevLeadingCoeffHolds
import Formalism.LatticeRigidity.HeightMinimum.OneLeProdOfInt
import Formalism.LatticeRigidity.RecursionUnrestrictedFalse
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.LeadingMinorEqDetSubmatrix
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.SubgroupCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelProperties
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondVanishingOffRing
import Formalism.SobolevGaussianKernels.StatementCS
import Formalism.SobolevGaussianKernels.StatementNC
import Formalism.SobolevGaussianKernels.StatementMV
import Formalism.SobolevGaussianKernels.GaussianKernelBounds.HasDerivAtSphereChartLast
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
import Formalism.LogVandermondeBounds.LogVandermondeProofs.TaylorLogMetric
import Formalism.LogVandermondeBounds.LogVandermondeProofs.InertPrimeCountBound
import Formalism.LogVandermondeBounds.LogVandermondeProofs.RamifiedLatticeOperatorIdentity
import Formalism.LogVandermondeBounds.LogVandermondeProofs.MulSingleMulApplySelf
import Formalism.LogVandermondeBounds.LogVandermondeProofs.FourierIsometryOnNormKernel
import Formalism.GL3MeanSquares.GenusMassVolumeResults
import Formalism.GL3MeanSquares.FinalB
import Formalism.FockGram.FockGramProofs.FockSesq
import Formalism.FockGram.FockGramProofs.FockPerm
import Formalism.FockGram.FockGramProofs.DetSymPow
import Formalism.FockGram.FockGramProofs.HermitianTensorMulHermitian
import Formalism.FockGram.StatementSymPos
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.NormalisationIdentity
import Formalism.HermitianCurvature.StatementK
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLx
import Formalism.FlagUnipotentLattices.BlockMinorAbsoluteFromExplicit
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
import Formalism.FlagUnipotentLattices.QDetNegTranspose
import Formalism.FlagUnipotentLattices.HeightConditionFromCubic
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LanglandsParameterEquivariant
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionElement
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CovolumeIntegerLatticeEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandD
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GramEqConjTransposeMul
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandLA

set_option autoImplicit false

noncomputable section

open NumberField Matrix Filter Topology

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

def LatticeCommensurable : Prop :=
  ∀ (I : AutInst) (x : I.GA), ∃ m : ℕ, 1 ≤ m ∧
    (∀ u ∈ latSet I x, (m : I.E) • u ∈ I.L) ∧ ∀ u ∈ I.L, (m : I.E) • u ∈ latSet I x

def LatticeFinitelyGenerated : Prop :=
  ∀ (I : AutInst) (x : I.GA), ∃ M : Submodule (𝓞 I.E) (Fin I.n → I.E),
    M.FG ∧ (M : Set (Fin I.n → I.E)) = latSet I x

def ExistsBoundedBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n j : ℕ) (M B : Submodule (𝓞 K) (Fin n → K))
    (b : Fin j → Fin n → K), M.FG → B ≤ M → LinearIndependent K b → (∀ a, b a ∈ B) →
    (B : Set (Fin n → K)) ⊆ Submodule.span K (Set.range b) →
    Finite (B ⧸ (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype)

def SubmoduleExists : Prop :=
  ∀ I : AutInst, 1 ≤ I.n → ∀ x : I.GA, Nonempty (Sub I x)

def LatticeRightInvariant : Prop :=
  ∀ (I : AutInst) (x : I.GA) (y : I.Ginf) (k : I.Gf), k ∈ I.Kset → latSet I (x * (y, k)) = latSet I x

def GramDistortionBound : Prop :=
  ∀ (n j : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin j) ℂ) (a b : ℝ), 0 ≤ a →
    (∀ w : Fin n → ℂ, a * ∑ i, ‖w i‖ ^ 2 ≤ ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ∧
      ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤ b * ∑ i, ‖w i‖ ^ 2) →
    a ^ j * (Cᴴ * C).det.re ≤ ((Y * C)ᴴ * (Y * C)).det.re ∧
      ((Y * C)ᴴ * (Y * C)).det.re ≤ b ^ j * (Cᴴ * C).det.re

def SizesLocallyComparable : Prop :=
  ∀ (I : AutInst) (x : I.GA) (r : ℝ), 1 < r → ∀ᶠ x' in 𝓝 x,
    (∀ s : Sub I x, ∃ s' : Sub I x', size I s' ≤ r * size I s) ∧
      ∀ s' : Sub I x', ∃ s : Sub I x, size I s ≤ r * size I s'

def InfimumContinuousFamily : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (S : X → Type) (g : ∀ x, S x → ℝ),
    (∀ x, Nonempty (S x)) → (∀ x s, 0 ≤ g x s) →
    (∀ x (r : ℝ), 1 < r → ∀ᶠ x' in 𝓝 x,
      (∀ s, ∃ s', g x' s' ≤ r * g x s) ∧ ∀ s', ∃ s, g x s ≤ r * g x' s') →
    Continuous fun x => min (1 / 2 : ℝ) (⨅ s, g x s)

def MinkowskiFirstTheorem : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L],
      ∃ u ∈ L, u ≠ 0 ∧ ‖u‖ ^ 2 ≤ C * ZLattice.covolume L ^ ((2 : ℝ) / d)

def MinkowskiSubmodule : Prop :=
  ∀ I : AutInst, ∃ c : ℝ, 0 < c ∧ ∀ (x : I.GA) (s : Sub I x), ∃ u ∈ s.B, u ≠ 0 ∧
    ∑ v, ∑ i, ‖coordV I x v u i‖ ^ 2 ≤ c * size I s ^ 2

def LatticeVectorsBoundedBelow : Prop :=
  ∀ (I : AutInst) (x : I.GA), ∃ l : ℝ, 0 < l ∧ ∀ u ∈ latSet I x, u ≠ 0 →
    l ≤ ∑ v, ∑ i, ‖coordV I x v u i‖ ^ 2

def HeightsPositive : Prop :=
  ∀ (I : AutInst) (x : I.GA) (s : Sub I x), 0 < ht I s

end Formalism.L2.SG.Pf.Tau
