-- shake: keep-all (pre-minimization imports restored: this file fails to elaborate under the minimized set)
import BuildAid.Leniency.Variable
import BuildAid.Leniency.Open
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PartFiveExplicitOfPropositions
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Formalism.TameInertiaTowers.FinalGroup
import Formalism.HarderNarasimhan.StatementFrame
import Formalism.LatticeLocalGlobal.LatticeLocalGlobalOfGlobal
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaTallZero
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
import Formalism.SharpRestriction.DFam
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInducingCoeMatrix
import Formalism.RealPlaceAnalysis.IsRightTranslationIsometric
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
import Formalism.LocalRingCardinality.DataKerI
import Formalism.ZetaNonvanishingGeneralWeights
import Formalism.ProductFormula.StatementOCCM
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.OrbitSum
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Ipindep
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ChainScalar
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
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.EigenSwap
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.FFPlancherel
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.DetSwap
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrderOfSignGroupDvdTwo
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import Formalism.CMTypeGalois.CMTypeFrobenius.TypesA
import Formalism.CMTypeGalois.CMTypeFrobenius.TypesB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Example
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckebasic
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActionLevelMemHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AutomorphicFormsDecompositionHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Nabladual
import Formalism.SatakeDualWeyl.NablaRepApply
import Formalism.SatakeDualWeyl.DualWeylRepApply
import Formalism.SizeWindowBrackets.ChainSlopeWindows.CorollaryModelSideCondition
import Formalism.RankGapBounds.RankAndGapBounds
import Formalism.LogFactorialBounds.LocalFactorSplitDv
import Formalism.ThickAverageLoss.ParametersAveragedDifferenceBound
import Development.AutomorphicArithmetic.ConductorsKronecker.kronecker
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Formalism.RankGapBounds.UniformMeanBound
import Formalism.RankGapBounds.RankGapProofs.UniformMeanTopLine
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PChain
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Window
import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.ConductorsKronecker.ChCond
import ReciprocityTheory.BasicDefinitions.ExistsUnique
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.GrowthSums.FactorialBaseGrowth.Coarse
import Formalism.GrowthSums.FactorialBaseGrowth.QuadraticExponentIdentity
import Formalism.GrowthSums.FactorialBaseGrowth.LogCoef
import Formalism.GrowthSums.FactorialBaseGrowth.Length
import Formalism.GrowthSums.FactorialBaseGrowth.KapPrime
import Formalism.GrowthSums.FactorialBaseGrowth.PathBasisOfCount
import Formalism.SharpRestriction.GrowthBounds.Imports
import Formalism.PolynomialDimension.MultinomialDepth.FrameMultinomialBoundHolds
import Formalism.MahlerMeasure.StatementB
import Formalism.MahlerMeasure.WithMargin
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfPartStatementsWithDelta
import Formalism.LogVandermondeBounds.LogVandermondeProofs.TaylorLogMetric
import Formalism.LogVandermondeBounds.LogVandermondeProofs.InertPrimeCountBound
import Formalism.GL3MeanSquares.PrimeOrderRamificationResults
import Formalism.GL3MeanSquares.TraceIntegralityResults
import Formalism.LocalToGlobal.HermitianColumns.StepLevelQ
import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.BigCellConjI
import Formalism.YangianSpanCharacter.ModHypYangian
import Formalism.YangianSpanCharacter.YangianRTTProofs.MinusFrameIdentity
import Formalism.FormalDegreeBessel.FormalDegreeRatio.AdjointFunctionalHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VandermondeRatioHarmonic
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.FormalGroupWitt.ShiftSOneLetter
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
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IntegralityOfCommutation
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.FamilyPartFiveExplicitHolds
import Formalism.LocalToGlobal.GlobalTheory.GL5.VolumeAndDsigCompatOfCompatibleData
import Formalism.LocalToGlobal.GlobalTheory.GL5.TheoremThreeAllUnitary

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory

def MassRatioUnderVolume (D : D7) : Prop := StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D

def GenusMassUnderVolume (D : D7) : Prop := StandardLattice.VolTie D → StandardLattice.DefiniteVolumeEqMass D

theorem mass_ratio_unfolded_of_theorem_two (D : D7) (h : StandardLattice.Conclusion2 D) : StandardLattice.VolumeRatio₂ D := by
  let _ := D.host.cmStar
  intro W P Q hS hsig hr s hs
  obtain ⟨x, hx, W', ι, h1, h2, h3, h4, h5⟩ := h W P Q hS hsig hr s hs
  refine ⟨x, hx, W', ι, h1, h2, h3, h4, ?_⟩
  have key := Formalism.HermitianLattices.GenusMassVolumes.global_arithmetic_identity D.R.f W.rank D.host.v (Formalism.HermitianLatticesTheory.lValEta D.host.E W.rank)
    (by omega) (StandardLattice.host_v_pos D) (StandardLattice.lVal_pos D _ (by omega))
  rw [StandardLattice.mass_ratio_eq] at h5
  have e : D.vol W / D.vol W' =
      (((2 * Real.pi) ^ W.rank / ((W.rank - 1).factorial : ℝ)) ^ D.R.f *
        ((2 * D.host.v) ^ D.R.f) ^ ((1 : ℝ) / 2 - W.rank) / Formalism.HermitianLatticesTheory.lValEta D.host.E W.rank)⁻¹ :=
    h5.trans key.symm
  calc D.vol W' / D.vol W = (D.vol W / D.vol W')⁻¹ := (inv_div _ _).symm
    _ = _ := by rw [e, inv_inv]

theorem mass_ratio_unfolded_iff (D : D7) : StandardLattice.VolumeRatio₂ D ↔ StandardLattice.Conclusion2 D :=
  ⟨StandardLattice.volumeMass_of_unfolding D, mass_ratio_unfolded_of_theorem_two D⟩

theorem mass_ratio_of_true_volume_ratio (D : D7) (hV : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolRatioTrue D) : MassRatioUnderVolume D := by
  intro hT
  refine mass_ratio_unfolded_of_theorem_two D ?_
  intro W P Q hW hs hr s hsP
  obtain ⟨x, hx, W', ι, hι, hrg, hW', hs', hrat⟩ := hV W P Q hW hs hr s hsP
  refine ⟨x, hx, W', ι, hι, hrg, hW', hs', ?_⟩
  have hs'' : ∀ τ, W'.sig τ = ((if s then P - 1 else P), (if s then Q else Q - 1)) := by
    intro τ
    rw [hs' τ]
    cases s <;> simp
  obtain ⟨⟨μ, hμ⟩, h1⟩ := hT W P Q hW hs
  obtain ⟨⟨𝓕, h𝓕⟩, h2⟩ := h1 μ hμ
  obtain ⟨⟨μ', hμ'⟩, h1'⟩ := hT W' _ _ hW' hs''
  obtain ⟨⟨𝓕', h𝓕'⟩, h2'⟩ := h1' μ' hμ'
  have e1 : μ 𝓕 = ENNReal.ofReal (D.vol W) := h2 𝓕 h𝓕
  have e2 : μ' 𝓕' = ENNReal.ofReal (D.vol W') := h2' 𝓕' h𝓕'
  have e := hrat μ 𝓕 μ' 𝓕' hμ h𝓕 hμ' h𝓕'
  rw [e1, e2, ENNReal.toReal_ofReal (D.vol_pos W).le, ENNReal.toReal_ofReal (D.vol_pos W').le] at e
  exact e

theorem genus_mass_of_class_decomposition (D : D7) (hG : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassStd D)
    (hC : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.DefClassDecomp D) : GenusMassUnderVolume D :=
  fun hT => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT hG hC

theorem auxb_of_massRatio_of_genusMass_of_volTie (D : D7) (hU : MassRatioUnderVolume D) (hv : GenusMassUnderVolume D) (hT : StandardLattice.VolTie D) : StandardLattice.MassRatio₂ D :=
  StandardLattice.massRatio_of_definiteVolume D (StandardLattice.volumeMass_of_unfolding D (hU hT)) (hv hT)

theorem volumeY0EqualsMass_of_massRatio_of_genusMass (D : D7) (hU : MassRatioUnderVolume D) (hv : GenusMassUnderVolume D) (hT : StandardLattice.VolTie D) : StandardLattice.BaseVolumeEqualsMass D :=
  StandardLattice.volumeY0EqualsMass_of_aux2v D (StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU hT)) (hv hT))

theorem volTie_of_realTied (D : D7) (h : Formalism.L2.Theta.RealTied D) : StandardLattice.VolTie D := by
  intro W P Q hW hs
  have hv := h.vol W hW
  simp only [hs] at hv
  exact hv

variable {eps : ℝ}

theorem mass_ratio_family_of_volume (Fm : FamP eps) (hU : ∀ D, MassRatioUnderVolume D) (hv : ∀ D, GenusMassUnderVolume D)
    (tVol : flipTwoThree.fam0 Fm StandardLattice.VolTie) : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂ := by
  obtain ⟨x0, hx⟩ := tVol
  exact ⟨x0, fun x h1 h2 i => auxb_of_massRatio_of_genusMass_of_volTie _ (hU _) (hv _) (hx x h1 h2 i)⟩

theorem volume_mass_family_of_volume (Fm : FamP eps) (hU : ∀ D, MassRatioUnderVolume D) (hv : ∀ D, GenusMassUnderVolume D)
    (tVol : flipTwoThree.fam0 Fm StandardLattice.VolTie) : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass := by
  obtain ⟨x0, hx⟩ := tVol
  exact ⟨x0, fun x h1 h2 i => volumeY0EqualsMass_of_massRatio_of_genusMass _ (hU _) (hv _) (hx x h1 h2 i)⟩

theorem tVol_of_real (Fm : FamP eps) (h : flipTwoThree.fam0 Fm Formalism.L2.Theta.RealTied) : flipTwoThree.fam0 Fm StandardLattice.VolTie := by
  obtain ⟨x0, hx⟩ := h
  exact ⟨x0, fun x h1 h2 i => volTie_of_realTied _ (hx x h1 h2 i)⟩

theorem linkGLOBAL7_tiedV (Fm : FamP eps) (Cabs CH C0 C5 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)
    (hU : ∀ D, MassRatioUnderVolume D) (hv : ∀ D, GenusMassUnderVolume D) (tVol : flipTwoThree.fam0 Fm StandardLattice.VolTie)
    (h3 : flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap)
    (hZa : flipTwoThree.FamilySlopeLowerOpenPart Fm) (hZb : flipTwoThree.FamilySlopeMaxOpenPart Fm C5)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) (hμ : FamU Fm product_first_zeroth_parts.SlopeLine)
    (hI : FamU Fm LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero) (hB : FamU Fm LocalLatticeBases.SecondBranchInclusionLength) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 := by
  exact linkGLOBAL7_min Fm Cabs CH C0 C5 hCabs hCH hC0 (mass_ratio_family_of_volume Fm hU hv tVol) (volume_mass_family_of_volume Fm hU hv tVol) h3
    hZa hZb tCV hW hμ hI hR hB

end Formalism.MainNotions.RT

end
