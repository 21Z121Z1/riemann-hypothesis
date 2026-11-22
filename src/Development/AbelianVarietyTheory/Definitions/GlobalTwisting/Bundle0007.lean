import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
section
namespace GlobalTheory.Fc.S0

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure HypothesesU : Prop where
  clozelCohomological : GlobalTheory.Published.ClozelCohomological
  greenCuspidal : GlobalTheory.Published.GreenCuspidal
  cohomologicalCsdTempered : GlobalTheory.Published.CohomologicalCsdTempered
  heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter
  chebotarevDegreeOne : GlobalTheory.Published.ChebotarevDegreeOne
  discreteSpectrumGL : GlobalTheory.Published.DiscreteSpectrumGL
  galoisRepOfPolarizedCuspidal : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal
  baseChangeDefiniteUnitary : GlobalTheory.Published.BaseChangeDefiniteUnitary
  bhattScholzeCrystallineLattices : GlobalTheory.Published.BhattScholzeCrystallineLattices
  heckeLAdicCharacterAbove : GlobalTheory.Published.HeckeLAdicCharacterAbove
  cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay
  weilSiegelFormulaUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary
  siegelWeilUnitaryConvergent : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  doublingMethod : GlobalTheory.Published.DoublingMethod
  unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL
  bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual
  bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration
  unlinkedProductIrreducible : GlobalTheory.Published.UnlinkedProductIrreducible
  depthZeroJacquetInjective : GlobalTheory.Published.DepthZeroJacquetInjective
  howeDualityGL : GlobalTheory.Published.HoweDualityGL
  jacquetShalika : GlobalTheory.Published.JacquetShalika
  automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL
  localGlobalAboveL : GlobalTheory.Published.LocalGlobalAboveL
  regularAlgebraicPurity : GlobalTheory.Published.RegularAlgebraicPurity
  globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity
  heckeLAdicParameterAbove : GlobalTheory.Published.HeckeLAdicParameterAbove
  deRhamPotSemistable : GlobalTheory.Published.DeRhamPotSemistable
  harishChandraFinite : GlobalTheory.Published.HarishChandraFinite
  greenRegularCharacters : GlobalTheory.Published.GreenRegularCharacters
  zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing
  depthZeroInertia : GlobalTheory.Published.DepthZeroInertia
  rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt
  rayCharacterArtin : GlobalTheory.Published.RayCharacterArtin
  genericUnitaryDualGL : GlobalTheory.Published.GenericUnitaryDualGL
  standardCosocleGL : GlobalTheory.Published.StandardCosocleGL
  cheb : GlobalTheory.TwSys.Cheb
  discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover
  harishChandraModules : GlobalTheory.Published.HarishChandraModules
  casselmanWallach : GlobalTheory.Published.CasselmanWallach
  weilRepresentationUnitaryPair : GlobalTheory.Published.WeilRepresentationUnitaryPair
  discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists
  discreteSeriesClassification : GlobalTheory.Published.DiscreteSeriesClassification
  strongApproxSU : GlobalTheory.Published.StrongApproxSU
  siegelWeilUnitaryConvergent2 : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent
  harishChandraAnalyticity : GlobalTheory.Published.HarishChandraAnalyticity
  cuspTraceClass : GlobalTheory.Published.CuspTraceClass
  dixmierMalliavinFactorisation : GlobalTheory.Published.DixmierMalliavinFactorisation
  flathFactorisation : GlobalTheory.Published.FlathFactorisation
  pseudoCoefficientUpq : GlobalTheory.Published.PseudoCoefficientUpq
  harishChandraCharacters : GlobalTheory.Published.HarishChandraCharacters
  langlandsClassification : GlobalTheory.Published.LanglandsClassification
  labesseWaldspurger : GlobalTheory.Published.LabesseWaldspurger
  cMCurveGoodOutsidePrimeSt : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt
  weberRayFieldSt : GlobalTheory.Published.WeberRayFieldSt
  discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists
  besselUniquenessReal : GlobalTheory.Published.BesselUniquenessReal
  siegelWeilUnitarySchrodinger : GlobalTheory.Published.SiegelWeilUnitarySchrodinger
  siegelEisensteinContinuation : GlobalTheory.Published.SiegelEisensteinContinuation
  siegelEisensteinSimplePole : GlobalTheory.Published.SiegelEisensteinSimplePole
  schurOrthogonalitySquareIntegrable : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
  regularisedSiegelWeilFirstTerm : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  toHypothesesX : GlobalTheory.NRows.HypothesesX
  nLink : GlobalTheory.NLink.Hypotheses₂
  depthZeroWild' : GlobalTheory.Published.DepthZeroWild
  depthZeroSupport' : GlobalTheory.Published.DepthZeroSupport
  localFiniteness : ReciprocityTheory.Gal.LocalFiniteness
  localTateDuality : ReciprocityTheory.Gal.LocalTateDuality
  localEulerChar : ReciprocityTheory.Gal.LocalEulerChar

theorem Hypotheses2.toU (P : Hypotheses2) : HypothesesU :=
  ⟨P.clozelCohomological, P.greenCuspidal, P.cohomologicalCsdTempered, P.heckeLAdicCharacter, P.chebotarevDegreeOne, P.discreteSpectrumGL, P.galoisRepOfPolarizedCuspidal, P.baseChangeDefiniteUnitary, P.bhattScholzeCrystallineLattices, P.heckeLAdicCharacterAbove, P.cuspRapidDecay, P.weilSiegelFormulaUnitary, P.siegelWeilUnitaryConvergent, P.doublingMethod, P.unramifiedDoublingGL, P.bernsteinZelevinskyFiniteness, P.formalDegreeCompactDual, P.bernsteinUnitaryProductIrreducible, P.geometricLemmaFiltration, P.unlinkedProductIrreducible, P.depthZeroJacquetInjective, P.howeDualityGL, P.jacquetShalika, P.automorphicFormsFiniteGL, P.localGlobalAboveL, P.regularAlgebraicPurity, P.globalArtinReciprocity, P.heckeLAdicParameterAbove, P.deRhamPotSemistable, P.harishChandraFinite, P.greenRegularCharacters, P.zelevinskyPolynomialRing, P.depthZeroInertia, P.rayClassFieldSt, P.rayCharacterArtin, P.genericUnitaryDualGL, P.standardCosocleGL, P.cheb, P.discreteSeriesCover, P.harishChandraModules, P.casselmanWallach, P.weilRepresentationUnitaryPair, P.discreteSeriesExists, P.discreteSeriesClassification, P.strongApproxSU, P.siegelWeilUnitaryConvergent2, P.harishChandraAnalyticity, P.cuspTraceClass, P.dixmierMalliavinFactorisation, P.flathFactorisation, P.pseudoCoefficientUpq, P.harishChandraCharacters, P.langlandsClassification, P.labesseWaldspurger, P.cMCurveGoodOutsidePrimeSt, P.weberRayFieldSt, P.discreteSeriesCoverExists, P.besselUniquenessReal, P.siegelWeilUnitarySchrodinger, P.siegelEisensteinContinuation, P.siegelEisensteinSimplePole, P.schurOrthogonalitySquareIntegrable, P.regularisedSiegelWeilFirstTerm, P.litN, P.toHypothesesX, P.nLink, P.depthZeroWild', P.depthZeroSupport', P.localFiniteness, P.localTateDuality, P.localEulerChar⟩

theorem HypothesesU.geometricLemma (P : HypothesesU) : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration P.bernsteinZelevinskyFiniteness P.geometricLemmaFiltration

example (P : Hypotheses2) : GlobalTheory.Published.GeometricLemmaFiltration := P.toU.geometricLemmaFiltration

example (P : Hypotheses2) : GlobalTheory.Published.SiegelWeilUnitarySchrodinger := P.toU.siegelWeilUnitarySchrodinger

example (P : Hypotheses2) : GlobalTheory.NLink.Hypotheses₂ := P.toU.nLink

example (P : Hypotheses2) : GlobalTheory.Published.GeometricLemma := P.toU.geometricLemma

end GlobalTheory.Fc.S0
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeneralHyps
section
namespace GlobalTheory.Fc.S0

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure GeneralHyps : Prop where
  toroidalCompactification : GlobalTheory.Published.ToroidalCompactification
  volGe : GlobalTheory.Published.VolGe
  volNef : GlobalTheory.Published.VolNef
  arCalc : GlobalTheory.Published.ArCalc
  abelianDeRham : GlobalTheory.Published.AbelianDeRham
  gaussBonnetUnitary : GlobalTheory.Published.GaussBonnetUnitary
  rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt
  weberRayFieldSt : GlobalTheory.Published.WeberRayFieldSt
  complexMultiplicationJSt : GlobalTheory.Published.ComplexMultiplicationJSt
  cMCurveGoodOutsidePrimeSt : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt
  strongApproxSU : GlobalTheory.Published.StrongApproxSU
  greenSeriesSt : GlobalTheory.Published.GreenSeriesSt
  cuspidalMirabolic : GlobalTheory.Published.CuspidalMirabolic
  canonKeySt : GlobalTheory.Published.CanonKeySt
  finitenessOfHermitianClasses : GlobalTheory.Published.FinitenessOfHermitianClasses
  succMinTransference : GlobalTheory.Published.SuccMinTransference
  semiAbelianHomExtension : GlobalTheory.Published.SemiAbelianHomExtension
  polExtSt : GlobalTheory.Published.PolExtSt
  abMulNSt : GlobalTheory.Published.AbMulNSt
  goodChernWeil : GlobalTheory.Published.GoodChernWeil
  grothendieckMessing : GlobalTheory.Published.GrothendieckMessing
  deRhamCanonicalExtension : GlobalTheory.Published.DeRhamCanonicalExtension
  prismaticDieudonneHodge : GlobalTheory.Published.PrismaticDieudonneHodge
  prismaticDieudonne : GlobalTheory.Published.PrismaticDieudonne
  kawamataViehweg : GlobalTheory.Published.KawamataViehweg
  nefNumerics : GlobalTheory.Published.NefNumerics
  l2ExtensionLogCanonical : GlobalTheory.Published.L2ExtensionLogCanonical
  arithHilbertSamuel : GlobalTheory.Published.ArithHilbertSamuel
  chowFormExists : GlobalTheory.Published.ChowFormExists
  cycleHeights : GlobalTheory.Published.CycleHeights
  serreHolomorphicSections : GlobalTheory.Published.SerreHolomorphicSections
  dbarCompleteKaehler : GlobalTheory.Published.DbarCompleteKaehler
  nadelVanishingAndNonKltDivisor : GlobalTheory.Published.NadelVanishingAndNonKltDivisor
  principalisation : GlobalTheory.Published.Principalisation
  serreTateGoodReductionSt : GlobalTheory.Published.SerreTateGoodReductionSt
  formalAlgebraisation : GlobalTheory.Published.FormalAlgebraisation
  abelianDieudonne : GlobalTheory.Published.AbelianDieudonne
  deRhamVectorExtension : GlobalTheory.Published.DeRhamVectorExtension
  siegelToroidalIntegral : GlobalTheory.Published.SiegelToroidalIntegral
  toroidalChartsForFan : GlobalTheory.Published.ToroidalChartsForFan
  arDegree : GlobalTheory.Published.ArDegree
  properIntersectionLength : GlobalTheory.Published.ProperIntersectionLength
  harishChandraFinite : GlobalTheory.Published.HarishChandraFinite
  harishChandraModules : GlobalTheory.Published.HarishChandraModules
  discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover
  weilSiegelFormulaUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary
  bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  greenCuspidal : GlobalTheory.Published.GreenCuspidal
  schurOrthogonalitySquareIntegrable : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
  harishChandraAnalyticity : GlobalTheory.Published.HarishChandraAnalyticity
  discreteSeriesClassification : GlobalTheory.Published.DiscreteSeriesClassification
  cuspTraceClass : GlobalTheory.Published.CuspTraceClass
  dixmierMalliavinFactorisation : GlobalTheory.Published.DixmierMalliavinFactorisation
  flathFactorisation : GlobalTheory.Published.FlathFactorisation
  pseudoCoefficientUpq : GlobalTheory.Published.PseudoCoefficientUpq
  harishChandraCharacters : GlobalTheory.Published.HarishChandraCharacters
  langlandsClassification : GlobalTheory.Published.LanglandsClassification
  labesseWaldspurger : GlobalTheory.Published.LabesseWaldspurger
  zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing
  heckeFunctionalEquationAbs : GlobalTheory.Published.HeckeFunctionalEquationAbs
  canonicalExtensionRankOne : GlobalTheory.Published.CanonicalExtensionRankOne
  formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual
  heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter
  heckeLAdicCharacterAbove : GlobalTheory.Published.HeckeLAdicCharacterAbove
  siegelEisensteinContinuation : GlobalTheory.Published.SiegelEisensteinContinuation
  idealInvariantsOneOrbitSt : GlobalTheory.Published.IdealInvariantsOneOrbitSt
  hermitianHassePrinciple : GlobalTheory.Published.HermitianHassePrinciple
  thetaRationalInvariance : GlobalTheory.Published.ThetaRationalInvariance
  stoneVonNeumann : GlobalTheory.Published.StoneVonNeumann
  logDerOne : GlobalTheory.Mem.An.LogDerOne
  discreteSeriesUpqExists : GlobalTheory.Published.DiscreteSeriesUpqExists
  discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists
  discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists
  abelianDualCrystal : GlobalTheory.Published.AbelianDualCrystal
  discreteSeriesHermitianUnique : GlobalTheory.Published.DiscreteSeriesHermitianUnique
  besselUniquenessReal : GlobalTheory.Published.BesselUniquenessReal
  kudlaSplittingSplitUnitary : GlobalTheory.Published.KudlaSplittingSplitUnitary
  gLHoweDuality : GlobalTheory.Published.GLHoweDuality
  metaplecticRepresentation : GlobalTheory.Published.MetaplecticRepresentation
  bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  borelCasselman : GlobalTheory.Published.BorelCasselman
  quadraticClassFieldTheory : GlobalTheory.Published.QuadraticClassFieldTheory
  rallisInnerProductConvergent : GlobalTheory.Published.RallisInnerProductConvergent
  siegelWeilAnisotropicUnitary : GlobalTheory.Published.SiegelWeilAnisotropicUnitary
  regularisedSiegelWeilFirstTerm : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm
  heckeLPartialContinuation : GlobalTheory.Published.HeckeLPartialContinuation
  hermitianLocalGlobal : GlobalTheory.Published.HermitianLocalGlobal
  radfordShufflePolynomial : GlobalTheory.Published.RadfordShufflePolynomial
  weylBranching : GlobalTheory.Published.WeylBranching
  cuspDecaySobolev : GlobalTheory.Published.CuspDecaySobolev
  linnik : GlobalTheory.Published.Linnik
  cuspBounded : GlobalTheory.Published.CuspBounded
  gKGlobalisation : GlobalTheory.Published.GKGlobalisation
  heckeLEntireAndNonzeroAtOne : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne
  holomorphicDiscreteSeries : GlobalTheory.Published.HolomorphicDiscreteSeries
  kFiniteVectorsUnitary : GlobalTheory.Published.KFiniteVectorsUnitary
  discreteSeriesLowestKType : GlobalTheory.Published.DiscreteSeriesLowestKType
  realMetaplecticRepresentation : GlobalTheory.Published.RealMetaplecticRepresentation
  automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL
  jacquetShalika : GlobalTheory.Published.JacquetShalika
  deRhamPotSemistable : GlobalTheory.Published.DeRhamPotSemistable
  explZeta : GlobalTheory.Mem.An.ExplZeta
  explChi : GlobalTheory.Mem.An.ExplChi
  jutila : GlobalTheory.Mem.An.Jutila
  pageThm : GlobalTheory.Mem.An.PageThm
  tZRat : GlobalTheory.Mem.An.TZRat
  tZQuad : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates
  discreteSeriesUpqUnique : GlobalTheory.Published.DiscreteSeriesUpqUnique
  automorphicFormsFiniteUnitary : GlobalTheory.Published.AutomorphicFormsFiniteUnitary
  discreteSeriesCoefficientsCuspidal : GlobalTheory.Published.DiscreteSeriesCoefficientsCuspidal
  principalIdealSt : GlobalTheory.Published.PrincipalIdealSt
  standardCosocleGL : GlobalTheory.Published.StandardCosocleGL
  blochKatoLocal : GlobalTheory.Published.BlochKatoLocal
  siegelKlingenDeligneRibet : GlobalTheory.Published.SiegelKlingenDeligneRibet
  heckeTateFunctionalEquation : GlobalTheory.Published.HeckeTateFunctionalEquation
  hilbertBlumenthal : GlobalTheory.Published.HilbertBlumenthal
  ellipticMainTheoremCM : GlobalTheory.Published.EllipticMainTheoremCM
  siegelSetUnitary : GlobalTheory.Published.SiegelSetUnitary
  langlandsSumMultiplicityOne : GlobalTheory.Published.LanglandsSumMultiplicityOne
  caraianiLocalGlobal : GlobalTheory.Published.CaraianiLocalGlobal
  algebraicCharacterWD : GlobalTheory.Published.AlgebraicCharacterWD
  clozelCohomological : GlobalTheory.Published.ClozelCohomological
  minguezThetaGL : GlobalTheory.Published.MinguezThetaGL
  moyPrasadJacquetIso : GlobalTheory.Published.MoyPrasadJacquetIso
  clozelPurity : GlobalTheory.Published.ClozelPurity
  totallyDisjointProductIrreducible : GlobalTheory.Published.TotallyDisjointProductIrreducible
  toroidalForFanKS : GlobalTheory.Published.ToroidalForFanKS
  semiAbelianLieSeminegative : GlobalTheory.Published.SemiAbelianLieSeminegative
  cuspidalSpectrumGL : GlobalTheory.Published.CuspidalSpectrumGL
  essSquareIntegrableSegments : GlobalTheory.Published.EssSquareIntegrableSegments
  temperedProductOfSquareIntegrable : GlobalTheory.Published.TemperedProductOfSquareIntegrable
  caraianiTempered : GlobalTheory.Published.CaraianiTempered
  galoisRepOfPolarizedPair : GlobalTheory.Published.GaloisRepOfPolarizedPair
  gelfandKazhdanDual : GlobalTheory.Published.GelfandKazhdanDual
  squareIntegrableSegment : GlobalTheory.Published.SquareIntegrableSegment
  geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration
  localConverseGL : GlobalTheory.Published.LocalConverseGL
  localLanglandsExists : GlobalTheory.Published.LocalLanglandsExists
  langlandsExhaustionGL : GlobalTheory.Published.LanglandsExhaustionGL
  partialZetaFunctionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation
  periodComparison : GlobalTheory.Published.PeriodComparison
  chernDegreeComplex : GlobalTheory.Published.ChernDegreeComplex
  arFormExists : GlobalTheory.Published.ArFormExists
  abelianDeRhamStructure : GlobalTheory.Published.AbelianDeRhamStructure
  abelianLifting : GlobalTheory.Published.AbelianLifting
  poincareDeRhamDuality : GlobalTheory.Published.PoincareDeRhamDuality
  pDivisibleGroupsOverOC : GlobalTheory.Published.PDivisibleGroupsOverOC
  tamagawaNumberSU : GlobalTheory.Published.TamagawaNumberSU
  complementaryThetaInert : GlobalTheory.Published.ComplementaryThetaInert
  greenRegularCharacters : GlobalTheory.Published.GreenRegularCharacters
  langlandsMultisegments : GlobalTheory.Published.LanglandsMultisegments
  discreteSpectrumResidual : GlobalTheory.Published.DiscreteSpectrumResidual
  baseChangeIsobaric : GlobalTheory.Published.BaseChangeIsobaric
  poitouTateNormalised : GlobalTheory.Published.PoitouTateNormalised
  unitaryDualGL : GlobalTheory.Published.UnitaryDualGL
  genericUnlinkedGL : GlobalTheory.Published.GenericUnlinkedGL
  gaussManinPeriods : GlobalTheory.Published.GaussManinPeriods
  siegelEisensteinSimplePole : GlobalTheory.Published.SiegelEisensteinSimplePole
  normalCompletionSt : GlobalTheory.Published.NormalCompletionSt
  depthZeroTypeInertia : GlobalTheory.Published.DepthZeroTypeInertia
  weilSiegelOneVector : GlobalTheory.Published.WeilSiegelOneVector
  weylDimensionGL : GlobalTheory.Published.WeylDimensionGL
  unitaryFiniteCovolume : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E], GlobalTheory.Published.UnitaryFiniteCovolume E
  discreteSeriesFormalDegree : GlobalTheory.Published.DiscreteSeriesFormalDegree
  casselmanWallachAdm : GlobalTheory.Published.CasselmanWallachAdm
  casselmanWallachLift : GlobalTheory.Published.CasselmanWallachLift
  fontaineEtale : GlobalTheory.Published.FontaineEtale
  prasadVolumeSU : GlobalTheory.Published.PrasadVolumeSU
  tateCharPolySt : GlobalTheory.Published.TateCharPolySt
  rosatiTracePosSt : GlobalTheory.Published.RosatiTracePosSt
  howeDualityReal : GlobalTheory.Published.HoweDualityReal
  globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity
  localFiniteness : ReciprocityTheory.Gal.LocalFiniteness
  localTateDuality : ReciprocityTheory.Gal.LocalTateDuality
  localEulerChar : ReciprocityTheory.Gal.LocalEulerChar
  globalFiniteness : ReciprocityTheory.Gal.GlobalFiniteness
  globalEulerChar : ReciprocityTheory.Gal.GlobalEulerChar
  unramifiedOrthogonality : ReciprocityTheory.Gal.UnramifiedOrthogonality
  greenbergWiles : ReciprocityTheory.Gal.GreenbergWiles
  hilbertClassFieldJ : GlobalTheory.Published.HilbertClassFieldJ
  siegelWeilUnitarySchrodinger : GlobalTheory.Published.SiegelWeilUnitarySchrodinger
  localTateDualityK : Formalism.GaloisCohomology.LocalTateDualityK
  localEulerCharK : Formalism.GaloisCohomology.LocalEulerCharK
  localFinitenessK : Formalism.GaloisCohomology.LocalFinitenessK
  bhattScholzeIntegral : GlobalTheory.Published.BhattScholzeIntegral
  jacquetShalikaRigidity : GlobalTheory.Published.JacquetShalikaRigidity
  depthZeroCuspidalLL : GlobalTheory.Published.DepthZeroCuspidalLL
  caraianiLocalGlobalDual : GlobalTheory.Published.CaraianiLocalGlobalDual

end GlobalTheory.Fc.S0
end

