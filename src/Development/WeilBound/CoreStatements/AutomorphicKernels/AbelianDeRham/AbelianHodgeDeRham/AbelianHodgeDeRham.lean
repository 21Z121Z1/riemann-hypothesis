import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0051
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0876
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0855
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0142
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HtpyStOfCxSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0143
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeExOfAcyclic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExactOfSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0178
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0174
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UOfIsBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleHomCompSquareZeroSection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0165
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0854
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0865
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFirstCohomologyBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCohomologyComparisonSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0168
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferSumProjectionsDegreeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0139
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeFunctionalTwoFormNaturality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0136
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorPairingIotaTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOfRTensor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormComponentOfWedgeClassZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleRestrictCompositeInjectiveCohomologyFo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BilinearStatementWithDescentHypotheses
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0725
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0258
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0857
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1BoundaryOfBoundary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0856
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianWedgeProducts.EqZeroOfExteriorPowerMapAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOfSmulEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0871
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0261
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0866
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.ClosedPoints.IsClosedPoint
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0864

namespace MainStatements.Hodge.Free

theorem abelianHodgeDeRham' : Chapters where
  dict := GlobalTheory.CompanionTheory.Dict.dictSt
  cx := GlobalTheory.CompanionTheory.HodgeCx.cxSt
  low := GlobalTheory.CompanionTheory.HodgeLow.lowSt_of_dictSt
  htpy := GlobalTheory.CompanionTheory.Hodge.htpySt_of_cxSt
  qcalc := GlobalTheory.CompanionTheory.QCalc.qCalcSt
  fubini := GlobalTheory.CompanionTheory.NerveCoh.fubiniSt
  affacyc := GlobalTheory.CompanionTheory.AffAcyc.main
  descent := GlobalTheory.CompanionTheory.Descent.descentSt
  sysbc := GlobalTheory.CompanionTheory.SysBC.sysBCSt
  stein := GlobalTheory.CompanionTheory.Hodge.stein_holds
  cot := GlobalTheory.CompanionTheory.Cot.cotSt
  par := GlobalTheory.CompanionTheory.AbForms.parSt
  axo := GlobalTheory.CompanionTheory.Axis.axOSt
  axform := GlobalTheory.CompanionTheory.AxForm.axFormSt
  cmp := GlobalTheory.CompanionTheory.Hodge.Nerve.cmpSt_of_cxSt
  fincoh := GlobalTheory.CompanionTheory.Hodge.finCohSt_of_cmpSt
  van := GlobalTheory.CompanionTheory.Hodge.vanSt
  perfnoeth := GlobalTheory.CompanionTheory.PerfN.perfNoeth
  perfbase := GlobalTheory.CompanionTheory.PerfExt.main
  perfh1 := GlobalTheory.CompanionTheory.PerfectFirstCohomology.perfect_first_cohomology_base_change
  perfh2 := GlobalTheory.CompanionTheory.PerfectSecondCohomology.perfect_second_cohomology_from_fibres
  wedgeof := GlobalTheory.CompanionTheory.WedgeOf.wedgeOf_of_low
  hopffield := GlobalTheory.CompanionTheory.HopfC.hopfFieldSt
  oneform := GlobalTheory.CompanionTheory.OneFormCoh.oneFormCohSt
  twoform := GlobalTheory.CompanionTheory.HodgeTwoForm.twoFormCohSt
  closed := GlobalTheory.CompanionTheory.HodgeClosed.closedSt_of_twoFormCohSt
  lift := GlobalTheory.CompanionTheory.Hodge.LiftO.lift_of_forms
  alt := GlobalTheory.CompanionTheory.HodgeAlt.altSt
  hyp2 := GlobalTheory.CompanionTheory.HypWedge.hyp2St
  hopf := GlobalTheory.CompanionTheory.HopfSys.hopfSt
  bi := GlobalTheory.CompanionTheory.GroupLaw.bilinear_statement_with_descent_hypotheses
  formbc := GlobalTheory.CompanionTheory.Hodge.FormBC.formBC
  oside := GlobalTheory.CompanionTheory.HodgeO.oBC_wedge
  perf := GlobalTheory.CompanionTheory.PerfModels.perfSt_of_spreads
  final := GlobalTheory.CompanionTheory.HodgeAssembly.abelianHodgeDeRham_of_statements
  hopfle := GlobalTheory.CompanionTheory.HopfLe.hopfLeSt
  h1le := GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds.h1Le
  wedgefield2 := GlobalTheory.CompanionTheory.Hodge.WedgeFieldGeo.wedgeField_of_field
  noprim := MainStatements.Hodge.Pf.noprim
  smalllift := GlobalTheory.CompanionTheory.SmallLift.main
  perfvb := GlobalTheory.CompanionTheory.PerfVB.perfVB
  h1all := GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle.first_cohomology_vector_bundle_rank
  flatbc := GlobalTheory.CompanionTheory.Hodge.FlatBase.flatBC
  feweqn := GlobalTheory.CompanionTheory.FewEq.fewEq
  stalkdim := MainStatements.Hodge.Pf.stalkdim
  h1ge := GlobalTheory.CompanionTheory.FirstCohomologyLowerBound.first_cohomology_dimension_lower_bound
  h1field := GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField.first_cohomology_rank_over_field

theorem abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham :=
  abelianHodgeDeRham'.print GlobalTheory.CompanionTheory.NoethApprox.schemeModels GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads GlobalTheory.CompanionTheory.SpreadingModels.properSpreads
    GlobalTheory.CompanionTheory.TrivLoc.trivLocus GlobalTheory.CompanionTheory.KLFinite.kFinite

end MainStatements.Hodge.Free
