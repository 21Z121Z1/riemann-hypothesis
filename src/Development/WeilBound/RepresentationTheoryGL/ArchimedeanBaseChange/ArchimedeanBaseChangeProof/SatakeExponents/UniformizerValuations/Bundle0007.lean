import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataExOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DiagCommOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0006
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PeakTraceBoundHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SphericalHeckeUnitary.PuSphHecke
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.SphStarUPlug
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0709

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.RunFinChain
section
namespace PositivityTheory.Rg.BcB.F

theorem runFin_chain (hF : F5.FinFam) (hW : WeightEx) (hQ : PermSat) (hD : Eig.DiagAlg) (hG : GenEx) : One.RunFin :=
  F5.runFin_of (runT_of peak_trace_bound_holds (setupEx_of setupAlg (dataEx_of (diagComm_of hD) genToData hG))) hF hW hQ

end PositivityTheory.Rg.BcB.F
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.UnitaryAdjointHolds
section
namespace PositivityTheory.Rg.BcB.F.U

theorem unitary_words_holds : UWord :=
  UU.uWordOfU GlobalTheory.T.diagonal_algebra_holds GlobalTheory.T.local_algebra_holds (GlobalTheory.T.spherical_one_of_local_algebra GlobalTheory.T.local_algebra_holds) GlobalTheory.T.compact_unit_holds PositivityTheory.Rg.BcB.F.Fok.sphStarU

theorem unitary_adjoint_holds : UAdj :=
  UU.uAdjOfU GlobalTheory.T.diagonal_algebra_holds GlobalTheory.T.local_algebra_holds (GlobalTheory.T.spherical_one_of_local_algebra GlobalTheory.T.local_algebra_holds) GlobalTheory.T.compact_unit_holds PositivityTheory.Rg.BcB.F.Fok.sphStarU

end PositivityTheory.Rg.BcB.F.U
end

