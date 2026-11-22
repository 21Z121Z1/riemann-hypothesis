import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0536
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0326
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.CechDescentTests.A6
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1386
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0238

noncomputable section

namespace PositivityTheory.SphericalProduct

theorem jacquet_hecke (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : A2 G :=
  GlobalTheory.T.jacquet_projection_hecke_holds G

theorem iwahori_u : IwahoriU :=
  GlobalTheory.T.iwahori_unipotent_datum

theorem dom_u : DomU :=
  GlobalTheory.T.dominant_unipotent_contraction

end PositivityTheory.SphericalProduct

end
