import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.LimitOfFiniteDiscrete
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TreeLemmas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0804
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0659
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0433

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LimG

theorem lim5 : PositivityTheory.Rg.BcB.SpectralAccumulation.FinDisc → PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5 := fun hFD =>
  PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.limit_of_finite_discrete hFD GlobalTheory.T.limit_block_types GlobalTheory.T.limit_twist_bound GlobalTheory.T.limit_node_embedding
    PositivityTheory.Rg.BcB.SpectralAccumulation.Trees.treeLemmas.2.2.1 PositivityTheory.Rg.BcB.SpectralAccumulation.Trees.treeLemmas.2.1
    PositivityTheory.Rg.BcB.SpectralAccumulation.Trees.treeLemmas.1

end PositivityTheory.Rg.BcB.SpectralAccumulation.LimG
