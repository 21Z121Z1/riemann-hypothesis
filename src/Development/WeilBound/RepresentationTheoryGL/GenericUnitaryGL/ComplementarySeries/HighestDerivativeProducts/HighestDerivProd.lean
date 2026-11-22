import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.Bundle0001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0734
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0526
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.IsSmoothCharDpowM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0735
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0745
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerCharEqOneOfMemUnipRad
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0738

namespace GlobalTheory.RgGu.Leib.Hand

theorem leibnizOrd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    LeibnizOrd k :=
  GlobalTheory.T.leibniz_order_of_exact_sequences k (GlobalTheory.T.residue_sequence_holds k) (GlobalTheory.T.psi_gp_commutation_holds k) (GlobalTheory.T.phi_gp_commutation_holds k) (GlobalTheory.CompanionTheory.BZPsiPG.Hand.psiPG k) (GlobalTheory.CompanionTheory.BZPhiPG.phiPG k)
    (GlobalTheory.T.phi_pg_rank_zero_holds k)

end GlobalTheory.RgGu.Leib.Hand
