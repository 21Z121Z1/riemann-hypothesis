import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.Adapted
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.MulVecInjectiveOfKer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.LatticeFinitelyGenerated
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.LocalPairingPerfect
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.MirrorDecompOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0033
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0030
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0025
import Formalism.PeriodIntegrals.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.GramMapFibreUniqueness
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.AdditiveCharacterNontrivial
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Bundle0001
import Formalism.PeriodIntegrals.Bundle0029
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.FinrankOrthAddLe
import Formalism.PeriodIntegrals.Bundle0026
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.SchurFockOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvProjRows
section
theorem projection_rows_bound : PI.Dv.division_rows_base_level :=
  PI.DvRows.dvProjRows_of_pieces PI.DvRows.lattice_finitely_generated PI.DvRows.adapted_bases_exist PI.DvRows.gram_cauchy_schwarz
    PI.DvRows.archimedean_identity (PI.DvRows.localGamma_of_gramCS PI.DvRows.gram_cauchy_schwarz)
    PI.DvRows.local_pairing_perfect PI.DvRows.conjugate_prime PI.DvRows.norm_finite_sum
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MirrorDecomp
section
theorem mirrorDecomp : Formalism.FourierDecayAlt.C2.MirrorDecomp :=
  PI.MirrorSection₂.mirrorDecomp_of stabPairs eichlerTau lowUniSplit
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OmFibreUniq
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

theorem omUnique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : ℕ) :
    PI.OmFibreUniq.OmUnique σ J ψ v a :=
  PI.OmFibreUniq.W.omUnique_of_sdEx
    (PI.OmFibreUniq.W.SdInst.sdEx_of_psiNT PI.OmFibreUniq.W.Sd.additive_character_nontrivial) σ J ψ v a
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PairCorankPos
section
theorem pair_corank_pos : PI.PairCorankPos.CorankPosG := PI.PairCorankPos.W.corankPosG
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SchurFock
section
theorem schur_fock : PI.SchurFock := PI.WSF.schurFock_of highest_weight_irreducible
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitPairGen
section
theorem split_pair_generation : Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen := square_pair_glue square_pair_local
end

