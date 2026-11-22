import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackward
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InfinitesimalCharacterStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0037
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeBackward : CompanionTheory.RgExh.Hk.Back := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back | exact GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ImportsAlt
section
namespace GlobalTheory.CompanionTheory.DSCapelliAction

theorem actQ : CompanionTheory.D.DSIC.ActQ := by
  intro n ε H _ _ σ S E h u v
  exact GlobalTheory.CapelliFreeAction.actU_qdet n ε H σ S E (fun a b w => h.act a b w) u v

end GlobalTheory.CompanionTheory.DSCapelliAction
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InfinitesimalCharacterStatementStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.InfinitesimalCharacterStatement : CompanionTheory.RgExh.StepChar := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar | exact GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KExp
section
namespace GlobalTheory.CompanionTheory.DSICKExp

theorem kExp : CompanionTheory.D.DSIC.KExp := by
  intro n ε g hg
  obtain ⟨Y, hY, he, -⟩ := Formalism.REAL.compact_exponential_surjective n ε g hg
  exact ⟨Y, hY, he.symm⟩

end GlobalTheory.CompanionTheory.DSICKExp
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SpanGeneratorsStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SpanGenerators : SpanG := by
  first | exact @GlobalTheory.CompanionTheory.BmuSpan.spanG | exact GlobalTheory.CompanionTheory.BmuSpan.spanG | (intros; apply GlobalTheory.CompanionTheory.BmuSpan.spanG <;> assumption)
end

