import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0056
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0059
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0060

-- bundled from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.ExhaustionStart
section
namespace CompanionTheory.RgExh.Dec.N.S

theorem exhaustion_start : CompanionTheory.RgExh.Dec.Start :=
  GlobalTheory.T.InitialStatement GlobalTheory.T.rgExh_flagFacts GlobalTheory.T.ParabolicSubgroupEquality GlobalTheory.T.rgExh_lineFacts GlobalTheory.T.SlabStatement (GlobalTheory.T.fubini_of_parabolic_haar_multiple GlobalTheory.T.FubiniParabolicMultiple) GlobalTheory.T.MaximalCompactStatement

end CompanionTheory.RgExh.Dec.N.S
end

-- bundled from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFinal
section
namespace CompanionTheory.RgExh.Dec.N.S

theorem line_formula : CompanionTheory.RgExh.Dec.L.LineFormula := GlobalTheory.T.line_formula_of_fubini_and_parabolic GlobalTheory.T.FubiniParabolicMultiple GlobalTheory.T.rgExh_lineFacts GlobalTheory.T.ParabolicSubgroupEquality

end CompanionTheory.RgExh.Dec.N.S
end

