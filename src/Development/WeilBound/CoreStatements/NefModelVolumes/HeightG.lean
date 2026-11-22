import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
import Development.WeilBound.CoreStatements.NefModelVolumes.TwoLtHalfFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
open GlobalTheory.CovTop GlobalTheory.BigTop

namespace SelfIntersectionVolumeEstimates

set_option maxHeartbeats 1000000 in

theorem heightG : SelfIntersectionVolumeEstimates.VolInputs → GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.CompanionTheory.Ar.Plug.DeepStR → DeepGood → Size → Deg → FlatDeg → Height :=
  fun hSB hX hGD hQ hP hH hD hG hS hDg hF => GlobalTheory.CovHt.HtTopG.height_of_steps hSB hP hG hS hDg (GlobalTheory.T.short_of_inputs hP hG hS hF) (GlobalTheory.T.geometric_of_published_inputs hX hGD hQ hP hH.sieg hX.ks hX.lie hG hS) (GlobalTheory.T.carrying_section_integral_frame (GlobalTheory.T.reference_weight_of_deep_good hP hG hS hF) (GlobalTheory.T.exists_carrying_section_orders hP hH hG hS hF)) (GlobalTheory.T.budget_of_size_and_weight GlobalTheory.T.host_bound_holds GlobalTheory.T.weight_bound_holds hS) hD

end SelfIntersectionVolumeEstimates
