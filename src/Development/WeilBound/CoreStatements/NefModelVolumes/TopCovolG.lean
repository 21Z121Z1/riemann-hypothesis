import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2525
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.WeilBound.CoreStatements.NefModelVolumes.HeightG
open GlobalTheory.CovTop GlobalTheory.BigTop

namespace SelfIntersectionVolumeEstimates

set_option maxHeartbeats 1000000 in

theorem topCovolG : SelfIntersectionVolumeEstimates.VolInputs → GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.CompanionTheory.Ar.Plug.DeepStR → CovolX :=
  by
  intro hSB hX hP hH hSW hGD hQ hD
  have hS := hH.sieg
  have hK := hX.ks
  have hN := hX.lie
  have gram := GlobalTheory.T.gram_bound_statement hP
  have size := GlobalTheory.T.size_bound_statement
  have meas := GlobalTheory.T.measure_bound_statement hP
  have anc := GlobalTheory.T.anchor_bound_statement
  have dex := GlobalTheory.T.deep_existence_statement hP
  have dg := GlobalTheory.T.deep_good_reduction_statement hSW hP hGD hQ hS hK hN
  have fd := GlobalTheory.T.flat_degree_statement hSW hP
  have deg := GlobalTheory.T.degree_bound_of_deep_good hX hP hS hK hGD hQ hN dg size fd
  have sh := GlobalTheory.T.share_of_toroidal hX hP hS hK hGD hQ hN dg size fd deg
  have ht := heightG hSB hX hGD hQ hP hH hD dg size deg fd
  have hs := GlobalTheory.T.height_theorem_of_hypotheses hX hP hGD hQ hS hK hN dg size fd deg sh
  have ul := GlobalTheory.T.uniform_lower_bound_of_sums dg size deg sh ht hs (GlobalTheory.T.sum_constant_of_deep_good dg)
  have low := GlobalTheory.T.lower_bound_of_all_estimates size (GlobalTheory.T.low_definition_from_anchor hP gram anc) dex dg (GlobalTheory.T.ring_bound_of_deep_good hP gram dg) (GlobalTheory.T.maps_bound_of_deep_good hP hGD hQ hS hK hN gram dg size fd) (GlobalTheory.T.rank_bound_of_deep_good hX hP hGD hQ hS hK hN dg size fd deg sh) (GlobalTheory.T.minimal_genus_bound hP gram dg size) (GlobalTheory.T.flat_bound_of_anchor hP dg fd anc) ul
  exact GlobalTheory.T.covolume_from_gram_and_bounds gram (GlobalTheory.T.recursion_of_gram_bound gram) (GlobalTheory.T.cutoff_bound_statement hP) (GlobalTheory.T.bad_set_bound_of_degeneration hX hP hGD hQ hS hK hN hX.green gram dex dg size fd deg sh) (GlobalTheory.T.lambda_bound_from_measure hP gram meas) size (GlobalTheory.T.covering_le_from_measure gram meas (GlobalTheory.T.rational_cover_bound hP)) low

end SelfIntersectionVolumeEstimates
