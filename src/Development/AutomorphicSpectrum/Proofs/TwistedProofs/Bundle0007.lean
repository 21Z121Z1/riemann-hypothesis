import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.PointwiseOfSpanHeisenberg
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0002
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SpanEquality
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SphericalTransitiveOfLevi

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.LatticeIndexOfSmithStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_of_smith : Smith → LatIndex := by
  first | exact @GlobalTheory.CompanionTheory.InertIndex.latIndex | exact GlobalTheory.CompanionTheory.InertIndex.latIndex | (intros; apply GlobalTheory.CompanionTheory.InertIndex.latIndex <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.LeviDecompositionExistsStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_decomposition_exists : LeviExists := by
  first | exact @GlobalTheory.CompanionTheory.InertLevi.leviExists | exact GlobalTheory.CompanionTheory.InertLevi.leviExists | (intros; apply GlobalTheory.CompanionTheory.InertLevi.leviExists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.PointwiseOfSpanHeisenbergStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwise_of_span_heisenberg : AddVec → Dual → SpanEq → Heis → Pointwise := by
  first | exact @GlobalTheory.CompanionTheory.InertLen.pointwise | exact GlobalTheory.CompanionTheory.InertLen.pointwise | (intros; apply GlobalTheory.CompanionTheory.InertLen.pointwise <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.RecursionIdentityStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recursion_identity : Step := by
  first | exact @GlobalTheory.CompanionTheory.InertLevi.step | exact GlobalTheory.CompanionTheory.InertLevi.step | (intros; apply GlobalTheory.CompanionTheory.InertLevi.step <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallCornerOfHeisenbergDualStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_corner_of_heisenberg_dual : Heis → Dual → SmallCorner := by
  first | exact @GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis | exact GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis | (intros; apply GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallRankBoundStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_rank_bound : SmallRank := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.smallRank | exact GlobalTheory.CompanionTheory.InertZeta.smallRank | (intros; apply GlobalTheory.CompanionTheory.InertZeta.smallRank <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SpanEqualityStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_equality : SpanEq := by
  first | exact @GlobalTheory.CompanionTheory.InertSpan.spanEq | exact GlobalTheory.CompanionTheory.InertSpan.spanEq | (intros; apply GlobalTheory.CompanionTheory.InertSpan.spanEq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SphericalTransitiveOfLeviStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_transitive_of_levi : LeviExists → SphTrans := by
  first | exact @GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists | exact GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists | (intros; apply GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.TraceIndexFormulaStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_index_formula : TraceIndex := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.traceIndex | exact GlobalTheory.CompanionTheory.InertZeta.traceIndex | (intros; apply GlobalTheory.CompanionTheory.InertZeta.traceIndex <;> assumption)
end

