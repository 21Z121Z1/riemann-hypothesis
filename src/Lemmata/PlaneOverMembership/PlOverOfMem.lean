import Mathlib
import Formalism.LocalToGlobal.ExponentGrids.ScaledCoordinatesValuationLemma
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0005
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003
import Formalism.PairingDivisors.PairingDivisorProofs.Height
import Formalism.PairingDivisors.PairingDivisorProofs.SumValuationNat
import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd
import Formalism.TowerValuationBounds.TowerValuationProofs.SumAdditiveCharacterEqZero
import Formalism.SizeWindowBrackets.LcvBaseChange
import Formalism.QuotientMetricDivisors.Bundle0005
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0006
import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0004
import Formalism.SizeWindowBrackets.ChainSlopeWindows.Bundle0001
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0001
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0003
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0002
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Duality
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PiSumForallInsertOnly
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Example
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
import Formalism.HarderNarasimhan.Bundle0002
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.CorankShare.CorankShareProofs.LayerCakeFormula
import Formalism.CorankShare.CorankShareProofs.SumNormSqLeHilbertSchmidt

namespace Bl.PlaneOverMembership

open NumberField IsDedekindDomain

private theorem plOver_of_mem {K : Type} [Field K] [NumberField K] {g : ℕ} (hg : 0 < g)
    (w : HeightOneSpectrum (𝓞 K)) (h : (g : 𝓞 K) ∈ w.asIdeal) : Formalism.DivisionValues.PlOver g w := by
  classical
  have hc : ((g : 𝓞 K) : K) = (g : K) := by simp
  have hg0 : (g : 𝓞 K) ≠ 0 := by exact_mod_cast hg.ne'
  have hJ : (Ideal.span {(g : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hm : Associates.mk (Ideal.span {(g : 𝓞 K)}) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors := by
    rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
      Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  unfold Formalism.DivisionValues.PlOver Formalism.DivisionValues.vw
  rw [← hc, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ hJ]
  exact_mod_cast h1

theorem goal1 :
  Formalism.AtG.FinitePlaceLiesOverPrime := by
  intro K _ _
  refine ⟨fun w => Ideal.absNorm (Ideal.under ℤ w.asIdeal), fun w => ?_⟩
  have : NeZero w.asIdeal := ⟨w.ne_bot⟩
  have hp : (Ideal.absNorm (Ideal.under ℤ w.asIdeal)).Prime := Nat.absNorm_under_prime w.asIdeal
  exact ⟨hp, plOver_of_mem hp.pos w (Int.absNorm_under_mem w.asIdeal)⟩

end Bl.PlaneOverMembership
