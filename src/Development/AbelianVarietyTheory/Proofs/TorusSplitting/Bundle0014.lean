import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0032
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtValIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaInt

theorem etVal_integral :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)), (Formalism.MainNotions.ModuliIntegralCharts.H1.EtVal (recPJ h j hj) i η ↔ Formalism.L2.Pj.EtVal h j hj i η) ∧ (∀ la (y : (recPJ h j hj).Pt la), 0 ≤ (recPJ h j hj).phiC la y) ∧ (Formalism.L2.Pj.EtVal h j hj i η → IntAlg η.1 ∧ η ∈ (recB h.toLawsCore).Mlat j (wEt D j i)) := by
  intro D T h j hj i η
  refine ⟨Iff.rfl, GlobalTheory.EtaValuationTest.phiC_nonneg _, fun hv => ?_⟩
  have hm : η ∈ (recB h.toLawsCore).Mlat j (wEt D j i) :=
    GlobalTheory.EtaValuationTest.mem_Mlat (recPJ h j hj) i η hv
  refine ⟨?_, hm⟩
  have h0 := ((recPJ h j hj).Mlat_eq _ η).1 hm
  refine (nonneg_iff_of_liesTotal (T.G.liesTotal h.points_condition h.bc66 hj) η.1).2 fun la y => ?_
  exact le_of_le_of_eq (h0 la y) (recPJ_vAt_inc h j hj la y _ η)

end GlobalTheory.EtaInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.LogbNormUniformizerNormalisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EtaVal.UnitNorm

theorem vV_unit_mul_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (u : Vˣ) (n : ℕ) :
    vV V (algebraMap V (FractionRing V) (u * ϖ ^ n)) = n := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal V).intValuation (u : V) = 1 := by
    rw [HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal (u : V)).1 h u.isUnit
  have h2 : (IsDiscreteValuationRing.maximalIdeal V).intValuation ϖ = WithZero.exp (-1 : ℤ) :=
    HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq
  rw [vV, valV, HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow, h1, h2, _root_.one_mul,
    ← WithZero.exp_nsmul, WithZero.log_exp]
  simp

theorem norm_map_unit {V F : Type} [CommRing V] [NormedField F] (f : V →+* F) (hf : ∀ a, ‖f a‖ ≤ 1)
    (u : Vˣ) : ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Vˣ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (hf _) ?_
  calc (1 : ℝ) = ‖f u‖ * ‖f (u⁻¹ : Vˣ)‖ := h.symm
    _ ≤ ‖f u‖ * 1 := mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
    _ = ‖f u‖ := _root_.mul_one _

theorem logb_norm_uniformiser : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (C : SCF (Formalism.MainNotions.WeightAlgebra.resCh la)) (f : T.V →+* ↥C.S), (∀ a, ‖f a‖ ≤ 1) → -Real.logb (Formalism.MainNotions.WeightAlgebra.resCh la) ‖f ϖ‖ * ((e : ℝ) * Formalism.BasicNotions.eWL K la) = 1 ∧ 0 < Formalism.BasicNotions.eWL K la := by
  intro K _ _ la T io e ho ϖ hϖ C f hf
  have hE := Formalism.MainNotions.ModuliIntegralCharts.H1.H1algLink.eWL_eq la
  refine ⟨?_, hE ▸ Nat.pos_of_ne_zero (Formalism.MainNotions.ModuliIntegralCharts.H1.H1algLink.ramOverZ_ne_zero la)⟩
  have hp : (Formalism.MainNotions.WeightAlgebra.resCh la).Prime := Crude.resCharOf_prime la
  have hv : vLa la ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : K) = Formalism.BasicNotions.eWL K la := by
    rw [hE]; exact Crude.crv_vLa_char la
  have hn := C.norm_p
  generalize Formalism.BasicNotions.eWL K la = E at hv ⊢
  have h0 : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : T.V) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have h1 := vV_unit_mul_pow hϖ u n
  rw [← hu, map_natCast, ← map_natCast io, ho.2, hv] at h1
  have h2 : ((e : ℝ) * E) = n := by exact_mod_cast h1
  have h3 : ‖f ϖ‖ ^ n = ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : ℝ)⁻¹ := by
    rw [← hn, ← map_natCast f, hu, map_mul, norm_mul, norm_map_unit f hf u, _root_.one_mul, map_pow, norm_pow]
  have hp1 : (1 : ℝ) < ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : ℝ) := by exact_mod_cast hp.one_lt
  have h4 := congrArg (Real.logb (Formalism.MainNotions.WeightAlgebra.resCh la)) h3
  rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one hp1] at h4
  rw [h2]
  linarith

end GlobalTheory.EtaVal.UnitNorm
end
end

