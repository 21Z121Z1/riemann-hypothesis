import Mathlib
import Formalism.PeriodIntegrals.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSum.Imports
import Formalism.PeriodIntegrals.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderReduction.EqOneOfIsOfFinOrder
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderReduction.Bridge
import Formalism.PeriodIntegrals.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandPairConvolution.ConvComm
import Formalism.PeriodIntegrals.GeometricProductPowers.GaussianProductPowerBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GeometricProductBound.OneSubSumLeProd
import Formalism.PeriodIntegrals.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramIsometryCoefficient.ExCoeffOneNe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramUnitMultiplication.BeMulByZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselOpenValuation.IsOpenLeVal
import Formalism.LocalToGlobal.AdelicCompactOpens.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDefiniteOrthonormal.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IndexUpperBound.OneSubSumLeProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeJacobi.NotIsSquareOfJacobi
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
import Formalism.PeriodIntegrals.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDualPair.SymmetricMeasureL2NormEqResolutionL2

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EmbTraceSum
section
theorem sumEqTrace_holds : PI.EmbTraceSum := by
  intro E _ _ K φ₀ S _ emb hinj hext hcard y
  let _ : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  have hcomm : ∀ (s : S) (a : K), emb s (algebraMap K E a) = algebraMap K ℂ a := fun s a => hext s a
  let f : S → (E →ₐ[K] ℂ) := fun s => { emb s with commutes' := hcomm s }
  have hf : Function.Injective f := by
    intro s t hst
    apply hinj
    ext x
    exact AlgHom.congr_fun hst x
  have : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  have hcard' : Fintype.card S = Fintype.card (E →ₐ[K] ℂ) := by
    rw [hcard, AlgHom.card]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard'⟩
  have htr := trace_eq_sum_embeddings (K := K) (L := E) (E := ℂ) (x := y)
  calc ∑ s, emb s y = ∑ s, f s y := rfl
    _ = ∑ σ : E →ₐ[K] ℂ, σ y := Fintype.sum_bijective f hbij _ _ (fun _ => rfl)
    _ = algebraMap K ℂ (Algebra.trace K E y) := htr.symm
    _ = φ₀ ((Algebra.trace K E y : K) : E) := rfl
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FinOrdRedOne
section
open NumberField IsDedekindDomain PI.FinOrdRedOne

theorem finite_order_reduction_one : PI.FinOrdRedOne := by
  intro E _ _ p hp hp3 hU P hpP N β hfin hred
  exact Core.eq_one_of_isOfFinOrder p hp hp3 (Bridge.natCast_ne_zero p hp hU P hpP)
    (Bridge.maximalIdeal_eq p hp hU P hpP) (Bridge.eq_zero_of_forall_dvd p hp hU P hpP) β hfin hred
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GelfConv
section
theorem gelfand_convolution_comm : PI.UMultOne.ConvComm := PI.UnitaryGroupMassFormula.GelfConv.convComm
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GeoProdPow
section
theorem geometric_product_power : ConditionalKappaBounds.G2.GaussianProductPowerBound := GeoProdPow.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GramIso
section
theorem flag_gram_iso : PI.FglGram.GramIso := PI.UnitaryGroupMassFormula.GramIso.gramIso
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GramUnit
section
theorem gramExpansion_orthonormal : PI.FglGram.GramUnit := PI.UnitaryGroupMassFormula.GramUnit.gramUnit
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Hensel
section
theorem hensel_strong : PI.HenselStrong := PI.HenselValuation.henselStrong
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HermDefON
section
theorem posDefCongruentOne : Formalism.L2.Props.HermDefON := fun _ G hG => PI.UnitaryGroupMassFormula.HermDefON.exists_congr_one G hG
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IndexUBound
section
theorem product_lowerBound : PI.IndexUBound.IndexUBound := by
  classical
  intro ι S g r y hg hy
  have h2 : ∀ v ∈ S, (2 : ℝ) ≤ g v := fun v hv => by exact_mod_cast hg v hv

  have hfac : ∀ v ∈ S, ∏ i ∈ Finset.Ico 1 r, ((g v : ℝ) ^ i - 1) =
      (g v : ℝ) ^ (r * (r - 1) / 2) * ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i) :=
    fun v hv => PI.UnitaryGroupMassFormula.IndexUBound.prod_factor _ (by linarith [h2 v hv] : (0 : ℝ) < g v).ne' r
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]

  have hQ := PI.UnitaryGroupMassFormula.IndexUBound.one_sub_sum_le_prod S
    (fun v => ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i)) (fun v => 1 / ((g v : ℝ) - 1))
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).1)
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).2.1)
    (fun v hv => div_nonneg zero_le_one (by linarith [h2 v hv]))
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).2.2)
  beta_reduce at hQ
  have hpos : 0 ≤ ∏ v ∈ S, (g v : ℝ) ^ (r * (r - 1) / 2) :=
    Finset.prod_nonneg fun v _ => by positivity
  have key := mul_le_mul_of_nonneg_right
    (show 1 - y ≤ ∏ v ∈ S, ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i) by linarith) hpos
  linarith
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InertPrime
section
open NumberField

theorem isPrime_span_of_jacobi_neg_one : PI.InertPrime := by
  intro K _ _ hK b d p hb hp hj
  exact PI.InertPrimeWork.inert K hK b d p hb hp hj
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntAdCpctOpen
section
theorem finiteAdeleIntegers_compactOpen : Formalism.L2.Props.IntAdelesCompactOpen := PI.IntAdCpctOpenWork.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoDualPair
section
theorem isometry_dual_pair : PI.IsoDualPair.IsoDualPair := PI.IsoDualPair.UnitaryGroupMassFormula.isoDualPair
end

