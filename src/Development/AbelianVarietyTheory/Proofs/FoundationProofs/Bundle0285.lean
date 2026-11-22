import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0275
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0280
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexCompletedStandardNeZero
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem relIndex_ne_zero_of_denom {A ι κ : Type} [CommRing A] [Finite ι] [Finite κ] (S : Subring A) (I : AddSubgroup A) (k n : ℕ)
    (hk : IsUnit (k : A)) (hfin : Finite (S ⧸ Ideal.span {((k * n : ℕ) : S)})) (hn : ∀ s ∈ S, (n : A) * s ∈ I)
    (L T : AddSubgroup (Matrix ι κ A)) (hL : ∀ ζ : Matrix ι κ A, (∀ i j, ζ i j ∈ I) → ζ ∈ L)
    (hT : ∀ ζ ∈ T, ∀ i j, (k : A) * ζ i j ∈ S) : L.relIndex T ≠ 0 := by
  let φ : T →+ (ι → κ → S ⧸ Ideal.span {((k * n : ℕ) : S)}) :=
    AddMonoidHom.mk' (fun ζ i j => Ideal.Quotient.mk _ ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩) (fun x y => by
      funext i j
      rw [Pi.add_apply, Pi.add_apply, ← map_add]
      congr 1
      exact Subtype.ext (mul_add _ _ _))
  have hle : φ.ker ≤ L.addSubgroupOf T := by
    intro ζ hζ
    rw [AddSubgroup.mem_addSubgroupOf]
    refine hL _ fun i j => ?_
    have h0 : Ideal.Quotient.mk (Ideal.span {((k * n : ℕ) : S)}) ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩ = 0 :=
      congrFun (congrFun ((AddMonoidHom.mem_ker).1 hζ) i) j
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have h1 : (s : A) * (((k * n : ℕ) : S) : A) = (k : A) * ζ.1 i j := congrArg Subtype.val hs
    have h2 : ζ.1 i j = (n : A) * s := by
      apply hk.mul_left_cancel
      rw [← h1]
      push_cast
      ring
    rw [h2]
    exact hn _ s.2
  have : φ.ker.FiniteIndex := AddSubgroup.finiteIndex_ker φ
  exact (AddSubgroup.finiteIndex_of_le hle).index_ne_zero

theorem idx_latA_ne_zero : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m : ℕ), 0 < m → ∀ T : Submodule (𝓞 D.host.E) (XA D N N'), (∀ ζ ∈ T, m • ζ ∈ latA D cc N N') → idx (latA D cc N N') T ≠ 0 := by
  intro D hD cc δ hc N N' m hm T hT
  obtain ⟨-, -, -, -, ⟨m₁, hm₁, h₁⟩, m₂, hm₂, h₂⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hD cc δ hc N N'
  have hk : 0 < m₁ * m := Nat.mul_pos hm₁ hm
  have hu : IsUnit ((m₁ * m : ℕ) : AE D) := by
    have := (IsUnit.mk0 ((m₁ * m : ℕ) : D.host.E) (Nat.cast_ne_zero.2 hk.ne')).map (inc D)
    rwa [map_natCast] at this
  refine relIndex_ne_zero_of_denom (OhE D) (IhE D cc) (m₁ * m) m₂ hu
    (GlobalTheory.HeckeVal.finite_quot D _ (Nat.mul_pos hk hm₂)) h₂ _ _ (fun ζ h => mem_latA.2 h) fun ζ hζ i j => ?_
  have h := h₁ _ (mem_latA.1 (hT ζ hζ) i j)
  rw [Matrix.smul_apply, nsmul_eq_mul, ← mul_assoc] at h
  rwa [Nat.cast_mul]

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaussianUnitaryPos
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem integral_gaussian_unitary_pos : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, 0 < κ ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet
  obtain ⟨n, e, l, he, hl⟩ := GlobalTheory.UnitaryTheta.unitary_exists_orthonormal_eigenbasis V H hH a ha
  have hb : ∀ i, (1 - (a : V →ₗ[ℂ] V)) (e i) = (1 - l i) • e i := fun i => by
    simp [(hl i).2, sub_smul]
  have hd := det_of_eigen e _ _ hb
  have hr : ∀ z i, e.repr (z - a z) i = (1 - l i) * e.repr z i := fun z i => by
    simpa using repr_apply_of_eigen e _ _ hb z i
  have hne : ∀ i, 1 - l i ≠ 0 := fun i => by
    rw [hd] at hdet
    exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
  have hre : ∀ i, 0 < (1 - l i).re := fun i => by
    have h1 : (l i).re ≤ 1 := (hl i).1 ▸ re_le_norm (l i)
    have h2 : (l i).re ≠ 1 := by
      intro h
      apply hne i
      have h3 : (l i).re * (l i).re + (l i).im * (l i).im = 1 := by
        rw [← normSq_apply, normSq_eq_norm_sq, (hl i).1]; norm_num
      have h4 : (l i).im = 0 := by
        rw [h] at h3
        exact mul_self_eq_zero.1 (by linarith)
      apply Complex.ext <;> simp [h, h4]
    simp only [sub_re, one_re]
    exact sub_pos.2 (lt_of_le_of_ne h1 h2)
  let T : V ≃L[ℂ] (Fin n → ℂ) := e.equivFun.toContinuousLinearEquiv
  let Tm : V ≃ᵐ (Fin n → ℂ) := T.toHomeomorph.toMeasurableEquiv
  have hT : ∀ z i, Tm z i = e.repr z i := fun z i => rfl
  haveI : (μ.map Tm).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hν := Measure.isAddLeftInvariant_eq_smul (μ.map Tm) (volume : Measure (Fin n → ℂ))
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map Tm) (volume : Measure (Fin n → ℂ))
  set c := Measure.addHaarScalarFactor (μ.map Tm) (volume : Measure (Fin n → ℂ)) with hc
  refine ⟨(c : ℝ), by exact_mod_cast hpos, fun y v => ?_⟩
  let g : Fin n → ℂ → ℂ := fun i z => cexp (-(π : ℂ) * (1 - l i) * (z * conj z) +
    π * (((1 - l i) * e.repr y i) * conj z) + π * (z * conj (e.repr v i)))
  have hg := fun i => GlobalTheory.T.integral_cexp_complex_gaussian_linear (1 - l i) ((1 - l i) * e.repr y i) (e.repr v i) (hre i)
  have hF : (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) =
      (fun x : Fin n → ℂ => ∏ i, g i (x i)) ∘ Tm := by
    funext z
    simp only [Function.comp, g, hT, ← Complex.exp_sum, sesq_eq_sum_repr H e he, hr, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint : Integrable (fun x : Fin n → ℂ => ∏ i, g i (x i)) volume :=
    Integrable.fintype_prod (f := g) fun i => (hg i).1
  rw [hF]
  refine ⟨?_, ?_⟩
  · rw [← integrable_map_equiv, hν]
    exact hint.smul_measure_nnreal
  · have h1 := integral_map_equiv (μ := μ) Tm (fun x : Fin n → ℂ => ∏ i, g i (x i))
    simp only [Function.comp_def]
    rw [← h1, hν, integral_smul_nnreal_measure, integral_fintype_prod_volume_eq_prod, hd,
      sesq_eq_sum_repr H e he, Finset.mul_sum, Complex.exp_sum]
    have h2 : ∀ i, ∫ z, g i z = (1 - l i)⁻¹ * cexp (π * (e.repr y i * conj (e.repr v i))) := fun i => by
      rw [show ∫ z, g i z = _ from (hg i).2]
      congr 2
      field_simp [hne i]
    simp only [h2, Finset.prod_mul_distrib, Finset.prod_inv_distrib, NNReal.smul_def, real_smul]
    ring

end GlobalTheory.UnitaryTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaussianUnitaryStatement
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_cexp_herm_gaussian_eq_div_det : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  first | exact @GlobalTheory.UnitaryTheta.integral_gaussian_unitary | exact GlobalTheory.UnitaryTheta.integral_gaussian_unitary | (intros; apply GlobalTheory.UnitaryTheta.integral_gaussian_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicDataStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admJ_and_torsion_data_algebraic : ∀ (D : D7), admG1 D → GL3Theta.admJ D ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → DataIn D (tor0 D cc δ) Qbar ∧ ∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ Qbar ∧ wpD (lamOf D cc δ) t ∈ Qbar := by
  first | exact @GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data | exact GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data | (intros; apply GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralSeriesOfCommonDivisorLineProducts
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem dvd_pow_prod_sub {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ] (d : R) (a : ι → R)
    (b : κ → R) (ha : d ∣ (∏ i, a i) ^ 2) (hb : d ∣ ∏ j, b j) :
    ∃ N : ℕ, d ∣ (∏ i, ∏ j, (b j - a i)) ^ N := by
  have h : (∏ i, ∏ j, (b j - a i)) ∈ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hle, hP⟩
    have h1 : (∏ i, a i) ∈ P := hP.mem_of_pow_mem 2 (hle (Ideal.mem_span_singleton.2 ha))
    have h2 : (∏ j, b j) ∈ P := hle (Ideal.mem_span_singleton.2 hb)
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h1
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.1 h2
    exact Ideal.IsPrime.prod_mem_iff.2 ⟨i, Finset.mem_univ _,
      Ideal.IsPrime.prod_mem_iff.2 ⟨j, Finset.mem_univ _, P.sub_mem hj hi⟩⟩
  obtain ⟨N, hN⟩ := h
  exact ⟨N, Ideal.mem_span_singleton.1 hN⟩

noncomputable def bddSubring (p : ℕ) [Fact p.Prime] : Subring (PowerSeries ℂ_[p]) where
  carrier := {f | BddSer f}
  mul_mem' ha hb := ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ ha hb).2.2
  add_mem' ha hb := ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ ha hb).1
  one_mem' := by simpa using ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 1).1
  zero_mem' := by simpa using ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 0).1
  neg_mem' {x} hx := by
    obtain ⟨B, hB⟩ := hx
    exact ⟨B, fun n => by simpa using hB n⟩

theorem intSer_of_common_divisor (p : ℕ) [Fact p.Prime] (m n : ℕ) (e Ψ A B : PowerSeries ℂ_[p])
    (y : Fin m → ℂ_[p]) (y' : Fin n → ℂ_[p]) (he : BddSer e) (hΨ : BddSer Ψ) (hA : BddSer A)
    (hB : BddSer B) (h1 : PowerSeries.constantCoeff Ψ = 1)
    (hΨA : Ψ * A = (∏ i, lineSer e (y i)) ^ 2) (hΨB : Ψ * B = ∏ j, lineSer e (y' j))
    (hy : ∀ i j, y i ≠ y' j) : IntSer Ψ := by
  have hl : ∀ x : ℂ_[p], lineSer e x ∈ bddSubring p := fun x =>
    (bddSubring p).sub_mem he ((bddSubring p).mul_mem ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 x).1
      ((bddSubring p).pow_mem (show BddSer _ from ⟨1, (GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.2.1⟩) 2))
  obtain ⟨N, H, hH⟩ := dvd_pow_prod_sub (R := bddSubring p) ⟨Ψ, hΨ⟩
    (fun i => ⟨lineSer e (y i), hl _⟩) (fun j => ⟨lineSer e (y' j), hl _⟩)
    ⟨⟨A, hA⟩, Subtype.ext (by simpa using hΨA.symm)⟩
    ⟨⟨B, hB⟩, Subtype.ext (by simpa using hΨB.symm)⟩
  set c : ℂ_[p] := (∏ i, ∏ j, (y i - y' j)) ^ N with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ =>
    Finset.prod_ne_zero_iff.2 fun j _ => sub_ne_zero.2 (hy i j))
  have key : Ψ * (H : PowerSeries ℂ_[p]) = PowerSeries.monomial (2 * n * m * N) c := by
    have h := congrArg Subtype.val hH
    have e1 : ∀ i j, lineSer e (y' j) - lineSer e (y i) =
        PowerSeries.C (y i - y' j) * PowerSeries.X ^ 2 := fun i j => by
      simp only [lineSer, map_sub]; ring
    simp only [SubmonoidClass.coe_pow, Subring.coe_mul, SubmonoidClass.coe_finsetProd,
      AddSubgroupClass.coe_sub, e1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_pow, ← pow_mul] at h
    rw [← h, PowerSeries.monomial_eq_C_mul_X_pow, hc]
    simp only [map_pow, map_prod, mul_assoc]
  have hHc : PowerSeries.coeff (2 * n * m * N) (H : PowerSeries ℂ_[p]) = c := by
    have hinv : Ψ⁻¹ * Ψ = 1 := PowerSeries.inv_mul_cancel _ (by simp [h1])
    have : (H : PowerSeries ℂ_[p]) = PowerSeries.X ^ (2 * n * m * N) * (PowerSeries.C c * Ψ⁻¹) := by
      have h2 := congrArg (Ψ⁻¹ * ·) key
      simp only [← mul_assoc, hinv, one_mul, PowerSeries.monomial_eq_C_mul_X_pow] at h2
      rw [h2]; ring
    rw [this, PowerSeries.coeff_X_pow_mul']
    simp [h1]
  intro i
  have := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p Ψ H ‖c‖ hΨ H.2 (fun k => by
    rw [key, PowerSeries.coeff_monomial]
    split_ifs <;> simp) i (2 * n * m * N)
  rw [hHc] at this
  exact le_of_mul_le_mul_right (by simpa using this) (norm_pos_iff.2 hc0)

end GlobalTheory.EvenTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuumStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.om_eq_mul_pull_of_om_eq_on_vacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), (∀ F ∈ TT D (tor0 D cc δ) N N', ∃ (k : ℕ) (r : Fin k → ℂ) (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), F = ∑ i, r i • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0) → ∀ (W : WeilO D cc δ N N' e0) (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (a : ℂ), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → (W.Om γA γA' e0 = fun z => a * pull D (tor0 D cc δ) γ γ' e0 z) → ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om γA γA' F = fun z => a * pull D (tor0 D cc δ) γ γ' F z := by
  first | exact @GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum | exact GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum | (intros; apply GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReciprocityLargeLevel
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem reciprocity_large_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb, hab⟩ := T.io_surj f
  have hbK : T.io b ≠ 0 := by
    intro h
    exact hb (T.io_inj (by rw [h, map_zero]))
  have hf : f = T.io a / T.io b := by
    rw [eq_div_iff hbK, hab]
  obtain ⟨Na, wa, hNa, hLa⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 a).1 a.2
  obtain ⟨Nb, wb, hNb, hLb⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 b).1 b.2
  refine ⟨Na * Nb, Nat.mul_pos hNa hNb, ?_⟩
  intro N hN hdiv s d hs γ γ' hc
  have hLa' : Lv ε.range N wa a :=
    GlobalTheory.T.lv_mono_of_dvd_of_le ε.range Na N wa wa a hN (dvd_trans (dvd_mul_right Na Nb) hdiv) le_rfl hLa
  have hLb' : Lv ε.range N wb b :=
    GlobalTheory.T.lv_mono_of_dvd_of_le ε.range Nb N wb wb b hN (dvd_trans (dvd_mul_left Nb Na) hdiv) le_rfl hLb
  have ra := GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr Ω ε T a N wa hN hLa' s d hs γ γ' hc
  have rb := GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr Ω ε T b N wb hN hLb' s d hs γ γ' hc
  rw [hf, map_div₀, map_div₀, map_div₀, map_div₀, ra, rb]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RelIndexImageOneSubComplexLinearEquiv
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.ThetaCovIndex

open GlobalTheory.ThetaInter Module

section General

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
set_option backward.isDefEq.respectTransparency false in

theorem relIndex_eq_abs_det {ι : Type} [Fintype ι] [DecidableEq ι] (b₁ b₂ : Basis ι ℝ W) {L₁ L₂ : AddSubgroup W}
    (h₁ : (Submodule.span ℤ (Set.range b₁)).toAddSubgroup = L₁)
    (h₂ : (Submodule.span ℤ (Set.range b₂)).toAddSubgroup = L₂) (h : L₁ ≤ L₂) :
    (L₁.relIndex L₂ : ℝ) = |b₂.det b₁| := by
  subst h₁ h₂
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ h (b₁.restrictScalars ℤ) (b₂.restrictScalars ℤ),
    Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  have := b₂.restrictScalars_repr_apply ℤ
    ⟨b₁.restrictScalars ℤ j, h (Submodule.coe_mem _)⟩ i
  refine this.trans ?_
  simp

theorem exists_basis_finrank {A : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) :
    ∃ b : Basis (Fin (finrank ℝ W)) ℝ W, (Submodule.span ℤ (Set.range b)).toAddSubgroup = A := by
  have : DiscreteTopology A.toIntSubmodule := hA
  have : IsZLattice ℝ A.toIntSubmodule := ⟨hsp⟩
  let b₀ := Module.finBasisOfFinrankEq ℤ A.toIntSubmodule (ZLattice.rank ℝ A.toIntSubmodule)
  refine ⟨b₀.ofZLatticeBasis ℝ A.toIntSubmodule, ?_⟩
  rw [Basis.ofZLatticeBasis_span]
  rfl

theorem relIndex_map {A B : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) (f : W ≃ₗ[ℝ] W) (hB : B ≤ A)
    (hf : B.map (f : W →ₗ[ℝ] W).toAddMonoidHom ≤ A) {m : ℕ} (hm : 0 < m)
    (hx : ∀ x ∈ A, ∃ y ∈ B, m • x = f y) :
    B.relIndex A ≠ 0 ∧ ((B.map (f : W →ₗ[ℝ] W).toAddMonoidHom).relIndex A : ℝ) =
      B.relIndex A * |LinearMap.det (f : W →ₗ[ℝ] W)| := by
  have hBd : DiscreteTopology B := DiscreteTopology.of_subset hA hB
  have hBs : Submodule.span ℝ (B : Set W) = ⊤ := by
    have h1 : (Submodule.span ℝ (B : Set W)).map (f : W →ₗ[ℝ] W) = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      intro x hxA
      obtain ⟨y, hy, e⟩ := hx x hxA
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      refine ⟨(m : ℝ)⁻¹ • y, Submodule.smul_mem _ _ (Submodule.subset_span hy), ?_⟩
      simp only [LinearEquiv.coe_coe, map_smul]
      rw [← e, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, e⟩ := (h1.ge (Submodule.mem_top (x := f x)))
    exact f.injective e ▸ hy
  obtain ⟨a, ha⟩ := exists_basis_finrank hA hsp
  obtain ⟨b, hb⟩ := exists_basis_finrank hBd hBs
  have hb₁ : (Submodule.span ℤ (Set.range (b.map f))).toAddSubgroup =
      B.map (f : W →ₗ[ℝ] W).toAddMonoidHom := by
    ext y
    obtain ⟨x, rfl⟩ := f.surjective y
    have : f x ∈ B.map (f : W →ₗ[ℝ] W).toAddMonoidHom ↔ x ∈ B :=
      AddSubgroup.mem_map_iff_mem (f := (f : W →ₗ[ℝ] W).toAddMonoidHom) f.injective
    rw [this, ← hb, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
      Module.Basis.mem_span_iff_repr_mem, Module.Basis.mem_span_iff_repr_mem]
    simp
  have e1 := relIndex_eq_abs_det b a hb ha hB
  generalize B.map (f : W →ₗ[ℝ] W).toAddMonoidHom = C at hf hb₁ ⊢
  have e2 := relIndex_eq_abs_det (b.map f) a hb₁ ha hf
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, Nat.cast_zero, eq_comm, abs_eq_zero] at e1
    exact IsUnit.ne_zero (a.isUnit_det b) e1
  · rw [e2, e1, ← abs_mul, mul_comm, ← a.det_comp (f : W →ₗ[ℝ] W) b, Basis.coe_map]
    rfl

end General

theorem relIndex_image_one_sub_complexLinearEquiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {A A₁ : AddSubgroup W} (t₁ : DiscreteTopology A) (s₁ : Submodule.span ℝ (A : Set W) = ⊤)
    (u : W ≃ₗ[ℂ] W) (hA : ∀ x, x ∈ A ↔ u x ∈ A₁)
    (hdet : LinearMap.det (LinearMap.id - (u.symm : W →ₗ[ℂ] W)) ≠ 0) {m : ℕ} (hm : 0 < m)
    (hx : ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) :
    A₁.relIndex A ≠ 0 ∧
      (((A.map (LinearMap.id - (u.symm : W →ₗ[ℂ] W)).toAddMonoidHom).relIndex A : ℕ) : ℝ) =
        (A₁.relIndex A : ℝ) * ‖LinearMap.det (LinearMap.id - (u.symm : W →ₗ[ℂ] W))‖ ^ 2 := by
  set g : W →ₗ[ℂ] W := LinearMap.id - (u.symm : W →ₗ[ℂ] W) with hg
  have hgy : ∀ y, g y = y - u.symm y := fun y => rfl
  let f : W ≃ₗ[ℝ] W := (LinearMap.equivOfDetNeZero g hdet).restrictScalars ℝ
  have hfg : (f : W →ₗ[ℝ] W) = g.restrictScalars ℝ := by
    ext1 y; simp [f]
  have hfy : ∀ y, f y = y - u.symm y := fun y => congrArg (fun φ => φ y) hfg
  have hA' : ∀ y, u.symm y ∈ A ↔ y ∈ A₁ := fun y => by rw [hA, u.apply_symm_apply]
  have hinf : (A₁ ⊓ A).map (f : W →ₗ[ℝ] W).toAddMonoidHom = A.map g.toAddMonoidHom ⊓ A := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy₁, hy⟩, rfl⟩
      refine ⟨⟨y, hy, (hfy y).symm⟩, ?_⟩
      change f y ∈ A
      rw [hfy]
      exact A.sub_mem hy ((hA' y).2 hy₁)
    · rintro ⟨⟨y, hy, rfl⟩, h2⟩
      refine ⟨y, ⟨(hA' y).1 ?_, hy⟩, hfy y⟩
      have h3 : y - u.symm y ∈ A := h2
      simpa using A.sub_mem hy h3
  have key := relIndex_map (B := A₁ ⊓ A) t₁ s₁ f inf_le_right (hinf.le.trans inf_le_right) hm
    fun x hxA => by
      obtain ⟨y, hy, hy', e⟩ := hx x hxA
      exact ⟨y, ⟨(hA' y).1 hy', hy⟩, e.trans (hfy y).symm⟩
  rw [hinf, AddSubgroup.inf_relIndex_right, AddSubgroup.inf_relIndex_right, hfg,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity)] at key
  exact key

theorem relIndex_one_sub : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → A₁.relIndex A ≠ 0 ∧ ((((A.map (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')).toAddMonoidHom).relIndex A : ℕ) : ℝ)) = (A₁.relIndex A : ℝ) * ‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ ^ 2 := by
  intro D cc δ hc N N' A A₁ h₁ _ u _ hA hdet ⟨m, hm, hx⟩
  obtain ⟨f₁, s₁, d₁, -⟩ := klat_facts hc h₁
  have t₁ := discrete_of_selfDual (isHerm_sesqOf D (tor0 D cc δ) N N') d₁ f₁
  exact relIndex_image_one_sub_complexLinearEquiv t₁ s₁ u hA hdet hm hx

end GlobalTheory.ThetaCovIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeAgreeOfTrivialAtPrimeStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLattice_agree_of_trivialAt_prime : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' q : ℕ) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TrivAt D q (k : GL (Fin N) (AE D)) → TrivAt D q (k' : GL (Fin N') (AE D)) → Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → (∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₂ L₂') ∧ (∀ x ∈ La D (tor0 D cc δ) L₂ L₂', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₁ L₁') := by
  first | exact @GlobalTheory.NormSum.La_agree_of_trivAt | exact GlobalTheory.NormSum.La_agree_of_trivAt | (intros; apply GlobalTheory.NormSum.La_agree_of_trivAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwinerUnitary_all : ∀ D : D7, IntertwinerUnitary D := by
  first | exact @GlobalTheory.theta_translation_intertwiner_unitary | exact GlobalTheory.theta_translation_intertwiner_unitary | (intros; apply GlobalTheory.theta_translation_intertwiner_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqCocycleSum
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TripleConstant

theorem Wd_mul_sum (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') (c : ℂ) {ι : Type} (s : Finset ι)
    (G : ι → VC D N N' → ℂ) (v : VC D N N') :
    Wd D T y (fun z => c * ∑ i ∈ s, G i z) v = c * ∑ i ∈ s, Wd D T y (G i) v := by
  simp only [Wd, U, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem out_mem_iff {V : Type} [AddCommGroup V] (A B : AddSubgroup V) (q : B ⧸ A.addSubgroupOf B) :
    ((Quotient.out q : B) : V) ∈ A ↔ q = 0 := by
  rw [← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']

theorem mu_form : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → ∃ r : ℝ, 0 < r ∧ μ * (r : ℂ) = ∑ᶠ p : (A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂), (if ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁ then bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N') else 0) := by
  intro D T N N' A₁ A₂ A₃ e μ h
  obtain ⟨h1, h2, h3, n12, n23, n13, he, he0, -, hI⟩ := h
  haveI f12 : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.fintypeOfIndexNeZero n12
  haveI f23 : Fintype (A₃ ⧸ A₂.addSubgroupOf A₃) := AddSubgroup.fintypeOfIndexNeZero n23
  haveI f13 : Fintype (A₃ ⧸ A₁.addSubgroupOf A₃) := AddSubgroup.fintypeOfIndexNeZero n13
  rw [h3.Iop_eq A₂, h2.Iop_eq A₁, h3.Iop_eq A₁] at hI
  simp only [finsum_eq_sum_of_fintype] at hI ⊢
  have p12 : 0 < Real.sqrt ((A₁.addSubgroupOf A₂).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n12))
  have p23 : 0 < Real.sqrt ((A₂.addSubgroupOf A₃).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n23))
  have p13 : 0 < Real.sqrt ((A₁.addSubgroupOf A₃).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n13))
  generalize Real.sqrt ((A₁.addSubgroupOf A₂).index : ℝ) = s12 at *
  generalize Real.sqrt ((A₂.addSubgroupOf A₃).index : ℝ) = s23 at *
  generalize Real.sqrt ((A₁.addSubgroupOf A₃).index : ℝ) = s13 at *
  have key := GlobalTheory.T.thetaTranslate_combination_coef_eq_zero D T N N' A₁ h1 e he he0
    (((A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂)) ⊕ (A₃ ⧸ A₁.addSubgroupOf A₃))
    (Sum.elim (fun p => (s23 : ℂ)⁻¹ * (s12 : ℂ)⁻¹ *
        bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N'))
      (fun _ => -(μ * (s13 : ℂ)⁻¹)))
    (Sum.elim (fun p => ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N'))
      (fun q => ((Quotient.out q : A₃) : VC D N N'))) (by
      intro v
      have hv := congrFun hI v
      simp only [Wd_mul_sum, Wd_Wd, Pi.smul_apply, smul_eq_mul] at hv
      simp only [Finset.mul_sum] at hv
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, neg_mul,
        Finset.sum_neg_distrib, mul_assoc]
      rw [hv]; ring)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, out_mem_iff, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at key
  refine ⟨s23 * s12 / s13, by positivity, ?_⟩
  have q12 : (s12 : ℂ) ≠ 0 := by exact_mod_cast p12.ne'
  have q23 : (s23 : ℂ) ≠ 0 := by exact_mod_cast p23.ne'
  have q13 : (s13 : ℂ) ≠ 0 := by exact_mod_cast p13.ne'
  have k2 := congrArg (fun t => (s23 : ℂ) * s12 * t) (add_neg_eq_zero.1 key)
  simp only [Finset.mul_sum] at k2
  have : μ * ((s23 * s12 / s13 : ℝ) : ℂ) = (s23 : ℂ) * s12 * (μ * (s13 : ℂ)⁻¹) := by
    push_cast; ring
  rw [this, ← k2]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁
  · simp only [hp, if_true]
    field_simp
  · simp only [hp, if_false, mul_zero]

end GlobalTheory.TripleConstant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDataOfNeighbourTripleStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTripleData_of_neighbourTriple : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → ∀ A B C : Lat D N', Tri D P A B C → TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) A) (La D (tor0 D cc δ) (stdL D N) B) (La D (tor0 D cc δ) (stdL D N) C) P N := by
  first | exact @GlobalTheory.TriangleColumns.triDat_of_tri | exact GlobalTheory.TriangleColumns.triDat_of_tri | (intros; apply GlobalTheory.TriangleColumns.triDat_of_tri <;> assumption)
end

