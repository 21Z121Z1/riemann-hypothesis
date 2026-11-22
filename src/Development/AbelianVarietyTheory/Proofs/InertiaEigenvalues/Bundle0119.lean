import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0090
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0102
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0093
import ReciprocityTheory.NeutralLocalFields.Bundle0001
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0080
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0110
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityFixedDvdWeilGroupDegree
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

open NumberField IsDedekindDomain Polynomial in
private theorem dvd_of_primitiveRoot_pow_pow_eq_self {Ω : Type} [Field Ω] {q k m : ℕ} (hq : 1 < q)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ (q ^ k - 1)) (hpos : 0 < q ^ k - 1) (hm : ζ ^ q ^ m = ζ) :
    k ∣ m := by
  have hz : ζ ≠ 0 := hζ.ne_zero hpos.ne'
  have h1 : q ^ k - 1 ∣ q ^ m - 1 := by
    apply hζ.dvd_of_pow_eq_one
    have h0 : ζ ^ (q ^ m - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega)), one_mul]
      exact hm
    exact mul_right_cancel₀ hz h0
  have h2 := Nat.pow_sub_one_gcd_pow_sub_one q k m
  rw [Nat.gcd_eq_left h1] at h2
  have h3 : q ^ k = q ^ Nat.gcd k m := by
    have := Nat.one_le_pow (Nat.gcd k m) q (by omega)
    have := Nat.one_le_pow k q (by omega)
    omega
  have h4 := Nat.pow_right_injective hq h3
  rw [h4]
  exact Nat.gcd_dvd_right k m

open NumberField IsDedekindDomain Polynomial in

theorem _root_.GlobalTheory.exists_fixed_dvd_deg : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (k : ℕ), 0 < k →
    ∃ ζ : Ω, ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) ζ = ζ → (k : ℤ) ∣ _root_.GlobalTheory.WeilDeligne.deg σ := by
  intro E Ω _ _ _ _ _ A w h k hk
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hq1 : 1 < _root_.Formalism.ConjugateSelfDual.normV w := _root_.GlobalTheory.WeilDeligne.one_lt_normV w
  have hpos : 0 < _root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hk.ne' hq1)
  haveI : NeZero ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : Ω) := ⟨by
    rw [← map_natCast (algebraMap E Ω)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hpos.ne')⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1)
  have hvN : ¬ A.valuation ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : Ω) < 1 := by
    have hmem : ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : 𝓞 E) ∉ w.asIdeal := by
      intro hN
      have h1 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem w.asIdeal
      have h2 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ^ k ∈ w.asIdeal := Ideal.pow_mem_of_mem _ h1 _ hk
      have h3 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ^ k - ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : 𝓞 E) = 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
        ring
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h3 ▸ sub_mem h2 hN))
    simpa using _root_.ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver hmem h 1
  have hζv : A.valuation ζ ≤ 1 := le_of_eq (_root_.ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hpos.ne' hζ.pow_eq_one)
  have hroot : ∀ m : ℕ, (ζ ^ _root_.Formalism.ConjugateSelfDual.normV w ^ m) ^ (_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1) = 1 := by
    intro m
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨ζ, fun σ hσ => ?_⟩
  rcases le_or_gt 0 (_root_.GlobalTheory.WeilDeligne.deg σ) with hd | hd
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hd
    have hact := _root_.GlobalTheory.WeilDeligne.actsAs_of_deg (σ := σ) (a := m) (b := 0)
      (by rw [hm]; simp)
    have hv := hact.2 ζ hζv
    rw [pow_zero, pow_one, hσ] at hv
    have heq := _root_.ReciprocityTheory.Gal.eq_of_pow_eq_one A hvN hζ.pow_eq_one (hroot m) hv
    rw [hm]
    exact Int.natCast_dvd_natCast.2 (dvd_of_primitiveRoot_pow_pow_eq_self hq1 hζ hpos heq.symm)
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hd.le)
    have hact := _root_.GlobalTheory.WeilDeligne.actsAs_of_deg (σ := σ) (a := 0) (b := m)
      (by rw [← hm]; simp)
    have hv := hact.2 ζ hζv
    rw [pow_zero, pow_one, hσ] at hv
    have heq := _root_.ReciprocityTheory.Gal.eq_of_pow_eq_one A hvN (hroot m) hζ.pow_eq_one hv
    rw [← neg_neg (_root_.GlobalTheory.WeilDeligne.deg σ), hm, dvd_neg]
    exact Int.natCast_dvd_natCast.2 (dvd_of_primitiveRoot_pow_pow_eq_self hq1 hζ hpos heq)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualMeasuresAndAbsKScale
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise NNReal ENNReal

noncomputable section

namespace GlobalTheory.JR.MeasScale

theorem fourB_nnreal_smul {V : Type} [MeasurableSpace V] (μ : Measure V) (c : ℝ≥0) (B : V → V → ℂ)
    (f : V → ℂ) (y : V) : fourB (c • μ) B f y = (c : ℂ) * fourB μ B f y := by
  simp only [fourB]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem fourB_const_mul {V : Type} [MeasurableSpace V] (μ : Measure V) (a : ℂ) (B : V → V → ℂ)
    (g : V → ℂ) (y : V) : fourB μ B (fun z => a * g z) y = a * fourB μ B g y := by
  simp only [fourB, mul_assoc]
  exact integral_const_mul a _

theorem fourB_twice_nnreal_smul {V : Type} [MeasurableSpace V] (μ : Measure V) (c : ℝ≥0) (B : V → V → ℂ)
    (f : V → ℂ) (y : V) :
    fourB (c • μ) B (fourB (c • μ) B f) y = (c : ℂ) ^ 2 * fourB μ B (fourB μ B f) y := by
  have h : fourB (c • μ) B f = fun z => (c : ℂ) * fourB μ B f z :=
    funext fun z => fourB_nnreal_smul μ c B f z
  rw [fourB_nnreal_smul, h, fourB_const_mul]
  ring

theorem exists_test_ne_zero {V : Type} [AddCommGroup V] [TopologicalSpace V] [T2Space V]
    (h : ∃ S : Set V, IsOpen S ∧ IsCompact S ∧ S.Nonempty) : ∃ f : V → ℂ, IsTest f ∧ ∃ y, f (-y) ≠ 0 := by
  obtain ⟨S, hSo, hSc, s, hs⟩ := h
  have hcl : IsClosed S := hSc.isClosed
  refine ⟨S.indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, -s, ?_⟩
  · intro t
    have := Set.indicator_const_preimage S t (1 : ℂ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact isOpen_univ
    · exact hSo
    · exact hcl.isOpen_compl
    · exact isOpen_empty
  · exact HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _
  · simp [hs]

theorem selfDual_unique {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (hS : ∃ S : Set V, IsOpen S ∧ IsCompact S ∧ S.Nonempty) (B : V → V → ℂ) {μ μ' : Measure V}
    (h : SelfDual μ B) (h' : SelfDual μ' B) : μ' = μ := by
  obtain ⟨hμ, hF⟩ := h
  obtain ⟨hμ', hF'⟩ := h'
  have e := Measure.isAddLeftInvariant_eq_smul μ' μ
  obtain ⟨f, hf, y, hy⟩ := exists_test_ne_zero hS
  have h1 := hF' f hf y
  rw [e, fourB_twice_nnreal_smul, hF f hf y] at h1
  have hc : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℂ) ^ 2 = 1 :=
    mul_right_cancel₀ hy (h1.trans (one_mul _).symm)
  have hc2 : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℝ) ^ 2 = 1 := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ (μ'.addHaarScalarFactor μ : ℝ≥0) := NNReal.coe_nonneg _
  have hc1 : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℝ) = 1 := by nlinarith
  have hc3 : μ'.addHaarScalarFactor μ = 1 := by exact_mod_cast hc1
  rw [e, hc3, one_smul]

theorem integral_units_smul {L : Type} [CommRing L] [TopologicalSpace L] [IsTopologicalRing L]
    [LocallyCompactSpace L] [T2Space L] [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (μ : Measure L) [μ.IsAddHaarMeasure] (u : Lˣ) (G : L → ℂ) :
    ∫ y, G (u • y) ∂μ = ((distribHaarChar L u : ℝ≥0) : ℂ)⁻¹ * ∫ y, G y ∂μ := by
  let φ := Homeomorph.smul (α := L) u
  have hmap : μ.map (fun y => u • y) = (distribHaarChar L u⁻¹) • μ := by
    ext s hs
    rw [Measure.map_apply (continuous_const_smul u).measurable hs, Set.preimage_smul, Measure.smul_apply,
      ← distribHaarChar_mul μ u⁻¹ s]
    rfl
  have : ∫ y, G y ∂(μ.map fun y => u • y) = ∫ y, G (u • y) ∂μ :=
    φ.measurableEmbedding.integral_map (μ := μ) G
  rw [← this, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, map_inv]
  push_cast
  rfl

end GlobalTheory.JR.MeasScale

namespace GlobalTheory.JR.MeasScale

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def unitL (A : Et F E) (x : A.Kˣ) : A.Lˣ := Units.map (algebraMap A.K A.L : A.K →* A.L) x

theorem unitL_smul (A : Et F E) (x : A.Kˣ) (y : A.L) : unitL A x • y = algebraMap A.K A.L x * y := rfl

theorem kerL_eq (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (y' y : A.L) :
    A.kerL ψ x y' y = A.kerL ψ ((1 : A.Kˣ) : A.K) y' (unitL A x • y) := by
  simp only [Et.kerL, unitL_smul, Units.val_one, one_mul]
  congr 1
  have : star y' * (algebraMap A.K A.L x * y) = (x : A.K) • (star y' * y) := by
    rw [Algebra.smul_def]; ring
  rw [this, map_smul, smul_eq_mul]

theorem kerL_swap (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (y' y : A.L) :
    A.kerL ψ ((1 : A.Kˣ) : A.K) y' (unitL A x • y) = A.kerL ψ ((1 : A.Kˣ) : A.K) (unitL A x • y') y := by
  simp only [Et.kerL, unitL_smul]
  rw [star_mul', A.star_K]
  congr 3
  ring

theorem selfDual_scale [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (h : SelfDual μ (A.kerL ψ ((1 : A.Kˣ) : A.K))) :
    SelfDual (distribHaarChar A.K x • μ) (A.kerL ψ x) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hN : distribHaarChar A.L (unitL A x) = distribHaarChar A.K x ^ 2 := by
    obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
    obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
    have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
    rw [← map_pow]
    refine GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) _ _ ?_
    simp [unitL, A.star_K, pow_two]
  obtain ⟨hμ, hF⟩ := h
  have hc : distribHaarChar A.K x ≠ 0 := distribHaarChar_pos.ne'
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul _ hc, fun f hf y => ?_⟩
  set c := distribHaarChar A.K x with hcdef
  set B1 := A.kerL ψ ((1 : A.Kˣ) : A.K)
  have h1 : ∀ g z, fourB (c • μ) (A.kerL ψ x) g z = (c : ℂ) * fourB μ B1 g (unitL A x • z) := by
    intro g z
    rw [fourB_nnreal_smul]
    simp only [fourB, kerL_eq A ψ x, B1]
  have h2 : fourB (c • μ) (A.kerL ψ x) f = fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z) :=
    funext (h1 f)
  rw [h1, h2]
  have h3 : fourB μ B1 (fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z)) (unitL A x • y) =
      (c : ℂ) * ((distribHaarChar A.L (unitL A x) : ℝ≥0) : ℂ)⁻¹ * fourB μ B1 (fourB μ B1 f) y := by
    rw [fourB_const_mul, mul_assoc]
    congr 1
    have e := integral_units_smul μ (unitL A x) (fun z => fourB μ B1 f z * B1 z y)
    refine Eq.trans ?_ e
    show ∫ y', fourB μ B1 f (unitL A x • y') * B1 y' (unitL A x • y) ∂μ = _
    refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
    exact congrArg _ (kerL_swap A ψ x y' y)
  rw [h3, hF f hf y, hN]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp

theorem meas_scale [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (m : A.Meas ψ) (x : A.Kˣ) :
    m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  have := (inferInstance : Unram F E).charZero
  have hu := ‹Unram F E›.ultraF; have := ‹Unram F E›.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, hS⟩ := EtMeas.top_facts F A.L
  rw [EtMeas.absK_unit, ENNReal.ofReal_coe_nnreal]
  exact selfDual_unique hS _ (selfDual_scale A ψ x (m.μL 1) (m.sdL 1)) (m.sdL x)

end GlobalTheory.JR.MeasScale

theorem GlobalTheory.JR.exists_meas_and_scale : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    Nonempty (A.Meas ψ) ∧ ∀ (m : A.Meas ψ) (x : A.Kˣ), m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  intro F E _ _ _ _ _ A ψ hψ
  exact ⟨(EtMeas.nonempty_meas_and_reps F E A ψ hψ).1, GlobalTheory.JR.MeasScale.meas_scale A ψ⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSurjectiveValuationIsIntegralIffNonneg
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem exists_surjective_valuation_isIntegral_iff (K : UQ) (L : Type) [Field L] [Algebra K.E L]
    [Algebra K.O L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L] :
    ∃ v : Lˣ →* Multiplicative ℤ, Function.Surjective v ∧
      ∀ x : Lˣ, IsIntegral K.O (x : L) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
  haveI hdvr := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure K.O K.E L
  haveI hfr := integralClosure.isFractionRing_of_finite_extension (A := K.O) K.E L
  set R := integralClosure K.O L
  let P := IsDiscreteValuationRing.maximalIdeal R
  let u : Lˣ →* Multiplicative ℤ := WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (P.valuation L).toMonoidWithZeroHom.toMonoidHom)
  have hu : ∀ x : Lˣ, ((u x : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = P.valuation L x := by
    intro x
    simp [u, WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  have key : ∀ x : L, x ≠ 0 → (IsIntegral K.O x ↔ P.valuation L x ≤ 1) := by
    intro x hx
    rw [← mem_integralClosure_iff]
    constructor
    · intro h
      have : x = algebraMap R L ⟨x, h⟩ := rfl
      rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    · intro h
      rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
      · rw [← hr]; exact r.2
      · by_cases hrm : r ∈ IsLocalRing.maximalIdeal R
        · exfalso
          have h1 : P.valuation L (algebraMap R L r) < 1 :=
            (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem P r).2 hrm
          rw [hr] at h1
          have h2 : P.valuation L x * P.valuation L x⁻¹ = 1 := by
            rw [← map_mul, mul_inv_cancel₀ hx, map_one]
          have h3 : P.valuation L x * P.valuation L x⁻¹ < 1 :=
            lt_of_le_of_lt (mul_le_of_le_one_left' h) h1
          exact (ne_of_lt h3) h2
        · have hru : IsUnit r := by
            by_contra hh; exact hrm ((IsLocalRing.mem_maximalIdeal r).2 hh)
          obtain ⟨s, hs⟩ := hru
          have : x = algebraMap R L (s⁻¹ : Rˣ) := by
            have e1 : algebraMap R L (s : R) * algebraMap R L ((s⁻¹ : Rˣ) : R) = 1 := by
              rw [← map_mul, Units.mul_inv, map_one]
            rw [hs, hr] at e1
            exact (inv_mul_eq_one₀ hx).1 e1
          rw [this]; exact ((s⁻¹ : Rˣ) : R).2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : algebraMap R L π ≠ 0 := by
    intro h
    exact hπ.ne_zero ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective R L) _ h)
  let πL : Lˣ := Units.mk0 _ hπ0
  have huπ : u πL = Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [hu]
    change P.valuation L (algebraMap R L π) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_singleton P hπ.ne_zero hπ.maximalIdeal_eq]
    rfl
  refine ⟨u⁻¹, ?_, ?_⟩
  · intro n
    refine ⟨πL ^ (Multiplicative.toAdd n), ?_⟩
    rw [map_zpow, MonoidHom.inv_apply, huπ, ← ofAdd_neg, neg_neg, ← ofAdd_zsmul, smul_eq_mul, mul_one]
    rfl
  · intro x
    rw [key _ x.ne_zero, ← hu, MonoidHom.inv_apply, toAdd_inv, neg_nonneg, ← WithZero.coe_one,
      WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one]

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitLeftMulMatrixOfCommuteCompanionStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_leftMulMatrix_of_commute_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (t : GL (Fin r) F), (t : Matrix (Fin r) (Fin r) F) * companion p = companion p * (t : Matrix (Fin r) (Fin r) F) → ∃ t₁ : A.Kˣ, LinDesc.tm A hG t₁ = t := by
  first | exact @GlobalTheory.JR.LinDesc.centr | exact GlobalTheory.JR.LinDesc.centr | (intros; apply GlobalTheory.JR.LinDesc.centr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleHermitianPairNormPropertiesStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteEtaleHermitianPair_norm_properties : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) := by
  first | exact @GlobalTheory.JR.Et.norm_facts | exact GlobalTheory.JR.Et.norm_facts | (intros; apply GlobalTheory.JR.Et.norm_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRatStatement
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGaloisInertia_lifts_absoluteInertia_rat : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (M : IntermediateField ℚ Ω) [FiniteDimensional ℚ M] [IsGalois ℚ M] (τ : M ≃ₐ[ℚ] M), (∀ x : M, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) → (∀ x : M, A.valuation ((τ x : M) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) → ∃ σ ∈ Ine (F := ℚ) A, ∀ x : M, σ (x : Ω) = (τ x : Ω) := by
  first | exact @GlobalTheory.InertiaLift.main | exact GlobalTheory.InertiaLift.main | (intros; apply GlobalTheory.InertiaLift.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtensionStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_places_inertia_not_fixing_finiteExtension : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L], {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ ¬ Ine (F := F) B ≤ L.fixingSubgroup}.Finite := by
  first | exact @GlobalTheory.InertiaAlmostAll.finite_ramified | exact GlobalTheory.InertiaAlmostAll.finite_ramified | (intros; apply GlobalTheory.InertiaAlmostAll.finite_ramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitsQuotSqFiniteEtaleHermitianPairStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_units_quot_sq_finiteEtaleHermitianPair : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range) := by
  first | exact @GlobalTheory.Et.finite_units_quot_sq | exact GlobalTheory.Et.finite_units_quot_sq | (intros; apply GlobalTheory.Et.finite_units_quot_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierEtaleKEqIntegralPartialFourierStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierEtaleK_eq_integral_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → ∀ b c : A.K, A.fourK μK ψ φ' (b, c) = fourB μK (A.kerK ψ) (fun c' => A.tilde μK ψ φ' c' c) b := by
  first | exact @GlobalTheory.FourKFub.fourK_eq_fourB_tilde | exact GlobalTheory.FourKFub.fourK_eq_fourB_tilde | (intros; apply GlobalTheory.FourKFub.fourK_eq_fourB_tilde <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisAddHomVanishesComplexConjugationStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisAddHom_vanishes_complexConjugation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    ∀ (c : Ω ≃ₐ[E] Ω), IsComplexConjugation c → z c = 0 := by
  first | exact @GlobalTheory.addHom_complexConjugation_eq_zero | exact GlobalTheory.addHom_complexConjugation_eq_zero | (intros; apply GlobalTheory.addHom_complexConjugation_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityLaurentShiftEqSumSen
section
noncomputable section
namespace GlobalTheory.PhiGam.Range
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem finite_map_trans {k U : Type} [Field k] [AddCommGroup U] [Module k U] {P Q S : Submodule k U}
    (hSQ : S ≤ Q) (h1 : FiniteDimensional k (P.map Q.mkQ)) (h2 : FiniteDimensional k (Q.map S.mkQ)) :
    FiniteDimensional k (P.map S.mkQ) := by
  refine Module.Finite.iff_fg.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.factor hSQ) ?_ ?_)
  · rw [← Submodule.map_comp, Submodule.factor_comp_mk]
    exact Module.Finite.iff_fg.mp h1
  · have hle : P.map S.mkQ ⊓ LinearMap.ker (Submodule.factor hSQ) ≤ Q.map S.mkQ := by
      rintro _ ⟨⟨p, -, rfl⟩, hp⟩
      exact ⟨p, (Submodule.Quotient.mk_eq_zero Q).mp hp, rfl⟩
    exact Module.Finite.iff_fg.mp (Submodule.finiteDimensional_of_le hle)

theorem finite_quot_of_map {k U : Type} [Field k] [AddCommGroup U] [Module k U] {P S : Submodule k U}
    (h : FiniteDimensional k (P.map S.mkQ)) : FiniteDimensional k (↥P ⧸ S.submoduleOf P) := by
  have hker : LinearMap.ker (S.mkQ ∘ₗ P.subtype) = S.submoduleOf P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
  have hr : LinearMap.range (S.mkQ ∘ₗ P.subtype) = P.map S.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  haveI : FiniteDimensional k (LinearMap.range (S.mkQ ∘ₗ P.subtype)) := by rw [hr]; exact h
  rw [← hker]
  exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm

theorem gmult_self {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P : Submodule k U) (x : k) : gmult T P P x = 0 := by
  unfold gmult
  set P' := P ⊓ ⨆ m : ℕ, P.comap ((T - algebraMap k (Module.End k U) x) ^ m)
  have h : P.submoduleOf P' = ⊤ := eq_top_iff.mpr fun y _ => y.2.1
  haveI : Subsingleton (↥P' ⧸ P.submoduleOf P') := Submodule.Quotient.subsingleton_iff.mpr h
  exact Module.finrank_zero_of_subsingleton

theorem finite_sh {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
    [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    {N : Submodule k⟦X⟧ V} (hN : IsLat N) (a : ℤ) (m : ℕ) :
    FiniteDimensional k (((sh a N).restrictScalars k).map ((sh (a + m) N).restrictScalars k).mkQ) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero, Submodule.mkQ_map_self]
    infer_instance
  | succ m ih =>
    have h := Window.finite_quot (hN.shift (a + m)).1
    rw [sh_sh_eq, add_comm (1 : ℤ)] at h
    rw [Nat.cast_succ, ← add_assoc]
    exact finite_map_trans (fun y hy => Window.sh_succ_le _ _ hy) ih h

theorem qmult_sh_range : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ) (x : k), qmult g (sh a N) (sh (a + m) N) x = ∑ j ∈ Finset.range m, sen g N (x + (a + j : ℤ)) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC a m x
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero, Finset.sum_range_zero]
    exact gmult_self _ _ _
  | succ m ih =>
    have hf := finite_quot_of_map (finite_sh hN a (m + 1))
    rw [Finset.sum_range_succ, ← ih, ← GlobalTheory.T.senMultiplicity_shift_lattice_variablePow R g hg N hN hC (a + m) x, sen, sh_sh_eq,
      add_comm (1 : ℤ)]
    rw [Nat.cast_succ, ← add_assoc] at hf ⊢
    exact GlobalTheory.T.genEigenMultiplicityQuotient_additive_chain (nab g) _ _ _ (fun y hy => Window.sh_succ_le _ _ hy)
      (fun y hy => Window.sh_add_le a m N hy) (fun y hy => Window.nab_mem_sh R hg hC _ hy)
      (fun y hy => Window.nab_mem_sh R hg hC _ hy) (fun y hy => Window.nab_mem_sh R hg hC _ hy) hf x

end GlobalTheory.PhiGam.Range
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureLUnitSmulAbsKSq
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise

namespace GlobalTheory.JR.ScaleHaarL

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ (c : A.Kˣ) (S : Set A.L), μ {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = ENNReal.ofReal (A.absK (c : A.K) ^ 2) * μ S := by
  intro F E _ _ _ _ U A μ hμ c S
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := GlobalTheory.JR.EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  let u : A.Lˣ := Units.map (algebraMap A.K A.L : A.K →* A.L) c
  have hu : (u : A.L) = algebraMap A.K A.L (c : A.K) := rfl
  have hset : {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = u • S := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, Units.smul_def, hu, smul_eq_mul]
    exact ⟨fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩, fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩⟩
  have hc1 : Continuous (b.equivFun.symm : (Fin 2 → A.K) → A.L) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F)
  have hc2 : Continuous (b.equivFun : A.L → (Fin 2 → A.K)) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)
  let e : (Fin 2 → A.K) ≃ₜ+ A.L :=
    { b.equivFun.symm.toAddEquiv with
      continuous_toFun := hc1
      continuous_invFun := hc2 }
  have key : distribHaarChar A.L u = distribHaarChar A.K c ^ 2 := by
    rw [GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e c u (fun x => ?_),
      GlobalTheory.JR.ModuleNorm.distribHaarChar_pi_two]
    change b.equivFun.symm ((c : A.K) • x) = (u : A.L) * b.equivFun.symm x
    rw [map_smul, Algebra.smul_def, hu]
  rw [hset, ← distribHaarChar_mul μ u S, key, GlobalTheory.JR.EtMeas.absK_unit]
  rw [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.JR.ScaleHaarL
end

