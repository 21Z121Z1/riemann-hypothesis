import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0098
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0070
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0090
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0068
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0084
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0085
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0087
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProper
section
open MeasureTheory Topology Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreUniq

theorem fibreFamily_eq_inter (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (W : Set V) (hW : IsOpen W)
    (B B' : Set X) (hB : IsOpen B) (hB' : IsOpen B') (hBB : B' ⊆ B)
    (fib fib' : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B ∩ W) ν B fib)
    (h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B' ∩ W) ν B' fib')
    (b : X) (hb : b ∈ B') : fib' b = fib b := by
  have hO : IsOpen (g ⁻¹' B' ∩ W) := (hB'.preimage hg).inter hW
  have hOU : g ⁻¹' B' ∩ W ⊆ g ⁻¹' B ∩ W := Set.inter_subset_inter_left _ (Set.preimage_mono hBB)
  have hbB : b ∈ B := hBB hb
  refine measure_eq_of_lintegral_eq (fib' b) (fib b) (g ⁻¹' B' ∩ W) hO ?_ ?_ ?_
  · refine measure_mono_null ?_ (h'.1 b)
    intro v hv hv'
    exact hv hv'.2
  · refine measure_mono_null ?_ (h.1 b)
    intro v hv hv'
    have hgv : g v = b := hι (by rw [← hf v]; exact hv'.1)
    exact hv ⟨show g v ∈ B' from hgv ▸ hb, hv'.2.2⟩
  · intro φ hφc hφs hφO hφnn
    have hφU : tsupport φ ⊆ g ⁻¹' B ∩ W := hφO.trans hOU
    obtain ⟨hint', hcont'⟩ := h'.2.2 φ hφc hφs hφO
    obtain ⟨hint, hcont⟩ := h.2.2 φ hφc hφs hφU
    refine ⟨hint' b hb, ?_⟩
    have hψm : Measurable (fun v => ENNReal.ofReal (φ v)) := hφc.measurable.ennreal_ofReal
    have hψ0 : ∀ v, v ∉ g ⁻¹' B' ∩ W → ENNReal.ofReal (φ v) = 0 := by
      intro v hv
      have hz : φ v = 0 := by
        by_contra hne
        exact hv (hφO (subset_tsupport φ (Function.mem_support.mpr hne)))
      simp [hz]
    have hF : ∀ c ∈ B, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) = ENNReal.ofReal (∫ v, φ v ∂(fib c)) :=
      fun c hc => (ofReal_integral_eq_lintegral_ofReal (hint c hc) (ae_of_all _ hφnn)).symm
    have hF' : ∀ c ∈ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) =
        ENNReal.ofReal (∫ v, φ v ∂(fib' c)) :=
      fun c hc => (ofReal_integral_eq_lintegral_ofReal (hint' c hc) (ae_of_all _ hφnn)).symm
    have hset : ∀ S, MeasurableSet S →
        ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) ∂ν =
          ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) ∂ν := by
      intro S hS
      have hS' : MeasurableSet (S ∩ B') := hS.inter hB'.measurableSet
      have e1 := lintegral_preimage hι hg hf hO hOU h (fun v => ENNReal.ofReal (φ v)) hψm hψ0 _ hS'
      have e2 := lintegral_preimage hι hg hf hO Set.Subset.rfl h' (fun v => ENNReal.ofReal (φ v))
        hψm hψ0 _ hS'
      exact e1.symm.trans e2
    have key : ∀ (k k' : X → ℝ≥0∞) (T : Set X), MeasurableSet T → (∀ c ∈ T, k c = k' c) →
        ∫⁻ c in T, k c ∂ν = ∫⁻ c in T, k' c ∂ν := fun k k' T hT hkk =>
      lintegral_congr_ae ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall hkk))
    have hae : (fun c => ENNReal.ofReal (∫ v, φ v ∂(fib c))) =ᵐ[ν.restrict B']
        (fun c => ENNReal.ofReal (∫ v, φ v ∂(fib' c))) := by
      refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ ?_ ?_ ?_
      · exact ((hcont.mono hBB).aemeasurable hB'.measurableSet).ennreal_ofReal
      · exact (hcont'.aemeasurable hB'.measurableSet).ennreal_ofReal
      · intro S hS _
        rw [Measure.restrict_restrict hS]
        have hT : MeasurableSet (S ∩ B') := hS.inter hB'.measurableSet
        calc ∫⁻ c in S ∩ B', ENNReal.ofReal (∫ v, φ v ∂(fib c)) ∂ν
            = ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) ∂ν :=
              key _ _ _ hT (fun c hc => (hF c (hBB hc.2)).symm)
          _ = ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) ∂ν := hset S hS
          _ = ∫⁻ c in S ∩ B', ENNReal.ofReal (∫ v, φ v ∂(fib' c)) ∂ν :=
              key _ _ _ hT (fun c hc => hF' c hc.2)
    have heq := Measure.eqOn_open_of_ae_eq hae hB'
      (ENNReal.continuous_ofReal.comp_continuousOn (hcont.mono hBB))
      (ENNReal.continuous_ofReal.comp_continuousOn hcont') hb
    rw [hF' b hb, hF b hbB]
    exact heq.symm

end GlobalTheory.CompanionTheory.SW.FibreUniq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultipliableLocalFactors
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem eventually_valued_algebraMap_eq_one (F : Type) [Field F] [NumberField F] (β : F) (hβ : β ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (algebraMap F (Fv F v) β) = 1 := by
  rw [Filter.eventually_cofinite]
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) β).union
    (HeightOneSpectrum.Support.finite (𝓞 F) β⁻¹)).subset ?_
  intro v hv
  have e : Valued.v (algebraMap F (Fv F v) β) = v.valuation F β :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) β
  rw [Set.mem_ofPred_eq, e] at hv
  rcases lt_or_gt_of_ne hv with h | h
  · refine Set.mem_union_right _ ?_
    show 1 < v.valuation F β⁻¹
    exact ((v.valuation F).one_lt_val_iff (inv_ne_zero hβ)).mpr (by rwa [inv_inv])
  · exact Set.mem_union_left _ h

theorem multipliable_localFactors :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), (∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ β : F, β ≠ 0 → Multipliable fun v => g v (algebraMap F (Fv F v) β) := by
  intro F _ _ S C g hg β hβ
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) => C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) :=
    (GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ‖g v (algebraMap F (Fv F v) β) - 1‖ ≤ C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
    filter_upwards [eventually_valued_algebraMap_eq_one F β hβ,
      Set.Finite.compl_mem_cofinite S.finite_toSet] with v hv hvS
    rw [Real.norm_eq_abs, mul_one_div]
    exact hg v hvS _ hv
  have hf : Summable fun v : HeightOneSpectrum (𝓞 F) => g v (algebraMap F (Fv F v) β) - 1 :=
    Summable.of_norm_bounded_eventually hsum hev
  simpa using Real.multipliable_one_add_of_summable hf

end GlobalTheory.CompanionTheory.Mass.MeanV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetConjugateNegOfProd
section
open Formalism.REAL

namespace GlobalTheory.CompanionTheory.Clozel

private theorem neg_one_pow_card_mul_prod_neg_add_conj (u : ℂ) (s : Multiset ℂ) :
    (-1 : ℂ) ^ Multiset.card s * (s.map fun w => -u + (starRingEnd ℂ) w).prod =
      (s.map fun w => u - (starRingEnd ℂ) w).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons, ← ih, pow_succ]
    ring

theorem multiset_eq_map_neg_conj_of_polyEq :
    ∀ (n : ℕ) (m m' : Multiset ℂ), Multiset.card m = n → Multiset.card m' = n →
      (∀ u : ℂ, (m.map (u + ·)).prod =
        (starRingEnd ℂ) (((-1 : ℂ) ^ n) * (m'.map (-(starRingEnd ℂ) u + ·)).prod)) →
      m' = m.map fun z => -(starRingEnd ℂ) z := by
  intro n m m' _ hm' h
  have key : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map fun w => u - (starRingEnd ℂ) w).prod := by
    intro u
    have hc : ((starRingEnd ℂ) ∘ fun w => -(starRingEnd ℂ) u + w) =
        fun w => -u + (starRingEnd ℂ) w := by
      funext w
      simp
    rw [h u, map_mul, map_pow, map_neg, map_one, map_multiset_prod, Multiset.map_map, hc, ← hm',
      neg_one_pow_card_mul_prod_neg_add_conj]
  have hpoly : ((m.map fun z => -z).map fun a => Polynomial.X - Polynomial.C a).prod =
      ((m'.map (starRingEnd ℂ)).map fun a => Polynomial.X - Polynomial.C a).prod := by
    apply Polynomial.funext
    intro u
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def] using key u
  have hroots := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots
  have hinv : (m'.map (starRingEnd ℂ)).map (starRingEnd ℂ) = m' := by
    simp [Multiset.map_map, Function.comp_def]
  rw [← hinv, ← hroots, Multiset.map_map]
  exact Multiset.map_congr rfl fun z _ => by simp

end GlobalTheory.CompanionTheory.Clozel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationOfDichotomy
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonStep

theorem isUnit_or_of_add_quot {S : Type} [CommRing S] (ϖ : S)
    (hj : ϖ ∈ (⊥ : Ideal S).jacobson) (hD : Dich ϖ) (a b : S ⧸ Ideal.span {ϖ ^ 2})
    (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨w', hw'⟩ := h.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w'
  have h1 : (a + b) * w - 1 ∈ Ideal.span {ϖ ^ 2} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_add, map_one]
    rw [hw', sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp h1
  have hu : IsUnit ((a + b) * w) := by
    have h2 := (Ideal.mem_jacobson_bot.mp hj) (ϖ * v)
    have e : (a + b) * w = ϖ * (ϖ * v) + 1 := by linear_combination hv
    rw [e]; exact h2
  have hab : IsUnit (a + b) := isUnit_of_mul_isUnit_left hu
  have hspan : ϖ ^ 0 ∈ Ideal.span {a, b} := by
    obtain ⟨t, ht⟩ := hab.exists_right_inv
    have h3 : (a + b) * t ∈ Ideal.span {a, b} :=
      Ideal.mul_mem_right _ _ (Ideal.add_mem _ (Ideal.subset_span (by simp))
        (Ideal.subset_span (by simp)))
    rw [ht] at h3
    simpa using h3
  rcases hD a b ⟨0, hspan⟩ with h4 | h4
  · right
    exact (isUnit_of_dvd_unit (dvd_add h4 dvd_rfl) hab).map _
  · left
    exact (isUnit_of_dvd_unit (dvd_add dvd_rfl h4) hab).map _

theorem step_comp : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S ⧸ Ideal.span {ϖ ^ 2}) → Step ϖ := by
  intro S _ ϖ hj hnz hD hA Q n hQ hd hn
  have hRoots : Roots ϖ := GlobalTheory.T.polynomial_roots_of_closed_quotient ϖ hj hnz hD hA
  have hq0 : Q.coeff 0 = Q.eval 0 := Polynomial.coeff_zero_eq_eval_zero Q
  have hspan : ϖ ^ (n + 1) ∈ Ideal.span {Q.coeff 0, ϖ ^ (n + 1)} :=
    Ideal.subset_span (by simp)
  rcases hD (Q.coeff 0) (ϖ ^ (n + 1)) ⟨n + 1, hspan⟩ with hdiv | hdiv
  · refine ⟨0, ?_, ?_⟩
    · rw [← hq0]; exact hdiv
    · rw [zero_pow hd.ne']; exact dvd_zero _
  ·
    have hpow : ϖ ^ (n + 1) ∈ nonZeroDivisors S := pow_mem hnz _
    have hcancel : ∀ x : S, Q.coeff 0 * x = 0 → x = 0 := by
      intro x hx
      obtain ⟨e, he⟩ := hdiv
      have h0 : ϖ ^ (n + 1) * x = 0 := by
        rw [he]; linear_combination e * hx
      exact (mem_nonZeroDivisors_iff_right.mp hpow) x (by rw [mul_comm]; exact h0)
    obtain ⟨c, hc1, i0, hi1, hi2, hi3⟩ := GlobalTheory.T.newton_polygon_slope_existence ϖ hD hRoots (fun i => Q.coeff i)
      Q.natDegree (n + 1) hd hQ.coeff_natDegree hdiv
    have hs : ∀ i, ∃ t, (i = 0 → t = 1) ∧
        (i ≤ Q.natDegree → Q.coeff i * c ^ i = Q.coeff 0 * t) := by
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact ⟨1, fun _ => rfl, fun _ => by simp⟩
      · by_cases hid : i ≤ Q.natDegree
        · obtain ⟨t, ht⟩ := hc1 i hi hid
          exact ⟨t, fun h => by omega, fun _ => ht⟩
        · exact ⟨0, fun h => by omega, fun h => by omega⟩
    choose s hs0 hsd using hs
    have hunit : IsUnit (s i0) := by
      obtain ⟨t, ht⟩ := hi3
      have h5 : Q.coeff 0 * (s i0 * t - 1) = 0 := by
        have h6 := hsd i0 hi2
        rw [h6] at ht
        linear_combination -ht
      have h7 := hcancel _ h5
      exact IsUnit.of_mul_eq_one t (by linear_combination h7)
    let R : Polynomial S := ∑ i ∈ Finset.range (Q.natDegree + 1),
      Polynomial.C (s i) * Polynomial.X ^ i
    have hRc : ∀ j, j ≤ Q.natDegree → R.coeff j = s j := by
      intro j hj'
      simp only [R, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq]
      simp [Nat.lt_succ_of_le hj']
    have hRe : ∀ y, R.eval y = ∑ i ∈ Finset.range (Q.natDegree + 1), s i * y ^ i := by
      intro y
      simp [R, Polynomial.eval_finsetSum]
    let P : Polynomial (S ⧸ Ideal.span {ϖ ^ 2}) := R.map (Ideal.Quotient.mk _)
    have hP0 : P.coeff 0 = 1 := by
      simp only [P, Polynomial.coeff_map]
      rw [hRc 0 (Nat.zero_le _), hs0 0 rfl, map_one]
    have hPi : IsUnit (P.coeff i0) := by
      simp only [P, Polynomial.coeff_map]
      rw [hRc i0 hi2]
      exact hunit.map _
    obtain ⟨y', hy'⟩ := GlobalTheory.T.absolutely_closed_unit_coefficient_root hA (isUnit_or_of_add_quot ϖ hj hD) P i0 hP0 hi1 hPi
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
    have hRy : ϖ ^ 2 ∣ R.eval y := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
      simp only [P, Polynomial.eval_map] at hy'
      rwa [Polynomial.eval₂_at_apply] at hy'
    have hQz : Q.eval (c * y) = Q.coeff 0 * R.eval y := by
      rw [Polynomial.eval_eq_sum_range, hRe, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have h8 := hsd i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      rw [mul_pow]
      linear_combination (y ^ i) * h8
    have hn0 : ϖ ^ n ∣ Q.coeff 0 := by rw [hq0]; exact hn
    refine ⟨c * y, ?_, ?_⟩
    · rw [hQz]
      have h9 : ϖ ^ n * ϖ ^ 2 ∣ Q.coeff 0 * R.eval y := mul_dvd_mul hn0 hRy
      refine dvd_trans ?_ h9
      rw [← pow_add]
      exact pow_dvd_pow _ (by omega)
    · have h10 : Q.coeff 0 ∣ c ^ Q.natDegree := by
        have h11 := hc1 Q.natDegree hd le_rfl
        simpa [hQ.coeff_natDegree] using h11
      rw [mul_pow]
      exact dvd_mul_of_dvd_left (dvd_trans hn0 h10) _

end GlobalTheory.CompanionTheory.NewtonStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapThirdProperty
section
open scoped TensorProduct
open IsLocalRing

namespace GlobalTheory.CompanionTheory.UnitNorm

noncomputable section

section Basics

variable {O O' R : Type} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R]

def tw (τ : O' ≃ₐ[O] O') (j : ℕ) : O' ⊗[O] R →ₐ[O] O' ⊗[O] R :=
  Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R)

def nrm (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (s : O' ⊗[O] R) : O' ⊗[O] R :=
  ∏ j ∈ Finset.range ℓ, tw τ j s

abbrev inc : R →ₐ[O] O' ⊗[O] R := Algebra.TensorProduct.includeRight

theorem nrm_mul (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (x y : O' ⊗[O] R) :
    nrm ℓ τ (x * y) = nrm ℓ τ x * nrm ℓ τ y := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_mul, Finset.prod_mul_distrib]

theorem nrm_one (ℓ : ℕ) (τ : O' ≃ₐ[O] O') : nrm ℓ τ (1 : O' ⊗[O] R) = 1 := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_one, Finset.prod_const_one]

theorem map_tw (τ : O' ≃ₐ[O] O') (j : ℕ) (s : O' ⊗[O] R) :
    Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) (tw τ j s) = tw τ (j + 1) s := by
  induction s using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [GlobalTheory.CompanionTheory.UnitNorm.tw, Algebra.TensorProduct.map_tmul, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
      AlgHom.id_apply, pow_succ', AlgEquiv.mul_apply]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tw_period {ℓ : ℕ} {τ : O' ≃ₐ[O] O'} (hτ : τ ^ ℓ = 1) (s : O' ⊗[O] R) :
    tw τ ℓ s = tw τ 0 s := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.tw, hτ, pow_zero]

theorem nrm_fixed {ℓ : ℕ} {τ : O' ≃ₐ[O] O'} (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1) (s : O' ⊗[O] R) :
    Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) (nrm ℓ τ s) = nrm ℓ τ s := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_prod, GlobalTheory.CompanionTheory.UnitNorm.map_tw]
  rw [Finset.prod_range_succ, Finset.prod_range_succ', GlobalTheory.CompanionTheory.UnitNorm.tw_period hτ]

theorem map_inc_map (A : Ideal O) :
    Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) (Ideal.map (algebraMap O R) A) =
      Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hx
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← AlgHom.commutes (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)

theorem tw_mem (τ : O' ≃ₐ[O] O') (j : ℕ) (A : Ideal O) {x : O' ⊗[O] R}
    (hx : x ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A) :
    tw τ j x ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  have h : Ideal.map (algebraMap O (O' ⊗[O] R)) A ≤
      Ideal.comap (GlobalTheory.CompanionTheory.UnitNorm.tw τ j) (Ideal.map (algebraMap O (O' ⊗[O] R)) A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ ha
  exact h hx

theorem nrm_sub_mem (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (A : Ideal O) {x y : O' ⊗[O] R}
    (h : x - y ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A) :
    nrm ℓ τ x - nrm ℓ τ y ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  rw [← Ideal.Quotient.eq]
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Ideal.Quotient.eq, ← map_sub]
  exact GlobalTheory.CompanionTheory.UnitNorm.tw_mem τ j A h

theorem step [Module.Finite O O'] [Module.Free O O'] [Nontrivial O'] {ℓ : ℕ} {τ : O' ≃ₐ[O] O'}
    (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1)
    (hfixS : ∀ s : O' ⊗[O] R, Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s →
      s ∈ Set.range (inc : R →ₐ[O] O' ⊗[O] R))
    (a : O')
    (hcong : ∀ m : ℕ, 1 ≤ m → ∀ r ∈ (⊥ : Ideal R).jacobson ^ m,
      nrm ℓ τ (1 + a ⊗ₜ[O] r) - (inc : R →ₐ[O] O' ⊗[O] R) (1 + r) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)))
    (u : R) (m : ℕ) (hm : 1 ≤ m) (P : (O' ⊗[O] R)ˣ)
    (h : (inc : R →ₐ[O] O' ⊗[O] R) u - nrm ℓ τ (P : O' ⊗[O] R) ∈
      Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m)) :
    ∃ P' : (O' ⊗[O] R)ˣ, (P' : O' ⊗[O] R) - (P : O' ⊗[O] R) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m) ∧
      (inc : R →ₐ[O] O' ⊗[O] R) u - nrm ℓ τ (P' : O' ⊗[O] R) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)) := by
  have hfix_incR : ∀ x : R, Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R)
      ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x) = (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x := by
    intro x
    simp only [GlobalTheory.CompanionTheory.UnitNorm.inc, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
      map_one, AlgHom.id_apply]
  obtain ⟨r, hr⟩ := hfixS ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) u - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R)) (by
    rw [map_sub, hfix_incR, GlobalTheory.CompanionTheory.UnitNorm.nrm_fixed hℓ hτ])
  obtain ⟨v, hv⟩ := hfixS (GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ ((P⁻¹ : (O' ⊗[O] R)ˣ) : O' ⊗[O] R))
    (GlobalTheory.CompanionTheory.UnitNorm.nrm_fixed hℓ hτ _)
  have hrm : r ∈ (⊥ : Ideal R).jacobson ^ m := by
    have h' := h
    rw [← hr] at h'
    exact GlobalTheory.T.tensor_ideal_map_injective O O' R _ r h'
  have hvr : v * r ∈ (⊥ : Ideal R).jacobson ^ m := Ideal.mul_mem_left _ v hrm
  have hsplit : a ⊗ₜ[O] (v * r) = (a ⊗ₜ[O] (1 : R)) * (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (v * r) := by
    simp only [GlobalTheory.CompanionTheory.UnitNorm.inc, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]
  have hmem : a ⊗ₜ[O] (v * r) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m) := by
    rw [hsplit]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hvr)
  have hJ : a ⊗ₜ[O] (v * r) ∈ Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson :=
    Ideal.map_mono (Ideal.pow_le_self (by omega)) hmem
  have hU : IsUnit (1 + a ⊗ₜ[O] (v * r)) :=
    GlobalTheory.T.isUnit_one_add_jacobson_tensor O O' R _ hJ
  have hPP : GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) *
      GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ ((P⁻¹ : (O' ⊗[O] R)ˣ) : O' ⊗[O] R) = 1 := by
    rw [← GlobalTheory.CompanionTheory.UnitNorm.nrm_mul, Units.mul_inv, GlobalTheory.CompanionTheory.UnitNorm.nrm_one]
  have hc' : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (1 + v * r) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r)) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)) := by
    have h'' := neg_mem (hcong m hm (v * r) hvr)
    rwa [neg_sub] at h''
  have key : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) u -
        GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) * GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r)) =
      GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) *
        ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (1 + v * r) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r))) := by
    rw [map_add, map_one, map_mul]
    linear_combination (-1 : O' ⊗[O] R) * hr +
      (-((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) r * GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R))) * hv +
      (-((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) r)) * hPP
  refine ⟨P * hU.unit, ?_, ?_⟩
  · rw [Units.val_mul, IsUnit.unit_spec,
      show (P : O' ⊗[O] R) * (1 + a ⊗ₜ[O] (v * r)) - P = P * (a ⊗ₜ[O] (v * r)) by ring]
    exact Ideal.mul_mem_left _ _ hmem
  · rw [Units.val_mul, IsUnit.unit_spec, GlobalTheory.CompanionTheory.UnitNorm.nrm_mul, key]
    exact Ideal.mul_mem_left _ _ hc'

end Basics

theorem norm_units_surjective : PositivityTheory.Rg.Tf.Loc.N1 → PositivityTheory.Rg.Tf.Loc.N2 → PositivityTheory.Rg.Tf.Loc.N3 := by
  intro hInt hConj
  unfold PositivityTheory.Rg.Tf.Loc.N3
  intro O O' R _ _ _ _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hbasis r
  by_cases hO' : Nontrivial O'
  swap
  · haveI : Subsingleton O' := not_nontrivial_iff_subsingleton.mp hO'
    have h1 : (1 : O' ⊗[O] R) = 0 := by
      calc (1 : O' ⊗[O] R) = (1 : O') ⊗ₜ[O] (1 : R) := Algebra.TensorProduct.one_def
        _ = (0 : O') ⊗ₜ[O] (1 : R) := by rw [Subsingleton.elim (1 : O') 0]
        _ = 0 := by rw [TensorProduct.zero_tmul]
    haveI : Subsingleton (O' ⊗[O] R) := subsingleton_of_zero_eq_one h1.symm
    exact ⟨1, Subsingleton.elim _ _⟩
  haveI := hO'
  obtain ⟨hfixS, a, ha1, hcong⟩ := hConj O O' R ℓ τ hℓ hτ hfix hbasis
  obtain ⟨hle, N, hN⟩ := GlobalTheory.T.local_finite_algebra_jacobson_radical O R
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) (O' ⊗[O] R) :=
    GlobalTheory.T.finite_module_adic_complete O (O' ⊗[O] R)
  obtain ⟨P₁, hP₁⟩ :=
    GlobalTheory.T.cyclic_algebra_hilbert_ninety hInt O O' R ℓ τ hℓ hτ hfix hbasis ⟨a, ha1⟩ r
  have h2 : ∀ k : ℕ, Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (N * k + 1)) ≤
      Ideal.map (algebraMap O (O' ⊗[O] R)) (IsLocalRing.maximalIdeal O ^ k) := by
    intro k
    rw [← GlobalTheory.CompanionTheory.UnitNorm.map_inc_map]
    refine Ideal.map_mono ?_
    rw [Ideal.map_pow]
    exact le_trans (Ideal.pow_le_pow_right (Nat.le_succ _))
      (by rw [pow_mul]; exact Ideal.pow_right_mono hN k)
  have h3 : Ideal.map (algebraMap O (O' ⊗[O] R)) (IsLocalRing.maximalIdeal O) ≤
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1) := by
    rw [← GlobalTheory.CompanionTheory.UnitNorm.map_inc_map, pow_one]
    exact Ideal.map_mono hle
  have h4 : ∀ x ∈ Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1),
      IsUnit (1 + x) := fun x hx =>
    GlobalTheory.T.isUnit_one_add_jacobson_tensor O O' R x (by rwa [pow_one] at hx)
  have h6 : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (r : R) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P₁ : O' ⊗[O] R) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1) := by
    rw [pow_one, ← neg_sub]
    exact neg_mem hP₁
  obtain ⟨L, hL⟩ := GlobalTheory.T.norm_map_congruence O (O' ⊗[O] R)
    (IsLocalRing.maximalIdeal O)
    (fun m => Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m)) N
    (GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ) ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (r : R)) P₁
    (fun m => Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ m))) h2 h3 h4
    (fun k x y hxy => GlobalTheory.CompanionTheory.UnitNorm.nrm_sub_mem ℓ τ _ hxy) h6
    (fun m hm P hP => GlobalTheory.CompanionTheory.UnitNorm.step hℓ hτ hfixS a hcong (r : R) m hm P hP)
  exact ⟨L, hL⟩

end

end GlobalTheory.CompanionTheory.UnitNorm
end

