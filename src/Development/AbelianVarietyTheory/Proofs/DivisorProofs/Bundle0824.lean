import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0804
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePeriodQuasiLogarithmPDivGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisor
section
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors

namespace GlobalTheory.NumeratorIdeal

section general
variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem count_span_int (v : HeightOneSpectrum R) {a : R} (ha : a ≠ 0) :
    v.valuation K (algebraMap R K a) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a))) := by
  classical
  have hJ : (Ideal.span {a} : Ideal R) ≠ 0 := by simpa using ha
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v hJ,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v ha]

theorem valuation_eq_count (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have ha' : algebraMap R K a ≠ 0 := by simpa using ha0
  have hb' : algebraMap R K b ≠ 0 := by simpa using hb0
  rw [map_div₀, count_span_int K v ha0, count_span_int K v hb0, div_eq_mul_inv (algebraMap R K a),
    ← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v
      (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using ha0)
      (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hb0),
    ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, ← WithZero.exp_sub]
  congr 1
  ring

theorem le_one_of_count {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, 0 ≤ FractionalIdeal.count K v I) : I ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
  refine finprod_induction (fun J : FractionalIdeal R⁰ K => J ≤ 1) le_rfl
    (fun a b ha hb => mul_le_one' ha hb) fun v => ?_
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
  show _ ≤ _
  rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one

theorem le_of_count {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v J ≤ FractionalIdeal.count K v I) :
    I ≤ J := by
  have h1 : I * J⁻¹ ≤ 1 := le_one_of_count K (mul_ne_zero hI (inv_ne_zero hJ)) fun v => by
    rw [FractionalIdeal.count_mul K v hI (inv_ne_zero hJ), FractionalIdeal.count_inv]
    linarith [h v]
  have h2 := mul_le_mul_left h1 J
  rwa [inv_mul_cancel_right₀ hJ, one_mul] at h2

theorem mem_iff_valuation {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ I ↔ ∀ v : HeightOneSpectrum R,
      v.valuation K x ≤ WithZero.exp (-FractionalIdeal.count K v I) := by
  by_cases hx : x = 0
  · subst hx
    simp [FractionalIdeal.zero_mem]
  have hs : FractionalIdeal.spanSingleton R⁰ x ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hx
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  simp only [valuation_eq_count K _ hx, WithZero.exp_le_exp, neg_le_neg_iff]
  exact ⟨fun h v => FractionalIdeal.count_mono K v hs h, le_of_count K hs hI⟩

theorem one_le_count {I : Ideal R} (hI : I ≠ ⊥) (v : HeightOneSpectrum R) (h : I ≤ v.asIdeal) :
    1 ≤ FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := by
  rw [← FractionalIdeal.count_self K v]
  exact FractionalIdeal.count_mono K v (FractionalIdeal.coeIdeal_ne_zero.2 hI)
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).2 h)

theorem sup_eq_top_of {I J : Ideal R} (hI : I ≠ ⊥)
    (h : ∀ v : HeightOneSpectrum R, I ≤ v.asIdeal → J ≤ v.asIdeal → False) : I ⊔ J = ⊤ := by
  by_contra H
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ H
  have h1 : I ≤ p := le_sup_left.trans hle
  exact h ⟨p, hp.isPrime, fun e => hI (le_bot_iff.1 (e ▸ h1))⟩ h1 (le_sup_right.trans hle)

theorem count_prod_pow (s : Finset (HeightOneSpectrum R)) (n : HeightOneSpectrum R → ℕ)
    (f : HeightOneSpectrum R → HeightOneSpectrum R) (hf : ∀ Q, f (f Q) = Q)
    (hs : ∀ Q, Q ∉ s → n Q = 0) (P : HeightOneSpectrum R) :
    FractionalIdeal.count K P ((∏ Q ∈ s, (f Q).asIdeal ^ n Q : Ideal R) : FractionalIdeal R⁰ K)
      = n (f P) := by
  classical
  have e : ((∏ Q ∈ s, (f Q).asIdeal ^ n Q : Ideal R) : FractionalIdeal R⁰ K)
      = ∏ Q ∈ s, ((f Q).asIdeal : FractionalIdeal R⁰ K) ^ n Q := by
    have := map_prod (FractionalIdeal.coeIdealHom R⁰ K) (fun Q => (f Q).asIdeal ^ n Q) s
    simp only [map_pow] at this
    exact this
  rw [e, FractionalIdeal.count_prod K P _ _
    (fun Q _ => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (f Q).ne_bot)),
    Finset.sum_eq_single (f P)]
  · rw [hf, FractionalIdeal.count_pow_self]
  · intro Q _ hQ
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime, mul_zero]
    rintro rfl
    exact hQ (hf Q).symm
  · intro h
    rw [hs _ h, pow_zero, FractionalIdeal.count_one]

end general

theorem exists_numerator : ∀ (E : Type) [Field E] [NumberField E] (σ : 𝓞 E ≃+* 𝓞 E) (cp : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 E)), (∀ x, σ (σ x) = x) → (∀ Q x, x ∈ (cp Q).asIdeal ↔ σ x ∈ Q.asIdeal) → ∀ δ : HeightOneSpectrum (𝓞 E) → ℤ, (Function.support δ).Finite → (∀ Q, δ (cp Q) = -δ Q) → ∃ cc : Ideal (𝓞 E), cc ≠ ⊥ ∧ cc ⊔ cc.map (σ : 𝓞 E →+* 𝓞 E) = ⊤ ∧ (∀ Q, FractionalIdeal.count E Q (cc : FractionalIdeal (𝓞 E)⁰ E) = max (δ Q) 0) ∧ (∀ b : 𝓞 E, (∀ Q, δ Q ≠ 0 → b ∉ Q.asIdeal) → cc ⊔ Ideal.span {b} = ⊤) ∧ ∀ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ WithZero.exp (-δ Q)) → J * idlE (cc.map (σ : 𝓞 E →+* 𝓞 E)) = idlE cc := by
  intro E _ _ σ cp hσ hcp δ hfin hanti
  have hinv : ∀ Q, cp (cp Q) = Q := fun Q => by
    ext x
    rw [hcp, hcp, hσ]
  have hmap : ∀ Q : HeightOneSpectrum (𝓞 E),
      Q.asIdeal.map (σ : 𝓞 E →+* 𝓞 E) = (cp Q).asIdeal := fun Q => by
    ext x
    rw [hcp, Ideal.mem_map_iff_of_surjective (σ : 𝓞 E →+* 𝓞 E) σ.surjective]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hσ] using hy
    · intro h
      exact ⟨σ x, h, hσ x⟩
  set s := hfin.toFinset with hsdef
  have hs : ∀ Q, Q ∉ s → (δ Q).toNat = 0 := fun Q hQ => by
    have : δ Q = 0 := by simpa [hsdef] using hQ
    simp [this]
  set cc : Ideal (𝓞 E) := ∏ Q ∈ s, Q.asIdeal ^ (δ Q).toNat with hcc
  have hbar : cc.map (σ : 𝓞 E →+* 𝓞 E) = ∏ Q ∈ s, (cp Q).asIdeal ^ (δ Q).toNat := by
    have := map_prod (Ideal.mapHom (σ : 𝓞 E →+* 𝓞 E)) (fun Q => Q.asIdeal ^ (δ Q).toNat) s
    simp only [map_pow, Ideal.mapHom_apply, hmap] at this
    exact this
  have h0 : cc ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ Q.ne_bot
  have h0' : cc.map (σ : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    rw [hbar]
    exact Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ (cp Q).ne_bot
  have hc : ∀ Q, FractionalIdeal.count E Q (cc : FractionalIdeal (𝓞 E)⁰ E) = max (δ Q) 0 :=
    fun Q => by
      rw [← Int.ofNat_toNat]
      exact count_prod_pow E s (fun Q => (δ Q).toNat) id (fun _ => rfl) hs Q
  have hc' : ∀ Q, FractionalIdeal.count E Q
      ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = max (-δ Q) 0 :=
    fun Q => by
      rw [← hanti, ← Int.ofNat_toNat, hbar]
      exact count_prod_pow E s (fun Q => (δ Q).toNat) cp hinv hs Q
  refine ⟨cc, h0, sup_eq_top_of h0 fun v h1 h2 => ?_, hc, fun b hb => sup_eq_top_of h0 fun v h1 h2 => ?_,
    fun J hJ => ?_⟩
  · have a1 := one_le_count E h0 v h1
    have a2 := one_le_count E h0' v h2
    rw [hc] at a1
    rw [hc'] at a2
    omega
  · have a1 := one_le_count E h0 v h1
    rw [hc] at a1
    exact hb v (by omega) ((Ideal.span_singleton_le_iff_mem _).1 h2)
  · have f0 : (cc : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h0
    have f0' : ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 h0'
    have hJD : J = (((cc : FractionalIdeal (𝓞 E)⁰ E) *
        ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ :
          FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
      ext x
      rw [hJ, FractionalIdeal.mem_coe, mem_iff_valuation E (mul_ne_zero f0 (inv_ne_zero f0'))]
      refine forall_congr' fun Q => ?_
      rw [FractionalIdeal.count_mul E Q f0 (inv_ne_zero f0'), FractionalIdeal.count_inv, hc, hc']
      have : max (δ Q) 0 + -max (-δ Q) 0 = δ Q := by omega
      rw [this]
    have hid : ∀ I : Ideal (𝓞 E),
        idlE I = ((I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := fun _ => rfl
    rw [hJD, hid, hid, ← FractionalIdeal.coe_mul, inv_mul_cancel_right₀ f0']

end GlobalTheory.NumeratorIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceZeroIsTayStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_isTay_of_slice_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∃ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ := by
  first | exact @GlobalTheory.AnPer.exists_sliceZero_isTay | exact GlobalTheory.AnPer.exists_sliceZero_isTay | (intros; apply GlobalTheory.AnPer.exists_sliceZero_isTay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanMaximalIdealMapOfFlatRegularStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_span_maximalIdeal_map_of_flat_regular : ∀ (O' O : Type) [CommRing O'] [IsRegularLocalRing O'] [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (σ : O' →+* O), IsLocalHom σ → σ.Flat → IsArtinianRing (O ⧸ (IsLocalRing.maximalIdeal O').map σ) → ∀ g : ℕ, ringKrullDim O = g → ∃ f : Fin g → O, Ideal.span (Set.range f) = (IsLocalRing.maximalIdeal O').map σ := by
  first | exact @GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre | exact GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre | (intros; apply GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialUnitarySectionLowerUnitriangularChaStatement
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specialUnitary_section_lowerUnitriangular_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (σ : V (nd X) → realSU X.Ψ X.Gm) (ρ : ℝ) (D₁ : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), 0 < ρ ∧ σ 0 = 1 ∧ ContinuousOn σ (Metric.ball 0 ρ) ∧ (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) ∧ HasStrictFDerivAt (fun z => (fun τ a b => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) D₁ 0 ∧ ∀ z, D₁ z ∈ realLie X.Ψ X.Gm ∧ (∀ τ a b, b < a → inFrame x (D₁ z) τ a b = nmat X z τ a b) ∧ ∀ τ a, inFrame x (D₁ z) τ a a = 0 := by
  first | exact @GlobalTheory.SUChartSection.exists_section | exact GlobalTheory.SUChartSection.exists_section | (intros; apply GlobalTheory.SUChartSection.exists_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqAddPrimeOddModThreeValuationOneStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sq_add_prime_odd_mod_three_valuation_one : ∀ (p : ℕ) (V : ValuationSubring ℂ), p.Prime → 3 < p → ∃ a N : ℕ, N = a ^ 2 + p ∧ Odd N ∧ N % 3 = 2 ∧ V.valuation (N : ℂ) = 1 := by
  first | exact @GlobalTheory.CMModel.exists_sq_add_prime_odd_mod_three_unit | exact GlobalTheory.CMModel.exists_sq_add_prime_odd_mod_three_unit | (intros; apply GlobalTheory.CMModel.exists_sq_add_prime_odd_mod_three_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtNegPrimeKernelDatumOfIntegersLattice
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_ker_point_sqrtNegNat {p : ℕ} (hp : 1 < p) (L : PeriodPair)
    (hL : MulStable L (sqrtNegNat p)) :
    ∃ t : ℂ, t ∉ L.lattice ∧ sqrtNegNat p * t ∈ L.lattice := by
  have hn : Complex.normSq (sqrtNegNat p) = p := by
    rw [sqrtNegNat, map_mul, Complex.normSq_I, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg p), mul_one]
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have h0 : sqrtNegNat p ≠ 0 := fun h => by
    rw [h, map_zero] at hn
    linarith
  obtain ⟨S, hS⟩ := kerRepsExist L _ h0 hL
  have hc := kerRepsCard L _ S h0 hL hS
  rw [hn] at hc
  have hpos : S.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < S.card := by
      push_cast at hc
      linarith
    exact_mod_cast this
  obtain ⟨t, ht⟩ := hpos
  have := hS.1 t ht
  exact ⟨t, by tauto, by tauto⟩

theorem g₂_mem_adjoin_j_of_eq (L : PeriodPair) (h0 : L.g₂ ≠ 0) (h : L.g₃ = L.g₂) :
    L.g₂ ∈ ℚ⟮(latticeCurve L).j⟯ := by
  have hΔ := latticeCurve_Δ_ne_zero L
  rw [latticeCurve_Δ, h] at hΔ
  have h27 : L.g₂ - 27 ≠ 0 := fun e => hΔ (by linear_combination L.g₂ ^ 2 * e)
  have hj : (latticeCurve L).j = 1728 * L.g₂ / (L.g₂ - 27) := by
    rw [latticeCurve_j_eq, h, div_eq_div_iff hΔ h27]
    ring
  have hj' : (latticeCurve L).j - 1728 = 1728 * 27 / (L.g₂ - 27) := by
    rw [hj]
    field_simp
    ring
  have e : L.g₂ = 27 * (latticeCurve L).j / ((latticeCurve L).j - 1728) := by
    rw [hj', hj]
    field_simp
  have hm := IntermediateField.mem_adjoin_simple_self ℚ (latticeCurve L).j
  rw [e]
  exact div_mem (mul_mem (ofNat_mem _ 27) hm) (sub_mem hm (ofNat_mem _ 1728))

theorem exists_datum_of_isIntegersLattice : ∀ (p : ℕ) (L₀ : PeriodPair), p.Prime → p % 4 = 3 →
    3 < p → IsIntegersLattice p L₀ → ∃ (L : PeriodPair) (t : ℂ),
      Datum p ℚ⟮(latticeCurve L₀).j⟯ L t ∧ (latticeCurve L).j = (latticeCurve L₀).j := by
  intro p L₀ hp _ h3 hL₀
  obtain ⟨h2, h3', hmul⟩ := GlobalTheory.T.integersLattice_g2_g3_ne_zero_and_mulStable p L₀ hp h3 hL₀
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L₀.g₃ / L₀.g₂) two_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact div_ne_zero h3' h2 (by rw [← hc]; simp)
  obtain ⟨L, hlat, hg2, hg3, -, hj⟩ := GlobalTheory.T.exists_scaled_periodPair_invariants L₀ c hc0
  have hmul' : MulStable L (sqrtNegNat p) := by
    intro ω hω
    have h1 : c⁻¹ * ω ∈ L₀.lattice := (hlat _).mp (by rwa [mul_inv_cancel_left₀ hc0])
    have h2 := (hlat _).mpr (hmul _ h1)
    rwa [mul_left_comm, mul_inv_cancel_left₀ hc0] at h2
  have hne : L.g₂ ≠ 0 := by
    rw [hg2]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hc0)) h2
  have heq : L.g₃ = L.g₂ := by
    have : L₀.g₃ = c ^ 2 * L₀.g₂ := by rw [hc, div_mul_cancel₀ _ h2]
    rw [hg2, hg3, this]
    field_simp
  have hmem := g₂_mem_adjoin_j_of_eq L hne heq
  rw [hj] at hmem
  obtain ⟨t, ht, ht'⟩ := exists_ker_point_sqrtNegNat hp.one_lt L hmul'
  exact ⟨L, t, ⟨hmul', hmem, heq ▸ hmem, ht, ht'⟩, hj⟩

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePeriodQuasiLogarithmPDivGroupStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_period_quasiLogarithm_pDivGroup : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate), QL μ' ⊤ f → ∃! y : F.B, c.HasPeriod F.θ t f y := by
  first | exact @GlobalTheory.PeriodExists.main | exact GlobalTheory.PeriodExists.main | (intros; apply GlobalTheory.PeriodExists.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitIntertwinerAdelicQuaternion
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem nrm_smul_eq_sq_mul {R : Type*} [CommRing R] {a b : R} (t : R) (x : ℍ[R, a, b]) :
    nrm (t • x) = t ^ 2 * nrm x := by
  simp [nrm]; ring

theorem nrm_sum_orthIdem_smul {R : Type*} [CommRing R] {a b : R} {ι : Type} [Fintype ι] (η : ι → R)
    (y : ι → ℍ[R, a, b]) (h1 : ∀ i, η i * η i = η i) (h2 : ∀ i j, i ≠ j → η i * η j = 0)
    (h3 : ∑ i, η i = 1) : nrm (∑ i, η i • y i) = ∑ i, η i * nrm (y i) := by
  classical
  have key : ∀ i, η i * nrm (∑ j, η j • y j) = η i * nrm (y i) := by
    intro i
    have hs : η i • (∑ j, η j • y j) = η i • y i := by
      rw [Finset.smul_sum, Finset.sum_eq_single i]
      · rw [smul_smul, h1]
      · intro j _ hj
        rw [smul_smul, h2 i j (Ne.symm hj), zero_smul]
      · simp
    have := congrArg nrm hs
    rwa [nrm_smul_eq_sq_mul, nrm_smul_eq_sq_mul, sq, h1] at this
  calc nrm (∑ i, η i • y i) = ∑ i, η i * nrm (∑ j, η j • y j) := by
        rw [← Finset.sum_mul, h3, one_mul]
    _ = _ := Finset.sum_congr rfl fun i _ => key i

def quatStdBasis {R : Type*} [CommRing R] (a b : R) : Fin 4 → ℍ[R, a, b] :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

theorem nrm_intertwiner_comb {R : Type*} [CommRing R] {a b c : R} (p q : ℍ[R, a, b]) (hp : p.re = 0) (hq : q.re = 0)
    (hpp : p * p = algebraMap R ℍ[R, a, b] c) (hqq : q * q = algebraMap R ℍ[R, a, b] c) :
    ∑ i, (![a * b, -b, -a, 1] : Fin 4 → R) i * nrm (p * quatStdBasis a b i + quatStdBasis a b i * q)
      = -8 * a * b * c := by
  have h1 := congrArg QuaternionAlgebra.re hpp
  have h2 := congrArg QuaternionAlgebra.re hqq
  simp [QuaternionAlgebra.algebraMap_eq, hp, hq] at h1 h2
  simp [Fin.sum_univ_four, quatStdBasis, nrm, hp, hq]
  linear_combination (-4 * a * b) * h1 + (-4 * a * b) * h2

theorem exists_unit_intertwiner : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ p q : DA F a b, p.re = 0 → q.re = 0 → p * p = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ y : DA F a b, IsUnit (nrm y) ∧ y * q = p * y := by
  intro F _ _ a b ha hb c hc p q hp hq hpp hqq
  have hcomb := nrm_intertwiner_comb p q hp hq hpp hqq
  have hu : IsUnit (-8 * algebraMap F (AF F) a * algebraMap F (AF F) b * algebraMap F (AF F) c) := by
    have h : IsUnit (-8 * a * b * c) := by
      refine Ne.isUnit ?_
      have : (-8 : F) ≠ 0 := by norm_num
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero this ha) hb) hc
    have h' := h.map (algebraMap F (AF F))
    rwa [map_mul, map_mul, map_mul, map_neg, map_ofNat] at h'
  rw [← hcomb] at hu
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination F (Fin 4) _ _ hu
  refine ⟨∑ i, η i • (p * quatStdBasis _ _ i + quatStdBasis _ _ i * q), ?_, ?_⟩
  · rw [nrm_sum_orthIdem_smul η _ h1 h2 h3]; exact h4
  · rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [add_mul, mul_add, mul_assoc _ q q, hqq, ← mul_assoc p p, hpp, add_comm, mul_assoc,
      Algebra.commutes]

end GlobalTheory.QSA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNormGramDetPairFieldCaseStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitNorm_gramDet_pair_fieldCase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ a b : Fin M → K ⊗[F] E, a ≠ 0 → b ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J a w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w b)) := by
  first | exact @GlobalTheory.PlaneNorm.FieldCase.exists_unitNorm_pair | exact GlobalTheory.PlaneNorm.FieldCase.exists_unitNorm_pair | (intros; apply GlobalTheory.PlaneNorm.FieldCase.exists_unitNorm_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZeroSectionValueInPowerFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUnivVals

open TopologicalSpace Opposite

theorem comp_base_pt {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).base x = g.base (f.base x) := rfl

theorem glue_fn {X : Scheme.{0}} {J : Type} (W : J → X.Opens) (hc : (⊤ : X.Opens) ≤ iSup W) (a : ∀ i, Γ(X, W i))
    (h : ∀ i j x, x ∈ W i → x ∈ W j → gs (𝟙 X) x (W i) (a i) = gs (𝟙 X) x (W j) (a j)) :
    ∃ α : Γ(X, ⊤), ∀ i x, x ∈ W i → gs (𝟙 X) x ⊤ α = gs (𝟙 X) x (W i) (a i) := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hc a
    (fun i j => fn_ext (V := W i ⊓ W j) fun y hy =>
      (gs_res (𝟙 X) y inf_le_left hy _).trans ((h i j y hy.1 hy.2).trans (gs_res (𝟙 X) y inf_le_right hy _).symm))
  refine ⟨s, fun i x hx => ?_⟩
  exact (gs_res (𝟙 X) x (le_top : W i ≤ ⊤) hx s).symm.trans (congrArg (gs (𝟙 X) x (W i)) (hs i))

theorem vals (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ)
    (eA : LB.Gen (L.pull (eSec A))) (s : LB.Sec (LPow A L (k : ℤ) (topS Rg))) (hL : L.IsLB) (hA : eA.IsGen) :
    ∃ α : Γ(Sp Rg, ⊤), GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) s α := by
  set S : Scheme.{0} := (𝟙_ (Over (Sp Rg))).left with hS
  set e : S ⟶ (topS Rg ⊗ A).left := eSec A ≫ θ A with he_def
  have he : e ≫ (snd (topS Rg) A).left = eSec A := by
    rw [he_def, Category.assoc, θ_snd, Category.comp_id]
  have memN : ∀ (z : S) (q : Fin 1 → L.ι), e z ∈ (LPow A L (k : ℤ) (topS Rg)).U q ↔ eSec A z ∈ L.U (q 0) := by
    intro z q
    constructor
    · intro h
      have h0 := Set.mem_iInter.1 h 0
      rw [Set.mem_preimage, ← comp_base_pt, he] at h0
      exact h0
    · intro h
      refine Set.mem_iInter.2 fun t => ?_
      rw [Subsingleton.elim t 0, Set.mem_preimage, ← comp_base_pt, he]
      exact h
  let W : L.ι → S.Opens := fun i => e ⁻¹ᵁ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => i)
  have memW : ∀ (z : S) (i : L.ι), z ∈ W i ↔ eSec A z ∈ L.U i := by
    intro z i
    constructor
    · intro h; exact mem_pull.1 h.2
    · intro h; exact ⟨(memN z _).2 h, mem_pull.2 h⟩
  let a : ∀ i, Γ(S, W i) := fun i =>
    (S.presheaf.map (homOfLE (inf_le_left : W i ≤ e ⁻¹ᵁ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i))).op).hom ((e.app _).hom (s.f (fun _ => i))) *
      ((res (inf_le_right : W i ≤ (L.pull (eSec A)).U (fun _ => i)) (eA.s (fun _ => i)))⁻¹ ^ k).val
  have ga : ∀ i x, x ∈ W i → gs (𝟙 S) x (W i) (a i) =
      gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i)) (s.f (fun _ => i)) * ((gm (𝟙 S) x _ (eA.s (fun _ => i)))⁻¹ ^ k).val := by
    intro i x hx
    rw [gs_mul (𝟙 S) x _ hx, gs_res (𝟙 S) x _ hx, gs_pull (𝟙 S) e x _ hx.1, Category.id_comp, gs_unit (𝟙 S) x _ hx,
      map_pow, map_inv, gm_res (𝟙 S) x _ hx]

  have compat : ∀ i j x, x ∈ W i → x ∈ W j → gs (𝟙 S) x (W i) (a i) = gs (𝟙 S) x (W j) (a j) := by
    intro i j x hx hy
    have hxi := (memW x i).1 hx
    have hxj := (memW x j).1 hy
    have hx' : e x ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j) := ⟨hx.1, hy.1⟩
    have mem : (snd (topS Rg) A).left (e x) ∈ L.U i ⊓ L.U j := by
      rw [← comp_base_pt, he]; exact ⟨hxi, hxj⟩
    have hg : gm e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j)) ((LPow A L (k : ℤ) (topS Rg)).g (fun _ => i) (fun _ => j)) =
        (gm (eSec A) x _ (L.g i j)) ^ k := by
      show gm e x _ (∏ _t : Fin 1, (res _ (pullU (snd (topS Rg) A).left _ (L.g i j))) ^ (k : ℤ)) = _
      rw [Fintype.prod_unique, map_zpow]
      erw [gm_res e x _ hx']
      rw [gm_pull e _ x _ mem, he, zpow_natCast]
    have hs := congrArg (gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j))) (s.compat (fun _ => i) (fun _ => j))
    rw [gs_res e x _ hx', gs_mul e x _ hx', gs_res e x _ hx', gs_unit e x _ hx', hg] at hs
    have hp : x ∈ (L.pull (eSec A)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => j) := ⟨hx.2, hy.2⟩
    have mem' : (eSec A) ((𝟙 S : S ⟶ S) x) ∈ L.U i ⊓ L.U j := ⟨hxi, hxj⟩
    have hg' : gm (𝟙 S) x _ ((L.pull (eSec A)).g (fun _ => i) (fun _ => j)) = gm (eSec A) x _ (L.g i j) := by
      show gm (𝟙 S) x _ (∏ _t : PUnit, (res _ (pullU (eSec A) _ (L.g i j))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      erw [gm_res (𝟙 S) x _ hp]
      rw [gm_pull (𝟙 S) (eSec A) x _ mem', Category.id_comp]
    have hA' := congrArg (gm (𝟙 S) x ((L.pull (eSec A)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => j)))
      (hA (fun _ => i) (fun _ => j))
    rw [map_mul, gm_res _ x _ hp, gm_res _ x _ hp, hg'] at hA'
    rw [ga i x hx, ga j x hy, hs, hA']
    set u := gm (eSec A) x _ (L.g i j)
    set B := gm (𝟙 S) x _ (eA.s (fun _ => j))
    have hinv : (u * B)⁻¹ ^ k = (u ^ k)⁻¹ * B⁻¹ ^ k := by rw [mul_inv, mul_pow, inv_pow]
    have hU : (u ^ k).val * ((u ^ k)⁻¹).val = 1 := Units.mul_inv _
    rw [hinv, Units.val_mul]
    linear_combination (gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => j)) (s.f (fun _ => j)) * (B⁻¹ ^ k).val) * hU
  obtain ⟨α, hα⟩ := glue_fn W (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart hL (eSec A x)
      exact Opens.mem_iSup.2 ⟨i, (memW x i).2 hi⟩) a compat
  refine ⟨α, fun z q hz => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, q = fun _ => i := ⟨q 0, funext fun t => by rw [Subsingleton.elim t 0]⟩
  have hzW : z ∈ W i := (memW z i).2 ((memN z _).1 hz)
  rw [hα i z hzW, ga i z hzW]
  show _ = _ * ((gm (𝟙 S) z _ (eA.s fun _ => i)) ^ k).val
  rw [_root_.mul_assoc, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, _root_.mul_one]

end GlobalTheory.HomFixUnivVals
end
end

